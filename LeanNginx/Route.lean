import LeanNginx.Config
/-!
# Request routing (pure)

Given the configuration and a parsed request, decide what to do: serve a file, list a
directory, redirect, return a fixed response, proxy, or answer with an error. Routing needs to
know which paths exist, so `route` returns a small program (`Step`) that asks `stat` questions;
the IO layer answers them with real `stat` calls, and the specs quantify over *every* possible
answer (`Step.run` with an arbitrary oracle).

Locations are matched like nginx (exact `=` first, then the longest prefix), on the normalised
URI. File paths are always `base ++ "/" ++ seg₁ ++ "/" ++ …` with `base` a configured `root` or
`alias` and every segment `Safe`; the spec `route_confined` proves it, which rules out path
traversal (including the classic `alias` off-by-slash bug) by construction.
-/
namespace LeanNginx

/-! ## Server and location selection -/

def isSuffixB (s b : Bytes) : Bool := s.reverse.isPrefixOf b.reverse

/-- `example.com`, `*.example.com` (sub-domains only), `.example.com` (both). -/
def nameMatches (pat host : Bytes) : Bool :=
  if pat.take 2 == b!"*." then isSuffixB (pat.drop 1) host
  else if pat.head? == some 46 then host == pat.drop 1 || isSuffixB pat host
  else pat == host

/-- Candidate servers for a connection accepted on local address `addr` (`none` = the wildcard
socket) and `port`. nginx hands each connection to the most specific bound socket and only its
own servers are candidates, so the match on `addr` is exact: a `listen 127.0.0.1:…` server is
*not* reachable through the wildcard socket, and vice versa. Without the `addr` match an
address-restricted vhost (e.g. a loopback-only admin block) would be served on every interface. -/
def serversOn (servers : List Server) (addr : Option String) (port : Nat) : List Server :=
  servers.filter fun s => s.listens.any fun l => l.addr == addr && l.port == port

/-- nginx order: exact name, then wildcard, then the `default_server`, then the first server. -/
def selectServer (servers : List Server) (addr : Option String) (port : Nat) (host : Option Bytes) :
    Option Server :=
  let cands := serversOn servers addr port
  let byName := host.bind fun h =>
    (cands.find? (·.names.contains h)) <|>
    (cands.find? (·.names.any fun p => (p.head? == some 42 || p.head? == some 46) && nameMatches p h))
  byName <|> cands.find? (·.listens.any fun l => l.addr == addr && l.port == port && l.default)
         <|> cands.head?

def matchesLoc (l : Location) (uri : Bytes) : Bool :=
  match l.kind with
  | .exact => l.uri == uri
  | .regex re => regexMatches re uri
  | _ => isPrefixB l.uri uri

/-- `location /p` or `location ^~ /p`. -/
def isPrefixLoc (l : Location) : Bool :=
  match l.kind with
  | .pre | .noRegex => true
  | _ => false

/-- A regex location whose regex matches `uri`. -/
def regexHit (uri : Bytes) (l : Location) : Bool :=
  match l.kind with
  | .regex re => regexMatches re uri
  | _ => false

/-- The longest-`uri` location (the first one on ties). -/
def longest : List Location → Option Location → Option Location
  | [], best => best
  | l :: ls, best =>
    longest ls (match best with
      | none => some l
      | some b => if b.uri.length < l.uri.length then some l else some b)

/-- nginx's order: an exact `=` match; else the longest matching prefix, unless a regex
location matches (first in configuration order), which wins over a plain prefix but not over
a `^~` prefix. -/
def selectLocation (locs : List Location) (uri : Bytes) : Option Location :=
  match locs.find? (fun l => l.kind == .exact && l.uri == uri) with
  | some l => some l
  | none =>
    match longest (locs.filter fun l => isPrefixLoc l && isPrefixB l.uri uri) none with
    | some p => if p.kind == .noRegex then some p else some ((locs.find? (regexHit uri)).getD p)
    | none => locs.find? (regexHit uri)

/-! ## Variables (`$uri`, `$host`, …) -/

structure Vars where
  uri : Bytes
  requestUri : Bytes
  args : Bytes
  host : Bytes
  method : Bytes
  remoteAddr : Bytes
  serverPort : Bytes
  scheme : Bytes := b!"http"
  deriving Repr, Inhabited

def Vars.lookup (v : Vars) (name : Bytes) : Option Bytes :=
  if name == b!"uri" || name == b!"document_uri" then some v.uri
  else if name == b!"request_uri" then some v.requestUri
  else if name == b!"args" || name == b!"query_string" then some v.args
  else if name == b!"is_args" then some (if v.args.isEmpty then [] else b!"?")
  else if name == b!"host" || name == b!"server_name" then some v.host
  else if name == b!"request_method" then some v.method
  else if name == b!"remote_addr" then some v.remoteAddr
  else if name == b!"server_port" then some v.serverPort
  else if name == b!"scheme" then some v.scheme
  else none

def isVarChar (c : UInt8) : Bool := isAlpha c || isDigit c || c == 95

def takeVarName : Bytes → Bytes × Bytes
  | c :: rest => if isVarChar c then let (a, b) := takeVarName rest; (c :: a, b) else ([], c :: rest)
  | [] => ([], [])

def expandAux (v : Vars) : Nat → Bytes → Bytes
  | 0, b => b
  | _, [] => []
  | fuel + 1, 36 :: 123 :: rest =>
    let (n, r) := takeVarName rest
    match r, v.lookup n with
    | 125 :: r', some val => val ++ expandAux v fuel r'
    | _, _ => 36 :: 123 :: expandAux v fuel rest
  | fuel + 1, 36 :: rest =>
    let (n, r) := takeVarName rest
    match v.lookup n with
    | some val => if n.isEmpty then 36 :: expandAux v fuel rest else val ++ expandAux v fuel r
    | none => 36 :: expandAux v fuel rest
  | fuel + 1, c :: rest => c :: expandAux v fuel rest

/-- Expand `$name` and `${name}`; unknown variables stay as written. -/
def expand (v : Vars) (b : Bytes) : Bytes := expandAux v (b.length + 1) b

/-! ## Actions and stat programs -/

/-- What `stat` reports about a path. -/
inductive Kind where
  | file (size : Nat) (mtime : Int)
  | dir
  deriving Repr, DecidableEq, Inhabited

inductive Action where
  | file (path : Bytes) (size : Nat) (mtime : Int)
  | autoindex (path : Bytes)
  | redirect (code : Nat) (location : Bytes)
  /-- `return code text` -/
  | text (code : Nat) (body : Bytes)
  | error (code : Nat)
  /-- `return 444`: close the connection without answering -/
  | close
  /-- re-run routing on this path (index files, `try_files` fallback). The path is already
  normalised and is not decoded again; `query`, when present, replaces the query string. -/
  | internal (np : NPath) (query : Option Bytes)
  | proxy (up : Upstream) (uri : Bytes)
  deriving Repr, Inhabited, DecidableEq

inductive Step where
  | done (a : Action)
  | stat (path : Bytes) (k : Option Kind → Step)
  deriving Inhabited

/-- Run a stat program against an oracle. -/
def Step.run (o : Bytes → Option Kind) : Step → Action
  | .done a => a
  | .stat p k => (k (o p)).run o

/-! ## File-system mapping -/

def joinSegs (segs : List Bytes) : Bytes := segs.flatMap (47 :: ·)

def dropTrailingSlash (b : Bytes) : Bytes :=
  if b.getLast? == some 47 && b.length > 1 then b.dropLast else b

def defaultRoot : Bytes := b!"html"

/-- Directory a location serves from and the safe segments below it. -/
def fsTarget (l : Location) (eff : Settings) (np : NPath) : Option (Bytes × List Bytes) :=
  match l.alias with
  | some a => do
    let rem := np.uri.drop l.uri.length
    let segs ← normSegs (splitOnByte 47 rem) []
    pure (dropTrailingSlash a, segs)
  | none => some (dropTrailingSlash (eff.root.getD defaultRoot), np.segs)

def redirectCodes : List Nat := [301, 302, 303, 307, 308]

def retAction (v : Vars) : Nat × Option Bytes → Action
  | (444, _) => .close
  | (c, some t) => if redirectCodes.contains c then .redirect c (expand v t) else .text c (expand v t)
  | (c, none) => .error c

def withQuery (uri : Bytes) (q : Option Bytes) : Bytes :=
  match q with
  | some q => uri ++ [63] ++ q
  | none => uri

/-- Target of an internal redirect that is written as a URI (the `try_files` fallback, an
`error_page`): the query is split off at the first `?` and the path is normalised as it stands.
It is not percent-decoded: like nginx, an internal redirect takes its path literally. -/
def internalTarget (u : Bytes) : Option (NPath × Option Bytes) :=
  match splitTarget u with
  | (p, q) => (normalizeDecoded p).map (·, q)

/-- Directory request: first existing index file (internal redirect), else autoindex/403/404.
The redirect goes to the directory's own segments plus the index name, so the file routed next
is the one that was just found: nothing is re-parsed, decoded or split at `?`. -/
def serveDir (eff : Settings) (np : NPath) (base : Bytes) (segs : List Bytes) : List Bytes → Step
  | idx :: rest =>
    if segOk idx then
      .stat (base ++ joinSegs (segs ++ [idx])) fun
        | some (.file _ _) => .done (.internal { segs := np.segs ++ [idx], dir := false } none)
        | _ => serveDir eff np base segs rest
    else serveDir eff np base segs rest
  | [] =>
    .stat (base ++ joinSegs segs) fun
      | some .dir => .done (if eff.autoindex.getD false then .autoindex (base ++ joinSegs segs) else .error 403)
      | _ => .done (.error 404)

def serveStatic (l : Location) (eff : Settings) (np : NPath) (query : Option Bytes) : Step :=
  match fsTarget l eff np with
  | none => .done (.error 404)
  | some (base, segs) =>
    if np.dir then serveDir eff np base segs (eff.index.getD [b!"index.html"])
    else
      .stat (base ++ joinSegs segs) fun
        | some (.file size mtime) => .done (.file (base ++ joinSegs segs) size mtime)
        | some .dir => .done (.redirect 301 (withQuery (percentEncode (np.uri ++ [47])) query))
        | none => .done (.error 404)

/-- `try_files a b … last`: the first of `a b …` that exists, else `last` (`=code` or a URI).
Entries are paths, not request targets: after variable expansion they are used as they stand
(`normalizeDecoded`), never percent-decoded. `$uri` therefore names exactly the path the
location was selected on (`tryFiles_uri_serves_request_file` in `Spec.lean`). A fallback URI
that does not normalise is a 500.

`own np` says whether the path `np` belongs to this location (selects it). A file or directory
found for an entry that belongs to another location is not served here: routing continues with an
internal redirect to it (without `stat`ing it, so its existence does not leak), so that location's rules, `auth_basic` among them, decide. nginx would
serve it under the current location; with an entry built from client input
(`try_files /q/$args.html`, `GET /?../admin/x`) that serves another location's files without its
access check. Here a file is only ever served for a path of the location whose access check passed
(`routeAuth_file_authorized`). -/
def tryFiles (l : Location) (eff : Settings) (v : Vars) (query : Option Bytes)
    (own : NPath → Bool) (guarded : NPath → Bool) : List Bytes → Step
  | [] => .done (.error 404)
  | [last] =>
    let e := expand v last
    if e.head? == some 61 then .done (.error ((parseNat? (e.drop 1)).getD 404))
    else match internalTarget e with
      | some (np, q) => .done (.internal np q)
      | none => .done (.error 500)
  | item :: rest =>
    let e := expand v item
    match normalizeDecoded e with
    | none => tryFiles l eff v query own guarded rest
    | some np =>
      match fsTarget l eff np with
      | none => tryFiles l eff v query own guarded rest
      | some (base, segs) =>
        -- A path that selects a *different*, password-protected location hands off to it without a
        -- `stat`, so whether that location's file exists never shows in this location's answer (no
        -- existence oracle across `auth_basic`). An unprotected cross-location path keeps the normal
        -- stat-then-fallthrough, so a catalog like `try_files /q/$args.html /index.html` still works.
        if guarded np then .done (.internal np none)
        else
          .stat (base ++ joinSegs segs) fun
            | some (.file size mtime) =>
              if np.dir then tryFiles l eff v query own guarded rest
              else if own np then .done (.file (base ++ joinSegs segs) size mtime)
              else .done (.internal np none)
            | some .dir =>
              if np.dir then
                if own np then serveDir eff np base segs (eff.index.getD [b!"index.html"])
                else .done (.internal np none)
              else tryFiles l eff v query own guarded rest
            | none => tryFiles l eff v query own guarded rest

/-- The implicit location used when no `location` matches. -/
def defaultLocation : Location := { kind := .pre, uri := b!"/" }

def effective (h : HttpConf) (sv : Server) (l : Location) : Settings :=
  l.s.merge (sv.s.merge h.s)

/-- Route a request whose path normalised to `np`. -/
def route (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath) : Step :=
  match sv.ret with
  | some r => .done (retAction v r)
  | none =>
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    let eff := effective h sv l
    match l.ret, l.proxy with
    | some r, _ => .done (retAction v r)
    | none, some up =>
      -- The upstream gets the path that was routed, decoded once and normalised, re-encoded
      -- strictly (nginx forwards the client's raw path, so `/admin/..%2Fapi/x` is routed as
      -- `/api/x` and reaches an upstream that does not decode `%2F` as `/admin/…`).
      if np.segs.any proxyAmbiguous then .done (.error 400) else
      let uri := match up.uri with
        | some u => percentEncode u ++ percentEncodeStrict (np.uri.drop l.uri.length)
        | none => percentEncodeStrict np.uri
      .done (.proxy up (withQuery uri req.query))
    | none, none =>
      if !(req.method == b!"GET" || req.method == b!"HEAD") then .done (.error 405)
      else match l.tryFiles with
        | some items =>
          tryFiles l eff v req.query (fun p => (selectLocation sv.locations p.uri).getD defaultLocation == l)
            (fun p => let l' := (selectLocation sv.locations p.uri).getD defaultLocation
                      !(l' == l) && (match (effective h sv l').authBasic with | some (some _) => true | _ => false)) items
        | none => serveStatic l eff np req.query

end LeanNginx

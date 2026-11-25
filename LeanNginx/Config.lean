import LeanNginx.Http
import LeanNginx.Regex
/-!
# nginx configuration files

Three layers, all pure:

1. `lex`: bytes → tokens (words, quoted strings, `;`, `{`, `}`; `#` comments).
2. `parseDirectives`: tokens → a tree of `Directive`s (nginx's generic block syntax).
3. `elabConfig`: the tree → a typed `Config` (`http`, `server`, `location` …), with nginx's
   error messages for unknown or misplaced directives and bad arguments.

`include` is expanded by the IO layer between 2 and 3. Directives that only tune nginx's
internals (`worker_processes`, `sendfile`, …) are accepted and ignored so that stock
configuration files load; they are reported as warnings.
-/
namespace LeanNginx

/-! ## Lexer -/

inductive Tok where
  | word (b : Bytes)
  | semi
  | lbrace
  | rbrace
  deriving Repr, DecidableEq, Inhabited

def isSpaceB (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

def wordEnd (c : UInt8) : Bool := isSpaceB c || c == 59 || c == 123 || c == 125

/-- Unquoted word: up to whitespace, `;`, `{`, `}`. -/
def takeWord : Bytes → Bytes × Bytes
  | [] => ([], [])
  | c :: rest =>
    if wordEnd c then ([], c :: rest)
    else let (w, r) := takeWord rest; (c :: w, r)

/-- Quoted string body after the opening quote `q`; handles `\"`, `\\`, `\n`, `\t`. -/
def takeQuoted (q : UInt8) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | 92 :: c :: rest => do
    let (w, r) ← takeQuoted q rest
    let c' := if c == 110 then 10 else if c == 116 then 9 else if c == 114 then 13 else c
    pure (c' :: w, r)
  | c :: rest =>
    if c == q then some ([], rest)
    else do let (w, r) ← takeQuoted q rest; pure (c :: w, r)

def skipLine : Bytes → Bytes
  | [] => []
  | c :: rest => if c == 10 then rest else skipLine rest

def lexAux : Nat → Bytes → Except String (List Tok)
  | 0, _ => .error "configuration too large"
  | _, [] => .ok []
  | fuel + 1, c :: rest =>
    if isSpaceB c then lexAux fuel rest
    else if c == 35 then lexAux fuel (skipLine rest)
    else if c == 59 then (Tok.semi :: ·) <$> lexAux fuel rest
    else if c == 123 then (Tok.lbrace :: ·) <$> lexAux fuel rest
    else if c == 125 then (Tok.rbrace :: ·) <$> lexAux fuel rest
    else if c == 34 || c == 39 then
      match takeQuoted c rest with
      | none => .error "unexpected end of file, expecting closing quote"
      | some (w, r) => (Tok.word w :: ·) <$> lexAux fuel r
    else
      let (w, r) := takeWord (c :: rest)
      (Tok.word w :: ·) <$> lexAux fuel r

def lex (b : Bytes) : Except String (List Tok) := lexAux (b.length + 1) b

/-! ## Directive trees -/

inductive Directive where
  | mk (name : Bytes) (args : List Bytes) (block : Option (List Directive))
  deriving Repr, Inhabited

def Directive.name : Directive → Bytes | .mk n _ _ => n
def Directive.args : Directive → List Bytes | .mk _ a _ => a
def Directive.block : Directive → Option (List Directive) | .mk _ _ b => b

def takeArgs : List Tok → List Bytes × List Tok
  | .word w :: rest => let (a, r) := takeArgs rest; (w :: a, r)
  | toks => ([], toks)

/-- Parse a sequence of directives up to `}` (or end of input when `top`). -/
def parseBlock : Nat → Bool → List Tok → Except String (List Directive × List Tok)
  | 0, _, _ => .error "configuration nested too deeply"
  | _, top, [] => if top then .ok ([], []) else .error "unexpected end of file, expecting \"}\""
  | fuel + 1, top, t :: rest =>
    match t with
    | .rbrace => if top then .error "unexpected \"}\"" else .ok ([], rest)
    | .semi => .error "unexpected \";\""
    | .lbrace => .error "unexpected \"{\""
    | .word n =>
      let (args, rest') := takeArgs rest
      match rest' with
      | .semi :: r => do
        let (ds, r') ← parseBlock fuel top r
        pure (.mk n args none :: ds, r')
      | .lbrace :: r => do
        let (inner, r1) ← parseBlock fuel false r
        let (ds, r2) ← parseBlock fuel top r1
        pure (.mk n args (some inner) :: ds, r2)
      | _ => .error s!"directive \"{toStr n}\" is not terminated by \";\""

def parseDirectives (b : Bytes) : Except String (List Directive) := do
  let toks ← lex b
  let (ds, _) ← parseBlock (toks.length + 1) true toks
  pure ds

/-! ## Typed configuration -/

inductive LocKind where
  /-- `location = /uri` -/
  | exact
  /-- `location ^~ /uri` (no regex locations exist here, so it behaves like a prefix) -/
  | noRegex
  /-- `location /uri` -/
  | pre
  /-- `location ~ regex` / `location ~* regex` (case-insensitivity is compiled into `re`) -/
  | regex (re : Re)
  deriving Repr, DecidableEq, Inhabited

structure Upstream where
  host : String
  port : Nat
  /-- `proxy_pass http://h:p/uri` replaces the matched location prefix with `uri`. -/
  uri : Option Bytes
  deriving Repr, Inhabited, DecidableEq

/-- Settings inherited http → server → location (a lower level overrides, as in nginx). -/
structure Settings where
  root : Option Bytes := none
  index : Option (List Bytes) := none
  autoindex : Option Bool := none
  addHeaders : Option (List (Bytes × Bytes)) := none
  errorPages : Option (List (Nat × Bytes)) := none
  defaultType : Option Bytes := none
  maxBody : Option Nat := none
  sslCert : Option Bytes := none
  sslKey : Option Bytes := none
  gzip : Option Bool := none
  /-- `gzip_types` (lower case); `text/html` is always included, `*` means every type. -/
  gzipTypes : Option (List Bytes) := none
  gzipMinLength : Option Nat := none
  gzipLevel : Option Nat := none
  gzipVary : Option Bool := none
  /-- `auth_basic`: `some (some realm)` = on, `some none` = `off`. -/
  authBasic : Option (Option Bytes) := none
  /-- `auth_basic_user_file`, relative to the configuration directory. -/
  authUserFile : Option Bytes := none
  deriving Repr, Inhabited, DecidableEq

def Settings.merge (child parent : Settings) : Settings where
  root := child.root <|> parent.root
  index := child.index <|> parent.index
  autoindex := child.autoindex <|> parent.autoindex
  addHeaders := child.addHeaders <|> parent.addHeaders
  errorPages := child.errorPages <|> parent.errorPages
  defaultType := child.defaultType <|> parent.defaultType
  maxBody := child.maxBody <|> parent.maxBody
  sslCert := child.sslCert <|> parent.sslCert
  sslKey := child.sslKey <|> parent.sslKey
  gzip := child.gzip <|> parent.gzip
  gzipTypes := child.gzipTypes <|> parent.gzipTypes
  gzipMinLength := child.gzipMinLength <|> parent.gzipMinLength
  gzipLevel := child.gzipLevel <|> parent.gzipLevel
  gzipVary := child.gzipVary <|> parent.gzipVary
  authBasic := child.authBasic <|> parent.authBasic
  authUserFile := child.authUserFile <|> parent.authUserFile

structure Location where
  kind : LocKind
  uri : Bytes
  s : Settings := {}
  alias : Option Bytes := none
  ret : Option (Nat × Option Bytes) := none
  tryFiles : Option (List Bytes) := none
  proxy : Option Upstream := none
  deriving Repr, Inhabited, DecidableEq

structure Listen where
  /-- `none` = all addresses. -/
  addr : Option String
  port : Nat
  default : Bool
  /-- `listen … ssl`: TLS 1.3 on this socket. -/
  ssl : Bool := false
  deriving Repr, Inhabited, DecidableEq

structure Server where
  /-- Position in the `http` block (identifies the server's TLS certificate). -/
  idx : Nat := 0
  listens : List Listen := []
  names : List Bytes := []
  s : Settings := {}
  ret : Option (Nat × Option Bytes) := none
  locations : List Location := []
  deriving Repr, Inhabited

structure HttpConf where
  s : Settings := {}
  servers : List Server := []
  /-- extension (lower case) → MIME type -/
  types : List (Bytes × Bytes) := []
  /-- `none` = `access_log off` -/
  accessLog : Option Bytes := some b!"logs/access.log"
  keepaliveTimeout : Nat := 75
  serverTokens : Bool := true
  deriving Repr, Inhabited

structure Config where
  http : HttpConf := {}
  errorLog : Option Bytes := none
  /-- `worker_processes`: `some n` processes, `none` = `auto` (one per CPU core). -/
  workers : Option Nat := some 1
  /-- `worker_connections` (in `events`): open client connections at most, per process. Further
  connections are closed at once (nginx: "worker_connections are not enough"). -/
  workerConnections : Nat := 512
  deriving Repr, Inhabited

/-! ### Argument parsers -/

def onOff (name : Bytes) : List Bytes → Except String Bool
  | [v] => if v == b!"on" then .ok true else if v == b!"off" then .ok false
           else .error s!"invalid value \"{toStr v}\" in \"{toStr name}\" directive, it must be \"on\" or \"off\""
  | _ => .error s!"invalid number of arguments in \"{toStr name}\" directive"

/-- `10`, `10k`, `10m`, `1g` (bytes). -/
def parseSize (b : Bytes) : Option Nat :=
  match b.getLast? with
  | some c =>
    let c := toLower c
    let mul := if c == 107 then 1024 else if c == 109 then 1024 * 1024
               else if c == 103 then 1024 * 1024 * 1024 else 1
    let digits := if mul == 1 then b else b.dropLast
    (· * mul) <$> parseNat? digits
  | none => none

/-- `75`, `75s`, `2m`, `1h` (seconds). -/
def parseTime (b : Bytes) : Option Nat :=
  match b.getLast? with
  | some c =>
    let mul := if c == 115 then 1 else if c == 109 then 60 else if c == 104 then 3600 else 0
    if mul == 0 then parseNat? b else (· * mul) <$> parseNat? b.dropLast
  | none => none

/-- `8080`, `127.0.0.1:8080`, `*:8080`, `localhost:8080`, `[::]:8080`, plus `default_server`. -/
def parseListen (args : List Bytes) : Except String Listen := do
  match args with
  | [] => throw "invalid number of arguments in \"listen\" directive"
  | a :: opts =>
    for o in opts do
      if o == b!"default_server" || o == b!"default" || o == b!"reuseport" || o == b!"ssl" ||
         o == b!"http2" then pure ()
      else if o == b!"quic" then
        throw "\"quic\" in \"listen\" is not supported by leannginx (HTTP/1.1 over TCP only)"
      else throw s!"invalid parameter \"{toStr o}\""
    let dflt := opts.contains b!"default_server" || opts.contains b!"default"
    let (addr, portB) :=
      if a.head? == some 91 then
        let (v6, rest) := splitFirst 93 (a.drop 1)
        (some v6, match rest with | some (58 :: p) => p | _ => b!"80")
      else match splitFirst 58 a with
        | (p, none) => if p.all isDigit then (none, p) else (some p, b!"80")
        | (h, some p) => (some h, p)
    let some port := parseNat? portB | throw s!"invalid port in \"{toStr a}\" of the \"listen\" directive"
    unless 0 < port && port < 65536 do throw s!"invalid port in \"{toStr a}\" of the \"listen\" directive"
    let addr := match addr with
      | some h => if h == b!"*" || h == b!"0.0.0.0" then none
                  else if h == b!"localhost" then some "127.0.0.1" else some (toStr h)
      | none => none
    pure { addr, port, default := dflt, ssl := opts.contains b!"ssl" }

/-- `proxy_pass http://host[:port][/uri]` -/
def parseUpstream (u : Bytes) : Except String Upstream := do
  unless isPrefixB b!"http://" (lowerB u) do
    if isPrefixB b!"https://" (lowerB u) then throw "proxy_pass to https:// is not supported (yet)"
    throw s!"invalid URL prefix in \"{toStr u}\""
  let rest := u.drop 7
  let (auth, path?) := splitFirst 47 rest
  let (h, p?) :=
    if auth.head? == some 91 then
      let (v6, r) := splitFirst 93 (auth.drop 1)
      (v6, match r with | some (58 :: p) => some p | _ => none)
    else splitFirst 58 auth
  if h.isEmpty then throw s!"no host in \"{toStr u}\" of the \"proxy_pass\" directive"
  let port ← match p? with
    | none => pure 80
    | some p => match parseNat? p with
      | some n => if 0 < n && n < 65536 then pure n else throw s!"invalid port in upstream \"{toStr u}\""
      | none => throw s!"invalid port in upstream \"{toStr u}\""
  pure { host := toStr h, port, uri := (fun p => 47 :: p) <$> path? }

def parseReturn (args : List Bytes) : Except String (Nat × Option Bytes) :=
  match args with
  | [a] =>
    match parseNat? a with
    | some c => if c ≤ 999 then .ok (c, none) else .error "invalid return code"
    | none =>
      if isPrefixB b!"http://" a || isPrefixB b!"https://" a || isPrefixB b!"$scheme" a then .ok (302, some a)
      else .error s!"invalid return code \"{toStr a}\""
  | [a, t] =>
    match parseNat? a with
    | some c => if c ≤ 999 then .ok (c, some t) else .error "invalid return code"
    | none => .error s!"invalid return code \"{toStr a}\""
  | _ => .error "invalid number of arguments in \"return\" directive"

/-! ### Elaboration -/

/-- Tuning knobs of nginx's process model and buffers: accepted silently, no effect. -/
def silentDirectives : List Bytes :=
  [b!"worker_connections", b!"pid", b!"sendfile", b!"tcp_nopush",
   b!"tcp_nodelay", b!"types_hash_max_size", b!"types_hash_bucket_size",
   b!"server_names_hash_bucket_size", b!"server_names_hash_max_size", b!"multi_accept",
   b!"use", b!"worker_rlimit_nofile", b!"client_body_buffer_size", b!"keepalive_requests",
   b!"reset_timedout_connection", b!"open_file_cache", b!"client_header_timeout",
   b!"client_body_timeout", b!"send_timeout", b!"proxy_http_version", b!"proxy_buffering",
   b!"proxy_read_timeout", b!"proxy_connect_timeout", b!"proxy_send_timeout",
   b!"port_in_redirect",
   b!"ssl_protocols", b!"ssl_ciphers", b!"ssl_prefer_server_ciphers", b!"ssl_session_cache",
   b!"ssl_session_timeout", b!"ssl_session_tickets", b!"ssl_stapling", b!"ssl_stapling_verify",
   b!"ssl_trusted_certificate", b!"ssl_dhparam", b!"ssl_ecdh_curve", b!"ssl_buffer_size",
   b!"ssl_early_data", b!"http2"]

/-- Accepted for compatibility but with no effect that a client could notice: warned about. -/
def ignoredDirectives : List Bytes :=
  [b!"log_format", b!"gzip_proxied", b!"gzip_http_version", b!"gzip_buffers",
   b!"gzip_disable", b!"gzip_static", b!"charset", b!"proxy_redirect", b!"etag",
   b!"if_modified_since", b!"expires"]

abbrev Elab := StateT (List String) (Except String)

def warn (m : String) : Elab Unit := modify (· ++ [m])

def needArgs (d : Directive) (lo hi : Nat) : Elab Unit := do
  let n := d.args.length
  unless lo ≤ n && n ≤ hi do
    throw s!"invalid number of arguments in \"{toStr d.name}\" directive"

def noBlock (d : Directive) : Elab Unit :=
  if d.block.isSome then throw s!"directive \"{toStr d.name}\" has no opening \"\{\"" else pure ()

/-- Settings directives valid at http, server and location level. Returns `none` if `d`
is not one of them. -/
def elabSetting (s : Settings) (d : Directive) : Elab (Option Settings) := do
  let n := d.name
  if n == b!"root" then
    needArgs d 1 1; noBlock d; return some { s with root := d.args.head? }
  if n == b!"index" then
    needArgs d 1 64; noBlock d; return some { s with index := some d.args }
  if n == b!"autoindex" then
    noBlock d; let v ← liftM (onOff n d.args); return some { s with autoindex := some v }
  if n == b!"add_header" then
    needArgs d 2 3; noBlock d
    match d.args with
    | [_, _, flag] =>
      throw s!"the \"{toStr flag}\" parameter of \"add_header\" is not supported: leannginx applies add_header only to 2xx/3xx responses, so headers would be silently missing on error responses. Use the two-argument form."
    | k :: v :: _ =>
      unless isToken k && validValue v do throw "invalid header in \"add_header\" directive"
      return some { s with addHeaders := some (s.addHeaders.getD [] ++ [(k, v)]) }
    | _ => throw "invalid number of arguments in \"add_header\" directive"
  if n == b!"error_page" then
    needArgs d 2 64; noBlock d
    let uri := d.args.getLast!
    let codes := d.args.dropLast
    let mut pages := s.errorPages.getD []
    for c in codes do
      match parseNat? c with
      | some k => if 300 ≤ k && k ≤ 599 then pages := pages ++ [(k, uri)]
                  else throw s!"value \"{toStr c}\" must be between 300 and 599"
      | none => throw s!"invalid value \"{toStr c}\" (\"=code\" responses are not supported)"
    return some { s with errorPages := some pages }
  if n == b!"default_type" then
    needArgs d 1 1; noBlock d; return some { s with defaultType := d.args.head? }
  if n == b!"ssl_certificate" then
    needArgs d 1 1; noBlock d; return some { s with sslCert := d.args.head? }
  if n == b!"ssl_certificate_key" then
    needArgs d 1 1; noBlock d; return some { s with sslKey := d.args.head? }
  if n == b!"gzip" then
    noBlock d; let v ← liftM (onOff n d.args); return some { s with gzip := some v }
  if n == b!"gzip_vary" then
    noBlock d; let v ← liftM (onOff n d.args); return some { s with gzipVary := some v }
  if n == b!"gzip_types" then
    needArgs d 1 256; noBlock d; return some { s with gzipTypes := some (d.args.map lowerB) }
  if n == b!"gzip_min_length" then
    needArgs d 1 1; noBlock d
    match parseSize d.args.head! with
    | some v => return some { s with gzipMinLength := some v }
    | none => throw "\"gzip_min_length\" directive invalid value"
  if n == b!"gzip_comp_level" then
    needArgs d 1 1; noBlock d
    match parseNat? d.args.head! with
    | some v => if 1 ≤ v && v ≤ 9 then return some { s with gzipLevel := some v }
                else throw "\"gzip_comp_level\" must be between 1 and 9"
    | none => throw "\"gzip_comp_level\" directive invalid value"
  if n == b!"auth_basic" then
    needArgs d 1 1; noBlock d
    let a := d.args.head!
    return some { s with authBasic := some (if a == b!"off" then none else some a) }
  if n == b!"auth_basic_user_file" then
    needArgs d 1 1; noBlock d; return some { s with authUserFile := d.args.head? }
  if n == b!"client_max_body_size" then
    needArgs d 1 1; noBlock d
    match parseSize d.args.head! with
    | some v => return some { s with maxBody := some v }
    | none => throw "\"client_max_body_size\" directive invalid value"
  return none

/-- Unsupported directives whose *silent* acceptance would turn off a protection the operator
asked for. These fail `nginx -t` with an explanation, so the operator is never left trusting a
defence that is not in effect (a stock nginx honours each of these). -/
def securityRejected : List (Bytes × String) :=
  [(b!"proxy_set_header",
      "leannginx does not rewrite upstream request headers, so a rule meant to sanitize a client-controlled header (e.g. clearing X-Forwarded-For or Authorization before the backend sees it) would do nothing. Remove it, or do not proxy with leannginx."),
   (b!"user",
      "leannginx does not drop privileges, so running it as root to bind ports 80/443 would stay root. Run it as a non-root user instead."),
   (b!"absolute_redirect",
      "leannginx always builds absolute redirects from the request Host, so \"absolute_redirect off\" (set to stop Host-header redirect poisoning) would have no effect."),
   (b!"server_name_in_redirect",
      "leannginx redirects always use the request Host; this directive would have no effect.")]

def elabIgnored (d : Directive) : Elab Bool := do
  if let some reason := securityRejected.lookup d.name then
    throw s!"directive \"{toStr d.name}\" is not supported and silently accepting it would disable a protection: {reason}"
  if silentDirectives.contains d.name then return true
  if ignoredDirectives.contains d.name then
    warn s!"directive \"{toStr d.name}\" is accepted but has no effect in leannginx"
    return true
  if d.name == b!"events" && d.block.isSome then return true
  if d.name == b!"error_log" then return true
  return false

def unknown (d : Directive) (ctx : String) : Elab α :=
  throw s!"unknown directive \"{toStr d.name}\" (or not allowed in {ctx})"

def elabLocation (d : Directive) : Elab Location := do
  let (kind, uri) ← match d.args with
    | [u] =>
      if u.head? == some 64 then throw "named locations (@name) are not supported"
      pure (LocKind.pre, u)
    | [m, u] =>
      if m == b!"=" then pure (LocKind.exact, u)
      else if m == b!"^~" then pure (LocKind.noRegex, u)
      else if m == b!"~" || m == b!"~*" then
        match compileRegex (m == b!"~*") u with
        | .ok re => pure (LocKind.regex re, u)
        | .error e => throw s!"{e} in location \"{toStr u}\""
      else throw s!"invalid location modifier \"{toStr m}\""
    | _ => throw "invalid number of arguments in \"location\" directive"
  let isRegex := match kind with | .regex _ => true | _ => false
  unless isRegex || uri.head? == some 47 do throw s!"location \"{toStr uri}\" must start with \"/\""
  let some body := d.block | throw "directive \"location\" has no opening \"{\""
  let mut l : Location := { kind, uri }
  for c in body do
    if let some s ← elabSetting l.s c then l := { l with s }; continue
    if ← elabIgnored c then continue
    let n := c.name
    if n == b!"alias" then
      needArgs c 1 1; noBlock c; l := { l with alias := c.args.head? }
    else if n == b!"return" then
      noBlock c; let r ← liftM (parseReturn c.args); l := { l with ret := some r }
    else if n == b!"try_files" then
      needArgs c 2 64; noBlock c; l := { l with tryFiles := some c.args }
    else if n == b!"proxy_pass" then
      needArgs c 1 1; noBlock c; let u ← liftM (parseUpstream c.args.head!)
      if isRegex && u.uri.isSome then
        throw "\"proxy_pass\" cannot have a URI part in a location given by a regular expression"
      l := { l with proxy := some u }
    else if n == b!"location" then throw "nested locations are not supported by leannginx"
    else unknown c "location"
  if isRegex && l.alias.isSome then
    throw "\"alias\" in a regex location needs captures, which leannginx does not support; use \"root\""
  if l.alias.isSome && l.s.root.isSome then throw "\"alias\" directive is duplicate, \"root\" directive was specified earlier"
  pure l

def elabServer (d : Directive) : Elab Server := do
  let some body := d.block | throw "directive \"server\" has no opening \"{\""
  let mut sv : Server := {}
  for c in body do
    if let some s ← elabSetting sv.s c then sv := { sv with s }; continue
    if ← elabIgnored c then continue
    let n := c.name
    if n == b!"listen" then
      noBlock c; let l ← liftM (parseListen c.args); sv := { sv with listens := sv.listens ++ [l] }
    else if n == b!"server_name" then
      needArgs c 1 64; noBlock c
      if c.args.any (·.head? == some 126) then throw "regex server names are not supported"
      sv := { sv with names := sv.names ++ c.args.map lowerB }
    else if n == b!"location" then
      let l ← elabLocation c; sv := { sv with locations := sv.locations ++ [l] }
    else if n == b!"return" then
      noBlock c; let r ← liftM (parseReturn c.args); sv := { sv with ret := some r }
    else unknown c "server"
  if sv.listens.isEmpty then sv := { sv with listens := [{ addr := none, port := 80, default := false }] }
  pure sv

def elabTypes (d : Directive) : Elab (List (Bytes × Bytes)) := do
  let some body := d.block | throw "directive \"types\" has no opening \"{\""
  let mut out := []
  for c in body do
    noBlock c
    for ext in c.args do out := out ++ [(lowerB ext, c.name)]
  pure out

def elabHttp (d : Directive) : Elab HttpConf := do
  let some body := d.block | throw "directive \"http\" has no opening \"{\""
  let mut h : HttpConf := {}
  for c in body do
    if let some s ← elabSetting h.s c then h := { h with s }; continue
    if ← elabIgnored c then continue
    let n := c.name
    if n == b!"server" then
      let sv ← elabServer c; h := { h with servers := h.servers ++ [{ sv with idx := h.servers.length }] }
    else if n == b!"types" then
      let t ← elabTypes c; h := { h with types := t ++ h.types }
    else if n == b!"access_log" then
      needArgs c 1 4; noBlock c
      h := { h with accessLog := if c.args.head! == b!"off" then none else c.args.head? }
    else if n == b!"keepalive_timeout" then
      needArgs c 1 2; noBlock c
      match parseTime c.args.head! with
      | some t => h := { h with keepaliveTimeout := t }
      | none => throw "\"keepalive_timeout\" directive invalid value"
    else if n == b!"server_tokens" then
      noBlock c; let v ← liftM (onOff n c.args); h := { h with serverTokens := v }
    else unknown c "http"
  pure h

/-- Elaborate the directive tree (after `include` expansion). Returns the config and warnings. -/
def elabConfig (ds : List Directive) : Except String (Config × List String) :=
  (go ds).run []
where
  go (ds : List Directive) : Elab Config := do
    let mut cfg : Config := {}
    let mut seenHttp := false
    for d in ds do
      if d.name == b!"http" then
        if seenHttp then throw "\"http\" directive is duplicate"
        seenHttp := true
        let h ← elabHttp d; cfg := { cfg with http := h }
      else if d.name == b!"error_log" then
        cfg := { cfg with errorLog := d.args.head? }
      else if d.name == b!"worker_processes" then
        needArgs d 1 1; noBlock d
        let a := d.args.head!
        if a == b!"auto" then cfg := { cfg with workers := none }
        else match parseNat? a with
          | some n => if n ≥ 1 then cfg := { cfg with workers := some n }
                      else throw "invalid value \"0\" in \"worker_processes\" directive"
          | none => throw s!"invalid value \"{toStr a}\" in \"worker_processes\" directive"
      else if d.name == b!"events" && d.block.isSome then
        for e in d.block.getD [] do
          if e.name == b!"worker_connections" then
            needArgs e 1 1; noBlock e
            match parseNat? e.args.head! with
            | some n => if n ≥ 1 then cfg := { cfg with workerConnections := n }
                        else throw "invalid value \"0\" in \"worker_connections\" directive"
            | none => throw s!"invalid value \"{toStr e.args.head!}\" in \"worker_connections\" directive"
      else if ← elabIgnored d then continue
      else unknown d "main"
    unless seenHttp do throw "no \"http\" block in the configuration"
    pure cfg

end LeanNginx

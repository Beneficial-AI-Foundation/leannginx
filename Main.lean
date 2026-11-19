import LeanNginx
import LeanTLS.Server
import Zip.Native.Gzip
import Std.Async
import Std.Data.HashMap
/-!
# lnginx — the IO shell

Everything that touches sockets, files and clocks lives here; every decision is made by the
pure, specified code in `LeanNginx/`: request parsing (`parseRequest`), path normalisation
(`normalizePath`), location/server selection and file mapping (`route`), responses
(`fileResponse`, `renderHead`, `errorPage`, `autoindexPage`). Not covered by specs: this file.

Networking uses Lean's built-in `Std.Async` (libuv); TLS 1.3 comes from LeanTLS
(`LeanTLS.Server`). There is no hand-written C.
-/
open Std.Async Std.Net LeanNginx

def version : String := "0.1.0"

/-! ## Small helpers -/

def bytesOf (b : Bytes) : ByteArray := ⟨b.toArray⟩

def nowSecs : IO Int := return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

def eprintln (s : String) : IO Unit := IO.eprintln s!"lnginx: {s}"

def isAbs (b : Bytes) : Bool := b.head? == some 47

def resolveIn (dir : Bytes) (p : Bytes) : Bytes := if isAbs p then p else dir ++ [47] ++ p

def addrString : SocketAddress → String
  | .v4 a => (IPAddr.v4 a.addr).toString
  | .v6 a => (IPAddr.v6 a.addr).toString

/-! ## Configuration loading -/

/-- `*` in the last path component (`conf.d/*.conf`). -/
def globMatch (pat name : String) : Bool :=
  match pat.splitOn "*" with
  | [p] => p == name
  | [a, b] => name.startsWith a && name.endsWith b && name.length ≥ a.length + b.length
  | _ => false

def globFiles (path : String) : IO (List String) := do
  let fp : System.FilePath := path
  match fp.fileName with
  | some fn =>
    if fn.contains '*' then
      let dir := fp.parent.getD "."
      let entries ← dir.readDir
      let names := entries.toList.map (·.fileName) |>.filter (globMatch fn) |>.mergeSort (· ≤ ·)
      return names.map fun (n : String) => (dir / n).toString
    else return [path]
  | none => return [path]

partial def expandIncludes (confDir : Bytes) (depth : Nat) : List Directive → IO (List Directive)
  | [] => pure []
  | d :: ds => do
    let rest ← expandIncludes confDir depth ds
    if d.name == b!"include" then
      if depth > 10 then throw (IO.userError "include nesting too deep")
      let [pat] := d.args | throw (IO.userError "invalid number of arguments in \"include\" directive")
      let files ← globFiles (toStr (resolveIn confDir pat))
      let mut out := []
      for f in files do
        let txt ← try IO.FS.readBinFile f catch e =>
          throw (IO.userError s!"open() \"{f}\" failed ({e})")
        match parseDirectives txt.toList with
        | .ok sub => out := out ++ (← expandIncludes confDir (depth + 1) sub)
        | .error e => throw (IO.userError s!"{e} in {f}")
      pure (out ++ rest)
    else match d.block with
      | some b => pure (.mk d.name d.args (some (← expandIncludes confDir depth b)) :: rest)
      | none => pure (d :: rest)

def absSettings (pfx : Bytes) (s : Settings) : Settings :=
  { s with root := (resolveIn pfx ·) <$> s.root }

/-- Relative `root`/`alias` paths are relative to the prefix, as in nginx. -/
def absolutize (pfx : Bytes) (c : Config) : Config :=
  let http := c.http
  let hs := absSettings pfx { http.s with root := http.s.root <|> some defaultRoot }
  let servers := http.servers.map fun sv =>
    { sv with s := absSettings pfx sv.s,
              locations := sv.locations.map fun l =>
                { l with s := absSettings pfx l.s, alias := (resolveIn pfx ·) <$> l.alias } }
  { c with http := { http with s := hs, servers } }

def loadConfig (pfx confFile : String) : IO (Config × List String) := do
  let txt ← try IO.FS.readBinFile confFile catch e =>
    throw (IO.userError s!"open() \"{confFile}\" failed ({e})")
  let ds ← match parseDirectives txt.toList with
    | .ok ds => pure ds
    | .error e => throw (IO.userError s!"{e} in {confFile}")
  let confDir := ((confFile : System.FilePath).parent.getD ".").toString
  let ds ← expandIncludes (ofStr confDir) 0 ds
  match elabConfig ds with
  | .ok (cfg, warns) => pure (absolutize (ofStr pfx) cfg, warns)
  | .error e => throw (IO.userError s!"{e} in {confFile}")

/-! ## Environment -/

/-- A socket whose reads have a deadline, enforced by the watchdog (`sweeper`). -/
structure Watch where
  sock : TCP.Socket.Client
  /-- Monotonic milliseconds by which the pending read must finish; 0 = no read pending. -/
  deadline : IO.Ref Nat

abbrev Registry := Std.Mutex (Std.HashMap Nat Watch)

/-- A cached small file: its bytes and, once asked for, its gzip encoding at one level. -/
structure CachedFile where
  size : Nat
  mtime : Int
  data : ByteArray
  gz : Option (Nat × ByteArray) := none

/-- Small-file cache (like nginx's `open_file_cache`, plus compressed copies). -/
structure FileCache where
  files : Std.HashMap String CachedFile := {}
  bytes : Nat := 0

structure Env where
  cfg : Config
  log : Option (Std.Mutex IO.FS.Handle)
  /-- TLS identity of each server (by `Server.idx`), for servers with `listen … ssl`. -/
  idents : Array (Option LeanTLS.Server.Identity) := #[]
  /-- Every open socket with its read deadline. -/
  watches : Registry
  nextId : IO.Ref Nat
  /-- `(second, "Date" value)`, so the date is formatted once a second, not per response. -/
  dateCache : IO.Ref (Int × Bytes)
  fileCache : Std.Mutex FileCache

def Env.http (e : Env) : HttpConf := e.cfg.http

/-! ## File system -/

def statPath (p : Bytes) : IO (Option Kind) := do
  match toStrStrict? p with
  | none => pure none
  | some s =>
    try
      let m ← System.FilePath.metadata s
      match m.type with
      | .dir => pure (some .dir)
      | .file => pure (some (.file m.byteSize.toNat m.modified.sec))
      | _ => pure none
    catch _ => pure none

/-- Interpret a stat program with real `stat` calls. -/
def runStep : Step → IO Action
  | .done a => pure a
  | .stat p k => do
    let r ← statPath p
    runStep (k r)

def listDir (p : Bytes) : IO (List Entry) := do
  let some s := toStrStrict? p | return []
  let es ← (s : System.FilePath).readDir
  let mut out := []
  for e in es do
    try
      let m ← e.path.metadata
      out := { name := ofStr e.fileName, isDir := m.type == .dir, size := m.byteSize.toNat,
               mtime := m.modified.sec } :: out
    catch _ => pure ()
  return out

/-! ## Sockets -/

/-- Receive with a timeout: `none` = timed out, `some none` = peer closed.

A read only records its deadline; one watchdog task per server (`sweeper`) checks all deadlines
once a second and cancels overdue reads (`cancelRecv` resolves the read's promise to `none`).
This costs one libuv operation per read instead of four (a timer per read, or `Selectable.one`,
which on Lean 4.35 costs ~4x throughput). Timeouts are therefore accurate to about a second, as
in nginx. After a timeout the caller closes the connection. -/
def recvW (w : Watch) (ms : Nat) : Async (Option (Option ByteArray)) := do
  w.deadline.set ((← IO.monoMsNow) + ms)
  let p ← w.sock.native.recv? 65536
  let r ← MonadAwait.await p.result?
  w.deadline.set 0
  match r with
  | none => return none
  | some (.ok v) => return some v
  | some (.error e) => throw e

/-- The watchdog: once a second, cancel every read that is past its deadline. -/
partial def sweeper (reg : Registry) : Async Unit := do
  Std.Async.sleep 1000
  let now ← IO.monoMsNow
  let ws ← reg.atomically do return (← get).toArray
  for (_, w) in ws do
    let d ← w.deadline.get
    if d != 0 && now ≥ d then w.sock.native.cancelRecv
  sweeper reg

/-- Register a socket with the watchdog for the duration of `k`. -/
def withWatch (env : Env) (c : TCP.Socket.Client) (k : Watch → Async α) : Async α := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  let w : Watch := { sock := c, deadline := ← IO.mkRef 0 }
  env.watches.atomically (modify (·.insert id w))
  try k w finally env.watches.atomically (modify (·.erase id))

/-- A client connection: plain TCP or TLS. -/
structure Link where
  /-- `none` = timed out, `some none` = closed. -/
  recv : Nat → Async (Option (Option ByteArray))
  send : ByteArray → Async Unit
  close : Async Unit
  /-- `http` or `https` -/
  scheme : Bytes

def tcpLink (w : Watch) : Link where
  recv := recvW w
  send := w.sock.send
  close := do try w.sock.shutdown catch _ => pure ()
  scheme := b!"http"

def tlsLink (t : LeanTLS.Server.Conn) (c : TCP.Socket.Client) : Link where
  recv := t.read
  send := t.write
  close := do t.close; try c.shutdown catch _ => pure ()
  scheme := b!"https"

def sendB (c : Link) (b : Bytes) : Async Unit := c.send (bytesOf b)

def closeConn (c : Link) : Async Unit := do
  try c.close catch _ => pure ()

def maxHead : Nat := 32768

inductive HeadRes where
  | ok (head : ByteArray) (rest : ByteArray)
  | closed
  | timeout
  | tooLarge

def dropLeadingNewlines (b : ByteArray) : ByteArray := Id.run do
  let mut i := 0
  while i < b.size && (b.get! i == 10 || b.get! i == 13) do i := i + 1
  return if i == 0 then b else b.extract i b.size

partial def readHead (c : Link) (buf : ByteArray) (ms : Nat) : Async HeadRes := do
  let buf := dropLeadingNewlines buf
  match findHeadEnd buf with
  | some (h, b) =>
    if h > maxHead then return .tooLarge
    pure (.ok (buf.extract 0 h) (buf.extract b buf.size))
  | none =>
    if buf.size > maxHead then return .tooLarge
    match ← c.recv ms with
    | none => pure (if buf.size == 0 then .closed else .timeout)
    | some none => pure .closed
    | some (some d) => readHead c (buf ++ d) ms

partial def readBody (c : Link) (buf : ByteArray) (n : Nat) (ms : Nat) :
    Async (Option ByteArray) := do
  if buf.size ≥ n then return some buf
  match ← c.recv ms with
  | some (some d) => readBody c (buf ++ d) n ms
  | _ => return none

/-! ## Responses -/

structure Out where
  status : Nat
  sent : Nat
  keep : Bool

/-- The `Date` value for `now`, formatted at most once a second. -/
def dateFor (env : Env) (now : Int) : BaseIO Bytes := do
  let (t, d) ← env.dateCache.get
  if t == now then return d
  let d := httpDate now
  env.dateCache.set (now, d)
  return d

def baseHeaders (env : Env) (now : Int) : List (Bytes × Bytes) :=
  [(b!"Server", serverName env.http.serverTokens), (b!"Date", httpDate now)]

def cacheMaxFile : Nat := 1048576
def cacheMaxBytes : Nat := 67108864

/-- Bytes of a file the router just `stat`ed with this size and mtime. Small files that have not
changed for 2 seconds are kept in memory, keyed by path and checked against size and mtime, so a
modified file is never served from the cache. -/
def readFileCached (env : Env) (path : String) (size : Nat) (mtime : Int) : IO ByteArray := do
  if size > cacheMaxFile then return ← IO.FS.readBinFile path
  let hit ← env.fileCache.atomically do
    return (← get).files.get? path |>.filter fun e => e.size == size && e.mtime == mtime
  if let some e := hit then return e.data
  let data ← IO.FS.readBinFile path
  if data.size == size && mtime + 2 ≤ (← nowSecs) then
    env.fileCache.atomically do
      let c ← get
      let c := if c.bytes + size > cacheMaxBytes then {} else c
      set { files := c.files.insert path { size, mtime, data }, bytes := c.bytes + size : FileCache }
  return data

/-- gzip of a file at `level`, cached next to the file's bytes when the file is cached. -/
def gzipCached (env : Env) (path : String) (size : Nat) (mtime : Int) (level : Nat) : IO ByteArray := do
  let hit ← env.fileCache.atomically do
    return ((← get).files.get? path).bind fun e =>
      if e.size == size && e.mtime == mtime then
        e.gz.bind fun (l, z) => if l == level then some z else none
      else none
  if let some z := hit then return z
  let data ← readFileCached env path size mtime
  let z := Zip.Native.GzipEncode.compress data level.toUInt8
  env.fileCache.atomically do
    let c ← get
    if let some e := c.files.get? path then
      if e.size == size && e.mtime == mtime then
        set { c with files := c.files.insert path { e with gz := some (level, z) },
                     bytes := c.bytes + z.size : FileCache }
  return z

def baseHeadersIO (env : Env) : IO (List (Bytes × Bytes)) := do
  let now ← nowSecs
  return [(b!"Server", serverName env.http.serverTokens), (b!"Date", ← dateFor env now)]

def connHeader (keep : Bool) : Bytes × Bytes :=
  (b!"Connection", if keep then b!"keep-alive" else b!"close")

/-- `add_header` applies to these codes (nginx without `always`). -/
def addHeaderCodes : List Nat := [200, 201, 204, 206, 301, 302, 303, 304, 307, 308]

def sendSimple (env : Env) (c : Link) (head : Bool) (keep : Bool) (code : Nat)
    (ctype : Bytes) (body : Bytes) (extra : List (Bytes × Bytes)) : Async Out := do
  let now ← nowSecs
  let hs := (← baseHeadersIO env) ++ [(b!"Content-Type", ctype),
    (b!"Content-Length", decDigits body.length)] ++ extra ++ [connHeader keep]
  sendB c (renderHead code hs ++ (if head then [] else body))
  return { status := code, sent := if head then 0 else body.length, keep }

def sendErrorPage (env : Env) (c : Link) (head keep : Bool) (code : Nat)
    (extra : List (Bytes × Bytes) := []) : Async Out := do
  -- Errors that leave the request stream in doubt close the connection, as nginx does.
  let keep := keep && !([400, 408, 413, 414, 431, 500, 501, 505].contains code)
  if code == 204 || code == 304 then
    let now ← nowSecs
    sendB c (renderHead code ((← baseHeadersIO env) ++ extra ++ [connHeader keep]))
    return { status := code, sent := 0, keep }
  sendSimple env c head keep code b!"text/html" (errorPage code env.http.serverTokens) extra

/-- Send `len` bytes of a file starting at `off`. Returns the number of bytes sent. -/
def sendFileRange (c : Link) (path : String) (off len : Nat) : Async Nat := do
  let h ← IO.FS.Handle.mk path .read
  let mut skipped := 0
  while skipped < off do
    let chunk ← h.read (min (off - skipped) 1048576).toUSize
    if chunk.isEmpty then break
    skipped := skipped + chunk.size
  let mut left := len
  while left > 0 do
    let chunk ← h.read (min left 262144).toUSize
    if chunk.isEmpty then break
    let chunk := if chunk.size > left then chunk.extract 0 left else chunk
    c.send chunk
    left := left - chunk.size
  return len - left

/-! ## Reverse proxy -/

def hopByHop : List Bytes :=
  [b!"connection", b!"keep-alive", b!"proxy-connection", b!"te", b!"trailer",
   b!"transfer-encoding", b!"upgrade", b!"host", b!"content-length", b!"expect"]

def hiddenUpstream : List Bytes :=
  [b!"connection", b!"keep-alive", b!"transfer-encoding", b!"date", b!"server", b!"x-accel-redirect"]

def connectUpstream (up : Upstream) : Async TCP.Socket.Client := do
  let addrs ← DNS.getAddrInfo up.host (toString up.port)
  let ip ← match addrs.find? (·.family == .ipv4), addrs[0]? with
    | some a, _ => pure a
    | none, some a => pure a
    | none, none => throw <| IO.userError s!"no address for {up.host}"
  let sa : SocketAddress := match ip with
    | .v4 a => .v4 { addr := a, port := up.port.toUInt16 }
    | .v6 a => .v6 { addr := a, port := up.port.toUInt16 }
  let sock ← TCP.Socket.Client.mk
  sock.connect sa
  return sock

/-- Parse an upstream status line + headers leniently. -/
def parseUpstreamHead (head : Bytes) : Option (Nat × List (Bytes × Bytes)) := do
  let line :: rest := headLines head | none
  let code ← parseNat? ((splitOnByte 32 line).getD 1 [])
  let hs := rest.filterMap fun l =>
    match splitFirst 58 l with
    | (n, some v) => some (n, trimWS v)
    | _ => none
  pure (code, hs)

partial def relay (up c : Link) (acc : Nat) : Async Nat := do
  match ← up.recv 60000 with
  | some (some d) => c.send d; relay up c (acc + d.size)
  | _ => return acc

def proxyRequest (env : Env) (c : Link) (req : Request) (body : ByteArray)
    (up : Upstream) (uri : Bytes) : Async Out := do
  let head := req.method == b!"HEAD"
  let upSock? ← try (some <$> connectUpstream up) catch e => do
    eprintln s!"connect() to {up.host}:{up.port} failed ({e}) while connecting to upstream"
    pure none
  let some sock := upSock? | sendErrorPage env c head false 502
  withWatch env sock fun uw => do
  let us := tcpLink uw
  let hostHdr := ofStr up.host ++ (if up.port == 80 then [] else 58 :: decDigits up.port)
  let fwd := req.headers.filter fun (n, _) => !hopByHop.contains n
  let reqHead := req.method ++ [32] ++ uri ++ b!" HTTP/1.0" ++ crlf ++
    renderField (b!"Host", hostHdr) ++ renderField (b!"Connection", b!"close") ++
    (if body.size > 0 || req.contentLength > 0 then renderField (b!"Content-Length", decDigits body.size) else []) ++
    fwd.flatMap renderField ++ crlf
  try
    us.send (bytesOf reqHead ++ body)
    match ← readHead us .empty 60000 with
    | .ok h rest =>
      match parseUpstreamHead h.toList with
      | none => closeConn us; sendErrorPage env c head false 502
      | some (code, hs) =>
        let now ← nowSecs
        let hs := hs.filter fun (n, _) => !hiddenUpstream.contains (lowerB n)
        sendB c (renderHead code ((← baseHeadersIO env) ++ hs ++ [connHeader false]))
        let n ← if head then pure 0 else do
          if rest.size > 0 then c.send rest
          relay us c rest.size
        closeConn us
        return { status := code, sent := n, keep := false }
    | .timeout => closeConn us; sendErrorPage env c head false 504
    | _ => closeConn us; sendErrorPage env c head false 502
  catch e =>
    eprintln s!"upstream {up.host}:{up.port}: {e}"
    sendErrorPage env c head false 502

/-! ## Request handling -/

def logEscape (b : Bytes) : String :=
  String.join <| b.map fun c =>
    if c == 34 || c == 92 || c < 32 || c ≥ 127 then
      "\\x" ++ toStr (hexUpper (c.toNat / 16) :: [hexUpper (c.toNat % 16)])
    else toString (Char.ofNat c.toNat)

/-- `19/Nov/2026:10:00:00 +0000` -/
def logTime (t : Int) : String :=
  let s := t.toNat
  let (y, m, d) := civil (s / 86400)
  let rem := s % 86400
  toStr (pad2 d ++ [47] ++ monthNames.getD (m - 1) [] ++ [47] ++ decDigits y ++ [58] ++
    pad2 (rem / 3600) ++ [58] ++ pad2 (rem % 3600 / 60) ++ [58] ++ pad2 (rem % 60)) ++ " +0000"

def accessLog (env : Env) (peer : String) (reqLine : Bytes) (req? : Option Request) (o : Out) :
    IO Unit := do
  let some m := env.log | return
  let hdr (n : Bytes) : String :=
    match req?.bind (header? ·.headers n) with
    | some v => logEscape v
    | none => "-"
  let line := s!"{peer} - - [{logTime (← nowSecs)}] \"{logEscape reqLine}\" {o.status} {o.sent} \"{hdr b!"referer"}\" \"{hdr b!"user-agent"}\"\n"
  m.atomically do
    let h ← get
    h.putStr line
    h.flush

/-- Serve one parsed request. Internal redirects (index, `try_files`, `error_page`) loop here,
at most 10 times, like nginx. -/
def handle (env : Env) (port : Nat) (peer : String) (c : Link) (req : Request)
    (body : ByteArray) : Async Out := do
  let head := req.method == b!"HEAD"
  let keep := req.keepAlive
  let some sv := selectServer env.http.servers port req.host
    | sendErrorPage env c head false 500
  let host := req.host.getD ((sv.names.find? (fun n => !n.isEmpty && n != b!"_")).getD b!"localhost")
  let some np0 := normalizePath req.path | sendErrorPage env c head false 400
  let mut np := np0
  let mut query := req.query
  let mut method := req.method
  let mut errCode : Option Nat := none
  for _ in [0:10] do
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    let eff := effective env.http sv l
    let vars : Vars := { uri := np.uri, requestUri := req.target, args := query.getD [],
                         host, method, remoteAddr := ofStr peer, serverPort := decDigits port,
                         scheme := c.scheme }
    let addH (code : Nat) := if addHeaderCodes.contains code then eff.addHeaders.getD [] else []
    let a ← runStep (route env.http sv { req with method, query } vars np)
    match a with
    | .internal u =>
      let (p, q) := splitTarget u
      match normalizePath p with
      | some np' => np := np'; if q.isSome then query := q
      | none => return ← sendErrorPage env c head keep 500
    | .error code =>
      match errCode, (eff.errorPages.getD []).lookup code with
      | none, some page =>
        errCode := some code
        if method != b!"HEAD" then method := b!"GET"
        let (p, q) := splitTarget page
        if isPrefixB b!"http://" p || isPrefixB b!"https://" p then
          return ← sendErrorPage env c head keep 302 [(b!"Location", page)]
        match normalizePath p with
        | some np' => np := np'; query := q
        | none => return ← sendErrorPage env c head keep code
      | some orig, _ => return ← sendErrorPage env c head keep orig
      | none, none => return ← sendErrorPage env c head keep code (if code == 405 then [] else addH code)
    | .file path size mtime =>
      let mime := mimeFor env.http.types (eff.defaultType.getD b!"text/plain") path
      let some pathS := toStrStrict? path | return ← sendErrorPage env c head keep 404
      let fr : FileResp := match errCode with
        | some code => { status := code, body := some (0, size),
                         headers := [(b!"Content-Type", mime), (b!"Content-Length", decDigits size)] }
        | none => fileResponse req mime size mtime
      let now ← nowSecs
      -- gzip (lean-zip): whole files up to 16 MiB, 200 responses only
      if fr.status == 200 && errCode.isNone && gzipApplies eff req mime size && size ≤ 16777216 then
        let z ← gzipCached env pathS size mtime (eff.gzipLevel.getD 1)
        let hs := [(b!"Content-Type", mime), (b!"Last-Modified", httpDate mtime),
          (b!"ETag", weakEtag (etag size mtime)), (b!"Content-Encoding", b!"gzip"),
          (b!"Content-Length", decDigits z.size)] ++
          (if eff.gzipVary.getD false then [(b!"Vary", b!"Accept-Encoding")] else [])
        sendB c (renderHead 200 ((← baseHeadersIO env) ++ hs ++ addH 200 ++ [connHeader keep]))
        unless head do c.send z
        return { status := 200, sent := if head then 0 else z.size, keep }
      let hdr := renderHead fr.status ((← baseHeadersIO env) ++ fr.headers ++ addH fr.status ++ [connHeader keep])
      match fr.body, head with
      | some (off, len), false =>
        -- small whole files: header and body in one write (one event-loop operation)
        if off == 0 && len == size && size ≤ 65536 then
          let data ← readFileCached env pathS size mtime
          if data.size == size then
            c.send (bytesOf hdr ++ data)
            return { status := fr.status, sent := size, keep }
        sendB c hdr
        let n ← sendFileRange c pathS off len
        return { status := fr.status, sent := n, keep := keep && n == len }
      | _, _ => sendB c hdr; return { status := fr.status, sent := 0, keep }
    | .autoindex dir =>
      let es ← listDir dir
      return ← sendSimple env c head keep 200 b!"text/html" (autoindexPage np.uri es) (addH 200)
    | .redirect code loc =>
      let dfltPort := if c.scheme == b!"https" then 443 else 80
      let loc := if isAbs loc then
          c.scheme ++ b!"://" ++ host ++ (if port == dfltPort then [] else 58 :: decDigits port) ++ loc
        else loc
      return ← sendSimple env c head keep code b!"text/html" (errorPage code env.http.serverTokens)
        ([(b!"Location", loc)] ++ addH code)
    | .text code t =>
      return ← sendSimple env c head keep code (eff.defaultType.getD b!"text/plain") t (addH code)
    | .close => return { status := 444, sent := 0, keep := false }
    | .proxy up uri => return ← proxyRequest env c req body up uri
  eprintln s!"rewrite or internal redirection cycle while processing \"{toStr np.uri}\""
  sendErrorPage env c head keep 500

def firstLine (h : ByteArray) : Bytes := (headLines (h.extract 0 (min h.size 8192)).toList).headD []

partial def connLoop (env : Env) (port : Nat) (peer : String) (c : Link)
    (buf : ByteArray) (first : Bool) : Async Unit := do
  let ms := if first then 60000 else env.http.keepaliveTimeout * 1000
  match ← readHead c buf ms with
  | .closed | .timeout => closeConn c
  | .tooLarge =>
    let o ← sendErrorPage env c false false 431
    accessLog env peer [] none o
    closeConn c
  | .ok h rest =>
    let reqLine := firstLine h
    match parseRequest h.toList with
    | .error code =>
      let o ← sendErrorPage env c false false code
      accessLog env peer reqLine none o
      closeConn c
    | .ok req =>
      let maxBody := (env.http.s.maxBody).getD (1024 * 1024)
      if maxBody != 0 && req.contentLength > maxBody then
        let o ← sendErrorPage env c (req.method == b!"HEAD") false 413
        accessLog env peer reqLine (some req) o
        closeConn c
        return
      if req.contentLength > 0 && rest.size < req.contentLength &&
          (header? req.headers b!"expect").map lowerB == some b!"100-continue" then
        sendB c (b!"HTTP/1.1 100 Continue" ++ crlf ++ crlf)
      match ← readBody c rest req.contentLength 60000 with
      | none => closeConn c
      | some all =>
        let body := all.extract 0 req.contentLength
        let rest := all.extract req.contentLength all.size
        let o ← handle env port peer c req body
        accessLog env peer reqLine (some req) o
        if o.keep then connLoop env port peer c rest false else closeConn c

/-- The TLS identity for an SNI name on `port`: the matching server's, else the port's default. -/
def pickIdentity (env : Env) (port : Nat) (sni : Option String) : Option LeanTLS.Server.Identity :=
  let host := sni.map fun s => lowerB (ofStr s)
  let ofServer (sv : Server) := (env.idents[sv.idx]?).join
  match (selectServer env.http.servers port host).bind ofServer with
  | some i => some i
  | none => (serversOn env.http.servers port).findSome? ofServer

/-- nginx's answer to plain HTTP on a TLS port. -/
def plainOnTlsPage (tokens : Bool) : Bytes :=
  b!"<html>\r\n<head><title>400 The plain HTTP request was sent to HTTPS port</title></head>\r\n<body>\r\n<center><h1>400 Bad Request</h1></center>\r\n<center>The plain HTTP request was sent to HTTPS port</center>\r\n<hr><center>" ++
    serverName tokens ++ b!"</center>\r\n</body>\r\n</html>\r\n"

def serveConn (env : Env) (port : Nat) (ssl : Bool) (c : TCP.Socket.Client) : Async Unit :=
  withWatch env c fun w => do
  let peer ← try (addrString <$> c.getPeerName) catch _ => pure "-"
  let plain := tcpLink w
  if !ssl then
    try connLoop env port peer plain .empty true
    catch _ => closeConn plain
    return
  let tr : LeanTLS.Server.Transport := { recv := recvW w, send := c.send }
  try
    match ← LeanTLS.Server.accept tr (pickIdentity env port) 60000 with
    | .tls t => connLoop env port peer (tlsLink t c) .empty true
    | .plain _ =>
      let o ← sendSimple env plain false false 400 b!"text/html" (plainOnTlsPage env.http.serverTokens) []
      accessLog env peer [] none o
      closeConn plain
    | .failed _ => closeConn plain
  catch _ => closeConn plain

/-! ## Listeners and main -/

structure Bound where
  sock : TCP.Socket.Server
  port : Nat
  ssl : Bool
  label : String

def bindListen (l : Listen) : IO Bound := do
  let addrS := l.addr.getD "0.0.0.0"
  let sa : SocketAddress ←
    match IPv4Addr.ofString addrS with
    | some a => pure (.v4 { addr := a, port := l.port.toUInt16 })
    | none => match IPv6Addr.ofString addrS with
      | some a => pure (.v6 { addr := a, port := l.port.toUInt16 })
      | none => throw (IO.userError s!"host not found in \"{addrS}:{l.port}\" of the \"listen\" directive")
  let s ← TCP.Socket.Server.mk
  try
    s.bind sa
    s.listen 511
  catch e => throw (IO.userError s!"bind() to {addrS}:{l.port} failed ({e})")
  let shown := if addrS == "0.0.0.0" then "localhost" else if addrS.contains ':' then s!"[{addrS}]" else addrS
  let scheme := if l.ssl then "https" else "http"
  return { sock := s, port := l.port, ssl := l.ssl, label := s!"{scheme}://{shown}:{l.port}/" }

partial def acceptLoop (env : Env) (b : Bound) : Async Unit := do
  let c ← try (some <$> b.sock.accept) catch e => do eprintln s!"accept() failed ({e})"; pure none
  if let some c := c then background (serveConn env b.port b.ssl c)
  acceptLoop env b

def usage : String :=
"Usage: lnginx [-?hvVt] [-p prefix] [-c filename]

Options:
  -?,-h         : this help
  -v            : show version and exit
  -V            : show version and what is verified, then exit
  -t            : test configuration and exit
  -p prefix     : set prefix path (default: current directory)
  -c filename   : set configuration file (default: conf/nginx.conf)
"

structure Opts where
  pfx : Option String := none
  conf : Option String := none
  test : Bool := false

def parseOpts : List String → Opts → Except String (Option Opts)
  | [], o => .ok (some o)
  | "-p" :: p :: rest, o => parseOpts rest { o with pfx := some p }
  | "-c" :: f :: rest, o => parseOpts rest { o with conf := some f }
  | "-t" :: rest, o => parseOpts rest { o with test := true }
  | a :: _, _ =>
    if a == "-h" || a == "-?" || a == "--help" || a == "-v" || a == "-V" then .ok none
    else .error s!"invalid option: \"{a}\""

def absPath (cwd : System.FilePath) (p : String) : String :=
  if p.startsWith "/" then p else (cwd / p).toString

def main (args : List String) : IO UInt32 := do
  if args.contains "-v" || args.contains "-V" then
    IO.println s!"lnginx version: leannginx/{version} (Lean 4, compiled to C)"
    if args.contains "-V" then
      IO.println "verified (lake build): request parsing, path normalisation, location matching,\n  regex matching, file confinement under root/alias, header sanitising, byte ranges\n  (see LeanNginx/Spec.lean)\nTLS 1.3 server: LeanTLS (ChaCha20-Poly1305, X25519/P-256, ECDSA P-256 or RSA-PSS certificates)\ngzip: lean-zip (decompress (compress x) = x, proved)"
    return 0
  let opts ← match parseOpts args {} with
    | .ok (some o) => pure o
    | .ok none => IO.print usage; return 0
    | .error e => eprintln e; IO.eprint usage; return 1
  let cwd ← IO.currentDir
  let pfx : String := String.ofList ((match opts.pfx with | some p => absPath cwd p | none => cwd.toString).toList.reverse.dropWhile (· == '/')).reverse
  let pfx : String := if pfx.isEmpty then "/" else pfx
  let pfxPath : System.FilePath := pfx
  let confFile := match opts.conf with
    | some f => absPath cwd f
    | none => (pfxPath / "conf" / "nginx.conf").toString
  let (cfg, warns) ← try loadConfig pfx confFile catch e => do
    eprintln s!"[emerg] {e}"
    if opts.test then eprintln s!"configuration file {confFile} test failed"
    return 1
  for w in warns do eprintln s!"[warn] {w} in {confFile}"
  if opts.test then
    eprintln s!"the configuration file {confFile} syntax is ok"
    eprintln s!"configuration file {confFile} test is successful"
    return 0
  if cfg.http.servers.isEmpty then
    eprintln "[emerg] no \"server\" blocks in the \"http\" block"; return 1
  -- access log
  let log ← match cfg.http.accessLog with
    | none => pure none
    | some p =>
      let path := toStr (resolveIn (ofStr pfx) p)
      try
        if let some dir := (path : System.FilePath).parent then IO.FS.createDirAll dir
        let h ← IO.FS.Handle.mk path .append
        some <$> Std.Mutex.new h
      catch e =>
        eprintln s!"[warn] cannot open access log \"{path}\" ({e}), logging disabled"
        pure none
  -- TLS identities for servers with `listen … ssl` (paths relative to the configuration directory)
  let confDir := ofStr (((confFile : System.FilePath).parent.getD ".").toString)
  let mut idents : Array (Option LeanTLS.Server.Identity) := #[]
  for sv in cfg.http.servers do
    if sv.listens.any (·.ssl) then
      let eff := sv.s.merge cfg.http.s
      let (some certP, some keyP) := (eff.sslCert, eff.sslKey) | do
        eprintln s!"[emerg] no \"ssl_certificate\"/\"ssl_certificate_key\" for a server with \"listen ... ssl\" in {confFile}"
        return 1
      let certF := toStr (resolveIn confDir certP)
      let keyF := toStr (resolveIn confDir keyP)
      let read (f : String) : IO (Option String) := try some <$> IO.FS.readFile f catch e => do
        eprintln s!"[emerg] cannot load certificate \"{f}\": {e}"; pure none
      let (some certPem, some keyPem) := (← read certF, ← read keyF) | return 1
      match LeanTLS.Server.Identity.ofPem certPem keyPem with
      | .ok i => idents := idents.push (some i)
      | .error e => eprintln s!"[emerg] cannot load certificate \"{certF}\" / key \"{keyF}\": {e}"; return 1
    else idents := idents.push none
  let env : Env := { cfg, log, idents, watches := ← Std.Mutex.new {}, nextId := ← IO.mkRef 0,
                     dateCache := ← IO.mkRef (0, []), fileCache := ← Std.Mutex.new {} }
  -- listeners: one socket per distinct address:port (TLS if any `listen` on it says `ssl`)
  let listens := cfg.http.servers.flatMap (·.listens)
  let uniq := listens.foldl (fun acc l =>
    if acc.any (fun x => x.addr == l.addr && x.port == l.port) then
      acc.map fun x => if x.addr == l.addr && x.port == l.port then { x with ssl := x.ssl || l.ssl } else x
    else acc ++ [l]) []
  let mut bound := #[]
  for l in uniq do
    try bound := bound.push (← bindListen l)
    catch e => eprintln s!"[emerg] {e}"; return 1
  IO.eprintln s!"leannginx/{version}: prefix {pfx}, configuration {confFile}"
  for b in bound do IO.eprintln s!"  listening on {b.label}"
  IO.eprintln "  (Ctrl-C to stop)"
  let loops : Async Unit := do
    match bound.toList with
    | [] => pure ()
    | b :: bs =>
      background (sweeper env.watches)
      for x in bs do background (acceptLoop env x)
      acceptLoop env b
  loops.block
  return 0

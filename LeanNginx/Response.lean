import LeanNginx.Route
/-!
# Responses (pure)

Status lines and headers (`renderHead`), nginx-style error pages, MIME types, HTTP dates,
`ETag`/`Last-Modified`/conditional requests, byte ranges, and the autoindex listing.

Header injection is impossible by construction: `renderHead` drops every byte that is not a
legal field byte from names and values, so a CR or LF can never reach the wire inside a header
(specs `renderHead_values_safe`, `renderHead_names_safe`). Ranges are proved to stay inside the
file (`resolveRange_bounds`).
-/
namespace LeanNginx

def crlf : Bytes := [13, 10]

def reason (code : Nat) : Bytes :=
  match code with
  | 100 => b!"Continue" | 200 => b!"OK" | 201 => b!"Created" | 204 => b!"No Content"
  | 206 => b!"Partial Content" | 301 => b!"Moved Permanently" | 302 => b!"Found"
  | 303 => b!"See Other" | 304 => b!"Not Modified" | 307 => b!"Temporary Redirect"
  | 308 => b!"Permanent Redirect" | 400 => b!"Bad Request" | 401 => b!"Unauthorized"
  | 403 => b!"Forbidden" | 404 => b!"Not Found" | 405 => b!"Not Allowed"
  | 408 => b!"Request Time-out" | 409 => b!"Conflict" | 410 => b!"Gone" | 411 => b!"Length Required" | 412 => b!"Precondition Failed"
  | 413 => b!"Request Entity Too Large" | 414 => b!"Request-URI Too Large"
  | 416 => b!"Requested Range Not Satisfiable" | 429 => b!"Too Many Requests"
  | 431 => b!"Request Header Fields Too Large"
  | 500 => b!"Internal Server Error" | 501 => b!"Not Implemented" | 502 => b!"Bad Gateway"
  | 503 => b!"Service Temporarily Unavailable" | 504 => b!"Gateway Time-out"
  | 505 => b!"HTTP Version Not Supported"
  | _ => []

def statusLine (code : Nat) : Bytes :=
  b!"HTTP/1.1 " ++ decDigits code ++ (32 :: reason code) ++ crlf

def cleanName (n : Bytes) : Bytes := n.filter isTChar
def cleanValue (v : Bytes) : Bytes := v.filter fieldByteOk

def renderField (f : Bytes × Bytes) : Bytes := cleanName f.1 ++ b!": " ++ cleanValue f.2 ++ crlf

/-- Status line, header fields, empty line. -/
def renderHead (code : Nat) (hs : List (Bytes × Bytes)) : Bytes :=
  statusLine code ++ hs.flatMap renderField ++ crlf

/-! ## HTML -/

def htmlEscape : Bytes → Bytes
  | [] => []
  | c :: rest =>
    (if c == 38 then b!"&amp;" else if c == 60 then b!"&lt;" else if c == 62 then b!"&gt;"
     else if c == 34 then b!"&quot;" else [c]) ++ htmlEscape rest

def serverName (tokens : Bool) : Bytes := if tokens then b!"leannginx/0.1.0" else b!"leannginx"

/-- nginx's built-in error page. -/
def errorPage (code : Nat) (tokens : Bool) : Bytes :=
  let title := decDigits code ++ (let r := reason code; if r.isEmpty then [] else 32 :: r)
  b!"<html>\r\n<head><title>" ++ title ++ b!"</title></head>\r\n<body>\r\n<center><h1>" ++ title ++
  b!"</h1></center>\r\n<hr><center>" ++ serverName tokens ++ b!"</center>\r\n</body>\r\n</html>\r\n"

/-! ## MIME types -/

def builtinTypes : List (Bytes × Bytes) :=
  [(b!"html", b!"text/html"), (b!"htm", b!"text/html"), (b!"shtml", b!"text/html"),
   (b!"css", b!"text/css"), (b!"xml", b!"text/xml"), (b!"txt", b!"text/plain"),
   (b!"md", b!"text/markdown"), (b!"csv", b!"text/csv"),
   (b!"js", b!"application/javascript"), (b!"mjs", b!"application/javascript"),
   (b!"json", b!"application/json"), (b!"wasm", b!"application/wasm"),
   (b!"pdf", b!"application/pdf"), (b!"zip", b!"application/zip"), (b!"gz", b!"application/gzip"),
   (b!"tar", b!"application/x-tar"),
   (b!"gif", b!"image/gif"), (b!"jpeg", b!"image/jpeg"), (b!"jpg", b!"image/jpeg"),
   (b!"png", b!"image/png"), (b!"svg", b!"image/svg+xml"), (b!"svgz", b!"image/svg+xml"),
   (b!"ico", b!"image/x-icon"), (b!"webp", b!"image/webp"), (b!"avif", b!"image/avif"),
   (b!"woff", b!"font/woff"), (b!"woff2", b!"font/woff2"), (b!"ttf", b!"font/ttf"),
   (b!"otf", b!"font/otf"),
   (b!"mp3", b!"audio/mpeg"), (b!"ogg", b!"audio/ogg"), (b!"wav", b!"audio/wav"),
   (b!"mp4", b!"video/mp4"), (b!"webm", b!"video/webm"), (b!"mov", b!"video/quicktime"),
   (b!"glb", b!"model/gltf-binary"), (b!"gltf", b!"model/gltf+json"),
   (b!"obj", b!"text/plain"), (b!"ply", b!"application/octet-stream"),
   (b!"bin", b!"application/octet-stream")]

/-- Extension of the last path segment (lower case), or empty. -/
def extOf (path : Bytes) : Bytes :=
  let last := ((splitOnByte 47 path).getLast?).getD []
  match (splitOnByte 46 last) with
  | [_] | [] => []
  | parts => lowerB (parts.getLast?.getD [])

def mimeFor (types : List (Bytes × Bytes)) (dflt : Bytes) (path : Bytes) : Bytes :=
  let table := if types.isEmpty then builtinTypes else types
  (table.lookup (extOf path)).getD dflt

/-! ## Dates -/

def pad2 (n : Nat) : Bytes := if n < 10 then 48 :: decDigits n else decDigits n

def dayNames : List Bytes := [b!"Sun", b!"Mon", b!"Tue", b!"Wed", b!"Thu", b!"Fri", b!"Sat"]
def monthNames : List Bytes :=
  [b!"Jan", b!"Feb", b!"Mar", b!"Apr", b!"May", b!"Jun", b!"Jul", b!"Aug", b!"Sep", b!"Oct",
   b!"Nov", b!"Dec"]

/-- Days since 1970-01-01 → (year, month 1-12, day 1-31) (H. Hinnant's `civil_from_days`). -/
def civil (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  (y, m, d)

/-- IMF-fixdate, e.g. `Sun, 06 Nov 1994 08:49:37 GMT` (times before 1970 clamp to the epoch). -/
def httpDate (t : Int) : Bytes :=
  let s := t.toNat
  let days := s / 86400
  let rem := s % 86400
  let (y, m, d) := civil days
  dayNames.getD ((days + 4) % 7) [] ++ b!", " ++ pad2 d ++ [32] ++ monthNames.getD (m - 1) [] ++
    [32] ++ decDigits y ++ [32] ++ pad2 (rem / 3600) ++ [58] ++ pad2 (rem % 3600 / 60) ++ [58] ++
    pad2 (rem % 60) ++ b!" GMT"

/-- Autoindex style, e.g. `19-Nov-2026 10:00`. -/
def listingDate (t : Int) : Bytes :=
  let s := t.toNat
  let (y, m, d) := civil (s / 86400)
  let rem := s % 86400
  pad2 d ++ [45] ++ monthNames.getD (m - 1) [] ++ [45] ++ decDigits y ++ [32] ++
    pad2 (rem / 3600) ++ [58] ++ pad2 (rem % 3600 / 60)

/-- nginx's ETag: `"<mtime hex>-<size hex>"`. -/
def etag (size : Nat) (mtime : Int) : Bytes :=
  [34] ++ hexDigitsB mtime.toNat ++ [45] ++ hexDigitsB size ++ [34]

/-! ## Ranges (RFC 9110 §14) -/

inductive RangeRes where
  | full
  | part (first last : Nat)
  | unsat
  deriving Repr, DecidableEq

def stripPrefix? (p b : Bytes) : Option Bytes := if p.isPrefixOf b then some (b.drop p.length) else none

/-- A single `bytes=` range against a file of `size` bytes. Multiple ranges and malformed
headers are ignored (the whole file is sent), as RFC 9110 allows. -/
def resolveRange (size : Nat) (spec : Bytes) : RangeRes :=
  match stripPrefix? b!"bytes=" spec with
  | none => .full
  | some r =>
    if r.contains 44 then .full else
    match splitFirst 45 r with
    | (a, some b) =>
      if a.isEmpty then
        match parseNat? b with
        | some n => if n == 0 || size == 0 then .unsat else .part (size - min n size) (size - 1)
        | none => .full
      else match parseNat? a with
        | none => .full
        | some s =>
          if size ≤ s then .unsat
          else if b.isEmpty then .part s (size - 1)
          else match parseNat? b with
            | some e => if e < s then .full else .part s (min e (size - 1))
            | none => .full
    | _ => .full

/-! ## Static file responses -/

structure FileResp where
  status : Nat
  headers : List (Bytes × Bytes)
  /-- `(offset, length)` of the file to send; `none` = no body. -/
  body : Option (Nat × Nat)
  deriving Repr

/-- Does an `If-None-Match` list contain `tag` (weak comparison) or `*`? -/
def etagMatches (inm tag : Bytes) : Bool :=
  (splitOnByte 44 inm).any fun t =>
    let t := trimWS t
    let t := (stripPrefix? b!"W/" t).getD t
    t == tag || t == b!"*"

/-- `If-None-Match` (preferred) or `If-Modified-Since` (exact, nginx's default) matches. -/
def notModified (req : Request) (tag lm : Bytes) : Bool :=
  match header? req.headers b!"if-none-match" with
  | some inm => etagMatches inm tag
  | none => header? req.headers b!"if-modified-since" == some lm

/-- The range to send: `Range`, unless `If-Range` names another version of the file. -/
def chosenRange (req : Request) (size : Nat) (tag lm : Bytes) : RangeRes :=
  let rangeOk := match header? req.headers b!"if-range" with
    | some ir => ir == tag || ir == lm
    | none => true
  match header? req.headers b!"range" with
  | some r => if rangeOk then resolveRange size r else .full
  | none => .full

def rangeResponse (mime : Bytes) (size : Nat) (tag lm : Bytes) : RangeRes → FileResp
  | .full =>
    { status := 200, body := some (0, size),
      headers := [(b!"Content-Type", mime), (b!"Last-Modified", lm), (b!"ETag", tag),
                  (b!"Content-Length", decDigits size), (b!"Accept-Ranges", b!"bytes")] }
  | .part a b =>
    { status := 206, body := some (a, b + 1 - a),
      headers := [(b!"Content-Type", mime), (b!"Last-Modified", lm), (b!"ETag", tag),
                  (b!"Content-Length", decDigits (b + 1 - a)),
                  (b!"Content-Range", b!"bytes " ++ decDigits a ++ [45] ++ decDigits b ++ [47] ++ decDigits size)] }
  | .unsat =>
    { status := 416, body := none, headers := [(b!"Content-Range", b!"bytes */" ++ decDigits size)] }

/-- Status, headers and byte range for serving a file. -/
def fileResponse (req : Request) (mime : Bytes) (size : Nat) (mtime : Int) : FileResp :=
  let lm := httpDate mtime
  let tag := etag size mtime
  if notModified req tag lm then
    { status := 304, headers := [(b!"Last-Modified", lm), (b!"ETag", tag)], body := none }
  else rangeResponse mime size tag lm (chosenRange req size tag lm)

/-! ## gzip (the compressor itself is lean-zip's, with its roundtrip theorem) -/

/-- Does `Accept-Encoding` list `gzip` (or `*`) without `q=0`? -/
def acceptsGzip (hs : List (Bytes × Bytes)) : Bool :=
  (headerVals hs b!"accept-encoding").any fun v =>
    (splitOnByte 44 v).any fun item =>
      let parts := (splitOnByte 59 item).map (fun p => lowerB (trimWS p))
      match parts with
      | coding :: params =>
        (coding == b!"gzip" || coding == b!"*") &&
          !params.any (fun p => p == b!"q=0" || p == b!"q=0.0" || p == b!"q=0.00" || p == b!"q=0.000")
      | [] => false

/-- The MIME type without parameters, lower case. -/
def mimeBase (m : Bytes) : Bytes := lowerB (trimWS (splitFirst 59 m).1)

/-- The largest file compressed on the fly, in bytes (1 MiB). Compression holds the whole file
and lean-zip's working state in memory, about five times the file's size, so each request for a
large compressible file costs that much; without a limit, a few dozen parallel requests for a
10 MB HTML file take gigabytes. Larger files are sent uncompressed. (The same size is the
small-file cache's limit, so every compressed file is also cached and compressed only once.) -/
def gzipMaxSize : Nat := 1048576

/-- nginx's rule for compressing a response: `gzip on`, the client accepts gzip, the type is
`text/html` or listed in `gzip_types` (or `gzip_types *`), the body is at least
`gzip_min_length` bytes (default 20), and no byte range was asked for. Unlike nginx, which
compresses as it streams, files larger than `gzipMaxSize` are not compressed. -/
def gzipApplies (eff : Settings) (req : Request) (mime : Bytes) (size : Nat) : Bool :=
  let types := eff.gzipTypes.getD []
  let m := mimeBase mime
  eff.gzip.getD false && acceptsGzip req.headers &&
    (m == b!"text/html" || types.contains m || types.contains b!"*") &&
    size ≥ eff.gzipMinLength.getD 20 && size ≤ gzipMaxSize &&
    (header? req.headers b!"range").isNone

/-- Weak ETag for a compressed representation (as nginx does). -/
def weakEtag (tag : Bytes) : Bytes := if isPrefixB b!"W/" tag then tag else b!"W/" ++ tag

/-! ## Autoindex -/

structure Entry where
  name : Bytes
  isDir : Bool
  size : Nat
  mtime : Int
  deriving Repr

def padTo (n : Nat) (b : Bytes) : Bytes := b ++ List.replicate (n - b.length) 32

/-- Directories first, then by name (byte order). -/
def entryLe (a b : Entry) : Bool :=
  if a.isDir != b.isDir then a.isDir else decide (a.name.toArray ≤ b.name.toArray)

/-- The link to a listed entry: its name as one encoded segment (`/` added for a directory). -/
def autoindexHref (e : Entry) : Bytes := percentEncodeSeg e.name ++ (if e.isDir then [47] else [])

/-- nginx-style `Index of /dir/` page. Names are URL-encoded in links and HTML-escaped as text. -/
def autoindexPage (uri : Bytes) (es : List Entry) : Bytes :=
  let es := (es.filter fun e => e.name.head? != some 46).mergeSort entryLe
  let title := b!"Index of " ++ htmlEscape uri
  let row (e : Entry) : Bytes :=
    let n := if e.isDir then e.name ++ [47] else e.name
    let shown := if n.length > 50 then n.take 47 ++ b!"..>" else n
    b!"<a href=\"" ++ autoindexHref e ++ b!"\">" ++ htmlEscape shown ++ b!"</a>" ++
      List.replicate (51 - shown.length) 32 ++ listingDate e.mtime ++
      (let sz := if e.isDir then b!"-" else decDigits e.size; List.replicate (20 - min 20 sz.length) 32 ++ sz) ++ crlf
  b!"<html>\r\n<head><title>" ++ title ++ b!"</title></head>\r\n<body>\r\n<h1>" ++ title ++
    b!"</h1><hr><pre><a href=\"../\">../</a>\r\n" ++ es.flatMap row ++ b!"</pre><hr></body>\r\n</html>\r\n"

end LeanNginx

import LeanNginx.Uri
/-!
# HTTP/1.x request heads (RFC 9112)

`parseRequest` turns the bytes before the blank line into a `Request` or an HTTP status code
to answer with (400, 411, 414, 501, 505). It is deliberately strict where laxness causes
request smuggling or header injection:

* field names must be tokens (so `Name :` and obs-folded lines are rejected),
* field values contain no NUL, CR, LF or other controls except HTAB,
* `Transfer-Encoding` is never accepted (411), so a body is framed only by `Content-Length`,
  and every `Content-Length` value must agree,
* HTTP/1.1 needs exactly one valid `Host`.

The specs in `Spec.lean` state these for all inputs.
-/
namespace LeanNginx

/-- RFC 9110 field-value bytes: VCHAR, obs-text, SP, HTAB (no NUL/CR/LF/DEL/controls). -/
def fieldByteOk (c : UInt8) : Bool := c == 9 || (32 ≤ c && c != 127)
def validValue (v : Bytes) : Bool := v.all fieldByteOk

def stripCR (l : Bytes) : Bytes := if l.getLast? == some 13 then l.dropLast else l

/-- Lines of a head; LF or CRLF terminated. -/
def headLines (head : Bytes) : List Bytes := (splitOnByte 10 head).map stripCR

/-- `name: value` with the name lower-cased and the value trimmed. -/
def parseField (l : Bytes) : Option (Bytes × Bytes) :=
  match splitFirst 58 l with
  | (_, none) => none
  | (n, some v) =>
    let v := trimWS v
    if isToken n && validValue v then some (lowerB n, v) else none

def parseFields : List Bytes → Option (List (Bytes × Bytes))
  | [] => some []
  | l :: ls => do
    let f ← parseField l
    let fs ← parseFields ls
    pure (f :: fs)

def headerVals (hs : List (Bytes × Bytes)) (name : Bytes) : List Bytes :=
  hs.filterMap fun (n, v) => if n == name then some v else none

def header? (hs : List (Bytes × Bytes)) (name : Bytes) : Option Bytes :=
  (headerVals hs name).head?

/-- Host characters we accept (letters, digits, `-`, `.`, `_`, and `:`/`[`/`]` for IPv6). -/
def hostByteOk (c : UInt8) : Bool := isAlpha c || isDigit c || b!"-._:[]".contains c

/-- Does `..` occur in `b`? -/
def hasDotDot : Bytes → Bool
  | 46 :: 46 :: _ => true
  | _ :: rest => hasDotDot rest
  | [] => false

def hostOk (h : Bytes) : Bool :=
  !h.isEmpty && h.all hostByteOk && !hasDotDot h && h.head? != some 46

/-- Drop a `:port` suffix (not for bracketed IPv6 literals' inner colons) and one trailing dot. -/
def hostName (h : Bytes) : Bytes :=
  let h := lowerB h
  let noPort :=
    if h.head? == some 91 then (splitFirst 93 h).1 ++ [93]  -- "[v6]:port" → "[v6]"
    else (splitFirst 58 h).1
  if noPort.getLast? == some 46 then noPort.dropLast else noPort

structure Request where
  method : Bytes
  /-- The request target as sent (nginx `$request_uri`). -/
  target : Bytes
  /-- Path part of the target (still percent-encoded). -/
  path : Bytes
  query : Option Bytes
  /-- HTTP/1.`minor` (0 or 1). -/
  minor : Nat
  /-- Header fields, names lower-cased, in arrival order. -/
  headers : List (Bytes × Bytes)
  /-- Validated, lower-cased host without port (from the target or the `Host` header). -/
  host : Option Bytes
  contentLength : Nat
  deriving Repr, Inhabited, DecidableEq

/-- `HTTP/1.0` → 0, `HTTP/1.1` → 1; other versions are 505, garbage is 400. -/
def parseVersion : Bytes → Except Nat Nat
  | [72, 84, 84, 80, 47, a, 46, b] =>
    if a == 49 && b == 48 then .ok 0
    else if a == 49 && b == 49 then .ok 1
    else if isDigit a && isDigit b then .error 505
    else .error 400
  | _ => .error 400

def maxTarget : Nat := 8192

/-- Origin-form `/p?q`, or absolute-form `http://host/p?q` (its host overrides `Host`). -/
def parseTarget (t : Bytes) : Except Nat (Option Bytes × Bytes × Option Bytes) :=
  if t.length > maxTarget then .error 414
  else if !t.all (fun c => 33 ≤ c && c != 127) then .error 400
  else match t with
    | 47 :: _ => let (p, q) := splitTarget t; .ok (none, p, q)
    | _ =>
      if isPrefixB b!"http://" (lowerB t) then
        let rest := t.drop 7
        let (auth, path?) := splitFirst 47 rest
        let (p, q) := splitTarget (47 :: path?.getD [])
        if hostOk auth then .ok (some (hostName auth), p, q) else .error 400
      else .error 400

def parseContentLength (hs : List (Bytes × Bytes)) : Except Nat Nat :=
  match headerVals hs b!"content-length" with
  | [] => .ok 0
  | v :: vs =>
    match parseNat? v with
    | none => .error 400
    | some n => if vs.all (· == v) then .ok n else .error 400

def parseHost (minor : Nat) (fromTarget : Option Bytes) (hs : List (Bytes × Bytes)) :
    Except Nat (Option Bytes) :=
  match headerVals hs b!"host" with
  | [] => if minor == 1 && fromTarget.isNone then .error 400 else .ok fromTarget
  | [h] =>
    if !hostOk h then .error 400
    else .ok (fromTarget <|> some (hostName h))
  | _ => .error 400

/-- Host values we can carry around: non-empty, host characters only. -/
def hostOk' : Option Bytes → Bool
  | none => true
  | some h => !h.isEmpty && h.all hostByteOk

/-- Parse a request head (everything before the empty line). Errors are HTTP status codes.
Written as explicit matches (no `do`) so that the specs can follow every branch. -/
def parseRequest (head : Bytes) : Except Nat Request :=
  match headLines head with
  | [] => .error 400
  | line :: rest =>
    match splitOnByte 32 line with
    | [m, t, v] =>
      if !isToken m then .error 400 else
      match parseVersion v with
      | .error e => .error e
      | .ok minor =>
      match parseTarget t with
      | .error e => .error e
      | .ok (thost, path, query) =>
      match parseFields rest with
      | none => .error 400
      | some fields =>
      if !(headerVals fields b!"transfer-encoding").isEmpty then .error 411 else
      match parseContentLength fields with
      | .error e => .error e
      | .ok cl =>
      match parseHost minor thost fields with
      | .error e => .error e
      | .ok host =>
      if hostOk' host then
        .ok { method := m, target := t, path, query, minor, headers := fields, host,
              contentLength := cl }
      else .error 400
    | _ => .error 400

/-- Should the connection stay open after this request? (RFC 9112 §9.3) -/
def Request.keepAlive (r : Request) : Bool :=
  let conn := (headerVals r.headers b!"connection").map lowerB
  let has (tok : Bytes) := conn.any fun v => (splitOnByte 44 v).any (trimWS · == tok)
  if r.minor == 1 then !has b!"close" else has b!"keep-alive"

/-- If a head ends at the line feed at `i` (followed by LF, or by CR LF), where the body starts. -/
def headEndAt (b : ByteArray) (i : Nat) : Option Nat :=
  if b.get! i == 10 then
    if i + 1 < b.size && b.get! (i + 1) == 10 then some (i + 2)
    else if i + 2 < b.size && b.get! (i + 1) == 13 && b.get! (i + 2) == 10 then some (i + 3)
    else none
  else none

/-- The first `i ≥ start` where a head ends. -/
def findHeadEndFrom (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if i < b.size then
    match headEndAt b i with
    | some e => some (i, e)
    | none => findHeadEndFrom b (i + 1)
  else none
termination_by b.size - i

/-- Where the head ends in a receive buffer: `(headLen, bodyStart)`, at the first empty line
(CRLFCRLF, LFLF or LFCRLF). Spec: `findHeadEnd_first`. -/
def findHeadEnd (b : ByteArray) : Option (Nat × Nat) := findHeadEndFrom b 0

end LeanNginx

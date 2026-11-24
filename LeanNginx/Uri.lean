import LeanNginx.Bytes
/-!
# Request URIs: percent-decoding and path normalisation

nginx decodes `%XX`, merges `//`, drops `.` and resolves `..` before it matches locations or
touches the file system, and answers 400 when `..` would climb above `/`. We do the same; the
result is a list of *segments*, each of which is proved `Safe` (non-empty, not `.`/`..`, no `/`,
no NUL). File paths are only ever built from safe segments (see `Route.lean`).
-/
namespace LeanNginx

/-- Decode `%XX` escapes. A `%` not followed by two hex digits is an error (nginx: 400). -/
def percentDecode : Bytes → Option Bytes
  | [] => some []
  | 37 :: h :: l :: rest => do
    let a ← hexVal? h
    let b ← hexVal? l
    let r ← percentDecode rest
    pure ((a * 16 + b).toUInt8 :: r)
  | 37 :: _ => none
  | c :: rest => (c :: ·) <$> percentDecode rest

/-- A path segment that can be appended to a directory without leaving it. -/
def segOk (s : Bytes) : Bool :=
  !s.isEmpty && s != b!"." && s != b!".." && s.all (fun c => c != 47 && c != 0)

def Safe (s : Bytes) : Prop := segOk s = true

/-- Resolve `.`, `..` and empty segments. `acc` holds the resolved segments in reverse.
`none` when `..` climbs above the root, or a segment contains NUL. -/
def normSegs : List Bytes → List Bytes → Option (List Bytes)
  | [], acc => some acc.reverse
  | s :: rest, acc =>
    if s.isEmpty || s == b!"." then normSegs rest acc
    else if s == b!".." then
      match acc with
      | [] => none
      | _ :: acc' => normSegs rest acc'
    else if segOk s then normSegs rest (s :: acc)
    else none

/-- A normalised request path: its segments and whether it names a directory
(ends in `/`, or in `.`/`..`, or is the root). -/
structure NPath where
  segs : List Bytes
  dir : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The path bytes nginx calls `$uri`: `/a/b` or `/a/b/`. -/
def NPath.uri (p : NPath) : Bytes :=
  (p.segs.flatMap (47 :: ·)) ++ (if p.dir && !p.segs.isEmpty then [47] else []) ++
    (if p.segs.isEmpty then [47] else [])

def lastSegDir (raw : Bytes) : Bool :=
  match (splitOnByte 47 raw).getLast? with
  | some s => s.isEmpty || s == b!"." || s == b!".."
  | none => true

/-- Normalise a path that is already percent-decoded (must start with `/`): merge `//`, drop `.`,
resolve `..`. Nothing is decoded here, so a `%` is an ordinary byte. This is what `$uri`, a
`try_files` entry and the target of an internal redirect go through: nginx decodes a request
path exactly once, and decoding again would turn `%2561` into `a` behind the back of the
location that was selected (and whose `auth_basic` was checked) on `%61`. -/
def normalizeDecoded (d : Bytes) : Option NPath :=
  match d with
  | 47 :: _ => do
    let segs ← normSegs (splitOnByte 47 d) []
    pure { segs, dir := lastSegDir d || segs.isEmpty }
  | _ => none

/-- Normalise an origin-form request path (must start with `/`): percent-decode it, once, then
`normalizeDecoded`. Only the path of a request line goes through here. -/
def normalizePath (raw : Bytes) : Option NPath :=
  match raw with
  | 47 :: _ => (percentDecode raw).bind normalizeDecoded
  | _ => none

/-- Bytes that may appear unescaped in a path we put into a `Location` header or an HTML link
(RFC 3986 unreserved plus `/` and a few sub-delims; never controls, space, `"`, `<`, `>`). -/
def pathSafeByte (c : UInt8) : Bool :=
  isAlpha c || isDigit c || b!"-._~/!$&'()*+,;=:@".contains c

def hexUpper (n : Nat) : UInt8 := (if n < 10 then 48 + n else 55 + n).toUInt8

/-- Percent-encode everything outside `pathSafeByte`. -/
def percentEncode : Bytes → Bytes
  | [] => []
  | c :: rest =>
    if pathSafeByte c then c :: percentEncode rest
    else 37 :: hexUpper (c.toNat / 16) :: hexUpper (c.toNat % 16) :: percentEncode rest

/-- Split a request target into path and query (`?`). -/
def splitTarget (t : Bytes) : Bytes × Option Bytes := splitFirst 63 t

end LeanNginx

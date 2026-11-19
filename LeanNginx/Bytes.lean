/-!
# Byte-string helpers

Everything the server parses (request heads, URIs, the config file) is handled as
`Bytes := List UInt8`, so specs can be stated over all inputs and concrete vectors are
kernel-checkable. `b!"text"` expands, at elaboration time, to an explicit byte list.
-/
namespace LeanNginx

abbrev Bytes := List UInt8

/-- `b!"text"`: the UTF-8 bytes of a string literal as an explicit list (kernel friendly). -/
macro:max "b!" s:str : term => do
  let elems := s.getString.toUTF8.toList.toArray.map fun b => Lean.Syntax.mkNumLit (toString b.toNat)
  `(([$elems,*] : Bytes))

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isUpper (c : UInt8) : Bool := 65 ≤ c && c ≤ 90
def isLowerA (c : UInt8) : Bool := 97 ≤ c && c ≤ 122
def isAlpha (c : UInt8) : Bool := isUpper c || isLowerA c
def toLower (c : UInt8) : UInt8 := if isUpper c then c + 32 else c
def lowerB (b : Bytes) : Bytes := b.map toLower

/-- RFC 9110 `tchar`. -/
def isTChar (c : UInt8) : Bool :=
  isDigit c || isAlpha c || b!"!#$%&'*+-.^_`|~".contains c

/-- RFC 9110 `token`: one or more `tchar`. -/
def isToken (b : Bytes) : Bool := !b.isEmpty && b.all isTChar

def isWS (c : UInt8) : Bool := c == 32 || c == 9

def trimWS (b : Bytes) : Bytes := ((b.dropWhile isWS).reverse.dropWhile isWS).reverse

/-- Split on every occurrence of `sep` (like `String.splitOn` with a one-char separator). -/
def splitOnByte (sep : UInt8) : Bytes → List Bytes
  | [] => [[]]
  | c :: rest =>
    if c == sep then [] :: splitOnByte sep rest
    else match splitOnByte sep rest with
      | [] => [[c]]
      | h :: t => (c :: h) :: t

/-- Split at the first `sep`: `(before, some after)` or `(all, none)`. -/
def splitFirst (sep : UInt8) : Bytes → Bytes × Option Bytes
  | [] => ([], none)
  | c :: rest =>
    if c == sep then ([], some rest)
    else let (a, b) := splitFirst sep rest; (c :: a, b)

def joinWith (sep : Bytes) : List Bytes → Bytes
  | [] => []
  | [x] => x
  | x :: xs => x ++ sep ++ joinWith sep xs

def isPrefixB (p b : Bytes) : Bool := p.isPrefixOf b

/-- Decimal digits of `n`, most significant first (structural on `fuel`). -/
def decDigits (n : Nat) : Bytes := go (n + 1) n []
where
  go : Nat → Nat → Bytes → Bytes
    | 0, _, acc => acc
    | fuel + 1, n, acc =>
      let acc := (48 + n % 10).toUInt8 :: acc
      if n < 10 then acc else go fuel (n / 10) acc

/-- Lower-case hex digits of `n`. -/
def hexDigitsB (n : Nat) : Bytes := go (n + 1) n []
where
  go : Nat → Nat → Bytes → Bytes
    | 0, _, acc => acc
    | fuel + 1, n, acc =>
      let d := n % 16
      let acc := (if d < 10 then 48 + d else 87 + d).toUInt8 :: acc
      if n < 16 then acc else go fuel (n / 16) acc

/-- Parse a non-empty run of decimal digits (at most 18, so the value fits comfortably). -/
def parseNat? (b : Bytes) : Option Nat :=
  if b.isEmpty || b.length > 18 || !b.all isDigit then none
  else some (b.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)

def hexVal? (c : UInt8) : Option Nat :=
  if isDigit c then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none

/-- Bytes → String: UTF-8 if valid, otherwise Latin-1 (used for logs and messages only). -/
def toStr (b : Bytes) : String :=
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => s
  | none => String.ofList (b.map fun x => Char.ofNat x.toNat)

/-- Bytes → String only when the bytes are valid UTF-8 (used for file-system paths). -/
def toStrStrict? (b : Bytes) : Option String := String.fromUTF8? ⟨b.toArray⟩

def ofStr (s : String) : Bytes := s.toUTF8.toList

end LeanNginx

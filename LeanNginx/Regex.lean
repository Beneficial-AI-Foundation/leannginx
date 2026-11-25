import LeanNginx.Bytes
/-!
# Regular expressions for `location ~` / `location ~*`

A matcher based on Brzozowski derivatives, over bytes, with a proof that it decides the
standard language semantics exactly (`matchB_iff` in `Proofs/Regex.lean`). It never backtracks.
`mkAlt` canonicalises every alternation it builds — flatten (associativity), sort (commutativity)
and de-duplicate (idempotence) — so by Brzozowski's theorem the set of distinct derivatives of a
fixed pattern is finite. The derivative term therefore stays bounded by a per-pattern constant no
matter how long the input is, even for an *ambiguous* operator-written regex such as `(a|aa)+b`:
work per byte does not grow with input length, so there is no catastrophic (ReDoS) blow-up.

Supported syntax (the PCRE subset nginx configurations use in practice): literals, `.`, classes
`[a-z0-9_]`, `[^…]`, `\d \w \s \D \W \S`, escapes, groups `(…)` and `(?:…)`, alternation `|`,
quantifiers `* + ? {n} {n,} {n,m}` (a lazy `?` suffix is accepted and does not change what is
matched; a possessive `*+`/`++` suffix is accepted but treated as greedy, so on a pattern like
`a*+a` it can accept where PCRE would not — operator-visible, not a soundness issue for
matches), anchors `^` at the start and `$` at the end. `~*` is case-insensitive (ASCII).
Captures are not available (`$1` in `alias`/`root` is not supported); back-references and
look-around are rejected with an error.
-/
namespace LeanNginx

/-- A set of bytes: a list of inclusive ranges, possibly negated. -/
structure CClass where
  neg : Bool
  ranges : List (UInt8 × UInt8)
  deriving Repr, DecidableEq, Inhabited

def CClass.mem (c : CClass) (x : UInt8) : Bool :=
  c.ranges.any (fun (a, b) => a ≤ x && x ≤ b) != c.neg

inductive Re where
  | none
  | eps
  | cls (c : CClass)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  deriving Repr, DecidableEq, Inhabited

/-- The language semantics: `Matches r s` says the whole of `s` is in the language of `r`. -/
inductive Matches : Re → Bytes → Prop where
  | eps : Matches .eps []
  | cls {c : CClass} {x : UInt8} : c.mem x = true → Matches (.cls c) [x]
  | seq {a b : Re} {s t : Bytes} : Matches a s → Matches b t → Matches (.seq a b) (s ++ t)
  | altL {a b : Re} {s : Bytes} : Matches a s → Matches (.alt a b) s
  | altR {a b : Re} {s : Bytes} : Matches b s → Matches (.alt a b) s
  | starNil {a : Re} : Matches (.star a) []
  | starCons {a : Re} {s t : Bytes} : Matches a s → Matches (.star a) t → Matches (.star a) (s ++ t)

def Re.nullable : Re → Bool
  | .none => false
  | .eps => true
  | .cls _ => false
  | .seq a b => a.nullable && b.nullable
  | .alt a b => a.nullable || b.nullable
  | .star _ => true

/-- `seq` with the obvious simplifications (keeps derivatives small). -/
def mkSeq : Re → Re → Re
  | .none, _ => .none
  | _, .none => .none
  | .eps, b => b
  | a, b => .seq a b

/-- The alternatives of a regex, flattening nested `alt`s: `a|b|c` -> `[a, b, c]`. -/
def Re.altList : Re → List Re
  | .alt a b => a.altList ++ b.altList
  | r => [r]

/-- Fold a list of alternatives back into a right-nested `alt` (`[]` -> `.none`). -/
def altOf : List Re → Re
  | [] => .none
  | [r] => r
  | r :: rs => .alt r (altOf rs)

/-- A structural key used only to order alternatives, so that `mkAlt` can sort them into a
canonical order. Any deterministic order works; this one is a prefix encoding of the tree. -/
def Re.key : Re → List Nat
  | .none => [0]
  | .eps => [1]
  | .cls c => 2 :: (if c.neg then 1 else 0) :: c.ranges.length :: c.ranges.flatMap (fun p => [p.1.toNat, p.2.toNat])
  | .seq a b => 3 :: (a.key ++ b.key)
  | .alt a b => 4 :: (a.key ++ b.key)
  | .star a => 5 :: a.key

/-- Lexicographic `≤` on `Nat` lists, as a `Bool` (the order `sortByKey` uses). -/
def natListLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else natListLe as bs

def Re.leB (a b : Re) : Bool := natListLe a.key b.key

/-- Insertion of `x` into `l` by `Re.leB` (structural, so `decide` reduces it in the kernel). -/
def insByKey (x : Re) : List Re → List Re
  | [] => [x]
  | y :: ys => if Re.leB x y then x :: y :: ys else y :: insByKey x ys

/-- Insertion sort of alternatives by `Re.leB`. -/
def sortByKey : List Re → List Re
  | [] => []
  | x :: xs => insByKey x (sortByKey xs)

/-- `alt` that normalises: `.none` is dropped, and the set of alternatives is flattened, sorted
and de-duplicated into a canonical form. Normalising (Brzozowski's A/C/I up to this order) bounds
the number of distinct derivatives, so the derivative matcher cannot blow up (no ReDoS), while the
language is unchanged (`mkAlt_iff`). -/
def mkAlt (a b : Re) : Re :=
  match a, b with
  | .none, b => b
  | a, .none => a
  | a, b => altOf ((sortByKey (a.altList ++ b.altList)).eraseDups)

/-- Brzozowski derivative: the words `w` such that `x :: w` matches `r`. -/
def Re.deriv (x : UInt8) : Re → Re
  | .none => .none
  | .eps => .none
  | .cls c => if c.mem x then .eps else .none
  | .seq a b =>
    if a.nullable then mkAlt (mkSeq (a.deriv x) b) (b.deriv x) else mkSeq (a.deriv x) b
  | .alt a b => mkAlt (a.deriv x) (b.deriv x)
  | .star a => mkSeq (a.deriv x) (.star a)

/-- Does `r` match the whole of `s`? -/
def Re.matchB (r : Re) : Bytes → Bool
  | [] => r.nullable
  | x :: s => (r.deriv x).matchB s

/-! ## Parsing -/

def rng (a b : UInt8) : UInt8 × UInt8 := (a, b)

def digitR : List (UInt8 × UInt8) := [rng 48 57]
def wordR : List (UInt8 × UInt8) := [rng 48 57, rng 65 90, rng 97 122, rng 95 95]
def spaceR : List (UInt8 × UInt8) := [rng 32 32, rng 9 13]

/-- Add the other ASCII case of every letter in the ranges. -/
def foldRanges (rs : List (UInt8 × UInt8)) : List (UInt8 × UInt8) :=
  rs ++ rs.flatMap fun (a, b) =>
    let up := if b < 65 || a > 90 then [] else [(max a 65 + 32, min b 90 + 32)]
    let lo := if b < 97 || a > 122 then [] else [(max a 97 - 32, min b 122 - 32)]
    up ++ lo

def mkCls (ci neg : Bool) (rs : List (UInt8 × UInt8)) : Re :=
  .cls { neg, ranges := if ci then foldRanges rs else rs }

/-- `.`: any byte except newline. -/
def dotRe : Re := .cls { neg := true, ranges := [rng 10 10] }
def anyByte : Re := .cls { neg := true, ranges := [] }

/-- `\d`-style escapes as ranges (`some (neg, ranges)`), else the literal byte. -/
def escRanges (c : UInt8) : Option (Bool × List (UInt8 × UInt8)) :=
  if c == 100 then some (false, digitR) else if c == 68 then some (true, digitR)
  else if c == 119 then some (false, wordR) else if c == 87 then some (true, wordR)
  else if c == 115 then some (false, spaceR) else if c == 83 then some (true, spaceR)
  else none

def escLiteral (c : UInt8) : UInt8 :=
  if c == 110 then 10 else if c == 116 then 9 else if c == 114 then 13 else c

/-- Body of `[...]` after `[` (and `^`): ranges and the rest after `]`. -/
def parseClassBody : Nat → Bytes → List (UInt8 × UInt8) → Except String (List (UInt8 × UInt8) × Bytes)
  | 0, _, _ => .error "regex: character class too long"
  | _, [], _ => .error "regex: missing ]"
  | fuel + 1, 93 :: rest, acc => if acc.isEmpty then parseClassBody fuel rest (acc ++ [rng 93 93]) else .ok (acc, rest)
  | fuel + 1, 92 :: c :: rest, acc =>
    match escRanges c with
    | some (false, rs) => parseClassBody fuel rest (acc ++ rs)
    | some (true, _) => .error "regex: negated escapes inside [...] are not supported"
    | none => parseClassBody fuel rest (acc ++ [rng (escLiteral c) (escLiteral c)])
  | fuel + 1, a :: 45 :: b :: rest, acc =>
    if b == 93 then parseClassBody fuel (45 :: b :: rest) (acc ++ [rng a a])
    else if a ≤ b then parseClassBody fuel rest (acc ++ [rng a b])
    else .error "regex: invalid range in [...]"
  | fuel + 1, c :: rest, acc => parseClassBody fuel rest (acc ++ [rng c c])

def digitsPrefix : Bytes → Bytes × Bytes
  | c :: rest => if isDigit c then let (d, r) := digitsPrefix rest; (c :: d, r) else ([], c :: rest)
  | [] => ([], [])

/-- `{n}`, `{n,}`, `{n,m}` after `{`: `some ((n, m?), rest)`; `none` if it is not a quantifier. -/
def parseBraces (s : Bytes) : Option ((Nat × Option Nat) × Bytes) :=
  let (d1, r1) := digitsPrefix s
  match parseNat? d1, r1 with
  | some n, 125 :: r => some ((n, some n), r)
  | some n, 44 :: 125 :: r => some ((n, none), r)
  | some n, 44 :: r2 =>
    let (d2, r3) := digitsPrefix r2
    match parseNat? d2, r3 with
    | some m, 125 :: r => if n ≤ m then some ((n, some m), r) else none
    | _, _ => none
  | _, _ => none

def repeatRe (a : Re) : Nat → Re
  | 0 => .eps
  | n + 1 => .seq a (repeatRe a n)

/-- `a{n,m}`: `n` copies, then up to `m - n` optional ones (nested). -/
def boundedRe (a : Re) (n : Nat) : Option Nat → Re
  | none => .seq (repeatRe a n) (.star a)
  | some m => .seq (repeatRe a n) (optRe (m - n))
where
  optRe : Nat → Re
    | 0 => .eps
    | k + 1 => .alt .eps (.seq a (optRe k))

/-- Apply a quantifier after an atom, if there is one. -/
def parseQuant (a : Re) : Bytes → Except String (Re × Bytes)
  | 42 :: rest => .ok (.star a, skipLazy rest)
  | 43 :: rest => .ok (.seq a (.star a), skipLazy rest)
  | 63 :: rest => .ok (.alt a .eps, skipLazy rest)
  | 123 :: rest =>
    match parseBraces rest with
    | some ((n, m), r) =>
      if n > 255 || (m.getD n) > 255 then .error "regex: repetition count too large (max 255)"
      else .ok (boundedRe a n m, skipLazy r)
    | none => .ok (a, 123 :: rest)
  | s => .ok (a, s)
where
  skipLazy : Bytes → Bytes
    | 63 :: r => r
    | 43 :: r => r
    | r => r

mutual
/-- `alt := seq ('|' seq)*` -/
def parseAlt (ci : Bool) : Nat → Bytes → Except String (Re × Bytes)
  | 0, _ => .error "regex too complex"
  | fuel + 1, s => do
    let (a, r) ← parseSeq ci fuel s .eps
    match r with
    | 124 :: r' => let (b, r'') ← parseAlt ci fuel r'; pure (.alt a b, r'')
    | _ => pure (a, r)

/-- A sequence of quantified atoms, up to `|`, `)` or the end. -/
def parseSeq (ci : Bool) : Nat → Bytes → Re → Except String (Re × Bytes)
  | 0, _, _ => .error "regex too complex"
  | _, [], acc => pure (acc, [])
  | fuel + 1, c :: rest, acc =>
    if c == 124 || c == 41 then pure (acc, c :: rest) else do
    let (atom, r) ← parseAtom ci fuel (c :: rest)
    let (q, r) ← parseQuant atom r
    parseSeq ci fuel r (if acc == .eps then q else .seq acc q)

def parseAtom (ci : Bool) : Nat → Bytes → Except String (Re × Bytes)
  | 0, _ => .error "regex too complex"
  | _, [] => .error "regex: unexpected end"
  | fuel + 1, c :: rest =>
    if c == 40 then
      let body : Except String Bytes := match rest with
        | 63 :: 58 :: r => .ok r
        | 63 :: _ => .error "regex: (?...) groups other than (?:...) are not supported"
        | r => .ok r
      match body with
      | .error e => .error e
      | .ok r => do
        let (a, r') ← parseAlt ci fuel r
        match r' with
        | 41 :: r'' => pure (a, r'')
        | _ => throw "regex: missing )"
    else if c == 91 then
      let (neg, r) := match rest with
        | 94 :: r => (true, r)
        | r => (false, r)
      match parseClassBody 4096 r [] with
      | .ok (rs, r') => pure (mkCls ci neg rs, r')
      | .error e => .error e
    else if c == 46 then pure (dotRe, rest)
    else if c == 92 then
      match rest with
      | [] => .error "regex: trailing backslash"
      | e :: r =>
        if isDigit e && e != 48 then .error "regex: back-references are not supported"
        else match escRanges e with
          | some (neg, rs) => pure (mkCls ci neg rs, r)
          | none => let l := escLiteral e; pure (mkCls ci false [rng l l], r)
    else if c == 94 || c == 36 then .error "regex: ^ and $ are only supported at the start and end"
    else if c == 42 || c == 43 || c == 63 then .error "regex: nothing to repeat"
    else pure (mkCls ci false [rng c c], rest)
end

/-- Compile an nginx regex to a whole-URI matcher: unanchored ends match anything. -/
def compileRegex (ci : Bool) (pat : Bytes) : Except String Re := do
  let (startAnchor, p) := match pat with
    | 94 :: r => (true, r)
    | r => (false, r)
  let (endAnchor, p) :=
    if p.getLast? == some 36 && (p.dropLast.getLast? != some 92) then (true, p.dropLast) else (false, p)
  let (r, rest) ← parseAlt ci (4 * p.length + 4) p
  unless rest.isEmpty do throw "regex: unbalanced )"
  let r := if startAnchor then r else .seq (.star anyByte) r
  pure (if endAnchor then r else .seq r (.star anyByte))

/-- Does the URI match the compiled location regex? -/
def regexMatches (r : Re) (uri : Bytes) : Bool := r.matchB uri

end LeanNginx

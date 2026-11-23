import LeanNginx.Route
import LeanTLS.SHA256

/-!
# HTTP Basic authentication (`auth_basic`, `auth_basic_user_file`)

Credentials come from the `Authorization: Basic …` header (RFC 7617). The user file uses nginx's
htpasswd format, `user:hash` per line; hashes are SHA-256-crypt (`$5$…`, as made by
`openssl passwd -5`), the scheme glibc's `crypt` — and so nginx on Linux — accepts.

`routeAuth` puts the check in front of `route`. Like nginx, a `return` in the server or the selected
location answers before access checks run.
-/

namespace LeanNginx

/-! ## Base64 (RFC 4648) -/

def b64Val (c : UInt8) : Option Nat :=
  if isUpper c then some (c.toNat - 65)
  else if isLowerA c then some (c.toNat - 71)
  else if isDigit c then some (c.toNat + 4)
  else if c == 43 then some 62
  else if c == 47 then some 63
  else none

def b64Groups : List Nat → Option Bytes
  | a :: b :: c :: d :: r =>
    let n := a * 262144 + b * 4096 + c * 64 + d
    (b64Groups r).map fun rest => (n / 65536).toUInt8 :: (n / 256 % 256).toUInt8 :: (n % 256).toUInt8 :: rest
  | [a, b, c] => let n := a * 262144 + b * 4096 + c * 64; some [(n / 65536).toUInt8, (n / 256 % 256).toUInt8]
  | [a, b] => some [((a * 262144 + b * 4096) / 65536).toUInt8]
  | [] => some []
  | [_] => none

def b64Decode (s : Bytes) : Option Bytes :=
  (((s.reverse.dropWhile (· == 61)).reverse).mapM b64Val).bind b64Groups

/-! ## Credentials -/

/-- `Basic <base64(user:password)>` → `(user, password)`; the scheme name is case-insensitive. -/
def basicCreds (v : Bytes) : Option (Bytes × Bytes) :=
  match splitFirst 32 (trimWS v) with
  | (scheme, some rest) =>
    if lowerB scheme == b!"basic" then
      match (b64Decode (trimWS rest)).map (splitFirst 58) with
      | some (u, some p) => some (u, p)
      | _ => none
    else none
  | _ => none

/-- htpasswd lines `user:hash[:comment]`; blank lines and `#` comments are skipped. -/
def parseUsers (f : Bytes) : List (Bytes × Bytes) :=
  (splitOnByte 10 f).filterMap fun l =>
    let l := trimWS (stripCR l)
    if l.isEmpty || l.head? == some 35 then none
    else match splitFirst 58 l with
      | (u, some rest) => some (u, (splitFirst 58 rest).1)
      | _ => none

/-! ## SHA-256-crypt (Drepper, "Unix crypt using SHA-256 and SHA-512") -/

def sha (b : ByteArray) : ByteArray := LeanTLS.SHA256.hash b

/-- The first `n` bytes of `src` repeated. -/
def cycleTo (src : ByteArray) (n : Nat) : ByteArray :=
  if src.size = 0 then .empty else ⟨((List.range n).map fun i => src.get! (i % src.size)).toArray⟩

def repeatB (src : ByteArray) : Nat → ByteArray
  | 0 => .empty
  | k + 1 => src ++ repeatB src k

/-- For each bit of `n`, least significant first: `b` for a one, `pw` for a zero. -/
def bitParts (b pw : ByteArray) : Nat → Nat → ByteArray
  | 0, _ => .empty
  | fuel + 1, n => if n = 0 then .empty else (if n % 2 = 1 then b else pw) ++ bitParts b pw fuel (n / 2)

def sha256CryptRaw (pw salt : ByteArray) (rounds : Nat) : ByteArray :=
  let b := sha (pw ++ salt ++ pw)
  let a := sha (pw ++ salt ++ cycleTo b pw.size ++ bitParts b pw 64 pw.size)
  let p := cycleTo (sha (repeatB pw pw.size)) pw.size
  let s := cycleTo (sha (repeatB salt (16 + (a.get! 0).toNat))) salt.size
  (List.range rounds).foldl (fun c i =>
    sha ((if i % 2 = 1 then p else c) ++ (if i % 3 = 0 then .empty else s) ++
         (if i % 7 = 0 then .empty else p) ++ (if i % 2 = 1 then c else p))) a

def cryptAlphabet : Bytes := b!"./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

def b64From24 (b2 b1 b0 : UInt8) (n : Nat) : Bytes :=
  let w := b2.toNat * 65536 + b1.toNat * 256 + b0.toNat
  (List.range n).map fun i => cryptAlphabet.getD (w / 64 ^ i % 64) 0

def cryptEncode256 (c : ByteArray) : Bytes :=
  let g (i j k : Nat) := b64From24 (c.get! i) (c.get! j) (c.get! k) 4
  g 0 10 20 ++ g 21 1 11 ++ g 12 22 2 ++ g 3 13 23 ++ g 24 4 14 ++ g 15 25 5 ++ g 6 16 26 ++
  g 27 7 17 ++ g 18 28 8 ++ g 9 19 29 ++ b64From24 0 (c.get! 31) (c.get! 30) 3

def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩

/-- `$5$[rounds=N$]salt$hash` → `(rounds, salt, hash)`; salt is cut to 16 bytes, rounds clamped. -/
def parseCrypt5 (h : Bytes) : Option (Nat × Bytes × Bytes) :=
  match splitOnByte 36 h with
  | [[], [53], r, salt, enc] =>
    if isPrefixB b!"rounds=" r then
      (parseNat? (r.drop 7)).map fun n => (min 999999999 (max 1000 n), salt.take 16, enc)
    else none
  | [[], [53], salt, enc] => some (5000, salt.take 16, enc)
  | _ => none

/-- Does `pw` match the stored SHA-256-crypt hash `h`? Any other hash format never matches. -/
def verifyCrypt (h pw : Bytes) : Bool :=
  match parseCrypt5 h with
  | some (rounds, salt, enc) => cryptEncode256 (sha256CryptRaw (toBA pw) (toBA salt) rounds) == enc
  | none => false

-- Vectors from `openssl passwd -5` (5,000 rounds are too many for the kernel, so these are
-- evaluated at build time rather than proved): short password, salt cut to 16 bytes, password
-- longer than one digest, wrong password.
#guard verifyCrypt b!"$5$saltstring$5B8vYYiY.CVt1RlTTf8KbXBH3hsxY/GNooZaBBGWEc5" b!"Hello world!"
#guard verifyCrypt b!"$5$saltstringsaltst$a5C8Ofk71MUIoKve2QuP9FMl.dwNgseF5tR1LGAL7iB" b!"Hello world!"
#guard verifyCrypt b!"$5$abc$qW8rTLSXKNArKNacA48LAFAdZNWfi84zou2Lg9tY4j3"
  b!"a much longer password that is more than thirty-two bytes long!!"
#guard !verifyCrypt b!"$5$saltstring$5B8vYYiY.CVt1RlTTf8KbXBH3hsxY/GNooZaBBGWEc5" b!"Hello world"

/-! ## The access check -/

/-- Valid credentials for one of `users` in the `Authorization` header. -/
def basicOk (users : List (Bytes × Bytes)) (authz : Option Bytes) : Bool :=
  match authz.bind basicCreds with
  | some (u, p) => users.any fun e => e.1 == u && verifyCrypt e.2 p
  | none => false

/-- With `auth_basic` on, the request lacks valid credentials. `users path` reads a user file;
a missing file has no users, so every request is refused. -/
def authDenied (eff : Settings) (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes) : Bool :=
  match eff.authBasic with
  | some (some _) => !basicOk (users (eff.authUserFile.getD [])) authz
  | _ => false

/-- The `WWW-Authenticate` challenge sent with a 401 from `auth_basic`. Quotes and control bytes
are dropped from the realm, so the header value stays one well-formed field. -/
def authChallenge (eff : Settings) : List (Bytes × Bytes) :=
  match eff.authBasic with
  | some (some realm) =>
    [(b!"WWW-Authenticate", b!"Basic realm=\"" ++ realm.filter (fun c => c != 34 && fieldByteOk c) ++ b!"\"")]
  | _ => []

/-- `route`, behind `auth_basic`: 401 when credentials are required and missing or wrong. -/
def routeAuth (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes) : Step :=
  let l := (selectLocation sv.locations np.uri).getD defaultLocation
  if sv.ret.isNone && l.ret.isNone && authDenied (effective h sv l) users authz then .done (.error 401)
  else route h sv req v np

end LeanNginx

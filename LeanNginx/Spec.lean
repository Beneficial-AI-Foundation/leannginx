import LeanNginx.Proofs.Misc
import LeanNginx.Proofs.Regex
import Zip.Spec.GzipCorrect
import LeanNginx.Auth
import LeanNginx.Proofs.Serve
/-!
# leannginx specification

This file is the test suite. Every behaviour we rely on is a theorem here, checked by
`lake build`; there are no runtime unit tests. Section headers name the nginx feature and,
where there is one, the script in nginx's own Perl test suite (nginx-tests) that covers it.

Rules (see CLAUDE.md):
* New behaviour ⇒ new spec in this file, in the matching section, with a docstring.
* Prefer statements over *all* inputs. Concrete vectors are kernel-checked
  (`decide +kernel` or `rfl`); never `native_decide`.
* Every spec is covered by the axiom audit in `LeanNginx/Audit.lean` (`./audit.sh`); the build
  fails if a spec gains `sorry` or a non-standard axiom.
* Supporting lemmas live in `LeanNginx/Proofs/`.
-/

set_option linter.unusedSimpArgs false

deriving instance DecidableEq for Except

namespace LeanNginx.Spec
open LeanNginx LeanNginx.Proofs

/-! ## 1. Request heads — RFC 9112 (nginx-tests: `http_method.t`, `http_header_buffers.t`) -/

/-- Every accepted request has a method that is an RFC 9110 token. -/
theorem parseRequest_method_token (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    isToken r.method = true :=
  (parseRequest_ok head r h).1

/-- Only HTTP/1.0 and HTTP/1.1 are accepted. -/
theorem parseRequest_minor (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    r.minor ≤ 1 :=
  (parseRequest_ok head r h).2.1

/-- Every header field name of an accepted request is a (lower-cased) token, and every value
is made of legal field bytes. -/
theorem parseRequest_fields (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    ∀ f ∈ r.headers, isToken f.1 = true ∧ validValue f.2 = true := by
  obtain ⟨ls, hls⟩ := (parseRequest_ok head r h).2.2.1
  exact parseFields_ok ls r.headers hls

/-- **No header injection from requests.** No header value of an accepted request contains
NUL, CR or LF, so a value copied into a response or an upstream request cannot start a new
header line. -/
theorem parseRequest_values_no_crlf (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    ∀ f ∈ r.headers, ∀ c ∈ f.2, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 := by
  intro f hf
  exact validValue_no_ctl f.2 (parseRequest_fields head r h f hf).2

/-- **No request smuggling via framing.** An accepted request never carries
`Transfer-Encoding` (those get 411), so its body is framed by `Content-Length` alone… -/
theorem parseRequest_no_transfer_encoding (head : Bytes) (r : Request)
    (h : parseRequest head = .ok r) :
    headerVals r.headers b!"transfer-encoding" = [] :=
  (parseRequest_ok head r h).2.2.2.1

/-- …and every `Content-Length` field it carries states exactly the length the server uses. -/
theorem parseRequest_content_length (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    ∀ v ∈ headerVals r.headers b!"content-length", parseNat? v = some r.contentLength :=
  parseContentLength_agree _ _ (parseRequest_ok head r h).2.2.2.2.1

/-- The host an accepted request names (from `Host` or an absolute-form target) contains no
`/`, NUL, CR, LF, space, `"` or `<`, so it is safe to put into `Location` headers and logs. -/
theorem parseRequest_host_safe (head : Bytes) (r : Request) (h : parseRequest head = .ok r)
    (host : Bytes) (hh : r.host = some host) :
    ∀ c ∈ host, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 32 ∧ c ≠ 47 ∧ c ≠ 34 ∧ c ≠ 60 := by
  have hk := (parseRequest_ok head r h).2.2.2.2.2
  rw [hh] at hk
  simp only [hostOk', Bool.and_eq_true, List.all_eq_true] at hk
  intro c hc
  exact hostByteOk_nat c.toNat c.toNat_lt (by simpa using hk.2 c hc) |> fun h => by
    simpa [← UInt8.toNat_inj] using h

/-- A minimal HTTP/1.1 request. -/
theorem vector_get : parseRequest b!"GET /index.html?x=1 HTTP/1.1\r\nHost: Example.COM:8080" =
    .ok { method := b!"GET", target := b!"/index.html?x=1", path := b!"/index.html",
          query := some b!"x=1", minor := 1, headers := [(b!"host", b!"Example.COM:8080")],
          host := some b!"example.com", contentLength := 0 } := by decide +kernel

/-- HTTP/1.1 without `Host` is 400 (RFC 9112 §3.2). -/
theorem vector_no_host : parseRequest b!"GET / HTTP/1.1" = .error 400 := by decide +kernel

/-- HTTP/1.0 without `Host` is fine. -/
theorem vector_http10 : (parseRequest b!"GET / HTTP/1.0").toOption.map (·.minor) = some 0 := by
  decide +kernel

/-- `Content-Length` + `Transfer-Encoding` (the classic CL.TE smuggling shape) is refused. -/
theorem vector_cl_te : parseRequest
    b!"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 4\r\nTransfer-Encoding: chunked" = .error 411 := by
  decide +kernel

/-- Two different `Content-Length`s are refused. -/
theorem vector_cl_cl : parseRequest
    b!"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 4\r\nContent-Length: 5" = .error 400 := by
  decide +kernel

/-- Whitespace between a field name and the colon is refused (RFC 9112 §5.1). -/
theorem vector_space_colon : parseRequest b!"GET / HTTP/1.1\r\nHost : a" = .error 400 := by
  decide +kernel

/-- Obsolete line folding is refused. -/
theorem vector_obs_fold : parseRequest b!"GET / HTTP/1.1\r\nHost: a\r\nX: 1\r\n 2" = .error 400 := by
  decide +kernel

/-- A NUL inside a value is refused. -/
theorem vector_nul_value : parseRequest b!"GET / HTTP/1.1\r\nHost: a\r\nX: a\x00b" = .error 400 := by
  decide +kernel

/-- Unsupported versions get 505, garbage gets 400. -/
theorem vector_versions : parseRequest b!"GET / HTTP/2.0\r\nHost: a" = .error 505 ∧
    parseRequest b!"GET / HTTX/1.1\r\nHost: a" = .error 400 := by decide +kernel

/-- `Host: ../x` and duplicate `Host` fields are refused. -/
theorem vector_bad_host : parseRequest b!"GET / HTTP/1.1\r\nHost: ../x" = .error 400 ∧
    parseRequest b!"GET / HTTP/1.1\r\nHost: a\r\nHost: b" = .error 400 := by decide +kernel

/-- Absolute-form targets: the host comes from the target. -/
theorem vector_absolute_form :
    (parseRequest b!"GET http://Lean.example/a?b HTTP/1.1\r\nHost: other").toOption.map
      (fun r => (r.host, r.path, r.query)) = some (some b!"lean.example", b!"/a", some b!"b") := by
  decide +kernel

/-! ## 2. URI normalisation (nginx-tests: `http_uri.t`) -/

/-- **Every normalised path is made of safe segments**: none is empty, `.` or `..`, and none
contains `/` or NUL — whatever the client sent, percent-encoded or not. -/
theorem normalizePath_segments_safe (raw : Bytes) (np : NPath) (h : normalizePath raw = some np) :
    ∀ s ∈ np.segs, Safe s :=
  normalizePath_safe raw np h

/-- **A request path is decoded exactly once.** `normalizePath` is `percentDecode` followed by
`normalizeDecoded`, and `normalizeDecoded` (the only normaliser used after that point: for
`$uri` in `try_files`, internal redirects and `error_page`) does no decoding at all. -/
theorem normalizePath_decodes_once (raw : Bytes) (np : NPath) (h : normalizePath raw = some np) :
    ∃ d, percentDecode raw = some d ∧ normalizeDecoded d = some np :=
  normalizePath_decoded raw np h

/-- Paths normalised without decoding are made of safe segments too. -/
theorem normalizeDecoded_segments_safe (d : Bytes) (np : NPath) (h : normalizeDecoded d = some np) :
    ∀ s ∈ np.segs, Safe s :=
  normalizeDecoded_safe d np h

/-- **`$uri` is stable.** Reading the `$uri` of a normalised request path back as a path gives
the same segments and the same file/directory flag, for every request path: nothing in it is
decoded, merged or resolved a second time. So a location that works on `$uri` (`try_files`) sees
the path its `location` was selected on. -/
theorem normalizePath_uri_stable (raw : Bytes) (np : NPath) (h : normalizePath raw = some np) :
    normalizeDecoded np.uri = some np := by
  obtain ⟨d, _, hd⟩ := normalizePath_decoded raw np h
  exact normalizeDecoded_uri np (normalizeDecoded_safe d np hd) (normalizeDecoded_root_dir d np hd)

/-- `$uri/` is the same path as a directory. -/
theorem normalizePath_uri_slash (raw : Bytes) (np : NPath) (h : normalizePath raw = some np) :
    normalizeDecoded (np.uri ++ b!"/") = some { np with dir := true } :=
  normalizeDecoded_uri_slash np (normalizePath_safe raw np h)

/-- Percent-decoding undoes percent-encoding, for all byte strings. -/
theorem percentDecode_encode (b : Bytes) : percentDecode (percentEncode b) = some b :=
  percentDecode_percentEncode b

/-- Percent-encoded output (used in redirects and autoindex links) only contains
URL-safe bytes, so no CR, LF, space, quote or angle bracket. -/
theorem percentEncode_safe (b : Bytes) :
    ∀ c ∈ percentEncode b, c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 32 ∧ c ≠ 34 ∧ c ≠ 60 ∧ c ≠ 62 := by
  intro c hc
  have h := percentEncode_byte_ok b c hc
  have key : ∀ n, n < 256 → (pathSafeByte n.toUInt8 = true ∨ n = 37 ∨ isAlpha n.toUInt8 = true ∨
      isDigit n.toUInt8 = true) → n ≠ 10 ∧ n ≠ 13 ∧ n ≠ 32 ∧ n ≠ 34 ∧ n ≠ 60 ∧ n ≠ 62 := by
    decide +kernel
  have := key c.toNat c.toNat_lt (by
    rcases h with h | h | h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl (by subst h; rfl))
    · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using h))))
  simpa [← UInt8.toNat_inj] using this

/-- `.`, `..` and `//` are resolved like nginx does. -/
theorem vector_dots : normalizePath b!"/a/./b/../c//d" = some ⟨[b!"a", b!"c", b!"d"], false⟩ := by
  decide +kernel

/-- Trailing `/` marks a directory; `/` is the root directory. -/
theorem vector_dirs : normalizePath b!"/a/b/" = some ⟨[b!"a", b!"b"], true⟩ ∧
    normalizePath b!"/" = some ⟨[], true⟩ ∧ normalizePath b!"/a/b/.." = some ⟨[b!"a"], true⟩ := by
  decide +kernel

/-- Climbing above the root is 400, also when percent-encoded. -/
theorem vector_traversal : normalizePath b!"/../etc/passwd" = none ∧
    normalizePath b!"/files/%2e%2e/%2E%2E/%2e%2e/etc/passwd" = none ∧
    normalizePath b!"/a/..%2f..%2fetc" = none := by
  decide +kernel

/-- Encoded NUL and malformed escapes are 400; paths must start with `/`. -/
theorem vector_bad_escapes : normalizePath b!"/a%00b" = none ∧ normalizePath b!"/%zz" = none ∧
    normalizePath b!"/%4" = none ∧ normalizePath b!"a/b" = none := by
  decide +kernel

/-- `%2F` is decoded and treated as a separator (as nginx does). -/
theorem vector_encoded_slash : normalizePath b!"/a%2Fb" = some ⟨[b!"a", b!"b"], false⟩ := by
  decide +kernel

/-- `NPath.uri` is nginx's `$uri`. -/
theorem vector_uri : (normalizePath b!"/a//b/./c/").map NPath.uri = some b!"/a/b/c/" ∧
    (normalizePath b!"/x/%20y").map NPath.uri = some b!"/x/ y" := by
  decide +kernel

/-- A double-encoded path is decoded once: `%2561` is the three bytes `%61`, not `a`, and
`%252e%252e` is a directory called `%2e%2e`, not `..`. Reading the result again changes nothing. -/
theorem vector_double_encoding :
    normalizePath b!"/%2561dmin/x" = some ⟨[b!"%61dmin", b!"x"], false⟩ ∧
    (normalizePath b!"/%2561dmin/x").bind (normalizeDecoded ·.uri) =
      some ⟨[b!"%61dmin", b!"x"], false⟩ ∧
    normalizePath b!"/a/%252e%252e/b" = some ⟨[b!"a", b!"%2e%2e", b!"b"], false⟩ ∧
    normalizeDecoded b!"/a/%2e%2e/b" = some ⟨[b!"a", b!"%2e%2e", b!"b"], false⟩ ∧
    normalizeDecoded b!"/a/../b//c/" = some ⟨[b!"b", b!"c"], true⟩ ∧
    normalizeDecoded b!"/../a" = none := by
  decide +kernel

/-! ## 3. Location matching (nginx docs, `location`; nginx-tests: `http_location.t`) -/

theorem regexHit_matches (uri : Bytes) (l : Location) (h : regexHit uri l = true) :
    matchesLoc l uri = true := by
  unfold regexHit at h; unfold matchesLoc
  split at h <;> simp_all

theorem regexHit_kind (uri : Bytes) (l : Location) (h : regexHit uri l = true) :
    ∃ re, l.kind = .regex re ∧ regexMatches re uri = true := by
  unfold regexHit at h
  split at h
  · rename_i re hk; exact ⟨re, hk, h⟩
  · cases h

theorem prefixLoc_matches (uri : Bytes) (l : Location) (hp : isPrefixLoc l = true)
    (hu : isPrefixB l.uri uri = true) : matchesLoc l uri = true := by
  unfold isPrefixLoc at hp; unfold matchesLoc
  split at hp <;> simp_all

theorem mem_prefixFilter {locs : List Location} {uri : Bytes} {l : Location}
    (h : l ∈ locs.filter fun l => isPrefixLoc l && isPrefixB l.uri uri) :
    l ∈ locs ∧ isPrefixLoc l = true ∧ isPrefixB l.uri uri = true := by
  simp only [List.mem_filter, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The regex matcher is exact**: it accepts a URI iff the URI is in the regex's language
(`Matches`, the textbook inductive semantics), for every regex and every URI. -/
theorem regexMatches_iff (re : Re) (uri : Bytes) : regexMatches re uri = true ↔ Matches re uri :=
  matchB_iff re uri

/-- The selected location is one of the configured ones and matches the URI. -/
theorem selectLocation_sound (locs : List Location) (uri : Bytes) (l : Location)
    (h : selectLocation locs uri = some l) : l ∈ locs ∧ matchesLoc l uri = true := by
  unfold selectLocation at h
  split at h
  · rename_i l' hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨List.mem_of_find?_eq_some hf, by simp [matchesLoc, hp.1, hp.2]⟩
  · split at h
    · rename_i p hl
      have hpm : p ∈ locs ∧ matchesLoc p uri = true := by
        rcases longest_mem _ none p hl with hm | hm
        · obtain ⟨h1, h2, h3⟩ := mem_prefixFilter hm
          exact ⟨h1, prefixLoc_matches uri p h2 h3⟩
        · cases hm
      split at h
      · cases h; exact hpm
      · cases h
        cases hf : locs.find? (regexHit uri) with
        | none => simpa [hf] using hpm
        | some r =>
          simp only [hf, Option.getD_some]
          exact ⟨List.mem_of_find?_eq_some hf, regexHit_matches uri r (List.find?_some hf)⟩
    · exact ⟨List.mem_of_find?_eq_some h, regexHit_matches uri l (List.find?_some h)⟩

/-- An exact (`=`) location that equals the URI always wins. -/
theorem selectLocation_exact (locs : List Location) (uri : Bytes)
    (he : ∃ l ∈ locs, l.kind = .exact ∧ l.uri = uri) :
    ∃ l, selectLocation locs uri = some l ∧ l.kind = .exact ∧ l.uri = uri := by
  unfold selectLocation
  split
  · rename_i l hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨l, rfl, hp⟩
  · rename_i hf
    obtain ⟨l, hl, hk, hu⟩ := he
    have := List.find?_eq_none.mp hf l hl
    simp [hk, hu] at this

/-- When a prefix location is selected, no matching prefix location is longer. -/
theorem selectLocation_longest (locs : List Location) (uri : Bytes) (l : Location)
    (h : selectLocation locs uri = some l) (hk : isPrefixLoc l = true) :
    ∀ l' ∈ locs, isPrefixLoc l' = true → isPrefixB l'.uri uri = true →
      l'.uri.length ≤ l.uri.length := by
  intro l' hl' hk' hp'
  have hmem : l' ∈ locs.filter fun l => isPrefixLoc l && isPrefixB l.uri uri := by
    simp [hl', hk', hp']
  unfold selectLocation at h
  split at h
  · rename_i l0 hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    simp [isPrefixLoc, hp.1] at hk
  · split at h
    · rename_i p hl
      have hmax := (longest_max _ none p hl).1 l' hmem
      split at h
      · cases h; exact hmax
      · cases h
        cases hf : locs.find? (regexHit uri) with
        | none => simpa [hf] using hmax
        | some r =>
          simp only [hf, Option.getD_some] at hk
          obtain ⟨re, hre, _⟩ := regexHit_kind uri r (List.find?_some hf)
          simp [isPrefixLoc, hre] at hk
    · obtain ⟨re, hre, _⟩ := regexHit_kind uri l (List.find?_some h)
      simp [isPrefixLoc, hre] at hk

/-- A regex location is selected only as the **first** regex location (in configuration order)
whose regex matches the URI. -/
theorem selectLocation_regex (locs : List Location) (uri : Bytes) (l : Location) (re : Re)
    (h : selectLocation locs uri = some l) (hk : l.kind = .regex re) :
    locs.find? (regexHit uri) = some l := by
  unfold selectLocation at h
  split at h
  · rename_i l0 hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1] at hk; cases hk
  · split at h
    · rename_i p hl
      have hpk : isPrefixLoc p = true := by
        rcases longest_mem _ none p hl with hm | hm
        · exact (mem_prefixFilter hm).2.1
        · cases hm
      split at h
      · cases h; simp [isPrefixLoc, hk] at hpk
      · cases h
        cases hf : locs.find? (regexHit uri) with
        | none => simp only [hf, Option.getD_none] at hk; simp [isPrefixLoc, hk] at hpk
        | some r => simp [hf]
    · exact h

/-- A plain prefix location is selected only when no regex location matches the URI. -/
theorem selectLocation_prefix_no_regex (locs : List Location) (uri : Bytes) (l : Location)
    (h : selectLocation locs uri = some l) (hk : l.kind = .pre) :
    locs.find? (regexHit uri) = none := by
  unfold selectLocation at h
  split at h
  · rename_i l0 hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1] at hk; cases hk
  · split at h
    · split at h
      · rename_i hn; cases h; simp [hk] at hn
      · cases h
        cases hf : locs.find? (regexHit uri) with
        | none => rfl
        | some r =>
          simp only [hf, Option.getD_some] at hk
          obtain ⟨re, hre, _⟩ := regexHit_kind uri r (List.find?_some hf)
          rw [hre] at hk; cases hk
    · obtain ⟨re, hre, _⟩ := regexHit_kind uri l (List.find?_some h)
      rw [hre] at hk; cases hk

/-- The example from the nginx documentation of `location`:
`= /` (A), `/` (B), `/documents/` (C), `^~ /images/` (D), `~* \.(gif|jpg|jpeg)$` (E). -/
def docRe : Re :=
  match compileRegex true b!"\\.(gif|jpg|jpeg)$" with
  | .ok r => r
  | .error _ => .none

def docLocs : List Location :=
  [{ kind := .exact, uri := b!"A" }, { kind := .pre, uri := b!"/" },
   { kind := .pre, uri := b!"/documents/" }, { kind := .noRegex, uri := b!"/images/" },
   { kind := .regex docRe, uri := b!"E" }]

def docPick (uri : Bytes) : Option Bytes :=
  (selectLocation ({ kind := .exact, uri := b!"/" } :: docLocs.drop 1) uri).map fun l =>
    if l.kind == .exact then b!"A" else if l.uri == b!"/" then b!"B"
    else if l.uri == b!"/documents/" then b!"C" else if l.uri == b!"/images/" then b!"D" else l.uri

theorem vector_location_doc :
    docPick b!"/" = some b!"A" ∧
    docPick b!"/index.html" = some b!"B" ∧
    docPick b!"/documents/document.html" = some b!"C" ∧
    docPick b!"/images/1.gif" = some b!"D" ∧
    docPick b!"/documents/1.jpg" = some b!"E" ∧
    docPick b!"/documents/1.JPG" = some b!"E" := by
  decide +kernel

/-- Regex syntax: anchors, classes, alternation, counted repetition, `\d`, case folding. -/
theorem vector_regex :
    (compileRegex false b!"^/api/v[0-9]+/").toOption.map (regexMatches · b!"/api/v12/x") = some true ∧
    (compileRegex false b!"^/api/v[0-9]+/").toOption.map (regexMatches · b!"/x/api/v1/") = some false ∧
    (compileRegex false b!"^/(foo|bar)\\d{2,3}$").toOption.map (regexMatches · b!"/bar123") = some true ∧
    (compileRegex false b!"^/(foo|bar)\\d{2,3}$").toOption.map (regexMatches · b!"/bar1234") = some false ∧
    (compileRegex false b!"\\.php$").toOption.map (regexMatches · b!"/index.PHP") = some false ∧
    (compileRegex true b!"\\.php$").toOption.map (regexMatches · b!"/index.PHP") = some true ∧
    (compileRegex false b!"[^/]+\\.css$").toOption.map (regexMatches · b!"/a/b.css") = some true := by
  decide +kernel

/-- Unsupported regex features are configuration errors, not silent mismatches. -/
theorem vector_regex_errors :
    (compileRegex false b!"a(b").toOption.isNone = true ∧
    (compileRegex false b!"(\\w+)/\\1").toOption.isNone = true ∧
    (compileRegex false b!"/(?!x)").toOption.isNone = true ∧
    (compileRegex false b!"*a").toOption.isNone = true := by
  decide +kernel

/-! ## 4. Serving files: confinement (nginx-tests: `http_alias.t`, `index.t`, `autoindex.t`) -/

/-- **Confinement.** For every configuration, request and file-system state: every path that
routing `stat`s, serves or lists is the matched location's directory (its `alias`, else its
effective `root`) followed by safe segments. No `..`, no absolute path, no escape from the
configured directory; this includes nginx's classic `alias` off-by-slash traversal
(`location /img { alias /data/img/; }` + `GET /img../secret`). -/
theorem route_confined (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (raw : Bytes)
    (np : NPath) (hn : normalizePath raw = some np) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    (route h sv req v np).Confined (Under (baseOf l (effective h sv l))) :=
  route_confined' h sv req v np (normalizePath_safe raw np hn)

/-- The same, for the action finally taken, under any answers to the `stat` questions. -/
theorem route_serves_under (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (raw : Bytes)
    (np : NPath) (hn : normalizePath raw = some np) (o : Bytes → Option Kind) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    ((route h sv req v np).run o).Touches (Under (baseOf l (effective h sv l))) :=
  confined_run _ o _ (route_confined h sv req v raw np hn)

/-- A test server: `root /srv/www;`, `location /img { alias /data/img/; }`,
`location /f/ { autoindex on; }`, `location = /health { return 200 "ok"; }`. -/
def tServer : Server :=
  { s := { root := some b!"/srv/www" },
    locations := [{ kind := .pre, uri := b!"/img", alias := some b!"/data/img/" },
                  { kind := .pre, uri := b!"/f/", s := { autoindex := some true } },
                  { kind := .exact, uri := b!"/health", ret := some (200, some b!"ok") }] }

def tReq (m path : Bytes) : Request :=
  { method := m, target := path, path, query := none, minor := 1, headers := [],
    host := some b!"t", contentLength := 0 }

def tVars : Vars := { uri := [], requestUri := [], args := [], host := b!"t", method := b!"GET",
                      remoteAddr := [], serverPort := b!"80" }

/-- A file system with `/srv/www/index.html`, `/srv/www/f/` and `/data/img/a.png`. -/
def tFs (p : Bytes) : Option Kind :=
  if p == b!"/srv/www/index.html" then some (.file 10 0)
  else if p == b!"/data/img/a.png" then some (.file 20 0)
  else if p == b!"/srv/www/f" || p == b!"/srv/www" then some .dir
  else none

def tRoute (m path : Bytes) : Option Action :=
  (normalizePath path).map fun np => (route {} tServer (tReq m path) tVars np).run tFs

/-- `/` finds `index.html` (internal redirect), files are served, directories without a slash
are redirected, `autoindex` lists, `return` answers, unknown paths are 404, POST is 405. -/
theorem vector_routes :
    tRoute b!"GET" b!"/" = some (.internal ⟨[b!"index.html"], false⟩ none) ∧
    tRoute b!"GET" b!"/index.html" = some (.file b!"/srv/www/index.html" 10 0) ∧
    tRoute b!"GET" b!"/f" = some (.redirect 301 b!"/f/") ∧
    tRoute b!"GET" b!"/f/" = some (.autoindex b!"/srv/www/f") ∧
    tRoute b!"GET" b!"/health" = some (.text 200 b!"ok") ∧
    tRoute b!"GET" b!"/nope" = some (.error 404) ∧
    tRoute b!"POST" b!"/index.html" = some (.error 405) := by
  decide +kernel

/-- `alias` replaces the location prefix; the off-by-slash traversal finds nothing. -/
theorem vector_alias :
    tRoute b!"GET" b!"/img/a.png" = some (.file b!"/data/img/a.png" 20 0) ∧
    tRoute b!"GET" b!"/img../srv/www/index.html" = some (.error 404) := by
  decide +kernel

/-! ## 4b. Serving files: the right file (nginx docs, `root`, `alias`, `autoindex`;
nginx-tests: `http_alias.t`, `autoindex.t`) -/

/-- **The right file, with `root`.** For every configuration, request and file system: a GET or
HEAD for a file path (`/a/b.html`) in a location with a `root` and without `alias`, `return`,
`proxy_pass` or `try_files` looks at exactly one path, `root` followed by the request's URI, and

* serves *that* file if it exists (never another one),
* redirects to the same URI plus `/` if it is a directory,
* answers 404 if nothing is there. -/
theorem route_serves_root_file (h : HttpConf) (sv : Server) (req : Request) (v : Vars)
    (raw : Bytes) (np : NPath) (hn : normalizePath raw = some np) (o : Bytes → Option Kind)
    (l : Location) (hl : (selectLocation sv.locations np.uri).getD defaultLocation = l)
    (hsv : sv.ret = none) (hret : l.ret = none) (hpx : l.proxy = none)
    (htf : l.tryFiles = none) (hal : l.alias = none)
    (hm : req.method = b!"GET" ∨ req.method = b!"HEAD") (hd : np.dir = false) :
    let root := dropTrailingSlash ((effective h sv l).root.getD defaultRoot)
    (route h sv req v np).run o =
      match o (root ++ np.uri) with
      | some (.file size mtime) => .file (root ++ np.uri) size mtime
      | some .dir => .redirect 301 (withQuery (percentEncode (np.uri ++ [47])) req.query)
      | none => .error 404 := by
  intro root
  have hs := route_static h sv req v np o l root np.segs hl hsv hret hpx htf hm hd
    (by simp [fsTarget, hal, root])
  rw [← normalizePath_file_uri raw np hn hd] at hs
  exact hs

/-- **The right file, with `alias`.** `location /img { alias /data/img/; }` (or
`location /img/ …`): a GET or HEAD for `/img/x/y` looks at exactly `/data/img/x/y` and answers
from it as above. Stated for every location prefix `/p₁/…/pₖ` (with or without the trailing
slash) and every remainder `x/y/…` below it. -/
theorem route_serves_alias_file (h : HttpConf) (sv : Server) (req : Request) (v : Vars)
    (raw : Bytes) (np : NPath) (hn : normalizePath raw = some np) (o : Bytes → Option Kind)
    (l : Location) (hl : (selectLocation sv.locations np.uri).getD defaultLocation = l)
    (hsv : sv.ret = none) (hret : l.ret = none) (hpx : l.proxy = none)
    (htf : l.tryFiles = none) (a : Bytes) (hal : l.alias = some a)
    (hm : req.method = b!"GET" ∨ req.method = b!"HEAD") (hd : np.dir = false)
    (p rest : List Bytes) (hsegs : np.segs = p ++ rest) (hne : rest ≠ [])
    (hpre : l.uri = joinSegs p ∨ l.uri = joinSegs p ++ [47]) :
    let file := dropTrailingSlash a ++ joinSegs rest
    (route h sv req v np).run o =
      match o file with
      | some (.file size mtime) => .file file size mtime
      | some .dir => .redirect 301 (withQuery (percentEncode (np.uri ++ [47])) req.query)
      | none => .error 404 := by
  intro file
  have hsafe : ∀ s ∈ p ++ rest, Safe s := hsegs ▸ normalizePath_safe raw np hn
  have hu := normalizePath_file_uri raw np hn hd
  refine route_static h sv req v np o l _ rest hl hsv hret hpx htf hm hd ?_
  simp only [fsTarget, hal, hu, hsegs, alias_segs p rest l.uri hsafe hpre hne]
  rfl

/-- **No directory listing unless it is switched on.** For every configuration, request and
file system: if routing answers with a directory listing, then `autoindex on` is in effect for
the location that handled the request (set there, in its `server`, or in `http`). -/
theorem route_lists_only_if_enabled (h : HttpConf) (sv : Server) (req : Request) (v : Vars)
    (np : NPath) (o : Bytes → Option Kind) (p : Bytes)
    (hr : (route h sv req v np).run o = .autoindex p) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    (effective h sv l).autoindex = some true :=
  route_autoindex' h sv req v np o p hr

/-- **Files outside the served directory cannot change the answer.** Two file systems that agree
on everything under the location's directory (its `alias`, else its `root`) give the same
routing result for every configuration and request, whatever else exists, changes, or is
missing on the machine. -/
theorem route_outside_irrelevant (h : HttpConf) (sv : Server) (req : Request) (v : Vars)
    (raw : Bytes) (np : NPath) (hn : normalizePath raw = some np) (o₁ o₂ : Bytes → Option Kind) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    (∀ path, Under (baseOf l (effective h sv l)) path → o₁ path = o₂ path) →
    (route h sv req v np).run o₁ = (route h sv req v np).run o₂ := by
  intro l hag
  exact run_congr _ o₁ o₂ hag _ (route_confined h sv req v raw np hn)

/-- `location /img/ { alias /data/img/; }` and a file system with `/data/img/x/a.png`. -/
def tAliasServer : Server :=
  { s := { root := some b!"/srv/www" },
    locations := [{ kind := .pre, uri := b!"/img/", alias := some b!"/data/img/" }] }

def tAliasFs (p : Bytes) : Option Kind :=
  if p == b!"/data/img/x/a.png" then some (.file 5 0) else none

def tAliasRoute (path : Bytes) : Option Action :=
  (normalizePath path).map fun np => (route {} tAliasServer (tReq b!"GET" path) tVars np).run tAliasFs

/-- The trailing-slash spelling of an alias location, on concrete requests. -/
theorem vector_alias_slash :
    tAliasRoute b!"/img/x/a.png" = some (.file b!"/data/img/x/a.png" 5 0) ∧
    tAliasRoute b!"/img/x/b.png" = some (.error 404) ∧
    tAliasRoute b!"/img/../../etc/passwd" = none := by
  decide +kernel

/-! ## 4c. `try_files` and internal redirects: no second decoding (nginx docs, `try_files`,
`index`; nginx-tests: `http_try_files.t`, `index.t`)

A location is selected, and its `auth_basic` checked, on the normalised request path. These specs
say that what `try_files` and internal redirects do afterwards is about that same path: a
double-encoded request (`/%2561dmin/…`) cannot be routed by one location and then served from
another one's files. -/

/-- **`try_files $uri $uri/ …` serves the file the request names.** For every configuration,
request and file system: in a location with a `root` (no `alias`) whose `try_files` entries
before the fallback are `$uri` or `$uri/`, the only file that can be served is `root` followed by
the request's own `$uri`, the URI the location was selected on (and, with `routeAuth`, the one
`auth_basic` was decided for). In particular a file is never served for a directory path. -/
theorem tryFiles_uri_serves_request_file (h : HttpConf) (sv : Server) (req : Request) (v : Vars)
    (raw : Bytes) (np : NPath) (hn : normalizePath raw = some np) (hv : v.uri = np.uri)
    (o : Bytes → Option Kind) (l : Location)
    (hl : (selectLocation sv.locations np.uri).getD defaultLocation = l)
    (hal : l.alias = none) (items : List Bytes) (last : Bytes)
    (htf : l.tryFiles = some (items ++ [last]))
    (hitems : ∀ i ∈ items, i = b!"$uri" ∨ i = b!"$uri/")
    (path : Bytes) (size : Nat) (mtime : Int)
    (hr : (route h sv req v np).run o = .file path size mtime) :
    path = dropTrailingSlash ((effective h sv l).root.getD defaultRoot) ++ np.uri := by
  obtain ⟨d, _, hd⟩ := normalizePath_decoded raw np hn
  have hs := normalizeDecoded_safe d np hd
  have hroot := normalizeDecoded_root_dir d np hd
  have key : ∀ st : Step, st = route h sv req v np → st.run o = .file path size mtime →
      np.dir = false ∧
      path = dropTrailingSlash ((effective h sv l).root.getD defaultRoot) ++ joinSegs np.segs := by
    intro st hst hrun
    unfold route at hst
    split at hst
    · subst hst; exact absurd hrun (retAction_ne_file _ _ _ _ _)
    · simp only [hl] at hst
      split at hst
      · subst hst; exact absurd hrun (retAction_ne_file _ _ _ _ _)
      · subst hst; simp [Step.run] at hrun
      · split at hst
        · subst hst; simp [Step.run] at hrun
        · simp only [htf] at hst
          subst hst
          exact tryFiles_uri_file l _ v req.query np hs hroot hv hal o last items hitems
            path size mtime hrun
  obtain ⟨hdir, hp⟩ := key _ rfl hr
  rw [hp, normalizeDecoded_file_uri d np hd hdir]

/-- **Internal redirects stay normalised.** For every configuration, request and file system: when
routing a path of safe segments ends in an internal redirect (an index file was found, or
`try_files` fell back to its last entry), the path it redirects to is made of safe segments
again. The IO shell routes that path as it is, so every routing spec applies again at each hop. -/
theorem route_internal_safe (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (hnp : ∀ s ∈ np.segs, Safe s) (o : Bytes → Option Kind) (np' : NPath) (q : Option Bytes)
    (hr : (route h sv req v np).run o = .internal np' q) : ∀ s ∈ np'.segs, Safe s := by
  have := redirectsSafe_run o _ (route_redirects' h sv req v np hnp)
  rw [hr] at this
  exact this

/-- **Confinement survives internal redirects.** After a request path was routed to an internal
redirect, routing the redirect's path (with whatever method, query and variables the shell then
uses) is confined to the directory of the location selected for *that* path. -/
theorem route_confined_after_redirect (h : HttpConf) (sv : Server) (req req' : Request)
    (v v' : Vars) (raw : Bytes) (np : NPath) (hn : normalizePath raw = some np)
    (o : Bytes → Option Kind) (np' : NPath) (q : Option Bytes)
    (hr : (route h sv req v np).run o = .internal np' q) :
    let l := (selectLocation sv.locations np'.uri).getD defaultLocation
    (route h sv req' v' np').Confined (Under (baseOf l (effective h sv l))) :=
  route_confined' h sv req' v' np'
    (route_internal_safe h sv req v np (normalizePath_safe raw np hn) o np' q hr)

/-- The target of a `try_files` fallback or an `error_page` is made of safe segments, and is taken
as written: `internalTarget` splits off the query and normalises, without decoding. -/
theorem internalTarget_segments_safe (u : Bytes) (np : NPath) (q : Option Bytes)
    (h : internalTarget u = some (np, q)) : ∀ s ∈ np.segs, Safe s :=
  internalTarget_safe u np q h

/-- A server with a protected directory and a denied file next to a `try_files` location, all
under one `root`: `root /srv/www;`, `location /admin/ { auth_basic "admin"; }`,
`location = /secret.html { return 403; }`, `location /app/ { try_files $uri /app/index.html?p=$uri; }`,
`location / { try_files $uri $uri/ =404; }`. -/
def tGuardServer : Server :=
  { s := { root := some b!"/srv/www" },
    locations := [{ kind := .pre, uri := b!"/admin/", s := { authBasic := some (some b!"admin") } },
                  { kind := .exact, uri := b!"/secret.html", ret := some (403, none) },
                  { kind := .pre, uri := b!"/app/",
                    tryFiles := some [b!"$uri", b!"/app/index.html?p=$uri"] },
                  { kind := .pre, uri := b!"/", tryFiles := some [b!"$uri", b!"$uri/", b!"=404"] }] }

/-- A file system with `/srv/www/admin/secret.txt`, `/srv/www/secret.html`, `/srv/www/pub.txt`,
and two directories with awkward names that hold an `index.html`: `a?b` and `100%`. -/
def tGuardFs (p : Bytes) : Option Kind :=
  if p == b!"/srv/www/admin/secret.txt" || p == b!"/srv/www/secret.html" ||
     p == b!"/srv/www/pub.txt" || p == b!"/srv/www/a?b/index.html" ||
     p == b!"/srv/www/100%/index.html" then some (.file 7 0)
  else if p == b!"/srv/www" || p == b!"/srv/www/admin" || p == b!"/srv/www/a?b" ||
     p == b!"/srv/www/100%" then some .dir
  else none

/-- Route a request without credentials, as the server does (`$uri` is the normalised path). -/
def tGuardRoute (path : Bytes) : Option Action :=
  (normalizePath path).map fun np =>
    (routeAuth {} tGuardServer (tReq b!"GET" path) { tVars with uri := np.uri } np (fun _ => []) none).run tGuardFs

/-- **Double encoding does not get around `auth_basic` or a `location` that denies.** The
protected file asks for credentials however its path is spelled once-encoded; spelled
twice-encoded (`%2561dmin`, `%252e%252e`, `%2573ecret.html`) it is a different, non-existent
path, not a way into `/admin/` or to `/secret.html` through the `try_files` of `location /`. -/
theorem vector_try_files_double_encoding :
    tGuardRoute b!"/pub.txt" = some (.file b!"/srv/www/pub.txt" 7 0) ∧
    tGuardRoute b!"/admin/secret.txt" = some (.error 401) ∧
    tGuardRoute b!"/%61dmin/secret.txt" = some (.error 401) ∧
    tGuardRoute b!"/x/%2e%2e/admin/secret.txt" = some (.error 401) ∧
    tGuardRoute b!"/%2561dmin/secret.txt" = some (.error 404) ∧
    tGuardRoute b!"/admin%252Fsecret.txt" = some (.error 404) ∧
    tGuardRoute b!"/x/%252e%252e/admin/secret.txt" = some (.error 404) ∧
    tGuardRoute b!"/secret.html" = some (.error 403) ∧
    tGuardRoute b!"/%2573ecret.html" = some (.error 404) := by
  decide +kernel

/-- Index files are found by segments, so a directory whose name contains `?` or `%` works: the
redirect names the file that was just found (no split at `?`, no decoding), and routing that
path serves it. A `try_files` fallback is a URI: its query is split off, its path is not decoded. -/
theorem vector_internal_redirects :
    tGuardRoute b!"/a%3Fb/" = some (.internal ⟨[b!"a?b", b!"index.html"], false⟩ none) ∧
    tGuardRoute b!"/100%25/" = some (.internal ⟨[b!"100%", b!"index.html"], false⟩ none) ∧
    (route {} tGuardServer (tReq b!"GET" []) { tVars with uri := b!"/a?b/index.html" }
      ⟨[b!"a?b", b!"index.html"], false⟩).run tGuardFs =
      .file b!"/srv/www/a?b/index.html" 7 0 ∧
    tGuardRoute b!"/app/%2561" =
      some (.internal ⟨[b!"app", b!"index.html"], false⟩ (some b!"p=/app/%61")) ∧
    internalTarget b!"/50x.html" = some (⟨[b!"50x.html"], false⟩, none) ∧
    internalTarget b!"/e/%2e%2e/x?a=1" = some (⟨[b!"e", b!"%2e%2e", b!"x"], false⟩, some b!"a=1") ∧
    internalTarget b!"@named" = none := by
  decide +kernel

/-! ## 5. Responses (nginx-tests: `http_headers_multi.t`, `range.t`, `not_modified.t`) -/

/-- **No header injection into responses.** Whatever a header value contains (config,
redirect target, upstream response), what `renderHead` writes for it has no NUL, CR or LF… -/
theorem renderHead_values_safe (v : Bytes) : ∀ c ∈ cleanValue v, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 :=
  cleanValue_safe v

/-- …and a header name has no NUL, CR, LF, space or colon. -/
theorem renderHead_names_safe (n : Bytes) :
    ∀ c ∈ cleanName n, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 32 ∧ c ≠ 58 :=
  cleanName_safe n

/-- HTML-escaped text (autoindex names, page titles) has no `<`, `>` or `"`. -/
theorem htmlEscape_no_markup (b : Bytes) : ∀ c ∈ htmlEscape b, c ≠ 60 ∧ c ≠ 62 ∧ c ≠ 34 :=
  htmlEscape_safe b

/-- A satisfiable range lies inside the file. -/
theorem resolveRange_in_file (size : Nat) (spec : Bytes) (a b : Nat)
    (h : resolveRange size spec = .part a b) : a ≤ b ∧ b < size :=
  resolveRange_bounds size spec a b h

/-- The bytes a file response sends lie inside the file, and `Content-Length` is their count. -/
theorem fileResponse_body_in_file (req : Request) (mime : Bytes) (size : Nat) (mtime : Int)
    (off len : Nat) (h : (fileResponse req mime size mtime).body = some (off, len)) :
    off + len ≤ size ∧
      (b!"Content-Length", decDigits len) ∈ (fileResponse req mime size mtime).headers := by
  unfold fileResponse at *
  simp only at *
  split at *
  · simp at h
  · rename_i hnm
    have hb : ∀ a b, chosenRange req size (etag size mtime) (httpDate mtime) = .part a b →
        a ≤ b ∧ b < size := by
      intro a b hr
      unfold chosenRange at hr
      simp only at hr
      repeat' split at hr
      all_goals first | exact resolveRange_bounds _ _ _ _ hr | cases hr
    revert h hb
    generalize chosenRange req size (etag size mtime) (httpDate mtime) = rr
    intro h hb
    cases rr with
    | full =>
      simp only [rangeResponse, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by simp [rangeResponse, hnm]⟩
    | part a b =>
      have := hb a b rfl
      simp only [rangeResponse, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by simp [rangeResponse, hnm]⟩
    | unsat => simp [rangeResponse] at h

/-- Ranges: first-last, suffix, open-ended, unsatisfiable, multiple (ignored). -/
theorem vector_ranges :
    resolveRange 1000 b!"bytes=0-499" = .part 0 499 ∧
    resolveRange 1000 b!"bytes=-500" = .part 500 999 ∧
    resolveRange 1000 b!"bytes=900-" = .part 900 999 ∧
    resolveRange 1000 b!"bytes=900-5000" = .part 900 999 ∧
    resolveRange 1000 b!"bytes=1000-" = .unsat ∧
    resolveRange 1000 b!"bytes=0-1,5-6" = .full ∧
    resolveRange 1000 b!"items=0-1" = .full := by
  decide +kernel

/-- HTTP dates (RFC 9110 §5.6.7 example, and the epoch). -/
theorem vector_http_date : httpDate 784111777 = b!"Sun, 06 Nov 1994 08:49:37 GMT" ∧
    httpDate 0 = b!"Thu, 01 Jan 1970 00:00:00 GMT" ∧
    httpDate 1795089600 = b!"Thu, 19 Nov 2026 12:00:00 GMT" := by
  decide +kernel

/-- nginx's ETag format: `"<mtime hex>-<size hex>"`. -/
theorem vector_etag : etag 612 1700000000 = b!"\"6553f100-264\"" := by decide +kernel

/-- Status lines. -/
theorem vector_status : statusLine 404 = b!"HTTP/1.1 404 Not Found\r\n" ∧
    statusLine 299 = b!"HTTP/1.1 299\r\n" := by decide +kernel

/-! ## 5b. gzip (nginx-tests: `gzip.t`) -/

/-- **Compression never corrupts data** (lean-zip's theorem, restated here so that our build
checks it): decompressing what the server sends returns the file, for every file and level. -/
theorem gzip_roundtrip (data : ByteArray) (level : UInt8) (maxOut : Nat) (h : data.size ≤ maxOut) :
    Zip.Native.GzipDecode.decompressSingle (Zip.Native.GzipEncode.compress data level) maxOut =
      .ok data :=
  Zip.Native.gzip_decompressSingle_compress data level maxOut h

/-- A response is only compressed for a client that accepts gzip, and never for a range
request (so `Content-Range` always refers to the file's own bytes). -/
theorem gzipApplies_requires (eff : Settings) (req : Request) (mime : Bytes) (size : Nat)
    (h : gzipApplies eff req mime size = true) :
    acceptsGzip req.headers = true ∧ header? req.headers b!"range" = none ∧
      eff.gzip = some true := by
  unfold gzipApplies at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨hg, ha⟩, _⟩, _⟩, hr⟩ := h
  refine ⟨ha, hr, ?_⟩
  cases hgz : eff.gzip with
  | none => simp [hgz] at hg
  | some b => simp [hgz] at hg; simp [hg]

/-- `Accept-Encoding` parsing: lists, parameters, `q=0` refusals, `*`. -/
theorem vector_accept_encoding :
    acceptsGzip [(b!"accept-encoding", b!"gzip, deflate, br")] = true ∧
    acceptsGzip [(b!"accept-encoding", b!"br;q=1.0, GZIP;q=0.8")] = true ∧
    acceptsGzip [(b!"accept-encoding", b!"br, gzip;q=0")] = false ∧
    acceptsGzip [(b!"accept-encoding", b!"*")] = true ∧
    acceptsGzip [(b!"accept-encoding", b!"identity")] = false ∧
    acceptsGzip [] = false := by
  decide +kernel

/-- `text/html` is always compressible; other types only when listed; parameters are ignored. -/
def gzEff : Settings := { gzip := some true, gzipTypes := some [b!"text/css"] }

def gzReq : Request :=
  { method := b!"GET", target := b!"/", path := b!"/", query := none, minor := 1,
    headers := [(b!"accept-encoding", b!"gzip")], host := none, contentLength := 0 }

theorem vector_gzip_types :
    gzipApplies gzEff gzReq b!"text/html; charset=utf-8" 100 = true ∧
    gzipApplies gzEff gzReq b!"text/css" 100 = true ∧
    gzipApplies gzEff gzReq b!"image/png" 100 = false ∧
    gzipApplies gzEff gzReq b!"text/html" 10 = false ∧
    gzipApplies { gzEff with gzip := some false } gzReq b!"text/html" 100 = false := by
  decide +kernel

/-! ## 6. Virtual hosts and variables (nginx-tests: `http_server_name.t`, `http_variables.t`) -/

/-- The selected server listens on the port the request came in on. -/
theorem selectServer_port (servers : List Server) (port : Nat) (host : Option Bytes) (s : Server)
    (h : selectServer servers port host = some s) :
    s ∈ servers ∧ s.listens.any (·.port == port) = true := by
  have key : s ∈ serversOn servers port := by
    unfold selectServer at h
    simp only [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff] at h
    rcases h with h | ⟨_, h | ⟨_, h⟩⟩
    · cases host with
      | none => simp at h
      | some hh =>
        simp only [Option.bind_some, Option.orElse_eq_orElse, Option.orElse_eq_or,
          Option.or_eq_some_iff] at h
        rcases h with h | ⟨_, h⟩
        · exact List.mem_of_find?_eq_some h
        · exact List.mem_of_find?_eq_some h
    · exact List.mem_of_find?_eq_some h
    · exact List.mem_of_mem_head? h
  simpa [serversOn, List.mem_filter] using key

/-- Server names: exact, `*.suffix` (sub-domains only), `.suffix` (domain and sub-domains). -/
theorem vector_server_names :
    nameMatches b!"example.com" b!"example.com" = true ∧
    nameMatches b!"*.example.com" b!"www.example.com" = true ∧
    nameMatches b!"*.example.com" b!"example.com" = false ∧
    nameMatches b!".example.com" b!"example.com" = true ∧
    nameMatches b!".example.com" b!"a.b.example.com" = true ∧
    nameMatches b!"example.com" b!"evil-example.com" = false := by
  decide +kernel

/-- Variables expand like nginx; unknown ones stay literal. -/
theorem vector_expand :
    expand { tVars with uri := b!"/a", args := b!"x=1" } b!"$uri/ ${uri}.html $is_args$args $nope" =
      b!"/a/ /a.html ?x=1 $nope" := by
  decide +kernel

/-! ## 7. Configuration syntax (nginx-tests: `config` tests, `nginx -t`) -/

theorem vector_lex : lex b!"root \"/a b\"; # comment\nlocation = / { }" =
    .ok [.word b!"root", .word b!"/a b", .semi, .word b!"location", .word b!"=", .word b!"/",
         .lbrace, .rbrace] := by
  decide +kernel

theorem vector_parse_shape :
    ((parseDirectives b!"events {} http { server { listen 8080; } }").toOption.map
      fun ds => ds.map (·.name)) = some [b!"events", b!"http"] := by
  decide +kernel

theorem vector_unterminated :
    (parseDirectives b!"http { root /x }").toOption.isNone = true ∧
    (parseDirectives b!"http { root /x;").toOption.isNone = true := by
  decide +kernel

theorem vector_listen :
    (parseListen [b!"8080"]).toOption.map (fun l => (l.port, l.default)) = some (8080, false) ∧
    (parseListen [b!"127.0.0.1:81", b!"default_server"]).toOption.map (fun l => (l.port, l.default)) =
      some (81, true) ∧
    (parseListen [b!"99999"]).toOption.isNone = true := by
  decide +kernel

theorem vector_sizes : parseSize b!"1m" = some 1048576 ∧ parseSize b!"10k" = some 10240 ∧
    parseTime b!"75s" = some 75 ∧ parseTime b!"2m" = some 120 := by
  decide +kernel

/-! ## 8. Basic authentication (nginx docs, `auth_basic`; nginx-tests: `auth_basic.t`) -/

/-- A request without an `Authorization` header never passes. -/
theorem basicOk_none (users : List (Bytes × Bytes)) : basicOk users none = false := rfl

/-- `basicOk` only accepts a `Basic` header whose user is in the user file and whose password
matches that user's stored hash. -/
theorem basicOk_sound (users : List (Bytes × Bytes)) (authz : Option Bytes)
    (h : basicOk users authz = true) :
    ∃ v u p hash, authz = some v ∧ basicCreds v = some (u, p) ∧ (u, hash) ∈ users ∧
      verifyCrypt hash p = true := by
  unfold basicOk at h
  cases authz with
  | none => simp at h
  | some v =>
    cases hc : basicCreds v with
    | none => simp [hc] at h
    | some up =>
      obtain ⟨u, p⟩ := up
      simp only [Option.bind_some, hc, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨u', hash⟩, hmem, hu, hv⟩ := h
      simp only at hu hv
      exact ⟨v, u, p, hash, rfl, hc, hu ▸ hmem, hv⟩

/-- **A password check does a bounded amount of work.** A password longer than `maxPasswordLen`
(511 bytes, the longest that libxcrypt's `crypt` takes) never matches, whatever the stored hash:
`verifyCrypt` answers before it hashes anything. The password is attacker-chosen (it comes from
the `Authorization` header, which may be tens of kilobytes) and SHA-256-crypt's cost grows with
the square of its length. -/
theorem verifyCrypt_long_password (h pw : Bytes) (hl : maxPasswordLen < pw.length) :
    verifyCrypt h pw = false := by
  simp [verifyCrypt, hl]

/-- So a `Basic` header with such a password is refused, for every user and every user file. -/
theorem basicOk_long_password (users : List (Bytes × Bytes)) (v u p : Bytes)
    (hc : basicCreds v = some (u, p)) (hl : maxPasswordLen < p.length) :
    basicOk users (some v) = false := by
  simp [basicOk, hc, verifyCrypt_long_password _ p hl]

/-- For every password that does get hashed, the one input of SHA-256-crypt that grows
quadratically (the password repeated once per byte of itself, hashed into its "P" digest) is
under 256 KiB. -/
theorem cryptWork_bounded (pw : Bytes) (hl : pw.length ≤ maxPasswordLen) :
    (repeatB (toBA pw) (toBA pw).size).size ≤ 511 * 511 := by
  have hsz : (toBA pw).size = pw.length := by simp [toBA, ByteArray.size]
  rw [repeatB_size, hsz]
  exact Nat.mul_le_mul hl hl

/-- The repeat that actually runs (`repeatBFast`: one buffer, appended to in a loop, registered
with `@[csimp]`) computes the specified `repeatB`, for every input. -/
theorem repeatB_fast (src : ByteArray) (k : Nat) : repeatB src k = repeatBFast src k :=
  congrFun (congrFun repeatB_eq_fast src) k

/-- The limit itself: 511 bytes pass the length check, 512 do not. -/
theorem vector_password_limit : maxPasswordLen = 511 ∧
    verifyCrypt b!"$5$abc$x" (List.replicate 512 97) = false := by
  decide +kernel

/-- `auth_basic` refuses exactly when it is on and the credentials do not check out. -/
theorem authDenied_iff (eff : Settings) (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes) :
    authDenied eff users authz = true ↔
      (∃ realm, eff.authBasic = some (some realm)) ∧
      basicOk (users (eff.authUserFile.getD [])) authz = false := by
  unfold authDenied
  rcases hb : eff.authBasic with _ | _ | realm <;> simp

/-- With `auth_basic` on, a request without valid credentials is answered 401 before any file is
looked at (unless a `return` answers first, as in nginx). -/
theorem routeAuth_denied (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes)
    (hs : sv.ret = none)
    (hl : ((selectLocation sv.locations np.uri).getD defaultLocation).ret = none)
    (hd : authDenied (effective h sv ((selectLocation sv.locations np.uri).getD defaultLocation))
      users authz = true) :
    routeAuth h sv req v np users authz = .done (.error 401) := by
  simp [routeAuth, hs, hl, hd]

/-- When access is granted, routing is exactly `route`, so every routing spec above still holds. -/
theorem routeAuth_allowed (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes)
    (hd : authDenied (effective h sv ((selectLocation sv.locations np.uri).getD defaultLocation))
      users authz = false) :
    routeAuth h sv req v np users authz = route h sv req v np := by
  simp [routeAuth, hd]

/-- `routeAuth` only ever adds a 401; any other answer is `route`'s. -/
theorem routeAuth_cases (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (users : Bytes → List (Bytes × Bytes)) (authz : Option Bytes) :
    routeAuth h sv req v np users authz = .done (.error 401) ∨
      routeAuth h sv req v np users authz = route h sv req v np := by
  simp only [routeAuth]
  by_cases hc : ((sv.ret.isNone && ((selectLocation sv.locations np.uri).getD defaultLocation).ret.isNone) &&
      authDenied (effective h sv ((selectLocation sv.locations np.uri).getD defaultLocation)) users authz) = true
  · exact Or.inl (if_pos hc)
  · exact Or.inr (if_neg hc)

/-- The 401 challenge header is a token name and a value with no CR, LF or NUL, whatever realm the
configuration gives. -/
theorem authChallenge_valid (eff : Settings) :
    ∀ hv ∈ authChallenge eff, isToken hv.1 = true ∧ validValue hv.2 = true := by
  unfold authChallenge
  rcases eff.authBasic with _ | _ | realm
  · simp
  · simp
  · simp only [List.mem_singleton, forall_eq]
    refine ⟨by decide +kernel, ?_⟩
    simp only [validValue, List.all_append, List.all_filter, Bool.and_eq_true]
    refine ⟨⟨by decide +kernel, ?_⟩, by decide +kernel⟩
    simp only [List.all_eq_true]
    intro c _
    cases fieldByteOk c <;> simp

theorem vector_basic_creds :
    basicCreds b!"Basic dXNlcjpwYXNz" = some (b!"user", b!"pass") ∧
    basicCreds b!"basic dXNlcjpwYTpzcw==" = some (b!"user", b!"pa:ss") ∧
    basicCreds b!"Bearer dXNlcjpwYXNz" = none ∧
    basicCreds b!"Basic dXNlcnBhc3M=" = none := by
  decide +kernel

theorem vector_users :
    parseUsers b!"# team\nbaif:$5$x$y\n\nother:$5$a$b:comment\n" =
      [(b!"baif", b!"$5$x$y"), (b!"other", b!"$5$a$b")] := by
  decide +kernel

end LeanNginx.Spec

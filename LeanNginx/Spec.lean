import LeanNginx.Proofs.Misc
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

/-! ## 3. Location matching (nginx docs, `location`; nginx-tests: `http_location.t`) -/

/-- The selected location is one of the configured ones and matches the URI. -/
theorem selectLocation_sound (locs : List Location) (uri : Bytes) (l : Location)
    (h : selectLocation locs uri = some l) : l ∈ locs ∧ matchesLoc l uri = true := by
  unfold selectLocation at h
  split at h
  · rename_i l' hf
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨hm, ?_⟩
    simp [matchesLoc, hp.1, hp.2]
  · rcases longest_mem _ none l h with hm | hm
    · simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
      refine ⟨hm.1, ?_⟩
      unfold matchesLoc
      split
      · rename_i hk; exact absurd hk hm.2.1
      · exact hm.2.2
    · cases hm

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

/-- Otherwise the longest matching prefix wins: no other prefix location that matches the
URI is longer than the one selected. -/
theorem selectLocation_longest (locs : List Location) (uri : Bytes) (l : Location)
    (h : selectLocation locs uri = some l) (hk : l.kind ≠ .exact) :
    ∀ l' ∈ locs, l'.kind ≠ .exact → isPrefixB l'.uri uri = true → l'.uri.length ≤ l.uri.length := by
  unfold selectLocation at h
  split at h
  · rename_i l' hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact absurd hp.1 hk
  · intro l' hl' hk' hp
    exact (longest_max _ none l h).1 l' (by simp [hl', hk', hp])

/-- The example from the nginx documentation of `location`. -/
def docLocs : List Location :=
  [{ kind := .exact, uri := b!"/" }, { kind := .pre, uri := b!"/" },
   { kind := .pre, uri := b!"/documents/" }, { kind := .noRegex, uri := b!"/images/" }]

theorem vector_location_doc :
    (selectLocation docLocs b!"/").map (·.kind) = some .exact ∧
    (selectLocation docLocs b!"/index.html").map (·.uri) = some b!"/" ∧
    (selectLocation docLocs b!"/documents/document.html").map (·.uri) = some b!"/documents/" ∧
    (selectLocation docLocs b!"/images/1.gif").map (·.uri) = some b!"/images/" := by
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
    tRoute b!"GET" b!"/" = some (.internal b!"/index.html") ∧
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

end LeanNginx.Spec

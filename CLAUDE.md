# leannginx — nginx-compatible web server in Lean 4, with specs

## Workflow
- Lean 4.35.0 (pinned because lean-zip's commit builds with 4.35, not 4.36), no Mathlib. Builds
  locally on macOS: `lake build` checks every proof and spec (the default target is the
  `LeanNginx` library only — probe-lean loads default targets); `lake build lnginx` builds the
  server binary.
- Dependencies: LeanTLS (HTTPS; its server side lives in that repo: `LeanTLS/Server.lean`,
  `ServerMessages.lean`, `Sign.lean`, specs in `LeanTLS/Spec/Server.lean`) and lean-zip (gzip).
  Always `lake update --keep-toolchain`; plain `lake update` bumps to LeanTLS's 4.36 toolchain and
  lean-zip stops building.
- `scripts/smoke.sh` is the end-to-end check of the binary (ports 18089 HTTP, 18091 HTTPS with
  throwaway openssl certificates, python upstream on 18090). Run it after touching `Main.lean`.
- The default site is `conf/nginx.conf` + `html/`; `.lake/build/bin/lnginx` serves it on
  http://127.0.0.1:8080/.

## Architecture
- Pure, specified: `Bytes`, `Uri`, `Http`, `Config`, `Route`, `Response` (all on
  `Bytes := List UInt8`). IO shell: `Main.lean` only (sockets via `Std.Async`, files, clock,
  logs). Keep decisions out of `Main.lean`: anything that decides a status code, a header, or a
  file path belongs in the pure layer with a spec.
- Routing is a stat program (`Step`): `route` asks `stat` questions and `Main.runStep` answers
  them. Specs quantify over all answers. New file-system lookups must go through `Step.stat`
  with paths built as `base ++ joinSegs segs` from safe segments, or `route_confined` breaks.
- `parseRequest` is written as explicit matches (no `do`) so proofs can split every branch.

- `Main.recvT` (read with timeout) races the native read promise against a libuv timer by hand.
  Do not switch it to `Selectable.one`: on Lean 4.35 that costs ~4x throughput (measured).
- Replacing an installed binary: `rm` it first, then `cp`. Overwriting in place makes macOS kill
  the new binary (exit 137, stale code signature).

## Specs, not tests
- No runtime unit tests. `LeanNginx/Spec.lean` is the test suite; sections name the nginx
  feature and the nginx-tests script it corresponds to.
- New or changed behaviour gets a spec (docstring saying what it guarantees). Then run
  `./audit.sh`: it regenerates `LeanNginx/Audit.lean` and fails on any axiom other than
  `propext`, `Classical.choice`, `Quot.sound`.
- State specs for all inputs where possible. Concrete vectors: `decide +kernel` (or `rfl`);
  never `native_decide`. Write byte literals as `b!"text"`.
- Supporting lemmas go in `LeanNginx/Proofs/`.
- The VeriLib page source is `pages/leannginx.md` (`OWNER` is replaced by the account name when posting).
- Regex: `Regex.lean` (derivative matcher); `Proofs/Regex.lean` proves `matchB_iff` against the
  inductive `Matches`. New syntax must compile to the existing `Re` constructors, or extend `Re`
  and the proof.
- The audit allows lean-zip's `bv_decide` axioms only for `gzip_roundtrip` (`BV_DECIDE_OK` in
  `scripts/gen_audit.py`).
- `Except` gets `DecidableEq` via `deriving instance` at the top of `Spec.lean`.

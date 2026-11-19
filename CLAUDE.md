# leannginx — nginx-compatible web server in Lean 4, with specs

## Workflow
- Lean 4.36.0, no Mathlib. Builds locally on macOS: `lake build` checks every proof and spec
  (the default target is the `LeanNginx` library only — probe-lean loads default targets);
  `lake build lnginx` builds the server binary.
- `scripts/smoke.sh` is the end-to-end check of the binary (starts it on port 18089 with a
  temporary config and a python upstream on 18090). Run it after touching `Main.lean`.
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

## Specs, not tests
- No runtime unit tests. `LeanNginx/Spec.lean` is the test suite; sections name the nginx
  feature and the nginx-tests script it corresponds to.
- New or changed behaviour gets a spec (docstring saying what it guarantees). Then run
  `./audit.sh`: it regenerates `LeanNginx/Audit.lean` and fails on any axiom other than
  `propext`, `Classical.choice`, `Quot.sound`.
- State specs for all inputs where possible. Concrete vectors: `decide +kernel` (or `rfl`);
  never `native_decide`. Write byte literals as `b!"text"`.
- Supporting lemmas go in `LeanNginx/Proofs/`.
- `Except` gets `DecidableEq` via `deriving instance` at the top of `Spec.lean`.

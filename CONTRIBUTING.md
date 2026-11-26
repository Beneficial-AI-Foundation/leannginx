# Contributing to LeanNginx

Thanks for your interest in contributing. LeanNginx is an nginx-compatible web
server written in Lean 4, with path confinement and other properties proved for
every request. This guide covers how to build it, the standards we hold code to,
and how to send a change. It follows the shared contribution standard used across
the [Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation) Lean
projects.

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project
uses, so you don't install Lean by hand:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

No other dependencies are required to build; the end-to-end smoke test additionally
uses `curl`, `openssl` and `nc`, which are present on most systems.

## Building

```sh
lake build          # the LeanNginx library and its proofs (a few seconds)
lake build lnginx   # the server binary at .lake/build/bin/lnginx
```

## Testing

```sh
./audit.sh            # regenerate the axiom audit; fails on a disallowed axiom
sh scripts/smoke.sh   # end-to-end check of the built binary against ./html
```

Continuous integration runs the build, the audit and the smoke test on Linux and
macOS for every push and pull request (see `.github/workflows/ci.yml`). Please make
sure these pass locally before opening a PR.

## Proof discipline

Correctness here comes from machine-checked proofs, so the sources must stay free of
proof escape hatches:

- **No `sorry`, `admit` or `native_decide`.** CI greps for them and fails on a hit.
- Concrete vectors are decided with `decide +kernel` or `rfl`, not `native_decide`.
- The axiom audit pins every spec to `propext`, `Classical.choice` and `Quot.sound`;
  if a change makes a spec depend on anything else, `./audit.sh` and the build fail.

See `CLAUDE.md` for the full house rules.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a spec/test for behaviour you
   change — tests are theorems here.
3. Make sure `lake build lnginx`, `./audit.sh` and `sh scripts/smoke.sh` pass, and
   that CI is green.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest configuration or request that reproduces it. Security-sensitive reports can
be sent privately to **support@beneficialaifoundation.org** instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.

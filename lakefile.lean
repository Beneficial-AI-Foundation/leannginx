import Lake
open Lake DSL System

package leannginx where
  version := v!"0.1.0"

-- TLS 1.3 (client and server). Pinned commit; the server side was added for leannginx.
require leantls from git "https://github.com/Beneficial-AI-Foundation/leantls" @
  "4e8c4a3697157679c5924c07eca34a237cd62490"

-- Verified DEFLATE/gzip (gzip_decompressSingle_compress: decompress ∘ compress = id).
-- Pinned commit targets Lean 4.35, hence this package's toolchain.
require «lean-zip» from git "https://github.com/kim-em/lean-zip" @
  "2f7a63f38195bc667a926881b55d10c9f8a88eeb"

-- The library only: VeriLib's probe-lean loads the default targets into one environment.
-- Build the server binary with `lake build lnginx`.
@[default_target]
lean_lib LeanNginx where
  globs := #[.one `LeanNginx, .submodules `LeanNginx]

-- SO_REUSEPORT bind for the worker processes: project-local stopgap until Std.Async has it
-- (leanprover/lean4#16687). Tied to the Lean v4.35 runtime internals; see c/reuseport.c.
input_file reuseport.c where
  path := "c" / "reuseport.c"
  text := true

target reuseport.o pkg : FilePath := do
  let srcJob ← reuseport.c.fetch
  let oFile := pkg.buildDir / "c" / "reuseport.o"
  buildLeanO oFile srcJob #[] (#["-O2"] ++ if Platform.isWindows then #[] else #["-fPIC"])

extern_lib libreuseport pkg := do
  let o ← reuseport.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "reuseport") #[o]

-- The web server: lnginx [-p PREFIX] [-c CONF] [-t] [-v]
lean_exe lnginx where
  root := `Main

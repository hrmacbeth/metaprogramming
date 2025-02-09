import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false"
]

def moreLeanArgs := moreServerArgs

package «metaprogramming» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionString}"

@[default_target]
lean_lib «Metaprogramming» where
  globs := #[.submodules `Metaprogramming]
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := #[]

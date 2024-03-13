import Lake
open Lake DSL

package saturn where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.1"


@[default_target]
lean_lib Saturn

lean_exe nqueens

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

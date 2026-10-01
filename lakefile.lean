import Lake
open Lake DSL

package «superposition» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Superposition» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

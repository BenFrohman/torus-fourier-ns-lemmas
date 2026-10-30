import Lake
open Lake DSL

package «TorusFourierNS»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

@[default_target]
lean_lib «TorusFourierNS» where
  roots := #[`TorusFourierNS]

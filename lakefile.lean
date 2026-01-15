import Lake
open Lake DSL

package mlc where
  @[default_target]
  lean_lib Mlc

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

lean_exe check_axioms where
  root := `check_axioms

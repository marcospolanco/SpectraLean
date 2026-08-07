import Lake
open Lake DSL

package scaffold {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib Scaffold {
  -- add library configuration options here
}

@[default_target]
lean_exe scaffold {
  root := `Main
}

import Lake
open Lake DSL

package scaffold {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-- The default target is the library root `Scaffold.lean`, so `lake build`
certifies every public module reachable from the umbrella. The former
executable target referenced a nonexistent `Main.lean` and broke the
default build; it will be reintroduced together with a real driver. -/
@[default_target]
lean_lib Scaffold {
  -- add library configuration options here
}

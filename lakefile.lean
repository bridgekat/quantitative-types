import Lake
open Lake DSL

package simpleLinearTypes {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib SimpleLinearTypes
lean_lib Mult

@[default_target]
lean_exe simpleLinearTypes {
  root := `Main
}

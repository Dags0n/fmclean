import Lake
open Lake DSL

package «fmclean» {
  -- add package configuration options here
}

lean_lib «Fmclean» {
  mathlib = {git = "https://github.com/leanprover-community/mathlib", rev = "cd7f0626a0b04be1dda223a26123313514a55fb4"}
}

@[default_target]
lean_exe «fmclean» {
  root := `Main
}

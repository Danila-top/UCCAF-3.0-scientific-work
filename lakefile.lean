import Lake
open Lake DSL

package UCCAFFormalization where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib UCCAF where
  globs := #[.submodules `UCCAF]

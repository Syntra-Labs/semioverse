import Lake
open Lake DSL

package «semioverse» where
  -- add package configuration options here

require proofwidgets from git
    "https://github.com/leanprover-community/proofwidgets4.git" @ "main"

@[default_target]
lean_lib «semioverse» where
  -- expects semioverse.lean (or semioverse/*.lean) at the project root

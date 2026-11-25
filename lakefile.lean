import Lake
open Lake DSL

package «semioverse» where
  -- add package configuration options here

require proofwidgets from git
    "https://github.com/leanprover-community/proofwidgets4.git" @ "main"

lean_lib «semioverse» where
  -- semioverse.lean: the theory, §§1–7

@[default_target]
lean_lib «Gap» where
  -- Gap.lean imports semioverse, so `lake build` checks both

@[default_target]
lean_lib «Alignment» where
  -- Alignment.lean: the residual ledger; built so its open sorries stay type-checked

/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-scale-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-scale» from ".."

-- Compile-time tests: compiling is passing.
@[default_target]
lean_lib InkproofScaleTest where
  globs := #[.submodules `InkproofScaleTest]

-- Runtime tests. `Main.lean` must stay buildable by Lasm, so it imports nothing that needs Lean's
-- compiler at run time.
@[default_target]
lean_exe tests where
  root := `Main

@[test_driver]
script test do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-core/inkproof-test-driver"], cwd := __dir__ }
  return if (← child.wait) == 0 then 0 else 1

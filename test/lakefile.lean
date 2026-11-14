/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-float-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-float» from ".."

@[default_target]
lean_exe tests where
  root := `Main

@[test_driver]
script test do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-test-driver"], cwd := __dir__ }
  child.wait

require «inkproof-tools» from git
  "https://github.com/paulbutcher/inkproof-tools" @ "v0.1.0"

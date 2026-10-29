module

import NPComplete.BoundedWhile.Basic

/-!
# Must fail: `simp only` on a mutual definition under a plain `import`

`scripts/check_importer_tests.sh` expects this file to be rejected with the text `_mutual`. If it
passed, a plain-import module importer would see the bodies of non-exposed definitions, and the pinned
failures in `NPCompleteTest.Pilot.EvalPlain` would be wrong. It is outside the globs of `NPCompleteTest`.
-/

open NPComplete.BoundedWhile

example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]

module

import NPCompleteTest.Pilot.Mid

/-!
# `Mid` re-exports Basic with `public import`; this file uses a plain `import Mid`

Expected: the importer's own import must be `public` too, so unfolding still fails.
-/

open NPComplete.BoundedWhile
/-- Program.eval._mutual -/
#guard_msgs (substring := true) in
example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]

module

import NPComplete.BoundedWhile.Basic

/-!
# plain `import Basic`: `simp [Program.eval]` (not `simp only`) with the shipped `@[simp]` lemmas

Expected: ok. The shipped `@[simp]` equation lemmas close the goal even though the `Program.eval`
argument itself is useless, unlike `simp only [Program.eval]`.
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile
example (σ : Store) : Program.skip.eval σ = σ := by simp [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp [Program.eval]

module

public import NPCompleteTest.Pilot.Mid

/-!
# Unfolding through a public re-export

Clients may import an intermediate module rather than the defining module. This
example checks that definitions re-exported by `public import` remain available
for evaluation and unfolding at that boundary.
-/

open NPComplete.BoundedWhile
example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  rw [Program.eval]

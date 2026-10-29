module

import NPComplete.BoundedWhile.Basic

/-!
# plain `import Basic`: the same operations

Expected: the equation lemmas of the mutual definitions are unusable. `simp only [f]`,
`unfold f`, `rw [f]` rewrite `f x` into `f._mutual (PSum.inl ..)` and do not close the goal, so each
is pinned with `#guard_msgs (substring := true)` on the text `_mutual` (all three mutual blocks share `Program.eval._mutual`). Everything through shipped
lemmas, `f.eq_def`, structural definitions (`Expr.eval`) or `Store` application still works.
-/

open NPComplete.BoundedWhile

-- expected FAIL: the goal is left in terms of `_mutual`
/-- _mutual -/
#guard_msgs (substring := true) in
example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]
/-- _mutual -/
#guard_msgs (substring := true) in
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp only [Program.eval]
/-- _mutual -/
#guard_msgs (substring := true) in
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  rw [Program.eval]
/-- _mutual -/
#guard_msgs (substring := true) in
example (σ : Store) : Program.skip.eval σ = σ := by unfold Program.eval; rfl
/-- _mutual -/
#guard_msgs (substring := true) in
example (b : Program) (σ : Store) : loopEval b 0 σ = σ := by simp only [loopEval]
/-- _mutual -/
#guard_msgs (substring := true) in
example (σ : Store) : Program.skip.cost σ = 1 := by simp only [Program.cost]
/-- _mutual -/
#guard_msgs (substring := true) in
example (b : Program) (r : Nat) (σ : Store) : scanListEval b [] r σ = σ := by
  simp only [scanListEval]
-- expected OK: shipped lemmas and `eq_def`
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp only [eval_seq]
example (σ : Store) : (Program.assign 1 (.const 2)).eval σ = writeReg σ 1 2 := by
  simp only [eval_assign, Expr.eval_const]
example (σ : Store) : (Program.seq .skip .skip).cost σ = 1 + 1 := by
  simp only [cost_seq, cost_skip, eval_skip]
example (b : Program) (σ : Store) : loopEval b 1 σ = b.eval σ := by
  simp only [loopEval_succ, loopEval_zero]
example (σ : Store) : Program.skip.eval σ = σ := by rw [Program.eval.eq_def]
example (σ : Store) : Program.skip.eval σ = σ := by rw [Program.eval.eq_1]
example (σ : Store) : Program.skip.eval σ = σ := by simp
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by simp
-- expected OK: structural definitions and Store application
example (σ : Store) : (Expr.add (.const 1) (.const 2)).eval σ = 3 := by simp [Expr.eval]
example : (Expr.add (.const 1) (.reg 2)).cost = 3 := by simp [Expr.cost]
example (σ : Store) : writeReg σ 1 2 1 = 2 := by simp
example : emptyStore 3 = 0 := rfl
-- expected FAIL, as with a public import (not a module effect)
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : (Program.skip.eval emptyStore) 3 = 0 := by decide

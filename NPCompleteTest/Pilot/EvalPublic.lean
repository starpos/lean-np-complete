module

public import NPComplete.BoundedWhile.Basic

/-!
# `public import Basic`: unfolding the mutual / structural defs

Expected: every test succeeds (the equation lemmas of the mutual definitions have their usual shape
because the importer sees the exposed bodies). Closed-term `decide` on `Program.eval` fails even
here (mutual -> well-founded -> irreducible; a non-module importer behaves the same), so it is
pinned with `#guard_msgs`.
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile

-- Program.eval (mutual): expected ok
example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp only [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp [Program.eval]
example (σ : Store) : Program.skip.eval σ = σ := by unfold Program.eval; rfl
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  rw [Program.eval]
example (σ : Store) : Program.skip.eval σ = σ := by rw [Program.eval.eq_1]
example (σ : Store) : Program.skip.eval σ = σ := by rw [Program.eval.eq_def]
-- loopEval / scanListEval / cost family: expected ok
example (b : Program) (σ : Store) : loopEval b 0 σ = σ := by simp only [loopEval]
example (b : Program) (k : Nat) (σ : Store) : loopEval b (k + 1) σ = loopEval b k (b.eval σ) := by
  simp only [loopEval]
example (b : Program) (r : Nat) (σ : Store) : scanListEval b [] r σ = σ := by
  simp only [scanListEval]
example (σ : Store) : (Program.seq .skip .skip).cost σ = 2 := by simp [Program.cost]
example (σ : Store) : Program.skip.cost σ = 1 := by unfold Program.cost; rfl
example (b : Program) (σ : Store) : loopCost b 0 σ = 0 := by simp only [loopCost]
example (b : Program) (r : Nat) (σ : Store) : scanListCost b [] r σ = 0 := by
  simp only [scanListCost]
-- library equation lemmas: expected ok
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp only [eval_seq]
example (σ : Store) : (Program.assign 1 (.const 2)).eval σ = writeReg σ 1 2 := by
  simp only [eval_assign, Expr.eval_const]
-- Expr (structural): expected ok
example (σ : Store) : (Expr.add (.const 1) (.const 2)).eval σ = 3 := by simp [Expr.eval]
example : (Expr.add (.const 1) (.reg 2)).cost = 3 := by simp [Expr.cost]
-- Store is a function type: application needs the exposed body
example (σ : Store) : writeReg σ 1 2 1 = 2 := by simp
example : emptyStore 3 = 0 := rfl
-- closed-term decide on eval: expected FAIL, not a module effect
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : (Program.skip.eval emptyStore) 3 = 0 := by decide

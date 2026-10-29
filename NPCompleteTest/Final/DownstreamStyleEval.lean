module

import NPComplete

/-!
# Mutual and well-founded definitions through plain `import NPComplete`

Exercises common downstream proof patterns: `simp only [eval_seq]`, rewriting with `loopEval_succ`,
`simp [compile]`, `simp [addRaw]`, `unfold Program.eval`, and `rw [compile.eq_def]`.
Expected with a plain import: the shipped-lemma steps and the `compile.eq_def` rewrite are ok;
`simp [compile]`, `simp [addRaw]`, and `unfold Program.eval` FAIL. The complementary
`show`/`change` check spells out the `.seq` case of `ProgramBoundedIn` in
`DownstreamStyleShow.lean`.
-/

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM

-- ok: shipped lemmas
example (σ : Store) (p q : Program) (r : Nat) (h : (p.eval σ) r = σ r) (h2 : q.eval (p.eval σ) r = p.eval σ r) :
    (Program.seq p q).eval σ r = σ r := by
  simp only [eval_seq]; rw [h2, h]
example (b : Program) (k : Nat) (σ : Store) : loopEval b (k + 1) σ = loopEval b k (b.eval σ) := by
  rw [loopEval_succ]
-- FAIL (plain import)
/-- compile._mutual -/
#guard_msgs (substring := true) in
example : compile .skip 0 0 = [] := by simp [compile]
/-- compile._mutual -/
#guard_msgs (substring := true) in
example : compile (.assign 2 (.const 1)) 0 0 = [] ++ [] := by simp [compile]
/-- addRaw._unary -/
#guard_msgs (substring := true) in
example : addRaw [] [] false = [] := by simp [addRaw]
/-- Program.eval._mutual -/
#guard_msgs (substring := true) in
example (σ : Store) : Program.skip.eval σ = σ := by unfold Program.eval; rfl
-- ok: eq_def
example : compile .skip 0 0 = [] := by rw [compile.eq_def]

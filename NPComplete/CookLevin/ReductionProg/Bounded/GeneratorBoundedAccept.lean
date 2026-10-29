module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedPersist

/-!
The accept family's only `writeClauseProg` call is `acceptLeafProgParam`'s
`implyPosLits` — a fixed head cell implying the staged output symbol cell,
repeated once per `(pHead, p)` pair by the two enclosing loops.  Its halt
clause is `acceptHaltProgParam`'s `writeAtLeastOneProg` shape, a run-time
width whose literals are not a `LitsBounded` obligation, matching the init
family's free-cell clause.

`AcceptEnv` is the family's single dominating inequality, as in the other
families; its larger majorant is the staged-cell expression's
`ExprBoundedIn` obligation, which already dominates the head expression's
smaller one without any extra arithmetic identity.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- One inequality dominating every majorant the accept expressions use.  The
    larger of the two is the staged-cell expression's `ExprBoundedIn`
    obligation. -/
def AcceptEnv (K X n m : ℕ) : Prop :=
  K * (n + K + K * m) + n + K + K * m + K ≤ X

lemma acceptEnv_of_le {K X X' n m : ℕ} (h : AcceptEnv K X n m) (hX : X ≤ X') :
    AcceptEnv K X' n m := le_trans h hX

/-- The leaf writing the accept implication: the fixed head implies the
    staged-symbol cell. -/
lemma litsBounded_accept_leaf (K S B M n m wReg tReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR : 2 ≤ tReg) (htR2 : tReg ≤ 23)
    (hMB : M + 24 ≤ B)
    (henvB : AcceptEnv K B n m) (henvS : AcceptEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (implyPosLits (acceptHeadEParam n m wReg tReg)
      (acceptCellStagedEParam n m wReg tReg)) := by
  unfold AcceptEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g7 : τ (M + tmpJ) ≤ K := ht tmpJ (by norm_num [tmpJ]) (by norm_num [tmpJ])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  have gt : τ (M + tReg) ≤ K := ht tReg htR (by omega)
  simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_acceptHeadEParam M K B n m wReg tReg τ hK1 h0 gw gt g2 hwR2 htR2
        (by omega) (by omega) hn hm (by omega)
    · exact le_trans (acceptHeadEParam_eval_le M K n m wReg tReg τ h0 gw gt g2) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_acceptCellStagedEParam M K B n m wReg tReg τ hK1 h0 gw gt g3 g7 hwR2 htR2
        (by omega) (by omega) hn hm (by omega)
    · exact le_trans (acceptCellStagedEParam_eval_le M K n m wReg tReg τ h0 gw gt g3 g7) (by omega)

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedPersist

/-!
The init family's `writeClauseProg` calls are its five fixed-width leaves:
the start-state clause, the head clause, and — inside `initWindowLeafProgParam`
— the prefix-cell and blank-cell clauses, plus `initTailProgParam`'s tail
implication.  Its free-cell clause is `writeAtLeastOneProg`'s run-time-width
shape, not a `writeClauseProg` literal list, so it carries no `LitsBounded`
obligation here.

`InitEnv` is the family's single dominating inequality, as in the persist and
uniqueness families.  Its largest majorant is the tail-cell-next expression's
`ExprBoundedIn` obligation, which is also the only one whose `3 * K * m` term
needs an explicit `ring`-derived link to `K * m` before `omega` can use the
envelope — the other four leaves' obligations are already linear in the terms
`InitEnv` names.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- One inequality dominating every majorant the init expressions use.  The
    largest is the tail-cell-next expression's `ExprBoundedIn` obligation. -/
def InitEnv (K X n m : ℕ) : Prop :=
  n + K + K * m + (3 * K * m + m) + 3 * K + 1 ≤ X

lemma initEnv_of_le {K X X' n m : ℕ} (h : InitEnv K X n m) (hX : X ≤ X') :
    InitEnv K X' n m := le_trans h hX

/-- Every `LitsBounded` obligation is vacuous on the empty literal list, the
    shape `initStateProgParam` writes when the descriptor's start state is
    out of range. -/
lemma litsBounded_nil (K S B M : ℕ) : LitsBounded K S B M [] :=
  fun _ hq => absurd hq (List.not_mem_nil)

/-! ## The five leaves -/

/-- The leaf writing the start-state clause. -/
lemma litsBounded_init_state (K S B M n m wReg startState : ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) (hstart : startState ≤ K) :
    LitsBounded K S B M (unitPosLits (initStateEParam n m wReg startState)) := by
  unfold InitEnv at henvB henvS
  intro q hq τ h0 ht hst
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
  · exact exprBoundedIn_initStateEParam M K B n m wReg startState τ h0 gw hwR2
      (by omega) (by omega) hn hm (by omega) (by omega)
  · exact le_trans (initStateEParam_eval_le M K n m wReg startState τ h0 gw (by omega)) (by omega)

/-- The leaf writing the head clause. -/
lemma litsBounded_init_head (K S B M n m wReg tReg : ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR : 2 ≤ tReg) (htR2 : tReg ≤ 23)
    (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (unitPosLits (initHeadEParam n m wReg tReg)) := by
  unfold InitEnv at henvB henvS
  intro q hq τ h0 ht hst
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  have gt : τ (M + tReg) ≤ K := ht tReg htR (by omega)
  simp only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
  · exact exprBoundedIn_initHeadEParam M K B n m wReg tReg τ h0 gw gt hwR2 htR2
      (by omega) (by omega) hn hm (by omega)
  · exact le_trans (initHeadEParam_eval_le M K n m wReg tReg τ h0 gw gt) (by omega)

/-- The leaf writing the prefix-symbol clause, once staged into `tmpJ`. -/
lemma litsBounded_init_prefix_cell (K S B M n m wReg : ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (unitPosLits (initPrefixCellStagedEParam n m wReg)) := by
  unfold InitEnv at henvB henvS
  have hrel : 3 * K * m = 3 * (K * m) := by ring
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g7 : τ (M + tmpJ) ≤ K := ht tmpJ (by norm_num [tmpJ]) (by norm_num [tmpJ])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
  · exact exprBoundedIn_initPrefixCellStagedEParam M K B n m wReg τ h0 g2 g7 gw hwR2
      (by omega) (by omega) hn hm (by omega)
  · exact le_trans (initPrefixCellStagedEParam_eval_le M K n m wReg τ h0 g2 g7 gw) (by omega)

/-- The leaf writing the blank-cell clause. -/
lemma litsBounded_init_blank_cell (K S B M n m wReg blank : ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) (hblank : blank ≤ K) :
    LitsBounded K S B M (unitPosLits (initBlankCellEParam n m wReg blank)) := by
  unfold InitEnv at henvB henvS
  have hrel : 3 * K * m = 3 * (K * m) := by ring
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
  · exact exprBoundedIn_initBlankCellEParam M K B n m wReg blank τ h0 g2 gw hwR2
      (by omega) (by omega) hn hm hblank (by omega)
  · exact le_trans (initBlankCellEParam_eval_le M K n m wReg blank τ h0 g2 gw hblank) (by omega)

/-- The leaf writing the free-suffix implication. -/
lemma litsBounded_init_tail (K S B M n m wReg tReg plReg blank : ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR : 2 ≤ tReg) (htR2 : tReg ≤ 23)
    (hplR : 2 ≤ plReg) (hplR2 : plReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) (hblank : blank ≤ K) :
    LitsBounded K S B M (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
      (initTailCellNextEParam n m wReg tReg plReg blank)) := by
  unfold InitEnv at henvB henvS
  have hrel : 3 * K * m = 3 * (K * m) := by ring
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  have gt : τ (M + tReg) ≤ K := ht tReg htR (by omega)
  have gpl : τ (M + plReg) ≤ K := ht plReg hplR (by omega)
  simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_initTailCellEParam M K B n m wReg tReg plReg blank τ h0 gt gpl g2 gw
        hwR2 htR2 hplR2 (by omega) (by omega) hn hm hblank (by omega)
    · exact le_trans (initTailCellEParam_eval_le M K n m wReg tReg plReg blank τ h0 gt gpl g2 gw hblank)
        (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_initTailCellNextEParam M K B n m wReg tReg plReg blank τ h0 gt gpl g2 gw
        hwR2 htR2 hplR2 (by omega) (by omega) hn hm hblank (by omega)
    · exact le_trans
        (initTailCellNextEParam_eval_le M K n m wReg tReg plReg blank τ h0 gt gpl g2 gw hblank)
        (by omega)

end NPComplete.CookLevin

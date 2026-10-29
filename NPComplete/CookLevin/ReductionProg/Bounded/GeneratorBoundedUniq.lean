module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedPersist

/-!
The uniqueness family writes `negPair` rows at three shapes — state, head, cell
— each pairing a base variable number with its shifted successor.  All six
expressions are dense-layout builders already covered by
`GeneratorBoundedExpr`/`GeneratorBoundedValue`, so as with the persist family a
single inequality, `UniqEnv`, dominates every majorant the three leaves need.

The largest majorant is the cell-shift expression's `ExprBoundedIn` obligation,
so `UniqEnv` is stated at that shape; the other five leaves' obligations are
each termwise below it, which `omega` closes once the arithmetic identity
`(2 * K + 1) * m = 2 * (K * m) + m`-style rewriting is unnecessary here (unlike
persist, none of the shift expressions folds a `(2K+1)` coefficient).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- One inequality dominating every majorant the uniqueness expressions use.
    The largest is the cell-shift expression's `ExprBoundedIn` obligation. -/
def UniqEnv (K X n m : ℕ) : Prop :=
  K * (n + K + K * m) + n + K + K * m + K + K + K ≤ X

lemma uniqEnv_of_le {K X X' n m : ℕ} (h : UniqEnv K X n m) (hX : X ≤ X') :
    UniqEnv K X' n m := le_trans h hX

/-! ## The three leaves

Each writes a `negPair` of a base variable number and its shifted successor, so
each discharges `LitsBounded` the same way — an expression bound and a value
bound per literal, at any store with the right control cells. -/

/-- The leaf writing the state-uniqueness pair. -/
lemma litsBounded_uniq_state (K S B M n m wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B n m) (henvS : UniqEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (negPairLits (uniqStateBaseEParam n m wReg)
      (uniqStateShiftEParam n m wReg)) := by
  unfold UniqEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [negPairLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqStateBaseEParam M K B n m wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqStateBaseEParam_eval_le M K n m wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqStateShiftEParam M K B n m wReg τ hK1 h0 g2 g3 g4 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqStateShiftEParam_eval_le M K n m wReg τ h0 g2 g3 g4 gw) (by omega)

/-- The leaf writing the head-uniqueness pair. -/
lemma litsBounded_uniq_head (K S B M n m wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B n m) (henvS : UniqEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (negPairLits (uniqHeadBaseEParam n m wReg)
      (uniqHeadShiftEParam n m wReg)) := by
  unfold UniqEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [negPairLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqHeadBaseEParam M K B n m wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqHeadBaseEParam_eval_le M K n m wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqHeadShiftEParam M K B n m wReg τ hK1 h0 g2 g3 g4 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqHeadShiftEParam_eval_le M K n m wReg τ h0 g2 g3 g4 gw) (by omega)

/-- The leaf writing the cell-uniqueness pair. -/
lemma litsBounded_uniq_cell (K S B M n m wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B n m) (henvS : UniqEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (negPairLits (uniqCellBaseEParam n m wReg)
      (uniqCellShiftEParam n m wReg)) := by
  unfold UniqEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [negPairLits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqCellBaseEParam M K B n m wReg τ hK1 h0 g2 g3 g4 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqCellBaseEParam_eval_le M K n m wReg τ h0 g2 g3 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_uniqCellShiftEParam M K B n m wReg τ hK1 h0 g2 g3 g4 g5 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (uniqCellShiftEParam_eval_le M K n m wReg τ h0 g2 g3 g4 g5 gw) (by omega)

end NPComplete.CookLevin

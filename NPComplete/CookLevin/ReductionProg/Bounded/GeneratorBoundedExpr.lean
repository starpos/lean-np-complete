module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedCore

/-!
Each clause family builds its variable numbers and table reads from a handful
of `Expr` shapes: dense variable-number arithmetic (`denseStateE`/`denseHeadE`/
`denseCellE` composed with `ctlCell`s and constants), the "successor time"
variant that adds a constant `1` before multiplying, and indirect table reads
(`wordReadEBaseParam` and its per-family clones) that additionally consult the
value the address points at.  This file gives each such builder its own
`ExprBoundedIn` lemma, so a family's compiled-operand bound can cite one lemma
per expression rather than re-deriving the arithmetic from scratch.

Two hypothesis shapes recur, matching the two things a dense expression reads:
`TightCells K M σ` for the control and parameter cells it multiplies, and
`StoreValuesLe K σ` for the table cell an indirect read consults (the address
itself is never read back, only used to index).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Trans family (`ClauseFamilyTransParam`) -/

lemma exprBoundedIn_transStateEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + K ≤ B) (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transStateEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  have hflat : nS + K + K * mS ≤ K * (nS + K + K * mS) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ2] at h2 h4 hmul
  unfold transStateEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ2
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transHeadEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + nS + K ≤ B) (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transHeadEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  have hflat : nS + K + K * mS ≤ K * (nS + K + K * mS) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold transHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transCellEParam (M K B nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + nS + K + K * mS + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transCellEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  have hpe : σ (M + lvJ1) * mS ≤ K * mS := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ3] at h2 h3 h5 hmul hpe
  unfold transCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transStateSameEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + (nS + K + K * mS) + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transStateSameEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, lvJ2] at h2 h4 hmul
  unfold transStateSameEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ2
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transHeadSameEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transHeadSameEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold transHeadSameEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transCellSameEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K + K * mS + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transCellSameEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  have hpe : σ (M + lvJ1) * mS ≤ K * mS := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ3] at h2 h3 h5 hmul hpe
  unfold transCellSameEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transStateNextEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h6 : σ (M + litJ) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + (nS + K + K * mS) + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transStateNextEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, litJ] at h2 h6 hmul
  unfold transStateNextEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 litJ
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_transCellWriteEParam (M K B nS mS wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h7 : σ (M + tmpJ) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K + K * mS + K ≤ B)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ExprBoundedIn B σ (transCellWriteEParam nS mS wReg) := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  have hpe : σ (M + lvJ1) * mS ≤ K * mS := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, tmpJ] at h2 h3 h7 hmul hpe
  unfold transCellWriteEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 tmpJ
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-- Both branches of `moveOkEParam` share the same operand bounds, so a single
    upper bound on `pE.eval σ + 1` (rather than a separate case per direction)
    covers both the `.lt (.const 0) pE` and `.lt (.add pE 1) (ctlCell wReg)`
    subterms. -/
lemma exprBoundedIn_moveOkEParam (B wReg : ℕ) (σ : Store) (pE dirE : Expr) (hB1 : 1 ≤ B)
    (hp : ExprBoundedIn B σ pE) (hd : ExprBoundedIn B σ dirE)
    (hpv : pE.eval σ + 1 ≤ B) (hdv : dirE.eval σ ≤ B)
    (hw : ExprBoundedIn B σ (ctlCell wReg)) (hwv : (ctlCell wReg).eval σ ≤ B) :
    ExprBoundedIn B σ (moveOkEParam wReg pE dirE) := by
  unfold moveOkEParam
  simp only [ExprBoundedIn, Expr.eval]
  refine ⟨⟨⟨hB1, hd, hB1⟩, ⟨by omega, hp⟩,
    by by_cases h : 0 < pE.eval σ <;> simp [h] ; omega⟩,
    ⟨hd, ⟨⟨hp, hB1, hpv⟩, hw⟩,
    by by_cases h : pE.eval σ + 1 < (ctlCell wReg).eval σ <;> simp [h] ; omega⟩,
    by by_cases h1 : 0 < pE.eval σ <;>
      by_cases h2 : pE.eval σ + 1 < (ctlCell wReg).eval σ <;>
      simp [h1, h2] <;> omega⟩

/-- The row-major table index `qi * mC + ai` both cells read to locate their
    column entry. -/
lemma exprBoundedIn_transIdxE (M K B mC : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hprod : K * mC + K ≤ B) (hmC : mC ≤ B) (hM : M + 5 ≤ B) :
    ExprBoundedIn B σ (transIdxE mC) ∧ (transIdxE mC).eval σ ≤ K * mC + K := by
  have hmul : σ (M + lvJ2) * mC ≤ K * mC := Nat.mul_le_mul_right _ h4
  simp only [lvJ2, lvJ3] at h4 h5 hmul
  unfold transIdxE ctlCell ctlAddr lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  refine ⟨?_, by omega⟩
  repeat' apply And.intro
  all_goals omega

/-! ## Uniqueness family (`ClauseFamilyUniqueness`) -/

lemma exprBoundedIn_uniqStateBaseEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqStateBaseEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold uniqStateBaseEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_uniqStateShiftEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqStateShiftEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul
  unfold uniqStateShiftEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_uniqHeadBaseEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqHeadBaseEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold uniqHeadBaseEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_uniqHeadShiftEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqHeadShiftEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul
  unfold uniqHeadShiftEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_uniqCellBaseEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K * m + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqCellBaseEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul hpe
  unfold uniqCellBaseEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_uniqCellShiftEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K * m + K + K + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (uniqCellShiftEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ2, lvJ3] at h2 h3 h4 h5 hmul hpe
  unfold uniqCellShiftEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-! ## Persist family (`ClauseFamilyPersist`) -/

lemma exprBoundedIn_persistHeadEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (persistHeadEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold persistHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_persistCellEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K * m + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (persistCellEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have hpe : σ (M + lvJ2) * m ≤ K * m := Nat.mul_le_mul_right _ h4
  simp only [lvJ0, lvJ2, lvJ3] at h2 h4 h5 hmul hpe
  unfold persistCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_persistCellNextEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + (n + K + K * m) + n + K + K * m + K ≤ B)
    (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (persistCellNextEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : (σ (M + lvJ0) + 1) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤
      K * (n + K + K * m) + (n + K + K * m) := by
    calc (σ (M + lvJ0) + 1) * (n + σ (M + wReg) + σ (M + wReg) * m)
        ≤ (K + 1) * (n + K + K * m) := Nat.mul_le_mul (by omega) hsum
      _ = K * (n + K + K * m) + (n + K + K * m) := by ring
  have hpe : σ (M + lvJ2) * m ≤ K * m := Nat.mul_le_mul_right _ h4
  simp only [lvJ0, lvJ2, lvJ3] at h2 h4 h5 hmul hpe
  unfold persistCellNextEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_persistCellShiftEParam (M K B n m wReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + ((2 * K + 1) * m + K) ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (persistCellShiftEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have hpe : (σ (M + lvJ1) + 1 + σ (M + lvJ2)) * m ≤ (2 * K + 1) * m :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [lvJ0, lvJ1, lvJ2, lvJ3] at h2 h3 h4 h5 hmul hpe
  unfold persistCellShiftEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-- `persistCellShiftNextEParam` is bounded by `B` given the four loop counters and `wReg`'s cell
    `≤ K`, and the product bound `hprod` on the shifted cell index. -/
lemma exprBoundedIn_persistCellShiftNextEParam (M K B n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) ≤ B)
    (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (persistCellShiftNextEParam n m wReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : (σ (M + lvJ0) + 1) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤
      K * (n + K + K * m) + (n + K + K * m) := by
    calc (σ (M + lvJ0) + 1) * (n + σ (M + wReg) + σ (M + wReg) * m)
        ≤ (K + 1) * (n + K + K * m) := Nat.mul_le_mul (by omega) hsum
      _ = K * (n + K + K * m) + (n + K + K * m) := by ring
  have hpe : (σ (M + lvJ1) + 1 + σ (M + lvJ2)) * m ≤ (2 * K + 1) * m :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [lvJ0, lvJ1, lvJ2, lvJ3] at h2 h3 h4 h5 hmul hpe
  unfold persistCellShiftNextEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2 lvJ3
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-! ## Init family (`ClauseFamilyInitExpr`, `ClauseFamilyInitTail`,
    `ClauseFamilyInitWindow`) -/

/-- The time coordinate is `.const 0`, so only the `wReg`/`lvJ0` product
    (window width times letter index) needs a `TightCells`-style bound; the
    `aE` argument brings its own, against an explicit bound `A` (which need
    not be `K` — `initFreeCellVarEParam` below supplies one drawn from
    `listGetE`, whose values reach only `B`, not `K`). -/
lemma exprBoundedIn_initCellEParam (M K B n m wReg A : ℕ) (σ : Store) (aE : Expr)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (ha : ExprBoundedIn B σ aE) (hav : aE.eval σ ≤ A)
    (hprod : n + K + K * m + (K * m + A) ≤ B) (hn : n ≤ B) (hm : m ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initCellEParam n m wReg aE) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hb2 : σ (M + lvJ0) * m ≤ K * m := Nat.mul_le_mul_right _ h2
  simp only [lvJ0] at h2 hb2
  unfold initCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_initStateEParam (M K B n m wReg startState : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m ≤ B) (hn : n ≤ B) (hm : m ≤ B) (hstart : startState ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initStateEParam n m wReg startState) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  unfold initStateEParam denseStateE denseBlockE ctlCell ctlAddr
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_initHeadEParam (M K B n m wReg tReg : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initHeadEParam n m wReg tReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  unfold initHeadEParam denseHeadE denseBlockE ctlCell ctlAddr
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_initBlankCellEParam (M K B n m wReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m + (K * m + K) ≤ B) (hn : n ≤ B) (hm : m ≤ B) (hblank : blank ≤ K)
    (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initBlankCellEParam n m wReg blank) := by
  unfold initBlankCellEParam
  exact exprBoundedIn_initCellEParam M K B n m wReg K σ (.const blank) h0 h2 hw hwR hMK
    (by simp [ExprBoundedIn]; omega) (by simp [Expr.eval]; omega) hprod hn hm h1B

lemma exprBoundedIn_initPrefixCellStagedEParam (M K B n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h7 : σ (M + tmpJ) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m + (K * m + K) ≤ B) (hn : n ≤ B) (hm : m ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initPrefixCellStagedEParam n m wReg) := by
  unfold initPrefixCellStagedEParam
  have htmp : ExprBoundedIn B σ (ctlCell tmpJ) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
    have := h7
    simp only [tmpJ] at this ⊢
    omega
  have htmpv : (ctlCell tmpJ).eval σ ≤ K := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]
    exact h7
  exact exprBoundedIn_initCellEParam M K B n m wReg K σ (ctlCell tmpJ) h0 h2 hw hwR hMK
    htmp htmpv hprod hn hm h1B

/-- `listGetE`'s recursion peels one list entry at a time, each time reading
    `kE - 1` against the shrunk tail.  The result is bounded by `V`, a value
    bound on the list entries — which need not be `B` itself, since forcing
    `V = B` would make the caller's own envelope inequality unsatisfiable
    (`... + B ≤ B` forces every other term to `0`). -/
lemma exprBoundedIn_listGetE (B V : ℕ) (σ : Store) (hB1 : 1 ≤ B) (hVB : V ≤ B) :
    ∀ (L : List ℕ) (kE : Expr), (∀ v ∈ L, v ≤ V) → ExprBoundedIn B σ kE → kE.eval σ ≤ B →
      ExprBoundedIn B σ (listGetE L kE) ∧ (listGetE L kE).eval σ ≤ V
  | [], _, _, _, _ => by unfold listGetE; simp only [ExprBoundedIn, Expr.eval]; omega
  | v :: vs, kE, hL, hk, hkv => by
      have hv : v ≤ V := hL v (List.mem_cons.mpr (Or.inl rfl))
      have hvs : ∀ w ∈ vs, w ≤ V := fun w hw => hL w (List.mem_cons.mpr (Or.inr hw))
      have hsub : ExprBoundedIn B σ (Expr.sub kE (.const 1)) :=
        ⟨hk, by simp [ExprBoundedIn]; omega, by omega⟩
      have hsubv : (Expr.sub kE (.const 1)).eval σ ≤ B := by simp only [Expr.eval]; omega
      obtain ⟨hrec, hrecv⟩ :=
        exprBoundedIn_listGetE B V σ hB1 hVB vs (Expr.sub kE (.const 1)) hvs hsub hsubv
      unfold listGetE
      simp only [ExprBoundedIn, Expr.eval]
      refine ⟨⟨⟨⟨hk, by omega⟩, by omega,
          by
            by_cases hz : kE.eval σ = 0
            · simpa [hz] using hv.trans hVB
            · simp [hz]⟩,
        ⟨⟨hB1, ⟨hk, by omega⟩, hB1⟩, hrec,
          by
            by_cases hz : kE.eval σ = 0
            · simp [hz]
            · simpa [hz] using hrecv.trans hVB⟩,
        by
          by_cases hz : kE.eval σ = 0
          · simpa [hz] using hv.trans hVB
          · simpa [hz] using hrecv.trans hVB⟩, ?_⟩
      by_cases hz : kE.eval σ = 0
      · simpa [hz] using hv
      · simpa [hz] using hrecv

/-- The staged variable is `listGetE (blank :: allowedIdx) (ctlCell litJ)`, an
    `initCellEParam` argument whose bound is the letter-list bound `V`
    (usually `≤ K`, the symbol alphabet size), not `K` itself, since the
    listed values are compile-time letters read off `ctlCell litJ` rather
    than a `TightCells` control cell. -/
lemma exprBoundedIn_initFreeCellVarEParam (M K B n m wReg blank V : ℕ) (allowedIdx : List ℕ)
    (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h6 : σ (M + litJ) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B) (hVB : V ≤ B)
    (hallowed : ∀ v ∈ allowedIdx, v ≤ V) (hblank : blank ≤ V)
    (hprod : n + K + K * m + (K * m + V) ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (initFreeCellVarEParam n m wReg blank allowedIdx) := by
  have hlit : ExprBoundedIn B σ (ctlCell litJ) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
    have := h6; simp only [litJ] at this ⊢; omega
  have hlitv : (ctlCell litJ).eval σ ≤ B := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]; omega
  have hL : ∀ v ∈ (blank :: allowedIdx), v ≤ V := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hblank
    · exact hallowed v hv
  obtain ⟨hlg, hlgv⟩ :=
    exprBoundedIn_listGetE B V σ h1B hVB (blank :: allowedIdx) (ctlCell litJ) hL hlit hlitv
  unfold initFreeCellVarEParam
  exact exprBoundedIn_initCellEParam M K B n m wReg V σ
    (listGetE (blank :: allowedIdx) (ctlCell litJ)) h0 h2 hw hwR hMK hlg hlgv hprod hn hm h1B

lemma exprBoundedIn_initInPrefixEParam (M K B tReg plReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (htR : tReg ≤ 23) (hplR : plReg ≤ 23)
    (hMK : M + 23 ≤ B) (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (hK : K + K ≤ B) :
    ExprBoundedIn B σ (initInPrefixEParam tReg plReg) := by
  unfold initInPrefixEParam
  simp only [ExprBoundedIn, Expr.eval, ctlCell, ctlAddr, lvJ0, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_initInFreeEParam (M K B tReg plReg fReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (htR : tReg ≤ 23) (hplR : plReg ≤ 23) (hfR : fReg ≤ 23)
    (hMK : M + 23 ≤ B) (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (hf : σ (M + fReg) ≤ K)
    (hK : K + K + K ≤ B) :
    ExprBoundedIn B σ (initInFreeEParam tReg plReg fReg) := by
  unfold initInFreeEParam
  simp only [ExprBoundedIn, Expr.eval, ctlCell, ctlAddr, lvJ0, h0]
  repeat' apply And.intro
  all_goals omega

/-- The tail cells sum three counters (`tReg`, `plReg`, `lvJ0`) into the
    letter index, so the multiplier bound is `3K` rather than a single cell's
    `K`. -/
lemma exprBoundedIn_initTailCellEParam (M K B n m wReg tReg plReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K)
    (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hplR : plReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m + 3 * K * m + 3 * K ≤ B) (hn : n ≤ B) (hm : m ≤ B) (hblank : blank ≤ K)
    (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initTailCellEParam n m wReg tReg plReg blank) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hpe : (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0)) * m ≤ 3 * K * m :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [lvJ0] at h2 hpe
  unfold initTailCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_initTailCellNextEParam (M K B n m wReg tReg plReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K)
    (hw : σ (M + wReg) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hplR : plReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : n + K + K * m + (3 * K * m + m) + 3 * K + 1 ≤ B)
    (hn : n ≤ B) (hm : m ≤ B) (hblank : blank ≤ K)
    (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (initTailCellNextEParam n m wReg tReg plReg blank) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hpe : (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1) * m ≤ 3 * K * m + m := by
    have hh : σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1 ≤ 3 * K + 1 := by omega
    calc (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1) * m
        ≤ (3 * K + 1) * m := Nat.mul_le_mul_right _ hh
      _ = 3 * K * m + m := by ring
  simp only [lvJ0] at h2 hpe
  unfold initTailCellNextEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-! ## Accept family (`ClauseFamilyAcceptParam`) -/

/-- Unlike the init family's `initStateEParam`/`initHeadEParam`, accept reads
    the time coordinate from `ctlCell tReg` rather than `.const 0`, so the
    product bound needs the same `t * (...)` step as the dense trans
    lemmas. -/
lemma exprBoundedIn_acceptHeadEParam (M K B n m wReg tReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K ≤ B) (hn : n ≤ B) (hm : m ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (acceptHeadEParam n m wReg tReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  simp only [lvJ0] at h2
  unfold acceptHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

lemma exprBoundedIn_acceptCellStagedEParam (M K B n m wReg tReg : ℕ) (σ : Store) (hK1 : 1 ≤ K)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K)
    (h3 : σ (M + lvJ1) ≤ K) (h7 : σ (M + tmpJ) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hMK : M + 23 ≤ B)
    (hprod : K * (n + K + K * m) + n + K + K * m + K ≤ B)
    (hn : n ≤ B) (hm : m ≤ B) (h1B : 1 ≤ B) :
    ExprBoundedIn B σ (acceptCellStagedEParam n m wReg tReg) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ1, tmpJ] at h3 h7 hpe
  unfold acceptCellStagedEParam denseCellE denseBlockE ctlCell ctlAddr lvJ1 tmpJ
  simp only [ExprBoundedIn, Expr.eval, h0]
  repeat' apply And.intro
  all_goals omega

/-- The halt clause's variable number reads its state index off the compile-
    time list `qs` through `listGetE`, exactly as `initFreeCellVarEParam`
    reads its symbol off `blank :: allowedIdx`. The register bounds `hwR`,
    `htR` are needed here (unlike `initFreeCellVarEParam`, whose time
    coordinate is `.const 0`) because both `wReg` and `tReg` are read as
    `ctlCell` addresses feeding into the same product. -/
lemma exprBoundedIn_acceptHaltVarEParam (M K B n m wReg tReg V : ℕ) (qs : List ℕ) (σ : Store)
    (hK1 : 1 ≤ K)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K) (h6 : σ (M + litJ) ≤ K)
    (hwR : wReg ≤ 23) (htR : tReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B) (hVB : V ≤ B)
    (hqs : ∀ v ∈ qs, v ≤ V)
    (hprod : K * (n + K + K * m) + V ≤ B) (hn : n ≤ B) (hm : m ≤ B) :
    ExprBoundedIn B σ (acceptHaltVarEParam n m wReg tReg qs) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  have hflat : n + K + K * m ≤ K * (n + K + K * m) := Nat.le_mul_of_pos_left _ hK1
  have htc : ExprBoundedIn B σ (ctlCell tReg) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]; omega
  have htcv : (ctlCell tReg).eval σ = σ (M + tReg) := by simp only [ctlCell, ctlAddr, Expr.eval, h0]
  have hwc : ExprBoundedIn B σ (ctlCell wReg) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]; omega
  have hwcv : (ctlCell wReg).eval σ = σ (M + wReg) := by simp only [ctlCell, ctlAddr, Expr.eval, h0]
  have hlit : ExprBoundedIn B σ (ctlCell litJ) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
    have h6' := h6; simp only [litJ] at h6' ⊢; omega
  have hlitv : (ctlCell litJ).eval σ ≤ B := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]; omega
  obtain ⟨hlg, hlgv⟩ := exprBoundedIn_listGetE B V σ h1B hVB qs (ctlCell litJ) hqs hlit hlitv
  unfold acceptHaltVarEParam denseStateE denseBlockE
  simp only [ExprBoundedIn, Expr.eval, htcv, hwcv]
  refine ⟨⟨htc, ⟨⟨hn, hwc, by omega⟩, ⟨hwc, hm, by omega⟩, by omega⟩, by omega⟩, hlg, by omega⟩

end NPComplete.CookLevin

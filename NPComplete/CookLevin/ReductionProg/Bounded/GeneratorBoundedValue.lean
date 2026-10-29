module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedExpr

/-!
`ExprBoundedIn B σ e` bounds an expression's *syntax* — every subexpression's
arithmetic stays under `B`.  It says nothing about `e.eval σ` on its own,
which `LitsBounded` additionally requires: a variable number is written into
the clause table, so the store-wide bound `S` must dominate the value, not
merely the syntax that computed it.

This file pairs an `eval σ ≤ ...` lemma with each `exprBoundedIn_*` lemma in
`GeneratorBoundedExpr`, dropping the assumptions that were only there to
bound intermediate products against `B` (`hMK`, `hprod`, `hn`/`hm`, `h1B`,
...) and keeping only what the *value* computation needs: `h0` and the
`TightCells`/`StoreValuesLe`-style cell bounds.  The right-hand side is, with
the exceptions described below, literally the left-hand side of the matching
`exprBoundedIn_*` lemma's `hprod` hypothesis — so a caller supplying `B` for
that hypothesis gets the value bound "for free" via `≤`.

The exceptions are the four `*Shift*`/`*Same*` shapes whose `ExprBoundedIn`
proof needs `K ≥ 1` only to keep a `denseBlockE`-style
subterm inside its own product bound (`n + K + K * m ≤ K * (n + K + K * m)`,
via `hflat`) — a step the value computation never takes, since it reads the
subterm directly rather than through that inequality.  The matching value lemmas
omit `K ≥ 1`; when `K ≥ 1`, their bounds are at most the corresponding `hprod`
left-hand side (equal for `transStateSameEParam_eval_le`).  Their docstrings explain
the difference.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Trans family (`ClauseFamilyTransParam`) -/

lemma transStateEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (transStateEParam nS mS wReg).eval σ ≤ K * (nS + K + K * mS) + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ2] at h2 h4 hmul
  unfold transStateEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ2
  simp only [Expr.eval, h0]
  omega

lemma transHeadEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (transHeadEParam nS mS wReg).eval σ ≤ K * (nS + K + K * mS) + nS + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold transHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [Expr.eval, h0]
  omega

lemma transCellEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (transCellEParam nS mS wReg).eval σ ≤ K * (nS + K + K * mS) + nS + K + K * mS + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : σ (M + lvJ0) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤ K * (nS + K + K * mS) :=
    Nat.mul_le_mul h2 hsum
  have hpe : σ (M + lvJ1) * mS ≤ K * mS := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ3] at h2 h3 h5 hmul hpe
  unfold transCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ3
  simp only [Expr.eval, h0]
  omega

/-- The same upper bound as `exprBoundedIn_transStateSameEParam`'s `hprod`
    LHS, without requiring `hK1`. The `ExprBoundedIn` proof needs `hflat` to
    fold the flat term `nS + K + K * mS` into the product; this value
    computation reads the term directly. -/
lemma transStateSameEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (transStateSameEParam nS mS wReg).eval σ
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, lvJ2] at h2 h4 hmul
  unfold transStateSameEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ2
  simp only [Expr.eval, h0]
  omega

lemma transHeadSameEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (transHeadSameEParam nS mS wReg).eval σ
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold transHeadSameEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [Expr.eval, h0]
  omega

lemma transCellSameEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (transCellSameEParam nS mS wReg).eval σ
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K + K * mS + K := by
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
  simp only [Expr.eval, h0]
  omega

lemma transStateNextEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h6 : σ (M + litJ) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (transStateNextEParam nS mS wReg).eval σ
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) + K := by
  have hb : σ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ hw
  have hsum : nS + σ (M + wReg) + σ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS) ≤
      K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (σ (M + lvJ0) + 1) * (nS + σ (M + wReg) + σ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [lvJ0, litJ] at h2 h6 hmul
  unfold transStateNextEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 litJ
  simp only [Expr.eval, h0]
  omega

lemma transCellWriteEParam_eval_le (M K nS mS wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h7 : σ (M + tmpJ) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (transCellWriteEParam nS mS wReg).eval σ
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K + K * mS + K := by
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
  simp only [Expr.eval, h0]
  omega

/-! ## Uniqueness family (`ClauseFamilyUniqueness`) -/

lemma uniqStateBaseEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (uniqStateBaseEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold uniqStateBaseEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [Expr.eval, h0]
  omega

/-- Tighter than `exprBoundedIn_uniqStateShiftEParam`'s `hprod` LHS, for the
    same reason as `transStateSameEParam_eval_le`: `hflat`'s `K ≥ 1` step is not
    needed to read the flat term off the store. -/
lemma uniqStateShiftEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (uniqStateShiftEParam n m wReg).eval σ ≤ K * (n + K + K * m) + 2 * K + 1 := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul
  unfold uniqStateShiftEParam denseStateE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [Expr.eval, h0]
  omega

lemma uniqHeadBaseEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (uniqHeadBaseEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold uniqHeadBaseEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [Expr.eval, h0]
  omega

/-- Tighter than `exprBoundedIn_uniqHeadShiftEParam`'s `hprod` LHS, same gap
    as `uniqStateShiftEParam_eval_le`. -/
lemma uniqHeadShiftEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (uniqHeadShiftEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + 2 * K + 1 := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul
  unfold uniqHeadShiftEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [Expr.eval, h0]
  omega

lemma uniqCellBaseEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (uniqCellBaseEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + K + K * m + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ2] at h2 h3 h4 hmul hpe
  unfold uniqCellBaseEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2
  simp only [Expr.eval, h0]
  omega

/-- Tighter than `exprBoundedIn_uniqCellShiftEParam`'s `hprod` LHS, same gap
    as `uniqStateShiftEParam_eval_le`. -/
lemma uniqCellShiftEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (uniqCellShiftEParam n m wReg).eval σ
      ≤ K * (n + K + K * m) + n + K + K * m + 2 * K + 1 := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ0, lvJ1, lvJ2, lvJ3] at h2 h3 h4 h5 hmul hpe
  unfold uniqCellShiftEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2 lvJ3
  simp only [Expr.eval, h0]
  omega

/-! ## Persist family (`ClauseFamilyPersist`) -/

lemma persistHeadEParam_eval_le (M K n m wReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (persistHeadEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  simp only [lvJ0, lvJ1] at h2 h3 hmul
  unfold persistHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1
  simp only [Expr.eval, h0]
  omega

lemma persistCellEParam_eval_le (M K n m wReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (persistCellEParam n m wReg).eval σ ≤ K * (n + K + K * m) + n + K + K * m + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hpe : σ (M + lvJ2) * m ≤ K * m := Nat.mul_le_mul_right _ h4
  simp only [lvJ0, lvJ2, lvJ3] at h2 h4 h5 hmul hpe
  unfold persistCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ2 lvJ3
  simp only [Expr.eval, h0]
  omega

lemma persistCellNextEParam_eval_le (M K n m wReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (persistCellNextEParam n m wReg).eval σ
      ≤ K * (n + K + K * m) + (n + K + K * m) + n + K + K * m + K := by
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
  simp only [Expr.eval, h0]
  omega

lemma persistCellShiftEParam_eval_le (M K n m wReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (persistCellShiftEParam n m wReg).eval σ
      ≤ K * (n + K + K * m) + n + K + ((2 * K + 1) * m + K) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + lvJ0) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul h2 hsum
  have hpe : (σ (M + lvJ1) + 1 + σ (M + lvJ2)) * m ≤ (2 * K + 1) * m :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [lvJ0, lvJ1, lvJ2, lvJ3] at h2 h3 h4 h5 hmul hpe
  unfold persistCellShiftEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 lvJ2 lvJ3
  simp only [Expr.eval, h0]
  omega

lemma persistCellShiftNextEParam_eval_le (M K n m wReg : ℕ) (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h3 : σ (M + lvJ1) ≤ K) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hw : σ (M + wReg) ≤ K) :
    (persistCellShiftNextEParam n m wReg).eval σ
      ≤ K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) := by
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
  simp only [Expr.eval, h0]
  omega

/-! ## Init family (`ClauseFamilyInitExpr`, `ClauseFamilyInitTail`,
    `ClauseFamilyInitWindow`) -/

lemma initCellEParam_eval_le (M K n m wReg A : ℕ) (σ : Store) (aE : Expr)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hav : aE.eval σ ≤ A) :
    (initCellEParam n m wReg aE).eval σ ≤ n + K + K * m + (K * m + A) := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hb2 : σ (M + lvJ0) * m ≤ K * m := Nat.mul_le_mul_right _ h2
  simp only [lvJ0] at h2 hb2
  unfold initCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [Expr.eval, h0]
  omega

/-- Needs `startState ≤ K` (unlike `exprBoundedIn_initStateEParam`'s
    `hstart : startState ≤ B`), since the value bound is stated against `K`
    rather than the wider expression envelope `B`. -/
lemma initStateEParam_eval_le (M K n m wReg startState : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (hstart : startState ≤ K) :
    (initStateEParam n m wReg startState).eval σ ≤ n + K + K * m := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  unfold initStateEParam denseStateE denseBlockE ctlCell ctlAddr
  simp only [Expr.eval, h0]
  omega

lemma initHeadEParam_eval_le (M K n m wReg tReg : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K) :
    (initHeadEParam n m wReg tReg).eval σ ≤ n + K + K * m + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  unfold initHeadEParam denseHeadE denseBlockE ctlCell ctlAddr
  simp only [Expr.eval, h0]
  omega

lemma initBlankCellEParam_eval_le (M K n m wReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (hw : σ (M + wReg) ≤ K) (hblank : blank ≤ K) :
    (initBlankCellEParam n m wReg blank).eval σ ≤ n + K + K * m + (K * m + K) := by
  unfold initBlankCellEParam
  exact initCellEParam_eval_le M K n m wReg K σ (.const blank) h0 h2 hw (by simp [Expr.eval]; omega)

lemma initPrefixCellStagedEParam_eval_le (M K n m wReg : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (h7 : σ (M + tmpJ) ≤ K) (hw : σ (M + wReg) ≤ K) :
    (initPrefixCellStagedEParam n m wReg).eval σ ≤ n + K + K * m + (K * m + K) := by
  unfold initPrefixCellStagedEParam
  have htmpv : (ctlCell tmpJ).eval σ ≤ K := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]
    exact h7
  exact initCellEParam_eval_le M K n m wReg K σ (ctlCell tmpJ) h0 h2 hw htmpv

-- The bounded-expression result already carries the value bound; the lemma below
-- packages it for direct use by families that read compile-time lists.

/-- Reusable value bound for `listGetE`, extracted for the two families
    (`initFreeCellVarEParam`, `acceptHaltVarEParam`) that read a compile-time
    list through it here. -/
lemma listGetE_eval_le (V : ℕ) (σ : Store) :
    ∀ (L : List ℕ) (kE : Expr), (∀ v ∈ L, v ≤ V) → (listGetE L kE).eval σ ≤ V
  | [], _, _ => by unfold listGetE; simp only [Expr.eval]; omega
  | v :: vs, kE, hL => by
      have hv : v ≤ V := hL v (List.mem_cons.mpr (Or.inl rfl))
      have hvs : ∀ w ∈ vs, w ≤ V := fun w hw => hL w (List.mem_cons.mpr (Or.inr hw))
      have hrec := listGetE_eval_le V σ vs (Expr.sub kE (.const 1)) hvs
      unfold listGetE
      simp only [Expr.eval]
      cases hval : kE.eval σ <;> simp [hval] at * <;> omega

lemma initFreeCellVarEParam_eval_le (M K n m wReg blank V : ℕ) (allowedIdx : List ℕ)
    (σ : Store) (h0 : σ 0 = M)
    (h2 : σ (M + lvJ0) ≤ K) (hw : σ (M + wReg) ≤ K)
    (hallowed : ∀ v ∈ allowedIdx, v ≤ V) (hblank : blank ≤ V) :
    (initFreeCellVarEParam n m wReg blank allowedIdx).eval σ
      ≤ n + K + K * m + (K * m + V) := by
  have hL : ∀ v ∈ (blank :: allowedIdx), v ≤ V := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hblank
    · exact hallowed v hv
  have hlgv := listGetE_eval_le V σ (blank :: allowedIdx) (ctlCell litJ) hL
  unfold initFreeCellVarEParam
  exact initCellEParam_eval_le M K n m wReg V σ
    (listGetE (blank :: allowedIdx) (ctlCell litJ)) h0 h2 hw hlgv

lemma initTailCellEParam_eval_le (M K n m wReg tReg plReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hblank : blank ≤ K) :
    (initTailCellEParam n m wReg tReg plReg blank).eval σ
      ≤ n + K + K * m + 3 * K * m + 3 * K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hpe : (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0)) * m ≤ 3 * K * m :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [lvJ0] at h2 hpe
  unfold initTailCellEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [Expr.eval, h0]
  omega

lemma initTailCellNextEParam_eval_le (M K n m wReg tReg plReg blank : ℕ) (σ : Store)
    (h0 : σ 0 = M)
    (ht : σ (M + tReg) ≤ K) (hpl : σ (M + plReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K)
    (hw : σ (M + wReg) ≤ K) (hblank : blank ≤ K) :
    (initTailCellNextEParam n m wReg tReg plReg blank).eval σ
      ≤ n + K + K * m + (3 * K * m + m) + 3 * K + 1 := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hpe : (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1) * m ≤ 3 * K * m + m := by
    have hh : σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1 ≤ 3 * K + 1 := by omega
    calc (σ (M + tReg) + σ (M + plReg) + σ (M + lvJ0) + 1) * m
        ≤ (3 * K + 1) * m := Nat.mul_le_mul_right _ hh
      _ = 3 * K * m + m := by ring
  simp only [lvJ0] at h2 hpe
  unfold initTailCellNextEParam denseCellE denseBlockE ctlCell ctlAddr lvJ0
  simp only [Expr.eval, h0]
  omega

/-! ## Accept family (`ClauseFamilyAcceptParam`) -/

lemma acceptHeadEParam_eval_le (M K n m wReg tReg : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K) (h2 : σ (M + lvJ0) ≤ K) :
    (acceptHeadEParam n m wReg tReg).eval σ ≤ K * (n + K + K * m) + n + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  simp only [lvJ0] at h2
  unfold acceptHeadEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0
  simp only [Expr.eval, h0]
  omega

lemma acceptCellStagedEParam_eval_le (M K n m wReg tReg : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K)
    (h3 : σ (M + lvJ1) ≤ K) (h7 : σ (M + tmpJ) ≤ K) :
    (acceptCellStagedEParam n m wReg tReg).eval σ
      ≤ K * (n + K + K * m) + n + K + K * m + K := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  have hpe : σ (M + lvJ1) * m ≤ K * m := Nat.mul_le_mul_right _ h3
  simp only [lvJ1, tmpJ] at h3 h7 hpe
  unfold acceptCellStagedEParam denseCellE denseBlockE ctlCell ctlAddr lvJ1 tmpJ
  simp only [Expr.eval, h0]
  omega

lemma acceptHaltVarEParam_eval_le (M K n m wReg tReg V : ℕ) (qs : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (hw : σ (M + wReg) ≤ K) (ht : σ (M + tReg) ≤ K)
    (hqs : ∀ v ∈ qs, v ≤ V) :
    (acceptHaltVarEParam n m wReg tReg qs).eval σ ≤ K * (n + K + K * m) + V := by
  have hb : σ (M + wReg) * m ≤ K * m := Nat.mul_le_mul_right _ hw
  have hsum : n + σ (M + wReg) + σ (M + wReg) * m ≤ n + K + K * m := by omega
  have hmul : σ (M + tReg) * (n + σ (M + wReg) + σ (M + wReg) * m) ≤ K * (n + K + K * m) :=
    Nat.mul_le_mul ht hsum
  have hlgv := listGetE_eval_le V σ qs (ctlCell litJ) hqs
  have htcv : (ctlCell tReg).eval σ = σ (M + tReg) := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]
  have hwcv : (ctlCell wReg).eval σ = σ (M + wReg) := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]
  unfold acceptHaltVarEParam denseStateE denseBlockE
  simp only [Expr.eval, htcv, hwcv]
  omega

end NPComplete.CookLevin

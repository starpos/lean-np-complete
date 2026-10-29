module

public import NPComplete.CookLevin.Tableau.TableauRamLoops
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyPersist
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitExpr
public import NPComplete.BoundedWhile.Frame

/-!
The clause-table emitter needs its unary length prefix before it writes the first
clause.  This module computes that length in the same store frame as the clause
families: a small control-cell loop supplies the triangular term that is not in
the expression language, and a final arithmetic expression assembles the count.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The control cell receiving the run-time clause count. -/
def rowCountReg : ℕ := 25

/-- The scratch counter used by the triangular-number loop. -/
def iterReg : ℕ := 26

/-- One M-relative iteration of the triangular-number accumulator. -/
def triAccStep (rowCountReg iterReg : ℕ) : Program :=
  .seq
    (ctlAssign rowCountReg (.add (ctlCell rowCountReg) (ctlCell iterReg)))
    (ctlAssign iterReg (.add (ctlCell iterReg) (.const 1)))

lemma triAccStep_zero (rowCountReg iterReg : ℕ) (hrowPos : 1 ≤ rowCountReg)
    (hiterPos : 1 ≤ iterReg) (σ : Store) :
    (triAccStep rowCountReg iterReg).eval σ 0 = σ 0 := by
  simp only [triAccStep, eval_seq]
  rw [ctlAssign_zero iterReg _ _ hiterPos]
  rw [ctlAssign_zero rowCountReg _ _ hrowPos]

lemma triAccStep_loop_zero (rowCountReg iterReg : ℕ) (hrowPos : 1 ≤ rowCountReg)
    (hiterPos : 1 ≤ iterReg) :
    ∀ (k : ℕ) (σ : Store),
      (loopEval (triAccStep rowCountReg iterReg) k σ) 0 = σ 0 := by
  intro k σ
  have hAvoids : (triAccStep rowCountReg iterReg).AvoidsAbove (fun r => r = 0) 1 := by
    simp_all [Program.AvoidsAbove, triAccStep, ctlAssign, ctlAddr, Expr.lb]
  exact hAvoids.loopEval_frame rfl (by decide) k σ

/-- The two control cells after one M-relative accumulation step. -/
lemma triAccStep_eval (M rowCountReg iterReg a i : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrow : σ (M + rowCountReg) = a)
    (hiter : σ (M + iterReg) = i) (hrowPos : 1 ≤ rowCountReg)
    (hne : rowCountReg ≠ iterReg) :
    (triAccStep rowCountReg iterReg).eval σ (M + rowCountReg) = a + i ∧
    (triAccStep rowCountReg iterReg).eval σ (M + iterReg) = i + 1 := by
  let σ1 := (ctlAssign rowCountReg
      (.add (ctlCell rowCountReg) (ctlCell iterReg))).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega), h0]
  have hσ1row : σ1 (M + rowCountReg) = a + i := by
    dsimp [σ1]
    rw [show M + rowCountReg = σ 0 + rowCountReg by rw [h0]]
    rw [ctlAssign_eval_same]
    simp [ctlCell_eval, Expr.eval, h0, hrow, hiter]
  have hσ1iter : σ1 (M + iterReg) = i := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hiter
  have h2iter : (ctlAssign iterReg
      (.add (ctlCell iterReg) (.const 1))).eval σ1 (M + iterReg) = i + 1 := by
    rw [show M + iterReg = σ1 0 + iterReg by rw [hσ10]]
    rw [ctlAssign_eval_same]
    simp [ctlCell_eval, Expr.eval, hσ10, hσ1iter]
  have h2row : (ctlAssign iterReg
      (.add (ctlCell iterReg) (.const 1))).eval σ1 (M + rowCountReg) = a + i := by
    have hne' : M + rowCountReg ≠ σ1 0 + iterReg := by
      rw [hσ10]
      omega
    rw [ctlAssign_eval_diff _ _ _ _ hne']
    exact hσ1row
  constructor
  · simp only [triAccStep, eval_seq]
    exact h2row
  · simp only [triAccStep, eval_seq]
    exact h2iter

/-- The accumulator's values after an arbitrary number of M-relative steps. -/
lemma triAccStep_loop_gen (M rowCountReg iterReg : ℕ)
    (hrowPos : 1 ≤ rowCountReg) (hiterPos : 1 ≤ iterReg)
    (hne : rowCountReg ≠ iterReg) :
    ∀ (k : ℕ) (σ : Store) (a i : ℕ), σ 0 = M →
      σ (M + rowCountReg) = a → σ (M + iterReg) = i →
      (loopEval (triAccStep rowCountReg iterReg) k σ) (M + rowCountReg) =
          a + (k * i + triAcc k) ∧
      (loopEval (triAccStep rowCountReg iterReg) k σ) (M + iterReg) = i + k := by
  intro k
  induction k with
  | zero =>
      intro σ a i h0 hrow hiter
      simpa [loopEval, triAcc] using ⟨hrow, hiter⟩
  | succ k ih =>
      intro σ a i h0 hrow hiter
      rw [loopEval_succ]
      have hstep := triAccStep_eval M rowCountReg iterReg a i σ h0 hrow hiter
        hrowPos hne
      let σ1 := (triAccStep rowCountReg iterReg).eval σ
      have hσ10 : σ1 0 = M := by
        dsimp [σ1]
        simp only [triAccStep, eval_seq]
        rw [ctlAssign_zero iterReg _ _ hiterPos]
        rw [ctlAssign_zero rowCountReg _ _ hrowPos]
        exact h0
      obtain ⟨hb1, hb2⟩ := ih σ1 (a + i) (i + 1) hσ10 hstep.1 hstep.2
      refine ⟨?_, ?_⟩
      · rw [hb1, triAcc]
        ring
      · rw [hb2]
        omega

/-- A triangular loop leaves any cell outside its two counter cells unchanged. -/
lemma triAccStep_frame (M rowCountReg iterReg r : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrowPos : 1 ≤ rowCountReg)
    (hneRow : r ≠ rowCountReg) (hneIter : r ≠ iterReg) :
    (triAccStep rowCountReg iterReg).eval σ (M + r) = σ (M + r) := by
  let σ1 := (ctlAssign rowCountReg
      (.add (ctlCell rowCountReg) (ctlCell iterReg))).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega), h0]
  have h1 : σ1 (M + r) = σ (M + r) := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
  have hne' : M + r ≠ σ1 0 + iterReg := by
    rw [hσ10]
    omega
  simp only [triAccStep, eval_seq]
  rw [ctlAssign_eval_diff _ _ _ _ hne']
  exact h1

lemma triAccStep_loop_frame (M rowCountReg iterReg r : ℕ) (hrowPos : 1 ≤ rowCountReg)
    (hiterPos : 1 ≤ iterReg) (hneRow : r ≠ rowCountReg) (hneIter : r ≠ iterReg) :
    ∀ (k : ℕ) (σ : Store), σ 0 = M →
      (loopEval (triAccStep rowCountReg iterReg) k σ) (M + r) = σ (M + r) := by
  intro k
  induction k with
  | zero =>
      intro σ h0
      rw [loopEval_zero]
  | succ k ih =>
      intro σ h0
      rw [loopEval_succ]
      have hbody0 : (triAccStep rowCountReg iterReg).eval σ 0 = M := by
        rw [triAccStep_zero rowCountReg iterReg hrowPos hiterPos, h0]
      calc
        (loopEval (triAccStep rowCountReg iterReg) k
            ((triAccStep rowCountReg iterReg).eval σ)) (M + r) =
            ((triAccStep rowCountReg iterReg).eval σ) (M + r) :=
              ih _ hbody0
        _ = σ (M + r) := triAccStep_frame M rowCountReg iterReg r σ h0
          hrowPos hneRow hneIter

def triAccLoop (rowCountReg iterReg widthJ : ℕ) : Program :=
  .seq (ctlAssign iterReg (.const 0))
    (.forN (ctlCell widthJ) (triAccStep rowCountReg iterReg))

lemma triAccLoop_eval (M rowCountReg iterReg widthJ W A : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrow : σ (M + rowCountReg) = A)
    (hW : σ (M + widthJ) = W) (hrowPos : 1 ≤ rowCountReg)
    (hiterPos : 1 ≤ iterReg) (hneRowIter : rowCountReg ≠ iterReg)
    (hneRowWidth : rowCountReg ≠ widthJ) (hneIterWidth : iterReg ≠ widthJ) :
    (triAccLoop rowCountReg iterReg widthJ).eval σ (M + rowCountReg) =
        A + triAcc W ∧
    (triAccLoop rowCountReg iterReg widthJ).eval σ (M + iterReg) = W := by
  let σ1 := (ctlAssign iterReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero iterReg _ σ hiterPos).trans h0
  have hσ1row : σ1 (M + rowCountReg) = A := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hrow
  have hσ1iter : σ1 (M + iterReg) = 0 := by
    dsimp [σ1]
    rw [show M + iterReg = σ 0 + iterReg by rw [h0]]
    rw [ctlAssign_eval_same]
    simp [Expr.eval]
  have hσ1width : σ1 (M + widthJ) = W := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hW
  have hloop := triAccStep_loop_gen M rowCountReg iterReg hrowPos hiterPos hneRowIter
    W σ1 A 0 hσ10 hσ1row hσ1iter
  have hcount : (ctlCell widthJ).eval σ1 = W := by
    rw [ctlCell_eval, hσ10]
    exact hσ1width
  have hprog : (triAccLoop rowCountReg iterReg widthJ).eval σ =
      loopEval (triAccStep rowCountReg iterReg) W σ1 := by
    simp only [triAccLoop, eval_seq]
    rw [eval_forN, hcount]
  rw [hprog]
  constructor
  · simpa using hloop.1
  · simpa using hloop.2

lemma triAccLoop_frame (M rowCountReg iterReg widthJ r : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrowPos : 1 ≤ rowCountReg) (hiterPos : 1 ≤ iterReg)
    (hneRow : r ≠ rowCountReg) (hneIter : r ≠ iterReg)
    (hneIterWidth : iterReg ≠ widthJ) :
    (triAccLoop rowCountReg iterReg widthJ).eval σ (M + r) = σ (M + r) := by
  let σ1 := (ctlAssign iterReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero iterReg _ σ hiterPos).trans h0
  have hσ1r : σ1 (M + r) = σ (M + r) := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
  have hσ1width : σ1 (M + widthJ) = σ (M + widthJ) := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
  have hcount : (ctlCell widthJ).eval σ1 = σ (M + widthJ) := by
    rw [ctlCell_eval, hσ10]
    exact hσ1width
  have hloop := triAccStep_loop_frame M rowCountReg iterReg r hrowPos hiterPos
    hneRow hneIter
  have hprog : (triAccLoop rowCountReg iterReg widthJ).eval σ =
      loopEval (triAccStep rowCountReg iterReg) (σ (M + widthJ)) σ1 := by
    simp only [triAccLoop, eval_seq]
    rw [eval_forN, hcount]
  rw [hprog]
  calc
    (loopEval (triAccStep rowCountReg iterReg) (σ (M + widthJ)) σ1) (M + r) =
        σ1 (M + r) := hloop (σ (M + widthJ)) σ1 hσ10
    _ = σ (M + r) := hσ1r

lemma triAccLoop_zero (M rowCountReg iterReg widthJ : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrowPos : 1 ≤ rowCountReg) (hiterPos : 1 ≤ iterReg) :
    (triAccLoop rowCountReg iterReg widthJ).eval σ 0 = M := by
  have hAvoids : (triAccLoop rowCountReg iterReg widthJ).AvoidsAbove (fun r => r = 0) 1 := by
    simp_all [Program.AvoidsAbove, triAccLoop, triAccStep, ctlAssign, ctlAddr, Expr.lb]
  exact (hAvoids.eval_frame σ rfl (by decide)).trans h0

/-- The arithmetic fragment of `clauseCount`, with the triangular term read from its control
cell.  `n` and `m` are the state and letter counts; `tJ`, `wJ`, `freeJ`, and `triJ` are cell
offsets, with `triJ` holding the already computed `triAcc W`. -/
def clauseCountExpr (n m tJ wJ freeJ triJ : ℕ) : Expr :=
  Expr.add
    (Expr.add
      (Expr.add
        (Expr.add
          (Expr.mul
            (Expr.add (ctlCell tJ) (.const 1))
            (Expr.add
              (Expr.add (.const (triAcc n)) (.const 1))
              (Expr.add
                (Expr.add (ctlCell triJ) (.const 1))
                (Expr.mul (ctlCell wJ) (Expr.add (.const (triAcc m)) (.const 1))))))
          (Expr.add (Expr.add (.const 2) (ctlCell wJ)) (ctlCell freeJ)))
        (Expr.mul (ctlCell tJ)
          (Expr.mul (ctlCell wJ)
            (Expr.mul (.const n) (Expr.mul (.const m) (.const 3))))))
      (Expr.mul (ctlCell tJ)
        (Expr.mul (ctlCell wJ)
          (Expr.mul (Expr.sub (ctlCell wJ) (.const 1)) (.const m)))))
    (Expr.add (Expr.mul (ctlCell wJ) (ctlCell wJ)) (.const 1))

lemma clauseCountExpr_eval (M n m tJ wJ freeJ triJ T W freeLen A : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hT : σ (M + tJ) = T) (hW : σ (M + wJ) = W)
    (hfree : σ (M + freeJ) = freeLen) (htri : σ (M + triJ) = A) :
    (clauseCountExpr n m tJ wJ freeJ triJ).eval σ =
      (T + 1) * (triAcc n + 1 + (A + 1) + W * (triAcc m + 1))
        + (2 + W + freeLen)
        + T * W * n * m * 3
        + T * W * (W - 1) * m
        + (W * W + 1) := by
  simp [clauseCountExpr, Expr.eval, ctlCell_eval, h0, hT, hW, hfree, htri]
  ring

/-- The complete stand-alone clause-count fragment.  Its input is a store whose
parameter cells already contain `T`, `W`, and `freeLen`; it leaves the count in
`M + rowCountReg`. -/
def clauseCountProg (n m : ℕ) : Program :=
  .seq
    (ctlAssign rowCountReg (.const 0))
    (.seq
      (triAccLoop rowCountReg iterReg persistWReg)
      (ctlAssign rowCountReg
        (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg)))

lemma clauseCountProg_eval (M n m T W freeLen : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hT : σ (M + persistTReg) = T)
    (hW : σ (M + persistWReg) = W)
    (hfree : σ (M + initFreeLenReg) = freeLen) :
    (clauseCountProg n m).eval σ (M + rowCountReg) =
      clauseCount n m T W freeLen := by
  have hrowPos : 1 ≤ rowCountReg := by norm_num [rowCountReg]
  have hiterPos : 1 ≤ iterReg := by norm_num [iterReg]
  have hrowIter : rowCountReg ≠ iterReg := by norm_num [rowCountReg, iterReg]
  have hrowW : rowCountReg ≠ persistWReg := by
    norm_num [rowCountReg, persistWReg]
  have hiterW : iterReg ≠ persistWReg := by
    norm_num [iterReg, persistWReg]
  have hrowT : rowCountReg ≠ persistTReg := by
    norm_num [rowCountReg, persistTReg]
  have hrowFree : rowCountReg ≠ initFreeLenReg := by
    norm_num [rowCountReg, initFreeLenReg]
  let σ1 := (ctlAssign rowCountReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero rowCountReg _ σ hrowPos).trans h0
  have hσ1row : σ1 (M + rowCountReg) = 0 := by
    dsimp [σ1]
    rw [show M + rowCountReg = σ 0 + rowCountReg by rw [h0]]
    rw [ctlAssign_eval_same]
    simp [Expr.eval]
  have hσ1T : σ1 (M + persistTReg) = T := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hT
  have hσ1W : σ1 (M + persistWReg) = W := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hW
  have hσ1free : σ1 (M + initFreeLenReg) = freeLen := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; omega)]
    exact hfree
  have hloop := triAccLoop_eval M rowCountReg iterReg persistWReg W 0 σ1 hσ10 hσ1row hσ1W
    hrowPos hiterPos hrowIter hrowW hiterW
  have hzero := triAccLoop_zero M rowCountReg iterReg persistWReg σ1 hσ10 hrowPos hiterPos
  have hframeT := triAccLoop_frame M rowCountReg iterReg persistWReg persistTReg σ1 hσ10
    hrowPos hiterPos (by norm_num [persistTReg, rowCountReg])
      (by norm_num [persistTReg, iterReg]) hiterW
  have hframeW := triAccLoop_frame M rowCountReg iterReg persistWReg persistWReg σ1 hσ10
    hrowPos hiterPos (by norm_num [persistWReg, rowCountReg])
      (by norm_num [persistWReg, iterReg]) hiterW
  have hframeFree := triAccLoop_frame M rowCountReg iterReg persistWReg initFreeLenReg σ1 hσ10
    hrowPos hiterPos (by norm_num [initFreeLenReg, rowCountReg])
      (by norm_num [initFreeLenReg, iterReg]) hiterW
  let τ := (triAccLoop rowCountReg iterReg persistWReg).eval σ1
  have hτ0 : τ 0 = M := by simpa [τ] using hzero
  have hτrow : τ (M + rowCountReg) = triAcc W := by simpa [τ] using hloop.1
  have hτT : τ (M + persistTReg) = T := by
    calc
      τ (M + persistTReg) = σ1 (M + persistTReg) := by simpa [τ] using hframeT
      _ = T := hσ1T
  have hτW : τ (M + persistWReg) = W := by
    calc
      τ (M + persistWReg) = σ1 (M + persistWReg) := by simpa [τ] using hframeW
      _ = W := hσ1W
  have hτfree : τ (M + initFreeLenReg) = freeLen := by
    calc
      τ (M + initFreeLenReg) = σ1 (M + initFreeLenReg) := by simpa [τ] using hframeFree
      _ = freeLen := hσ1free
  have hexpr := clauseCountExpr_eval M n m persistTReg persistWReg initFreeLenReg
    rowCountReg T W freeLen (triAcc W) τ hτ0 hτT hτW hτfree hτrow
  have hassign :
      (ctlAssign rowCountReg
        (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg)).eval τ
          (M + rowCountReg) = clauseCount n m T W freeLen := by
    have hsame := ctlAssign_eval_same rowCountReg
      (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg) τ
    calc
      (ctlAssign rowCountReg
        (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg)).eval τ
          (M + rowCountReg) =
          (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg).eval τ := by
            rw [show M + rowCountReg = τ 0 + rowCountReg by rw [hτ0]]
            exact hsame
      _ = clauseCount n m T W freeLen := by
        simpa [clauseCount] using hexpr
  simpa [clauseCountProg, τ, σ1, eval_seq] using hassign


end NPComplete.CookLevin

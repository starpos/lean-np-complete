module

public import NPComplete.RAMToTM.Generic.Relocate

/-!
# Generic wide-gap input relocation

A relocation destination with a length-dependent gap lets later RAM-to-TM phases reserve additional
memory without tying the copy mechanism to a particular encoding.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BoundedWhile (writeReg cost_seq cost_forN
  loopCost loopCost_le_of_body_le)

/-! ## Layout and structured postconditions -/

def loadRelocControlGap : ℕ := 100
def loadRelocSrcJ : ℕ := 1
def loadRelocDstJ : ℕ := 2
def loadRelocLenJ : ℕ := 3
def loadRelocBaseJ : ℕ := 4

def loadRelocCtlAddr (j : ℕ) : Expr := .add (.reg 0) (.const j)
def loadRelocCtlCell (j : ℕ) : Expr := .regInd (loadRelocCtlAddr j)
def loadRelocCtlAssign (j : ℕ) (e : Expr) : Program :=
  .assignInd (loadRelocCtlAddr j) e

/-! ## The executable phase -/

def loadRelocStep : Program :=
  .seq
    (.assignInd (loadRelocCtlCell loadRelocDstJ)
      (.regInd (loadRelocCtlCell loadRelocSrcJ)))
    (.seq
      (loadRelocCtlAssign loadRelocSrcJ
        (.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)))
      (loadRelocCtlAssign loadRelocDstJ
        (.add (loadRelocCtlCell loadRelocDstJ) (.const 1))))

/-- The destination base is `2 * N + loadRelocControlGap` (`reg 0` added twice), not `N +
    loadRelocControlGap` as in `relocateSetup` — the structural change that widens the gap. -/
def loadRelocSetup : Program :=
  .seq (loadRelocCtlAssign loadRelocSrcJ (.const 1))
    (.seq (loadRelocCtlAssign loadRelocDstJ
      (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))))
      (.seq (loadRelocCtlAssign loadRelocLenJ (.reg 0))
        (loadRelocCtlAssign loadRelocBaseJ
          (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))))))

def loadRelocProg : Program :=
  .seq loadRelocSetup (.forN (loadRelocCtlCell loadRelocLenJ) loadRelocStep)

lemma loadRelocCtlAddr_eval (j : ℕ) (σ : Store) :
    (loadRelocCtlAddr j).eval σ = σ 0 + j := by
  simp [loadRelocCtlAddr, Expr.eval]

lemma loadRelocCtlCell_eval (j : ℕ) (σ : Store) :
    (loadRelocCtlCell j).eval σ = σ (σ 0 + j) := by
  simp [loadRelocCtlCell, Expr.eval, loadRelocCtlAddr_eval]

lemma loadRelocCtlAssign_eval_same (j : ℕ) (e : Expr) (σ : Store) :
    ((loadRelocCtlAssign j e).eval σ) (σ 0 + j) = e.eval σ := by
  simp [loadRelocCtlAssign, eval_assignInd, loadRelocCtlAddr_eval, writeReg_same]

lemma loadRelocCtlAssign_eval_diff (j : ℕ) (e : Expr) (σ : Store) (r : ℕ)
    (h : r ≠ σ 0 + j) :
    ((loadRelocCtlAssign j e).eval σ) r = σ r := by
  simp only [loadRelocCtlAssign, eval_assignInd, loadRelocCtlAddr_eval]
  exact writeReg_diff σ (σ 0 + j) (e.eval σ) r h

/-- `loadRelocSetup`'s dst/base slots hold `N + (N + loadRelocControlGap)` — the shape the
    Program's `Expr` literally computes (`reg 0` added twice); `= 2 * N + loadRelocControlGap`
    by `omega`, used at the public-facing lemmas below. -/
lemma loadRelocSetup_eval (N : ℕ) (σ : Store) (h0 : σ 0 = N) :
    loadRelocSetup.eval σ =
      fun r => if r = N + loadRelocSrcJ then 1 else
        if r = N + loadRelocDstJ then N + (N + loadRelocControlGap) else
        if r = N + loadRelocLenJ then N else
        if r = N + loadRelocBaseJ then N + (N + loadRelocControlGap) else σ r := by
  funext r
  simp [loadRelocSetup, loadRelocCtlAssign, eval_seq, eval_assignInd,
    loadRelocCtlAddr_eval, Expr.eval, writeReg, loadRelocControlGap, loadRelocSrcJ,
    loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ, h0]
  by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
    by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;> simp_all

lemma loadRelocStep_eval (N C t : ℕ) (τ : Store)
    (h0 : τ 0 = N)
    (hs : τ (N + loadRelocSrcJ) = 1 + t)
    (hd : τ (N + loadRelocDstJ) = C + t)
    (hgap : N + loadRelocControlGap ≤ C) :
    loadRelocStep.eval τ =
      writeReg (writeReg (writeReg τ (C + t) (τ (1 + t)))
        (N + loadRelocSrcJ) (2 + t)) (N + loadRelocDstJ) (C + t + 1) := by
  have hgap' : N + 4 < C + t := by
    simp [loadRelocControlGap] at hgap
    omega
  have h0d : 0 ≠ C + t := by omega
  have hsd : N + loadRelocSrcJ ≠ C + t := by
    simp [loadRelocSrcJ]
    omega
  have hdd : N + loadRelocDstJ ≠ C + t := by
    simp [loadRelocDstJ]
    omega
  simp [loadRelocSrcJ, loadRelocDstJ] at hs hd hsd hdd
  simp [loadRelocStep, loadRelocCtlAssign, loadRelocCtlCell, loadRelocCtlAddr,
    eval_seq, eval_assignInd, Expr.eval, writeReg, h0, hs, hd, h0d,
    hsd, hdd, loadRelocSrcJ, loadRelocDstJ]
  congr 1; simp [Nat.add_left_comm, Nat.add_comm]

def LoadRelocInvariant (σ τ : Store) (N C t : ℕ) : Prop :=
  τ 0 = N ∧
  τ (N + loadRelocSrcJ) = 1 + t ∧
  τ (N + loadRelocDstJ) = C + t ∧
  τ (N + loadRelocLenJ) = N ∧
  τ (N + loadRelocBaseJ) = C ∧
  (∀ q, q < t → τ (C + q) = σ (1 + q)) ∧
  (∀ r, r < N + 1 → τ r = σ r)

lemma loadRelocStep_invariant (σ τ : Store) (N C t : ℕ)
    (hgap : N + loadRelocControlGap ≤ C) (ht : t < N)
    (hInv : LoadRelocInvariant σ τ N C t) :
    LoadRelocInvariant σ (loadRelocStep.eval τ) N C (t + 1) := by
  have hgapNum : N + 8 ≤ C := by simp [loadRelocControlGap] at hgap ⊢; omega
  have hgap' : N + 4 < C + t := by
    omega
  have hstep := loadRelocStep_eval N C t τ hInv.1 hInv.2.1 hInv.2.2.1 hgap
  have hlow : ∀ r, r < N + 1 → τ r = σ r := hInv.2.2.2.2.2.2
  have hC0 : C + t ≠ 0 := by omega
  have hCsrc : C + t ≠ N + loadRelocSrcJ := by
    simp [loadRelocSrcJ]
    omega
  have hCdst : C + t ≠ N + loadRelocDstJ := by
    simp [loadRelocDstJ]
    omega
  have hsrc0 : N + loadRelocSrcJ ≠ 0 := by simp [loadRelocSrcJ]
  have hdst0 : N + loadRelocDstJ ≠ 0 := by simp [loadRelocDstJ]
  have hsrcdst : N + loadRelocSrcJ ≠ N + loadRelocDstJ := by
    simp [loadRelocSrcJ, loadRelocDstJ]
  have hCq (q : ℕ) (hq : q < t) : C + q ≠ C + t := by omega
  have hClen : C + t ≠ N + loadRelocLenJ := by
    simp [loadRelocLenJ]
    omega
  have hCbase : C + t ≠ N + loadRelocBaseJ := by
    simp [loadRelocBaseJ]
    omega
  have hsrcLen : N + loadRelocSrcJ ≠ N + loadRelocLenJ := by
    simp [loadRelocSrcJ, loadRelocLenJ]
  have hdstLen : N + loadRelocDstJ ≠ N + loadRelocLenJ := by
    simp [loadRelocDstJ, loadRelocLenJ]
  have hsrcBase : N + loadRelocSrcJ ≠ N + loadRelocBaseJ := by
    simp [loadRelocSrcJ, loadRelocBaseJ]
  have hdstBase : N + loadRelocDstJ ≠ N + loadRelocBaseJ := by
    simp [loadRelocDstJ, loadRelocBaseJ]
  have hnew : (loadRelocStep.eval τ) (C + t) = σ (1 + t) := by
    rw [hstep, writeReg_diff _ _ _ _ hCdst,
      writeReg_diff _ _ _ _ hCsrc, writeReg_same]
    exact hlow (1 + t) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ 0 hdst0.symm,
      writeReg_diff _ (N + loadRelocSrcJ) _ 0 hsrc0.symm,
      writeReg_diff _ (C + t) _ 0 hC0.symm, hInv.1]
  · rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ _ hsrcdst,
      writeReg_same]
    omega
  · rw [hstep]
    have he := congrFun hstep (N + loadRelocDstJ)
    simp [writeReg, loadRelocDstJ] at he
    simp [Nat.add_assoc]
  · rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ _ hdstLen.symm,
      writeReg_diff _ (N + loadRelocSrcJ) _ _ hsrcLen.symm,
      writeReg_diff _ (C + t) _ _ hClen.symm,
      ]
    exact hInv.2.2.2.1
  · rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ _ hdstBase.symm,
      writeReg_diff _ (N + loadRelocSrcJ) _ _ hsrcBase.symm,
      writeReg_diff _ (C + t) _ _ hCbase.symm,
      ]
    exact hInv.2.2.2.2.1
  · intro q hq
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hq) with rfl | hq'
    · exact hnew
    have hqsrc : N + loadRelocSrcJ ≠ C + q := by
      simp [loadRelocSrcJ]
      omega
    have hqdst : N + loadRelocDstJ ≠ C + q := by
      simp [loadRelocDstJ]
      omega
    rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ _ hqdst.symm,
      writeReg_diff _ (N + loadRelocSrcJ) _ _ hqsrc.symm,
      writeReg_diff _ (C + t) _ _ (hCq q hq')]
    exact hInv.2.2.2.2.2.1 q hq'
  · intro r hr
    have hsr : N + loadRelocSrcJ ≠ r := by
      simp [loadRelocSrcJ]
      omega
    have hdr : N + loadRelocDstJ ≠ r := by
      simp [loadRelocDstJ]
      omega
    have hcr : C + t ≠ r := by omega
    rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ r hdr.symm,
      writeReg_diff _ (N + loadRelocSrcJ) _ r hsr.symm,
      writeReg_diff _ (C + t) _ r hcr.symm]
    exact hInv.2.2.2.2.2.2 r hr

lemma loadRelocSetup_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    LoadRelocInvariant σ (loadRelocSetup.eval σ) N (N + (N + loadRelocControlGap)) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [loadRelocSetup_eval N σ h0]
    simpa [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ] using h0
  · rw [loadRelocSetup_eval N σ h0]
    simp [loadRelocSrcJ]
  · rw [loadRelocSetup_eval N σ h0]
    simp [loadRelocControlGap, loadRelocSrcJ, loadRelocDstJ]
  · rw [loadRelocSetup_eval N σ h0]
    simp [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ]
  · rw [loadRelocSetup_eval N σ h0]
    simp [loadRelocControlGap, loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ]
  · intro q hq
    omega
  · intro r hr
    rw [loadRelocSetup_eval N σ h0]
    by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
      by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;>
      simp_all [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ]

lemma load_reloc_loop_invariant_from (σ τ : Store) (N C : ℕ)
    (hgap : N + loadRelocControlGap ≤ C)
    (h0 : LoadRelocInvariant σ τ N C 0) :
    ∀ t, t ≤ N → LoadRelocInvariant σ (loopEval loadRelocStep t τ) N C t := by
  intro t
  induction t generalizing τ with
  | zero => intro _; simpa using h0
  | succ t ih =>
      intro hle
      have ht : t < N := by omega
      have hprev := ih (τ := τ) h0 (by omega)
      rw [loopEval_add, loopEval_one]
      exact loadRelocStep_invariant σ _ N C t hgap ht hprev

lemma load_reloc_loop_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ∀ t, t ≤ N →
      LoadRelocInvariant σ
        (loopEval loadRelocStep t (loadRelocSetup.eval σ))
        N (N + (N + loadRelocControlGap)) t := by
  intro t ht
  exact load_reloc_loop_invariant_from σ (loadRelocSetup.eval σ) N
    (N + (N + loadRelocControlGap)) (by omega)
    (loadRelocSetup_invariant σ N h0) t ht

lemma loadRelocProg_eval_eq_loop (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    loadRelocProg.eval σ =
      loopEval loadRelocStep N (loadRelocSetup.eval σ) := by
  have hbound : (loadRelocCtlCell loadRelocLenJ).eval (loadRelocSetup.eval σ) = N := by
    rw [loadRelocCtlCell_eval, loadRelocSetup_eval N σ h0]
    simp [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ, h0]
  unfold loadRelocProg
  rw [eval_seq, eval_forN, hbound]

lemma loadRelocStep_frame (τ : Store) (N C t : ℕ)
    (hgap : N + loadRelocControlGap ≤ C) (ht : t < N)
    (h0 : τ 0 = N)
    (hs : τ (N + loadRelocSrcJ) = 1 + t)
    (hd : τ (N + loadRelocDstJ) = C + t) :
    ∀ r, r < N + 1 ∨ C + N ≤ r → loadRelocStep.eval τ r = τ r := by
  intro r hr
  have hgapNum : N + 8 ≤ C := by simp [loadRelocControlGap] at hgap ⊢; omega
  have hC : C + t < C + N := by omega
  have hC0 : r ≠ C + t := by
    rcases hr with hr | hr <;> omega
  have hsrc : r ≠ N + loadRelocSrcJ := by
    rcases hr with hr | hr
    · simp [loadRelocSrcJ]
      omega
    · simp [loadRelocSrcJ]
      omega
  have hdst : r ≠ N + loadRelocDstJ := by
    rcases hr with hr | hr
    · simp [loadRelocDstJ]
      omega
    · simp [loadRelocDstJ]
      omega
  have hstep := loadRelocStep_eval N C t τ h0 hs hd hgap
  rw [hstep, writeReg_diff _ (N + loadRelocDstJ) _ r hdst,
    writeReg_diff _ (N + loadRelocSrcJ) _ r hsrc,
    writeReg_diff _ (C + t) _ r hC0]

lemma load_reloc_loop_frame (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ∀ t, t ≤ N →
      ∀ r, r < N + 1 ∨ (N + (N + loadRelocControlGap)) + N ≤ r →
        (loopEval loadRelocStep t (loadRelocSetup.eval σ)) r = σ r := by
  intro t
  induction t with
  | zero =>
      intro _ r hr
      rw [loopEval_zero, loadRelocSetup_eval N σ h0]
      rcases hr with hr | hr
      · by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
          by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;>
          simp_all [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ]
      · simp only [loadRelocControlGap] at hr
        by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
          by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;>
          simp_all [loadRelocControlGap, loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ,
            loadRelocBaseJ] <;> omega
  | succ t ih =>
      intro hle r hr
      have ht : t < N := by omega
      have hprev := ih (by omega) r hr
      have hInv := load_reloc_loop_invariant σ N h0 t (by omega)
      rw [loopEval_add, loopEval_one]
      rw [loadRelocStep_frame _ N (N + (N + loadRelocControlGap)) t
        (by omega) ht hInv.1 hInv.2.1 hInv.2.2.1 r hr]
      exact hprev

/-! ## `ScanFree`: no `scanList`/`lookup` node anywhere in `loadRelocProg`

Callers that compose relocation with later stages under `compiledOperandBound_of_programBoundedIn`
need the input-staging component to be `ScanFree`. -/

lemma scanFree_loadRelocStep : ScanFree loadRelocStep := by
  simp [ScanFree, loadRelocStep, loadRelocCtlAssign]

lemma scanFree_loadRelocSetup : ScanFree loadRelocSetup := by
  simp [ScanFree, loadRelocSetup, loadRelocCtlAssign]

lemma scanFree_loadRelocProg : ScanFree loadRelocProg := by
  simp [ScanFree, loadRelocProg, scanFree_loadRelocSetup, scanFree_loadRelocStep]

/-! ## Access-range certificate

`ProgramBoundedIn` tracks only addresses and intermediate expression values.  The certificate below
is therefore independent of the cost estimate: it assumes the initial length cell and a large
enough bound, but no bound on the input bits or on any other store value. -/

lemma loadRelocCtlAddr_bounded_in (τ : Store) (N B j : ℕ)
    (h0 : τ 0 = N) (hj : N + j ≤ B) :
    ExprBoundedIn B τ (loadRelocCtlAddr j) := by
  simp [ExprBoundedIn, loadRelocCtlAddr, Expr.eval, h0]
  omega

lemma loadRelocCtlCell_bounded_in (τ : Store) (N B j : ℕ)
    (h0 : τ 0 = N) (hj : N + j ≤ B) :
    ExprBoundedIn B τ (loadRelocCtlCell j) := by
  refine ⟨loadRelocCtlAddr_bounded_in τ N B j h0 hj, ?_⟩
  simpa [loadRelocCtlAddr_eval, h0] using hj

lemma loadRelocCtlAssign_bounded_in (τ : Store) (N B j : ℕ) (e : Expr)
    (h0 : τ 0 = N) (he : ExprBoundedIn B τ e) (hj : N + j ≤ B) :
    ProgramBoundedIn B τ (loadRelocCtlAssign j e) := by
  change ExprBoundedIn B τ (loadRelocCtlAddr j) ∧
    ExprBoundedIn B τ e ∧ (loadRelocCtlAddr j).eval τ ≤ B
  exact ⟨loadRelocCtlAddr_bounded_in τ N B j h0 hj, he, by
    simpa [loadRelocCtlAddr_eval, h0] using hj⟩

/-- Note `loadRelocCtlAddr loadRelocControlGap = .add (.reg 0) (.const loadRelocControlGap)`, so
    the doubled destination `.add (.reg 0) (loadRelocCtlAddr loadRelocControlGap)` is bounded via
    `loadRelocCtlAddr_bounded_in` directly rather than needing a bespoke sub-proof. -/
lemma loadRelocSetup_programBoundedIn (σ : Store) (N B : ℕ)
    (h0 : σ 0 = N) (hB : N + (N + loadRelocControlGap) + N ≤ B) :
    ProgramBoundedIn B σ loadRelocSetup := by
  simp only [loadRelocControlGap] at hB
  have hB' : N + 8 + N ≤ B := by omega
  have hN1 : N + loadRelocSrcJ ≤ B := by simp [loadRelocSrcJ]; omega
  have hN2 : N + loadRelocDstJ ≤ B := by simp [loadRelocDstJ]; omega
  have hN3 : N + loadRelocLenJ ≤ B := by simp [loadRelocLenJ]; omega
  have hN4 : N + loadRelocBaseJ ≤ B := by simp [loadRelocBaseJ]; omega
  have he1 : ExprBoundedIn B σ (.const 1) := by simp [ExprBoundedIn]; omega
  have hp1 := loadRelocCtlAssign_bounded_in σ N B loadRelocSrcJ (.const 1) h0 he1 hN1
  let σ1 := (loadRelocCtlAssign loadRelocSrcJ (.const 1)).eval σ
  have h01 : σ1 0 = N := by
    dsimp [σ1]
    simp [loadRelocCtlAssign, loadRelocCtlAddr, loadRelocSrcJ, Expr.eval,
      writeReg, h0]
  have hNgap : N + loadRelocControlGap ≤ B := by
    simp only [loadRelocControlGap]; omega
  have he2 : ExprBoundedIn B σ1 (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))) := by
    refine ⟨by simp [ExprBoundedIn], loadRelocCtlAddr_bounded_in σ1 N B loadRelocControlGap h01
      hNgap, ?_⟩
    simp only [Expr.eval, h01, loadRelocControlGap]
    omega
  have hp2 := loadRelocCtlAssign_bounded_in σ1 N B loadRelocDstJ
    (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))) h01 he2 hN2
  let σ2 := (loadRelocCtlAssign loadRelocDstJ
    (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap)))).eval σ1
  have h02 : σ2 0 = N := by
    dsimp [σ2]
    simp [loadRelocCtlAssign, loadRelocCtlAddr, loadRelocDstJ, Expr.eval,
      writeReg, h01]
  have he3 : ExprBoundedIn B σ2 (.reg 0) := by
    simp [ExprBoundedIn]
  have hp3 := loadRelocCtlAssign_bounded_in σ2 N B loadRelocLenJ (.reg 0) h02 he3 hN3
  let σ3 := (loadRelocCtlAssign loadRelocLenJ (.reg 0)).eval σ2
  have h03 : σ3 0 = N := by
    dsimp [σ3]
    simp [loadRelocCtlAssign, loadRelocCtlAddr, loadRelocLenJ, Expr.eval,
      writeReg, h02]
  have he4 : ExprBoundedIn B σ3 (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))) := by
    refine ⟨by simp [ExprBoundedIn], loadRelocCtlAddr_bounded_in σ3 N B loadRelocControlGap h03
      hNgap, ?_⟩
    simp only [Expr.eval, h03, loadRelocControlGap]
    omega
  have hp4 := loadRelocCtlAssign_bounded_in σ3 N B loadRelocBaseJ
    (.add (.reg 0) (.add (.reg 0) (.const loadRelocControlGap))) h03 he4 hN4
  unfold loadRelocSetup
  exact ⟨hp1, ⟨hp2, ⟨hp3, hp4⟩⟩⟩

lemma loadRelocStep_programBoundedIn (τ : Store) (N C t B : ℕ)
    (h0 : τ 0 = N) (hs : τ (N + loadRelocSrcJ) = 1 + t)
    (hd : τ (N + loadRelocDstJ) = C + t)
    (hgap : N + loadRelocControlGap ≤ C) (ht : t < N)
    (hB : C + N ≤ B) :
    ProgramBoundedIn B τ loadRelocStep := by
  have hB' : N + 8 + N ≤ B := by
    have := hB
    simp [loadRelocControlGap] at hgap
    omega
  have hN1 : N + loadRelocSrcJ ≤ B := by simp [loadRelocSrcJ]; omega
  have hN2 : N + loadRelocDstJ ≤ B := by simp [loadRelocDstJ]; omega
  have hs' : τ (N + 1) = 1 + t := by simpa [loadRelocSrcJ] using hs
  have hd' : τ (N + 2) = C + t := by simpa [loadRelocDstJ] using hd
  have hgap8 : N + 8 ≤ C := by simp [loadRelocControlGap] at hgap ⊢; omega
  have heDst : ExprBoundedIn B τ (loadRelocCtlCell loadRelocDstJ) := by
    exact loadRelocCtlCell_bounded_in τ N B loadRelocDstJ h0 hN2
  have heSrc : ExprBoundedIn B τ (loadRelocCtlCell loadRelocSrcJ) := by
    exact loadRelocCtlCell_bounded_in τ N B loadRelocSrcJ h0 hN1
  have hp1 : ProgramBoundedIn B τ
      (Program.assignInd (loadRelocCtlCell loadRelocDstJ)
        (.regInd (loadRelocCtlCell loadRelocSrcJ))) := by
    change ExprBoundedIn B τ (loadRelocCtlCell loadRelocDstJ) ∧
      ExprBoundedIn B τ (.regInd (loadRelocCtlCell loadRelocSrcJ)) ∧
      (loadRelocCtlCell loadRelocDstJ).eval τ ≤ B
    refine ⟨heDst, ⟨heSrc, ?_⟩, ?_⟩
    · simp [loadRelocCtlCell_eval, loadRelocSrcJ, h0, hs']
      omega
    · simp [loadRelocCtlCell_eval, loadRelocDstJ, h0, hd']
      omega
  let τ1 := (Program.assignInd (loadRelocCtlCell loadRelocDstJ)
    (.regInd (loadRelocCtlCell loadRelocSrcJ))).eval τ
  have hp1_eval : τ1 = writeReg τ (C + t) (τ (1 + t)) := by
    funext r
    simp [τ1, loadRelocCtlCell_eval, Expr.eval, h0]
    rw [hd, hs]
  have h01 : τ1 0 = N := by
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) 0 (by omega), h0]
  have hs1 : τ1 (N + loadRelocSrcJ) = 1 + t := by
    have hne : N + loadRelocSrcJ ≠ C + t := by simp [loadRelocSrcJ]; omega
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) (N + loadRelocSrcJ) hne]
    simpa [loadRelocSrcJ] using hs
  have hd1 : τ1 (N + loadRelocDstJ) = C + t := by
    have hne : N + loadRelocDstJ ≠ C + t := by simp [loadRelocDstJ]; omega
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) (N + loadRelocDstJ) hne]
    exact hd
  have heIncSrc : ExprBoundedIn B τ1
      (.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) := by
    refine ⟨loadRelocCtlCell_bounded_in τ1 N B loadRelocSrcJ h01 hN1, ?_, ?_⟩
    · simp [ExprBoundedIn]
      omega
    · have hs1' : τ1 (N + 1) = 1 + t := by simpa [loadRelocSrcJ] using hs1
      simp [loadRelocCtlCell_eval, loadRelocSrcJ, Expr.eval, h01, hs1']
      omega
  have hp2 := loadRelocCtlAssign_bounded_in τ1 N B loadRelocSrcJ
    (.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) h01 heIncSrc hN1
  let τ2 := (loadRelocCtlAssign loadRelocSrcJ
    (.add (loadRelocCtlCell loadRelocSrcJ) (.const 1))).eval τ1
  have hp2_eval : τ2 (τ1 0 + loadRelocSrcJ) =
      (Expr.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)).eval τ1 := by
    dsimp [τ2]
    exact loadRelocCtlAssign_eval_same loadRelocSrcJ
      (Expr.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) τ1
  have h02 : τ2 0 = N := by
    dsimp [τ2]
    have he := loadRelocCtlAssign_eval_diff loadRelocSrcJ
      (.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) τ1 0
      (by simp [h01, loadRelocSrcJ])
    simpa [h01] using he.trans h01
  have hs2 : τ2 (N + loadRelocSrcJ) = 2 + t := by
    dsimp [τ2]
    rw [show N + loadRelocSrcJ = τ1 0 + loadRelocSrcJ by simp [h01, loadRelocSrcJ]]
    rw [loadRelocCtlAssign_eval_same loadRelocSrcJ
      (Expr.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) τ1]
    have hs1' : τ1 (N + 1) = 1 + t := by simpa [loadRelocSrcJ] using hs1
    simp [loadRelocCtlCell_eval, loadRelocSrcJ, Expr.eval, h01, hs1']
    omega
  have hd2 : τ2 (N + loadRelocDstJ) = C + t := by
    dsimp [τ2]
    have hne : N + loadRelocDstJ ≠ τ1 0 + loadRelocSrcJ := by
      simp [h01, loadRelocSrcJ, loadRelocDstJ]
    rw [loadRelocCtlAssign_eval_diff loadRelocSrcJ
      (Expr.add (loadRelocCtlCell loadRelocSrcJ) (.const 1)) τ1 (N + loadRelocDstJ) hne]
    exact hd1
  have heIncDst : ExprBoundedIn B τ2
      (.add (loadRelocCtlCell loadRelocDstJ) (.const 1)) := by
    refine ⟨loadRelocCtlCell_bounded_in τ2 N B loadRelocDstJ h02 hN2, ?_, ?_⟩
    · simp [ExprBoundedIn]
      omega
    · have hd2' : τ2 (N + 2) = C + t := by simpa [loadRelocDstJ] using hd2
      simp [loadRelocCtlCell_eval, loadRelocDstJ, h02, hd2', Expr.eval]
      omega
  have hp3 := loadRelocCtlAssign_bounded_in τ2 N B loadRelocDstJ
    (.add (loadRelocCtlCell loadRelocDstJ) (.const 1)) h02 heIncDst hN2
  unfold loadRelocStep
  exact ⟨hp1, ⟨hp2, hp3⟩⟩

lemma loadRelocProg_programBoundedIn (σ : Store) (N B : ℕ)
    (h0 : σ 0 = N)
    (hB : N + (N + loadRelocControlGap) + N ≤ B) :
    ProgramBoundedIn B σ loadRelocProg := by
  have hsetup := loadRelocSetup_programBoundedIn σ N B h0 hB
  have hbody : ∀ m' < N,
      ProgramBoundedIn B (loopEval loadRelocStep m' (loadRelocSetup.eval σ)) loadRelocStep := by
    intro m' hm'
    have hInv := load_reloc_loop_invariant σ N h0 m' (by omega)
    exact loadRelocStep_programBoundedIn _ N (N + (N + loadRelocControlGap)) m' B
      hInv.1 hInv.2.1 hInv.2.2.1 (by omega) hm' hB
  unfold loadRelocProg
  have hsetup0 : (loadRelocSetup.eval σ) 0 = N := by
    rw [loadRelocSetup_eval N σ h0]
    simp [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ, loadRelocBaseJ, h0]
  have hlen : ExprBoundedIn B (loadRelocSetup.eval σ)
      (loadRelocCtlCell loadRelocLenJ) := by
    have hB' : N + 8 + N ≤ B := by simp [loadRelocControlGap] at hB ⊢; omega
    exact loadRelocCtlCell_bounded_in (loadRelocSetup.eval σ) N B loadRelocLenJ hsetup0
      (by simp [loadRelocLenJ]; omega)
  change ProgramBoundedIn B σ loadRelocSetup ∧
    ProgramBoundedIn B (loadRelocSetup.eval σ)
      (.forN (loadRelocCtlCell loadRelocLenJ) loadRelocStep)
  have hbound : (loadRelocCtlCell loadRelocLenJ).eval (loadRelocSetup.eval σ) = N := by
    rw [loadRelocCtlCell_eval, hsetup0, loadRelocSetup_eval N σ h0]
    simp [loadRelocSrcJ, loadRelocDstJ, loadRelocLenJ]
  exact ⟨hsetup, ⟨hlen, by simpa [hbound] using hbody⟩⟩

end NPComplete.RAMToTM

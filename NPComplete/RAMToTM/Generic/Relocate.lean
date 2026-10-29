module

public import NPComplete.BitEncoding
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalize
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider

/-!
# Generic runtime relocation of a bit input

This phase is shared by RAM-to-TM constructions that need to move an input into a separated
region while preserving the low cells for a later phase.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BoundedWhile (writeReg cost_seq cost_forN
  loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits)

/-! ## Layout and structured postconditions -/

def relocateControlGap : ℕ := 100
def relocateSrcJ : ℕ := 1
def relocateDstJ : ℕ := 2
def relocateLenJ : ℕ := 3
def relocateBaseJ : ℕ := 4

def relocateCtlAddr (j : ℕ) : Expr := .add (.reg 0) (.const j)
def relocateCtlCell (j : ℕ) : Expr := .regInd (relocateCtlAddr j)
def relocateCtlAssign (j : ℕ) (e : Expr) : Program :=
  .assignInd (relocateCtlAddr j) e

/- The two-sided frame below is deliberately not a claim that the original input may be
   discarded.  The eventual finalize phase must cover the original `[1, N]` region either by
   overwriting it in the output window or by including it in its zeroing range; a function-wide
   canonical-store equality cannot justify destruction merely because decoding has finished. -/

/-! ## The executable phase -/

def relocateStep : Program :=
  .seq
    (.assignInd (relocateCtlCell relocateDstJ)
      (.regInd (relocateCtlCell relocateSrcJ)))
    (.seq
      (relocateCtlAssign relocateSrcJ
        (.add (relocateCtlCell relocateSrcJ) (.const 1)))
      (relocateCtlAssign relocateDstJ
        (.add (relocateCtlCell relocateDstJ) (.const 1))))

def relocateSetup : Program :=
  .seq (relocateCtlAssign relocateSrcJ (.const 1))
    (.seq (relocateCtlAssign relocateDstJ
      (.add (.reg 0) (.const relocateControlGap)))
      (.seq (relocateCtlAssign relocateLenJ (.reg 0))
        (relocateCtlAssign relocateBaseJ
          (.add (.reg 0) (.const relocateControlGap)))))

def relocateProg : Program :=
  .seq relocateSetup (.forN (relocateCtlCell relocateLenJ) relocateStep)

lemma relocateCtlAddr_eval (j : ℕ) (σ : Store) :
    (relocateCtlAddr j).eval σ = σ 0 + j := by
  simp [relocateCtlAddr, Expr.eval]

lemma relocateCtlCell_eval (j : ℕ) (σ : Store) :
    (relocateCtlCell j).eval σ = σ (σ 0 + j) := by
  simp [relocateCtlCell, Expr.eval, relocateCtlAddr_eval]

lemma relocateCtlAssign_eval_same (j : ℕ) (e : Expr) (σ : Store) :
    ((relocateCtlAssign j e).eval σ) (σ 0 + j) = e.eval σ := by
  simp [relocateCtlAssign, eval_assignInd, relocateCtlAddr_eval, writeReg_same]

lemma relocateCtlAssign_eval_diff (j : ℕ) (e : Expr) (σ : Store) (r : ℕ)
    (h : r ≠ σ 0 + j) :
    ((relocateCtlAssign j e).eval σ) r = σ r := by
  simp only [relocateCtlAssign, eval_assignInd, relocateCtlAddr_eval]
  exact writeReg_diff σ (σ 0 + j) (e.eval σ) r h

lemma relocateSetup_eval (N : ℕ) (σ : Store) (h0 : σ 0 = N) :
    relocateSetup.eval σ =
      fun r => if r = N + relocateSrcJ then 1 else
        if r = N + relocateDstJ then N + relocateControlGap else
        if r = N + relocateLenJ then N else
        if r = N + relocateBaseJ then N + relocateControlGap else σ r := by
  funext r
  simp [relocateSetup, relocateCtlAssign, eval_seq, eval_assignInd,
    relocateCtlAddr_eval, Expr.eval, writeReg, relocateControlGap, relocateSrcJ,
    relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
    by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;> simp_all

lemma relocateStep_eval (N C t : ℕ) (τ : Store)
    (h0 : τ 0 = N)
    (hs : τ (N + relocateSrcJ) = 1 + t)
    (hd : τ (N + relocateDstJ) = C + t)
    (hgap : N + relocateControlGap ≤ C) :
    relocateStep.eval τ =
      writeReg (writeReg (writeReg τ (C + t) (τ (1 + t)))
        (N + relocateSrcJ) (2 + t)) (N + relocateDstJ) (C + t + 1) := by
  have hgap' : N + 4 < C + t := by
    simp [relocateControlGap] at hgap
    omega
  have h0d : 0 ≠ C + t := by omega
  have hsd : N + relocateSrcJ ≠ C + t := by
    simp [relocateSrcJ]
    omega
  have hdd : N + relocateDstJ ≠ C + t := by
    simp [relocateDstJ]
    omega
  simp [relocateSrcJ, relocateDstJ] at hs hd hsd hdd
  simp [relocateStep, relocateCtlAssign, relocateCtlCell, relocateCtlAddr,
    eval_seq, eval_assignInd, Expr.eval, writeReg, h0, hs, hd, h0d,
    hsd, hdd, relocateSrcJ, relocateDstJ]
  congr 1; simp [Nat.add_left_comm, Nat.add_comm]

def RelocateInvariant (σ τ : Store) (N C t : ℕ) : Prop :=
  τ 0 = N ∧
  τ (N + relocateSrcJ) = 1 + t ∧
  τ (N + relocateDstJ) = C + t ∧
  τ (N + relocateLenJ) = N ∧
  τ (N + relocateBaseJ) = C ∧
  (∀ q, q < t → τ (C + q) = σ (1 + q)) ∧
  (∀ r, r < N + 1 → τ r = σ r)

lemma relocateStep_invariant (σ τ : Store) (N C t : ℕ)
    (hgap : N + relocateControlGap ≤ C) (ht : t < N)
    (hInv : RelocateInvariant σ τ N C t) :
    RelocateInvariant σ (relocateStep.eval τ) N C (t + 1) := by
  have hgapNum : N + 8 ≤ C := by simp [relocateControlGap] at hgap ⊢; omega
  have hgap' : N + 4 < C + t := by
    omega
  have hstep := relocateStep_eval N C t τ hInv.1 hInv.2.1 hInv.2.2.1 hgap
  have hlow : ∀ r, r < N + 1 → τ r = σ r := hInv.2.2.2.2.2.2
  have hC0 : C + t ≠ 0 := by omega
  have hCsrc : C + t ≠ N + relocateSrcJ := by
    simp [relocateSrcJ]
    omega
  have hCdst : C + t ≠ N + relocateDstJ := by
    simp [relocateDstJ]
    omega
  have hsrc0 : N + relocateSrcJ ≠ 0 := by simp [relocateSrcJ]
  have hdst0 : N + relocateDstJ ≠ 0 := by simp [relocateDstJ]
  have hsrcdst : N + relocateSrcJ ≠ N + relocateDstJ := by
    simp [relocateSrcJ, relocateDstJ]
  have hCq (q : ℕ) (hq : q < t) : C + q ≠ C + t := by omega
  have hClen : C + t ≠ N + relocateLenJ := by
    simp [relocateLenJ]
    omega
  have hCbase : C + t ≠ N + relocateBaseJ := by
    simp [relocateBaseJ]
    omega
  have hsrcLen : N + relocateSrcJ ≠ N + relocateLenJ := by
    simp [relocateSrcJ, relocateLenJ]
  have hdstLen : N + relocateDstJ ≠ N + relocateLenJ := by
    simp [relocateDstJ, relocateLenJ]
  have hsrcBase : N + relocateSrcJ ≠ N + relocateBaseJ := by
    simp [relocateSrcJ, relocateBaseJ]
  have hdstBase : N + relocateDstJ ≠ N + relocateBaseJ := by
    simp [relocateDstJ, relocateBaseJ]
  have hnew : (relocateStep.eval τ) (C + t) = σ (1 + t) := by
    rw [hstep, writeReg_diff _ _ _ _ hCdst,
      writeReg_diff _ _ _ _ hCsrc, writeReg_same]
    exact hlow (1 + t) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep, writeReg_diff _ (N + relocateDstJ) _ 0 hdst0.symm,
      writeReg_diff _ (N + relocateSrcJ) _ 0 hsrc0.symm,
      writeReg_diff _ (C + t) _ 0 hC0.symm, hInv.1]
  · rw [hstep, writeReg_diff _ (N + relocateDstJ) _ _ hsrcdst,
      writeReg_same]
    omega
  · rw [hstep]
    have he := congrFun hstep (N + relocateDstJ)
    simp [writeReg, relocateDstJ] at he
    simp [Nat.add_assoc]
  · rw [hstep, writeReg_diff _ (N + relocateDstJ) _ _ hdstLen.symm,
      writeReg_diff _ (N + relocateSrcJ) _ _ hsrcLen.symm,
      writeReg_diff _ (C + t) _ _ hClen.symm,
      ]
    exact hInv.2.2.2.1
  · rw [hstep, writeReg_diff _ (N + relocateDstJ) _ _ hdstBase.symm,
      writeReg_diff _ (N + relocateSrcJ) _ _ hsrcBase.symm,
      writeReg_diff _ (C + t) _ _ hCbase.symm,
      ]
    exact hInv.2.2.2.2.1
  · intro q hq
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hq) with rfl | hq'
    · exact hnew
    have hqsrc : N + relocateSrcJ ≠ C + q := by
      simp [relocateSrcJ]
      omega
    have hqdst : N + relocateDstJ ≠ C + q := by
      simp [relocateDstJ]
      omega
    rw [hstep, writeReg_diff _ (N + relocateDstJ) _ _ hqdst.symm,
      writeReg_diff _ (N + relocateSrcJ) _ _ hqsrc.symm,
      writeReg_diff _ (C + t) _ _ (hCq q hq')]
    exact hInv.2.2.2.2.2.1 q hq'
  · intro r hr
    have hsr : N + relocateSrcJ ≠ r := by
      simp [relocateSrcJ]
      omega
    have hdr : N + relocateDstJ ≠ r := by
      simp [relocateDstJ]
      omega
    have hcr : C + t ≠ r := by omega
    rw [hstep, writeReg_diff _ (N + relocateDstJ) _ r hdr.symm,
      writeReg_diff _ (N + relocateSrcJ) _ r hsr.symm,
      writeReg_diff _ (C + t) _ r hcr.symm]
    exact hInv.2.2.2.2.2.2 r hr

lemma relocateSetup_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    RelocateInvariant σ (relocateSetup.eval σ) N (N + relocateControlGap) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [relocateSetup_eval N σ h0]
    simpa [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ] using h0
  · rw [relocateSetup_eval N σ h0]
    simp [relocateSrcJ]
  · rw [relocateSetup_eval N σ h0]
    simp [relocateControlGap, relocateSrcJ, relocateDstJ]
  · rw [relocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ]
  · rw [relocateSetup_eval N σ h0]
    simp [relocateControlGap, relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ]
  · intro q hq
    omega
  · intro r hr
    rw [relocateSetup_eval N σ h0]
    by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
      by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;>
      simp_all [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ]

lemma relocate_loop_invariant_from (σ τ : Store) (N C : ℕ)
    (hgap : N + relocateControlGap ≤ C)
    (h0 : RelocateInvariant σ τ N C 0) :
    ∀ t, t ≤ N → RelocateInvariant σ (loopEval relocateStep t τ) N C t := by
  intro t
  induction t generalizing τ with
  | zero => intro _; simpa using h0
  | succ t ih =>
      intro hle
      have ht : t < N := by omega
      have hprev := ih (τ := τ) h0 (by omega)
      rw [loopEval_add, loopEval_one]
      exact relocateStep_invariant σ _ N C t hgap ht hprev

lemma relocate_loop_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ∀ t, t ≤ N →
      RelocateInvariant σ
        (loopEval relocateStep t (relocateSetup.eval σ))
        N (N + relocateControlGap) t := by
  intro t ht
  exact relocate_loop_invariant_from σ (relocateSetup.eval σ) N
    (N + relocateControlGap) (by omega)
    (relocateSetup_invariant σ N h0) t ht

lemma relocateProg_eval_eq_loop (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    relocateProg.eval σ =
      loopEval relocateStep N (relocateSetup.eval σ) := by
  have hbound : (relocateCtlCell relocateLenJ).eval (relocateSetup.eval σ) = N := by
    rw [relocateCtlCell_eval, relocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  unfold relocateProg
  rw [eval_seq, eval_forN, hbound]

/-! ## Access-range certificate

`ProgramBoundedIn` tracks only addresses and intermediate expression values.  The certificate below
is therefore independent of the cost estimate: it assumes the initial length cell and a large
enough bound, but no bound on the input bits or on any other store value. -/

lemma relocateCtlAddr_exprBoundedIn (τ : Store) (N B j : ℕ)
    (h0 : τ 0 = N) (hj : N + j ≤ B) :
    ExprBoundedIn B τ (relocateCtlAddr j) := by
  simp [ExprBoundedIn, relocateCtlAddr, Expr.eval, h0]
  omega

lemma relocateCtlCell_exprBoundedIn (τ : Store) (N B j : ℕ)
    (h0 : τ 0 = N) (hj : N + j ≤ B) :
    ExprBoundedIn B τ (relocateCtlCell j) := by
  refine ⟨relocateCtlAddr_exprBoundedIn τ N B j h0 hj, ?_⟩
  simpa [relocateCtlAddr_eval, h0] using hj

lemma relocateCtlAssign_programBoundedIn (τ : Store) (N B j : ℕ) (e : Expr)
    (h0 : τ 0 = N) (he : ExprBoundedIn B τ e) (hj : N + j ≤ B) :
    ProgramBoundedIn B τ (relocateCtlAssign j e) := by
  change ExprBoundedIn B τ (relocateCtlAddr j) ∧
    ExprBoundedIn B τ e ∧ (relocateCtlAddr j).eval τ ≤ B
  exact ⟨relocateCtlAddr_exprBoundedIn τ N B j h0 hj, he, by
    simpa [relocateCtlAddr_eval, h0] using hj⟩

lemma relocateSetup_programBoundedIn (σ : Store) (N B : ℕ)
    (h0 : σ 0 = N) (hB : N + relocateControlGap + N ≤ B) :
    ProgramBoundedIn B σ relocateSetup := by
  have hB' : N + 8 + N ≤ B := by simp [relocateControlGap] at hB ⊢; omega
  simp [relocateControlGap] at hB
  have hN1 : N + relocateSrcJ ≤ B := by simp [relocateSrcJ]; omega
  have hN2 : N + relocateDstJ ≤ B := by simp [relocateDstJ]; omega
  have hN3 : N + relocateLenJ ≤ B := by simp [relocateLenJ]; omega
  have hN4 : N + relocateBaseJ ≤ B := by simp [relocateBaseJ]; omega
  have he1 : ExprBoundedIn B σ (.const 1) := by simp [ExprBoundedIn]; omega
  have hp1 := relocateCtlAssign_programBoundedIn σ N B relocateSrcJ (.const 1) h0 he1 hN1
  let σ1 := (relocateCtlAssign relocateSrcJ (.const 1)).eval σ
  have h01 : σ1 0 = N := by
    dsimp [σ1]
    simp [relocateCtlAssign, relocateCtlAddr, relocateSrcJ, Expr.eval, writeReg, h0]
  have he2 : ExprBoundedIn B σ1 (.add (.reg 0) (.const relocateControlGap)) := by
    simp [ExprBoundedIn, Expr.eval, relocateControlGap, h01]
    omega
  have hp2 := relocateCtlAssign_programBoundedIn σ1 N B relocateDstJ
    (.add (.reg 0) (.const relocateControlGap)) h01 he2 hN2
  let σ2 := (relocateCtlAssign relocateDstJ
    (.add (.reg 0) (.const relocateControlGap))).eval σ1
  have h02 : σ2 0 = N := by
    dsimp [σ2]
    simp [relocateCtlAssign, relocateCtlAddr, relocateDstJ, Expr.eval, writeReg, h01]
  have he3 : ExprBoundedIn B σ2 (.reg 0) := by
    simp [ExprBoundedIn]
  have hp3 := relocateCtlAssign_programBoundedIn σ2 N B relocateLenJ (.reg 0) h02 he3 hN3
  let σ3 := (relocateCtlAssign relocateLenJ (.reg 0)).eval σ2
  have h03 : σ3 0 = N := by
    dsimp [σ3]
    simp [relocateCtlAssign, relocateCtlAddr, relocateLenJ, Expr.eval, writeReg, h02]
  have he4 : ExprBoundedIn B σ3 (.add (.reg 0) (.const relocateControlGap)) := by
    simp [ExprBoundedIn, Expr.eval, relocateControlGap, h03]
    omega
  have hp4 := relocateCtlAssign_programBoundedIn σ3 N B relocateBaseJ
    (.add (.reg 0) (.const relocateControlGap)) h03 he4 hN4
  unfold relocateSetup
  exact ⟨hp1, ⟨hp2, ⟨hp3, hp4⟩⟩⟩

lemma relocateStep_programBoundedIn (τ : Store) (N C t B : ℕ)
    (h0 : τ 0 = N) (hs : τ (N + relocateSrcJ) = 1 + t)
    (hd : τ (N + relocateDstJ) = C + t)
    (hgap : N + relocateControlGap ≤ C) (ht : t < N)
    (hB : C + N ≤ B) :
    ProgramBoundedIn B τ relocateStep := by
  have hB' : N + 8 + N ≤ B := by
    have := hB
    simp [relocateControlGap] at hgap
    omega
  have hN1 : N + relocateSrcJ ≤ B := by simp [relocateSrcJ]; omega
  have hN2 : N + relocateDstJ ≤ B := by simp [relocateDstJ]; omega
  have hs' : τ (N + 1) = 1 + t := by simpa [relocateSrcJ] using hs
  have hd' : τ (N + 2) = C + t := by simpa [relocateDstJ] using hd
  have hgap8 : N + 8 ≤ C := by simp [relocateControlGap] at hgap ⊢; omega
  have heDst : ExprBoundedIn B τ (relocateCtlCell relocateDstJ) := by
    exact relocateCtlCell_exprBoundedIn τ N B relocateDstJ h0 hN2
  have heSrc : ExprBoundedIn B τ (relocateCtlCell relocateSrcJ) := by
    exact relocateCtlCell_exprBoundedIn τ N B relocateSrcJ h0 hN1
  have hp1 : ProgramBoundedIn B τ
      (Program.assignInd (relocateCtlCell relocateDstJ)
        (.regInd (relocateCtlCell relocateSrcJ))) := by
    change ExprBoundedIn B τ (relocateCtlCell relocateDstJ) ∧
      ExprBoundedIn B τ (.regInd (relocateCtlCell relocateSrcJ)) ∧
      (relocateCtlCell relocateDstJ).eval τ ≤ B
    refine ⟨heDst, ⟨heSrc, ?_⟩, ?_⟩
    · simp [relocateCtlCell_eval, relocateSrcJ, h0, hs']
      omega
    · simp [relocateCtlCell_eval, relocateDstJ, h0, hd']
      omega
  let τ1 := (Program.assignInd (relocateCtlCell relocateDstJ)
    (.regInd (relocateCtlCell relocateSrcJ))).eval τ
  have hp1_eval : τ1 = writeReg τ (C + t) (τ (1 + t)) := by
    funext r
    simp [τ1, relocateCtlCell_eval, Expr.eval, h0]
    rw [hd, hs]
  have h01 : τ1 0 = N := by
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) 0 (by omega), h0]
  have hs1 : τ1 (N + relocateSrcJ) = 1 + t := by
    have hne : N + relocateSrcJ ≠ C + t := by simp [relocateSrcJ]; omega
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) (N + relocateSrcJ) hne]
    simpa [relocateSrcJ] using hs
  have hd1 : τ1 (N + relocateDstJ) = C + t := by
    have hne : N + relocateDstJ ≠ C + t := by simp [relocateDstJ]; omega
    rw [hp1_eval, writeReg_diff τ (C + t) (τ (1 + t)) (N + relocateDstJ) hne]
    exact hd
  have heIncSrc : ExprBoundedIn B τ1
      (.add (relocateCtlCell relocateSrcJ) (.const 1)) := by
    refine ⟨relocateCtlCell_exprBoundedIn τ1 N B relocateSrcJ h01 hN1, ?_, ?_⟩
    · simp [ExprBoundedIn]
      omega
    · have hs1' : τ1 (N + 1) = 1 + t := by simpa [relocateSrcJ] using hs1
      simp [relocateCtlCell_eval, relocateSrcJ, Expr.eval, h01, hs1']
      omega
  have hp2 := relocateCtlAssign_programBoundedIn τ1 N B relocateSrcJ
    (.add (relocateCtlCell relocateSrcJ) (.const 1)) h01 heIncSrc hN1
  let τ2 := (relocateCtlAssign relocateSrcJ
    (.add (relocateCtlCell relocateSrcJ) (.const 1))).eval τ1
  have hp2_eval : τ2 (τ1 0 + relocateSrcJ) =
      (Expr.add (relocateCtlCell relocateSrcJ) (.const 1)).eval τ1 := by
    dsimp [τ2]
    exact relocateCtlAssign_eval_same relocateSrcJ
      (Expr.add (relocateCtlCell relocateSrcJ) (.const 1)) τ1
  have h02 : τ2 0 = N := by
    dsimp [τ2]
    have he := relocateCtlAssign_eval_diff relocateSrcJ
      (.add (relocateCtlCell relocateSrcJ) (.const 1)) τ1 0
      (by simp [h01, relocateSrcJ])
    simpa [h01] using he.trans h01
  have hs2 : τ2 (N + relocateSrcJ) = 2 + t := by
    dsimp [τ2]
    rw [show N + relocateSrcJ = τ1 0 + relocateSrcJ by simp [h01, relocateSrcJ]]
    rw [relocateCtlAssign_eval_same relocateSrcJ
      (Expr.add (relocateCtlCell relocateSrcJ) (.const 1)) τ1]
    have hs1' : τ1 (N + 1) = 1 + t := by simpa [relocateSrcJ] using hs1
    simp [relocateCtlCell_eval, relocateSrcJ, Expr.eval, h01, hs1']
    omega
  have hd2 : τ2 (N + relocateDstJ) = C + t := by
    dsimp [τ2]
    have hne : N + relocateDstJ ≠ τ1 0 + relocateSrcJ := by
      simp [h01, relocateSrcJ, relocateDstJ]
    rw [relocateCtlAssign_eval_diff relocateSrcJ
      (Expr.add (relocateCtlCell relocateSrcJ) (.const 1)) τ1 (N + relocateDstJ) hne]
    exact hd1
  have heIncDst : ExprBoundedIn B τ2
      (.add (relocateCtlCell relocateDstJ) (.const 1)) := by
    refine ⟨relocateCtlCell_exprBoundedIn τ2 N B relocateDstJ h02 hN2, ?_, ?_⟩
    · simp [ExprBoundedIn]
      omega
    · have hd2' : τ2 (N + 2) = C + t := by simpa [relocateDstJ] using hd2
      simp [relocateCtlCell_eval, relocateDstJ, h02, hd2', Expr.eval]
      omega
  have hp3 := relocateCtlAssign_programBoundedIn τ2 N B relocateDstJ
    (.add (relocateCtlCell relocateDstJ) (.const 1)) h02 heIncDst hN2
  unfold relocateStep
  exact ⟨hp1, ⟨hp2, hp3⟩⟩

lemma relocateProg_programBoundedIn (σ : Store) (N B : ℕ)
    (h0 : σ 0 = N)
    (hB : N + relocateControlGap + N ≤ B) :
    ProgramBoundedIn B σ relocateProg := by
  have hsetup := relocateSetup_programBoundedIn σ N B h0 hB
  have hbody : ∀ m' < N,
      ProgramBoundedIn B (loopEval relocateStep m' (relocateSetup.eval σ)) relocateStep := by
    intro m' hm'
    have hInv := relocate_loop_invariant σ N h0 m' (by omega)
    exact relocateStep_programBoundedIn _ N (N + relocateControlGap) m' B
      hInv.1 hInv.2.1 hInv.2.2.1 (by omega) hm' hB
  unfold relocateProg
  have hsetup0 : (relocateSetup.eval σ) 0 = N := by
    rw [relocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  have hlen : ExprBoundedIn B (relocateSetup.eval σ)
      (relocateCtlCell relocateLenJ) := by
    have hB' : N + 8 + N ≤ B := by simp [relocateControlGap] at hB ⊢; omega
    exact relocateCtlCell_exprBoundedIn (relocateSetup.eval σ) N B relocateLenJ hsetup0
      (by simp [relocateLenJ]; omega)
  change ProgramBoundedIn B σ relocateSetup ∧
    ProgramBoundedIn B (relocateSetup.eval σ)
      (.forN (relocateCtlCell relocateLenJ) relocateStep)
  have hbound : (relocateCtlCell relocateLenJ).eval (relocateSetup.eval σ) = N := by
    rw [relocateCtlCell_eval, hsetup0, relocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ]
  exact ⟨hsetup, ⟨hlen, by simpa [hbound] using hbody⟩⟩

/-! ## Bit-vector relocation contract -/

def RelocateInput (σ : Store) (bits : Bits) : Prop :=
  σ 0 = bits.length ∧ BitsFrom σ 1 bits

def RelocatePost (σ : Store) (bits : Bits) : Prop :=
  σ 0 = bits.length ∧
  BitsFrom σ (bits.length + relocateControlGap) bits ∧
  σ (bits.length + relocateSrcJ) = bits.length + 1 ∧
  σ (bits.length + relocateDstJ) =
    bits.length + relocateControlGap + bits.length ∧
  σ (bits.length + relocateLenJ) = bits.length ∧
  σ (bits.length + relocateBaseJ) =
    bits.length + relocateControlGap

lemma relocateProg_output (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    ∀ t, t < bits.length →
      (relocateProg.eval σ) (bits.length + relocateControlGap + t) = σ (1 + t) := by
  intro t ht
  have h0 := hin.1
  have hInv := relocate_loop_invariant σ bits.length h0 bits.length le_rfl
  rw [relocateProg_eval_eq_loop σ bits.length h0]
  exact hInv.2.2.2.2.2.1 t ht

lemma relocateProg_final_state (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    (relocateProg.eval σ) 0 = bits.length ∧
    (relocateProg.eval σ) (bits.length + relocateSrcJ) =
      bits.length + 1 ∧
    (relocateProg.eval σ) (bits.length + relocateDstJ) =
      bits.length + relocateControlGap + bits.length ∧
    (relocateProg.eval σ) (bits.length + relocateLenJ) =
      bits.length ∧
    (relocateProg.eval σ) (bits.length + relocateBaseJ) =
      bits.length + relocateControlGap := by
  have hInv := relocate_loop_invariant σ bits.length hin.1 bits.length le_rfl
  rw [relocateProg_eval_eq_loop σ bits.length hin.1]
  exact ⟨hInv.1, by simpa [Nat.add_comm] using hInv.2.1,
    hInv.2.2.1, hInv.2.2.2.1, hInv.2.2.2.2.1⟩

lemma relocateProg_output_bits (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    BitsFrom (relocateProg.eval σ) (bits.length + relocateControlGap) bits := by
  intro i hi
  rw [relocateProg_output σ bits hin i hi]
  exact hin.2 i hi

lemma relocateProg_correct (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    RelocatePost (relocateProg.eval σ) bits := by
  have hs := relocateProg_final_state σ bits hin
  refine ⟨hs.1, relocateProg_output_bits σ bits hin, hs.2.1, hs.2.2.1,
    hs.2.2.2.1, hs.2.2.2.2⟩

end NPComplete.RAMToTM

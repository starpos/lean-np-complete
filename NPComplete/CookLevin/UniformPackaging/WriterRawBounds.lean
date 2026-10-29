module

public import NPComplete.CookLevin.UniformPackaging.Envelopes

/-!
# Raw bounds for writer programs

Low-level writer operations update control cells and the output range, so their
bounds depend on the current values and arena wall. This module proves raw
program bounds for bit, natural-number, literal, and clause appends, forming the
base cases for larger emission proofs.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma programBoundedIn_emitBitProg_const_bounds
    (B M curJ q b : ℕ) (σ : Store)
    (hM : σ 0 = M) (hwall : M + curJ ≤ B) (hcurJ : curJ ≤ B)
    (hwall0 : M + curJ ≠ 0) (hq0 : q ≠ 0) (hq : σ (M + curJ) = q)
    (hb : b + 1 ≤ B) (hq1 : q + 1 ≤ B) :
    ProgramBoundedIn B σ (emitBitProg curJ (.const b)) ∧
      (emitBitProg curJ (.const b)).eval σ 0 = M ∧
      (emitBitProg curJ (.const b)).eval σ (M + curJ) =
        if q = M + curJ then b + 1 else q + 1 := by
  have hv : ExprBoundedIn B σ (.const b) := by
    simp [ExprBoundedIn]
    omega
  have ha : (ctlCell curJ).eval σ ≤ B := by
    rw [ctlCell_eval, hM, hq]
    omega
  have hp : ExprBoundedIn B σ (ctlCell curJ) := by
    simp only [ctlCell, ExprBoundedIn, ctlAddr, Expr.eval]
    rw [hM]
    exact ⟨⟨by omega, hcurJ, hwall⟩, hwall⟩
  have hfirst : ProgramBoundedIn B σ (.assignInd (ctlCell curJ) (.const b)) :=
    ⟨hp, hv, ha⟩
  let σ1 := (Program.assignInd (ctlCell curJ) (.const b)).eval σ
  have hσ1 : σ1 = writeReg σ q b := by
    simp [σ1, eval_assignInd, ctlCell_eval, hM, hq, Expr.eval]
  have hσ10 : σ1 0 = M := by
    rw [hσ1, writeReg_diff σ q b 0 (by omega), hM]
  have hσ1w : σ1 (M + curJ) = if q = M + curJ then b else q := by
    rw [hσ1]
    by_cases h : q = M + curJ
    · simp [h]
    · rw [writeReg_diff σ q b (M + curJ) (Ne.symm h)]
      simp [h, hq]
  have hsecond : ProgramBoundedIn B σ1
      (ctlAssign curJ ((ctlCell curJ).add (.const 1))) := by
    unfold ctlAssign
    simp only [ProgramBoundedIn]
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, hσ10, hσ1w]
    split <;> omega
  have hprog : ProgramBoundedIn B σ (emitBitProg curJ (.const b)) := by
    unfold emitBitProg
    simpa [σ1] using ⟨hfirst, hsecond⟩
  have hctl0 : (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 0 = M := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, hσ10]
    rw [writeReg_diff σ1 (M + curJ) _ 0 (Ne.symm hwall0), hσ10]
  have hctlw : (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 (M + curJ) =
      if q = M + curJ then b + 1 else q + 1 := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, hσ10, writeReg_same]
    simp [Expr.eval, ctlCell_eval, hσ10, hσ1w]
    split <;> rfl
  have hroot : (emitBitProg curJ (.const b)).eval σ 0 = M := by
    unfold emitBitProg
    rw [eval_seq]
    change (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 0 = M
    exact hctl0
  have hcursor : (emitBitProg curJ (.const b)).eval σ (M + curJ) =
      if q = M + curJ then b + 1 else q + 1 := by
    unfold emitBitProg
    rw [eval_seq]
    change (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 (M + curJ) = _
    exact hctlw
  exact ⟨hprog, hroot, hcursor⟩

lemma programBoundedIn_emitBitProg_raw_bounds
    (B M curJ q : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hwall : M + curJ ≤ B) (hcurJ : curJ ≤ B)
    (hwall0 : M + curJ ≠ 0) (hq0 : q ≠ 0) (hq : σ (M + curJ) = q)
    (hv : ExprBoundedIn B σ v) (hval : v.eval σ + 1 ≤ B)
    (hq1 : q + 1 ≤ B) :
    ProgramBoundedIn B σ (emitBitProg curJ v) ∧
      (emitBitProg curJ v).eval σ 0 = M ∧
      (emitBitProg curJ v).eval σ (M + curJ) =
        if q = M + curJ then v.eval σ + 1 else q + 1 := by
  have ha : (ctlCell curJ).eval σ ≤ B := by
    rw [ctlCell_eval, hM, hq]
    omega
  have hp : ExprBoundedIn B σ (ctlCell curJ) := by
    simp only [ctlCell, ExprBoundedIn, ctlAddr, Expr.eval]
    rw [hM]
    exact ⟨⟨by omega, hcurJ, hwall⟩, hwall⟩
  have hfirst : ProgramBoundedIn B σ (.assignInd (ctlCell curJ) v) :=
    ⟨hp, hv, ha⟩
  let σ1 := (Program.assignInd (ctlCell curJ) v).eval σ
  have hσ1 : σ1 = writeReg σ q (v.eval σ) := by
    simp [σ1, eval_assignInd, ctlCell_eval, hM, hq]
  have hσ10 : σ1 0 = M := by
    rw [hσ1, writeReg_diff σ q (v.eval σ) 0 (by omega), hM]
  have hσ1w : σ1 (M + curJ) =
      if q = M + curJ then v.eval σ else q := by
    rw [hσ1]
    by_cases h : q = M + curJ
    · simp [h]
    · rw [writeReg_diff σ q (v.eval σ) (M + curJ) (Ne.symm h)]
      simp [h, hq]
  have hsecond : ProgramBoundedIn B σ1
      (ctlAssign curJ ((ctlCell curJ).add (.const 1))) := by
    unfold ctlAssign
    simp only [ProgramBoundedIn]
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, hσ10, hσ1w]
    split <;> omega
  have hprog : ProgramBoundedIn B σ (emitBitProg curJ v) := by
    unfold emitBitProg
    simpa [σ1] using ⟨hfirst, hsecond⟩
  have hctl0 : (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 0 = M := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, hσ10]
    rw [writeReg_diff σ1 (M + curJ) _ 0 (Ne.symm hwall0), hσ10]
  have hctlw : (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 (M + curJ) =
      if q = M + curJ then v.eval σ + 1 else q + 1 := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, hσ10, writeReg_same]
    simp [Expr.eval, ctlCell_eval, hσ10, hσ1w]
    split <;> rfl
  have hroot : (emitBitProg curJ v).eval σ 0 = M := by
    unfold emitBitProg
    rw [eval_seq]
    change (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 0 = M
    exact hctl0
  have hcursor : (emitBitProg curJ v).eval σ (M + curJ) =
      if q = M + curJ then v.eval σ + 1 else q + 1 := by
    unfold emitBitProg
    rw [eval_seq]
    change (ctlAssign curJ ((ctlCell curJ).add (.const 1))).eval σ1 (M + curJ) = _
    exact hctlw
  exact ⟨hprog, hroot, hcursor⟩

lemma programBoundedIn_emit_zero_loop_body_of_bounds
    (B M curJ cur n : ℕ) (σ : Store)
    (hM : σ 0 = M) (hwall : M + curJ ≤ B) (hcurJ : curJ ≤ B)
    (hwall0 : M + curJ ≠ 0) (hq0 : σ (M + curJ) ≠ 0)
    (hcur : σ (M + curJ) = cur) (hcurN : cur + n + 1 ≤ B) :
    (∀ m < n,
      ProgramBoundedIn B
        (loopEval (emitBitProg curJ (.const 0)) m σ)
        (emitBitProg curJ (.const 0))) ∧
    (∀ m ≤ n,
      (loopEval (emitBitProg curJ (.const 0)) m σ) 0 = M ∧
        (loopEval (emitBitProg curJ (.const 0)) m σ) (M + curJ) ≤ cur + m ∧
        (loopEval (emitBitProg curJ (.const 0)) m σ) (M + curJ) ≠ 0) := by
  have hinv : ∀ m ≤ n,
      (loopEval (emitBitProg curJ (.const 0)) m σ) 0 = M ∧
        (loopEval (emitBitProg curJ (.const 0)) m σ) (M + curJ) ≤ cur + m ∧
        (loopEval (emitBitProg curJ (.const 0)) m σ) (M + curJ) ≠ 0 := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
        exact ⟨hM, by omega, hq0⟩
    | succ m ih =>
        intro hm
        have him := ih (by omega)
        let τ := loopEval (emitBitProg curJ (.const 0)) m σ
        have hq : τ (M + curJ) ≤ cur + m := him.2.1
        have hq1 : τ (M + curJ) + 1 ≤ B := by omega
        have hstep := programBoundedIn_emitBitProg_const_bounds B M curJ
          (τ (M + curJ)) 0 τ him.1 hwall hcurJ hwall0 him.2.2
          rfl (by omega) hq1
        rw [uniform_loopEval_succ_right]
        refine ⟨hstep.2.1, ?_, ?_⟩
        · rw [hstep.2.2]
          split <;> omega
        · rw [hstep.2.2]
          split <;> omega
  refine ⟨?_, hinv⟩
  intro m hm
  have hi := hinv m (by omega)
  exact (programBoundedIn_emitBitProg_const_bounds B M curJ
    ((loopEval (emitBitProg curJ (.const 0)) m σ) (M + curJ)) 0
    (loopEval (emitBitProg curJ (.const 0)) m σ)
    hi.1 hwall hcurJ hwall0 hi.2.2
    rfl (by omega) (by omega)).1

/-- The bounded temporary cell supplies the `forN` count and its iteration bound. -/
lemma programBoundedIn_emitNatProg_for_bounds
    (B M curJ tmpJ n : ℕ) (σ1 : Store)
    (hσ10 : σ1 0 = M) (htmpJ : tmpJ ≤ B) (htmpwall : M + tmpJ ≤ B)
    (hσ1t : σ1 (M + tmpJ) = n)
    (hbody : ∀ m < n,
      ProgramBoundedIn B (loopEval (emitBitProg curJ (.const 0)) m σ1)
        (emitBitProg curJ (.const 0))) :
    ProgramBoundedIn B σ1
      (.forN (.regInd (ctlAddr tmpJ)) (emitBitProg curJ (.const 0))) := by
  simp only [ProgramBoundedIn]
  change ExprBoundedIn B σ1 (ctlCell tmpJ) ∧
    ∀ m < (ctlCell tmpJ).eval σ1,
      ProgramBoundedIn B (loopEval (emitBitProg curJ (.const 0)) m σ1)
        (emitBitProg curJ (.const 0))
  have ht : ExprBoundedIn B σ1 (ctlCell tmpJ) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval]
    rw [hσ10]
    exact ⟨⟨by omega, htmpJ, htmpwall⟩, htmpwall⟩
  refine ⟨ht, ?_⟩
  intro m hm
  rw [ctlCell_eval, hσ10, hσ1t] at hm
  exact hbody m hm

lemma programBoundedIn_emitNatProg_of_bounds
    (B M curJ tmpJ cur n : ℕ) (e : Expr) (σ : Store)
    (hM : σ 0 = M) (hwall : M + curJ ≤ B) (htmpwall : M + tmpJ ≤ B)
    (hcurJ : curJ ≤ B) (htmpJ : tmpJ ≤ B) (htmpPos : 1 ≤ tmpJ)
    (htmpNe : tmpJ ≠ curJ) (hwall0 : M + curJ ≠ 0)
    (hcur0 : σ (M + curJ) ≠ 0) (hcur : σ (M + curJ) = cur)
    (hcurN : cur + n + 1 ≤ B)
    (he : ExprBoundedIn B σ e) (hen : e.eval σ = n) :
    ProgramBoundedIn B σ (emitNatProg curJ tmpJ e) ∧
      (emitNatProg curJ tmpJ e).eval σ 0 = M ∧
      (emitNatProg curJ tmpJ e).eval σ (M + curJ) ≤ cur + n + 1 ∧
      (emitNatProg curJ tmpJ e).eval σ (M + curJ) ≠ 0 := by
  have hassign : ProgramBoundedIn B σ (ctlAssign tmpJ e) := by
    unfold ctlAssign
    simp only [ProgramBoundedIn]
    have ha : ExprBoundedIn B σ (ctlAddr tmpJ) := by
      simp only [ctlAddr, ExprBoundedIn, Expr.eval]
      rw [hM]
      exact ⟨by omega, htmpJ, htmpwall⟩
    exact ⟨ha, he, by simpa [ctlAddr, Expr.eval, hM] using htmpwall⟩
  let σ1 := (ctlAssign tmpJ e).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    rw [ctlAssign, eval_assignInd, ctlAddr_eval, hM]
    rw [writeReg_diff σ (M + tmpJ) _ 0 (by omega), hM]
  have hσ1c : σ1 (M + curJ) = cur := by
    dsimp [σ1]
    rw [ctlAssign, eval_assignInd, ctlAddr_eval, hM]
    rw [writeReg_diff σ (M + tmpJ) _ (M + curJ) (by omega), hcur]
  have hσ1t : σ1 (M + tmpJ) = n := by
    dsimp [σ1]
    rw [ctlAssign, eval_assignInd, ctlAddr_eval, hM, writeReg_same]
    exact hen
  have hcurVal0 : cur ≠ 0 := by
    intro h
    apply hcur0
    rw [hcur, h]
  have hbody : ∀ m < n,
      ProgramBoundedIn B (loopEval (emitBitProg curJ (.const 0)) m σ1)
        (emitBitProg curJ (.const 0)) := by
    intro m hm
    exact (programBoundedIn_emit_zero_loop_body_of_bounds B M curJ cur n σ1
      hσ10 hwall hcurJ hwall0 (by simpa [hσ1c] using hcurVal0) hσ1c hcurN).1 m hm
  have hfor := programBoundedIn_emitNatProg_for_bounds B M curJ tmpJ n σ1
    hσ10 htmpJ htmpwall hσ1t hbody
  have hloop : (Program.forN (.regInd (ctlAddr tmpJ))
      (emitBitProg curJ (.const 0))).eval σ1 =
      loopEval (emitBitProg curJ (.const 0)) n σ1 := by
    rw [eval_forN]
    have htval : (Expr.regInd (ctlAddr tmpJ)).eval σ1 = n := by
      simp [Expr.eval, ctlAddr, hσ10, hσ1t]
    rw [htval]
  have hinv :
      (loopEval (emitBitProg curJ (.const 0)) n σ1) 0 = M ∧
        (loopEval (emitBitProg curJ (.const 0)) n σ1) (M + curJ) ≤ cur + n ∧
        (loopEval (emitBitProg curJ (.const 0)) n σ1) (M + curJ) ≠ 0 := by
    exact (programBoundedIn_emit_zero_loop_body_of_bounds B M curJ cur n σ1
      hσ10 hwall hcurJ hwall0 (by simpa [hσ1c] using hcurVal0) hσ1c hcurN).2 n
      le_rfl
  have hlast := programBoundedIn_emitBitProg_const_bounds B M curJ
    ((loopEval (emitBitProg curJ (.const 0)) n σ1) (M + curJ)) 1
    (loopEval (emitBitProg curJ (.const 0)) n σ1)
    hinv.1 hwall hcurJ hwall0 hinv.2.2 rfl
    (by omega) (by omega)
  have hlast' : ProgramBoundedIn B
      ((Program.forN (.regInd (ctlAddr tmpJ))
        (emitBitProg curJ (.const 0))).eval σ1)
      (emitBitProg curJ (.const 1)) := by
    rw [hloop]
    exact hlast.1
  have hprog : ProgramBoundedIn B σ (emitNatProg curJ tmpJ e) := by
    unfold emitNatProg
    simpa [σ1] using ⟨hassign, ⟨hfor, hlast'⟩⟩
  have hroot : (emitNatProg curJ tmpJ e).eval σ 0 = M := by
    unfold emitNatProg
    rw [eval_seq, eval_seq]
    change (emitBitProg curJ (.const 1)).eval
      ((Program.forN (.regInd (ctlAddr tmpJ))
        (emitBitProg curJ (.const 0))).eval σ1) 0 = M
    rw [hloop]
    exact hlast.2.1
  have hcursor : (emitNatProg curJ tmpJ e).eval σ (M + curJ) ≤ cur + n + 1 := by
    unfold emitNatProg
    rw [eval_seq, eval_seq]
    change (emitBitProg curJ (.const 1)).eval
      ((Program.forN (.regInd (ctlAddr tmpJ))
        (emitBitProg curJ (.const 0))).eval σ1) (M + curJ) ≤ cur + n + 1
    rw [hloop]
    rw [hlast.2.2]
    split <;> omega
  have hcursor0 : (emitNatProg curJ tmpJ e).eval σ (M + curJ) ≠ 0 := by
    unfold emitNatProg
    rw [eval_seq, eval_seq]
    change (emitBitProg curJ (.const 1)).eval
      ((Program.forN (.regInd (ctlAddr tmpJ))
        (emitBitProg curJ (.const 0))).eval σ1) (M + curJ) ≠ 0
    rw [hloop]
    rw [hlast.2.2]
    split <;> omega
  exact ⟨hprog, hroot, hcursor, hcursor0⟩

lemma programBoundedIn_writerAppendLiteralProg_raw_bounds
    (B M curJ tmpJ q q' pol val' polReg varReg : ℕ) (σ : Store)
    (hM : σ 0 = M) (hwall : M + curJ ≤ B) (htmpwall : M + tmpJ ≤ B)
    (hcurJ : curJ ≤ B) (htmpJ : tmpJ ≤ B) (htmpPos : 1 ≤ tmpJ)
    (htmpNe : tmpJ ≠ curJ) (hwall0 : M + curJ ≠ 0)
    (hq0 : q ≠ 0) (hq : σ (M + curJ) = q)
    (hpolReg : polReg ≤ B) (hvarReg : varReg ≤ B)
    (hpol : σ polReg = pol)
    (hpol1 : pol + 1 ≤ B) (hq1 : q + 1 ≤ B)
    (hbit : q' = if q = M + curJ then pol + 1 else q + 1)
    (hvarAfter : (emitBitProg curJ (.reg polReg)).eval σ varReg = val')
    (hval1 : q' + val' + 1 ≤ B)
    (hq'0 : q' ≠ 0) :
    ProgramBoundedIn B σ (writerAppendLiteralProg curJ tmpJ polReg varReg) ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ 0 = M ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + curJ) ≤
        q' + val' + 1 ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + curJ) ≠ 0 := by
  have hpolE : ExprBoundedIn B σ (.reg polReg) := by
    simp only [ExprBoundedIn]
    exact hpolReg
  have hbitp := programBoundedIn_emitBitProg_raw_bounds B M curJ q
    (.reg polReg) σ hM hwall hcurJ hwall0 hq0 hq hpolE
    (by simpa [Expr.eval, hpol] using hpol1)
    (by simpa [Expr.eval, hpol] using hq1)
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  have hσ1q : σ1 (M + curJ) = q' := by
    simpa [σ1, Expr.eval, hpol, hbit]
      using hbitp.2.2
  have hσ1var : σ1 varReg = val' := hvarAfter
  have hvarE : ExprBoundedIn B σ1 (.reg varReg) := by
    simp only [ExprBoundedIn]
    exact hvarReg
  have hnat := programBoundedIn_emitNatProg_of_bounds B M curJ tmpJ q' val'
    (.reg varReg) σ1 hbitp.2.1 hwall htmpwall hcurJ htmpJ htmpPos htmpNe hwall0
    (by rw [hσ1q]; exact hq'0) hσ1q hval1 hvarE
       (by simp [Expr.eval, hσ1var])
  have hprog : ProgramBoundedIn B σ
      (writerAppendLiteralProg curJ tmpJ polReg varReg) := by
    unfold writerAppendLiteralProg
    simpa [σ1] using ⟨hbitp.1, hnat.1⟩
  have hroot : (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ 0 = M := by
    unfold writerAppendLiteralProg
    rw [eval_seq]
    change (emitNatProg curJ tmpJ (.reg varReg)).eval σ1 0 = M
    exact hnat.2.1
  have hcursor : (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ
      (M + curJ) ≤ q' + val' + 1 := by
    unfold writerAppendLiteralProg
    rw [eval_seq]
    change (emitNatProg curJ tmpJ (.reg varReg)).eval σ1 (M + curJ) ≤ _
    exact hnat.2.2.1
  have hcursor0 : (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ
      (M + curJ) ≠ 0 := by
    unfold writerAppendLiteralProg
    rw [eval_seq]
    change (emitNatProg curJ tmpJ (.reg varReg)).eval σ1 (M + curJ) ≠ 0
    exact hnat.2.2.2
  exact ⟨hprog, hroot, hcursor, hcursor0⟩

lemma program_eval_storeValuesLe {B : ℕ} (σ : Store) (p : Program)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ)
    (hp : ProgramBoundedIn B σ p) (hsf : ScanFree p) :
    StoreValuesLe B (p.eval σ) := by
  induction p generalizing σ with
  | skip => simpa using hσ
  | assign r e =>
      obtain ⟨hr, he⟩ := hp
      intro i
      simp [eval_assign, writeReg]
      split_ifs with hi
      · subst i
        exact expr_eval_le_of_bounded_in hσ hB1 e he
      · exact hσ i
  | assignInd eA eV =>
      obtain ⟨heA, heV, heAval⟩ := hp
      have hv := expr_eval_le_of_bounded_in hσ hB1 eV heV
      intro i
      simp [eval_assignInd, writeReg]
      split_ifs with hi
      · exact hv
      · exact hσ i
  | seq p1 p2 ih1 ih2 =>
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hsf1, hsf2⟩ := hsf
      rw [eval_seq]
      exact ih2 (p1.eval σ) (ih1 σ hσ hp1 hsf1) hp2 hsf2
  | ifNZ e t f iht ihf =>
      obtain ⟨he, hpt, hpf⟩ := hp
      obtain ⟨hsft, hsff⟩ := hsf
      by_cases hz : e.eval σ ≠ 0
      · rw [eval_ifNZ, ite_eq_left hz]
        exact iht σ hσ hpt hsft
      · rw [eval_ifNZ, ite_eq_right hz]
        exact ihf σ hσ hpf hsff
  | forN n body ihbody =>
      obtain ⟨hn, hbody⟩ := hp
      have hloop : ∀ k, k ≤ n.eval σ → StoreValuesLe B (loopEval body k σ) := by
        intro k
        induction k with
        | zero => intro _; simpa using hσ
        | succ k ihk =>
            intro hk
            rw [uniform_loopEval_succ_right]
            exact ihbody (loopEval body k σ) (ihk (by omega))
              (hbody k (by omega)) hsf
      rw [eval_forN]
      exact hloop (n.eval σ) le_rfl
  | scanList _ _ _ _ => cases hsf
  | lookup _ _ _ => cases hsf

lemma storeValuesLe_assign {B : ℕ} {σ : Store} {r : ℕ} {e : Expr}
    (hσ : StoreValuesLe B σ) (hv : e.eval σ ≤ B) :
    StoreValuesLe B ((Program.assign r e).eval σ) := by
  intro i
  rw [eval_assign]
  by_cases hi : i = r
  · rw [hi, writeReg_same]
    exact hv
  · rw [writeReg_diff _ _ _ _ hi]
    exact hσ i

lemma programBoundedIn_writerAppendLiteralProg_raw_post_bounds
    (K B M curJ tmpJ polReg varReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hlayout : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K ∧
      polReg ≤ K ∧ varReg ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hstep : 3 * K + 3 ≤ B) :
    ProgramBoundedIn B σ (writerAppendLiteralProg curJ tmpJ polReg varReg) ∧
      StoreValuesLe B
        ((writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ) ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ 0 = M ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + curJ) ≤ B ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + tmpJ) ≤ B ∧
      (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + curJ) ≠ 0 := by
  rcases hlayout with ⟨hwallK, htmpwallK, hcurJK, htmpJK, hpolRegK, hvarRegK⟩
  let q := σ (M + curJ)
  let pol := σ polReg
  let q' := if q = M + curJ then pol + 1 else q + 1
  have hqK : q ≤ K := by
    dsimp [q]
    exact hσ (M + curJ)
  have hpolK : pol ≤ K := by
    dsimp [pol]
    exact hσ polReg
  have hK1 : 1 ≤ K + 1 := by omega
  have hwall0 : M + curJ ≠ 0 := by omega
  have hbit := programBoundedIn_emitBitProg_raw_bounds (K + 1) M curJ q
    (.reg polReg) σ hM (by omega) (by omega) hwall0 hq0 (by rfl)
    (by simp only [ExprBoundedIn]; omega)
    (by simp only [Expr.eval]; omega) (by omega)
  have hσK1 : StoreValuesLe (K + 1) σ := by
    intro i
    exact (hσ i).trans (by omega)
  have hbitStore : StoreValuesLe (K + 1)
      ((emitBitProg curJ (.reg polReg)).eval σ) :=
    program_eval_storeValuesLe σ (emitBitProg curJ (.reg polReg)) hK1 hσK1
      hbit.1 (scanFree_emitBitProg curJ (.reg polReg))
  have hval' : (emitBitProg curJ (.reg polReg)).eval σ varReg ≤ K + 1 :=
    hbitStore varReg
  have hq'le : q' ≤ 2 * K + 1 := by
    dsimp [q']
    split <;> omega
  have hq'0 : q' ≠ 0 := by
    dsimp [q']
    split <;> omega
  have hlit := programBoundedIn_writerAppendLiteralProg_raw_bounds
    B M curJ tmpJ q q' pol
      ((emitBitProg curJ (.reg polReg)).eval σ varReg) polReg varReg σ hM
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hwall0 hq0 (by rfl) (by omega) (by omega) (by rfl)
    (by omega) (by omega) (by simp [q']) (by rfl) (by omega) hq'0
  have hσB : StoreValuesLe B σ := by
    intro i
    exact (hσ i).trans (by omega)
  have hstore : StoreValuesLe B
      ((writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ) :=
    program_eval_storeValuesLe σ (writerAppendLiteralProg curJ tmpJ polReg varReg)
      (by omega) hσB hlit.1 (scanFree_writerAppendLiteralProg curJ tmpJ polReg varReg)
  exact ⟨hlit.1, hstore, hlit.2.1, hlit.2.2.1.trans (by omega),
    hstore (M + tmpJ), hlit.2.2.2⟩

lemma programBoundedIn_writerAppendThreeRegsProg_raw_bounds
    (K B M curJ tmpJ p1 v1 p2 v2 p3 v3 : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : p1 ≤ K ∧ v1 ≤ K ∧ p2 ≤ K ∧ v2 ≤ K ∧ p3 ≤ K ∧ v3 ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : 3 * (3 * (3 * K + 3) + 3) + 3 ≤ B) :
    ProgramBoundedIn B σ
        (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3) ∧
      StoreValuesLe B
        ((writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ) ∧
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ 0 = M ∧
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ
          (M + curJ) ≤ B ∧
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ
          (M + curJ) ≠ 0 := by
  let K1 := 3 * K + 3
  let K2 := 3 * K1 + 3
  let K3 := 3 * K2 + 3
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hp1t := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K K1
    M curJ tmpJ p1 v1 σ hcurJ1 htmpJlt
    ⟨hstatic.1, hstatic.2.1, hstatic.2.2.1, hstatic.2.2.2, hidx.1, hidx.2.1⟩
    hσ hM hq0 (by dsimp [K1]; omega)
  have hσ1 : StoreValuesLe K1 σ1 := by
    simpa [σ1] using hp1t.2.1
  have hM1 : σ1 0 = M := by
    simpa [σ1] using hp1t.2.2.1
  have hq1 : σ1 (M + curJ) ≠ 0 := by
    simpa [σ1] using hp1t.2.2.2.2.2
  have hp1 := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K B
    M curJ tmpJ p1 v1 σ hcurJ1 htmpJlt (by omega) hσ hM hq0 (by omega)
  have hp2t := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K1 K2
    M curJ tmpJ p2 v2 σ1 hcurJ1 htmpJlt (by omega) hσ1 hM1 hq1
    (by dsimp [K1, K2]; omega)
  have hσ2 : StoreValuesLe K2 σ2 := by
    simpa [σ2] using hp2t.2.1
  have hM2 : σ2 0 = M := by
    simpa [σ2] using hp2t.2.2.1
  have hq2 : σ2 (M + curJ) ≠ 0 := by
    simpa [σ2] using hp2t.2.2.2.2.2
  have hp2 := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K1 B
    M curJ tmpJ p2 v2 σ1 hcurJ1 htmpJlt (by omega) hσ1 hM1 hq1 (by omega)
  have hp3t := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K2 K3
    M curJ tmpJ p3 v3 σ2 hcurJ1 htmpJlt (by omega) hσ2 hM2 hq2
    (by dsimp [K2, K3]; omega)
  have hp3 := programBoundedIn_writerAppendLiteralProg_raw_post_bounds K2 B
    M curJ tmpJ p3 v3 σ2 hcurJ1 htmpJlt (by omega) hσ2 hM2 hq2 (by omega)
  have hprog : ProgramBoundedIn B σ
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3) := by
    simp only [writerAppendThreeRegsProg, ProgramBoundedIn]
    exact ⟨hp1.1, ⟨hp2.1, hp3.1⟩⟩
  have hstore : StoreValuesLe B
      ((writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ) := by
    intro i
    simpa [writerAppendThreeRegsProg, σ1, σ2, eval_seq] using
      (hp3t.2.1 i).trans (by omega)
  have hroot :
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ 0 = M := by
    simpa [writerAppendThreeRegsProg, σ1, σ2, eval_seq] using hp3t.2.2.1
  have hcursor :
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ
        (M + curJ) ≤ B := by
    simpa [writerAppendThreeRegsProg, σ1, σ2, eval_seq] using
      hp3t.2.2.2.1.trans (by omega)
  have hcursor0 :
      (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ
        (M + curJ) ≠ 0 := by
    simpa [writerAppendThreeRegsProg, σ1, σ2, eval_seq] using hp3t.2.2.2.2.2
  exact ⟨hprog, hstore, hroot, hcursor, hcursor0⟩

lemma programBoundedIn_writerAppendClauseOneProg_raw_bounds
    (K B M curJ tmpJ polReg varReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : polReg ≤ K ∧ varReg ≤ K) (hσ : StoreValuesLe K σ)
    (hM : σ 0 = M) (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawThreeBound K ≤ B) :
    ProgramBoundedIn B σ (writerAppendClauseOneProg curJ tmpJ polReg varReg) := by
  have hbudget' : 3 * (3 * (3 * K + 3) + 3) + 3 ≤ B := by
    simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget
  simpa [writerAppendClauseOneProg] using
    (programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
      polReg varReg polReg varReg polReg varReg σ hcurJ1 htmpJlt hstatic
      ⟨hidx.1, hidx.2, hidx.1, hidx.2, hidx.1, hidx.2⟩ hσ hM hq0 hbudget').1

lemma programBoundedIn_writerAppendClauseTwoProg_raw_bounds
    (K B M curJ tmpJ p1 v1 p2 v2 : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : p1 ≤ K ∧ v1 ≤ K ∧ p2 ≤ K ∧ v2 ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawThreeBound K ≤ B) :
    ProgramBoundedIn B σ (writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2) := by
  have hbudget' : 3 * (3 * (3 * K + 3) + 3) + 3 ≤ B := by
    simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget
  simpa [writerAppendClauseTwoProg] using
    (programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
      p1 v1 p2 v2 p2 v2 σ hcurJ1 htmpJlt hstatic
      ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2, hidx.2.2.1, hidx.2.2.2⟩
      hσ hM hq0 hbudget').1

lemma programBoundedIn_writer_append_two_triples_prog_raw_bounds
    (K B M curJ tmpJ p1 v1 p2 v2 p3 v3
      q1 w1 q2 w2 q3 w3 : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : p1 ≤ K ∧ v1 ≤ K ∧ p2 ≤ K ∧ v2 ≤ K ∧ p3 ≤ K ∧ v3 ≤ K ∧
      q1 ≤ K ∧ w1 ≤ K ∧ q2 ≤ K ∧ w2 ≤ K ∧ q3 ≤ K ∧ w3 ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawSixBound K ≤ B) :
    ProgramBoundedIn B σ
      (.seq (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3)
        (writerAppendThreeRegsProg curJ tmpJ q1 w1 q2 w2 q3 w3)) := by
  rcases hidx with ⟨hp1, hv1, hp2, hv2, hp3, hv3, hq1B, hw1B, hq2B, hw2B, hq3B,
    hw3B⟩
  let K3 := writerAppendRawThreeBound K
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ
  have hfirstT := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K K3
    M curJ tmpJ p1 v1 p2 v2 p3 v3 σ hcurJ1 htmpJlt hstatic
    ⟨hp1, hv1, hp2, hv2, hp3, hv3⟩
    hσ hM hq0 (by dsimp [K3, writerAppendRawThreeBound, writerAppendRawStepBound]; omega)
  have hσ1 : StoreValuesLe K3 σ1 := by
    simpa [σ1] using hfirstT.2.1
  have hM1 : σ1 0 = M := by
    simpa [σ1] using hfirstT.2.2.1
  have hq1 : σ1 (M + curJ) ≠ 0 := by
    simpa [σ1] using hfirstT.2.2.2.2
  have hbudget3 : writerAppendRawThreeBound K ≤ B := by
    simp [writerAppendRawSixBound, writerAppendRawThreeBound,
      writerAppendRawStepBound] at hbudget ⊢
    omega
  have hfirst := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B
    M curJ tmpJ p1 v1 p2 v2 p3 v3 σ hcurJ1 htmpJlt hstatic
    ⟨hp1, hv1, hp2, hv2, hp3, hv3⟩ hσ hM hq0
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget3)
  have hbudgetK3 : writerAppendRawThreeBound K3 ≤ B := by
    simpa [K3, writerAppendRawSixBound] using hbudget
  have hK3 : K ≤ K3 := by
    dsimp [K3, writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hstatic3 : M + curJ ≤ K3 ∧ M + tmpJ ≤ K3 ∧ curJ ≤ K3 ∧ tmpJ ≤ K3 := by
    exact ⟨hstatic.1.trans hK3, hstatic.2.1.trans hK3,
      hstatic.2.2.1.trans hK3, hstatic.2.2.2.trans hK3⟩
  have hidx3 : q1 ≤ K3 ∧ w1 ≤ K3 ∧ q2 ≤ K3 ∧ w2 ≤ K3 ∧ q3 ≤ K3 ∧ w3 ≤ K3 := by
    exact ⟨hq1B.trans hK3, hw1B.trans hK3, hq2B.trans hK3,
      hw2B.trans hK3, hq3B.trans hK3, hw3B.trans hK3⟩
  have hsecond := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K3 B
    M curJ tmpJ q1 w1 q2 w2 q3 w3 σ1 hcurJ1 htmpJlt hstatic3 hidx3 hσ1 hM1 hq1
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudgetK3)
  simpa [σ1] using ⟨hfirst.1, hsecond.1⟩

lemma programBoundedIn_writerAppendClauseThreeProg_raw_bounds
    (K B M curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ)
    (σ : Store) (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : p1 ≤ K ∧ v1 ≤ K ∧ p2 ≤ K ∧ v2 ≤ K ∧ p3 ≤ K ∧ v3 ≤ K ∧
      posPolReg ≤ K ∧ negPolReg ≤ K ∧ freshReg ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawSixBound K ≤ B) :
    ProgramBoundedIn B σ
      (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg
        negPolReg freshReg) := by
  rcases hidx with ⟨hp1, hv1, hp2, hv2, hp3, hv3, hpos, hneg, hfresh⟩
  simpa [writerAppendClauseThreeProg] using
    programBoundedIn_writer_append_two_triples_prog_raw_bounds K B M curJ tmpJ
      p1 v1 p2 v2 posPolReg freshReg negPolReg freshReg p3 v3 p3 v3 σ
      hcurJ1 htmpJlt hstatic
      ⟨hp1, hv1, hp2, hv2, hpos, hfresh, hneg, hfresh, hp3, hv3, hp3, hv3⟩
      hσ hM hq0 hbudget

lemma programBoundedIn_writerAppendClauseEmptyProg_raw_bounds
    (K B M curJ tmpJ posPolReg negPolReg freshReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : posPolReg ≤ K ∧ negPolReg ≤ K ∧ freshReg ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawSixBound K ≤ B) :
    ProgramBoundedIn B σ
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg) := by
  rcases hidx with ⟨hpos, hneg, hfresh⟩
  simpa [writerAppendClauseEmptyProg] using
    programBoundedIn_writer_append_two_triples_prog_raw_bounds K B M curJ tmpJ
      posPolReg freshReg posPolReg freshReg posPolReg freshReg
      negPolReg freshReg negPolReg freshReg negPolReg freshReg σ
      hcurJ1 htmpJlt hstatic
      ⟨hpos, hfresh, hpos, hfresh, hpos, hfresh,
        hneg, hfresh, hneg, hfresh, hneg, hfresh⟩
      hσ hM hq0 hbudget

lemma programBoundedIn_writerAppendSplitTailLinkDynamicProg_raw_bounds
    (K B M curJ tmpJ carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ)
    (σ : Store) (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : carryPolReg ≤ K ∧ carryValReg ≤ K ∧ polReg ≤ K ∧ valReg ≤ K ∧
      posPolReg ≤ K ∧ freshReg ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hcarryVal0 : carryValReg ≠ 0) (hfresh0 : freshReg ≠ 0)
    (hcarryValCursor : carryValReg ≠ M + curJ)
    (hfreshCursor : freshReg ≠ M + curJ)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg) ∧
      StoreValuesLe B
        ((writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
          valReg posPolReg freshReg).eval σ) ∧
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ 0 = M ∧
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ (M + curJ) ≤ B ∧
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ carryValReg ≤ B ∧
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ freshReg ≤ B ∧
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ (M + curJ) ≠ 0 := by
  rcases hidx with ⟨hcp, hcv, hp, hv, hpp, hfresh⟩
  let K3 := writerAppendRawThreeBound K
  let σw := (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg polReg valReg
    posPolReg freshReg).eval σ
  have htripleT := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K K3
    M curJ tmpJ carryPolReg carryValReg polReg valReg posPolReg freshReg σ hcurJ1 htmpJlt
    hstatic ⟨hcp, hcv, hp, hv, hpp, hfresh⟩ hσ hM hq0
    (by dsimp [K3, writerAppendRawThreeBound, writerAppendRawStepBound]; omega)
  have hσw : StoreValuesLe K3 σw := by
    simpa [σw] using htripleT.2.1
  have hK3B : K3 + 1 ≤ B := by
    dsimp [K3]
    simpa [writerAppendRawThreeBound] using hbudget
  have hK3 : K ≤ K3 := by
    dsimp [K3, writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have htripleB := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B
    M curJ tmpJ carryPolReg carryValReg polReg valReg posPolReg freshReg σ hcurJ1 htmpJlt
    (by omega) (by omega) hσ hM hq0
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using
      (show writerAppendRawThreeBound K ≤ B by omega))
  let σ2 := (Program.assign carryValReg (.reg freshReg)).eval σw
  have hfresh2 : σ2 freshReg = σw freshReg := by
    simp [σ2, eval_assign, Expr.eval, writeReg]
  have hcassign : ProgramBoundedIn B σw
      (.assign carryValReg (.reg freshReg)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    exact ⟨by omega, by omega⟩
  have hfreshBound : σw freshReg ≤ K3 := hσw freshReg
  have hadd : ProgramBoundedIn B σ2
      (.assign freshReg (.add (.reg freshReg) (.const 1))) := by
    simp [ProgramBoundedIn, ExprBoundedIn, Expr.eval, hfresh2]
    exact ⟨by omega, by omega⟩
  have hprog : ProgramBoundedIn B σ
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg) := by
    simpa [writerAppendSplitTailLinkDynamicProg, σw, σ2] using
      ⟨htripleB.1, ⟨hcassign, hadd⟩⟩
  have hσB : StoreValuesLe B σ := fun i => (hσ i).trans (by omega)
  have hstore : StoreValuesLe B
      ((writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ) :=
    program_eval_storeValuesLe σ _ (by omega) hσB hprog
      (scanFree_writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg
        polReg valReg posPolReg freshReg)
  have hσ2root : σ2 0 = M := by
    simp [σ2, eval_assign, Expr.eval,
      writeReg_diff σw carryValReg _ 0 (Ne.symm hcarryVal0)]
    exact (by simpa [σw] using htripleB.2.2.1)
  have hσ2cursor : σ2 (M + curJ) = σw (M + curJ) := by
    simp [σ2, eval_assign, Expr.eval,
      writeReg_diff σw carryValReg _ (M + curJ) (Ne.symm hcarryValCursor)]
  let σ3 := (Program.assign freshReg (.add (.reg freshReg) (.const 1))).eval σ2
  have hσ3root : σ3 0 = M := by
    simp [σ3, eval_assign, Expr.eval,
      writeReg_diff σ2 freshReg _ 0 (Ne.symm hfresh0), hσ2root]
  have hσ3cursor : σ3 (M + curJ) = σ2 (M + curJ) := by
    simp [σ3, eval_assign, Expr.eval,
      writeReg_diff σ2 freshReg _ (M + curJ) (Ne.symm hfreshCursor)]
  have hroot :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ 0 = M := by
    rw [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_seq]
    change (Program.assign freshReg (.add (.reg freshReg) (.const 1))).eval σ2 0 = M
    exact hσ3root
  have hcursor :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ (M + curJ) ≤ B := by
    have h := htripleB.2.2.2.1
    rw [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_seq]
    change (Program.assign freshReg (.add (.reg freshReg) (.const 1))).eval σ2
      (M + curJ) ≤ B
    change σ3 (M + curJ) ≤ B
    rw [hσ3cursor, hσ2cursor]
    exact h.trans (by omega)
  have hcursor0 :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
        valReg posPolReg freshReg).eval σ (M + curJ) ≠ 0 := by
    rw [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_seq]
    change (Program.assign freshReg (.add (.reg freshReg) (.const 1))).eval σ2
      (M + curJ) ≠ 0
    change σ3 (M + curJ) ≠ 0
    rw [hσ3cursor, hσ2cursor]
    exact htripleB.2.2.2.2
  exact ⟨hprog, hstore, hroot, hcursor, hstore carryValReg, hstore freshReg,
    hcursor0⟩

end NPComplete.CookLevin

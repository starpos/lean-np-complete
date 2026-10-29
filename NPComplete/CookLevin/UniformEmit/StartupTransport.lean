module

public import NPComplete.CookLevin.UniformEmit.ClauseTransport
public import NPComplete.BoundedWhile.Frame

/-!
# Startup program transport

Startup programs depend on a runtime output bound and a start expression that must remain stable
during evaluation. This module transports those symbolic bounds into concrete program evaluations,
connecting startup-state facts to the assembled code.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF)


/-! ## Startup under a bound-stable start expression -/

lemma secondPassRewindProgramAt_avoids_frame
    (cursorReg inputBaseReg outerReg doneReg boundReg : ℕ) :
    (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ outerReg ∧ r ≠ doneReg) := by
  simp [Program.Avoids, secondPassRewindProgramAt, decodeNatProgramAt,
    decodeUnaryProgAt, decodeUnaryStep]

lemma secondPassRewindProgramAt_frame
    (cursorReg inputBaseReg outerReg doneReg boundReg r : ℕ) (σ : Store)
    (hrc : r ≠ cursorReg) (hro : r ≠ outerReg) (hrd : r ≠ doneReg) :
    (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ r =
      σ r := by
  exact (secondPassRewindProgramAt_avoids_frame cursorReg inputBaseReg outerReg doneReg
    boundReg).eval_frame σ ⟨hrc, hro, hrd⟩

lemma secondPassRewindProgramAt_bound_frame
    (cursorReg inputBaseReg outerReg doneReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbo : boundReg ≠ outerReg) :
    (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ
      boundReg = σ boundReg :=
  secondPassRewindProgramAt_frame cursorReg inputBaseReg outerReg doneReg boundReg
    boundReg σ hbc hbo hbd

lemma secondPassStartupProgramAt_eq_of_bound_expr
    (cursorReg inputBaseReg outerReg doneReg boundReg bound curJ tmpJ start : ℕ)
    (startE : Expr) (numVarsReg clauseCountReg : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hstartE : ∀ τ : Store, τ boundReg = bound → startE.eval τ = start)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbo : boundReg ≠ outerReg) :
    (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ
      startE numVarsReg clauseCountReg).eval σ =
      (secondPassStartupProgram cursorReg inputBaseReg outerReg doneReg bound curJ tmpJ start
        numVarsReg clauseCountReg).eval σ := by
  have hstart : startE.eval
      ((secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ) =
      start := by
    apply hstartE
    exact (secondPassRewindProgramAt_bound_frame cursorReg inputBaseReg outerReg doneReg
      boundReg σ hbc hbd hbo).trans hb
  exact secondPassStartupProgramAt_eq cursorReg inputBaseReg outerReg doneReg boundReg bound
    curJ tmpJ start startE numVarsReg clauseCountReg σ hb hbc hbd hbo hstart

lemma secondPassStartupProgramAt_eq_uniformStartE
    (cursorReg inputBaseReg outerReg doneReg N curJ tmpJ : ℕ)
    (numVarsReg clauseCountReg : ℕ) (σ : Store)
    (hb : σ uctSavedBoundReg = N)
    (hbc : uctSavedBoundReg ≠ cursorReg) (hbd : uctSavedBoundReg ≠ doneReg)
    (hbo : uctSavedBoundReg ≠ outerReg) :
    (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg uctSavedBoundReg
      curJ tmpJ uniformStartE numVarsReg clauseCountReg).eval σ =
      (secondPassStartupProgram cursorReg inputBaseReg outerReg doneReg N curJ tmpJ
        uniformStartNat numVarsReg clauseCountReg).eval σ :=
  secondPassStartupProgramAt_eq_of_bound_expr cursorReg inputBaseReg outerReg doneReg
    uctSavedBoundReg N curJ tmpJ uniformStartNat uniformStartE
    numVarsReg clauseCountReg σ hb
    (fun _ _ => uniformStartE_eval _) hbc hbd hbo

lemma secondPassStartupProgramAt_bound_frame
    (cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ M start : ℕ)
    (startE : Expr) (numVarsReg clauseCountReg numVars clauseCount : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbo : boundReg ≠ outerReg)
    (h0c : 0 ≠ cursorReg) (h0o : 0 ≠ outerReg) (h0d : 0 ≠ doneReg)
    (hM : σ 0 = M) (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hstart1 : 1 ≤ start) (hsafe : start < M + curJ) (hbelow : boundReg < start)
    (hstartE : startE.eval
      ((secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ) =
      start)
    (hnumCtrl : numVarsReg ≠ cursorReg ∧ numVarsReg ≠ outerReg ∧ numVarsReg ≠ doneReg)
    (hcountCtrl : clauseCountReg ≠ cursorReg ∧ clauseCountReg ≠ outerReg ∧
      clauseCountReg ≠ doneReg)
    (hnum : σ numVarsReg = numVars) (hcount : σ clauseCountReg = clauseCount)
    (hnumLow : numVarsReg < start) (hcountLow : clauseCountReg < start)
    (hroom : start + numVars + clauseCount + 2 < M + curJ) :
    (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ
      startE numVarsReg clauseCountReg).eval σ boundReg = σ boundReg := by
  set σr :=
    (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ
  have hbR : σr boundReg = σ boundReg :=
    secondPassRewindProgramAt_frame cursorReg inputBaseReg outerReg doneReg boundReg
      boundReg σ hbc hbo hbd
  have h0R : σr 0 = M :=
    (secondPassRewindProgramAt_frame cursorReg inputBaseReg outerReg doneReg boundReg
      0 σ h0c h0o h0d).trans hM
  have hnumR : σr numVarsReg = numVars :=
    (secondPassRewindProgramAt_frame cursorReg inputBaseReg outerReg doneReg boundReg
      numVarsReg σ hnumCtrl.1 hnumCtrl.2.1 hnumCtrl.2.2).trans hnum
  have hcountR : σr clauseCountReg = clauseCount :=
    (secondPassRewindProgramAt_frame cursorReg inputBaseReg outerReg doneReg boundReg
      clauseCountReg σ hcountCtrl.1 hcountCtrl.2.1 hcountCtrl.2.2).trans hcount
  set σi := (ctlAssign curJ startE).eval σr
  have hneCtl : boundReg ≠ σr 0 + curJ := by rw [h0R]; omega
  have hbI : σi boundReg = σr boundReg :=
    ctlAssign_eval_diff curJ startE σr boundReg hneCtl
  have h0I : σi 0 = M := (ctlAssign_zero curJ startE σr hcurJ).trans h0R
  have hcurI : σi (M + curJ) = start := by
    have h := ctlAssign_eval_same curJ startE σr
    rw [h0R, hstartE] at h
    simpa [σi] using h
  have hnumI : σi numVarsReg = numVars :=
    (ctlAssign_eval_diff curJ startE σr numVarsReg (by rw [h0R]; omega)).trans hnumR
  have hcountI : σi clauseCountReg = clauseCount :=
    (ctlAssign_eval_diff curJ startE σr clauseCountReg (by rw [h0R]; omega)).trans hcountR
  have hsInit : WriterInit M curJ start σi :=
    writerInit_mk M curJ start σi h0I hcurI hstart1 hsafe
  have hhead : (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σi
      boundReg = σi boundReg :=
    writerAppendHeaderProg_frame M curJ tmpJ start [] numVarsReg clauseCountReg
      numVars clauseCount σi hcurJ htmpJ hnumI hcountI hcountLow hsInit
      (by simpa using hroom) hbelow
  have hseq :
      (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ
        startE numVarsReg clauseCountReg).eval σ =
      (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σi := by
    simp [secondPassStartupProgramAt, σr, σi, eval_seq]
  rw [hseq, hhead, hbI, hbR]

/-! ## Top-level At unfolding -/

lemma uniformSatToThreeCNFProg_eval (σ : Store) :
    uniformSatToThreeCNFProg.eval σ =
      let σr := uniformRelocateProg.eval σ
      let σc := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σr
      let σi := uniformControlInitProg.eval σc
      let σd :=
        (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg).eval σi
      let σp := uniformPostDecodeStatsProg.eval σd
      let σs := uniformSaveBoundProg.eval σp
      let σa := uniformSetArenaProg.eval σs
      let σst :=
        (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
          uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa
      let σx := uniformEmitAuxInitProg.eval σst
       let σf := uniformFreshFromMaxProg.eval σx
       let σz := uniformEmitResetProg.eval σf
       let σe :=
         (Program.forN (.reg uctOuterReg) uniformEmitIterBody).eval σz
      let σb := (Program.assign uctOutBaseReg uniformStartE).eval σe
      let σl := (Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)).eval σb
      (finalizeOutputProg uctOutBaseReg uctOutLenReg).eval σl := by
  simp only [uniformSatToThreeCNFProg, eval_seq]

end NPComplete.CookLevin

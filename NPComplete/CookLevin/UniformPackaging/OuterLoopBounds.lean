module

public import NPComplete.CookLevin.UniformPackaging.DispatchTmp
public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalizeBody

/-!
# Bounds through the outer clause loop

Bounds for one dispatch must be lifted over all input clauses while retaining
the semantic relation and store-size invariant. This module proves prefix and
whole-loop bounds, including the setup and outer-loop programs.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma programBoundedIn_uniformSaveBoundProg (B : ℕ) (σ : Store)
    (hB : uctSavedBoundReg ≤ B) :
    ProgramBoundedIn B σ uniformSaveBoundProg := by
  simpa [uniformSaveBoundProg, ProgramBoundedIn, ExprBoundedIn,
    uctSavedBoundReg] using And.intro hB (show 0 ≤ B by omega)

lemma programBoundedIn_uniformFreshFromMaxProg (B : ℕ) (σ : Store)
    (hB : 25 ≤ B) :
    ProgramBoundedIn B σ uniformFreshFromMaxProg := by
  simp [uniformFreshFromMaxProg, ProgramBoundedIn, ExprBoundedIn,
    uctFreshReg, uctMaxReg]
  omega

lemma programBoundedIn_uniformEmitAuxInitProg (B : ℕ) (σ : Store)
    (hB : 25 ≤ B) :
    ProgramBoundedIn B σ uniformEmitAuxInitProg := by
  simp [uniformEmitAuxInitProg, ProgramBoundedIn, ExprBoundedIn,
    uctPosPolReg, uctNegPolReg]
  omega

lemma programBoundedIn_uniformEmitResetProg (B : ℕ) (σ : Store)
    (hB : 25 ≤ B) :
    ProgramBoundedIn B σ uniformEmitResetProg := by
  simp [uniformEmitResetProg, emitClauseResetProg, ProgramBoundedIn,
    ExprBoundedIn, uctLengthReg, uctDoneReg]
  omega

lemma programBoundedIn_uniformEmitScratchResetProg (B : ℕ) (σ : Store)
    (hB : 25 ≤ B) :
    ProgramBoundedIn B σ uniformEmitScratchResetProg := by
  unfold uniformEmitScratchResetProg
  simp [zeroRegsProg, uniformEmitScratchRegs, ProgramBoundedIn, ExprBoundedIn,
    uctPolReg, uctVarReg, uctDoneReg, uctLengthReg, uctRemainingReg,
    uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctPosPolReg,
    uctNegPolReg, uctCarryPolReg, uctCarryValReg]
  omega

lemma programBoundedIn_uniformEmitIterBody_of_reset
    (B : ℕ) (σ : Store) (hB : 25 ≤ B)
    (hp : ProgramBoundedIn B (uniformEmitScratchResetProg.eval σ)
      uniformEmitIterCoreBody) :
    ProgramBoundedIn B σ uniformEmitIterBody := by
  have hreset := programBoundedIn_uniformEmitScratchResetProg B σ hB
  have hend := programBoundedIn_uniformEmitScratchResetProg B
    (uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ)) hB
  exact ⟨hreset, hp, hend⟩

lemma storeValuesLe_uniformEmitScratchResetProg (B : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ) (hB25 : 25 ≤ B) :
    StoreValuesLe B (uniformEmitScratchResetProg.eval σ) := by
  exact program_eval_storeValuesLe σ uniformEmitScratchResetProg hB1 hσ
    (programBoundedIn_uniformEmitScratchResetProg B σ hB25)
    scanFree_uniformEmitScratchResetProg

lemma programBoundedIn_uniformControlInitProg (B : ℕ) (σ : Store)
    (hB : 25 ≤ B) :
    ProgramBoundedIn B σ uniformControlInitProg := by
  simp [uniformControlInitProg, zeroRegsProg, ProgramBoundedIn,
    ExprBoundedIn, uctControlRegs, uctPolReg, uctVarReg, uctDoneReg,
    uctOuterReg, uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg,
    uctCountReg, uctTmpReg, uctSeenReg]
  omega

lemma storeValuesLe_uniformFreshFromMaxProg (B : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ) (hB25 : 25 ≤ B) :
    StoreValuesLe B (uniformFreshFromMaxProg.eval σ) := by
  exact program_eval_storeValuesLe σ uniformFreshFromMaxProg hB1 hσ
    (programBoundedIn_uniformFreshFromMaxProg B σ hB25)
    scanFree_uniformFreshFromMaxProg

lemma storeValuesLe_uniformEmitAuxInitProg (B : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ) (hB25 : 25 ≤ B) :
    StoreValuesLe B (uniformEmitAuxInitProg.eval σ) := by
  exact program_eval_storeValuesLe σ uniformEmitAuxInitProg hB1 hσ
    (programBoundedIn_uniformEmitAuxInitProg B σ hB25)
    scanFree_uniformEmitAuxInitProg

lemma storeValuesLe_uniformEmitResetProg (B : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ) (hB25 : 25 ≤ B) :
    StoreValuesLe B (uniformEmitResetProg.eval σ) := by
  exact program_eval_storeValuesLe σ uniformEmitResetProg hB1 hσ
    (programBoundedIn_uniformEmitResetProg B σ hB25)
    scanFree_uniformEmitResetProg

lemma programBoundedIn_emitNatProg_of_writerState
    (B M curJ tmpJ start : ℕ) (pref : Bits) (e : Expr) (σ : Store)
    (hs : WriterState σ M curJ start pref)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcurJB : curJ ≤ B) (htmpJB : tmpJ ≤ B)
    (hMcurB : M + curJ ≤ B) (hMtmpB : M + tmpJ ≤ B)
    (he : ExprBoundedIn B σ e)
    (hroom : start + pref.length + e.eval σ + 1 < M + curJ) :
    ProgramBoundedIn B σ (emitNatProg curJ tmpJ e) := by
  rcases hs with ⟨hroot, hcursor, _, hstart, hsafe⟩
  have htmpJ1 : 1 ≤ tmpJ := by omega
  have hct : curJ ≠ tmpJ := by omega
  have hcur1 : 1 ≤ start + pref.length := by omega
  have hsep : start + pref.length + e.eval σ < M + curJ := by omega
  have hcurEB : start + pref.length + e.eval σ + 1 ≤ B := by omega
  exact programBoundedIn_emitNatProg B curJ tmpJ M (start + pref.length) e σ
    hcurJ htmpJ1 hct hroot hcursor hcur1 hsep he hcurJB htmpJB hMcurB hMtmpB hcurEB

lemma programBoundedIn_writerAppendNatProg_of_state
    (B M curJ tmpJ start : ℕ) (pref : Bits) (e : Expr) (σ : Store)
    (hs : WriterState σ M curJ start pref)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcurJB : curJ ≤ B) (htmpJB : tmpJ ≤ B)
    (hMcurB : M + curJ ≤ B) (hMtmpB : M + tmpJ ≤ B)
    (he : ExprBoundedIn B σ e)
    (hroom : start + pref.length + e.eval σ + 1 < M + curJ) :
    ProgramBoundedIn B σ (writerAppendNatProg curJ tmpJ e) := by
  simpa [writerAppendNatProg] using
    programBoundedIn_emitNatProg_of_writerState B M curJ tmpJ start pref e σ hs hcurJ htmpJ
      hcurJB htmpJB hMcurB hMtmpB he hroom

lemma programBoundedIn_writerAppendLiteralProg_of_state
    (B M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg varVal : ℕ) (σ : Store)
    (hs : WriterState σ M curJ start pref)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcurJB : curJ ≤ B) (htmpJB : tmpJ ≤ B)
    (hMcurB : M + curJ ≤ B) (hMtmpB : M + tmpJ ≤ B)
    (hpolB : polReg ≤ B) (hvarB : varReg ≤ B)
    (hvar : σ varReg = varVal) (hvarLow : varReg < start)
    (hroom : start + pref.length + varVal + 2 < M + curJ) :
    ProgramBoundedIn B σ (writerAppendLiteralProg curJ tmpJ polReg varReg) := by
  rcases hs with ⟨hroot, hcursor, _, hstart, hsafe⟩
  have htmpJ1 : 1 ≤ tmpJ := by omega
  have hct : curJ ≠ tmpJ := by omega
  have hcur0 : start + pref.length ≠ 0 := by omega
  have hne : start + pref.length ≠ M + curJ := by omega
  have hcursorB : start + pref.length ≤ B := by omega
  have hcursor1B : start + pref.length + 1 ≤ B := by omega
  have hbit : ProgramBoundedIn B σ (emitBitProg curJ (.reg polReg)) := by
    have hv : ExprBoundedIn B σ (.reg polReg) := by
      simp only [ExprBoundedIn]
      exact hpolB
    exact programBoundedIn_emitBitProg B curJ M (start + pref.length)
      (.reg polReg) σ hroot hcursor hcur0 hne hv hcurJB hMcurB hcursorB hcursor1B
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  have hroot1 : σ1 0 = M := by
    dsimp [σ1]
    exact emitBitProg_ctl curJ M (start + pref.length) (.reg polReg) σ hcurJ hroot
      hcursor hcur0 hne
  have hcursor1 : σ1 (M + curJ) = start + pref.length + 1 := by
    dsimp [σ1]
    exact emitBitProg_cursor curJ M (start + pref.length) (.reg polReg) σ hroot
      hcursor hcur0 hne
  have hvar1 : σ1 varReg = varVal := by
    dsimp [σ1]
    rw [emitBitProg_frame curJ M (start + pref.length) (.reg polReg) σ hroot hcursor
      hcur0 hne varReg (by omega) (by omega), hvar]
  have hroom1 : (start + pref.length + 1) + σ1 varReg + 1 ≤ B := by
    rw [hvar1]
    omega
  have hvarE : ExprBoundedIn B σ1 (.reg varReg) := by
    simp only [ExprBoundedIn]
    exact hvarB
  have hnat : ProgramBoundedIn B σ1 (emitNatProg curJ tmpJ (.reg varReg)) := by
    have hsep : (start + pref.length + 1) + σ1 varReg < M + curJ := by
      rw [hvar1]
      omega
    exact programBoundedIn_emitNatProg B curJ tmpJ M (start + pref.length + 1)
      (.reg varReg) σ1 hcurJ htmpJ1 hct hroot1 hcursor1 (by omega) hsep hvarE
      hcurJB htmpJB hMcurB hMtmpB hroom1
  refine ⟨hbit, ?_⟩
  simpa [writerAppendLiteralProg, σ1] using hnat

lemma programBoundedIn_writerAppendThreeRegsProg_of_state
    (B M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 : ℕ)
    (pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcurJB : curJ ≤ B) (htmpJB : tmpJ ≤ B)
    (hMcurB : M + curJ ≤ B) (hMtmpB : M + tmpJ ≤ B)
    (hp1B : p1 ≤ B) (hv1B : v1 ≤ B) (hp2B : p2 ≤ B) (hv2B : v2 ≤ B)
    (hp3B : p3 ≤ B) (hv3B : v3 ≤ B)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ) :
    ProgramBoundedIn B σ (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3) := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hp1' := programBoundedIn_writerAppendLiteralProg_of_state B M curJ tmpJ start
    pref p1 v1 val1 σ hs hcurJ htmpJ hcurJB htmpJB hMcurB hMtmpB hp1B hv1B hv1
    hlow1 hroom1
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ hcurJ htmpJ
    hp1 hv1 hpol1 hs hroom1 hlow1
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  have hs1' : WriterState σ1 M curJ start
      (pref ++ encodedLiteralBits pol1 val1) := by
    simpa [σ1] using hs1
  have hp2val := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.1
  have hp2' : σ1 p2 = pol2 := by simpa [σ1] using hp2val.trans hp2
  have hv2val := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.2
  have hv2' : σ1 v2 = val2 := by simpa [σ1] using hv2val.trans hv2
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hp2b := programBoundedIn_writerAppendLiteralProg_of_state B M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hs1' hcurJ htmpJ
    hcurJB htmpJB hMcurB hMtmpB hp2B hv2B hv2' hlow2.2 hroom2
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 σ1 hcurJ htmpJ hp2' hv2' hpol2 hs1'
    hroom2 hlow2.2
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hs2' : WriterState σ2 M curJ start
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2) := by
    simpa [σ2, σ1, List.append_assoc] using hs2
  have hp3val := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ hv2' hs1' hroom2
    hlow2.2 hlow3.1
  have hp3firstVal := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.1
  have hp3first : σ1 p3 = pol3 := by simpa [σ1] using hp3firstVal.trans hp3
  have hp3' : σ2 p3 = pol3 := by simpa [σ2] using hp3val.trans hp3first
  have hv3val := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ hv2' hs1' hroom2
    hlow2.2 hlow3.2
  have hv3firstVal := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.2
  have hv3first : σ1 v3 = val3 := by simpa [σ1] using hv3firstVal.trans hv3
  have hv3' : σ2 v3 = val3 := by simpa [σ2] using hv3val.trans hv3first
  have hroom3 : start + (pref ++ encodedLiteralBits pol1 val1 ++
      encodedLiteralBits pol2 val2).length + val3 + 2 < M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hp3b := programBoundedIn_writerAppendLiteralProg_of_state B M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 val3 σ2 hs2' hcurJ htmpJ hcurJB htmpJB hMcurB hMtmpB hp3B hv3B hv3'
    hlow3.2 hroom3
  simpa [writerAppendThreeRegsProg, σ1, σ2] using ⟨hp1', hp2b, hp3b⟩

lemma programBoundedIn_splitTailEmitStepProgAt_of_branches
    (B curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hB2 : 2 ≤ B)
    (hremaining : remainingReg ≤ B)
    (hone : ProgramBoundedIn B σ
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg))
    (htwo : ProgramBoundedIn B σ
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg))
    (hinter : ProgramBoundedIn B σ
      (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg)) :
    ProgramBoundedIn B σ
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg) := by
  simp only [splitTailEmitStepProgAt, ProgramBoundedIn]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ExprBoundedIn]
    exact ⟨hremaining, by omega⟩
  · trivial
  · refine ⟨?_, hone, ?_⟩
    · simp only [ExprBoundedIn]
      exact ⟨hremaining, by omega⟩
    · refine ⟨?_, htwo, hinter⟩
      simp only [ExprBoundedIn]
      exact ⟨hremaining, by omega⟩

lemma programBoundedIn_splitTailEmitProgAt_of_step
    (B curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hB1 : 1 ≤ B)
    (hremaining : remainingReg ≤ B)
    (hremainingValue : σ remainingReg + 1 ≤ B)
    (hzero : ProgramBoundedIn B σ
      (splitTailEmitTerminalZeroProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg))
    (hstep : ∀ m < σ remainingReg + 1,
      ProgramBoundedIn B
        (loopEval
          (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
            pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
            boundReg) m σ)
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          boundReg)) :
    ProgramBoundedIn B σ
      (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg) := by
  simp only [splitTailEmitProgAt, ProgramBoundedIn]
  refine ⟨?_, hzero, ?_⟩
  · simp only [ExprBoundedIn]
    exact ⟨hremaining, by omega⟩
  · refine ⟨?_, ?_⟩
    · simp only [ExprBoundedIn]
      exact ⟨hremaining, by omega, by simpa [Expr.eval] using hremainingValue⟩
    · intro m hm
      exact hstep m (by simpa [Expr.eval] using hm)

lemma programBoundedIn_splitTailEmitLongClauseProgAt_of_parts
    (B curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store)
    (hsetup : ProgramBoundedIn B σ
      (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg))
    (hlong : ProgramBoundedIn B
      ((splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg).eval σ)
      (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg)) :
    ProgramBoundedIn B σ
      (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg) :=
  ⟨hsetup, hlong⟩

lemma programBoundedIn_emitClauseCommitProg_of_bounds
    (B outerReg : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (houter : outerReg ≤ B)
    (hσ : StoreValuesLe B σ) :
    ProgramBoundedIn B σ (emitClauseCommitProg outerReg) := by
  simp only [emitClauseCommitProg, ProgramBoundedIn, ExprBoundedIn]
  exact ⟨houter, ⟨houter, by omega, hσ outerReg⟩⟩

lemma programBoundedIn_emitClauseResetProg_of_bounds
    (B lengthReg doneReg : ℕ) (σ : Store)
    (hlen : lengthReg ≤ B) (hdone : doneReg ≤ B) :
    ProgramBoundedIn B σ (emitClauseResetProg lengthReg doneReg) := by
  simp only [emitClauseResetProg, ProgramBoundedIn, ExprBoundedIn]
  exact ⟨⟨hlen, by omega⟩, ⟨hdone, by omega⟩⟩

lemma programBoundedIn_emitClauseDispatchProgAt
    (B curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
       pol3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg
      boundReg : ℕ) (σ : Store) (hB3 : 3 ≤ B)
    (hlength : lengthReg ≤ B)
    (hzero : ProgramBoundedIn B σ
      (Program.seq
        (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
        (Program.seq (emitClauseEmptyFreshProg freshReg)
          (emitClauseCommitProg outerReg))))
    (hone : ProgramBoundedIn B σ
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (writerAppendClauseOneProg curJ tmpJ polReg varReg)
          (emitClauseCommitProg outerReg))))
    (htwo : ProgramBoundedIn B σ
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
          (Program.seq (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
            (emitClauseCommitProg outerReg)))))
    (hthree : ProgramBoundedIn B σ
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
          (Program.seq (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
            (Program.seq
              (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
                pol3Reg var3Reg posPolReg negPolReg freshReg)
              (Program.seq (emitClauseEmptyFreshProg freshReg)
                (emitClauseCommitProg outerReg)))))))
    (hlong : ProgramBoundedIn B σ
      (Program.seq
        (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg
                  remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                  posPolReg freshReg boundReg)
                (emitClauseCommitProg outerReg))))))) :
    ProgramBoundedIn B σ
      (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
        carryValReg freshReg outerReg boundReg) := by
  simp only [emitClauseDispatchProgAt]
  refine ⟨?_, hzero, ?_⟩
  · simp only [ExprBoundedIn]
    exact ⟨hlength, by omega⟩
  · refine ⟨?_, hone, ?_⟩
    · simp only [ExprBoundedIn]
      exact ⟨hlength, by omega⟩
    · refine ⟨?_, htwo, ?_⟩
      · simp only [ExprBoundedIn]
        exact ⟨hlength, by omega⟩
      · refine ⟨?_, hthree, hlong⟩
        simp only [ExprBoundedIn]
        exact ⟨hlength, by omega⟩

lemma programBoundedIn_uniformEmitIterCoreBody_of_parts
    (B : ℕ) (σ : Store)
    (hdecode : ProgramBoundedIn B σ
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg))
    (hdispatch : ProgramBoundedIn B
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval σ)
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
        uctFreshReg uctOuterReg uctSavedBoundReg))
    (hreset : ProgramBoundedIn B
      ((emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
        uctFreshReg uctOuterReg uctSavedBoundReg).eval
        ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval σ)
      )
      uniformEmitResetProg) :
    ProgramBoundedIn B σ uniformEmitIterCoreBody := by
  unfold uniformEmitIterCoreBody emitClauseIterProgramAt emitClauseProgramAt
  simpa [uniformEmitResetProg] using ⟨⟨hdecode, hdispatch⟩, hreset⟩

lemma programBoundedIn_uniformEmitIterBody_of_program_parts
    (B : ℕ) (σ : Store) (hB25 : 25 ≤ B)
    (hdecode : ProgramBoundedIn B (uniformEmitScratchResetProg.eval σ)
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg))
    (hdispatch : ProgramBoundedIn B
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ))
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
        uctFreshReg uctOuterReg uctSavedBoundReg))
    (hreset : ProgramBoundedIn B
      ((emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
        uctFreshReg uctOuterReg uctSavedBoundReg).eval
        ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
          (uniformEmitScratchResetProg.eval σ)))
      uniformEmitResetProg) :
    ProgramBoundedIn B σ uniformEmitIterBody := by
  let σr := uniformEmitScratchResetProg.eval σ
  apply programBoundedIn_uniformEmitIterBody_of_reset B σ hB25
  exact programBoundedIn_uniformEmitIterCoreBody_of_parts B σr hdecode hdispatch hreset

end NPComplete.CookLevin

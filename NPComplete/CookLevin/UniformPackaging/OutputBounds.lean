module

public import NPComplete.CookLevin.UniformEmit
public import NPComplete.RAMToTM.Generic.Api.AbiBitProducerMachine
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatInputRelocate

/-!
# Physical output bounds

The reduction needs a bounded physical output slice, not merely a correct logical
formula. This module connects the final store and write log to output bits, length
bounds, scan-freeness, and polynomial output-size estimates.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeThreeCNF)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma decide_bit_cell (b : Bool) :
    decide ((if b then 1 else 0) = 1) = b := by
  cases b <;> simp

lemma physicalBits_of_bitsAt (log : WriteLog) (σ : Store) (base : ℕ) (bits : Bits)
    (hlog : ∀ a, lookupD log a 0 = σ a) (hbits : BitsAt σ base bits) :
    OutputSlice.physicalBits log ⟨base, bits.length⟩ = bits := by
  rw [physicalBits_eq_range]
  apply List.ext_getElem
  · simp
  · intro i hiRange hiBits
    have hi : i < bits.length := by simpa using hiBits
    have hcell := hbits i hi
    rw [List.getElem_map, List.getElem_range, hlog, hcell, decide_bit_cell]

noncomputable def uniformSatToThreeCNFOutPoly : Polynomial ℕ :=
  (X + 1) * (X + 1) * (X + 1) + C 17

lemma uniformSatToThreeCNFOutPoly_eval (N : ℕ) :
    uniformSatToThreeCNFOutPoly.eval N =
      (N + 1) * (N + 1) * (N + 1) + 17 := by
  simp [uniformSatToThreeCNFOutPoly]

lemma uniformSatToThreeCNFProg_outLen_le (φ : CNF) :
    (encodeThreeCNF (toThreeCNF φ)).length ≤
      uniformSatToThreeCNFOutPoly.eval (encodeCNF φ).length := by
  have h := encodeThreeCNF_toThreeCNF_length_lt_cube φ
  rw [uniformSatToThreeCNFOutPoly_eval]
  omega

lemma scanFree_zeroRegsProg (rs : List ℕ) : ScanFree (zeroRegsProg rs) := by
  induction rs with
  | nil => simp [ScanFree, zeroRegsProg]
  | cons _ rest ih => simp [ScanFree, zeroRegsProg, ih]

lemma scanFree_uniformRelocateProg : ScanFree uniformRelocateProg := by
  simp [ScanFree, uniformRelocateProg, uniformRelocateSetup, relocateCtlAssign,
    relocateStep]

lemma scanFree_uniformControlInitProg : ScanFree uniformControlInitProg := by
  simpa [uniformControlInitProg] using scanFree_zeroRegsProg uctControlRegs

lemma scanFree_uniformPostDecodeStatsProg : ScanFree uniformPostDecodeStatsProg := by
  simp [ScanFree, uniformPostDecodeStatsProg]

lemma scanFree_uniformSaveBoundProg : ScanFree uniformSaveBoundProg := by
  simp [ScanFree, uniformSaveBoundProg]

lemma scanFree_uniformSetArenaProg : ScanFree uniformSetArenaProg := by
  simp [ScanFree, uniformSetArenaProg, uniformME]

lemma scanFree_uniformEmitAuxInitProg : ScanFree uniformEmitAuxInitProg := by
  simp [ScanFree, uniformEmitAuxInitProg]

lemma scanFree_uniformFreshFromMaxProg : ScanFree uniformFreshFromMaxProg := by
  simp [ScanFree, uniformFreshFromMaxProg]

lemma scanFree_uniformEmitResetProg : ScanFree uniformEmitResetProg := by
  simp [ScanFree, uniformEmitResetProg, emitClauseResetProg]

lemma scanFree_finalizeOutputProg :
    ScanFree (finalizeOutputProg uctOutBaseReg uctOutLenReg) := by
  simp [ScanFree, finalizeOutputProg]

lemma scanFree_uniformCursorInitProg (cursorReg inputBaseReg : ℕ) :
    ScanFree (uniformCursorInitProg cursorReg inputBaseReg) := by
  simp [ScanFree, uniformCursorInitProg]

lemma scanFree_decodeUnaryStep (cursorReg countReg doneReg : ℕ) :
    ScanFree (decodeUnaryStep cursorReg countReg doneReg) := by
  simp [ScanFree, decodeUnaryStep]

lemma scanFree_decodeUnaryProgAt (cursorReg countReg doneReg : ℕ) (boundE : Expr) :
    ScanFree (decodeUnaryProgAt cursorReg countReg doneReg boundE) := by
  simpa [ScanFree, decodeUnaryProgAt] using
    scanFree_decodeUnaryStep cursorReg countReg doneReg

lemma scanFree_decodeNatProgramAt (cursorReg countReg doneReg boundReg : ℕ) :
    ScanFree (decodeNatProgramAt cursorReg countReg doneReg boundReg) := by
  simpa [decodeNatProgramAt] using
    scanFree_decodeUnaryProgAt cursorReg countReg doneReg (.reg boundReg)

lemma scanFree_decodeLiteralValueProgramAt
    (cursorReg polReg varReg doneReg boundReg : ℕ) :
    ScanFree (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg
      boundReg) := by
  simp [ScanFree, decodeLiteralValueProgramAt, readBitAdvanceProg,
    decodeNatProgramAt, decodeUnaryProgAt, decodeUnaryStep]

lemma scanFree_decodeClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ) :
    ScanFree (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg
      maxReg boundReg) := by
  simp [ScanFree, decodeClauseStepAt, decodeLiteralValueProgramAt,
    readBitAdvanceProg, decodeNatProgramAt, decodeUnaryProgAt, decodeUnaryStep]

lemma scanFree_decodeClauseWithLengthPrefixAt
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) :
    ScanFree (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg
      lengthReg boundReg) := by
  simp [ScanFree, decodeClauseWithLengthPrefixAt, decodeNatProgramAt,
    decodeUnaryProgAt, decodeUnaryStep]

lemma scanFree_decodeClauseWithLengthProgramAt
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg boundReg : ℕ) :
    ScanFree (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg
      remainingReg maxReg lengthReg boundReg) := by
  refine ⟨scanFree_decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg
    lengthReg boundReg, ?_⟩
  simpa [ScanFree] using
    scanFree_decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg
      maxReg boundReg

lemma scanFree_clauseStatsProgram
    (clauseLenReg freshReg countReg tmpReg : ℕ) :
    ScanFree (clauseStatsProgram clauseLenReg freshReg countReg tmpReg) := by
  simp [ScanFree, clauseStatsProgram]

lemma scanFree_decodeCNFClauseStepWithStatsAt
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg
      countReg tmpReg boundReg : ℕ) :
    ScanFree (decodeCNFClauseStepWithStatsAt cursorReg polReg varReg doneReg
      remainingReg maxReg lengthReg freshReg countReg tmpReg boundReg) :=
  ⟨scanFree_decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg
    remainingReg maxReg lengthReg boundReg,
    scanFree_clauseStatsProgram lengthReg freshReg countReg tmpReg⟩

lemma scanFree_decodeCNFStepAt
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg boundReg : ℕ) :
    ScanFree (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg
      remainingReg maxReg lengthReg freshReg countReg tmpReg boundReg) := by
  simp [ScanFree, decodeCNFStepAt,
    scanFree_decodeCNFClauseStepWithStatsAt]

lemma scanFree_decodeCNFMarkSeenProg (lengthReg seenReg : ℕ) :
    ScanFree (decodeCNFMarkSeenProg lengthReg seenReg) := by
  simp [ScanFree, decodeCNFMarkSeenProg]

lemma scanFree_decodeCNFStepAtSeen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg boundReg seenReg : ℕ) :
    ScanFree (decodeCNFStepAtSeen cursorReg polReg varReg doneReg outerReg
      remainingReg maxReg lengthReg freshReg countReg tmpReg boundReg seenReg) :=
  ⟨scanFree_decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg
    maxReg lengthReg freshReg countReg tmpReg boundReg,
    scanFree_decodeCNFMarkSeenProg lengthReg seenReg⟩

lemma scanFree_decodeCNFProgramAtSeen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg boundReg seenReg : ℕ) :
    ScanFree (decodeCNFProgramAtSeen cursorReg polReg varReg doneReg outerReg
      remainingReg maxReg lengthReg freshReg countReg tmpReg boundReg seenReg) := by
  simp [ScanFree, decodeCNFProgramAtSeen,
    scanFree_decodeNatProgramAt, scanFree_decodeCNFStepAtSeen]

lemma scanFree_emitBitProg (curJ : ℕ) (v : Expr) :
    ScanFree (emitBitProg curJ v) := by
  simp [ScanFree, emitBitProg, ctlAssign]

lemma scanFree_emitNatProg (curJ tmpJ : ℕ) (e : Expr) :
    ScanFree (emitNatProg curJ tmpJ e) := by
  simp [ScanFree, emitNatProg, ctlAssign, emitBitProg]

lemma scanFree_writerAppendNatProg (curJ tmpJ : ℕ) (e : Expr) :
    ScanFree (writerAppendNatProg curJ tmpJ e) := by
  simpa [writerAppendNatProg] using scanFree_emitNatProg curJ tmpJ e

lemma scanFree_writerAppendHeaderProg
    (curJ tmpJ numVarsReg clauseCountReg : ℕ) :
    ScanFree (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg) :=
  ⟨scanFree_writerAppendNatProg curJ tmpJ (.reg numVarsReg),
    scanFree_writerAppendNatProg curJ tmpJ (.reg clauseCountReg)⟩

lemma scanFree_writerAppendLiteralProg (curJ tmpJ polReg varReg : ℕ) :
    ScanFree (writerAppendLiteralProg curJ tmpJ polReg varReg) :=
  ⟨scanFree_emitBitProg curJ (.reg polReg),
    scanFree_emitNatProg curJ tmpJ (.reg varReg)⟩

lemma scanFree_writerAppendThreeRegsProg
    (curJ tmpJ p1 v1 p2 v2 p3 v3 : ℕ) :
    ScanFree (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3) :=
  ⟨scanFree_writerAppendLiteralProg curJ tmpJ p1 v1,
    ⟨scanFree_writerAppendLiteralProg curJ tmpJ p2 v2,
      scanFree_writerAppendLiteralProg curJ tmpJ p3 v3⟩⟩

lemma scanFree_writerAppendSplitTailLinkDynamicProg
    (curJ tmpJ carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ) :
    ScanFree (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg
      carryValReg polReg valReg posPolReg freshReg) := by
  simp [ScanFree, writerAppendSplitTailLinkDynamicProg,
    scanFree_writerAppendThreeRegsProg]

lemma scanFree_writerAppendClauseOneProg (curJ tmpJ polReg varReg : ℕ) :
    ScanFree (writerAppendClauseOneProg curJ tmpJ polReg varReg) := by
  simpa [writerAppendClauseOneProg] using
    scanFree_writerAppendThreeRegsProg curJ tmpJ polReg varReg polReg varReg
      polReg varReg

lemma scanFree_writerAppendClauseTwoProg
    (curJ tmpJ pol1Reg var1Reg pol2Reg var2Reg : ℕ) :
    ScanFree (writerAppendClauseTwoProg curJ tmpJ pol1Reg var1Reg pol2Reg
      var2Reg) := by
  simpa [writerAppendClauseTwoProg] using
    scanFree_writerAppendThreeRegsProg curJ tmpJ pol1Reg var1Reg pol2Reg var2Reg
      pol2Reg var2Reg

lemma scanFree_writerAppendClauseEmptyProg
    (curJ tmpJ posPolReg negPolReg freshReg : ℕ) :
    ScanFree (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg
      freshReg) :=
  ⟨scanFree_writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg posPolReg
    freshReg posPolReg freshReg,
    scanFree_writerAppendThreeRegsProg curJ tmpJ negPolReg freshReg negPolReg
      freshReg negPolReg freshReg⟩

lemma scanFree_writerAppendClauseThreeProg
    (curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ) :
    ScanFree (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg
      negPolReg freshReg) :=
  ⟨scanFree_writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg,
    scanFree_writerAppendThreeRegsProg curJ tmpJ negPolReg freshReg p3 v3 p3 v3⟩

lemma scanFree_emitClauseCommitProg (outerReg : ℕ) :
    ScanFree (emitClauseCommitProg outerReg) := by
  simp [ScanFree, emitClauseCommitProg]

lemma scanFree_emitClauseEmptyFreshProg (freshReg : ℕ) :
    ScanFree (emitClauseEmptyFreshProg freshReg) := by
  simp [ScanFree, emitClauseEmptyFreshProg]

lemma scanFree_emitClauseResetProg (lengthReg doneReg : ℕ) :
    ScanFree (emitClauseResetProg lengthReg doneReg) := by
  simp [ScanFree, emitClauseResetProg]

lemma scanFree_splitTailEmitTerminalZeroProg
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg
      carryValReg posPolReg freshReg bound : ℕ) :
    ScanFree (splitTailEmitTerminalZeroProg curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound) := by
  simp [ScanFree, splitTailEmitTerminalZeroProg,
    scanFree_writerAppendThreeRegsProg]

lemma scanFree_splitTailEmitTerminalOneProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg
      freshReg boundReg) := by
  simp [ScanFree, splitTailEmitTerminalOneProgAt,
    scanFree_decodeLiteralValueProgramAt, scanFree_writerAppendThreeRegsProg]

lemma scanFree_splitTailEmitTerminalTwoProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg boundReg) := by
  simp [ScanFree, splitTailEmitTerminalTwoProgAt,
    scanFree_decodeLiteralValueProgramAt, scanFree_writerAppendThreeRegsProg]

lemma scanFree_splitTailEmitIntermediateProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg
      carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg carryPolReg carryValReg posPolReg freshReg
      boundReg) := by
  simp [ScanFree, splitTailEmitIntermediateProgAt,
    scanFree_decodeLiteralValueProgramAt,
    scanFree_writerAppendSplitTailLinkDynamicProg]

lemma scanFree_splitTailEmitStepProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg boundReg) := by
  simp [ScanFree, splitTailEmitStepProgAt,
    scanFree_splitTailEmitTerminalOneProgAt,
    scanFree_splitTailEmitTerminalTwoProgAt,
    scanFree_splitTailEmitIntermediateProgAt]

lemma scanFree_splitTailEmitProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg boundReg) := by
  simp [ScanFree, splitTailEmitProgAt, scanFree_splitTailEmitTerminalZeroProg,
    scanFree_splitTailEmitStepProgAt]

lemma scanFree_splitTailEmitLongClauseSetupAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg boundReg) := by
  simp [ScanFree, splitTailEmitLongClauseSetupAt,
    scanFree_decodeLiteralValueProgramAt, scanFree_writerAppendThreeRegsProg]

lemma scanFree_splitTailEmitLongClauseProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) :
    ScanFree (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg boundReg) :=
  ⟨scanFree_splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg
    doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg boundReg,
    scanFree_splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg boundReg⟩

lemma scanFree_emitClauseDispatchProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg : ℕ) :
    ScanFree (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg boundReg) := by
  simp [ScanFree, emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong,
    scanFree_writerAppendClauseEmptyProg, scanFree_emitClauseEmptyFreshProg,
    scanFree_emitClauseCommitProg, scanFree_decodeLiteralValueProgramAt,
    scanFree_writerAppendClauseOneProg, scanFree_writerAppendClauseTwoProg,
    scanFree_writerAppendClauseThreeProg,
    scanFree_splitTailEmitLongClauseProgAt]

lemma scanFree_emitClauseProgramAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg : ℕ) :
    ScanFree (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg boundReg) :=
  ⟨scanFree_decodeNatProgramAt cursorReg lengthReg doneReg boundReg,
    scanFree_emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg boundReg⟩

lemma scanFree_emitClauseIterProgramAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg : ℕ) :
    ScanFree (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg boundReg) :=
  ⟨scanFree_emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg boundReg,
    scanFree_emitClauseResetProg lengthReg doneReg⟩

lemma scanFree_secondPassRewindProgramAt
    (cursorReg inputBaseReg outerReg doneReg boundReg : ℕ) :
    ScanFree (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg
      boundReg) := by
  simp [ScanFree, secondPassRewindProgramAt, scanFree_decodeNatProgramAt]

lemma scanFree_secondPassStartupProgramAt
    (cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ : ℕ)
    (startE : Expr) (numVarsReg clauseCountReg : ℕ) :
    ScanFree (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg
      boundReg curJ tmpJ startE numVarsReg clauseCountReg) := by
  simp [ScanFree, secondPassStartupProgramAt, ctlAssign,
    scanFree_secondPassRewindProgramAt, scanFree_writerAppendHeaderProg]

lemma scanFree_uniformEmitScratchResetProg : ScanFree uniformEmitScratchResetProg := by
  simp [uniformEmitScratchResetProg, uniformEmitScratchRegs, zeroRegsProg, ScanFree]

lemma scanFree_uniformEmitIterBody : ScanFree uniformEmitIterBody := by
  refine ⟨scanFree_uniformEmitScratchResetProg, ?_⟩
  refine ⟨?_, scanFree_uniformEmitScratchResetProg⟩
  exact scanFree_emitClauseIterProgramAt uctCurJ uctTmpJ uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
    uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg

end NPComplete.CookLevin

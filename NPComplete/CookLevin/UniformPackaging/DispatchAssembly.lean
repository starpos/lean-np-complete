module

public import NPComplete.CookLevin.UniformPackaging.DispatchLongBounds

/-!
# Clause-dispatch assembly bounds

Each clause-shape branch has a separate low-level proof, but the dispatcher must
be bounded as one program including its reset and iteration body. This module
combines branch bounds into the assembly-level envelope used by the outer
emitter.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma uniform_emit_dispatch_raw_bounds_of_branches
    (N : ℕ) (σ : Store)
    (hzero : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq
        (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg)
        (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
          (emitClauseCommitProg uctOuterReg))))
    (hone : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq (writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg)
          (emitClauseCommitProg uctOuterReg))))
    (htwo : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
              uctVar2Reg)
            (emitClauseCommitProg uctOuterReg)))))
    (hthree : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg)
            (Program.seq
              (writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
                uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg)
              (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
                (emitClauseCommitProg uctOuterReg)))))))
    (hlong : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
                  uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
                  uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
                  uctSavedBoundReg)
                 (emitClauseCommitProg uctOuterReg))))))) :
    EmitClauseDispatchRawBounds (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg σ := by
  have hB : 3 ≤ uniformEmitDispatchEnvelope N := by
    simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hlength : uctLengthReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctLengthReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  exact {
    bound := hB
    length := hlength
    zero := hzero
    one := hone
    two := htwo
    three := hthree
    long := hlong }

lemma uniformEmitDispatchEnvelope_ge_25 (N : ℕ) :
    25 ≤ uniformEmitDispatchEnvelope N := by
  simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound]
  omega

lemma programBoundedIn_uniformEmitResetProg_of_dispatch_envelope
    (N : ℕ) (σ : Store) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ uniformEmitResetProg := by
  simpa [uniformEmitResetProg] using
    (programBoundedIn_emitClauseResetProg_of_bounds (uniformEmitDispatchEnvelope N)
      uctLengthReg uctDoneReg σ
      (by simp only [uctLengthReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
        writerAppendRawThreeBound, writerAppendRawStepBound]; omega)
      (by simp only [uctDoneReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
        writerAppendRawThreeBound, writerAppendRawStepBound]; omega))

lemma programBoundedIn_uniformEmitIterBody_of_dispatch_envelope
    (N : ℕ) (σ : Store)
    (hdecode : ProgramBoundedIn (uniformEmitDispatchEnvelope N)
      (uniformEmitScratchResetProg.eval σ)
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg))
    (hdispatch : EmitClauseDispatchRawBounds (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ))) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ uniformEmitIterBody := by
  exact programBoundedIn_uniformEmitIterBody_of_dispatch_raw
    (uniformEmitDispatchEnvelope N) σ (uniformEmitDispatchEnvelope_ge_25 N) hdecode hdispatch
    (programBoundedIn_uniformEmitResetProg_of_dispatch_envelope N _)

/-! The five dispatch branch obligations on one decoded state: the four concrete
    branches are shape-free, and the long branch is covered by the short
    (structural) route for clauses of at most two literals and by the split-tail
    reachability route for longer clauses. -/

lemma uniform_emit_dispatch_raw_bounds_of_decoded
    (N inputEnd baseLimit base outer addr : ℕ)
    (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hcell01 : ∀ i, addr + ls.length + 1 ≤ i →
      i < addr + ls.length + 1 + 2 + 2 * N → σdec i ≤ 1)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls rest (addr + ls.length + 1))
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hwr : uniformStartNat + pref.length + N + N + base + 6 <
      uniformMNat N + uctCurJ) :
    EmitClauseDispatchRawBounds (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg σdec := by
  have hzeroB := programBoundedIn_uniform_emit_dispatch_zero_branch N base outer addr ls rest
    pref σr σdec hprep hstore
  have honeB := programBoundedIn_uniform_emit_dispatch_one_branch N base outer addr ls rest
    pref σr σdec hprep hstore hsaved
  have htwoB := programBoundedIn_uniform_emit_dispatch_two_branch N base outer addr ls rest
    pref σr σdec hprep hstore hsaved
  have hthreeB := programBoundedIn_uniform_emit_dispatch_three_branch N base outer addr ls
    rest pref σr σdec hprep hstore hsaved
  have hlongB : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
                  uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
                  uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
                  uctSavedBoundReg)
                (emitClauseCommitProg uctOuterReg)))))) := by
    rcases ls with _ | ⟨l1, rest1⟩
    · exact programBoundedIn_uniform_emit_dispatch_long_branch_short N inputEnd baseLimit
        base outer addr [] rest pref σr σdec hprep hstore hsaved (by simp) hcell01 hwin
        hend hwr
    rcases rest1 with _ | ⟨l2, rest2⟩
    · exact programBoundedIn_uniform_emit_dispatch_long_branch_short N inputEnd baseLimit
        base outer addr [l1] rest pref σr σdec hprep hstore hsaved (by simp) hcell01 hwin
        hend hwr
    rcases rest2 with _ | ⟨l3, litRest⟩
    · exact programBoundedIn_uniform_emit_dispatch_long_branch_short N inputEnd baseLimit
        base outer addr [l1, l2] rest pref σr σdec hprep hstore hsaved (by simp) hcell01
        hwin hend hwr
    · exact programBoundedIn_uniform_emit_dispatch_long_branch N inputEnd baseLimit base
        outer addr l1 l2 l3 litRest rest pref σr σdec hprep hstore hsaved hbound hwin
        hinputEnd hbaseLimit hend
  exact uniform_emit_dispatch_raw_bounds_of_branches N σdec hzeroB honeB htwoB hthreeB hlongB

/-! One outer iteration body from the clause-boundary relation: scratch reset,
    length decode, dispatch (all five branches), and the closing reset, all at
    the dispatch envelope.  The read-side cell premise and the writer-room
    premise are supplied by the outer invariant. -/

lemma programBoundedIn_uniformEmitIterBody_of_cnfEmitRel
    (N inputEnd : ℕ) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ)
    (hcell01 : ∀ i, addr + c.lits.length + 1 ≤ i →
      i < addr + c.lits.length + 1 + 2 + 2 * N →
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ) i ≤ 1)
    (hwin : SplitTailEmitWindow inputEnd (base + c.lits.length) base c.lits
      ((cs.map encodeClause).flatten ++ tail) (addr + c.lits.length + 1))
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hwr : uniformStartNat + pref.length + N + N + base + 6 <
      uniformMNat N + uctCurJ) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ uniformEmitIterBody := by
  have hdec := programBoundedIn_uniform_emit_decode_of_rel N c cs tail pref addr base σ
    hrel hb hσ
  have hwinAddr : SplitTailEmitWindow inputEnd (base + c.lits.length) base c.lits
      ((cs.map encodeClause).flatten ++ tail) addr := by
    refine ⟨?_, hwin.2⟩
    have h1 := hwin.1
    omega
  obtain ⟨hprep, hstoreDec⟩ := uniform_emit_decoded_state N inputEnd c cs tail pref addr
    base σ hrel hb hσ hwinAddr hend
  have hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with
      ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  have hbrd : (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg
      uctSavedBoundReg).eval (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N :=
    (decodeNatProgramAt_bound_frame uctCursorReg uctLengthReg uctDoneReg
      uctSavedBoundReg _ (by decide) (by decide) (by decide)).trans hbr
  have hbound : ∀ l ∈ c.lits, l.var + 1 ≤ N := hrel.literal_bound c (by simp)
  have hbaseLimit : base + c.lits.length ≤ uniformEmitLongValueEnvelope N := by
    have h1 : base ≤ uniformEmitTightEnvelope N := by
      rw [← hrel.fresh]
      exact hσ uctFreshReg
    have h2 : c.lits.length ≤ N := by
      have hclause := hrel.clause_bound c (by simp)
      omega
    have hL := uniformEmitTightEnvelope_le_long_value_envelope N
    have hN := uniform_emit_n_le_long_value_envelope N
    simp only [uniformEmitLongValueEnvelope] at ⊢
    omega
  have hraw := uniform_emit_dispatch_raw_bounds_of_decoded N inputEnd
    (base + c.lits.length) base (c :: cs).length addr c.lits
    ((cs.map encodeClause).flatten ++ tail) pref
    (uniformEmitScratchResetProg.eval σ)
    ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
      (uniformEmitScratchResetProg.eval σ))
    hprep hstoreDec hbrd hbound hcell01 hwin hinputEnd hbaseLimit hend hwr
  exact programBoundedIn_uniformEmitIterBody_of_dispatch_envelope N σ
    (programBoundedIn_of_le (uniformEmitSyntaxEnvelope_le_dispatch_envelope N) hdec) hraw

end NPComplete.CookLevin

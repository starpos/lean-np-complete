module

public import NPComplete.CookLevin.UniformEmit.Producer

/-!
# Producer correctness

The completed pipeline must turn the encoded CNF into the same 3-CNF result as the mathematical
transformation. This module composes startup, iteration, and ABI finalization into the end-to-end
output theorem, leaving lower-level proofs focused on individual phases.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral encodeThreeCNF)
open NPComplete.RAMToTM.Generic (ReductionOutput outAddrCell outLenCell)

lemma uniform_finalizeRegsOk : FinalizeRegsOk uctOutBaseReg uctOutLenReg := by
  simp [FinalizeRegsOk, uctOutBaseReg, uctOutLenReg, outAddrCell, outLenCell]

lemma uniform_out_regs_below_start :
    uctOutBaseReg < uniformStartNat ∧ uctOutLenReg < uniformStartNat ∧
      uctOutBaseReg ≠ uctOutLenReg := by
  simp [uctOutBaseReg, uctOutLenReg, uniformStartNat, relocateControlGap]

lemma uniformStartNat_ge_two : 2 ≤ uniformStartNat := by
  simp [uniformStartNat, relocateControlGap]

lemma uniformProducerResetStore_cnfEmitRel_reset (φ : CNF) :
    CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length
      (cnfVarBound φ) φ.clauses []
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (uniformProducerResetStore φ) :=
  uniform_producer_cnfEmitRel φ

lemma uniform_startup_preserves_savedBound (φ : CNF) (σ : Store)
    (h0 : σ 0 = uniformMNat (encodeCNF φ).length)
    (hnum : σ uctFreshReg = (toThreeCNF φ).numVars)
    (hcount : σ uctCountReg = (toThreeCNF φ).clauses.length) :
    ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
      uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
      uctFreshReg uctCountReg).eval σ) uctSavedBoundReg = σ uctSavedBoundReg := by
  set N := (encodeCNF φ).length
  set M := uniformMNat N
  exact secondPassStartupProgramAt_bound_frame
    uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg uctSavedBoundReg
    uctCurJ uctTmpJ M uniformStartNat uniformStartE uctFreshReg uctCountReg
    (toThreeCNF φ).numVars (toThreeCNF φ).clauses.length σ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h0 uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    (by simp [uniformStartNat, relocateControlGap])
    (uniform_layout_start_lt_M N)
    (by simp [uctSavedBoundReg, uniformStartNat, relocateControlGap])
    (uniformStartE_eval _) (by decide) (by decide) hnum hcount
    (by simp [uctFreshReg, uniformStartNat, relocateControlGap])
    (by simp [uctCountReg, uniformStartNat, relocateControlGap])
    (by simpa [N] using uniform_header_room φ)

lemma uniformProducerResetStore_savedBound (φ : CNF) :
    (uniformProducerResetStore φ) uctSavedBoundReg = (encodeCNF φ).length := by
  have hpre := uniform_producer_pre_startup φ
  set bits := encodeCNF φ
  set N := bits.length
  set σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  set σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  set σp := uniformPostDecodeStatsProg.eval σd
  set σs := uniformSaveBoundProg.eval σp
  set σa := uniformSetArenaProg.eval σs
  have hst := uniform_startup_preserves_savedBound φ σa hpre.1 hpre.2.2.2.1
    hpre.2.2.2.2.1
  set σst :=
    (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa
  have hx := uniformEmitAuxInitProg_frame σst (r := uctSavedBoundReg)
    (by decide) (by decide)
  set σx := uniformEmitAuxInitProg.eval σst
  have hf := uniformFreshFromMaxProg_frame σx (r := uctSavedBoundReg) (by decide)
  set σf := uniformFreshFromMaxProg.eval σx
  have hz := uniformEmitResetProg_frame σf (r := uctSavedBoundReg)
    (by decide) (by decide)
  simpa [uniformProducerResetStore, bits, N, σ0, σd, σp, σs, σa, σst, σx, σf] using
    hz.trans (hf.trans (hx.trans (hst.trans hpre.2.1)))

lemma uniform_producer_forN_eval (φ : CNF) (σ : Store)
    (houter : σ uctOuterReg = φ.clauses.length) :
    (Program.forN (.reg uctOuterReg) uniformEmitIterBody).eval σ =
      loopEval uniformEmitIterBody φ.clauses.length σ := by
  simp [eval_forN, Expr.eval, houter]

lemma uniform_emit_rel_list_to_done
    (N : ℕ) (clauses : List Clause) (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hcapacity : uniformStartNat + pref.length +
      (encodeThreeClausesPayload (clausesToThree base clauses).1).length + 2 <
        uniformMNat N + uctCurJ)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base clauses tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    ∃ k τ base' pref' addr',
      k = clauses.length ∧
      τ = loopEval uniformEmitIterBody k σ ∧
      CNFEmitDone (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base' tail pref' addr' τ ∧
      base' = (clausesToThree base clauses).2 ∧
      pref' = pref ++ encodeThreeClausesPayload (clausesToThree base clauses).1 ∧
      τ uctSavedBoundReg = N := by
  induction clauses generalizing base pref addr σ with
  | nil =>
      refine ⟨0, σ, base, pref, addr, by simp, by simp, ?_,
        by simp [clausesToThree], by simp [clausesToThree, encodeThreeClausesPayload], hb⟩
      exact ⟨hrel.input, hrel.cursor, by simpa using hrel.outer, hrel.fresh,
        hrel.length_zero, hrel.done_zero, hrel.pos, hrel.neg, hrel.writer,
        hrel.long_safety⟩
  | cons c cs ih =>
      obtain ⟨σ1, hstep, hnext, hb1⟩ := uniformEmitIterBody_eval_of_rel N c cs
        tail pref addr base σ hrel hb
      have hcapNext := cnfEmitRel_next_capacity (uniformMNat N) uctCurJ uniformStartNat
        base c cs pref (encodeThreeClausesPayload (clauseToThree base c.lits).1)
        hcapacity rfl
      obtain ⟨k, τ, base', pref', addr', hk, hloop, hdone, hbase, hpref, hbτ⟩ := ih
        (base := (clauseToThree base c.lits).2)
        (pref := pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
        (addr := addr + (encodeList encodeLiteral c.lits).length) (σ := σ1)
        hcapNext hnext hb1
      refine ⟨k + 1, τ, base', pref', addr', ?_, ?_, hdone, ?_, ?_, hbτ⟩
      · simp [hk]
      · calc
          τ = loopEval uniformEmitIterBody k σ1 := hloop
          _ = loopEval uniformEmitIterBody k (uniformEmitIterBody.eval σ) := by rw [hstep]
           _ = loopEval uniformEmitIterBody (k + 1) σ := by rw [loopEval_succ]
      · simp [hbase, clausesToThree_cons]
      · simp [hpref, clausesToThree_payload_cons, List.append_assoc]

lemma uniformProducerResetStore_emit_done (φ : CNF) :
    ∃ base' addr',
      CNFEmitDone (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
        (encodeCNF φ).length (encodeCNF φ).length base' ([] : Bits)
        (encodeThreeCNF (toThreeCNF φ)) addr'
        (loopEval uniformEmitIterBody φ.clauses.length
          (uniformProducerResetStore φ)) := by
  have hrel := uniformProducerResetStore_cnfEmitRel_reset φ
  obtain ⟨k, τ, base', pref', addr', hk, hloop, hdone, _, hpref, _⟩ :=
    uniform_emit_rel_list_to_done (encodeCNF φ).length φ.clauses []
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (cnfVarBound φ) (uniformProducerResetStore φ) hrel.capacity hrel
      (uniformProducerResetStore_savedBound φ)
  have hbits : pref' = encodeThreeCNF (toThreeCNF φ) :=
    hpref.trans (uniform_producer_pref_eq φ)
  refine ⟨base', addr', ?_⟩
  simpa [hk, hbits, hloop] using hdone

lemma uniformProducerResetStore_emit_writer (φ : CNF) :
    WriterState
      (loopEval uniformEmitIterBody φ.clauses.length (uniformProducerResetStore φ))
      (uniformMNat (encodeCNF φ).length) uctCurJ uniformStartNat
      (encodeThreeCNF (toThreeCNF φ)) := by
  obtain ⟨_, _, hdone⟩ := uniformProducerResetStore_emit_done φ
  exact hdone.writer

lemma uniformProducerResetStore_emit_forN (φ : CNF) :
    (Program.forN (.reg uctOuterReg) uniformEmitIterBody).eval
        (uniformProducerResetStore φ) =
      loopEval uniformEmitIterBody φ.clauses.length
        (uniformProducerResetStore φ) :=
  uniform_producer_forN_eval φ (uniformProducerResetStore φ)
    (uniformProducerResetStore_cnfEmitRel_reset φ).outer

lemma uniformSatToThreeCNFProg_eval_reset (φ : CNF) :
    uniformSatToThreeCNFProg.eval (bitInputStore (encodeCNF φ)) =
      (finalizeOutputProg uctOutBaseReg uctOutLenReg).eval
        ((Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)).eval
          ((Program.assign uctOutBaseReg uniformStartE).eval
            ((Program.forN (.reg uctOuterReg) uniformEmitIterBody).eval
              (uniformProducerResetStore φ)))) := by
  rw [uniformSatToThreeCNFProg_eval]
  rfl

lemma uniform_abi_suffix_eval (σ : Store) :
    (finalizeOutputProg uctOutBaseReg uctOutLenReg).eval
      ((Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)).eval
        ((Program.assign uctOutBaseReg uniformStartE).eval σ)) =
      (Program.seq (Program.assign uctOutBaseReg (.const uniformStartNat))
        (Program.seq
          (Program.assign uctOutLenReg
            (.sub (ctlCell uctCurJ) (.const uniformStartNat)))
          (finalizeOutputProg uctOutBaseReg uctOutLenReg))).eval σ := by
  simp [eval_seq, uniformStartE]

lemma uniform_abi_suffix_frame (σ : Store) (r : ℕ)
    (hr0 : r ≠ outAddrCell) (hr1 : r ≠ outLenCell)
    (hrb : r ≠ uctOutBaseReg) (hrl : r ≠ uctOutLenReg) :
    (finalizeOutputProg uctOutBaseReg uctOutLenReg).eval
      ((Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)).eval
        ((Program.assign uctOutBaseReg uniformStartE).eval σ)) r = σ r := by
  let program := Program.seq (Program.assign uctOutBaseReg uniformStartE)
    (Program.seq (Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE))
      (finalizeOutputProg uctOutBaseReg uctOutLenReg))
  let P : ℕ → Prop := fun w =>
    w ≠ outAddrCell ∧ w ≠ outLenCell ∧ w ≠ uctOutBaseReg ∧ w ≠ uctOutLenReg
  have hAvoids : program.Avoids P := by
    dsimp [program, P, finalizeOutputProg]
    decide +kernel
  simpa [program, eval_seq] using
    hAvoids.eval_frame σ (r := r) (show P r from ⟨hr0, hr1, hrb, hrl⟩)

lemma uniformSatToThreeCNFProg_bitsAt (φ : CNF) :
    BitsAt (uniformSatToThreeCNFProg.eval (bitInputStore (encodeCNF φ)))
      uniformStartNat (encodeThreeCNF (toThreeCNF φ)) := by
  intro i hi
  have hs := uniformProducerResetStore_emit_writer φ
  have hstart := uniformStartNat_ge_two
  have hlow := uniform_out_regs_below_start
  rw [uniformSatToThreeCNFProg_eval_reset, uniformProducerResetStore_emit_forN]
  rw [uniform_abi_suffix_frame _ (uniformStartNat + i)
    (by simp [outAddrCell]; omega) (by simp [outLenCell]; omega)
    (by omega) (by omega)]
  exact hs.bits i hi

lemma uniformSatToThreeCNFProg_reductionOutput (φ : CNF) :
    ReductionOutput
      (uniformSatToThreeCNFProg.eval (bitInputStore (encodeCNF φ)))
      uniformStartNat (encodeThreeCNF (toThreeCNF φ)).length := by
  have hs := uniformProducerResetStore_emit_writer φ
  have hro := reductionOutput_of_writerState_abiSuffix
    uctOutBaseReg uctOutLenReg (uniformMNat (encodeCNF φ).length)
    uctCurJ uniformStartNat (encodeThreeCNF (toThreeCNF φ))
    (loopEval uniformEmitIterBody φ.clauses.length (uniformProducerResetStore φ))
    hs uniform_out_regs_below_start.1 uniform_out_regs_below_start.2.1
    uniform_out_regs_below_start.2.2 uniform_finalizeRegsOk uniformStartNat_ge_two
  rw [uniformSatToThreeCNFProg_eval_reset, uniformProducerResetStore_emit_forN,
    uniform_abi_suffix_eval]
  exact hro

lemma encodeThreeCNF_toThreeCNF_length_lt_cube (φ : CNF) :
    (encodeThreeCNF (toThreeCNF φ)).length + 2 <
      ((encodeCNF φ).length + 1) * ((encodeCNF φ).length + 1) *
        ((encodeCNF φ).length + 1) + 17 := by
  have h := uniform_capacity_of_encodeCNF φ
  simp [uniformMNat, uniformSlackNat, uctCurJ] at h
  omega

lemma uniformSatToThreeCNFProg_eval_encode (φ : CNF) :
    let σ := uniformSatToThreeCNFProg.eval (bitInputStore (encodeCNF φ))
    let bits := encodeThreeCNF (toThreeCNF φ)
    σ outAddrCell = uniformStartNat ∧
      σ outLenCell = bits.length ∧
      BitsAt σ uniformStartNat bits ∧
      ReductionOutput σ uniformStartNat bits.length ∧
      bits = NPComplete.SAT.ValidThreeCNF.encode (toValidThreeCNF φ) := by
  have hro := uniformSatToThreeCNFProg_reductionOutput φ
  exact ⟨hro.addr_eq, hro.len_eq, uniformSatToThreeCNFProg_bitsAt φ, hro,
    (toValidThreeCNF_encode φ).symm⟩

end NPComplete.CookLevin

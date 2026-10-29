module

public import NPComplete.CookLevin.UniformEmit.LayoutBounds

/-!
# Producer startup state

The producer's first loop state must agree with decoded input, output capacity, and its initial
writer prefix. This module establishes those state and frame facts so subsequent clause emission
can start from a stable invariant.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral encodeThreeCNF)


lemma uniform_header_room (φ : CNF) :
    uniformStartNat + (toThreeCNF φ).numVars + (toThreeCNF φ).clauses.length + 2 <
      uniformMNat (encodeCNF φ).length + uctCurJ := by
  have hcap := uniform_capacity_of_encodeCNF φ
  have henc := encodeThreeCNF_toThreeCNF_length_le φ
  have : (toThreeCNF φ).numVars + (toThreeCNF φ).clauses.length + 2 ≤
      (encodeThreeCNF (toThreeCNF φ)).length := by
    simp [encodeThreeCNF, encodeList, List.length_append, encodeNat_length]
    omega
  omega

lemma uniform_rewind_eval (φ : CNF) (σ : Store)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hbase : σ uctInputBaseReg = uniformAddrNat (encodeCNF φ).length)
    (hbits : BitsFrom σ (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ)) :
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ uctCursorReg =
      uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1 ∧
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ uctOuterReg = φ.clauses.length ∧
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ uctDoneReg = 1 ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg →
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σ r = σ r) := by
  set N := (encodeCNF φ).length
  have heq := secondPassRewindProgramAt_eq uctCursorReg uctInputBaseReg uctOuterReg
    uctDoneReg uctSavedBoundReg N σ hN (by decide) (by decide) (by decide)
  have haddr := uniformAddrNat_ge_25 N
  have hbelow :
      uctCursorReg < uniformAddrNat N ∧ uctInputBaseReg < uniformAddrNat N ∧
        uctOuterReg < uniformAddrNat N ∧ uctDoneReg < uniformAddrNat N := by
    simp [uctCursorReg, uctInputBaseReg, uctOuterReg, uctDoneReg]
    omega
  have hbits' : BitsFrom σ (uniformAddrNat N) (encodeList encodeClause φ.clauses) := by
    simpa [encodeCNF, N] using hbits
  have hrew := secondPassRewindProgram_eval encodeClause uctCursorReg uctInputBaseReg
    uctOuterReg uctDoneReg N (uniformAddrNat N) φ.clauses ([] : Bits) σ
    (by decide) (by decide) (by decide) hbelow hbase
    (encodeCNF_length_ge_clauseCount φ) (by simpa using hbits')
  simpa [heq] using hrew

lemma uniformEmitAuxInitProg_frame (σ : Store) {r : ℕ}
    (hp : r ≠ uctPosPolReg) (hn : r ≠ uctNegPolReg) :
    uniformEmitAuxInitProg.eval σ r = σ r :=
  (by decide +kernel : uniformEmitAuxInitProg.Avoids
    (fun x => x ≠ uctPosPolReg ∧ x ≠ uctNegPolReg)).eval_frame σ ⟨hp, hn⟩

lemma uniformFreshFromMaxProg_frame (σ : Store) {r : ℕ}
    (hf : r ≠ uctFreshReg) :
    uniformFreshFromMaxProg.eval σ r = σ r :=
  (by decide +kernel : uniformFreshFromMaxProg.Avoids (· ≠ uctFreshReg)).eval_frame σ hf

lemma uniform_startup_cnfEmissionState (φ : CNF) (σ : Store)
    (h0 : σ 0 = uniformMNat (encodeCNF φ).length)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hbase : σ uctInputBaseReg = uniformAddrNat (encodeCNF φ).length)
    (hnum : σ uctFreshReg = (toThreeCNF φ).numVars)
    (hcount : σ uctCountReg = (toThreeCNF φ).clauses.length)
    (hbits : BitsFrom σ (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ)) :
    CNFEmissionState
      ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ)
      (uniformMNat (encodeCNF φ).length) uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++
        encodeNat (toThreeCNF φ).clauses.length)
      uctCursorReg uctOuterReg uctFreshReg
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      φ.clauses.length (toThreeCNF φ).numVars := by
  set N := (encodeCNF φ).length
  set M := uniformMNat N
  set start := uniformStartNat
  set numVars := (toThreeCNF φ).numVars
  set threeCount := (toThreeCNF φ).clauses.length
  have hrew := uniform_rewind_eval φ σ hN hbase hbits
  set σr :=
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ
  have h0r : σr 0 = M :=
    (hrew.2.2.2 0 (by decide) (by decide) (by decide)).trans h0
  have hnumR : σr uctFreshReg = numVars :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hnum
  have hcountR : σr uctCountReg = threeCount :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hcount
  have heq := secondPassStartupProgramAt_eq_uniformStartE uctCursorReg
    uctInputBaseReg uctOuterReg uctDoneReg N uctCurJ uctTmpJ
    uctFreshReg uctCountReg σ hN (by decide) (by decide) (by decide)
  have hstartR : uniformStartE.eval σr = start := uniformStartE_eval σr
  set σi := (ctlAssign uctCurJ uniformStartE).eval σr
  have h0I : σi 0 = M := (ctlAssign_zero uctCurJ uniformStartE σr (by decide)).trans h0r
  have hcurI : σi (M + uctCurJ) = start := by
    have h := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, hstartR] at h
    simpa [σi, uctCurJ] using h
  have hsInit : WriterInit M uctCurJ start σi :=
    writerInit_mk M uctCurJ start σi h0I hcurI (by simp [start, uniformStartNat,
      relocateControlGap]) (uniform_layout_start_lt_M N)
  have hMge : 100 ≤ M := by
    simp [M, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
  have hneCtl (r : ℕ) (hr : r ≤ 24) : r ≠ M + uctCurJ := by
    simp [uctCurJ]; omega
  have hltStart (r : ℕ) (hr : r ≤ 24) : r < start := by
    simp [start, uniformStartNat, relocateControlGap]; omega
  have hnumI : σi uctFreshReg = numVars :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg
      (by rw [h0r]; exact hneCtl _ (by decide))).trans hnumR
  have hcountI : σi uctCountReg = threeCount :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg
      (by rw [h0r]; exact hneCtl _ (by decide))).trans hcountR
  have hroom := uniform_header_room φ
  have hhead := writerAppendHeaderProg_eval M uctCurJ uctTmpJ start []
    uctFreshReg uctCountReg numVars threeCount σi (by decide) (by decide)
    hnumI hcountI (by simp [start, uniformStartNat, uctCountReg, relocateControlGap])
    hsInit (by simpa [List.length_nil] using hroom)
  have hseq :
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ =
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi := by
    unfold secondPassStartupProgramAt
    simp [eval_seq, σr, σi]
  have hcurF :
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi
        uctCursorReg = uniformAddrNat N + φ.clauses.length + 1 := by
    have hfr := writerAppendHeaderProg_frame M uctCurJ uctTmpJ start []
      uctFreshReg uctCountReg numVars threeCount σi (by decide) (by decide)
      hnumI hcountI (by simp [start, uniformStartNat, uctCountReg, relocateControlGap])
      hsInit (by simpa [List.length_nil] using hroom)
      (hltStart uctCursorReg (by decide))
    have hci := ctlAssign_eval_diff uctCurJ uniformStartE σr uctCursorReg
      (by rw [h0r]; exact hneCtl uctCursorReg (by decide))
    exact hfr.trans (hci.trans hrew.1)
  have houtF :
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi
        uctOuterReg = φ.clauses.length := by
    have hfr := writerAppendHeaderProg_frame M uctCurJ uctTmpJ start []
      uctFreshReg uctCountReg numVars threeCount σi (by decide) (by decide)
      hnumI hcountI (by simp [start, uniformStartNat, uctCountReg, relocateControlGap])
      hsInit (by simpa [List.length_nil] using hroom)
      (hltStart uctOuterReg (by decide))
    have hoi := ctlAssign_eval_diff uctCurJ uniformStartE σr uctOuterReg
      (by rw [h0r]; exact hneCtl uctOuterReg (by decide))
    exact hfr.trans (hoi.trans hrew.2.1)
  have hfreshF :
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi
        uctFreshReg = numVars := by
    have hfr := writerAppendHeaderProg_frame M uctCurJ uctTmpJ start []
      uctFreshReg uctCountReg numVars threeCount σi (by decide) (by decide)
      hnumI hcountI (by simp [start, uniformStartNat, uctCountReg, relocateControlGap])
      hsInit (by simpa [List.length_nil] using hroom)
      (hltStart uctFreshReg (by decide))
    exact hfr.trans hnumI
  rw [hseq]
  exact ⟨hhead, hcurF, houtF, hfreshF⟩

lemma writerState_congr {σ σ' : Store} {M curJ start : ℕ} {pref : Bits}
    (hw : WriterState σ M curJ start pref)
    (h0 : σ' 0 = σ 0)
    (hcur : σ' (M + curJ) = σ (M + curJ))
    (hbits : ∀ i, i < pref.length → σ' (start + i) = σ (start + i)) :
    WriterState σ' M curJ start pref :=
  ⟨h0.trans hw.root, hcur.trans hw.cursor,
    bitsAt_of_frame σ σ' start pref hw.bits (fun r hlo hhi => by
      have hi : r - start < pref.length := by omega
      have hr : start + (r - start) = r := by omega
      rw [← hr, hbits _ hi]),
    hw.start_pos, hw.safe⟩

lemma uniformEmitScratchResetProg_frame_ge_start (σ : Store) {r : ℕ}
    (hr : uniformStartNat ≤ r) :
    uniformEmitScratchResetProg.eval σ r = σ r :=
  (by decide +kernel : uniformEmitScratchResetProg.Avoids (uniformStartNat ≤ ·)).eval_frame σ hr

lemma uniformEmitScratchResetProg_cnfEmitRel
    (M curJ tmpJ bound tailBound base : ℕ) (clauses : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg bound tailBound
      base clauses tail pref addr σ) :
    CNFEmitRel M curJ tmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg bound tailBound
      base clauses tail pref addr (uniformEmitScratchResetProg.eval σ) := by
  have hcursor := uniformEmitScratchResetProg_frame σ
    (r := uctCursorReg)
    (by simp [uniformEmitScratchRegs, uctCursorReg, uctPolReg, uctVarReg,
      uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
      uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg]) (by decide) (by decide)
  have houter := uniformEmitScratchResetProg_frame σ
    (r := uctOuterReg)
    (by simp [uniformEmitScratchRegs, uctOuterReg, uctPolReg, uctVarReg,
      uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
      uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg]) (by decide) (by decide)
  have hfresh := uniformEmitScratchResetProg_frame σ
    (r := uctFreshReg)
    (by simp [uniformEmitScratchRegs, uctFreshReg, uctPolReg, uctVarReg,
      uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
      uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg]) (by decide) (by decide)
  have hroot := uniformEmitScratchResetProg_frame σ
    (r := 0) (by decide) (by decide) (by decide)
  have hcell : uniformStartNat ≤ M + curJ := by
    have hs := hrel.writer.safe
    omega
  have hwriter := writerState_congr hrel.writer hroot
    (uniformEmitScratchResetProg_frame_ge_start σ hcell)
    (fun i _ => uniformEmitScratchResetProg_frame_ge_start σ (by omega))
  have hv := uniformEmitScratchResetProg_values σ
  refine ⟨?_, hcursor.trans hrel.cursor, houter.trans hrel.outer,
    hfresh.trans hrel.fresh, hv.2.2.2.2.2.1, hv.2.2.2.2.1, hv.1, hv.2.1,
    hwriter, hrel.capacity, hrel.input_above, hrel.start_at_input, hrel.safety,
    hrel.long_safety, hrel.clause_bound, hrel.literal_bound, hrel.tail_bound_ok⟩
  refine bitsFrom_of_eq_on (σ := σ) ?_ hrel.input
  intro i hi
  have hstart := hrel.start_at_input
  exact uniformEmitScratchResetProg_frame_ge_start σ (by omega)

lemma uniformSetArenaProg_frame (σ : Store) {r : ℕ} (hr : r ≠ 0) :
    uniformSetArenaProg.eval σ r = σ r :=
  (by decide +kernel : uniformSetArenaProg.Avoids (· ≠ 0)).eval_frame σ hr

lemma uniform_decode_bitsFrom (φ : CNF) :
    BitsFrom
      ((decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval
        (uniformControlInitProg.eval
          ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
            (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))))
      (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ) := by
  set bits := encodeCNF φ
  set σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  have hs := uniformControlInitProg_after_cursor bits
  have hbits0 := uniformControlInitProg_bitsFrom bits
  have haddr := uniformAddrNat_ge_25 bits.length
  have hrem0 : σ0 uctRemainingReg = 0 := by
    simpa [σ0] using
      uniformControlInitProg_zero uctRemainingReg _ (by simp [uctControlRegs])
  have hmax0 : σ0 uctMaxReg = 0 := by
    simpa [σ0] using
      uniformControlInitProg_zero uctMaxReg _ (by simp [uctControlRegs])
  have hfresh0 : σ0 uctFreshReg = 0 := by
    simpa [σ0] using
      uniformControlInitProg_zero uctFreshReg _ (by simp [uctControlRegs])
  have hcount0 : σ0 uctCountReg = 0 := by
    simpa [σ0] using
      uniformControlInitProg_zero uctCountReg _ (by simp [uctControlRegs])
  have hseen0 : σ0 uctSeenReg = 0 := by
    simpa [σ0] using
      uniformControlInitProg_zero uctSeenReg _ (by simp [uctControlRegs])
  have hlists : BitsFrom σ0 (uniformAddrNat bits.length)
      (encodeList (encodeList encodeLiteral)
        (φ.clauses.map (fun c => c.lits)) ++ ([] : Bits)) := by
    simpa [σ0, bits, encodeCNF_eq_lists, List.append_nil] using hbits0
  refine bitsFrom_of_eq_on ?_ hbits0
  intro i hi
  exact decodeCNFProgramAtSeen_uct_frame_ge bits.length
    (φ.clauses.map (fun c => c.lits)) ([] : Bits)
    (uniformAddrNat bits.length) 0 0 0 0 σ0
    (by simpa using encodeCNF_length_ge_clauseCount φ) haddr hs.2.2.1
    hrem0 hmax0 hfresh0 hcount0 hseen0 hs.1 (encodeCNF_scan_bounds φ) hlists
    _ (by have := uniformAddrNat_ge_25 bits.length; omega)

end NPComplete.CookLevin

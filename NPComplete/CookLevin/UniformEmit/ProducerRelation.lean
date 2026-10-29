module

public import NPComplete.CookLevin.UniformEmit.StartupState

/-!
# Producer startup relation

The emitter can start only after encoded CNF data and writer state have been related to the abstract
clause stream. This module establishes that startup relation so the outer loop can reason from a
precise post-initialization invariant.
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


/-- Saving the bound and setting the arena only change registers `0` and `uctSavedBoundReg`. -/
lemma uniform_producer_pre_startup_arena_frame (σ : Store) {r : ℕ} (h0 : r ≠ 0)
    (hs : r ≠ uctSavedBoundReg) :
    (uniformSetArenaProg.eval (uniformSaveBoundProg.eval σ)) r = σ r :=
  (uniformSetArenaProg_frame _ h0).trans ((uniformSaveBoundProg_eval σ).2 r hs)

/-- The decode phase leaves the bound cell `0` and the input base register at their start values;
these two cells feed the arena setup. -/
lemma uniform_producer_pre_startup_decode_cells (φ : CNF) :
    let σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))
    let σd :=
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0
    σd 0 = (encodeCNF φ).length ∧
    σd uctInputBaseReg = uniformAddrNat (encodeCNF φ).length := by
  intro σ0 σd
  have hs := uniformControlInitProg_after_cursor (encodeCNF φ)
  have hz : ∀ r, r ∈ uctControlRegs → σ0 r = 0 := fun r hr =>
    uniformControlInitProg_zero r _ hr
  have hfr := decodeCNFProgramAtSeen_uct_append (encodeCNF φ).length
    (φ.clauses.map (fun c => c.lits)) ([] : Bits) (uniformAddrNat (encodeCNF φ).length)
    0 0 0 0 σ0
    (by simpa using encodeCNF_length_ge_clauseCount φ)
    (uniformAddrNat_ge_25 _) hs.2.2.1
    (hz _ (by simp [uctControlRegs])) (hz _ (by simp [uctControlRegs]))
    (hz _ (by simp [uctControlRegs])) (hz _ (by simp [uctControlRegs]))
    (hz _ (by simp [uctControlRegs])) hs.1 (encodeCNF_scan_bounds φ)
    (by simpa [σ0, encodeCNF_eq_lists, List.append_nil] using
      uniformControlInitProg_bitsFrom (encodeCNF φ))
  refine ⟨hfr.2.2.2.2.2.2.1, ?_⟩
  exact (hfr.2.2.2.2.2.2.2 uctInputBaseReg (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs.2.1

lemma uniform_producer_pre_startup (φ : CNF) :
    let bits := encodeCNF φ
    let N := bits.length
    let σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    let σd :=
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0
    let σp := uniformPostDecodeStatsProg.eval σd
    let σs := uniformSaveBoundProg.eval σp
    let σa := uniformSetArenaProg.eval σs
    σa 0 = uniformMNat N ∧
    σa uctSavedBoundReg = N ∧
    σa uctInputBaseReg = uniformAddrNat N ∧
    σa uctFreshReg = (toThreeCNF φ).numVars ∧
    σa uctCountReg = (toThreeCNF φ).clauses.length ∧
    σa uctMaxReg = cnfVarBound φ ∧
    BitsFrom σa (uniformAddrNat N) bits := by
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
  have hp := uniformPostDecodeStatsProg_zero_seed φ
  have hnv : σp uctFreshReg = (toThreeCNF φ).numVars := by
    have h := hp.2.1
    have hadd := cnfFreshBaseStat_add (cnfVarBound φ)
      (φ.clauses.map (fun c => c.lits))
    have hto := cnfFreshBaseStat_toThreeCNF φ
    simpa [σp, σd, σ0, bits, N, hadd.symm, hto] using h
  have hmaxp : σp uctMaxReg = cnfVarBound φ := by
    simpa [σp, σd, σ0, bits, N] using hp.1
  have hcount0 :=
    (decodeCNFProgramAtSeen_uct_encodeCNF_zero_seed φ).2.2.1
  have hcountp : σp uctCountReg = (toThreeCNF φ).clauses.length := by
    have hfr := uniformPostDecodeStatsProg_frame σd (r := uctCountReg)
      (by decide) (by decide) (by decide)
    have hto := cnfThreeCountStat_toThreeCNF φ
    simpa [σp, σd, σ0, bits, N, hto] using hfr.trans hcount0
  obtain ⟨h0d, hbased⟩ := uniform_producer_pre_startup_decode_cells φ
  have hbasep : σp uctInputBaseReg = uniformAddrNat N :=
    (uniformPostDecodeStatsProg_frame σd (r := uctInputBaseReg)
      (by decide) (by decide) (by decide)).trans hbased
  have h0p : σp 0 = N :=
    (uniformPostDecodeStatsProg_frame σd (r := 0)
      (by decide) (by decide) (by decide)).trans h0d
  have hsa := uniform_save_set_arena_savedBound σp N h0p
  have hbasea : σa uctInputBaseReg = uniformAddrNat N :=
    (uniform_producer_pre_startup_arena_frame σp (by decide) (by decide)).trans hbasep
  have hfresha : σa uctFreshReg = (toThreeCNF φ).numVars :=
    (uniform_producer_pre_startup_arena_frame σp (by decide) (by decide)).trans hnv
  have hcounta : σa uctCountReg = (toThreeCNF φ).clauses.length :=
    (uniform_producer_pre_startup_arena_frame σp (by decide) (by decide)).trans hcountp
  have hmaxa : σa uctMaxReg = cnfVarBound φ :=
    (uniform_producer_pre_startup_arena_frame σp (by decide) (by decide)).trans hmaxp
  have hbitsa : BitsFrom σa (uniformAddrNat N) bits := by
    refine bitsFrom_of_eq_on ?_ (uniform_decode_bitsFrom φ)
    intro i hi
    have had : 25 ≤ uniformAddrNat N + i := by
      have := uniformAddrNat_ge_25 N; omega
    have hd := uniformPostDecodeStatsProg_frame σd (r := uniformAddrNat N + i)
      (by simp [uctTmpReg]; omega) (by simp [uctMaxReg]; omega)
      (by simp [uctFreshReg]; omega)
    have ha := uniform_producer_pre_startup_arena_frame σp (r := uniformAddrNat N + i)
      (by omega) (by simp [uctSavedBoundReg]; omega)
    exact ha.trans hd
  have h0a : σa 0 = uniformMNat N := by
    have hsN : σs uctSavedBoundReg = N := (uniformSaveBoundProg_eval σp).1.trans h0p
    have hme : uniformME.eval σs = uniformMNat N := uniformME_eval σs N hsN
    simpa [σa] using (uniformSetArenaProg_eval σs).trans hme
  exact ⟨h0a, hsa.1, hbasea, hfresha, hcounta, hmaxa, hbitsa⟩

lemma uniform_startup_preserves_max (φ : CNF) (σ : Store)
    (h0 : σ 0 = uniformMNat (encodeCNF φ).length)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hbase : σ uctInputBaseReg = uniformAddrNat (encodeCNF φ).length)
    (hnum : σ uctFreshReg = (toThreeCNF φ).numVars)
    (hcount : σ uctCountReg = (toThreeCNF φ).clauses.length)
    (hbits : BitsFrom σ (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ)) :
    ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
      uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
      uctFreshReg uctCountReg).eval σ) uctMaxReg = σ uctMaxReg := by
  set N := (encodeCNF φ).length
  set M := uniformMNat N
  have hrew := uniform_rewind_eval φ σ hN hbase hbits
  set σr :=
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ
  have h0r : σr 0 = M :=
    (hrew.2.2.2 0 (by decide) (by decide) (by decide)).trans h0
  have hmaxr : σr uctMaxReg = σ uctMaxReg :=
    hrew.2.2.2 uctMaxReg (by decide) (by decide) (by decide)
  have hnumR : σr uctFreshReg = (toThreeCNF φ).numVars :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hnum
  have hcountR : σr uctCountReg = (toThreeCNF φ).clauses.length :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hcount
  have hseq :
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ =
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval
        ((ctlAssign uctCurJ uniformStartE).eval σr) := by
    unfold secondPassStartupProgramAt
    simp [eval_seq, σr]
  rw [hseq]
  set σi := (ctlAssign uctCurJ uniformStartE).eval σr
  have h0I : σi 0 = M := (ctlAssign_zero uctCurJ uniformStartE σr (by decide)).trans h0r
  have hstartR : uniformStartE.eval σr = uniformStartNat := uniformStartE_eval σr
  have hcurI : σi (M + uctCurJ) = uniformStartNat := by
    have h := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, hstartR] at h
    simpa [σi, uctCurJ] using h
  have hsInit := writerInit_mk M uctCurJ uniformStartNat σi h0I hcurI
    (by simp [uniformStartNat, relocateControlGap]) (uniform_layout_start_lt_M N)
  have hMge : 100 ≤ M := by
    simp [M, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
  have hne : uctMaxReg ≠ M + uctCurJ := by simp [uctCurJ, uctMaxReg]; omega
  have hctl : σi uctMaxReg = σr uctMaxReg :=
    ctlAssign_eval_diff uctCurJ uniformStartE σr uctMaxReg (by rw [h0r]; exact hne)
  have hnumI : σi uctFreshReg = (toThreeCNF φ).numVars :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg
      (by rw [h0r]; simp [uctCurJ, uctFreshReg]; omega)).trans hnumR
  have hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg
      (by rw [h0r]; simp [uctCurJ, uctCountReg]; omega)).trans hcountR
  have hfr : (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi
      uctMaxReg = σi uctMaxReg :=
    writerAppendHeaderProg_frame M uctCurJ uctTmpJ uniformStartNat []
      uctFreshReg uctCountReg (toThreeCNF φ).numVars (toThreeCNF φ).clauses.length
      σi (by decide) (by decide) hnumI hcountI
      (by simp [uniformStartNat, uctCountReg, relocateControlGap]) hsInit
      (by simpa [List.length_nil] using uniform_header_room φ)
      (by simp [uctMaxReg, uniformStartNat, relocateControlGap])
  exact hfr.trans (hctl.trans hmaxr)

lemma encodeThreeCNF_payload_split (φ : CNF) :
    (encodeNat (toThreeCNF φ).numVars ++
        encodeNat (toThreeCNF φ).clauses.length).length +
      (encodeThreeClausesPayload (toThreeCNF φ).clauses).length =
      (encodeThreeCNF (toThreeCNF φ)).length := by
  simp [encodeThreeCNF, encodeList, encodeThreeClausesPayload, List.length_append,
    encodeNat_length, List.length_flatten]
  ac_rfl

lemma clausesToThree_toThreeCNF (φ : CNF) :
    (clausesToThree (cnfVarBound φ) φ.clauses).1 = (toThreeCNF φ).clauses := by
  simp [toThreeCNF]

lemma uniform_startup_bitsFrom_flatten (φ : CNF) (σ : Store)
    (h0 : σ 0 = uniformMNat (encodeCNF φ).length)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hbase : σ uctInputBaseReg = uniformAddrNat (encodeCNF φ).length)
    (hnum : σ uctFreshReg = (toThreeCNF φ).numVars)
    (hcount : σ uctCountReg = (toThreeCNF φ).clauses.length)
    (hbits : BitsFrom σ (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ)) :
    BitsFrom
      ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (φ.clauses.map encodeClause).flatten := by
  set N := (encodeCNF φ).length
  set M := uniformMNat N
  set addr := uniformAddrNat N + φ.clauses.length + 1
  have hflat := bitsFrom_encodeCNF_flatten φ σ (uniformAddrNat N) hbits
  have hrew := uniform_rewind_eval φ σ hN hbase hbits
  set σr :=
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ
  have h0r : σr 0 = M :=
    (hrew.2.2.2 0 (by decide) (by decide) (by decide)).trans h0
  have hnumR : σr uctFreshReg = (toThreeCNF φ).numVars :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hnum
  have hcountR : σr uctCountReg = (toThreeCNF φ).clauses.length :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hcount
  have hseq :
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ =
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval
        ((ctlAssign uctCurJ uniformStartE).eval σr) := by
    unfold secondPassStartupProgramAt
    simp [eval_seq, σr]
  rw [hseq]
  set σi := (ctlAssign uctCurJ uniformStartE).eval σr
  have h0I : σi 0 = M := (ctlAssign_zero uctCurJ uniformStartE σr (by decide)).trans h0r
  have hstartR : uniformStartE.eval σr = uniformStartNat := uniformStartE_eval σr
  have hcurI : σi (M + uctCurJ) = uniformStartNat := by
    have h := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, hstartR] at h
    simpa [σi, uctCurJ] using h
  have hsInit := writerInit_mk M uctCurJ uniformStartNat σi h0I hcurI
    (by simp [uniformStartNat, relocateControlGap]) (uniform_layout_start_lt_M N)
  have hMge : 100 ≤ M := by
    simp [M, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
  have hnumI : σi uctFreshReg = (toThreeCNF φ).numVars :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg
      (by rw [h0r]; simp [uctCurJ, uctFreshReg]; omega)).trans hnumR
  have hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg
      (by rw [h0r]; simp [uctCurJ, uctCountReg]; omega)).trans hcountR
  refine bitsFrom_of_eq_on ?_ hflat
  intro i hi
  have hhi : M + uctTmpJ < addr + i := by
    have hlt := uniformMNat_add_two_lt_addr N
    simp [addr, uctTmpJ, M]
    omega
  have hhead := writerAppendHeaderProg_frame_high M uctCurJ uctTmpJ uniformStartNat []
    uctFreshReg uctCountReg (toThreeCNF φ).numVars (toThreeCNF φ).clauses.length
    σi (by decide) (by decide) hnumI hcountI
    (by simp [uniformStartNat, uctCountReg, relocateControlGap]) hsInit
    (by simpa [List.length_nil] using uniform_header_room φ) hhi
  have hctl : σi (addr + i) = σr (addr + i) :=
    ctlAssign_eval_diff uctCurJ uniformStartE σr (addr + i)
      (by
        rw [h0r]
        have : M + uctCurJ < addr + i := by
          simp [uctCurJ, uctTmpJ] at hhi ⊢; omega
        omega)
  have hrw : σr (addr + i) = σ (addr + i) :=
    hrew.2.2.2 (addr + i)
      (by
        have := uniformAddrNat_ge_25 N
        simp [uctCursorReg, addr]; omega)
      (by
        have := uniformAddrNat_ge_25 N
        simp [uctOuterReg, addr]; omega)
      (by
        have := uniformAddrNat_ge_25 N
        simp [uctDoneReg, addr]; omega)
  exact hhead.trans (hctl.trans hrw)

/-- Capacity of the uniform producer at the clause-emission start, phrased with the
header prefix as a single list so the startup bridge can consume it directly. -/
lemma uniform_producer_startup_aux_capacity (φ : CNF) :
    uniformStartNat +
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length).length +
      (encodeThreeClausesPayload (clausesToThree (cnfVarBound φ) φ.clauses).1).length + 2 <
        uniformMNat (encodeCNF φ).length + uctCurJ := by
  have hsplit := encodeThreeCNF_payload_split φ
  have hC := uniform_capacity_of_encodeCNF φ
  have hCs : (encodeThreeClausesPayload (clausesToThree (cnfVarBound φ) φ.clauses).1).length =
      (encodeThreeClausesPayload (toThreeCNF φ).clauses).length := by
    rw [clausesToThree_toThreeCNF]
  have hsplit' : (encodeNat (toThreeCNF φ).numVars ++
      encodeNat (toThreeCNF φ).clauses.length).length +
      (encodeThreeClausesPayload (clausesToThree (cnfVarBound φ) φ.clauses).1).length =
      (encodeThreeCNF (toThreeCNF φ)).length := by
    rw [hCs]; exact hsplit
  have hpn := encodeNat_length (toThreeCNF φ).numVars
  have hpc := encodeNat_length (toThreeCNF φ).clauses.length
  have hsum : (encodeNat (toThreeCNF φ).numVars ++
      encodeNat (toThreeCNF φ).clauses.length).length =
      (toThreeCNF φ).numVars + 1 + ((toThreeCNF φ).clauses.length + 1) := by
    rw [List.length_append, hpn, hpc]
  omega

/-- The emit-aux init keeps the writer state produced by startup. -/
lemma uniform_producer_emit_aux_init_writer {φ : CNF} {σst : Store}
    (hst : CNFEmissionState σst (uniformMNat (encodeCNF φ).length) uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      uctCursorReg uctOuterReg uctFreshReg
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      φ.clauses.length (toThreeCNF φ).numVars) :
    WriterState (uniformEmitAuxInitProg.eval σst) (uniformMNat (encodeCNF φ).length)
      uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length) :=
  writerState_congr hst.writer
    (uniformEmitAuxInitProg_frame σst (by decide) (by decide))
    (uniformEmitAuxInitProg_frame σst
      (by simp [uctPosPolReg, uctCurJ, uniformMNat, uniformStartNat, uniformSlackNat,
        relocateControlGap]; omega)
      (by simp [uctNegPolReg, uctCurJ, uniformMNat, uniformStartNat, uniformSlackNat,
        relocateControlGap]; omega))
    (fun i _ => uniformEmitAuxInitProg_frame σst
      (by simp [uctPosPolReg, uniformStartNat, relocateControlGap]; omega)
      (by simp [uctNegPolReg, uniformStartNat, relocateControlGap]; omega))

/-- The fresh-base reset (`uniformFreshFromMaxProg`) preserves an existing writer state. -/
lemma uniform_producer_startup_aux_writer {φ : CNF} {σx : Store}
    (hwx : WriterState σx (uniformMNat (encodeCNF φ).length) uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)) :
    WriterState (uniformFreshFromMaxProg.eval σx) (uniformMNat (encodeCNF φ).length)
      uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length) :=
  writerState_congr hwx
    (uniformFreshFromMaxProg_frame σx (by decide))
    (uniformFreshFromMaxProg_frame σx
      (by simp [uctFreshReg, uctCurJ, uniformMNat, uniformStartNat, uniformSlackNat,
        relocateControlGap]; omega))
    (fun i _ => uniformFreshFromMaxProg_frame σx
      (by simp [uctFreshReg, uniformStartNat, relocateControlGap]; omega))

/-- The state after the emit-aux init and the fresh-base reset: writer state kept,
polarities canonical, cursor and remaining count from startup, fresh base the max. -/
lemma uniform_producer_startup_aux_state (φ : CNF) :
    let bits := encodeCNF φ
    let N := bits.length
    let σa := uniformSetArenaProg.eval (uniformSaveBoundProg.eval
      (uniformPostDecodeStatsProg.eval
        ((decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg).eval
        (uniformControlInitProg.eval
          ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
            (uniformRelocateProg.eval (bitInputStore bits)))))))
    let σst :=
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa
    let σx := uniformEmitAuxInitProg.eval σst
    let σf := uniformFreshFromMaxProg.eval σx
    WriterState σf (uniformMNat N) uctCurJ uniformStartNat
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length) ∧
    σf uctCursorReg = uniformAddrNat N + φ.clauses.length + 1 ∧
    σf uctOuterReg = φ.clauses.length ∧
    σf uctFreshReg = cnfVarBound φ ∧
    σf uctPosPolReg = 0 ∧ σf uctNegPolReg = 1 ∧
    BitsFrom σf (uniformAddrNat N + φ.clauses.length + 1)
      (φ.clauses.map encodeClause).flatten := by
  intro bits N σa σst σx σf
  set σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  set σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  set σp := uniformPostDecodeStatsProg.eval σd
  set σs := uniformSaveBoundProg.eval σp
  have hpre := uniform_producer_pre_startup φ
  have hst := uniform_startup_cnfEmissionState φ σa hpre.1 hpre.2.1 hpre.2.2.1
    hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.2
  have hmaxst : σst uctMaxReg = cnfVarBound φ :=
    (uniform_startup_preserves_max φ σa hpre.1 hpre.2.1 hpre.2.2.1
      hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.2).trans hpre.2.2.2.2.2.1
  have hwx := uniform_producer_emit_aux_init_writer (φ := φ) hst
  refine ⟨uniform_producer_startup_aux_writer hwx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (uniformFreshFromMaxProg_frame σx (by decide)).trans
      ((uniformEmitAuxInitProg_frame σst (by decide) (by decide)).trans
        hst.input_cursor)
  · exact (uniformFreshFromMaxProg_frame σx (by decide)).trans
      ((uniformEmitAuxInitProg_frame σst (by decide) (by decide)).trans
        hst.clauses_remaining)
  · exact (uniformFreshFromMaxProg_eval σx).trans
      ((uniformEmitAuxInitProg_frame σst (by decide) (by decide)).trans hmaxst)
  · exact (uniformFreshFromMaxProg_frame σx (by decide)).trans
      (uniformEmitAuxInitProg_eval σst).1
  · exact (uniformFreshFromMaxProg_frame σx (by decide)).trans
      (uniformEmitAuxInitProg_eval σst).2
  · have hstB := uniform_startup_bitsFrom_flatten φ σa hpre.1 hpre.2.1 hpre.2.2.1
      hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.2
    refine bitsFrom_of_eq_on ?_ hstB
    intro i hi
    have hge : 25 ≤ uniformAddrNat N + φ.clauses.length + 1 + i := by
      have := uniformAddrNat_ge_25 N; omega
    exact (uniformFreshFromMaxProg_frame σx (by simp [uctFreshReg]; omega)).trans
      (uniformEmitAuxInitProg_frame σst (by simp [uctPosPolReg]; omega)
        (by simp [uctNegPolReg]; omega))

lemma uniform_producer_cnfEmitRel (φ : CNF) :
    let bits := encodeCNF φ
    let N := bits.length
    let σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    let σd :=
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0
    let σp := uniformPostDecodeStatsProg.eval σd
    let σs := uniformSaveBoundProg.eval σp
    let σa := uniformSetArenaProg.eval σs
    let σst :=
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa
    let σx := uniformEmitAuxInitProg.eval σst
    let σf := uniformFreshFromMaxProg.eval σx
    CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
      (cnfVarBound φ) φ.clauses []
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      (uniformAddrNat N + φ.clauses.length + 1)
      (uniformEmitResetProg.eval σf) := by
  intro bits N σ0 σd σp σs σa σst σx σf
  obtain ⟨hwf, hcurf, houterf, hfreshf, hpos, hneg, hbitsf⟩ :=
    uniform_producer_startup_aux_state φ
  exact cnfEmitRel_after_startup_reset (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
    uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
    (cnfVarBound φ) φ.clauses []
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    (uniformAddrNat N + φ.clauses.length + 1) σf
    ⟨hwf, hcurf, houterf, hfreshf⟩ (by simpa using hbitsf) hpos hneg
    (uniform_flatten_addr_inputAbove N φ.clauses.length)
    (uniformStartNat_le_uniformAddrNat_add_n_add_one N φ.clauses.length)
    (uniform_flatten_addr_gt_length_done N φ.clauses.length)
    uniform_clauseEmitSafety uniform_longClauseRegisterSafety
    (by
      have h := uniform_producer_startup_aux_capacity φ
      simpa using h)
    (fun c hc => encodeCNF_clause_lits_bound φ c hc)
    (fun c hc l hl => encodeCNF_literal_var_bound φ c hc l hl)
    (fun c hc => Nat.le_of_succ_le (encodeCNF_clause_lits_bound φ c hc))

end NPComplete.CookLevin

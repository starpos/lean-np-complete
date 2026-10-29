module

public import NPComplete.CookLevin.UniformPackaging.DecodeOuterBounds
public import NPComplete.CookLevin.UniformPackaging.DispatchShortBounds

/-!
# Producer setup bounds

Before clause emission begins, the program relocates and decodes its input and
initializes the writer state. This module proves bounds for that setup sequence
and transfers them to the complete producer from setup-level hypotheses.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma uniform_producer_decode_prefix_bounded
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    let bits := encodeCNF φ
    let σI := bitInputStore bits
    let σR := uniformRelocateProg.eval σI
    let σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
    let σ0 := uniformControlInitProg.eval σC
    let decoder := decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg
    let σd := decoder.eval σ0
    ProgramBoundedIn B σI uniformRelocateProg ∧
      ProgramBoundedIn B σR (uniformCursorInitProg uctCursorReg uctInputBaseReg) ∧
      ProgramBoundedIn B σC uniformControlInitProg ∧
      ProgramBoundedIn B σ0 decoder ∧ StoreValuesLe B σd := by
  dsimp only
  let bits := encodeCNF φ
  let N := bits.length
  let σI := bitInputStore bits
  let σR := uniformRelocateProg.eval σI
  let σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
  let σ0 := uniformControlInitProg.eval σC
  let decoder := decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
    uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
    uctBoundReg uctSeenReg
  let σd := decoder.eval σ0
  have hB25 : 25 ≤ B :=
    (uniformEmitDispatchEnvelope_ge_25 N).trans (by simpa [N, bits] using hB)
  have hB1 : 1 ≤ B := by omega
  have hN : N ≤ B := by
    exact (uniform_emit_n_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans
        (by simpa [N, bits] using hB))
  have hσI : StoreValuesLe B σI := by
    intro r
    cases r with
    | zero =>
        change N ≤ B
        exact hN
    | succ r =>
        simp [σI, bits, bitInputStore]
        split <;> omega
  have hreloc : ProgramBoundedIn B σI uniformRelocateProg := by
    simpa [σI, bits] using programBoundedIn_uniformRelocateProg_of_input φ B hB
  have hσR : StoreValuesLe B σR := by
    exact program_eval_storeValuesLe σI uniformRelocateProg hB1 hσI hreloc
      scanFree_uniformRelocateProg
  have h0R : σR 0 = N := by
    simpa [σR, σI, bits, N] using (uniformRelocateProg_bitInputStore bits).1
  have haddrE : ExprBoundedIn B σR uniformAddrE := by
    apply exprBoundedIn_uniformAddrE_of_input φ B σR
    · exact h0R
    · exact hB
  have hcursor : ProgramBoundedIn B σR
      (uniformCursorInitProg uctCursorReg uctInputBaseReg) :=
    programBoundedIn_uniformCursorInitProg_of_bounds B σR hB25 haddrE
  have hσC : StoreValuesLe B σC := by
    exact program_eval_storeValuesLe σR _ hB1 hσR hcursor
      (scanFree_uniformCursorInitProg _ _)
  have hcontrol : ProgramBoundedIn B σC uniformControlInitProg :=
    programBoundedIn_uniformControlInitProg B σC hB25
  have hσ0 : StoreValuesLe B σ0 := by
    exact program_eval_storeValuesLe σC _ hB1 hσC hcontrol scanFree_uniformControlInitProg
  have hdecode : ProgramBoundedIn B σ0 decoder := by
    simpa [decoder, σ0, σC, σR, σI, bits, N] using
      programBoundedIn_decodeCNFProgramAtSeen_of_input φ B hB
  have hσd : StoreValuesLe B σd := by
    exact program_eval_storeValuesLe σ0 decoder hB1 hσ0 hdecode
      (by simpa [decoder] using scanFree_decodeCNFProgramAtSeen _ _ _ _ _ _ _ _ _ _ _ _ _)
  exact ⟨hreloc, hcursor, hcontrol, hdecode, hσd⟩

lemma programBoundedIn_uniform_second_pass_rewind_of_pre_startup
    (φ : CNF) (B : ℕ) (σ : Store)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (hpre : UniformProducerPreStartupFacts φ (encodeCNF φ).length σ) :
    ProgramBoundedIn B σ
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg) := by
  let N := (encodeCNF φ).length
  let K := uniformEmitTightEnvelope N
  let τc := (Program.assign uctCursorReg (.reg uctInputBaseReg)).eval σ
  let τd := (Program.assign uctDoneReg (.const 0)).eval τc
  let τo := (Program.assign uctOuterReg (.const 0)).eval τd
  have hB25 : 25 ≤ B :=
    (uniformEmitDispatchEnvelope_ge_25 N).trans (by simpa [N] using hB)
  have hN : N ≤ B :=
    (uniform_emit_n_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans (by simpa [N] using hB))
  have hKtoB : K ≤ B :=
    (uniformEmitTightEnvelope_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans (by simpa [N] using hB))
  have hcursorIdx : uctCursorReg ≤ B := by
    have : 1 ≤ B := by omega
    simpa [uctCursorReg] using this
  have hinputIdx : uctInputBaseReg ≤ B := by
    have : 12 ≤ B := by omega
    simpa [uctInputBaseReg] using this
  have hdoneIdx : uctDoneReg ≤ B := by
    have : 4 ≤ B := by omega
    simpa [uctDoneReg] using this
  have houterIdx : uctOuterReg ≤ B := by
    have : 5 ≤ B := by omega
    simpa [uctOuterReg] using this
  unfold secondPassRewindProgramAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨⟨hcursorIdx, hinputIdx⟩, ?_⟩
  refine ⟨⟨hdoneIdx, by simp⟩, ?_⟩
  refine ⟨⟨houterIdx, by simp⟩, ?_⟩
  change ProgramBoundedIn B τo
    (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctSavedBoundReg)
  have hbase : σ uctInputBaseReg = uniformAddrNat N := by
    simpa [N] using hpre.inputBase
  have hsaved : σ uctSavedBoundReg = N := by
    simpa [N] using hpre.savedBound
  have hc : τo uctCursorReg = uniformAddrNat N := by
    simpa [τo, τd, τc, eval_assign, Expr.eval, writeReg,
      uctCursorReg, uctOuterReg, uctDoneReg] using hbase
  have hb : τo uctSavedBoundReg = N := by
    simp [τo, τd, τc, eval_assign, Expr.eval, writeReg,
      uctSavedBoundReg, uctOuterReg, uctDoneReg, uctCursorReg]
    simpa [uctSavedBoundReg] using hsaved
  have ho : τo uctOuterReg = 0 := by
    simp [τo, τd, τc, eval_assign, Expr.eval]
  have hsavedIdx : uctSavedBoundReg ≤ B := by
    have : 23 ≤ B := by omega
    simpa [uctSavedBoundReg] using this
  exact programBoundedIn_decodeNatProgramAt_of_bounds uctCursorReg uctOuterReg
    uctDoneReg uctSavedBoundReg B τo (by decide) (by decide) (by decide)
    ⟨hcursorIdx, houterIdx, hdoneIdx, hsavedIdx⟩
    (by
      rw [hc, hb]
      have hC : uniformAddrNat N + N ≤ B :=
        (uniform_split_tail_input_end_le_tight N).trans hKtoB
      omega)
    (by rw [ho, hb]; omega)

lemma programBoundedIn_uniform_second_pass_startup_of_pre_startup
    (φ : CNF) (B : ℕ) (σ : Store)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (hpre : UniformProducerPreStartupFacts φ (encodeCNF φ).length σ) :
    ProgramBoundedIn B σ
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg) := by
  let N := (encodeCNF φ).length
  let K := uniformEmitTightEnvelope N
  have hB25 : 25 ≤ B :=
    (uniformEmitDispatchEnvelope_ge_25 N).trans (by simpa [N] using hB)
  have hKtoB : K ≤ B :=
    (uniformEmitTightEnvelope_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans (by simpa [N] using hB))
  have hMcur : uniformMNat N + uctCurJ ≤ B :=
    (uniformMNat_cur_j_le_tight_envelope N).trans hKtoB
  have hrewind : ProgramBoundedIn B σ
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg) := by
    simpa [N] using
      programBoundedIn_uniform_second_pass_rewind_of_pre_startup φ B σ hB hpre
  let σr := (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg
    uctDoneReg uctSavedBoundReg).eval σ
  have hrew := uniform_rewind_eval φ σ hpre.savedBound hpre.inputBase hpre.inputBits
  have h0r : σr 0 = uniformMNat N := by
    have hfr := hrew.2.2.2 0 (by decide) (by decide) (by decide)
    exact hfr.trans (by simpa [N] using hpre.root)
  have hctl : ProgramBoundedIn B σr (ctlAssign uctCurJ uniformStartE) := by
    unfold ctlAssign
    have haddrCtl : ExprBoundedIn B σr (ctlAddr uctCurJ) := by
      simp only [ctlAddr, ExprBoundedIn, Expr.eval]
      exact ⟨by omega, by simp [uctCurJ]; omega, by rw [h0r]; exact hMcur⟩
    have hstartE : ExprBoundedIn B σr uniformStartE := by
      simp [uniformStartE, ExprBoundedIn]
      have hstartB : uniformStartNat ≤ B := by
        have hMstart : uniformStartNat ≤ uniformMNat N := by
          simp [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
        have hMtoK : uniformMNat N ≤ K := by
          simp [K, uniformEmitTightEnvelope]
          omega
        exact hMstart.trans (hMtoK.trans hKtoB)
      exact hstartB
    have haddrVal : (ctlAddr uctCurJ).eval σr ≤ B := by
      simpa [ctlAddr, Expr.eval, h0r, uctCurJ] using hMcur
    exact ⟨haddrCtl, hstartE, haddrVal⟩
  let σi := (ctlAssign uctCurJ uniformStartE).eval σr
  have h0i : σi 0 = uniformMNat N := by
    have := ctlAssign_zero uctCurJ uniformStartE σr (by decide)
    exact this.trans h0r
  have hcuri : σi (uniformMNat N + uctCurJ) = uniformStartNat := by
    have h := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, uniformStartE_eval] at h
    simpa [σi, uctCurJ] using h
  have hstartI : WriterState σi (uniformMNat N) uctCurJ uniformStartNat [] :=
    writerInit_mk _ _ _ _ h0i hcuri (by simp [uniformStartNat, relocateControlGap])
      (uniform_layout_start_lt_M N)
  have hnumI : σi uctFreshReg = (toThreeCNF φ).numVars := by
    have hr := hrew.2.2.2 uctFreshReg (by decide) (by decide) (by decide)
    have hM25 : 25 ≤ uniformMNat N := uniformMNat_ge_25 N
    have hi := ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg (by
      rw [h0r]
      simp [uctFreshReg, uctCurJ]
      omega)
    exact hi.trans (hr.trans hpre.fresh)
  have hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length := by
    have hr := hrew.2.2.2 uctCountReg (by decide) (by decide) (by decide)
    have hM25 : 25 ≤ uniformMNat N := uniformMNat_ge_25 N
    have hi := ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg (by
      rw [h0r]
      simp [uctCountReg, uctCurJ]
      omega)
    exact hi.trans (hr.trans hpre.count)
  have hheaderTight := programBoundedIn_uniform_writer_append_header_tight φ σi
    (by simpa [N] using hstartI) hnumI hcountI
  have hheader : ProgramBoundedIn B σi
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg) := by
    exact programBoundedIn_of_le hKtoB (by simpa [K, N] using hheaderTight)
  simpa [secondPassStartupProgramAt, σr, σi, eval_seq] using
    (show ProgramBoundedIn B σ
      ((secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).seq ((ctlAssign uctCurJ uniformStartE).seq
          (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg))) from
      ⟨hrewind, ⟨hctl, hheader⟩⟩)

lemma uniform_producer_decoded_stats_bounds
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    let bits := encodeCNF φ
    let σI := bitInputStore bits
    let σR := uniformRelocateProg.eval σI
    let σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
    let σ0 := uniformControlInitProg.eval σC
    let decoder := decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg
    let σd := decoder.eval σ0
    let σp := uniformPostDecodeStatsProg.eval σd
    let σs := uniformSaveBoundProg.eval σp
    let σa := uniformSetArenaProg.eval σs
    σd uctMaxReg + 1 ≤ B ∧ σd uctMaxReg + 1 + σd uctFreshReg ≤ B ∧
      UniformProducerPreStartupFacts φ (encodeCNF φ).length σa := by
  dsimp only
  let bits := encodeCNF φ
  let N := bits.length
  let K := uniformEmitTightEnvelope N
  let σI := bitInputStore bits
  let σR := uniformRelocateProg.eval σI
  let σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
  let σ0 := uniformControlInitProg.eval σC
  let decoder := decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
    uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
    uctBoundReg uctSeenReg
  let σd := decoder.eval σ0
  let σp := uniformPostDecodeStatsProg.eval σd
  let σs := uniformSaveBoundProg.eval σp
  let σa := uniformSetArenaProg.eval σs
  have hpre := uniform_producer_pre_startup φ
  have hpreFacts : UniformProducerPreStartupFacts φ N σa := by
    have hpre' : σa 0 = uniformMNat N ∧ σa uctSavedBoundReg = N ∧
        σa uctInputBaseReg = uniformAddrNat N ∧
        σa uctFreshReg = (toThreeCNF φ).numVars ∧
        σa uctCountReg = (toThreeCNF φ).clauses.length ∧
        σa uctMaxReg = cnfVarBound φ ∧ BitsFrom σa (uniformAddrNat N) bits := by
      simpa [σa, σs, σp, σd, decoder, σ0, σC, σR, σI, bits, N] using hpre
    exact ⟨hpre'.1, hpre'.2.1, hpre'.2.2.1, hpre'.2.2.2.1,
      hpre'.2.2.2.2.1, hpre'.2.2.2.2.2.1, hpre'.2.2.2.2.2.2⟩
  obtain ⟨hmaxD0, hfreshD0, _, hseenD0⟩ :=
    decodeCNFProgramAtSeen_uct_encodeCNF_zero_seed φ
  have hmaxD : σd uctMaxReg = cnfLiteralVarMaxStat 0
      (φ.clauses.map (fun c => c.lits)) := by
    simpa [σd, decoder, σ0, σC, σR, σI, bits, N] using hmaxD0
  have hfreshD : σd uctFreshReg = cnfFreshBaseStat 0
      (φ.clauses.map (fun c => c.lits)) := by
    simpa [σd, decoder, σ0, σC, σR, σI, bits, N] using hfreshD0
  have hseenD : σd uctSeenReg = cnfSeenStat 0
      (φ.clauses.map (fun c => c.lits)) := by
    simpa [σd, decoder, σ0, σC, σR, σI, bits, N] using hseenD0
  have hbounds : ∀ ls ∈ φ.clauses.map (fun c => c.lits),
      ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N := by
    simpa [N, bits] using encodeCNF_scan_bounds φ
  have hmaxDLe : σd uctMaxReg ≤ N := by
    rw [hmaxD]
    exact cnfLiteralVarMaxStat_le N 0 _ (by omega)
      (fun ls hls l hl => (hbounds ls hls).2 l hl)
  have hσpFresh : σp uctFreshReg = (toThreeCNF φ).numVars := by
    calc
      σp uctFreshReg = σs uctFreshReg :=
        ((uniformSaveBoundProg_eval σp).2 uctFreshReg (by decide)).symm
      _ = σa uctFreshReg :=
        (uniformSetArenaProg_frame σs (r := uctFreshReg) (by decide)).symm
      _ = (toThreeCNF φ).numVars := hpreFacts.fresh
  have hpostFresh : σp uctFreshReg =
      (if cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) ≠ 0 then
        cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) + 1
      else cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits))) +
        cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)) := by
    simpa [σp] using (uniformPostDecodeStatsProg_eval σd
      (cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)))
      (cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)))
      (cnfSeenStat 0 (φ.clauses.map (fun c => c.lits))) hmaxD hfreshD hseenD).2.1
  have hfreshDLe : σd uctFreshReg ≤ K := by
    rw [hσpFresh] at hpostFresh
    have hnumVarsK : (toThreeCNF φ).numVars ≤ K := by
      simpa [K, N, bits] using toThreeCNF_numVars_le_tight_envelope φ
    have hnonneg : 0 ≤ if cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) ≠ 0 then
        cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) + 1
      else cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) := by omega
    rw [hfreshD]
    omega
  have hKN : K + N + 2 ≤ B := by
    have h := hB
    simp [K, N, bits, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitSyntaxEnvelope,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ] at h ⊢
    ring_nf at h ⊢
    nlinarith
  exact ⟨by omega, by omega, by simpa [N, bits] using hpreFacts⟩

lemma programBoundedIn_uniform_producer_setup_tail
    (B : ℕ) (σd : Store) (pStart : Program)
    (hpostBound : ProgramBoundedIn B σd uniformPostDecodeStatsProg)
    (hsaveBound : ProgramBoundedIn B
      (uniformPostDecodeStatsProg.eval σd) uniformSaveBoundProg)
    (hsetBound : ProgramBoundedIn B
      (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd))
      uniformSetArenaProg)
    (hstartup : ProgramBoundedIn B
      (uniformSetArenaProg.eval
        (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd))) pStart)
    (haux : ProgramBoundedIn B
      (pStart.eval
        (uniformSetArenaProg.eval
          (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd))))
      uniformEmitAuxInitProg)
    (hfresh : ProgramBoundedIn B
      (uniformEmitAuxInitProg.eval
        (pStart.eval
          (uniformSetArenaProg.eval
            (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd)))))
      uniformFreshFromMaxProg)
    (hreset : ProgramBoundedIn B
      (uniformFreshFromMaxProg.eval
        (uniformEmitAuxInitProg.eval
          (pStart.eval
            (uniformSetArenaProg.eval
              (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd))))))
      uniformEmitResetProg) :
    ProgramBoundedIn B σd
      (uniformPostDecodeStatsProg.seq
          (uniformSaveBoundProg.seq
          (uniformSetArenaProg.seq
            (pStart.seq
              (uniformEmitAuxInitProg.seq
                 (uniformFreshFromMaxProg.seq (uniformEmitResetProg.seq Program.skip))))))) := by
  have htailSeq : ProgramBoundedInSequence B σd
      [uniformPostDecodeStatsProg, uniformSaveBoundProg, uniformSetArenaProg,
        pStart, uniformEmitAuxInitProg, uniformFreshFromMaxProg, uniformEmitResetProg,
        Program.skip] := by
    exact .cons _ _ _ hpostBound (.cons _ _ _ hsaveBound
      (.cons _ _ _ hsetBound
        (.cons _ _ _ hstartup
          (.cons _ _ _ haux
            (.cons _ _ _ hfresh
              (.cons _ _ _ hreset
                (.cons _ _ _ trivial (.nil _))))))))
  simpa [programSequence] using programBoundedIn_programSequence B σd _ htailSeq

/-- Bound the setup suffix from the decoded CNF state through its final reset. -/
lemma programBoundedIn_uniformProducerSetupProg_after_decode
    (φ : CNF) (B : ℕ) (σd : Store)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (hσd : StoreValuesLe B σd)
    (hσd0 : σd 0 = (encodeCNF φ).length)
    (hstats : σd uctMaxReg + 1 ≤ B ∧
      σd uctMaxReg + 1 + σd uctFreshReg ≤ B ∧
      UniformProducerPreStartupFacts φ (encodeCNF φ).length
        (uniformSetArenaProg.eval
          (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd)))) :
    ProgramBoundedIn B σd
      (uniformPostDecodeStatsProg.seq
        (uniformSaveBoundProg.seq
          (uniformSetArenaProg.seq
            ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
              uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).seq
              (uniformEmitAuxInitProg.seq
                (uniformFreshFromMaxProg.seq (uniformEmitResetProg.seq Program.skip))))))) := by
  set N := (encodeCNF φ).length
  have hB1 : 1 ≤ B := by
    have := uniformEmitDispatchEnvelope_ge_25 N
    omega
  have hB25 : 25 ≤ B := (uniformEmitDispatchEnvelope_ge_25 N).trans (by simpa [N] using hB)
  let σp := uniformPostDecodeStatsProg.eval σd
  let σs := uniformSaveBoundProg.eval σp
  let σa := uniformSetArenaProg.eval σs
  obtain ⟨hmaxBound, hsumBound, hpreFacts⟩ := hstats
  have hpostBound : ProgramBoundedIn B σd uniformPostDecodeStatsProg :=
    programBoundedIn_uniformPostDecodeStatsProg_of_bounds B σd hB25 hσd
      hmaxBound hsumBound
  have hσp : StoreValuesLe B σp := by
    exact program_eval_storeValuesLe σd _ hB1 hσd hpostBound
      scanFree_uniformPostDecodeStatsProg
  have hsaveBound : ProgramBoundedIn B σp uniformSaveBoundProg :=
    programBoundedIn_uniformSaveBoundProg B σp (by simp [uctSavedBoundReg]; omega)
  have hσs : StoreValuesLe B σs := by
    exact program_eval_storeValuesLe σp _ hB1 hσp hsaveBound scanFree_uniformSaveBoundProg
  have hσp0 : σp 0 = N := by
    have hf := uniformPostDecodeStatsProg_frame σd (r := 0)
      (by decide) (by decide) (by decide)
    exact hf.trans hσd0
  have hσsSaved : σs uctSavedBoundReg = N := by
    change (uniformSaveBoundProg.eval σp) uctSavedBoundReg = N
    rw [(uniformSaveBoundProg_eval σp).1, hσp0]
  have hME : ExprBoundedIn B σs uniformME :=
    exprBoundedIn_uniformME_of_input φ B σs hσsSaved hB
  have hsetBound : ProgramBoundedIn B σs uniformSetArenaProg := by
    exact ⟨by simp, hME⟩
  have hσa : StoreValuesLe B σa := by
    exact program_eval_storeValuesLe σs _ hB1 hσs hsetBound
      (by simp [ScanFree, uniformSetArenaProg])
  let pStart := secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
    uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg
  have hstartup : ProgramBoundedIn B σa pStart := by
    simpa [pStart, N] using
      programBoundedIn_uniform_second_pass_startup_of_pre_startup φ B σa hB hpreFacts
  let σst := pStart.eval σa
  have hσst : StoreValuesLe B σst := by
    exact program_eval_storeValuesLe σa _ hB1 hσa hstartup
      (scanFree_secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg)
  let σx := uniformEmitAuxInitProg.eval σst
  have haux : ProgramBoundedIn B σst uniformEmitAuxInitProg :=
    programBoundedIn_uniformEmitAuxInitProg B σst hB25
  have hσx : StoreValuesLe B σx := by
    exact program_eval_storeValuesLe σst _ hB1 hσst haux scanFree_uniformEmitAuxInitProg
  let σf := uniformFreshFromMaxProg.eval σx
  have hfresh : ProgramBoundedIn B σx uniformFreshFromMaxProg :=
    programBoundedIn_uniformFreshFromMaxProg B σx hB25
  have hσf : StoreValuesLe B σf := by
    exact program_eval_storeValuesLe σx _ hB1 hσx hfresh scanFree_uniformFreshFromMaxProg
  have hreset : ProgramBoundedIn B σf uniformEmitResetProg :=
    programBoundedIn_uniformEmitResetProg B σf hB25
  exact programBoundedIn_uniform_producer_setup_tail B σd pStart hpostBound
    (by simpa [σp] using hsaveBound)
    (by simpa [σp, σs] using hsetBound)
    (by simpa [σp, σs, σa] using hstartup)
    (by simpa [σp, σs, σa, σst] using haux)
    (by simpa [σp, σs, σa, σst, σx] using hfresh)
    (by simpa [σp, σs, σa, σst, σx, σf] using hreset)

lemma programBoundedIn_uniformProducerSetupProg
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformProducerSetupProg := by
  set bits := encodeCNF φ
  set N := bits.length
  set σI := bitInputStore bits
  set σR := uniformRelocateProg.eval σI
  set σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
  set σ0 := uniformControlInitProg.eval σC
  set decoder := decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
    uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
    uctBoundReg uctSeenReg
  set σd := decoder.eval σ0
  have hprefix := uniform_producer_decode_prefix_bounded φ B hB
  dsimp only at hprefix
  have hprefix' : ProgramBoundedIn B σI uniformRelocateProg ∧
      ProgramBoundedIn B σR (uniformCursorInitProg uctCursorReg uctInputBaseReg) ∧
      ProgramBoundedIn B σC uniformControlInitProg ∧
      ProgramBoundedIn B σ0 decoder ∧ StoreValuesLe B σd := by
    simpa [σd, decoder, σ0, σC, σR, σI, bits] using hprefix
  obtain ⟨hreloc, hcursor, hcontrol, hdecode, hσd⟩ := hprefix'
  have h0R : σR 0 = N := by
    simpa [σR, σI, bits, N] using (uniformRelocateProg_bitInputStore bits).1
  have hσ0root : σ0 0 = N := by
    have hc := uniformCursorInitProg_frame uctCursorReg uctInputBaseReg 0 σR
      (by decide) (by decide)
    have hcc := uniformControlInitProg_frame 0 σC uctControlRegs_not_bound
    exact hcc.trans (hc.trans h0R)
  have hσd0 : σd 0 = N := by
    simpa [σd, decoder, uctBoundReg] using
      (decodeCNFProgramAtSeen_uct_bound_frame σ0).trans hσ0root
  let σp := uniformPostDecodeStatsProg.eval σd
  let σs := uniformSaveBoundProg.eval σp
  let σa := uniformSetArenaProg.eval σs
  have hstats := uniform_producer_decoded_stats_bounds φ B hB
  dsimp only at hstats
  have hstats' : σd uctMaxReg + 1 ≤ B ∧
      σd uctMaxReg + 1 + σd uctFreshReg ≤ B ∧
      UniformProducerPreStartupFacts φ N σa := by
    simpa [σa, σs, σp, σd, decoder, σ0, σC, σR, σI, bits, N] using hstats
  have htail := programBoundedIn_uniformProducerSetupProg_after_decode φ B σd hB hσd
    (by simpa [N, bits] using hσd0)
    (by simpa [σa, σs, σp, N, bits] using hstats')
  unfold uniformProducerSetupProg uniformProducerSetupWith
  refine ⟨hreloc, ?_⟩
  refine ⟨hcursor, ?_⟩
  refine ⟨hcontrol, ?_⟩
  refine ⟨hdecode, ?_⟩
  simpa [σd, decoder, σ0, σC, σR, σI, bits, N] using htail

lemma programBoundedIn_uniform_producer_outer_loop
    (φ : CNF) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope (encodeCNF φ).length)
      (uniformProducerResetStore φ) (.forN (.reg uctOuterReg) uniformEmitIterBody) := by
  let N := (encodeCNF φ).length
  let K := uniformEmitTightEnvelope N
  let B := uniformEmitDispatchEnvelope N
  have hK1 : 1 ≤ K := by
    simp [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hσ : StoreValuesLe K (uniformProducerResetStore φ) := by
    simpa [K, N] using uniformProducerResetStore_tight φ
  have hrel := uniformProducerResetStore_cnfEmitRel_reset φ
  have hb := uniformProducerResetStore_savedBound φ
  have houterB : uctOuterReg ≤ B := by
    have hB := uniformEmitDispatchEnvelope_ge_25 N
    simp [B, uctOuterReg] at hB ⊢
    omega
  have hacc := OuterEmitAccounting.producer_init φ
  have hprefix := uniform_emit_loop_prefix_accounting_tight φ [] φ.clauses
    ([] : Bits)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    (uniformAddrNat N + φ.clauses.length + 1) (cnfVarBound φ)
    (uniformProducerResetStore φ) (by simp) hacc hrel hb hσ
  simp only [ProgramBoundedIn]
  refine ⟨?_, ?_⟩
  · simp only [ExprBoundedIn]
    exact houterB
  · intro m hm
    change m < (uniformProducerResetStore φ) uctOuterReg at hm
    rw [hrel.outer] at hm
    have hmle : m ≤ φ.clauses.length := by omega
    obtain ⟨τ, clauses', base', pref', addr', consumed', hτ, hlen, hsplit,
      hrel', hacc', hb', hσ'⟩ := hprefix m hmle
    obtain ⟨τ0, clauses0, base0, pref0, addr0, consumed0, hτ0, hsplit0,
      hrel0, hacc0, hb0, hzero0⟩ :=
      uniform_producer_outer_accounting_zero φ m hmle
    have hτeq : τ = τ0 := hτ.trans hτ0.symm
    have hzero : CellsZeroFrom (uniformAddrNat N + N) τ := by
      rw [hτeq]
      simpa [N] using hzero0
    rcases clauses' with _ | ⟨c, cs⟩
    · have hlenSplit := congrArg List.length hsplit
      simp only [List.length_append, List.length_nil] at hlenSplit
      have hlen' : consumed'.length = m := by simpa using hlen
      omega
    · have hsplitφ : consumed' ++ c :: cs = φ.clauses := by
        calc
          consumed' ++ c :: cs = [] ++ φ.clauses := hsplit
          _ = φ.clauses := by simp
      have hbody := programBoundedIn_uniformEmitIterBody_of_outer_accounting φ
        consumed' c cs pref' addr' base' τ hsplitφ hacc' hrel' hb' hσ' hzero
      rw [← hτ]
      exact hbody

lemma programBoundedIn_uniformProducerProg_of_setup
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (hsetup : ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformProducerSetupProg) :
    ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformProducerProg := by
  let N := (encodeCNF φ).length
  let K := uniformEmitTightEnvelope N
  have hσK : StoreValuesLe K (uniformProducerResetStore φ) := by
    simpa [K, N] using uniformProducerResetStore_tight φ
  have hKtoB : K ≤ B := by
    exact (uniformEmitTightEnvelope_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N) |>.trans hB
  have hloopD := programBoundedIn_uniform_producer_outer_loop φ
  have hreset : uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ)) =
      uniformProducerResetStore φ := uniformProducerSetupProg_eval φ
  have hloop : ProgramBoundedIn B
      (uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ)))
      uniformProducerLoopProg := by
    rw [hreset]
    exact programBoundedIn_of_le hB (by simpa [uniformProducerLoopProg] using hloopD)
  obtain ⟨σe, clauses', base', pref', addr', consumed', hσeτ, hlen, hsplit,
      hrelE, haccE, hbE, hσeK⟩ :=
    (uniform_emit_loop_prefix_accounting_tight φ [] φ.clauses ([] : Bits)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      (uniformAddrNat N + φ.clauses.length + 1) (cnfVarBound φ)
      (uniformProducerResetStore φ) (by simp) (OuterEmitAccounting.producer_init φ)
      (uniformProducerResetStore_cnfEmitRel_reset φ) (uniformProducerResetStore_savedBound φ)
      hσK) φ.clauses.length le_rfl
  have hσeB : StoreValuesLe B (loopEval uniformEmitIterBody φ.clauses.length
      (uniformProducerResetStore φ)) := by
    intro i
    have hi := hσeK i
    rw [hσeτ] at hi
    exact hi.trans hKtoB
  have hwriter := uniformProducerResetStore_emit_writer φ
  have h0e : (loopEval uniformEmitIterBody φ.clauses.length
      (uniformProducerResetStore φ)) 0 = uniformMNat N := by
    simpa [N] using hwriter.root
  have hMC : uniformMNat N + uctCurJ ≤ B := by
    exact (uniformMNat_cur_j_le_tight_envelope N).trans hKtoB
  have hstart : uniformStartNat ≤ B := by
    have hs := uniformAddrNat_ge_start N
    have hK := uniform_split_tail_input_end_le_tight N
    omega
  have hfinal := programBoundedIn_uniformProducerFinalizeProg B N
    (loopEval uniformEmitIterBody φ.clauses.length (uniformProducerResetStore φ))
    hσeB h0e hMC hstart
  have hloopEval : uniformProducerLoopProg.eval
      (uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ))) =
      loopEval uniformEmitIterBody φ.clauses.length (uniformProducerResetStore φ) := by
    rw [hreset]
    simpa [uniformProducerLoopProg] using
      (uniform_producer_forN_eval φ (uniformProducerResetStore φ)
        (uniformProducerResetStore_cnfEmitRel_reset φ).outer)
  have hfinal' : ProgramBoundedIn B
      (uniformProducerLoopProg.eval
        (uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ))))
      uniformProducerFinalizeProg := by
    rw [hloopEval]
    exact hfinal
  have hcontinuation : ProgramBoundedIn B
      (uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ)))
      (uniformProducerLoopProg.seq uniformProducerFinalizeProg) :=
    ⟨hloop, hfinal'⟩
  unfold uniformProducerProg
  exact programBoundedIn_uniform_producer_setup_append B
    (bitInputStore (encodeCNF φ)) (uniformProducerLoopProg.seq uniformProducerFinalizeProg)
    hsetup hcontinuation

lemma programBoundedIn_uniformSatToThreeCNFProg_of_setup
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (hsetup : ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformProducerSetupProg) :
    ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformSatToThreeCNFProg := by
  rw [← uniformProducerProg_eq_uniformSatToThreeCNFProg]
  exact programBoundedIn_uniformProducerProg_of_setup φ B hB hsetup

lemma programBoundedIn_uniformSatToThreeCNFProg
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformSatToThreeCNFProg :=
  programBoundedIn_uniformSatToThreeCNFProg_of_setup φ B hB
    (programBoundedIn_uniformProducerSetupProg φ B hB)

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.UniformPackaging.StartupBounds

/-!
# Zero-tail preservation

The producer relies on untouched cells above the relocated input window remaining
zero as clauses are emitted. This module carries that invariant through the
iteration loop and combines it with framing to establish zero-tail facts for the
complete producer path.
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

/-! ## Input high-zero transport through the outer loop

The iteration body's high frame (`uniformEmitIterBody_eval_frame_of_rel`)
leaves every cell above `M + tmpJ` untouched, so the zero tail above the
relocated input window survives each clause emission.  The accounting
induction below therefore carries the zero-tail invariant alongside the
semantic relation and the accounting template. -/

/-- Strengthened outer-loop reachability: every prefix state of the outer
loop keeps the semantic relation for the remaining clauses, the accounting
template for the consumed prefix, and the zero tail above the input window.
Only the semantic step and its high frame are used, so no store bound is
required. -/
lemma uniform_emit_loop_prefix_accounting_zero
    (N base₀ addr₀ inputEnd : ℕ) (header : Bits) (consumed clauses : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      clauses tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hacc : OuterEmitAccounting base₀ addr₀ header consumed base pref addr)
    (habove : uniformMNat N + uctTmpJ < inputEnd)
    (hzero : CellsZeroFrom inputEnd σ) :
    ∀ m ≤ clauses.length, ∃ τ clauses' base' pref' addr' consumed',
      τ = loopEval uniformEmitIterBody m σ ∧
      consumed' ++ clauses' = consumed ++ clauses ∧
      CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base'
        clauses' tail pref' addr' τ ∧
      OuterEmitAccounting base₀ addr₀ header consumed' base' pref' addr' ∧
      τ uctSavedBoundReg = N ∧
      CellsZeroFrom inputEnd τ := by
  induction clauses generalizing base pref addr σ consumed with
  | nil =>
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      exact ⟨σ, [], base, pref, addr, consumed, by simp, by simp, hrel, hacc, hb,
        hzero⟩
  | cons c cs ih =>
      intro m hm
      cases m with
      | zero =>
          exact ⟨σ, c :: cs, base, pref, addr, consumed, by simp, by simp, hrel,
            hacc, hb, hzero⟩
      | succ m =>
          have hm' : m ≤ cs.length := by simpa using hm
          obtain ⟨σ₁, hstep, hrel₁, hb₁, hframe₁⟩ :=
            uniformEmitIterBody_eval_frame_of_rel N c cs tail pref addr base σ
              hrel hb
          have hzero₁ : CellsZeroFrom inputEnd σ₁ := by
            intro i hi
            rw [hframe₁ i (by omega)]
            exact hzero i hi
          have hacc₁ : OuterEmitAccounting base₀ addr₀ header (consumed ++ [c])
            (clauseToThree base c.lits).2
            (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
            (addr + (encodeList encodeLiteral c.lits).length) :=
            OuterEmitAccounting.step base₀ addr₀ header consumed c base pref addr
              hacc
          obtain ⟨τ, clauses', base', pref', addr', consumed'', hτ, hsplit', hrel',
            hacc', hb', hzero'⟩ :=
            ih (base := (clauseToThree base c.lits).2)
              (pref := pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
              (addr := addr + (encodeList encodeLiteral c.lits).length)
              (σ := σ₁) (consumed := consumed ++ [c]) hrel₁ hb₁ hacc₁ hzero₁
              m hm'
          refine ⟨τ, clauses', base', pref', addr', consumed'', ?_, ?_, hrel', hacc',
            hb', hzero'⟩
          · calc
              τ = loopEval uniformEmitIterBody m σ₁ := hτ
              _ = loopEval uniformEmitIterBody m (uniformEmitIterBody.eval σ) := by
                rw [hstep]
              _ = loopEval uniformEmitIterBody (m + 1) σ := by rw [loopEval_succ]
          · simpa [List.append_assoc] using hsplit'

/-! ## Initial high-zero: the input tail through the whole startup chain

The producer builds its input on the zero-default store, so every cell from
the relocated window end `uniformAddrNat N + N` upward starts (and stays)
zero through relocate, decode, and the second-pass startup.  Each phase is
discharged with a local high frame; `RelocateInvariant` itself is left
untouched. -/

lemma cellsZeroFrom_of_frame {n : ℕ} {σ τ : Store}
    (hframe : ∀ r, n ≤ r → τ r = σ r) (h : CellsZeroFrom n σ) :
    CellsZeroFrom n τ := by
  intro i hi
  rw [hframe i hi]
  exact h i hi

/-- One relocate step only writes the output cell `C + t` and the two
    control cells `N + 1`, `N + 2`, all strictly below `C + N`. -/
lemma relocateStep_frame_ge (τ : Store) (N C n t : ℕ)
    (hgap : N + relocateControlGap ≤ C) (hn : C + N ≤ n) (ht : t < N)
    (h0 : τ 0 = N)
    (hs : τ (N + relocateSrcJ) = 1 + t)
    (hd : τ (N + relocateDstJ) = C + t)
    (r : ℕ) (hr : n ≤ r) :
    (relocateStep.eval τ) r = τ r := by
  have hgap100 : 100 = relocateControlGap := rfl
  rw [relocateStep_eval N C t τ h0 hs hd hgap]
  have h1 : ¬ r = C + t := by omega
  have h2 : ¬ r = N + relocateSrcJ := by
    simp [relocateSrcJ]; omega
  have h3 : ¬ r = N + relocateDstJ := by
    simp [relocateDstJ]; omega
  rw [writeReg_diff _ (N + relocateDstJ) _ r h3,
    writeReg_diff _ (N + relocateSrcJ) _ r h2,
    writeReg_diff _ (C + t) _ r h1]

/-- The whole relocate loop keeps the invariant and leaves every cell from
    `C + N` upward unchanged. -/
lemma relocate_loop_frame_ge (σ τ0 : Store) (N C n : ℕ)
    (hgap : N + relocateControlGap ≤ C) (hn : C + N ≤ n)
    (t : ℕ) (ht : t ≤ N) (hInv : RelocateInvariant σ τ0 N C 0) (r : ℕ) (hr : n ≤ r) :
    (loopEval relocateStep t τ0) r = τ0 r := by
  have key : ∀ t, t ≤ N → RelocateInvariant σ (loopEval relocateStep t τ0) N C t ∧
      (loopEval relocateStep t τ0) r = τ0 r := by
    intro t
    induction t with
    | zero =>
        intro _
        refine ⟨by simpa using hInv, ?_⟩
        simp
    | succ t ih =>
        intro ht'
        have htN : t < N := by omega
        have ih' := ih (by omega)
        have hInv' : RelocateInvariant σ (relocateStep.eval (loopEval relocateStep t τ0))
            N C (t + 1) :=
          relocateStep_invariant σ (loopEval relocateStep t τ0) N C t hgap htN ih'.1
        rw [uniform_loopEval_succ_right]
        refine ⟨hInv', ?_⟩
        have hstep := relocateStep_frame_ge (loopEval relocateStep t τ0) N C n t hgap hn
          htN ih'.1.1 (by simpa [relocateSrcJ] using ih'.1.2.1)
          (by simpa [relocateDstJ] using ih'.1.2.2.1) r hr
        exact hstep.trans ih'.2
  exact key t ht |>.2

/-- The uniform relocate phase leaves every cell from the relocated window
    end upward unchanged. -/
lemma uniformRelocateProg_frame_ge (σ : Store) (N n : ℕ)
    (h0 : σ 0 = N) (hn : uniformAddrNat N + N ≤ n) (r : ℕ) (hr : n ≤ r) :
    (uniformRelocateProg.eval σ) r = σ r := by
  have hg100 : relocateControlGap = 100 := rfl
  have hgapge : N + relocateControlGap ≤ uniformAddrNat N := uniformAddrNat_ge_gap N
  have hsetupInv : RelocateInvariant σ (uniformRelocateSetup.eval σ) N (uniformAddrNat N)
      0 := uniformRelocateSetup_invariant σ N h0
  have hsetupFrame : (uniformRelocateSetup.eval σ) r = σ r := by
    rw [uniformRelocateSetup_eval N σ h0]
    simp only [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ] at hr ⊢
    have hnot1 : ¬ r = N + 1 := by omega
    have hnot2 : ¬ r = N + 2 := by omega
    have hnot3 : ¬ r = N + 3 := by omega
    have hnot4 : ¬ r = N + 4 := by omega
    simp [hnot1, hnot2, hnot3, hnot4]
  rw [uniformRelocateProg_eval_eq_loop σ N h0]
  have hloop := relocate_loop_frame_ge σ (uniformRelocateSetup.eval σ) N (uniformAddrNat N)
    n hgapge hn N le_rfl hsetupInv r hr
  exact hloop.trans hsetupFrame

/-- The second-pass startup leaves every cell above `M + tmpJ` untouched. -/
lemma uniform_startup_frame_ge (φ : CNF) (σ : Store)
    (h0 : σ 0 = uniformMNat (encodeCNF φ).length)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hbase : σ uctInputBaseReg = uniformAddrNat (encodeCNF φ).length)
    (hnum : σ uctFreshReg = (toThreeCNF φ).numVars)
    (hcount : σ uctCountReg = (toThreeCNF φ).clauses.length)
    (hbits : BitsFrom σ (uniformAddrNat (encodeCNF φ).length) (encodeCNF φ))
    {r : ℕ} (hr : uniformMNat (encodeCNF φ).length + uctTmpJ < r) :
    (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
      uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
      uctFreshReg uctCountReg).eval σ r = σ r := by
  set N := (encodeCNF φ).length
  set M := uniformMNat N
  set start := uniformStartNat
  have hMge : 100 ≤ M := by
    simp [M, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
  have hregs : uctCurJ = 1 ∧ uctTmpJ = 2 ∧ uctFreshReg = 9 ∧ uctCountReg = 10 ∧
      uctCursorReg = 1 ∧ uctOuterReg = 5 ∧ uctDoneReg = 4 := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hcurJ1, htmpJ2, hfresh9, hcount10, hcursor1, houter5, hdone4⟩ := hregs
  have hrew := uniform_rewind_eval φ σ hN hbase hbits
  set σr :=
    (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg).eval σ with hσrdef
  have h0r : σr 0 = M :=
    (hrew.2.2.2 0 (by decide) (by decide) (by decide)).trans h0
  have hnumR : σr uctFreshReg = (toThreeCNF φ).numVars :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hnum
  have hcountR : σr uctCountReg = (toThreeCNF φ).clauses.length :=
    (hrew.2.2.2 _ (by decide) (by decide) (by decide)).trans hcount
  have hstartR : uniformStartE.eval σr = start := uniformStartE_eval σr
  set σi := (ctlAssign uctCurJ uniformStartE).eval σr with hσidef
  have h0I : σi 0 = M := (ctlAssign_zero uctCurJ uniformStartE σr (by decide)).trans h0r
  have hcurI : σi (M + uctCurJ) = start := by
    have h := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, hstartR] at h
    simpa [σi, uctCurJ] using h
  have hsInit : WriterInit M uctCurJ start σi :=
    writerInit_mk M uctCurJ start σi h0I hcurI
      (by simp [start, uniformStartNat, relocateControlGap]) (uniform_layout_start_lt_M N)
  have hnumI : σi uctFreshReg = (toThreeCNF φ).numVars :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg
      (by rw [h0r, hcurJ1, hfresh9]; omega)).trans hnumR
  have hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length :=
    (ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg
      (by rw [h0r, hcurJ1, hcount10]; omega)).trans hcountR
  have hroom := uniform_header_room φ
  have hseq :
      (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg
        uctDoneReg uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
        uctFreshReg uctCountReg).eval σ =
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi := by
    unfold secondPassStartupProgramAt
    simp [eval_seq, σr, σi]
  have hwriter := writerAppendHeaderProg_frame_high M uctCurJ uctTmpJ start []
    uctFreshReg uctCountReg (toThreeCNF φ).numVars (toThreeCNF φ).clauses.length σi
    (by decide) (by decide) hnumI hcountI
    (by simp [start, uniformStartNat, uctCountReg, relocateControlGap])
    hsInit (by simpa [List.length_nil] using hroom) hr
  have hctl : σi r = σr r := by
    apply ctlAssign_eval_diff uctCurJ uniformStartE σr r
    rw [h0r, hcurJ1]
    omega
  have hrewFrame : σr r = σ r := by
    refine hrew.2.2.2 r ?_ ?_ ?_
    · rw [hcursor1]; omega
    · rw [houter5]; omega
    · rw [hdone4]; omega
  rw [hseq]
  exact hwriter.trans (hctl.trans hrewFrame)

/-- Initial high-zero theorem: every cell from the relocated input window end
    upward is zero on the producer's outer-loop entry state.  Each startup
    phase contributes only a local frame; the semantic content is that the
    producer builds its input on the zero-default store. -/
lemma uniformProducerResetStore_cellsZeroFrom (φ : CNF) :
    CellsZeroFrom (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length)
      (uniformProducerResetStore φ) := by
  set bits := encodeCNF φ with hbitsdef
  set N := bits.length
  set C := uniformAddrNat N
  set n := C + N with hn
  set σR := uniformRelocateProg.eval (bitInputStore bits)
  set σC := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR
  set σ0 := uniformControlInitProg.eval σC
  set σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  set σp := uniformPostDecodeStatsProg.eval σd
  set σs := uniformSaveBoundProg.eval σp
  set σa := uniformSetArenaProg.eval σs
  set σst :=
    (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg uctCurJ uctTmpJ uniformStartE
      uctFreshReg uctCountReg).eval σa
  set σx := uniformEmitAuxInitProg.eval σst
  set σf := uniformFreshFromMaxProg.eval σx
  have hR0 : (bitInputStore bits) 0 = N := rfl
  have hC25 := uniformAddrNat_ge_25 N
  obtain ⟨hb0, hbase0, hcursor0, hpol0, hvar0, hdone0, houter0, hrem0, hmax0, hlen0,
    hfresh0, hcount0, htmp0, hseen0⟩ := uniformControlInitProg_after_cursor bits
  have hinit : CellsZeroFrom n (bitInputStore bits) := by
    intro i hi
    exact bitInputStore_eq_zero_of_ge_inputEnd bits i
      (by have hge := uniformAddrNat_ge_25 N; omega)
  have hreloc : CellsZeroFrom n σR := by
    refine cellsZeroFrom_of_frame ?_ hinit
    exact fun r hr => uniformRelocateProg_frame_ge (bitInputStore bits) N n hR0
      (by simp only [n, C]; exact le_rfl) r hr
  have hcur : CellsZeroFrom n σC := by
    refine cellsZeroFrom_of_frame ?_ hreloc
    intro r hr
    exact uniformCursorInitProg_frame uctCursorReg uctInputBaseReg r σR
      (by simp [uctCursorReg]; omega)
      (by simp [uctInputBaseReg]; omega)
  have hctl : CellsZeroFrom n σ0 := by
    refine cellsZeroFrom_of_frame ?_ hcur
    intro r hr
    exact uniformControlInitProg_frame r σC (not_mem_uctControlRegs_of_ge r (by omega))
  have hbits0 : BitsFrom σ0 C
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits)) := by
    have henc : encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits) = encodeCNF φ := by
      simp [encodeCNF_eq_lists, List.append_nil]
    rw [henc]
    exact uniformControlInitProg_bitsFrom bits
  have hdec : CellsZeroFrom n σd := by
    refine cellsZeroFrom_of_frame ?_ hctl
    intro r hr
    exact decodeCNFProgramAtSeen_uct_frame_ge N
      (φ.clauses.map (fun c => c.lits)) ([] : Bits) C 0 0 0 0 σ0
      (by simpa using encodeCNF_length_ge_clauseCount φ)
      hC25 hcursor0 hrem0 hmax0 hfresh0 hcount0 hseen0 hb0
      (encodeCNF_scan_bounds φ) hbits0
      r (by omega)
  have hpost : CellsZeroFrom n σp := by
    refine cellsZeroFrom_of_frame ?_ hdec
    intro r hr
    exact uniformPostDecodeStatsProg_frame σd (by simp [uctTmpReg]; omega)
      (by simp [uctMaxReg]; omega) (by simp [uctFreshReg]; omega)
  have hsave : CellsZeroFrom n σs := by
    refine cellsZeroFrom_of_frame ?_ hpost
    intro r hr
    exact (uniformSaveBoundProg_eval σp).2 r (by simp [uctSavedBoundReg]; omega)
  have harena : CellsZeroFrom n σa := by
    refine cellsZeroFrom_of_frame ?_ hsave
    intro r hr
    exact uniformSetArenaProg_frame σs (by omega)
  have hpre := uniform_producer_pre_startup φ
  have hstart : CellsZeroFrom n σst := by
    refine cellsZeroFrom_of_frame ?_ harena
    intro r hr
    have hlt : uniformMNat (encodeCNF φ).length + uctTmpJ < r := by
      have htmp2 : uctTmpJ = 2 := rfl
      have hC3 : uniformAddrNat (encodeCNF φ).length =
          uniformMNat (encodeCNF φ).length + 3 := rfl
      have hr' : uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length ≤ r := hr
      omega
    have hstartFrame := uniform_startup_frame_ge φ σa hpre.1 hpre.2.1 hpre.2.2.1
      hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2.2 (r := r) hlt
    exact hstartFrame
  have haux : CellsZeroFrom n σx := by
    refine cellsZeroFrom_of_frame ?_ hstart
    intro r hr
    exact uniformEmitAuxInitProg_frame σst (by simp [uctPosPolReg]; omega)
      (by simp [uctNegPolReg]; omega)
  have hfresh : CellsZeroFrom n σf := by
    refine cellsZeroFrom_of_frame ?_ haux
    intro r hr
    exact uniformFreshFromMaxProg_frame σx (by simp [uctFreshReg]; omega)
  refine cellsZeroFrom_of_frame ?_ hfresh
  intro r hr
  exact uniformEmitResetProg_frame σf (by simp [uctLengthReg]; omega)
    (by simp [uctDoneReg]; omega)

/-- The producer's outer loop: every prefix state carries the semantic
    relation for the remaining clauses, the accounting template for the
    consumed prefix, and the zero tail above the input window. -/
lemma uniform_producer_outer_accounting_zero (φ : CNF) (m : ℕ)
    (hm : m ≤ φ.clauses.length) :
    ∃ τ clauses' base' pref' addr' consumed,
      τ = loopEval uniformEmitIterBody m (uniformProducerResetStore φ) ∧
      consumed ++ clauses' = φ.clauses ∧
      CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
        (encodeCNF φ).length (encodeCNF φ).length base' clauses' ([] : Bits)
        pref' addr' τ ∧
      OuterEmitAccounting (cnfVarBound φ)
        (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
        (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
        consumed base' pref' addr' ∧
      τ uctSavedBoundReg = (encodeCNF φ).length ∧
      CellsZeroFrom (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length) τ := by
  have habove : uniformMNat (encodeCNF φ).length + uctTmpJ <
      uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
    have h := uniform_layout_inputAbove (encodeCNF φ).length
    omega
  have h := uniform_emit_loop_prefix_accounting_zero (encodeCNF φ).length (cnfVarBound φ)
    (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
    (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    [] φ.clauses []
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1) (cnfVarBound φ)
    (uniformProducerResetStore φ)
    (uniformProducerResetStore_cnfEmitRel_reset φ) (uniformProducerResetStore_savedBound φ)
    (OuterEmitAccounting.producer_init φ) habove
    (uniformProducerResetStore_cellsZeroFrom φ) m hm
  simpa using h

end NPComplete.CookLevin

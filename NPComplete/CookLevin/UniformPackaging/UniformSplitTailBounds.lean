module

public import NPComplete.CookLevin.UniformPackaging.SplitTailCertificates

/-!
# Uniform split-tail raw bounds

Generic split-tail bounds must be instantiated at the fixed registers and
envelopes of the uniform producer. This module derives concrete syntax and raw
bounds from its semantic reachability relation, bridging generic emitter facts
to dispatch.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

/-! ## Uniform double-envelope step bounds

At the fixed uct registers the value side runs on the long value envelope and
the operand side on the syntax envelope.  Both decoder cursor budgets come from
the split-tail window, which is what makes the long value envelope sufficient
where the tight envelope provably is not.  This is the concrete uniform instance
of the `K/B` split in `SplitTailEmitStepRawBounds`. -/

lemma uniform_split_tail_emit_step_syntax_bounds_of_rel
    (N base inputEnd baseLimit : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry ls
      pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hb : σ uctSavedBoundReg = N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ) :
    SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
      (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ := by
  have hok := uniform_emit_bound_reg_ok.split
  have hlt := uniform_emit_writer_layout_le_tight N
  have htl := uniformEmitTightEnvelope_le_long_value_envelope N
  have hidx : uctCursorReg ≤ uniformEmitLongValueEnvelope N ∧
      uctPolReg ≤ uniformEmitLongValueEnvelope N ∧
      uctVarReg ≤ uniformEmitLongValueEnvelope N ∧
      uctDoneReg ≤ uniformEmitLongValueEnvelope N ∧
      uctRemainingReg ≤ uniformEmitLongValueEnvelope N ∧
      uctPol2Reg ≤ uniformEmitLongValueEnvelope N ∧
      uctVar2Reg ≤ uniformEmitLongValueEnvelope N ∧
      uctPol3Reg ≤ uniformEmitLongValueEnvelope N ∧
      uctVar3Reg ≤ uniformEmitLongValueEnvelope N ∧
      uctCarryPolReg ≤ uniformEmitLongValueEnvelope N ∧
      uctCarryValReg ≤ uniformEmitLongValueEnvelope N ∧
      uctPosPolReg ≤ uniformEmitLongValueEnvelope N ∧
      uctFreshReg ≤ uniformEmitLongValueEnvelope N ∧
      uctSavedBoundReg ≤ uniformEmitLongValueEnvelope N := by
    simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg,
      uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg,
      uctPosPolReg, uctFreshReg, uctSavedBoundReg, uniformEmitLongValueEnvelope,
      uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat]
    omega
  obtain ⟨hcp, hcv, hcd, _, _, _⟩ := hrel.safety.second.distinct
  obtain ⟨hbc, _, _, hbd, _, hbp2, hbv2, _, _, _, _, _, _⟩ := hok.ne_write_set
  have hc1c2 := split_tail_emit_cursor_budgets_of_window
    (uniformEmitLongValueEnvelope N) inputEnd baseLimit base ls tail addr σ
    uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg uctSavedBoundReg
    hcp hcv hcd hbc hbp2 hbv2 hbd hwin hrel.cursor (by rw [hb]; exact hend)
  exact SplitTailEmitRel.to_raw_bounds (uniformEmitLongValueEnvelope N)
    (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    uctSavedBoundReg base carry ls pref tail addr σ hrel hok
    ⟨hlt.2.2.1.trans htl, hlt.2.2.2.trans htl, hlt.1.trans htl, hlt.2.1.trans htl⟩ hidx hσ
    hc1c2.1 hc1c2.2
    (by simp [uniformEmitSyntaxEnvelope])

lemma programBoundedIn_emitClauseEmptyFreshProg_of_bounds
    (B freshReg : ℕ) (σ : Store)
    (hfreshReg : freshReg ≤ B) (hval : σ freshReg + 1 ≤ B) :
    ProgramBoundedIn B σ (emitClauseEmptyFreshProg freshReg) := by
  simp only [emitClauseEmptyFreshProg, ProgramBoundedIn, ExprBoundedIn, Expr.eval]
  omega

/-- The two literal decoders of the long-clause setup stay inside `B`, keep the root
cell and the control cell nonzero, and leave the store within the decoder envelope `K`. -/
lemma programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds_decode
    (K B M curJ cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg boundReg : ℕ) (σ : Store)
    (hKB : K ≤ B) (hK1 : 1 ≤ K)
    (hidx1 : cursorReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ doneReg ≤ K ∧ boundReg ≤ K)
    (hidx2 : cursorReg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧ doneReg ≤ K ∧ boundReg ≤ K)
    (hdist1 : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
      var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
      boundReg ≠ var2Reg ∧ boundReg ≠ doneReg)
    (hdist2 : cursorReg ≠ pol3Reg ∧ cursorReg ≠ var3Reg ∧ cursorReg ≠ doneReg ∧
      var3Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol3Reg ∧
      boundReg ≠ var3Reg ∧ boundReg ≠ doneReg)
    (hzero1 : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0)
    (hzero2 : cursorReg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol1 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
      M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg)
    (hcontrol2 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol3Reg ∧
      M + curJ ≠ var3Reg ∧ M + curJ ≠ doneReg)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M) (hq0 : σ (M + curJ) ≠ 0)
    (hcursor1 : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
        cursorReg + 1 + σ boundReg ≤ K) :
    ∃ τ2, τ2 = (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg).eval
        ((decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ) ∧
      ProgramBoundedIn B σ
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg) ∧
      ProgramBoundedIn B
        ((decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ)
        (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg) ∧
      StoreValuesLe K τ2 ∧ τ2 0 = M ∧ τ2 (M + curJ) ≠ 0 := by
  rcases hdist1 with ⟨hcc1, hcv1, hcd1, hvd1, hbc1, hbp1, hbv1, hbd1⟩
  rcases hdist2 with ⟨hcc2, hcv2, hcd2, hvd2, hbc2, hbp2, hbv2, hbd2⟩
  have hdec1 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg pol2Reg var2Reg doneReg boundReg σ hidx1
    ⟨hcc1, hcv1, hcd1, hvd1, hbc1, hbp1, hbv1, hbd1⟩ hzero1 hK1 hσ hcursor1 hKB
  have hτ1bound : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      boundReg = σ boundReg :=
    decodeLiteralValueProgramAt_frame cursorReg pol2Reg var2Reg doneReg boundReg boundReg σ
      hbc1 hbp1 hbv1 hbd1
  have hτ1q0 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      (M + curJ) ≠ 0 := by
    rw [decodeLiteralValueProgramAt_frame cursorReg pol2Reg var2Reg doneReg boundReg (M + curJ) σ
      hcontrol1.1 hcontrol1.2.1 hcontrol1.2.2.1 hcontrol1.2.2.2]
    exact hq0
  have hdec2 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg pol3Reg var3Reg doneReg boundReg
    ((decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ) hidx2
    ⟨hcc2, hcv2, hcd2, hvd2, hbc2, hbp2, hbv2, hbd2⟩ hzero2 hK1 hdec1.2.1
    (by rw [hτ1bound]; exact hcursor2) hKB
  refine ⟨_, rfl, hdec1.1, hdec2.1, hdec2.2.1, ?_, ?_⟩
  · rw [hdec2.2.2.2.1, hdec1.2.2.2.1, hM]
  · rw [decodeLiteralValueProgramAt_frame cursorReg pol3Reg var3Reg doneReg boundReg (M + curJ) _
      hcontrol2.1 hcontrol2.2.1 hcontrol2.2.2.1 hcontrol2.2.2.2]
    exact hτ1q0

/-- The four register assignments closing the long-clause setup keep the root cell, and the
control cell stays in `B` and nonzero, when the incoming store is within the envelope `K3`. -/
lemma programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds_assigns
    (K3 B M curJ remainingReg carryPolReg carryValReg freshReg : ℕ) (σw : Store)
    (hK31 : 1 ≤ K3) (hK3B : K3 + 1 ≤ B)
    (hcpB : carryPolReg ≤ B) (hcvB : carryValReg ≤ B) (hfreshB : freshReg ≤ B)
    (hremB : remainingReg ≤ B)
    (hσw : StoreValuesLe K3 σw) (hroot : σw 0 = M) (hqB : σw (M + curJ) ≤ B)
    (hq0 : σw (M + curJ) ≠ 0)
    (hcarryPol0 : carryPolReg ≠ 0) (hcarryVal0 : carryValReg ≠ 0)
    (hfresh0 : freshReg ≠ 0) (hremaining0 : remainingReg ≠ 0)
    (hcarryPolCursor : carryPolReg ≠ M + curJ) (hcarryValCursor : carryValReg ≠ M + curJ)
    (hfreshCursor : freshReg ≠ M + curJ) (hremainingCursor : remainingReg ≠ M + curJ) :
    ProgramBoundedIn B σw
      (.seq (.assign carryPolReg (.const 1))
        (.seq (.assign carryValReg (.reg freshReg))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.seq (.assign remainingReg (.sub (.reg remainingReg) (.const 2))) .skip)))) ∧
    (Program.seq (.assign carryPolReg (.const 1))
        (.seq (.assign carryValReg (.reg freshReg))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.seq (.assign remainingReg (.sub (.reg remainingReg) (.const 2))) .skip)))).eval
        σw 0 = M ∧
    (Program.seq (.assign carryPolReg (.const 1))
        (.seq (.assign carryValReg (.reg freshReg))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.seq (.assign remainingReg (.sub (.reg remainingReg) (.const 2))) .skip)))).eval
        σw (M + curJ) ≤ B ∧
    (Program.seq (.assign carryPolReg (.const 1))
        (.seq (.assign carryValReg (.reg freshReg))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.seq (.assign remainingReg (.sub (.reg remainingReg) (.const 2))) .skip)))).eval
        σw (M + curJ) ≠ 0 := by
  have hcp : ProgramBoundedIn B σw (.assign carryPolReg (.const 1)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hσ3 : StoreValuesLe K3 ((Program.assign carryPolReg (.const 1)).eval σw) :=
    storeValuesLe_assign hσw (by simp only [Expr.eval]; omega)
  have hcv : ProgramBoundedIn B ((Program.assign carryPolReg (.const 1)).eval σw)
      (.assign carryValReg (.reg freshReg)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hσ4 : StoreValuesLe K3 ((Program.assign carryValReg (.reg freshReg)).eval
      ((Program.assign carryPolReg (.const 1)).eval σw)) :=
    storeValuesLe_assign hσ3 (hσ3 freshReg)
  have hfr : ProgramBoundedIn B ((Program.assign carryValReg (.reg freshReg)).eval
      ((Program.assign carryPolReg (.const 1)).eval σw))
      (.assign freshReg (.add (.reg freshReg) (.const 1))) := by
    have hf4 := hσ4 freshReg
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    omega
  have hrem5 : ((Program.assign freshReg (.add (.reg freshReg) (.const 1))).eval
      ((Program.assign carryValReg (.reg freshReg)).eval
        ((Program.assign carryPolReg (.const 1)).eval σw))) remainingReg ≤ B := by
    simp only [eval_assign, Expr.eval]
    by_cases hr : remainingReg = freshReg
    · rw [hr, writeReg_same]
      have := hσ4 freshReg
      simp only [eval_assign, Expr.eval] at this
      omega
    · rw [writeReg_diff _ _ _ _ hr]
      have := hσ4 remainingReg
      simp only [eval_assign, Expr.eval] at this
      omega
  refine ⟨⟨hcp, hcv, hfr, ?_, trivial⟩, ?_, ?_, ?_⟩
  · simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    omega
  · simp only [eval_seq, eval_skip, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (Ne.symm hremaining0), writeReg_diff _ _ _ _ (Ne.symm hfresh0),
      writeReg_diff _ _ _ _ (Ne.symm hcarryVal0), writeReg_diff _ _ _ _ (Ne.symm hcarryPol0)]
    exact hroot
  · simp only [eval_seq, eval_skip, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (Ne.symm hremainingCursor),
      writeReg_diff _ _ _ _ (Ne.symm hfreshCursor),
      writeReg_diff _ _ _ _ (Ne.symm hcarryValCursor),
      writeReg_diff _ _ _ _ (Ne.symm hcarryPolCursor)]
    exact hqB
  · simp only [eval_seq, eval_skip, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (Ne.symm hremainingCursor),
      writeReg_diff _ _ _ _ (Ne.symm hfreshCursor),
      writeReg_diff _ _ _ _ (Ne.symm hcarryValCursor),
      writeReg_diff _ _ _ _ (Ne.symm hcarryPolCursor)]
    exact hq0


lemma programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
      carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hdist1 : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
      var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
      boundReg ≠ var2Reg ∧ boundReg ≠ doneReg)
    (hdist2 : cursorReg ≠ pol3Reg ∧ cursorReg ≠ var3Reg ∧ cursorReg ≠ doneReg ∧
      var3Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol3Reg ∧
      boundReg ≠ var3Reg ∧ boundReg ≠ doneReg)
    (hzero1 : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0)
    (hzero2 : cursorReg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol1 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
      M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg)
    (hcontrol2 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol3Reg ∧
      M + curJ ≠ var3Reg ∧ M + curJ ≠ doneReg)
    (hcarryPol0 : carryPolReg ≠ 0) (hcarryVal0 : carryValReg ≠ 0)
    (hfresh0 : freshReg ≠ 0) (hremaining0 : remainingReg ≠ 0)
    (hcarryPolCursor : carryPolReg ≠ M + curJ) (hcarryValCursor : carryValReg ≠ M + curJ)
    (hfreshCursor : freshReg ≠ M + curJ) (hremainingCursor : remainingReg ≠ M + curJ)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hcursor1 : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
        cursorReg + 1 + σ boundReg ≤ K)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg) ∧
    StoreValuesLe B
      ((splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval σ) ∧
    (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval σ 0 = M ∧
    (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval σ (M + curJ) ≤ B ∧
    (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval σ (M + curJ) ≠ 0 := by
  rcases hidx with ⟨hcursorB, hpolB, hvarB, hdoneB, hremB, hpol2B, hvar2B,
    hpol3B, hvar3B, hcpB, hcvB, hposB, hfreshB, hboundB⟩
  have hK1 : 1 ≤ K := by omega
  have hKB : K ≤ B := by
    simp only [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hK3K : K ≤ writerAppendRawThreeBound K := by
    simp only [writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hK31 : 1 ≤ writerAppendRawThreeBound K := hK1.trans hK3K
  have hσB : StoreValuesLe B σ := fun i => (hσ i).trans hKB
  obtain ⟨τ2, hτ2, hd1, hd2, hτ2K, hτ2root, hτ2q0⟩ :=
    programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds_decode K B M curJ cursorReg
      pol2Reg var2Reg pol3Reg var3Reg doneReg boundReg σ hKB hK1
      ⟨hcursorB, hpol2B, hvar2B, hdoneB, hboundB⟩ ⟨hcursorB, hpol3B, hvar3B, hdoneB, hboundB⟩
      hdist1 hdist2 hzero1 hzero2 hcontrol1 hcontrol2 hσ hM hq0 hcursor1 hcursor2
  have hwriter := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
    pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg τ2 hcurJ1 htmpJlt hstatic
    ⟨hpol2B, hvar2B, hpol3B, hvar3B, hposB, hfreshB⟩ hτ2K hτ2root hτ2q0
    (by simp only [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
        omega)
  have hwriterT := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K
    (writerAppendRawThreeBound K) M curJ tmpJ
    pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg τ2 hcurJ1 htmpJlt hstatic
    ⟨hpol2B, hvar2B, hpol3B, hvar3B, hposB, hfreshB⟩ hτ2K hτ2root hτ2q0
    (by simp only [writerAppendRawThreeBound, writerAppendRawStepBound]; exact le_rfl)
  obtain ⟨σw, hσw⟩ : ∃ σw, σw = (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg
      var3Reg posPolReg freshReg).eval τ2 := ⟨_, rfl⟩
  rw [← hσw] at hwriter hwriterT
  have hasg := programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds_assigns
    (writerAppendRawThreeBound K) B M curJ remainingReg carryPolReg carryValReg freshReg σw
    hK31 hbudget (hcpB.trans hKB) (hcvB.trans hKB) (hfreshB.trans hKB) (hremB.trans hKB)
    hwriterT.2.1 hwriter.2.2.1 hwriter.2.2.2.1
    hwriter.2.2.2.2 hcarryPol0 hcarryVal0 hfresh0 hremaining0 hcarryPolCursor hcarryValCursor
    hfreshCursor hremainingCursor
  have hprog : ProgramBoundedIn B σ
      (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg) := by
    subst hτ2 hσw
    exact ⟨hd1, hd2, hwriter.1, hasg.1⟩
  have hchain : (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg).eval σ = (Program.seq (.assign carryPolReg (.const 1))
        (.seq (.assign carryValReg (.reg freshReg))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.seq (.assign remainingReg (.sub (.reg remainingReg) (.const 2))) .skip)))).eval
        σw := by
    subst hτ2 hσw
    simp only [splitTailEmitLongClauseSetupAt, eval_seq]
  refine ⟨hprog, ?_, ?_, ?_, ?_⟩
  · exact program_eval_storeValuesLe σ _ (by omega) hσB hprog
      (scanFree_splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg boundReg)
  · rw [hchain]
    exact hasg.2.1
  · rw [hchain]
    exact hasg.2.2.1
  · rw [hchain]
    exact hasg.2.2.2

lemma programBoundedIn_uniform_long_clause_setup_at_raw
    (N K B : ℕ) (σ : Store)
    (hstatic : uniformMNat N + uctCurJ ≤ K ∧ uniformMNat N + uctTmpJ ≤ K)
    (hregs : 24 ≤ K)
    (hσ : StoreValuesLe K σ)
    (hM : σ 0 = uniformMNat N)
    (hb : σ uctSavedBoundReg = N)
    (hq0 : σ (uniformMNat N + uctCurJ) ≠ 0)
    (hcursor1 : σ uctCursorReg + 1 + N ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ uctCursorReg + 1 + N ≤ K)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    StoreValuesLe B
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ 0
      = uniformMNat N ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
        (uniformMNat N + uctCurJ) ≤ B ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
        (uniformMNat N + uctCurJ) ≠ 0 := by
  have hctrl : ∀ r : ℕ, r ≤ 24 → (r ≠ uniformMNat N + uctCurJ) := by
    intro r _hr
    simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  have hidx : uctCursorReg ≤ K ∧ uctPolReg ≤ K ∧ uctVarReg ≤ K ∧ uctDoneReg ≤ K ∧
      uctRemainingReg ≤ K ∧ uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧ uctPol3Reg ≤ K ∧
      uctVar3Reg ≤ K ∧ uctCarryPolReg ≤ K ∧ uctCarryValReg ≤ K ∧ uctPosPolReg ≤ K ∧
      uctFreshReg ≤ K ∧ uctSavedBoundReg ≤ K := by
    simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg,
      uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg,
      uctPosPolReg, uctFreshReg, uctSavedBoundReg]
    omega
  exact programBoundedIn_splitTailEmitLongClauseSetupAt_raw_bounds K B (uniformMNat N)
    uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg uctSavedBoundReg σ
    (by exact uniform_cur_j_bounds.1) (by exact uniform_cur_j_bounds.2)
    ⟨hstatic.1, hstatic.2, by omega, by omega⟩ hidx
    (by decide) (by decide) (by decide) (by decide)
    ⟨Ne.symm (hctrl uctCursorReg (by decide)), Ne.symm (hctrl uctPol2Reg (by decide)),
      Ne.symm (hctrl uctVar2Reg (by decide)), Ne.symm (hctrl uctDoneReg (by decide))⟩
    ⟨Ne.symm (hctrl uctCursorReg (by decide)), Ne.symm (hctrl uctPol3Reg (by decide)),
      Ne.symm (hctrl uctVar3Reg (by decide)), Ne.symm (hctrl uctDoneReg (by decide))⟩
    (by decide) (by decide) (by decide) (by decide)
    (hctrl uctCarryPolReg (by decide)) (hctrl uctCarryValReg (by decide))
    (hctrl uctFreshReg (by decide)) (hctrl uctRemainingReg (by decide))
    hσ hM hq0
    (by rw [hb]; exact hcursor1)
    (by rw [hb]; exact hcursor2)
    hbudget

/-! The setup side of the double envelope: the two decoder cursor budgets are
    discharged from a window-level address bound instead of a store bound, so
    the entry state only needs the long value envelope. -/
lemma uniform_splitTailEmitLongClauseSetupAt_syntax
    (N : ℕ) (σ : Store)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hM : σ 0 = uniformMNat N)
    (hb : σ uctSavedBoundReg = N)
    (hq0 : σ (uniformMNat N + uctCurJ) ≠ 0)
    (haddr : σ uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    StoreValuesLe (uniformEmitSyntaxEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ 0
      = uniformMNat N ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
        (uniformMNat N + uctCurJ) ≤ uniformEmitSyntaxEnvelope N ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
        (uniformMNat N + uctCurJ) ≠ 0 := by
  have hlt := uniform_emit_writer_layout_le_tight N
  have htl := uniformEmitTightEnvelope_le_long_value_envelope N
  have hcursor2 : (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg).eval σ uctCursorReg + 1 + N ≤
      uniformEmitLongValueEnvelope N := by
    have hc := decodeLiteralValueProgramAt_cursor_le uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    omega
  exact programBoundedIn_uniform_long_clause_setup_at_raw N (uniformEmitLongValueEnvelope N)
    (uniformEmitSyntaxEnvelope N) σ
    ⟨hlt.2.2.1.trans htl, hlt.2.2.2.trans htl⟩
    (by simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat]; omega)
     hσ hM hb hq0 (by omega) hcursor2 (by simp [uniformEmitSyntaxEnvelope])

lemma decodeLiteralValueProgramAt_var_le
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
     (hcv : cursorReg ≠ varReg) (hcd : varReg ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
      varReg ≤ σ boundReg := by
  unfold decodeLiteralValueProgramAt
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ with hσ1
  have hb1 : σ1 boundReg = σ boundReg :=
    readBitAdvanceProg_frame cursorReg polReg boundReg σ hbc hbp
  set σ2 := (Program.assign varReg (.const 0)).eval σ1
  have hb2 : σ2 boundReg = σ boundReg := by
    have h := writeReg_diff σ1 varReg 0 boundReg hbv
    simpa [σ2, eval_assign, Expr.eval] using h.trans hb1
  have hv2 : σ2 varReg = 0 := by
     simp [σ2, eval_assign, Expr.eval]
  set σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hb3 : σ3 boundReg = σ boundReg := by
    have h := writeReg_diff σ2 doneReg 0 boundReg hbd
    simpa [σ3, eval_assign, Expr.eval] using h.trans hb2
  have hv3 : σ3 varReg = 0 := by
    have h := writeReg_diff σ2 doneReg 0 varReg hcd
    simpa [σ3, eval_assign, Expr.eval] using h.trans hv2
  have hnat := decodeNatProgramAt_count_le cursorReg varReg doneReg boundReg σ3
    hcv hcd
  rw [eval_seq, eval_seq, eval_seq, ← hσ1]
  have hle : (decodeNatProgramAt cursorReg varReg doneReg boundReg).eval σ3
      varReg ≤ σ3 varReg + σ3 boundReg := hnat
  calc
    _ ≤ σ3 varReg + σ3 boundReg := hle
    _ = σ boundReg := by rw [hv3, hb3]; simp

end NPComplete.CookLevin

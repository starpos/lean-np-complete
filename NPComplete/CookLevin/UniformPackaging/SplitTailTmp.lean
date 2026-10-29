module

public import NPComplete.CookLevin.UniformPackaging.EmitStateBounds

/-!
# Temporary values in split-tail emission

The split-tail proof stages encoded literals and clauses in temporary registers.
This module isolates those value bounds for bit, literal, clause, and
intermediate paths so higher-level reachability proofs can reuse them.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral encodeThreeClause)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma emitNatProg_tmp_value
    (curJ tmpJ M cur : ℕ) (e : Expr) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hsep : cur + e.eval σ < M + curJ) :
    (emitNatProg curJ tmpJ e).eval σ (M + tmpJ) = e.eval σ := by
  unfold emitNatProg
  rw [eval_seq, eval_seq, eval_forN]
  set σ1 := (ctlAssign tmpJ e).eval σ
  have hσ10 : σ1 0 = M := by
    exact (ctlAssign_zero tmpJ e σ (by omega)).trans hM
  have hσ1tmp : σ1 (M + tmpJ) = e.eval σ := by
    have h := ctlAssign_eval_same tmpJ e σ
    rw [hM] at h
    exact h
  have hσ1cur : σ1 (M + curJ) = cur := by
    have hne : M + curJ ≠ σ 0 + tmpJ := by rw [hM]; omega
    exact (ctlAssign_eval_diff tmpJ e σ (M + curJ) hne).trans hcur
  have hn : (ctlCell tmpJ).eval σ1 = e.eval σ := by
    rw [ctlCell_eval, hσ10, hσ1tmp]
  rw [hn]
  set σ2 := loopEval (emitBitProg curJ (.const 0)) (e.eval σ) σ1
  have hz := emit_zero_loop_invariant curJ M hcurJ (e.eval σ) cur σ1
    hσ10 hσ1cur hcur1 hsep
  have hσ2tmp : σ2 (M + tmpJ) = σ1 (M + tmpJ) := by
    exact hz.2.2.2 (M + tmpJ) (by omega) (Or.inr (by omega))
  have hterm := emitBitProg_frame curJ M (cur + e.eval σ) (.const 1) σ2
    hz.1 hz.2.1 (by omega) (by omega) (M + tmpJ) (by omega) (by omega)
  rw [hterm, hσ2tmp, hσ1tmp]

lemma writerAppendLiteralProg_tmp_value
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg varVal : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hvar : σ varReg = varVal)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + varVal + 2 < M + curJ)
    (hvarLow : varReg < start) :
    (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ (M + tmpJ) = varVal := by
  unfold writerAppendLiteralProg
  rw [eval_seq]
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  have hcur : σ (M + curJ) = start + pref.length := by simpa using hcursor
  have hcur0 : start + pref.length ≠ 0 := by omega
  have hcurN : start + pref.length ≠ M + curJ := by omega
  have h0 : σ1 0 = M := by
    dsimp [σ1]
    exact emitBitProg_ctl curJ M (start + pref.length) (.reg polReg) σ hcurJ hroot hcur
      hcur0 hcurN
  have hc : σ1 (M + curJ) = start + pref.length + 1 := by
    dsimp [σ1]
    exact emitBitProg_cursor curJ M (start + pref.length) (.reg polReg) σ hroot hcur
      hcur0 hcurN
  have hv : σ1 varReg = varVal := by
    dsimp [σ1]
    rw [emitBitProg_frame curJ M (start + pref.length) (.reg polReg) σ hroot hcur hcur0 hcurN
      varReg (by omega) (by omega)]
    exact hvar
  have hn := emitNatProg_tmp_value curJ tmpJ M (start + pref.length + 1)
    (.reg varReg) σ1 hcurJ htmpJ h0 hc (by omega) (by
      simp [Expr.eval, hv]
      omega)
  simpa [Expr.eval, hv] using hn

lemma writerAppendThreeRegsProg_tmp_value
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 : ℕ)
    (pol1 val1 pol2 val2 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ) :
    (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ (M + tmpJ) = val3 := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, encodeNat_length]
    omega
  have hroom3 : start + (pref ++ encodedLiteralBits pol1 val1 ++
      encodedLiteralBits pol2 val2).length + val3 + 2 < M + curJ := by
    simp [encodedLiteralBits, encodeNat_length]
    omega
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ
    hcurJ htmpJ hp1 hv1 hpol1 hs hroom1 hlow1
  have hp2' := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 (r := p2) hlow2.1
  have hv2' := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 (r := v2) hlow2.2
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2
    ((writerAppendLiteralProg curJ tmpJ p1 v1).eval σ) hcurJ htmpJ
    (hp2'.trans hp2) (hv2'.trans hv2) hpol2 hs1 hroom2 hlow2.2
  have hp3' := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 (r := p3) hlow3.1
  have hv3' := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 (r := v3) hlow3.2
  have hp3'' := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2
    ((writerAppendLiteralProg curJ tmpJ p1 v1).eval σ) hcurJ htmpJ
    (hv2'.trans hv2) hs1 hroom2 hlow2.2 (r := p3) hlow3.1
  have hv3'' := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2
    ((writerAppendLiteralProg curJ tmpJ p1 v1).eval σ) hcurJ htmpJ
    (hv2'.trans hv2) hs1 hroom2 hlow2.2 (r := v3) hlow3.2
  have htmp := writerAppendLiteralProg_tmp_value M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 val3
    ((writerAppendLiteralProg curJ tmpJ p2 v2).eval
      ((writerAppendLiteralProg curJ tmpJ p1 v1).eval σ)) hcurJ htmpJ
    (hv3''.trans (hv3'.trans hv3)) hs2 hroom3 hlow3.2
  simpa [writerAppendThreeRegsProg, List.append_assoc] using htmp

lemma writerAppendClauseOneProg_tmp_value
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg polarity varVal : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = polarity) (hvar : σ varReg = varVal)
    (hpol01 : polarity = 0 ∨ polarity = 1)
    (hlow : polReg < start ∧ varReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (varVal + 2) < M + curJ) :
    (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ (M + tmpJ) = varVal := by
  have hroom' : start + pref.length + varVal + varVal + varVal + 6 < M + curJ := by
    omega
  simpa [writerAppendClauseOneProg] using
    writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
      polReg varReg polReg varReg polReg varReg
      polarity varVal polarity varVal varVal σ hcurJ htmpJ
      hpol hvar hpol hvar hvar hpol01 hpol01
      hlow.2 ⟨hlow.1, hlow.2⟩ ⟨hlow.1, hlow.2⟩ hs hroom'

lemma writerAppendClauseTwoProg_tmp_value
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 pol1 val1 pol2 val2 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + 2 * val2 + 6 < M + curJ) :
    (writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2).eval σ (M + tmpJ) = val2 := by
  have hroom' : start + pref.length + val1 + val2 + val2 + 6 < M + curJ := by
    omega
  simpa [writerAppendClauseTwoProg] using
    writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
      p1 v1 p2 v2 p2 v2 pol1 val1 pol2 val2 val2 σ hcurJ htmpJ
      hp1 hv1 hp2 hv2 hv2 hpol1 hpol2 hlow1 hlow2 hlow2 hs hroom'

/-- Decoding the first literal preserves the split-tail writer registers. -/
lemma splitTailEmitIntermediateProgAt_tmp_value_of_rel_decode
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∃ τp : Store,
      τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ ∧
      WriterState τp M curJ start pref ∧
      τp carryPolReg = 1 ∧ τp carryValReg = carry.var ∧
      τp posPolReg = 0 ∧ τp freshReg = base ∧
      τp polReg = literalPolarity l ∧ τp varReg = l.var := by
  have hbits : BitsFrom σ addr (encodeLiteral l ++ splitTailInputBits (l2 :: l3 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  have hbelow := hrel.safety.main.below
  have hnonzero := hrel.safety.main.nonzero
  obtain ⟨_, hpol, hvar, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l
      (splitTailInputBits (l2 :: l3 :: rest) tail) σ
      hrel.safety.main.distinct.1 hrel.safety.main.distinct.2.1
      hrel.safety.main.distinct.2.2.1 hrel.safety.main.distinct.2.2.2.1
      hrel.safety.main.distinct.2.2.2.2.1 hrel.safety.main.distinct.2.2.2.2.2
      (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  let τp := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg polReg varReg doneReg hrel.writer (by simpa [τp] using hdecFrame)
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2
  have hkeep : ∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg →
      τp r = σ r := by
    intro r hr
    have hw := hrel.safety.writer_parser r (by
      rcases hr with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
    rcases hw with ⟨hc, hp, hv, hd, _, _, _, _⟩
    simpa [τp] using hdecFrame r hc hp hv hd
  refine ⟨τp, rfl, hτstate, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hkeep _ (Or.inl rfl)).trans hrel.carry_pol
  · exact (hkeep _ (Or.inr (Or.inl rfl))).trans hrel.carry_val
  · exact (hkeep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hrel.pos
  · exact (hkeep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hrel.fresh
  · cases l <;> simpa [τp, literalPolarity] using hpol
  · simpa [τp] using hvar

/-- The dynamic linking writer leaves its final fresh value in the tmp cell. -/
lemma splitTailEmitIntermediateProgAt_tmp_value_of_rel_link
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ τp : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτstate : WriterState τp M curJ start pref)
    (hτcarryPol : τp carryPolReg = 1) (hτcarryVal : τp carryValReg = carry.var)
    (hτpol : τp polReg = literalPolarity l) (hτvar : τp varReg = l.var)
    (hτfresh : τp freshReg = base)
    (hroom : start + pref.length + carry.var + l.var + base + 8 < M + curJ) :
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
      posPolReg freshReg).eval τp (M + tmpJ) = base := by
  have hpol01 : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have htmp := writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
    carryPolReg carryValReg polReg varReg posPolReg freshReg
    1 carry.var (literalPolarity l) l.var base τp hrel.cur_j_pos hrel.tmp_j_pos
    hτcarryPol hτcarryVal hτpol hτvar hτfresh
    (by simp) hpol01
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.main.below.2.1, hrel.safety.main.below.2.2.1⟩
    ⟨hrel.safety.writer_below.2.2.1, hrel.safety.writer_below.2.2.2.1⟩
    hτstate (by omega)
  unfold writerAppendSplitTailLinkDynamicProg
  rw [eval_seq, eval_seq, eval_assign, eval_assign, Expr.eval]
  have hstart : start < M + curJ := by
    have hs := hrel.writer.safe
    omega
  have hcurJtmpJ : M + curJ < M + tmpJ := Nat.add_lt_add_left hrel.tmp_j_pos M
  have hfresh : freshReg ≠ M + tmpJ := by
    have h := hrel.safety.writer_below.2.2.2.1
    omega
  have hcarryVal : carryValReg ≠ M + tmpJ := by
    have h := hrel.safety.writer_below.2.1
    omega
  rw [writeReg_diff _ freshReg _ (M + tmpJ) hfresh.symm,
    writeReg_diff _ carryValReg _ (M + tmpJ) hcarryVal.symm]
  exact htmp

/-- The final remaining-count assignment does not change the tmp value. -/
lemma splitTailEmitIntermediateProgAt_tmp_value_of_rel_eval
    (M curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg bound : ℕ) (base : ℕ) (σ τp : Store)
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    (hlink : (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg
      varReg posPolReg freshReg).eval τp (M + tmpJ) = base)
    (hremaining : remainingReg ≠ M + tmpJ) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ (M + tmpJ) = base := by
  unfold splitTailEmitIntermediateProg
  rw [eval_seq, eval_seq, ← hτp]
  rw [eval_assign, Expr.eval,
    writeReg_diff _ remainingReg _ (M + tmpJ) hremaining.symm]
  exact hlink

lemma splitTailEmitIntermediateProgAt_tmp_value_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hroom : start + pref.length + carry.var + l.var + base + 8 < M + curJ) :
    (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ (M + tmpJ) = base := by
  obtain ⟨τp, hτp, hτstate, hτcarryPol, hτcarryVal, _, hτfresh, hτpol, hτvar⟩ :=
    splitTailEmitIntermediateProgAt_tmp_value_of_rel_decode M curJ tmpJ start cursorReg polReg
      varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l l2 l3 rest pref tail addr σ hbound hrel
  have hlink := splitTailEmitIntermediateProgAt_tmp_value_of_rel_link M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg base carry l l2 l3 rest pref tail addr
    σ τp hrel hτstate hτcarryPol hτcarryVal hτpol hτvar hτfresh hroom
  have hremaining : remainingReg ≠ M + tmpJ := by
    have h := hrel.safety.writer_below.2.2.2.2
    have hstart : start < M + curJ := by
      have hs := hrel.writer.safe
      omega
    have hcurJtmpJ : M + curJ < M + tmpJ := Nat.add_lt_add_left hrel.tmp_j_pos M
    omega
  have htmpNonAt := splitTailEmitIntermediateProgAt_tmp_value_of_rel_eval M curJ tmpJ
    cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg
    bound base σ τp hτp hlink hremaining
  have heq := splitTailEmitIntermediateProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hok.ne_cursor hok.ne_pol hok.ne_var hok.ne_done
  rw [heq]
  exact htmpNonAt

lemma split_tail_emit_intermediate_room_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ)
    (_bound : ℕ) (base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    start + pref.length + carry.var + l.var + base + 8 < M + curJ := by
  have hc := hrel.capacity
  rw [splitTailPayload_cons3, hrel.carry_one] at hc
  simp only [List.length_append] at hc ⊢
  have hlen : carry.var + l.var + base + 6 ≤
      (encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base).length := by
    cases carry <;> cases l <;>
      simp [encodedThreeLiteralBits, encodedLiteralBits, encodeNat_length,
        NPComplete.SAT.Literal.var, literalPolarity, natBit] <;> omega
  omega

/-- Under `htmpAt`, the one-literal fixed step reaches done and leaves its tmp cell at most `K`. -/
lemma splitTailEmitProgAt_tmp_bound_of_rel_one
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (τ : Store)
    (hlb : l.var + 1 ≤ bound) (hbase : base + 1 ≤ K)
    (hrel : SplitTailEmitRel τ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : τ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hboundK : bound ≤ K)
    (htmpAt : (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ
        (M + tmpJ) = l.var) :
    ∃ τ', τ' = (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval τ ∧
      SplitTailEmitDone τ' M curJ start base carry [l] pref tail addr cursorReg remainingReg
        freshReg ∧
      base + [l].length ≤ K ∧ τ' (M + tmpJ) ≤ K := by
  obtain ⟨τ', hτ', hdone⟩ := splitTailEmitRel_one_to_done
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l pref tail addr τ hlb hrel
  have hstepAt : (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg).eval τ =
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval τ := by
    simp [splitTailEmitStepProgAt, hrel.remaining, Expr.eval]
  have heqAt := splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg
    freshReg boundReg bound τ hb hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  have hstep := hstepAt.trans (heqAt.trans hτ'.symm)
  have hval : τ' (M + tmpJ) = l.var := by
    rw [← hstep, hstepAt, htmpAt]
  exact ⟨τ', hstep.symm, hdone, by simpa using hbase, by omega⟩

/-- Under `htmpAt`, the two-literal fixed step reaches done and leaves its tmp cell at most `K`. -/
lemma splitTailEmitProgAt_tmp_bound_of_rel_two
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l l2 : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (τ : Store)
    (hlb : l.var + 1 ≤ bound) (hlb2 : l2.var + 1 ≤ bound) (hbase : base + 2 ≤ K)
    (hrel : SplitTailEmitRel τ M curJ tmpJ start base carry [l, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : τ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hboundK : bound ≤ K)
    (htmpAt : (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg boundReg).eval τ (M + tmpJ) = l2.var) :
    ∃ τ', τ' = (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval τ ∧
      SplitTailEmitDone τ' M curJ start base carry [l, l2] pref tail addr cursorReg remainingReg
        freshReg ∧
      base + [l, l2].length ≤ K ∧ τ' (M + tmpJ) ≤ K := by
  obtain ⟨τ', hτ', hdone⟩ := splitTailEmitRel_two_to_done
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l l2 pref tail addr τ hlb hlb2 hrel
  have hstepAt : (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg).eval τ =
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg).eval τ := by
    simp [splitTailEmitStepProgAt, hrel.remaining, Expr.eval]
  have heqAt := splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg boundReg bound τ hb hok.ne_cursor hok.ne_pol2
    hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  have hstep := hstepAt.trans (heqAt.trans hτ'.symm)
  have hval : τ' (M + tmpJ) = l2.var := by
    rw [← hstep, hstepAt, htmpAt]
  exact ⟨τ', hstep.symm, hdone, by simpa using hbase, by omega⟩

/-- Intermediate case: the fixed step keeps the relation (with one more fresh variable
consumed), re-establishes the bound-register invariants, and leaves `base` in the tmp cell. -/
lemma splitTailEmitProgAt_tmp_bound_of_rel_intermediate
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal) (rest : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (τ : Store)
    (hbound : ∀ x ∈ l :: l2 :: l3 :: rest, x.var + 1 ≤ bound)
    (hbase : base + (l :: l2 :: l3 :: rest).length ≤ K)
    (hrel : SplitTailEmitRel τ M curJ tmpJ start base carry (l :: l2 :: l3 :: rest)
      pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : τ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ', τ' = (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg).eval τ ∧
      SplitTailEmitRel τ' M curJ tmpJ start (base + 1) (NPComplete.SAT.Literal.neg base)
        (l2 :: l3 :: rest)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
        tail (addr + l.var + 2)
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg ∧
      (∀ x ∈ l2 :: l3 :: rest, x.var + 1 ≤ bound) ∧
      base + 1 + (l2 :: l3 :: rest).length ≤ K ∧ τ' (M + tmpJ) ≤ K ∧ τ' boundReg = bound := by
  have hlb : l.var + 1 ≤ bound := hbound l (by simp)
  obtain ⟨τ', hτ', hrel1⟩ := splitTailEmitRel_intermediate_to_rel
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l l2 l3 rest pref tail addr τ hlb hrel
  have heqAt := splitTailEmitIntermediateProgAt_eq curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg boundReg
    bound τ hb hok.ne_cursor hok.ne_pol hok.ne_var hok.ne_done
  have hstepAt : (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg).eval τ =
      (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ := by
    simp [splitTailEmitStepProgAt, hrel.remaining, Expr.eval]
  have hstep := hstepAt.trans (heqAt.trans hτ'.symm)
  have htmpAt := splitTailEmitIntermediateProgAt_tmp_value_of_rel M curJ tmpJ
    start cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
    posPolReg freshReg boundReg bound base carry l l2 l3
    rest pref tail addr τ hlb hrel hb hok
    (split_tail_emit_intermediate_room_of_rel M curJ tmpJ start cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l l2 l3 rest pref tail addr τ hrel)
  have hval : τ' (M + tmpJ) = base := by
    rw [← hstep, hstepAt, htmpAt]
  have hlow := splitTailEmitStepProg_low_frame_of_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry
    (l :: l2 :: l3 :: rest) pref tail addr τ hbound hrel
    hok.below hok.ne_write_set (r := boundReg)
  have heqStep := splitTailEmitStepProgAt_eq curJ tmpJ cursorReg polReg varReg
    doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg boundReg bound τ hb hok.ne_cursor hok.ne_pol hok.ne_var
    hok.ne_done hok.ne_pol2 hok.ne_var2 hok.ne_pol3 hok.ne_var3
  have hbd : τ' boundReg = bound := by
    rw [← hstep]
    exact (congrArg (fun s : Store => s boundReg) heqStep).trans (hlow.trans hb)
  refine ⟨τ', hstep.symm, hrel1, fun x hx => hbound x (by simp [hx]), ?_, by omega, hbd⟩
  simp only [List.length_cons] at hbase ⊢
  omega

/-- One fixed step from a relation state with `ls` remaining: dispatches on the length of `ls`
and returns the next relation or done state, with the tmp cell still bounded by `K`. -/
lemma splitTailEmitProgAt_tmp_bound_of_rel_step
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (τ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbase : base + ls.length ≤ K) (htmp : τ (M + tmpJ) ≤ K)
    (hrel : SplitTailEmitRel τ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : τ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hboundK : bound ≤ K)
    (honeTmp : ∀ (base : ℕ) (carry l : NPComplete.SAT.Literal)
      (pref tail : Bits) (addr : ℕ) (τ : Store),
      l.var + 1 ≤ bound →
      SplitTailEmitRel τ M curJ tmpJ start base carry [l] pref tail addr
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg →
      τ boundReg = bound →
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ
        (M + tmpJ) = l.var)
    (htwoTmp : ∀ (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal)
      (pref tail : Bits) (addr : ℕ) (τ : Store),
      l1.var + 1 ≤ bound → l2.var + 1 ≤ bound →
      SplitTailEmitRel τ M curJ tmpJ start base carry [l1, l2] pref tail addr
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg →
      τ boundReg = bound →
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ
        (M + tmpJ) = l2.var) :
    ∃ τ' base' carry' ls' pref' addr',
      τ' = (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          boundReg).eval τ ∧
      ((SplitTailEmitRel τ' M curJ tmpJ start base' carry' ls' pref' tail addr'
          cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
          carryPolReg carryValReg posPolReg freshReg ∧
          (∀ l ∈ ls', l.var + 1 ≤ bound) ∧
          base' + ls'.length ≤ K ∧ τ' (M + tmpJ) ≤ K ∧ τ' boundReg = bound) ∨
        (SplitTailEmitDone τ' M curJ start base' carry' ls' pref' tail addr'
          cursorReg remainingReg freshReg ∧
          base' + ls'.length ≤ K ∧ τ' (M + tmpJ) ≤ K)) := by
  match ls, hbound, hbase, hrel with
  | [], hbound, hbase, hrel =>
    exact ⟨τ, base, carry, [], pref, addr,
      (splitTailEmitStepProgAt_zero_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg τ
        (by simpa using hrel.remaining)).symm,
      Or.inl ⟨hrel, hbound, hbase, htmp, hb⟩⟩
  | [l], hbound, hbase, hrel =>
    have hlb : l.var + 1 ≤ bound := hbound l (by simp)
    obtain ⟨τ', hτ', hdone, hbase', htmp'⟩ := splitTailEmitProgAt_tmp_bound_of_rel_one K M curJ
      tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound base carry l pref tail addr τ hlb
      (by simpa using hbase) hrel hb hok hboundK (honeTmp base carry l pref tail addr τ hlb hrel hb)
    exact ⟨τ', base, carry, [l], pref, addr, hτ', Or.inr ⟨hdone, hbase', htmp'⟩⟩
  | [l, l2], hbound, hbase, hrel =>
    have hlb : l.var + 1 ≤ bound := hbound l (by simp)
    have hlb2 : l2.var + 1 ≤ bound := hbound l2 (by simp)
    obtain ⟨τ', hτ', hdone, hbase', htmp'⟩ := splitTailEmitProgAt_tmp_bound_of_rel_two K M curJ
      tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound base carry l l2 pref tail addr τ
      hlb hlb2 (by simpa using hbase) hrel hb hok hboundK
      (htwoTmp base carry l l2 pref tail addr τ hlb hlb2 hrel hb)
    exact ⟨τ', base, carry, [l, l2], pref, addr, hτ', Or.inr ⟨hdone, hbase', htmp'⟩⟩
  | l :: l2 :: l3 :: rest, hbound, hbase, hrel =>
    obtain ⟨τ', hτ', hrel1, hlist, hbase', htmp', hbd⟩ :=
      splitTailEmitProgAt_tmp_bound_of_rel_intermediate K M curJ tmpJ start cursorReg polReg
        varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg bound base carry l l2 l3 rest pref tail addr τ hbound hbase
        hrel hb hok
    exact ⟨τ', base + 1, NPComplete.SAT.Literal.neg base, l2 :: l3 :: rest,
      pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base,
      addr + l.var + 2, hτ', Or.inl ⟨hrel1, hlist, hbase', htmp', hbd⟩⟩

lemma splitTailEmitProgAt_tmp_bound_of_rel
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbase : base + ls.length ≤ K) (htmp : σ (M + tmpJ) ≤ K)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hboundK : bound ≤ K)
    (honeTmp : ∀ (base : ℕ) (carry l : NPComplete.SAT.Literal)
      (pref tail : Bits) (addr : ℕ) (τ : Store),
      l.var + 1 ≤ bound →
      SplitTailEmitRel τ M curJ tmpJ start base carry [l] pref tail addr
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg →
      τ boundReg = bound →
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ
        (M + tmpJ) = l.var)
    (htwoTmp : ∀ (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal)
      (pref tail : Bits) (addr : ℕ) (τ : Store),
      l1.var + 1 ≤ bound → l2.var + 1 ≤ bound →
      SplitTailEmitRel τ M curJ tmpJ start base carry [l1, l2] pref tail addr
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg →
      τ boundReg = bound →
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ
        (M + tmpJ) = l2.var)
    (n : ℕ) :
    ∃ τ base' carry' ls' pref' addr',
      τ = loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        n σ ∧
      ((SplitTailEmitRel τ M curJ tmpJ start base' carry' ls' pref' tail addr'
          cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
          carryPolReg carryValReg posPolReg freshReg ∧
          (∀ l ∈ ls', l.var + 1 ≤ bound) ∧
          base' + ls'.length ≤ K ∧ τ (M + tmpJ) ≤ K ∧ τ boundReg = bound) ∨
        (SplitTailEmitDone τ M curJ start base' carry' ls' pref' tail addr'
          cursorReg remainingReg freshReg ∧
          base' + ls'.length ≤ K ∧ τ (M + tmpJ) ≤ K)) := by
  induction n generalizing base carry ls pref addr σ with
  | zero =>
      exact ⟨σ, base, carry, ls, pref, addr, by simp,
        Or.inl ⟨hrel, hbound, hbase, htmp, hb⟩⟩
  | succ n ih =>
      obtain ⟨τ, base', carry', ls', pref', addr', hτ, hstate⟩ := ih
        (base := base) (carry := carry) (ls := ls) (pref := pref) (addr := addr)
        (σ := σ) hbound hbase htmp hrel hb
      have hsucc :
          loopEval
              (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
                pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
              (n + 1) σ =
            (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
              pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval τ := by
        rw [uniform_loopEval_succ_right, hτ]
      rcases hstate with ⟨hrel', hbound', hbase', htmp', hbτ⟩ | ⟨hdone', hbase', htmp'⟩
      · obtain ⟨τ', base'', carry'', ls'', pref'', addr'', hτ', hstate'⟩ :=
          splitTailEmitProgAt_tmp_bound_of_rel_step K M curJ tmpJ start cursorReg polReg varReg
            doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
            posPolReg freshReg boundReg bound base' carry' ls' pref' tail addr' τ hbound' hbase'
            htmp' hrel' hbτ hok hboundK honeTmp htwoTmp
        exact ⟨τ', base'', carry'', ls'', pref'', addr'', hτ'.trans hsucc.symm, hstate'⟩
      · have hzero := splitTailEmitStepProgAt_zero_eval curJ tmpJ cursorReg polReg varReg doneReg
          remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
          freshReg boundReg τ hdone'.remaining
        refine ⟨τ, base', carry', ls', pref', addr', hzero.symm.trans hsucc.symm,
          Or.inr ⟨hdone', hbase', htmp'⟩⟩

lemma splitTailEmitIntermediateProg_parser_values
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg bound : ℕ) (σ τp : Store) (polVal varVal : ℕ)
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    (hpol : τp polReg = polVal) (hvar : τp varReg = varVal)
    (hdone : τp doneReg = 1)
    (hframe : ∀ r, r = polReg ∨ r = varReg ∨ r = doneReg →
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg).eval τp r = τp r)
    (hrem : remainingReg ≠ polReg) (hremv : remainingReg ≠ varReg)
    (hremd : remainingReg ≠ doneReg) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ polReg = polVal ∧
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ varReg = varVal ∧
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ doneReg = 1 := by
  unfold splitTailEmitIntermediateProg
  rw [eval_seq, eval_seq, ← hτp]
  simp only [eval_assign, Expr.eval]
  refine ⟨?_, ?_, ?_⟩
  · rw [writeReg_diff _ remainingReg _ polReg hrem.symm]
    exact (hframe polReg (Or.inl rfl)).trans hpol
  · rw [writeReg_diff _ remainingReg _ varReg hremv.symm]
    exact (hframe varReg (Or.inr (Or.inl rfl))).trans hvar
  · rw [writeReg_diff _ remainingReg _ doneReg hremd.symm]
    exact (hframe doneReg (Or.inr (Or.inr rfl))).trans hdone


lemma uniform_emit_dispatch_one_tmp_value
    (N K base outer addr : ℕ) (l : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l] rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N) (hbound : l.var + 1 ≤ N)
    (hN : N ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec
      (uniformMNat N + uctTmpJ) ≤ K := by
  have haddr : addr + [l].length + 1 = addr + 2 := by simp
  have hbits : BitsFrom σdec (addr + 2) (encodeLiteral l ++ rest) := by
    simpa [haddr, splitTailInputBits] using hprep.input
  have hdec := decodeLiteralValueProgramAt_correct uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctSavedBoundReg N (addr + 2) l rest σdec
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by have := hprep.safety.cursor_below; have := hprep.start_at_input; omega)
    (by have := hprep.safety.pol_below; have := hprep.start_at_input; omega)
    (by have := hprep.safety.var_below; have := hprep.start_at_input; omega)
    (by have := hprep.safety.done_below; have := hprep.start_at_input; omega)
    hbound hsaved hprep.cursor hbits
  let τ := (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctSavedBoundReg).eval σdec
  have hτstate : WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref := by
    apply writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref σdec τ
      uctCursorReg uctPolReg uctVarReg uctDoneReg hprep.writer hdec.2.2.2.2
      (by decide) (by decide) (by decide) (by decide)
      hprep.safety.cursor_below hprep.safety.pol_below hprep.safety.var_below hprep.safety.done_below
  have hpol : τ uctPolReg = literalPolarity l := by
    cases l <;> simpa [τ, literalPolarity] using hdec.2.1
  have hvar : τ uctVarReg = l.var := by simpa [τ] using hdec.2.2.1
  have hpol01 : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hroom : uniformStartNat + pref.length + 3 * (l.var + 2) <
      uniformMNat N + uctCurJ := by
    have hr := hprep.room
    cases l <;>
       simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var, List.length_append] at hr ⊢ <;> omega
  have htmp := writerAppendClauseOneProg_tmp_value
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref uctPolReg uctVarReg
    (literalPolarity l) l.var τ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hpol hvar hpol01 ⟨hprep.safety.pol_below, hprep.safety.var_below⟩ hτstate hroom
  have hlen : σdec uctLengthReg = 1 := by simpa using hprep.length
  have hdispatch :
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
        uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec =
      (emitClauseCommitProg uctOuterReg).eval
        ((writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg).eval τ) := by
    simp only [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, eval_ifNZ]
    rw [ite_eq_right (by simp [Expr.eval, hlen]), ite_eq_left (by simp [Expr.eval, hlen])]
    simp [eval_seq, τ]
  rw [hdispatch]
  have hout : uctOuterReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctOuterReg, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hlK : l.var ≤ K := by omega
  have htmpLe :
      (writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg).eval τ
        (uniformMNat N + uctTmpJ) ≤ K := by
    calc
      _ = l.var := htmp
      _ ≤ K := hlK
  simpa [emitClauseCommitProg, eval_assign, Expr.eval,
    writeReg_diff _ uctOuterReg _ _ hout.symm] using htmpLe

/-- Both decoded literals and the writer state after their dispatch decodes. -/
lemma uniform_emit_dispatch_two_tmp_value_decode_state
    (N base outer addr : ℕ) (l1 l2 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2] rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N) :
    ∃ υ,
      υ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval
        ((decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg).eval σdec) ∧
      WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref ∧
      υ uctPolReg = literalPolarity l1 ∧ υ uctVarReg = l1.var ∧
      υ uctPol2Reg = literalPolarity l2 ∧ υ uctVar2Reg = l2.var := by
  have haddr : addr + [l1, l2].length + 1 = addr + 3 := by simp
  have hbits : BitsFrom σdec (addr + 3) (encodeLiteral l1 ++ encodeLiteral l2 ++ rest) := by
    simpa [haddr, splitTailInputBits, List.append_assoc] using hprep.input
  obtain ⟨τ, υ, hτ, hυ, _, hpol1, hvar1, _, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct uctCursorReg uctPolReg uctVarReg uctPol2Reg uctVar2Reg
      uctDoneReg N (addr + 3) l1 l2 rest σdec
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨by have := hprep.safety.cursor_below; have := hprep.start_at_input; omega,
        by have := hprep.safety.pol_below; have := hprep.start_at_input; omega,
        by have := hprep.safety.var_below; have := hprep.start_at_input; omega,
        by have := hprep.start_at_input; simp [uctPol2Reg, uniformStartNat, relocateControlGap] at *; omega,
        by have := hprep.start_at_input; simp [uctVar2Reg, uniformStartNat, relocateControlGap] at *; omega,
        by have := hprep.safety.done_below; have := hprep.start_at_input; omega⟩
      hbound1 hbound2 hprep.cursor hbits
  have hA1 := decodeLiteralValueProgramAt_eq uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctSavedBoundReg N σdec hsaved (by decide) (by decide) (by decide) (by decide)
  have hbτ : τ uctSavedBoundReg = N :=
    (hframe1 uctSavedBoundReg (by decide) (by decide) (by decide) (by decide)).trans hsaved
  have hA2 := decodeLiteralValueProgramAt_eq uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
    uctSavedBoundReg N τ hbτ (by decide) (by decide) (by decide) (by decide)
  have hτAt : τ = (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctSavedBoundReg).eval σdec := hτ.trans hA1.symm
  have hυAt : υ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
      uctSavedBoundReg).eval
      ((decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctSavedBoundReg).eval σdec) := by
    calc
      υ = (decodeLiteralValueProgram uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg N).eval τ := hυ
      _ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
          uctSavedBoundReg).eval τ := hA2.symm
      _ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
          uctSavedBoundReg).eval
          ((decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg).eval σdec) := by rw [hτAt]
  have hτstate : WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref := by
    apply writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref σdec τ
      uctCursorReg uctPolReg uctVarReg uctDoneReg hprep.writer hframe1
      (by decide) (by decide) (by decide) (by decide)
      hprep.safety.cursor_below hprep.safety.pol_below hprep.safety.var_below hprep.safety.done_below
  have hυstate : WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref := by
    apply writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref τ υ
      uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg hτstate hframe2
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hp1υ : υ uctPolReg = literalPolarity l1 := by
    exact (hframe2 uctPolReg (by decide) (by decide) (by decide) (by decide)).trans
      (by cases l1 <;> simpa [hτ, literalPolarity] using hpol1)
  have hv1υ : υ uctVarReg = l1.var := by
    exact (hframe2 uctVarReg (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa [hτ] using hvar1)
  have hp2υ : υ uctPol2Reg = literalPolarity l2 := by
    cases l2 <;> simpa [hυ, literalPolarity] using hpol2
  have hv2υ : υ uctVar2Reg = l2.var := by simpa [hυ] using hvar2
  exact ⟨υ, hυAt, hυstate, hp1υ, hv1υ, hp2υ, hv2υ⟩

/-- The second decoded literal becomes the append program's temporary value. -/
lemma uniform_emit_dispatch_two_tmp_value_append
    (N base outer addr : ℕ) (l1 l2 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2] rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N) :
    ∃ υ,
      υ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval
        ((decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg).eval σdec) ∧
      WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref ∧
      υ uctPolReg = literalPolarity l1 ∧ υ uctVarReg = l1.var ∧
      υ uctPol2Reg = literalPolarity l2 ∧ υ uctVar2Reg = l2.var ∧
      (writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
        uctVar2Reg).eval υ (uniformMNat N + uctTmpJ) = l2.var := by
  obtain ⟨υ, hυAt, hυstate, hp1υ, hv1υ, hp2, hv2⟩ :=
    uniform_emit_dispatch_two_tmp_value_decode_state N base outer addr l1 l2 rest pref σr σdec
      hprep hsaved hbound1 hbound2
  have hp01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hp02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hroom : uniformStartNat + pref.length + l1.var + 2 * l2.var + 6 <
      uniformMNat N + uctCurJ := by
    have hr := hprep.room
    cases l1 <;> cases l2 <;>
       simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var, List.length_append] at hr ⊢ <;> omega
  have htmp := writerAppendClauseTwoProg_tmp_value
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
    uctPolReg uctVarReg uctPol2Reg uctVar2Reg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var υ
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hp1υ hv1υ hp2 hv2 hp01 hp02
    hprep.safety.var_below
    (by simp [uctPol2Reg, uctVar2Reg, uniformStartNat, relocateControlGap]) hυstate hroom
  exact ⟨υ, hυAt, hυstate, hp1υ, hv1υ, hp2, hv2, htmp⟩

lemma uniform_emit_dispatch_two_tmp_value
    (N K base outer addr : ℕ) (l1 l2 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2] rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hN : N ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec
      (uniformMNat N + uctTmpJ) ≤ K := by
  obtain ⟨υ, hυAt, hυstate, hp1υ, hv1υ, hp2, hv2, htmp⟩ :=
    uniform_emit_dispatch_two_tmp_value_append N base outer addr l1 l2 rest pref σr σdec
      hprep hsaved hbound1 hbound2
  have hlen : σdec uctLengthReg = 2 := by simpa using hprep.length
  have hdispatch :
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
        uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec =
      (emitClauseCommitProg uctOuterReg).eval
        ((writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg).eval υ) := by
    simp only [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, eval_ifNZ]
    rw [ite_eq_right (by simp [Expr.eval, hlen]), ite_eq_right (by simp [Expr.eval, hlen]),
      ite_eq_left (by simp [Expr.eval, hlen])]
    simp only [eval_seq]
    rw [← hυAt]
  rw [hdispatch]
  have hout : uctOuterReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctOuterReg, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hl2K : l2.var ≤ K := by omega
  have htmpLe :
      (writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg).eval υ
        (uniformMNat N + uctTmpJ) ≤ K := by
    calc
      _ = l2.var := htmp
      _ ≤ K := hl2K
  simpa [emitClauseCommitProg, eval_assign, Expr.eval,
    writeReg_diff _ uctOuterReg _ _ hout.symm] using htmpLe

end NPComplete.CookLevin

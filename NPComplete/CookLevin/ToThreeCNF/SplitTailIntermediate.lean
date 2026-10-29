module

public import NPComplete.CookLevin.ToThreeCNF.SplitTailFrame

/-!
# Intermediate split-tail relation

The loop's temporary decode and carry state is not yet the outer emitter's
clause-boundary relation. This module reconstructs that relation from the
intermediate links, writer state, and remaining-input bounds.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
  (BitsFrom bitsFrom_append bitsFrom_writeReg bitsFrom_of_eq_on BitsAt bitsAt_of_frame finalizeOutputProg FinalizeRegsOk ctlCell ctlCell_eval)
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same cost_seq
    cost_ifNZ cost_forN eval_ifNZ eval_forN loopEval loopEval_succ
    loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

/-- Capacity slack of a split-tail step: the writer has room for the linking triple
    before the end of the output region. -/
lemma splitTailEmitRel_intermediate_to_rel_room
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    start + pref.length + carry.var + l.var + base + 8 < M + curJ := by
  have hlinkLen : carry.var + l.var + base + 6 ≤
      (encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base).length := by
    cases carry <;> cases l <;>
      simp [encodedThreeLiteralBits, encodedLiteralBits,
        encodeNat_length, Literal.var, literalPolarity, natBit] <;> omega
  have hc := hrel.capacity
  rw [splitTailPayload_cons3, hrel.carry_one] at hc
  simp only [List.length_append] at hc ⊢
  omega

/-- After decoding the head literal, the writer registers keep their values, the decoded
    literal sits in `polReg`/`varReg`, and the remaining input is untouched. -/
lemma splitTailEmitRel_intermediate_to_rel_decode
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τp : Store}
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ) :
    WriterState τp M curJ start pref ∧ τp carryPolReg = 1 ∧ τp carryValReg = carry.var ∧
      τp posPolReg = 0 ∧ τp freshReg = base ∧
      τp remainingReg = (l :: l2 :: l3 :: rest).length ∧
      τp varReg = l.var ∧ τp polReg = literalPolarity l ∧
      BitsFrom τp (addr + l.var + 2) (splitTailInputBits (l2 :: l3 :: rest) tail) := by
  have hbits : BitsFrom σ addr
      (encodeLiteral l ++ splitTailInputBits (l2 :: l3 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hrel.safety.main.below
  have hstartAddr := hrel.start_at_input
  obtain ⟨_, hpol, hvar, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l
      (splitTailInputBits (l2 :: l3 :: rest) tail) σ
      hrel.safety.main.distinct.1 hrel.safety.main.distinct.2.1
      hrel.safety.main.distinct.2.2.1 hrel.safety.main.distinct.2.2.2.1
      hrel.safety.main.distinct.2.2.2.2.1 hrel.safety.main.distinct.2.2.2.2.2
      (by omega) (by omega) (by omega) (by omega) hbound hrel.cursor hbits
  subst hτp
  have hkeep : ∀ r, (r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
      r = freshReg ∨ r = remainingReg) → ∀ v, σ r = v →
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ r = v := by
    intro r hr v hv
    have h := hrel.safety.writer_parser r hr
    exact (hdecFrame r h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans hv
  refine ⟨?_, hkeep _ (Or.inl rfl) _ hrel.carry_pol,
    hkeep _ (Or.inr (Or.inl rfl)) _ hrel.carry_val,
    hkeep _ (Or.inr (Or.inr (Or.inl rfl))) _ hrel.pos,
    hkeep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hrel.fresh,
    hkeep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _ hrel.remaining, hvar, ?_, ?_⟩
  · exact writerState_transport_of_frame4 M curJ start pref σ _
      cursorReg polReg varReg doneReg hrel.writer hdecFrame
      hrel.safety.main.nonzero.1 hrel.safety.main.nonzero.2.1
      hrel.safety.main.nonzero.2.2.1 hrel.safety.main.nonzero.2.2.2 hb1 hb2 hb3 hb4
  · cases l <;> simpa [literalPolarity] using hpol
  · obtain ⟨_, ht⟩ := bitsFrom_append σ addr (encodeLiteral l)
      (splitTailInputBits (l2 :: l3 :: rest) tail) hbits
    have hlen : (encodeLiteral l).length = l.var + 2 := by
      cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
    rw [hlen] at ht
    intro i hi
    exact (hdecFrame (addr + l.var + 2 + i) (by omega) (by omega) (by omega) (by omega)).trans
      (ht i hi)

/-- The linking triple written after decoding changes no low register other than the two
    link registers, and keeps the remaining input readable. -/
lemma splitTailEmitRel_intermediate_to_rel_link
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τp τw : Store}
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    (hτw : τw = (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg
      polReg varReg posPolReg freshReg).eval τp) :
    (∀ r, r < start → r ≠ carryValReg → r ≠ freshReg → τw r = τp r) ∧
      BitsFrom τw (addr + l.var + 2) (splitTailInputBits (l2 :: l3 :: rest) tail) := by
  obtain ⟨hst, hcp, hcv, hpos, hfresh, -, hvar, hpol, htail⟩ :=
    splitTailEmitRel_intermediate_to_rel_decode hbound hrel hτp
  have hpol01 : τp polReg = 0 ∨ τp polReg = 1 := by
    rw [hpol]; cases l <;> simp [literalPolarity]
  have hroom := splitTailEmitRel_intermediate_to_rel_room hrel
  obtain ⟨hw1, hw2, hw3, hw4, -⟩ := hrel.safety.writer_below
  obtain ⟨-, hb2, hb3, -⟩ := hrel.safety.main.below
  subst hτw
  constructor
  · intro r hr hrv hrf
    have hb := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      carryPolReg carryValReg polReg varReg posPolReg freshReg
      1 carry.var (τp polReg) l.var 0 base τp hrel.cur_j_pos hrel.tmp_j_pos
      hcp hcv rfl hvar hpos hfresh (Or.inr rfl) hpol01 (Or.inl rfl)
      hw2 ⟨hb2, hb3⟩ ⟨hw3, hw4⟩ hst (by omega) hr
    dsimp [writerAppendSplitTailLinkDynamicProg]
    simp only [eval_seq, eval_assign, Expr.eval]
    rw [writeReg_diff _ freshReg _ r hrf, writeReg_diff _ carryValReg _ r hrv]
    exact hb
  · have hinputHigh : M + tmpJ < addr + l.var + 2 := by
      have := hrel.input_above
      omega
    exact writerAppendSplitTailLinkDynamicProg_bitsFrom_frame M curJ tmpJ start pref
      (splitTailInputBits (l2 :: l3 :: rest) tail)
      (addr + l.var + 2) carryPolReg carryValReg polReg varReg posPolReg freshReg
      1 carry.var l.var base τp hrel.cur_j_pos hrel.tmp_j_pos hcp hcv
      hpol01 hvar hpos hfresh (Or.inr rfl) hw2 hb2 hb3 hw3 hw4
      hst (by omega) hinputHigh htail

/-- The decode-then-link part of the step evaluates to the expected writer state,
    remaining count, link registers and cursor. -/
lemma splitTailEmitRel_intermediate_to_rel_writer_eval
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τ : Store}
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ) :
    WriterState τ M curJ start
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base) ∧
      τ remainingReg = (l :: l2 :: l3 :: rest).length - 1 ∧ τ carryValReg = base ∧
      τ freshReg = base + 1 ∧ τ cursorReg = addr + l.var + 2 := by
  subst hτ
  have hbits : BitsFrom σ addr
      (encodeLiteral l ++ splitTailInputBits (l2 :: l3 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  obtain ⟨-, -, -, -, -, hcvf, hcvr, -, -, hfr⟩ := hrel.safety.writer_distinct
  have hwd : ∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
      r = freshReg ∨ r = remainingReg →
      r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg := fun r hr => by
    have h := hrel.safety.writer_parser r hr
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  exact splitTailEmitIntermediateProg_eval M curJ tmpJ start pref
    (splitTailInputBits (l2 :: l3 :: rest) tail)
    cursorReg polReg varReg doneReg remainingReg
    carryPolReg carryValReg posPolReg freshReg bound addr
    1 carry.var base (l :: l2 :: l3 :: rest).length l σ
    hrel.cur_j_pos hrel.tmp_j_pos hrel.carry_pol hrel.carry_val hrel.pos hrel.fresh hrel.remaining
    (Or.inr rfl) hrel.safety.writer_below.2.1
    hrel.safety.writer_below.2.2.1 hrel.safety.writer_below.2.2.2.1
    hrel.safety.writer_below.2.2.2.2 hrel.safety.remaining_nonzero
    hcvr.symm hfr.symm hrel.safety.writer_nonzero.1
    hrel.safety.writer_nonzero.2 hcvf hrel.safety.main.below hrel.safety.main.nonzero
    hrel.safety.main.distinct.1 hrel.safety.main.distinct.2.1
    hrel.safety.main.distinct.2.2.1 hrel.safety.main.distinct.2.2.2.1
    hrel.safety.main.distinct.2.2.2.2.1 hrel.safety.main.distinct.2.2.2.2.2
    hwd hrel.start_at_input hbound hrel.cursor hbits hrel.writer
    (splitTailEmitRel_intermediate_to_rel_room hrel)

/-- The final assignment to `remainingReg` is the only difference between the step and
    its decode-then-link prefix. -/
lemma splitTailEmitRel_intermediate_to_rel_remaining_frame
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) (σ : Store) {r : ℕ}
    (hr : r ≠ remainingReg) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ r =
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg
      polReg varReg posPolReg freshReg).eval
      ((decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ) r := by
  simp only [splitTailEmitIntermediateProg, eval_seq, eval_assign, Expr.eval]
  exact writeReg_diff _ remainingReg _ r hr

lemma splitTailEmitRel_intermediate_to_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ,
      τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ ∧
      SplitTailEmitRel τ M curJ tmpJ start (base + 1) (Literal.neg base)
        (l2 :: l3 :: rest)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
        tail (addr + l.var + 2)
        cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
        carryPolReg carryValReg posPolReg freshReg := by
  obtain ⟨τp, hτp⟩ : ∃ τp, τp =
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ := ⟨_, rfl⟩
  obtain ⟨τw, hτw⟩ : ∃ τw, τw = (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg
    carryValReg polReg varReg posPolReg freshReg).eval τp := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg
    doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ := ⟨_, rfl⟩
  obtain ⟨-, hcp, -, hpos, -, -, -, -, -⟩ :=
    splitTailEmitRel_intermediate_to_rel_decode hbound hrel hτp
  obtain ⟨hdyn, hbitsw⟩ := splitTailEmitRel_intermediate_to_rel_link hbound hrel hτp hτw
  obtain ⟨hws, hrem, hcv, hfr, hcur⟩ :=
    splitTailEmitRel_intermediate_to_rel_writer_eval hbound hrel hτ
  have hτrem : ∀ r, r ≠ remainingReg → τ r = τw r := fun r hr => by
    rw [hτ, hτw, hτp]
    exact splitTailEmitRel_intermediate_to_rel_remaining_frame curJ tmpJ cursorReg polReg
      varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ hr
  obtain ⟨hcpv, hcpp, hcpf, hcpr, hcvp, hcvf, hcvr, hpf, hpr, hfrr⟩ :=
    hrel.safety.writer_distinct
  have hstartAddr := hrel.start_at_input
  have hlt := hrel.safety.writer_below.2.2.2.2
  refine ⟨τ, hτ, ?_, hrel.cur_j_pos, hrel.tmp_j_pos,
    lt_of_lt_of_le hrel.input_above (by omega), le_trans hstartAddr (by omega), hws,
    ?_, by simp [literalPolarity], hcv, ?_, hfr, by rw [hrem]; simp, hcur, ?_, hrel.safety⟩
  · intro i hi
    have h := hbitsw i hi
    rw [hτrem _ (by omega)]
    exact h
  · rw [hτrem _ hcpr, hdyn _ hrel.safety.writer_below.1 hcpv hcpf]
    exact hcp
  · rw [hτrem _ hpr, hdyn _ hrel.safety.writer_below.2.2.1 hcvp.symm hpf]
    exact hpos
  · have hc := hrel.capacity
    rw [splitTailPayload_cons3, hrel.carry_one] at hc
    simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc

/-- Decoding the head literal changes only the four parser registers. -/
lemma decodeLiteralValueProgram_frame_of_rel_decode_frame
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τp : Store}
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    {r : ℕ} (h1 : r ≠ cursorReg) (h2 : r ≠ polReg) (h3 : r ≠ varReg) (h4 : r ≠ doneReg) :
    τp r = σ r := by
  have hbits : BitsFrom σ addr
      (encodeLiteral l ++ splitTailInputBits (l2 :: l3 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hrel.safety.main.below
  have hstartAddr := hrel.start_at_input
  obtain ⟨-, -, -, -, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l
      (splitTailInputBits (l2 :: l3 :: rest) tail) σ
      hrel.safety.main.distinct.1 hrel.safety.main.distinct.2.1
      hrel.safety.main.distinct.2.2.1 hrel.safety.main.distinct.2.2.2.1
      hrel.safety.main.distinct.2.2.2.2.1 hrel.safety.main.distinct.2.2.2.2.2
      (by omega) (by omega) (by omega) (by omega) hbound hrel.cursor hbits
  subst hτp
  exact hdecFrame r h1 h2 h3 h4

/-- The linking writer leaves the high input region unchanged after decoding. -/
lemma writerAppendSplitTailLinkDynamicProg_frame_of_rel_link_high
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τp : Store}
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg
      polReg varReg posPolReg freshReg).eval τp r = τp r := by
  obtain ⟨hst, hcp, hcv, hpos, hfresh, -, hvar, hpol, -⟩ :=
    splitTailEmitRel_intermediate_to_rel_decode hbound hrel hτp
  have hpol01 : τp polReg = 0 ∨ τp polReg = 1 := by
    rw [hpol]; cases l <;> simp [literalPolarity]
  have hroom := splitTailEmitRel_intermediate_to_rel_room hrel
  obtain ⟨hw1, hw2, hw3, hw4, -⟩ := hrel.safety.writer_below
  obtain ⟨-, hb2, hb3, -⟩ := hrel.safety.main.below
  exact writerAppendSplitTailLinkDynamicProg_frame_high M curJ tmpJ start pref
    carryPolReg carryValReg polReg varReg posPolReg freshReg
    1 carry.var l.var base τp hrel.cur_j_pos hrel.tmp_j_pos hcp hcv
    hpol01 hvar hpos hfresh (Or.inr rfl) hw2 hb2 hb3 hw3 hw4 hst (by omega) hr

/-- The linking writer leaves every register above its output region unchanged after
    decoding. -/
lemma writerAppendSplitTailLinkDynamicProg_frame_of_rel_link_after
    {M curJ tmpJ start base : ℕ} {carry l l2 l3 : Literal} {rest : List Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {τp : Store}
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
    {r : ℕ} (hr : start + pref.length + carry.var + l.var + base + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg
      polReg varReg posPolReg freshReg).eval τp r = τp r := by
  obtain ⟨hst, hcp, hcv, hpos, hfresh, -, hvar, hpol, -⟩ :=
    splitTailEmitRel_intermediate_to_rel_decode hbound hrel hτp
  have hpol01 : τp polReg = 0 ∨ τp polReg = 1 := by
    rw [hpol]; cases l <;> simp [literalPolarity]
  have hroom := splitTailEmitRel_intermediate_to_rel_room hrel
  exact writerAppendSplitTailLinkDynamicProg_frame_after M curJ tmpJ start pref
    carryPolReg carryValReg polReg varReg posPolReg freshReg
    1 carry.var l.var base τp hrel.cur_j_pos hrel.tmp_j_pos hcp hcv hpol01
    hvar hpos hfresh (Or.inr rfl)
    hrel.safety.writer_below.2.1
    hrel.safety.main.below.2.1 hrel.safety.main.below.2.2.1
    hrel.safety.writer_below.2.2.1 hrel.safety.writer_below.2.2.2.1
    hst (by omega) hr hrc hrt

lemma splitTailEmitIntermediateProg_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    (∀ r, M + tmpJ < r →
      (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r) ∧
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ posPolReg = 0 := by
  obtain ⟨-, -, -, hpos, -⟩ :=
    splitTailEmitRel_intermediate_to_rel_decode hbound hrel (τp := _) rfl
  have hroom := splitTailEmitRel_intermediate_to_rel_room hrel
  have hcurJ := hrel.cur_j_pos
  have htmpJ := hrel.tmp_j_pos
  have hremBelow := hrel.safety.writer_below.2.2.2.2
  obtain ⟨b1, b2, b3, b4⟩ := hrel.safety.main.below
  obtain ⟨-, -, -, -, hcvp, -, -, hpf, hpr, -⟩ := hrel.safety.writer_distinct
  refine ⟨fun r hr => ?_, ?_⟩
  · have hrem : r ≠ remainingReg := by omega
    rw [splitTailEmitRel_intermediate_to_rel_remaining_frame curJ tmpJ cursorReg polReg
      varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ hrem,
      writerAppendSplitTailLinkDynamicProg_frame_of_rel_link_high hbound hrel rfl hr]
    exact decodeLiteralValueProgram_frame_of_rel_decode_frame hbound hrel rfl
      (by omega) (by omega) (by omega) (by omega)
  · rw [splitTailEmitRel_intermediate_to_rel_remaining_frame curJ tmpJ cursorReg polReg
      varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ hpr,
      (splitTailEmitRel_intermediate_to_rel_link hbound hrel rfl rfl).1 posPolReg
        hrel.safety.writer_below.2.2.1 hcvp.symm hpf]
    exact hpos

lemma splitTailEmitIntermediateProg_after_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : start + pref.length + carry.var + l.var + base + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  have hroom := splitTailEmitRel_intermediate_to_rel_room hrel
  have hremBelow := hrel.safety.writer_below.2.2.2.2
  obtain ⟨b1, b2, b3, b4⟩ := hrel.safety.main.below
  have hrem : r ≠ remainingReg := by omega
  rw [splitTailEmitRel_intermediate_to_rel_remaining_frame curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ hrem,
    writerAppendSplitTailLinkDynamicProg_frame_of_rel_link_after hbound hrel rfl hr hrc hrt]
  exact decodeLiteralValueProgram_frame_of_rel_decode_frame hbound hrel rfl
    (by omega) (by omega) (by omega) (by omega)

lemma splitTailEmitIntermediateProg_low_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
      r ≠ carryValReg ∧ r ≠ posPolReg ∧ r ≠ freshReg ∧ r ≠ remainingReg) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  obtain ⟨hrc, hrp, hrv, hrd, hcv, -, hfr, hrem⟩ := hrsafe
  rw [splitTailEmitRel_intermediate_to_rel_remaining_frame curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ hrem,
    (splitTailEmitRel_intermediate_to_rel_link hbound hrel rfl rfl).1 r hr hcv hfr]
  exact decodeLiteralValueProgram_frame_of_rel_decode_frame hbound hrel rfl hrc hrp hrv hrd

def splitTailEmitStepWriteSet
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ) : List ℕ :=
  [cursorReg, polReg, varReg, doneReg, remainingReg, pol2Reg, var2Reg,
    pol3Reg, var3Reg, carryPolReg, carryValReg, posPolReg, freshReg]


end NPComplete.CookLevin

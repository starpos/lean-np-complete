module

public import NPComplete.CookLevin.ToThreeCNF.SplitTailRel

/-!
# Terminal split-tail cases

When the remaining clause suffix has at most two literals, the loop must flush
the final short clause and return to the outer emitter. This module proves those
terminal transitions, the room and payload facts they need, and the high-memory
frame of the one-literal case.
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
lemma splitTailEmitTerminalOneProg_high_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∀ r, M + tmpJ < r →
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  have hroom : start + pref.length + carry.var + 2 * l.var + 8 < M + curJ := by
    have hc := hrel.capacity
    have hlen : carry.var + 2 * l.var + 6 ≤
        (splitTailPayload base carry [l]).length := by
      cases carry <;> cases l <;>
        simp [splitTailPayload, encodeThreeClause, encodeLiteral,
          encodeNat_length, Literal.var] <;> omega
    omega
  have hwd : ∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = remainingReg →
      r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ doneReg := by
    intro r hr
    have h := hrel.safety.writer_parser r (by
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
    exact ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.1⟩
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  have hparserBelow : cursorReg < start ∧ pol2Reg < start ∧
      var2Reg < start ∧ doneReg < start := by
    exact ⟨hrel.safety.second.below.1, hrel.safety.second.below.2.1,
      hrel.safety.second.below.2.2.1, hrel.safety.second.below.2.2.2⟩
  have hparserNonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧
      var2Reg ≠ 0 ∧ doneReg ≠ 0 := by
    exact ⟨hrel.safety.second.nonzero.1, hrel.safety.second.nonzero.2.1,
      hrel.safety.second.nonzero.2.2.1, hrel.safety.second.nonzero.2.2.2⟩
  obtain ⟨_, hpol2, hvar2, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      (lt_of_lt_of_le hparserBelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hparserBelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hparserBelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hparserBelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  let τp := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg pol2Reg var2Reg doneReg hrel.writer
      (by simpa [τp] using hdecFrame)
      hparserNonzero.1 hparserNonzero.2.1 hparserNonzero.2.2.1 hparserNonzero.2.2.2
      hparserBelow.1 hparserBelow.2.1 hparserBelow.2.2.1 hparserBelow.2.2.2
  have hcarryPolτ : τp carryPolReg = 1 := by
    have hf := hdecFrame carryPolReg
      (hwd carryPolReg (Or.inl rfl)).1 (hwd carryPolReg (Or.inl rfl)).2.1
      (hwd carryPolReg (Or.inl rfl)).2.2.1 (hwd carryPolReg (Or.inl rfl)).2.2.2
    simpa [τp] using hf.trans hrel.carry_pol
  have hcarryValτ : τp carryValReg = carry.var := by
    have hf := hdecFrame carryValReg
      (hwd carryValReg (Or.inr (Or.inl rfl))).1
      (hwd carryValReg (Or.inr (Or.inl rfl))).2.1
      (hwd carryValReg (Or.inr (Or.inl rfl))).2.2.1
      (hwd carryValReg (Or.inr (Or.inl rfl))).2.2.2
    simpa [τp] using hf.trans hrel.carry_val
  have hpol2' : τp pol2Reg = literalPolarity l := by
    cases l <;> simpa [τp, literalPolarity] using hpol2
  have hvar2' : τp var2Reg = l.var := by simpa [τp] using hvar2
  have hpolCase : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hstartWorkspace : start < M + curJ := by
    have hc := hrel.capacity
    omega
  have hhighParser : ∀ r, M + tmpJ < r → τp r = σ r := by
    intro r hr
    have htmp := hrel.tmp_j_pos
    have hstart := hstartWorkspace
    have hf := hdecFrame r (by omega) (by omega) (by omega) (by omega)
    simpa [τp] using hf
  intro r hr
  have hw := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var τp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPolτ hcarryValτ hpol2' hvar2' hpol2' hvar2'
    (Or.inr rfl) hpolCase hpolCase
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    hτstate (by omega) hr
  have hrem : r ≠ remainingReg := by
    have hstart := hstartWorkspace
    have htmp := hrel.tmp_j_pos
    have hremBelow := hrel.safety.writer_below.2.2.2.2
    omega
  rw [splitTailEmitTerminalOneProg, eval_seq, eval_seq, eval_assign, Expr.eval]
  have hw' := (writeReg_diff
      ((writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
        pol2Reg var2Reg).eval τp) remainingReg 0 r hrem).trans hw
  exact hw'.trans (hhighParser r hr)

/-- Capacity of the split-tail payload yields the room the one-literal terminal writer needs. -/
lemma splitTailEmitRel_one_to_done_room
    (base start M curJ : ℕ) (carry l : Literal) (pref : Bits)
    (hc : start + pref.length + (splitTailPayload base carry [l]).length + 2 < M + curJ) :
    start + pref.length + carry.var + 2 * l.var + 8 < M + curJ := by
  have hlen : carry.var + 2 * l.var + 6 ≤
      (splitTailPayload base carry [l]).length := by
    cases carry <;> cases l <;>
      simp [splitTailPayload, encodeThreeClause, encodeLiteral,
        encodeNat_length, Literal.var]
    <;> omega
  omega

/-- When `literalPolarity carry = 1` (`hpol`), the three-literal bits written
    by the one-literal terminal writer are the split-tail payload. -/
lemma splitTailEmitRel_one_to_done_payload
    (base : ℕ) (carry l : Literal) (hpol : literalPolarity carry = 1) :
    encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var
        (literalPolarity l) l.var = splitTailPayload base carry [l] := by
  cases carry with
  | pos v => simp [literalPolarity] at hpol
  | neg v =>
    cases l <;> simp [splitTailPayload, encodedThreeLiteralBits, encodedLiteralBits,
      encodeThreeClause, encodeLiteral, Literal.var, literalPolarity, natBit]

/-- Length of the input consumed by a one-literal split-tail. -/
lemma splitTailEmitRel_one_to_done_input_length (l : Literal) :
    (splitTailInputBits [l] []).length = l.var + 2 := by
  cases l <;> simp [splitTailInputBits, encodeLiteral, encodeNat_length, Literal.var]

/-- Skipping one encoded literal leaves the tail readable at the shifted address. -/
lemma splitTailEmitRel_one_to_done_tail_bits
    (σ : Store) (addr : ℕ) (l : Literal) (tail : Bits)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ tail)) :
    BitsFrom σ (addr + l.var + 2) tail := by
  obtain ⟨_, ht⟩ := bitsFrom_append σ addr (encodeLiteral l) tail hbits
  have hlen : (encodeLiteral l).length = l.var + 2 := by
    cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  rw [hlen] at ht
  exact ht

/-- Writer registers are disjoint from every parser register used by the one-literal decode. -/
lemma splitTailEmitRel_one_to_done_writer_apart
    {start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hsafe : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg ∨ r = remainingReg) :
    r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ doneReg := by
  obtain ⟨hc, _, _, hd, hp2, hv2, _, _⟩ := hsafe.writer_parser r hr
  exact ⟨hc, hp2, hv2, hd⟩

/-- The decode step of the one-literal terminal program leaves a writer state with the decoded
literal value in the parser registers and everything else unchanged. -/
lemma splitTailEmitRel_one_to_done_parsed
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τp,
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ =
        (splitTailEmitTerminalOneWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
          pol2Reg var2Reg).eval τp ∧
      WriterState τp M curJ start pref ∧
      τp carryPolReg = 1 ∧ τp carryValReg = carry.var ∧
      τp pol2Reg = literalPolarity l ∧ τp var2Reg = l.var ∧
      τp cursorReg = addr + l.var + 2 ∧
      (∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ doneReg → τp r = σ r) := by
  have hstart := hrel.start_at_input
  have hs2 := hrel.safety.second
  obtain ⟨hb2c, hb2p, hb2v, hb2d⟩ := hs2.below
  obtain ⟨hcp, hcv, hcd, hpv, hpd, hvd⟩ := hs2.distinct
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  obtain ⟨hcur, hpol, hvar, -, hframe⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hcp hcv hcd hpv hpd hvd (by omega) (by omega) (by omega) (by omega) hbound
      hrel.cursor hbits
  have hτstate : WriterState
      ((decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ)
      M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ _ cursorReg pol2Reg var2Reg doneReg
      hrel.writer hframe hs2.nonzero.1 hs2.nonzero.2.1 hs2.nonzero.2.2.1 hs2.nonzero.2.2.2
      hb2c hb2p hb2v hb2d
  obtain ⟨a1, a2, a3, a4⟩ :=
    splitTailEmitRel_one_to_done_writer_apart hrel.safety (Or.inl rfl)
  obtain ⟨c1, c2, c3, c4⟩ :=
    splitTailEmitRel_one_to_done_writer_apart hrel.safety (Or.inr (Or.inl rfl))
  refine ⟨_, ?_, hτstate, (hframe _ a1 a2 a3 a4).trans hrel.carry_pol,
    (hframe _ c1 c2 c3 c4).trans hrel.carry_val, ?_, hvar, hcur, hframe⟩
  · simp [splitTailEmitTerminalOneProg, splitTailEmitTerminalOneWriterProg, eval_seq]
  · cases l <;> simpa [literalPolarity] using hpol

/-- The tail input stays readable after the parser registers change. -/
lemma splitTailEmitRel_one_to_done_tail_transport
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ τp : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hall : ∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ doneReg → τp r = σ r) :
    BitsFrom τp (addr + l.var + 2) tail := by
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  have htail := splitTailEmitRel_one_to_done_tail_bits σ addr l tail hbits
  have hstart := hrel.start_at_input
  obtain ⟨hb2c, hb2p, hb2v, hb2d⟩ := hrel.safety.second.below
  intro i hi
  rw [hall _ (by omega) (by omega) (by omega) (by omega)]
  exact htail i hi

/-- The terminal writer step turns a parsed state into the finished split-tail endpoint. -/
lemma splitTailEmitRel_one_to_done_emit
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ υp : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hυstate : WriterState υp M curJ start pref)
    (hcarryPol : υp carryPolReg = 1) (hcarryVal : υp carryValReg = carry.var)
    (hpol : υp pol2Reg = literalPolarity l) (hvar : υp var2Reg = l.var)
    (hcur : υp cursorReg = addr + l.var + 2)
    (hfresh : υp freshReg = base)
    (htail : BitsFrom υp (addr + l.var + 2) tail) :
    SplitTailEmitDone
      ((splitTailEmitTerminalOneWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
        pol2Reg var2Reg).eval υp)
      M curJ start base carry [l] pref tail addr cursorReg remainingReg freshReg := by
  have hroom := splitTailEmitRel_one_to_done_room base start M curJ carry l pref hrel.capacity
  have hl : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hrc : cursorReg ≠ remainingReg :=
    (hrel.safety.writer_parser remainingReg (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1.symm
  have hfr : freshReg ≠ remainingReg := hrel.safety.writer_distinct.2.2.2.2.2.2.2.2.2
  have hwe := splitTailEmitTerminalOneWriterProg_eval M curJ tmpJ start pref
    remainingReg carryPolReg carryValReg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol hvar (Or.inr rfl) hl
    hrel.safety.writer_below.2.1 hrel.safety.second.below.2.1
    hrel.safety.second.below.2.2.1 hrel.safety.writer_below.2.2.2.2
    hrel.safety.remaining_nonzero hυstate (by omega)
  have hwf := fun r (hr : r < start) (hne : r ≠ remainingReg) =>
    splitTailEmitTerminalOneWriterProg_frame M curJ tmpJ start pref
      remainingReg carryPolReg carryValReg pol2Reg var2Reg
      1 carry.var (literalPolarity l) l.var υp
      hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol hvar (Or.inr rfl) hl
      hrel.safety.writer_below.2.1 hrel.safety.second.below.2.1
      hrel.safety.second.below.2.2.1 hυstate (by omega) hr hne
  have hbitsW := writerAppendThreeRegsProg_bitsFrom_frame M curJ tmpJ start pref tail
    (addr + l.var + 2) carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol hvar hpol hvar (Or.inr rfl) hl hl
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    hυstate (by omega) (by have := hrel.input_above; omega) htail
  have hlenInput := splitTailEmitRel_one_to_done_input_length l
  have hpay := splitTailEmitRel_one_to_done_payload base carry l hrel.carry_one
  have hcurFinal := (hwf cursorReg hrel.safety.main.below.1 hrc).trans hcur
  refine ⟨?_, hwe.2, ?_, ?_, ?_⟩
  · rw [← hpay]; exact hwe.1
  · rw [hlenInput]; omega
  · exact (hwf freshReg hrel.safety.writer_below.2.2.2.1 hfr).trans hfresh
  · have hbitsFinal := bitsFrom_writeReg hbitsW remainingReg 0 (by
      have := hrel.start_at_input
      have := hrel.safety.writer_below.2.2.2.2
      omega)
    rw [hlenInput]
    simpa [splitTailEmitTerminalOneWriterProg, eval_seq, eval_assign, Expr.eval, Nat.add_assoc]
      using hbitsFinal

lemma splitTailEmitRel_one_to_done
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ,
      τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ ∧
      SplitTailEmitDone τ M curJ start base carry [l] pref tail addr cursorReg remainingReg
        freshReg := by
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp, hv, hcur, hall⟩ :=
    splitTailEmitRel_one_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l pref tail addr σ hbound hrel
  obtain ⟨f1, f2, f3, f4⟩ :=
    splitTailEmitRel_one_to_done_writer_apart hrel.safety (r := freshReg)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hfresh : υp freshReg = base := (hall _ f1 f2 f3 f4).trans hrel.fresh
  have htail := splitTailEmitRel_one_to_done_tail_transport M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l pref tail addr σ υp hrel hall
  refine ⟨_, rfl, ?_⟩
  rw [hτ]
  exact splitTailEmitRel_one_to_done_emit M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    base carry l pref tail addr σ υp hrel hυstate hcpol hcval hp hv hcur hfresh htail

/-- Capacity of the split-tail payload yields the room the two-literal terminal writer needs. -/
lemma splitTailEmitRel_two_to_done_room
    (base start M curJ : ℕ) (carry l1 l2 : Literal) (pref : Bits)
    (hc : start + pref.length + (splitTailPayload base carry [l1, l2]).length + 2 < M + curJ) :
    start + pref.length + carry.var + l1.var + l2.var + 8 < M + curJ := by
  have hlen : carry.var + l1.var + l2.var + 6 ≤
      (splitTailPayload base carry [l1, l2]).length := by
    cases carry <;> cases l1 <;> cases l2 <;>
      simp [splitTailPayload, encodeThreeClause, encodeLiteral,
        encodeNat_length, Literal.var]
    <;> omega
  omega

/-- When `literalPolarity carry = 1` (`hpol`), the three-literal bits written
    by the terminal writer are the split-tail payload. -/
lemma splitTailEmitRel_two_to_done_payload
    (base : ℕ) (carry l1 l2 : Literal) (hpol : literalPolarity carry = 1) :
    encodedThreeLiteralBits 1 carry.var (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var = splitTailPayload base carry [l1, l2] := by
  cases carry with
  | pos v => simp [literalPolarity] at hpol
  | neg v =>
    cases l1 <;> cases l2 <;>
      simp [splitTailPayload, encodedThreeLiteralBits, encodedLiteralBits,
        encodeThreeClause, encodeLiteral, Literal.var, literalPolarity, natBit]

/-- Length of the input consumed by a two-literal split-tail. -/
lemma splitTailEmitRel_two_to_done_input_length (l1 l2 : Literal) :
    (splitTailInputBits [l1, l2] []).length = l1.var + 2 + l2.var + 2 := by
  cases l1 <;> cases l2 <;>
    simp [splitTailInputBits, encodeLiteral, encodeNat_length, Literal.var]
    <;> omega

/-- Skipping two encoded literals leaves the tail readable at the shifted address. -/
lemma splitTailEmitRel_two_to_done_tail_bits
    (σ : Store) (addr : ℕ) (l1 l2 : Literal) (tail : Bits)
    (hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++ tail)) :
    BitsFrom σ (addr + l1.var + 2 + l2.var + 2) tail := by
  have hbits' : BitsFrom σ addr (encodeLiteral l1 ++ (encodeLiteral l2 ++ tail)) := by
    simpa [List.append_assoc] using hbits
  obtain ⟨_, hrest⟩ := bitsFrom_append σ addr (encodeLiteral l1) (encodeLiteral l2 ++ tail) hbits'
  have hlen1 : (encodeLiteral l1).length = l1.var + 2 := by
    cases l1 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  have hlen2 : (encodeLiteral l2).length = l2.var + 2 := by
    cases l2 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  rw [hlen1] at hrest
  obtain ⟨_, ht⟩ := bitsFrom_append σ (addr + l1.var + 2) (encodeLiteral l2) tail hrest
  rw [hlen2] at ht
  exact ht

/-- Writer registers are disjoint from every parser register used by the two-literal decode. -/
lemma splitTailEmitRel_two_to_done_writer_apart
    {start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hsafe : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg ∨ r = remainingReg) :
    r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧ r ≠ var3Reg ∧ r ≠ doneReg := by
  obtain ⟨hc, _, _, hd, hp2, hv2, hp3, hv3⟩ := hsafe.writer_parser r hr
  exact ⟨hc, hp2, hv2, hp3, hv3, hd⟩

/-- The two decode steps of the terminal program leave a writer state with the decoded
literal values in the parser registers and everything else unchanged. -/
lemma splitTailEmitRel_two_to_done_parsed
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ υp,
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ =
        (splitTailEmitTerminalTwoWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
          pol2Reg var2Reg pol3Reg var3Reg).eval υp ∧
      WriterState υp M curJ start pref ∧
      υp carryPolReg = 1 ∧ υp carryValReg = carry.var ∧
      υp pol2Reg = literalPolarity l1 ∧ υp var2Reg = l1.var ∧
      υp pol3Reg = literalPolarity l2 ∧ υp var3Reg = l2.var ∧
      υp cursorReg = addr + l1.var + 2 + l2.var + 2 ∧
      (∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ pol3Reg → r ≠ var3Reg →
        r ≠ doneReg → υp r = σ r) := by
  have hstart := hrel.start_at_input
  have hs2 := hrel.safety.second
  have hs3 := hrel.safety.third
  have hcross := hrel.safety.cross
  obtain ⟨hb2c, hb2p, hb2v, hb2d⟩ := hs2.below
  obtain ⟨hb3c, hb3p, hb3v, hb3d⟩ := hs3.below
  obtain ⟨hcp1, hcv1, hcd, hpv1, hpd1, hvd1⟩ := hs2.distinct
  obtain ⟨hcp2, hcv2, -, hpv2, hpd2, hvd2⟩ := hs3.distinct
  have hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++ tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  obtain ⟨τp, υp, hτp, hυp, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg bound
      addr l1 l2 tail σ hcp1 hcv1 hcd hpv1 hpd1 hvd1 hcp2 hcv2 hpv2 hpd2 hvd2
      (by omega) hbound1 hbound2 hrel.cursor hbits
  have hτstate : WriterState τp M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ τp cursorReg pol2Reg var2Reg doneReg
      hrel.writer hframe1 hs2.nonzero.1 hs2.nonzero.2.1 hs2.nonzero.2.2.1 hs2.nonzero.2.2.2
      hb2c hb2p hb2v hb2d
  have hυstate : WriterState υp M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref τp υp cursorReg pol3Reg var3Reg doneReg
      hτstate hframe2 hs3.nonzero.1 hs3.nonzero.2.1 hs3.nonzero.2.2.1 hs3.nonzero.2.2.2
      hb3c hb3p hb3v hb3d
  have hall : ∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ pol3Reg → r ≠ var3Reg →
      r ≠ doneReg → υp r = σ r := fun r h1 h2 h3 h4 h5 h6 =>
    (hframe2 r h1 h4 h5 h6).trans (hframe1 r h1 h2 h3 h6)
  have hpol1υ : υp pol2Reg = literalPolarity l1 :=
    (hframe2 pol2Reg hcp1.symm hcross.1 hcross.2.1 hpd1).trans hpol1
  have hvar1υ : υp var2Reg = l1.var :=
    (hframe2 var2Reg hcv1.symm hcross.2.2.1 hcross.2.2.2 hvd1).trans hvar1
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ :=
    splitTailEmitRel_two_to_done_writer_apart hrel.safety (Or.inl rfl)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    splitTailEmitRel_two_to_done_writer_apart hrel.safety (Or.inr (Or.inl rfl))
  refine ⟨υp, ?_, hυstate, (hall _ a1 a2 a3 a4 a5 a6).trans hrel.carry_pol,
    (hall _ c1 c2 c3 c4 c5 c6).trans hrel.carry_val, hpol1υ, hvar1υ, hpol2, hvar2, hcur2, hall⟩
  rw [hυp, hτp]
  simp [splitTailEmitTerminalTwoProg, splitTailEmitTerminalTwoWriterProg, eval_seq]

/-- The tail input stays readable after the parser registers change. -/
lemma splitTailEmitRel_two_to_done_tail_transport
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ υp : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hall : ∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ pol3Reg → r ≠ var3Reg →
      r ≠ doneReg → υp r = σ r) :
    BitsFrom υp (addr + l1.var + 2 + l2.var + 2) tail := by
  have hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++ tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  have htail := splitTailEmitRel_two_to_done_tail_bits σ addr l1 l2 tail hbits
  have hstart := hrel.start_at_input
  obtain ⟨hb2c, hb2p, hb2v, hb2d⟩ := hrel.safety.second.below
  obtain ⟨hb3c, hb3p, hb3v, hb3d⟩ := hrel.safety.third.below
  intro i hi
  rw [hall _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact htail i hi

/-- The terminal writer step turns a parsed state into the finished split-tail endpoint. -/
lemma splitTailEmitRel_two_to_done_emit
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ υp : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hυstate : WriterState υp M curJ start pref)
    (hcarryPol : υp carryPolReg = 1) (hcarryVal : υp carryValReg = carry.var)
    (hpol1 : υp pol2Reg = literalPolarity l1) (hvar1 : υp var2Reg = l1.var)
    (hpol2 : υp pol3Reg = literalPolarity l2) (hvar2 : υp var3Reg = l2.var)
    (hcur : υp cursorReg = addr + l1.var + 2 + l2.var + 2)
    (hfresh : υp freshReg = base)
    (htail : BitsFrom υp (addr + l1.var + 2 + l2.var + 2) tail) :
    SplitTailEmitDone
      ((splitTailEmitTerminalTwoWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
        pol2Reg var2Reg pol3Reg var3Reg).eval υp)
      M curJ start base carry [l1, l2] pref tail addr cursorReg remainingReg freshReg := by
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hl1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hl2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hlowRem := hrel.safety.writer_below.2.2.2.2
  have hrc : cursorReg ≠ remainingReg :=
    (hrel.safety.writer_parser remainingReg (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1.symm
  have hfr : freshReg ≠ remainingReg := hrel.safety.writer_distinct.2.2.2.2.2.2.2.2.2
  have hwe := splitTailEmitTerminalTwoWriterProg_eval M curJ tmpJ start pref
    remainingReg carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2 (Or.inr rfl) hl1 hl2
    hrel.safety.writer_below.2.1 hrel.safety.second.below.2.1
    hrel.safety.second.below.2.2.1 hrel.safety.third.below.2.1 hrel.safety.third.below.2.2.1
    hlowRem hrel.safety.remaining_nonzero hυstate (by omega)
  have hwf := fun r (hr : r < start) (hne : r ≠ remainingReg) =>
    splitTailEmitTerminalTwoWriterProg_frame M curJ tmpJ start pref
      remainingReg carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
      1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
      hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2 (Or.inr rfl) hl1 hl2
      hrel.safety.writer_below.2.1 hrel.safety.second.below.2.1
      hrel.safety.second.below.2.2.1 hrel.safety.third.below.2.1 hrel.safety.third.below.2.2.1
      hυstate (by omega) hr hne
  have hbitsW := writerAppendThreeRegsProg_bitsFrom_frame M curJ tmpJ start pref tail
    (addr + l1.var + 2 + l2.var + 2) carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2 (Or.inr rfl) hl1 hl2
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1⟩
    hυstate (by omega) (by have := hrel.input_above; omega) htail
  have hlenInput := splitTailEmitRel_two_to_done_input_length l1 l2
  have hpay := splitTailEmitRel_two_to_done_payload base carry l1 l2 hrel.carry_one
  have hcurFinal := (hwf cursorReg hrel.safety.main.below.1 hrc).trans hcur
  refine ⟨?_, hwe.2, ?_, ?_, ?_⟩
  · rw [← hpay]; exact hwe.1
  · rw [hlenInput]; omega
  · exact (hwf freshReg hrel.safety.writer_below.2.2.2.1 hfr).trans hfresh
  · have hbitsFinal := bitsFrom_writeReg hbitsW remainingReg 0 (by
      have := hrel.start_at_input
      omega)
    rw [hlenInput]
    simpa [splitTailEmitTerminalTwoWriterProg, eval_seq, eval_assign, Expr.eval, Nat.add_assoc]
      using hbitsFinal

lemma splitTailEmitRel_two_to_done
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ,
      τ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ ∧
      SplitTailEmitDone τ M curJ start base carry [l1, l2] pref tail addr cursorReg remainingReg
        freshReg := by
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp1, hv1, hp2, hv2, hcur, hall⟩ :=
    splitTailEmitRel_two_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ :=
    splitTailEmitRel_two_to_done_writer_apart hrel.safety (r := freshReg)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hfresh : υp freshReg = base := (hall _ f1 f2 f3 f4 f5 f6).trans hrel.fresh
  have htail := splitTailEmitRel_two_to_done_tail_transport M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l1 l2 pref tail addr σ υp hrel hall
  refine ⟨_, rfl, ?_⟩
  rw [hτ]
  exact splitTailEmitRel_two_to_done_emit M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    base carry l1 l2 pref tail addr σ υp hrel hυstate hcpol hcval hp1 hv1 hp2 hv2 hcur hfresh htail


end NPComplete.CookLevin

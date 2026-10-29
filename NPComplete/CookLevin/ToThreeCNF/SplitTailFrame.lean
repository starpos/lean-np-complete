module

public import NPComplete.CookLevin.ToThreeCNF.SplitTailDone

/-!
# Terminal split-tail framing

The final clause append must preserve surrounding input and register state before
the outer CNF loop resumes. This module derives low- and high-memory frame
properties for the one- and two-literal terminal branches from their evaluation
contracts.
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
/-! Terminal endpoints are transported to the frame-carrying relation used
by the enclosing emitter.  The high-region and polarity premises are discharged
by the parser and writer frame lemmas. -/

lemma splitTailEmitRel_one_to_done_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ,
      τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base carry [l] pref tail addr
        cursorReg remainingReg freshReg posPolReg := by
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_one_to_done
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l pref tail addr σ
    hbound hrel
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
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧ doneReg < start :=
    hrel.safety.second.below
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0 :=
    hrel.safety.second.nonzero
  obtain ⟨_, hpol2, hvar2, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  let τp := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg pol2Reg var2Reg doneReg hrel.writer
      (by simpa [τp] using hdecFrame)
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2
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
  have hposParser : τp posPolReg = σ posPolReg := by
    have hp := hrel.safety.writer_parser posPolReg
      (Or.inr (Or.inr (Or.inl rfl)))
    have hf := hdecFrame posPolReg hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.1
    simpa [τp] using hf
  have hneq : posPolReg ≠ remainingReg := by
    rcases hrel.safety.writer_distinct with ⟨_, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hw := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var τp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPolτ hcarryValτ hpol2' hvar2' hpol2' hvar2'
    (Or.inr rfl) hpolCase hpolCase
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    hτstate (by omega) hrel.safety.writer_below.2.2.1
  have hpos : τ posPolReg = 0 := by
    have hτeq : τ =
        (splitTailEmitTerminalOneWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
          pol2Reg var2Reg).eval τp := by
      simp [hτ, τp, splitTailEmitTerminalOneProg, splitTailEmitTerminalOneWriterProg]
    rw [hτeq, splitTailEmitTerminalOneWriterProg, eval_seq, eval_assign, Expr.eval]
    have hw' :
        (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
          pol2Reg var2Reg).eval τp posPolReg = 0 :=
      hw.trans (hposParser.trans hrel.pos)
    exact (writeReg_diff _ remainingReg 0 posPolReg hneq).trans hw'
  have hhigh := splitTailEmitTerminalOneProg_high_frame_of_rel
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l pref tail addr σ
    hbound hrel
  refine ⟨τ, hτ, ⟨hdone, ?_, hpos⟩⟩
  simpa [hτ] using hhigh

/-! The parser/writer cells are the complete write set of the singleton
    terminal.  This low-frame lemma is used by the outer clause emitter for
    control cells which live below the writer workspace. -/

lemma splitTailEmitTerminalOneProg_low_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ doneReg ∧
      r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ remainingReg) :
    (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  rcases hrsafe with ⟨hrc, hrp, hrv, hrd, hrcp, hrcv, hrr⟩
  have hroom : start + pref.length + carry.var + 2 * l.var + 8 < M + curJ := by
    have hc := hrel.capacity
    have hlen : carry.var + 2 * l.var + 6 ≤
        (splitTailPayload base carry [l]).length := by
      cases carry <;> cases l <;>
        simp [splitTailPayload, encodeThreeClause, encodeLiteral,
          encodeNat_length, Literal.var] <;> omega
    omega
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧ doneReg < start :=
    ⟨hrel.safety.second.below.1, hrel.safety.second.below.2.1,
      hrel.safety.second.below.2.2.1, hrel.safety.second.below.2.2.2⟩
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0 :=
    hrel.safety.second.nonzero
  obtain ⟨_, hpol, hvar, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  let τp := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg pol2Reg var2Reg doneReg hrel.writer
      (by simpa [τp] using hdecFrame)
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2
  have hcarryPolτ : τp carryPolReg = 1 := by
    have hf := hdecFrame carryPolReg
      (by exact hrel.safety.writer_parser carryPolReg (Or.inl rfl) |>.1)
      (by exact (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.1)
      (by exact (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.2.1)
      (by exact (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.1)
    simpa [τp] using hf.trans hrel.carry_pol
  have hcarryValτ : τp carryValReg = carry.var := by
    have hf := hdecFrame carryValReg
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.1
    simpa [τp] using hf.trans hrel.carry_val
  have hpol' : τp pol2Reg = literalPolarity l := by
    cases l <;> simpa [τp, literalPolarity] using hpol
  have hvar' : τp var2Reg = l.var := by simpa [τp] using hvar
  have hpol01 : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hw := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var τp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPolτ hcarryValτ hpol' hvar' hpol' hvar'
    (Or.inr rfl) hpol01 hpol01
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    hτstate (by omega) hr
  rw [splitTailEmitTerminalOneProg, eval_seq, eval_seq, eval_assign, Expr.eval]
  rw [writeReg_diff _ remainingReg _ r hrr]
  exact hw.trans (hdecFrame r hrc hrp hrv hrd)

lemma splitTailEmitTerminalOneProg_after_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (pref tail : Bits) (addr : ℕ)
    (σ : Store) (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : start + pref.length + carry.var + 2 * l.var + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
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
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧ doneReg < start :=
    hrel.safety.second.below
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0 :=
    hrel.safety.second.nonzero
  obtain ⟨_, hpol, hvar, _, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  let τp := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg pol2Reg var2Reg doneReg hrel.writer
      (by simpa [τp] using hdecFrame)
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2
  have hcarryPolτ : τp carryPolReg = 1 := by
    have hf := hdecFrame carryPolReg
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.2.1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.1
    simpa [τp] using hf.trans hrel.carry_pol
  have hcarryValτ : τp carryValReg = carry.var := by
    have hf := hdecFrame carryValReg
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.1
    simpa [τp] using hf.trans hrel.carry_val
  have hpol' : τp pol2Reg = literalPolarity l := by
    cases l <;> simpa [τp, literalPolarity] using hpol
  have hvar' : τp var2Reg = l.var := by simpa [τp] using hvar
  have hpol01 : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hrwriter := hr
  have hw := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var τp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPolτ hcarryValτ hpol' hvar' hpol' hvar'
    (Or.inr rfl) hpol01
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    hτstate (by omega) (by omega) hrc hrt
  rw [splitTailEmitTerminalOneProg, eval_seq, eval_seq, eval_assign, Expr.eval]
  have hrembelow := hrel.safety.writer_below.2.2.2.2
  have hrrem : r ≠ remainingReg := by omega
  rw [writeReg_diff _ remainingReg _ r hrrem]
  have hrcur : r ≠ cursorReg := by omega
  have hrpol : r ≠ pol2Reg := by omega
  have hrvar : r ≠ var2Reg := by omega
  have hrdone : r ≠ doneReg := by omega
  exact hw.trans (hdecFrame r hrcur hrpol hrvar hrdone)

/-! The two-literal terminal frame is derivable from the parser and writer
    frames.  Keeping this derivation here avoids making callers provide a
    frame premise for a program whose touched registers are already described
    by `SplitTailRegisterSafety`. -/

/-- The two-literal terminal writer leaves every low register except the remaining counter unchanged. -/
lemma splitTailEmitRel_two_to_done_frame_writer_low
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
    {r : ℕ} (hr : r < start) (hrr : r ≠ remainingReg) :
    (splitTailEmitTerminalTwoWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
      pol2Reg var2Reg pol3Reg var3Reg).eval υp r = υp r := by
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hl1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hl2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hw := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2
    (Or.inr rfl) hl1 hl2
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1⟩
    hυstate (by omega) hr
  rw [splitTailEmitTerminalTwoWriterProg, eval_seq, eval_assign, Expr.eval]
  exact (writeReg_diff _ remainingReg 0 r hrr).trans hw

lemma splitTailEmitTerminalTwoProg_low_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
      r ≠ var3Reg ∧ r ≠ doneReg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧
      r ≠ remainingReg) :
    (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp1, hv1, hp2, hv2, -, hall⟩ :=
    splitTailEmitRel_two_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  rw [hτ, splitTailEmitRel_two_to_done_frame_writer_low M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l1 l2 pref tail addr σ υp hrel hυstate hcpol hcval hp1 hv1
    hp2 hv2 hr hrsafe.2.2.2.2.2.2.2.2]
  exact hall r hrsafe.1 hrsafe.2.1 hrsafe.2.2.1 hrsafe.2.2.2.1 hrsafe.2.2.2.2.1
    hrsafe.2.2.2.2.2.1

/-- The two-literal terminal writer leaves the high input region unchanged. -/
lemma splitTailEmitRel_two_to_done_frame_writer_high
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
    {r : ℕ} (hr : M + tmpJ < r) (hrr : r ≠ remainingReg) :
    (splitTailEmitTerminalTwoWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
      pol2Reg var2Reg pol3Reg var3Reg).eval υp r = υp r := by
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hl1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hl2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hw := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2
    (Or.inr rfl) hl1 hl2
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1⟩
    hυstate (by omega) hr
  rw [splitTailEmitTerminalTwoWriterProg, eval_seq, eval_assign, Expr.eval]
  exact (writeReg_diff _ remainingReg 0 r hrr).trans hw

/-- The two-literal terminal program leaves the high input region unchanged. -/
lemma splitTailEmitRel_two_to_done_frame_high
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∀ r, M + tmpJ < r →
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval
        σ r = σ r := by
  intro r hr
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp1, hv1, hp2, hv2, -, hall⟩ :=
    splitTailEmitRel_two_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hcurJ := hrel.cur_j_pos
  have htmpJ := hrel.tmp_j_pos
  have hremBelow := hrel.safety.writer_below.2.2.2.2
  obtain ⟨b1, b2, b3, b4⟩ := hrel.safety.second.below
  obtain ⟨b5, b6, b7, b8⟩ := hrel.safety.third.below
  have hrr : r ≠ remainingReg := by omega
  rw [hτ, splitTailEmitRel_two_to_done_frame_writer_high M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l1 l2 pref tail addr σ υp hrel hυstate hcpol hcval hp1 hv1
    hp2 hv2 hr hrr]
  exact hall r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The two-literal terminal program leaves the positive-polarity register at zero. -/
lemma splitTailEmitRel_two_to_done_frame_pos
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval
      σ posPolReg = 0 := by
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp1, hv1, hp2, hv2, -, hall⟩ :=
    splitTailEmitRel_two_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ :=
    splitTailEmitRel_two_to_done_writer_apart hrel.safety (r := posPolReg)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hneq : posPolReg ≠ remainingReg := hrel.safety.writer_distinct.2.2.2.2.2.2.2.2.1
  rw [hτ, splitTailEmitRel_two_to_done_frame_writer_low M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l1 l2 pref tail addr σ υp hrel hυstate hcpol hcval hp1 hv1
    hp2 hv2 hrel.safety.writer_below.2.2.1 hneq]
  exact (hall _ a1 a2 a3 a4 a5 a6).trans hrel.pos

lemma splitTailEmitRel_two_to_done_frame
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
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base carry [l1, l2] pref tail addr
        cursorReg remainingReg freshReg posPolReg := by
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_two_to_done
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2
    pref tail addr σ hbound1 hbound2 hrel
  have hhigh := splitTailEmitRel_two_to_done_frame_high M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  have hpos := splitTailEmitRel_two_to_done_frame_pos M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  exact ⟨τ, hτ, ⟨hdone, by simpa [hτ] using hhigh, by simpa [hτ] using hpos⟩⟩

/-- The two-literal terminal writer leaves every register above the output
    region unchanged except `M + curJ`, `M + tmpJ`, and `remainingReg`. -/
lemma splitTailEmitTerminalTwoWriterProg_after_frame_writer
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
    {r : ℕ} (hr : start + pref.length + carry.var + l1.var + l2.var + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) (hrr : r ≠ remainingReg) :
    (splitTailEmitTerminalTwoWriterProg curJ tmpJ remainingReg carryPolReg carryValReg
      pol2Reg var2Reg pol3Reg var3Reg).eval υp r = υp r := by
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hl1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hw := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcarryPol hcarryVal hpol1 hvar1 hpol2 hvar2
    (Or.inr rfl) hl1
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1⟩
    hυstate (by omega) hr hrc hrt
  rw [splitTailEmitTerminalTwoWriterProg, eval_seq, eval_assign, Expr.eval]
  exact (writeReg_diff _ remainingReg 0 r hrr).trans hw

lemma splitTailEmitTerminalTwoProg_after_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : start + pref.length + carry.var + l1.var + l2.var + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  obtain ⟨υp, hτ, hυstate, hcpol, hcval, hp1, hv1, hp2, hv2, -, hall⟩ :=
    splitTailEmitRel_two_to_done_parsed M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
  have hroom := splitTailEmitRel_two_to_done_room base start M curJ carry l1 l2 pref hrel.capacity
  have hremBelow := hrel.safety.writer_below.2.2.2.2
  obtain ⟨b1, b2, b3, b4⟩ := hrel.safety.second.below
  obtain ⟨b5, b6, b7, b8⟩ := hrel.safety.third.below
  have hrr : r ≠ remainingReg := by omega
  rw [hτ, splitTailEmitTerminalTwoWriterProg_after_frame_writer M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg base carry l1 l2 pref tail addr σ υp hrel hυstate hcpol hcval hp1 hv1
    hp2 hv2 hr hrc hrt hrr]
  exact hall r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ToThreeCNF.LongClause

/-!
# Clause-emission program

Short clauses follow a direct writer path, while longer clauses need repeated
split-tail steps and a commit. This module assembles the dispatch, setup, and
reset programs so proofs can reason about one stable clause-program interface.
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
/-! A unified clause dispatcher.  The length prefix is decoded by
`emitClauseProgram`; this second program assumes that `lengthReg` already
contains the decoded length and selects the corresponding literal parser and
writer.  The outer counter update is intentionally part of every branch, so
the dispatcher is ready to be used as one iteration of the CNF loop. -/

def emitClauseCommitProg (outerReg : ℕ) : Program :=
  .assign outerReg (.sub (.reg outerReg) (.const 1))

def emitClauseEmptyFreshProg (freshReg : ℕ) : Program :=
  .assign freshReg (.add (.reg freshReg) (.const 1))

def emitClauseDispatchProg
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) : Program :=
  .ifNZ (.eq (.reg lengthReg) (.const 0))
    (.seq
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
      (.seq (emitClauseEmptyFreshProg freshReg)
        (emitClauseCommitProg outerReg)))
    (.ifNZ (.eq (.reg lengthReg) (.const 1))
      (.seq
        (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
        (.seq
          (writerAppendClauseOneProg curJ tmpJ polReg varReg)
          (emitClauseCommitProg outerReg)))
      (.ifNZ (.eq (.reg lengthReg) (.const 2))
        (.seq
          (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
          (.seq
            (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound)
            (.seq
              (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
              (emitClauseCommitProg outerReg))))
        (.ifNZ (.eq (.reg lengthReg) (.const 3))
          (.seq
            (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
            (.seq
              (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound)
              (.seq
                (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound)
                (.seq
                  (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
                    pol3Reg var3Reg posPolReg negPolReg freshReg)
                  (.seq (emitClauseEmptyFreshProg freshReg)
                    (emitClauseCommitProg outerReg))))))
          (.seq
            (.assign remainingReg (.reg lengthReg))
            (.seq
              (.assign carryPolReg (.const 1))
              (.seq
                (.assign carryValReg (.reg freshReg))
                (.seq
                  (.assign posPolReg (.const 0))
                  (.seq
                    (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
                      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                      posPolReg freshReg bound tailBound)
                    (emitClauseCommitProg outerReg)))))))))

def emitClauseProgram
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) : Program :=
  .seq (decodeNatProgram cursorReg lengthReg doneReg bound)
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound)

/-! The clause dispatcher leaves the parser scratch cells in their terminal
state.  The outer CNF loop starts the next clause with fresh parser scratch,
so the boundary wrapper clears exactly the two parser controls after the
clause has been emitted. -/

def emitClauseResetProg (lengthReg doneReg : ℕ) : Program :=
  .seq (.assign lengthReg (.const 0)) (.assign doneReg (.const 0))

def emitClauseIterProgram
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) : Program :=
  .seq (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound)
    (emitClauseResetProg lengthReg doneReg)

lemma emitClauseResetProg_eval (lengthReg doneReg : ℕ) (σ : Store) :
    (emitClauseResetProg lengthReg doneReg).eval σ =
      writeReg (writeReg σ lengthReg 0) doneReg 0 := by
  simp [emitClauseResetProg, eval_seq, eval_assign, Expr.eval]

lemma emitClauseResetProg_frame
    (lengthReg doneReg : ℕ) (σ : Store)
    {r : ℕ}
    (hrl : r ≠ lengthReg) (hrd : r ≠ doneReg) :
    (emitClauseResetProg lengthReg doneReg).eval σ r = σ r := by
  rw [emitClauseResetProg_eval]
  rw [writeReg_diff _ doneReg 0 r hrd, writeReg_diff σ lengthReg 0 r hrl]

lemma emitClauseResetProg_writer
    (M curJ start lengthReg doneReg : ℕ) (pref : Bits) (σ : Store)
    (hs : WriterState σ M curJ start pref)
    (hlowLength : lengthReg < start) (hlowDone : doneReg < start)
    (hlength0 : lengthReg ≠ 0) (hdone0 : doneReg ≠ 0)
    (hne : lengthReg ≠ doneReg) :
    WriterState ((emitClauseResetProg lengthReg doneReg).eval σ) M curJ start pref := by
  rw [emitClauseResetProg_eval]
  have hs1 := writerState_assign_value M curJ start pref lengthReg 0 σ hs
    hlowLength hlength0
  have hs2 := writerState_assign_value M curJ start pref doneReg 0
    (writeReg σ lengthReg 0) hs1 hlowDone hdone0
  have hne' : doneReg ≠ lengthReg := Ne.symm hne
  simpa [writeReg_diff _ lengthReg 0 doneReg hne'] using hs2

lemma splitTailEmitLongClauseSetup_frame_after
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ)
    (base : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref)
    (hpos : σ posPolReg = 0) (hfresh : σ freshReg = base)
    (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : start + pref.length + l1.var + l2.var + base + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r =
      σ r := by
  have hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++
      splitTailInputBits (l3 :: l4 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hinput
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start ∧ doneReg < start := by
    exact ⟨hsafety.second.below.1, hsafety.second.below.2.1,
      hsafety.second.below.2.2.1, hsafety.third.below.2.1,
      hsafety.third.below.2.2.1, hsafety.second.below.2.2.2⟩
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0 := by
    exact ⟨hsafety.second.nonzero.1, hsafety.second.nonzero.2.1,
      hsafety.second.nonzero.2.2.1, hsafety.third.nonzero.2.1,
      hsafety.third.nonzero.2.2.1, hsafety.second.nonzero.2.2.2⟩
  have hwd : ∀ x, x = posPolReg ∨ x = freshReg →
      x ≠ cursorReg ∧ x ≠ pol2Reg ∧ x ≠ var2Reg ∧ x ≠ pol3Reg ∧
        x ≠ var3Reg ∧ x ≠ doneReg := by
    intro x hx
    exact splitTailEmitLongClauseSetup_write_regs_avoid_parser hsafety (by
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨τp, υp, hτp, hυp, _, hpol1, hvar1, _, hpol2, hvar2,
      hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg bound addr
      l1 l2 (splitTailInputBits (l3 :: l4 :: rest) tail) σ
      hsafety.second.distinct.1 hsafety.second.distinct.2.1
      hsafety.second.distinct.2.2.1 hsafety.second.distinct.2.2.2.1
      hsafety.second.distinct.2.2.2.2.1 hsafety.second.distinct.2.2.2.2.2
      hsafety.third.distinct.1 hsafety.third.distinct.2.1
      hsafety.third.distinct.2.2.2.1 hsafety.third.distinct.2.2.2.2.1
      hsafety.third.distinct.2.2.2.2.2
      ⟨lt_of_lt_of_le hbelow.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.2.2 hstartAtInput⟩
      hbound1 hbound2 hcursor hbits
  have hτstate : WriterState τp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τp
      cursorReg pol2Reg var2Reg doneReg hwriter hframe1
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2.2.2
  have hυstate : WriterState υp M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref τp υp
      cursorReg pol3Reg var3Reg doneReg hτstate hframe2
      hnonzero.1 hnonzero.2.2.2.1 hnonzero.2.2.2.2.1 hnonzero.2.2.2.2.2
      hbelow.1 hbelow.2.2.2.1 hbelow.2.2.2.2.1 hbelow.2.2.2.2.2
  have hpol1' : υp pol2Reg = literalPolarity l1 := by
    have hf := hframe2 pol2Reg (Ne.symm hsafety.second.distinct.1)
      hsafety.cross.1 hsafety.cross.2.1 hsafety.second.distinct.2.2.2.2.1
    have ht : τp pol2Reg = literalPolarity l1 := by
      cases l1 <;> simpa [hτp, literalPolarity] using hpol1
    simpa [hυp] using hf.trans ht
  have hvar1' : υp var2Reg = l1.var := by
    have hf := hframe2 var2Reg (Ne.symm hsafety.second.distinct.2.1)
      hsafety.cross.2.2.1 hsafety.cross.2.2.2 hsafety.second.distinct.2.2.2.2.2
    simpa [hυp, hτp] using hf.trans hvar1
  have hpol2' : υp pol3Reg = literalPolarity l2 := by
    cases l2 <;> simpa [hυp, literalPolarity] using hpol2
  have hvar2' : υp var3Reg = l2.var := by simpa [hυp] using hvar2
  have hposwd := hwd posPolReg (Or.inl rfl)
  have hfreshwd := hwd freshReg (Or.inr rfl)
  have hposυ : υp posPolReg = 0 := by
    have h1 := hframe1 posPolReg hposwd.1 hposwd.2.1 hposwd.2.2.1 hposwd.2.2.2.2.2
    have h2 := hframe2 posPolReg hposwd.1 hposwd.2.2.2.1 hposwd.2.2.2.2.1
      hposwd.2.2.2.2.2
    simpa [hτp, hυp] using h2.trans (h1.trans hpos)
  have hfreshυ : υp freshReg = base := by
    have h1 := hframe1 freshReg hfreshwd.1 hfreshwd.2.1 hfreshwd.2.2.1 hfreshwd.2.2.2.2.2
    have h2 := hframe2 freshReg hfreshwd.1 hfreshwd.2.2.2.1 hfreshwd.2.2.2.2.1
      hfreshwd.2.2.2.2.2
    simpa [hτp, hυp] using h2.trans (h1.trans hfresh)
  have hpol01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpol02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hw := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υp
    hcurJ htmpJ hpol1' hvar1' hpol2' hvar2' hposυ hfreshυ hpol01 hpol02
    hsafety.second.below.2.2.1
    ⟨hsafety.third.below.2.1, hsafety.third.below.2.2.1⟩
    ⟨hsafety.writer_below.2.2.1, hsafety.writer_below.2.2.2.1⟩ hυstate (by omega) hr hrc hrt
  simp only [splitTailEmitLongClauseSetup, eval_seq, eval_assign,
    NPComplete.BoundedWhile.eval_skip, Expr.eval]
  have hrembelow := hsafety.writer_below.2.2.2.2
  have hcarryPolbelow := hsafety.writer_below.1
  have hcarryValbelow := hsafety.writer_below.2.1
  have hfreshbelow := hsafety.writer_below.2.2.2.1
  rw [writeReg_diff _ remainingReg _ r (by omega), writeReg_diff _ freshReg _ r (by omega),
    writeReg_diff _ carryValReg _ r (by omega), writeReg_diff _ carryPolReg _ r (by omega)]
  have hrcur : r ≠ cursorReg := by omega
  have hrpol2 : r ≠ pol2Reg := by omega
  have hrvar2 : r ≠ var2Reg := by omega
  have hrdone : r ≠ doneReg := by omega
  simpa [hτp, hυp] using
    (hw.trans (hframe2 r hrcur (by omega) (by omega) hrdone)).trans
      (hframe1 r hrcur hrpol2 hrvar2 hrdone)

lemma splitTailEmitLongClauseProg_eval_end_to_end_low_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound : ℕ)
    (base : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
      M + curJ)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref)
    (hpos : σ posPolReg = 0) (hfresh : σ freshReg = base)
    (hremaining : σ remainingReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : r < start)
    (hrnot : r ∉ splitTailEmitStepWriteSet cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ, τ = (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg bound tailBound).eval σ ∧ τ r = σ r := by
  let setup := splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  let σsetup := setup.eval σ
  obtain ⟨hpost, _hsetupHigh, _hsetupPos⟩ := splitTailEmitLongClauseSetup_eval
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base l1 l2 (l3 :: l4 :: rest) pref tail addr σ hbound1 hbound2 hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety
  have hsetupLow := splitTailEmitLongClauseSetup_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base l1 l2 (l3 :: l4 :: rest) pref tail addr σ hbound1 hbound2 hroom hcapacity
    hinput hcurJ htmpJ hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety hr
    (by
      obtain ⟨hc, hp, hv, hd, hrem, hp2, hv2, hp3, hv3, hcp, hcv, hpp, hf⟩ :=
        (by simpa [splitTailEmitStepWriteSet] using hrnot :
          ¬r = cursorReg ∧ ¬r = polReg ∧ ¬r = varReg ∧ ¬r = doneReg ∧
          ¬r = remainingReg ∧ ¬r = pol2Reg ∧ ¬r = var2Reg ∧ ¬r = pol3Reg ∧
          ¬r = var3Reg ∧ ¬r = carryPolReg ∧ ¬r = carryValReg ∧ ¬r = posPolReg ∧
          ¬r = freshReg)
      exact ⟨hc, hp2, hv2, hp3, hv3, hd, hcp, hcv, hpp, hf, hrem⟩)
  let τ := (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    tailBound).eval σsetup
  have hτr : τ r = σsetup r := splitTailEmitRel_nonempty_fixed_eval_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    tailBound (base + 1) (Literal.neg base) (l3 :: l4 :: rest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base) tail (addr + l1.var + 2 + l2.var + 2) σsetup
    hboundTail (by simp) hls hpost hr
    (by simpa [splitTailEmitStepWriteSet] using hrnot)
  refine ⟨τ, ?_, hτr.trans hsetupLow⟩
  rw [splitTailEmitLongClauseProg, eval_seq]

lemma emitClauseDispatchProg_zero_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 0) :
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound).eval σ =
      (Program.seq (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
        (Program.seq (emitClauseEmptyFreshProg freshReg)
          (emitClauseCommitProg outerReg))).eval σ := by
  simp [emitClauseDispatchProg, hlen, Expr.eval]

lemma emitClauseDispatchProg_one_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 1) :
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ =
      (Program.seq (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
        (Program.seq (writerAppendClauseOneProg curJ tmpJ polReg varReg)
          (emitClauseCommitProg outerReg))).eval σ := by
  simp [emitClauseDispatchProg, hlen, Expr.eval]

lemma emitClauseDispatchProg_two_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 2) :
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ =
      (Program.seq (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
        (Program.seq (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound)
          (Program.seq (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
            (emitClauseCommitProg outerReg)))).eval σ := by
  simp [emitClauseDispatchProg, hlen, Expr.eval]

lemma emitClauseDispatchProg_three_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 3) :
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ =
      (Program.seq (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
        (Program.seq (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound)
          (Program.seq (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound)
            (Program.seq (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
              pol3Reg var3Reg posPolReg negPolReg freshReg)
              (Program.seq (emitClauseEmptyFreshProg freshReg)
                (emitClauseCommitProg outerReg)))))).eval σ := by
  simp [emitClauseDispatchProg, hlen, Expr.eval]

lemma emitClauseDispatchProg_long_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ : Store)
    (hlen : 4 ≤ σ lengthReg) :
    (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
                  remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                  posPolReg freshReg bound tailBound)
                (emitClauseCommitProg outerReg)))))).eval σ := by
  have h0 : σ lengthReg ≠ 0 := by omega
  have h1 : σ lengthReg ≠ 1 := by omega
  have h2 : σ lengthReg ≠ 2 := by omega
  have h3 : σ lengthReg ≠ 3 := by omega
  simp [emitClauseDispatchProg, h0, h1, h2, h3, Expr.eval]

def clauseEmitRegs (cursorReg lengthReg polReg varReg doneReg outerReg freshReg
    posPolReg negPolReg : ℕ) : List ℕ :=
  [cursorReg, lengthReg, polReg, varReg, doneReg, outerReg, freshReg, posPolReg, negPolReg]

/- Register pairs are oriented pairs of distinct entries in a register list.
   This representation makes the non-collision premise explicit and does not
   assert the impossible inequality of a register with itself. -/
@[simp] def registerPairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
      xs.map (fun y => (x, y)) ++ xs.map (fun y => (y, x)) ++ registerPairs xs

lemma registerPairs_ne_of_nodup {xs : List ℕ} (hxs : xs.Nodup)
    {a b : ℕ} (hp : (a, b) ∈ registerPairs xs) : a ≠ b := by
  induction xs with
  | nil => simp [registerPairs] at hp
  | cons x xs ih =>
      have hparts := List.nodup_cons.mp hxs
      have hnot : x ∉ xs := hparts.1
      have htail : xs.Nodup := hparts.2
      simp [registerPairs] at hp
      aesop

def RegisterPairwise (xs : List ℕ) : Prop :=
  ∀ {a b : ℕ}, (a, b) ∈ registerPairs xs → a ≠ b

lemma registerPairwise_of_nodup {xs : List ℕ} (hxs : xs.Nodup) :
    RegisterPairwise xs := by
  intro a b hp
  exact registerPairs_ne_of_nodup hxs hp

@[simp] def clauseEmitPairs (cursorReg lengthReg polReg varReg doneReg outerReg freshReg
    posPolReg negPolReg : ℕ) : List (ℕ × ℕ) :=
  [(cursorReg, lengthReg), (lengthReg, cursorReg),
   (cursorReg, polReg), (polReg, cursorReg),
   (cursorReg, varReg), (varReg, cursorReg),
   (cursorReg, doneReg), (doneReg, cursorReg),
   (cursorReg, outerReg), (outerReg, cursorReg),
   (cursorReg, freshReg), (freshReg, cursorReg),
   (cursorReg, posPolReg), (posPolReg, cursorReg),
   (cursorReg, negPolReg), (negPolReg, cursorReg),
   (lengthReg, polReg), (polReg, lengthReg),
   (lengthReg, varReg), (varReg, lengthReg),
   (lengthReg, doneReg), (doneReg, lengthReg),
   (lengthReg, outerReg), (outerReg, lengthReg),
   (lengthReg, freshReg), (freshReg, lengthReg),
   (lengthReg, posPolReg), (posPolReg, lengthReg),
   (lengthReg, negPolReg), (negPolReg, lengthReg),
   (polReg, varReg), (varReg, polReg),
   (polReg, doneReg), (doneReg, polReg),
   (polReg, outerReg), (outerReg, polReg),
   (polReg, freshReg), (freshReg, polReg),
   (polReg, posPolReg), (posPolReg, polReg),
   (polReg, negPolReg), (negPolReg, polReg),
   (varReg, doneReg), (doneReg, varReg),
   (varReg, outerReg), (outerReg, varReg),
   (varReg, freshReg), (freshReg, varReg),
   (varReg, posPolReg), (posPolReg, varReg),
   (varReg, negPolReg), (negPolReg, varReg),
   (doneReg, outerReg), (outerReg, doneReg),
   (doneReg, freshReg), (freshReg, doneReg),
   (doneReg, posPolReg), (posPolReg, doneReg),
   (doneReg, negPolReg), (negPolReg, doneReg),
   (outerReg, freshReg), (freshReg, outerReg),
   (outerReg, posPolReg), (posPolReg, outerReg),
   (outerReg, negPolReg), (negPolReg, outerReg),
   (freshReg, posPolReg), (posPolReg, freshReg),
   (freshReg, negPolReg), (negPolReg, freshReg),
   (posPolReg, negPolReg), (negPolReg, posPolReg)]

structure ClauseEmitSafety
    (start cursorReg lengthReg polReg varReg doneReg outerReg freshReg posPolReg negPolReg : ℕ)
    : Prop where
  cursor_below : cursorReg < start
  length_below : lengthReg < start
  pol_below : polReg < start
  var_below : varReg < start
  done_below : doneReg < start
  outer_below : outerReg < start
  fresh_below : freshReg < start
  pos_below : posPolReg < start
  neg_below : negPolReg < start
  cursor_nonzero : cursorReg ≠ 0
  length_nonzero : lengthReg ≠ 0
  pol_nonzero : polReg ≠ 0
  var_nonzero : varReg ≠ 0
  done_nonzero : doneReg ≠ 0
  outer_nonzero : outerReg ≠ 0
  fresh_nonzero : freshReg ≠ 0
  pos_nonzero : posPolReg ≠ 0
  neg_nonzero : negPolReg ≠ 0
  register_nodup :
    (clauseEmitRegs cursorReg lengthReg polReg varReg doneReg outerReg freshReg
      posPolReg negPolReg).Nodup

lemma clause_emit_fixed_safety : ClauseEmitSafety 10 1 2 3 4 5 6 7 8 9 :=
  { cursor_below := by decide
    length_below := by decide
    pol_below := by decide
    var_below := by decide
    done_below := by decide
    outer_below := by decide
    fresh_below := by decide
    pos_below := by decide
    neg_below := by decide
    cursor_nonzero := by decide
    length_nonzero := by decide
    pol_nonzero := by decide
    var_nonzero := by decide
    done_nonzero := by decide
    outer_nonzero := by decide
    fresh_nonzero := by decide
    pos_nonzero := by decide
    neg_nonzero := by decide
    register_nodup := by decide }

lemma ClauseEmitSafety.core_distinct
    {start cursorReg lengthReg polReg varReg doneReg outerReg freshReg posPolReg negPolReg : ℕ}
    (hs : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg outerReg freshReg
      posPolReg negPolReg) :
    cursorReg ≠ lengthReg ∧ cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧
      cursorReg ≠ doneReg ∧ cursorReg ≠ outerReg ∧ cursorReg ≠ freshReg ∧
      cursorReg ≠ posPolReg ∧ cursorReg ≠ negPolReg ∧
      lengthReg ≠ polReg ∧ lengthReg ≠ varReg ∧ lengthReg ≠ doneReg ∧
      lengthReg ≠ outerReg ∧ lengthReg ≠ freshReg ∧ lengthReg ≠ posPolReg ∧
      lengthReg ≠ negPolReg ∧ polReg ≠ varReg ∧ polReg ≠ doneReg ∧
      polReg ≠ outerReg ∧ polReg ≠ freshReg ∧ polReg ≠ posPolReg ∧
      polReg ≠ negPolReg ∧ varReg ≠ doneReg ∧ varReg ≠ outerReg ∧
      varReg ≠ freshReg ∧ varReg ≠ posPolReg ∧ varReg ≠ negPolReg ∧
      doneReg ≠ outerReg ∧ doneReg ≠ freshReg ∧ doneReg ≠ posPolReg ∧
      doneReg ≠ negPolReg ∧ outerReg ≠ freshReg ∧ outerReg ≠ posPolReg ∧
      outerReg ≠ negPolReg ∧ freshReg ≠ posPolReg ∧ freshReg ≠ negPolReg ∧
      posPolReg ≠ negPolReg := by
  have h := hs.register_nodup
  simp [clauseEmitRegs, List.nodup_cons] at h
  aesop

lemma ClauseEmitSafety.ne_of_pair
    {start cursorReg lengthReg polReg varReg doneReg outerReg freshReg posPolReg negPolReg a b : ℕ}
    (hs : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg outerReg freshReg
      posPolReg negPolReg)
    (hp : (a, b) ∈ clauseEmitPairs cursorReg lengthReg polReg varReg doneReg outerReg freshReg
      posPolReg negPolReg) :
    a ≠ b := by
  have hd := hs.core_distinct
  simp [clauseEmitPairs] at hp
  aesop

/-- The state obtained after the length prefix of one clause has been decoded.

This bundle separates the common length-decode transport from the five clause
branches.  In particular, the literal cursor is already past the unary length
prefix, while the writer and all control-register facts are transported from
the pre-state unchanged. -/
structure EmitClausePrepState
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg outerReg freshReg
      posPolReg negPolReg bound : ℕ)
    (base outer addr : ℕ) (c : List Literal) (rest pref : Bits)
    (σ σ0 : Store) : Prop where
  decoded : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ
  cursor : σ0 cursorReg = addr + c.length + 1
  length : σ0 lengthReg = c.length
  done : σ0 doneReg = 1
  input : BitsFrom σ0 (addr + c.length + 1)
    ((c.map encodeLiteral).flatten ++ rest)
  writer : WriterState σ0 M curJ start pref
  outer_value : σ0 outerReg = outer
  fresh_value : σ0 freshReg = base
  pos_value : σ0 posPolReg = 0
  neg_value : σ0 negPolReg = 1
  frame : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg → σ0 r = σ r
  input_above : M + tmpJ < addr + c.length + 1
  start_at_input : start ≤ addr + c.length + 1
  room : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c).1).length + 2 < M + curJ
  safety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg freshReg posPolReg negPolReg
  cur_j_pos : 1 ≤ curJ
  tmp_j_pos : curJ < tmpJ
  bound : c.length + 1 ≤ bound
  start_at_base : start ≤ addr
  initial_input : BitsFrom σ addr (encodeList encodeLiteral c ++ rest)
  initial_cursor : σ cursorReg = addr
  initial_length : σ lengthReg = 0
  initial_done : σ doneReg = 0
  initial_outer : σ outerReg = outer
  initial_fresh : σ freshReg = base
  initial_pos : σ posPolReg = 0
  initial_neg : σ negPolReg = 1
  initial_input_above : M + tmpJ < addr
  initial_writer : WriterState σ M curJ start pref

lemma emitClausePrepState_of_pre_eq
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg outerReg freshReg
      posPolReg negPolReg bound : ℕ)
    (base outer addr : ℕ) (c : List Literal) (rest pref : Bits) (σ σ0 : Store)
    (hσ0 : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound : c.length + 1 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral c ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base) (hpos : σ posPolReg = 0)
    (hneg : σ negPolReg = 1) (hinputAbove : M + tmpJ < addr)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c).1).length + 2 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base outer addr c rest pref σ σ0 := by
  have hneq : ∀ {a b : ℕ},
      (a, b) ∈ clauseEmitPairs cursorReg lengthReg polReg varReg doneReg outerReg freshReg
        posPolReg negPolReg → True → a ≠ b := by
    intro a b hp _
    exact hsafety.ne_of_pair hp
  have hbits : BitsFrom σ
      addr (encodeNat c.length ++ ((c.map encodeLiteral).flatten ++ rest)) := by
    simpa [encodeList, List.append_assoc] using hinput
  obtain ⟨hcur0, hlen0, hdone0, hframe0⟩ :=
    decodeNatProgram_encodeList_length_append encodeLiteral cursorReg lengthReg doneReg bound
      addr 0 c rest σ
      (hneq (a := cursorReg) (b := lengthReg) (by simp) (by simp))
      (hneq (a := cursorReg) (b := doneReg) (by simp) (by simp))
      (hneq (a := lengthReg) (b := doneReg) (by simp) (by simp))
      hbound (lt_of_lt_of_le hsafety.cursor_below hstart)
      (lt_of_lt_of_le hsafety.length_below hstart)
      (lt_of_lt_of_le hsafety.done_below hstart)
      hcursor (by simpa using hlength) hdoneInit hinput
  have hframeσ0 : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg → σ0 r = σ r := by
    intro r hcr hlr hdr
    rw [hσ0]
    exact hframe0 r hcr hlr hdr
  have hwriter0 : WriterState σ0 M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ σ0
      cursorReg lengthReg doneReg polReg hs
      (by
        intro r hcr hlr hdr hpr
        exact hframeσ0 r hcr hlr hdr)
      hsafety.cursor_nonzero hsafety.length_nonzero hsafety.done_nonzero hsafety.pol_nonzero
      hsafety.cursor_below hsafety.length_below hsafety.done_below hsafety.pol_below
  have htail : BitsFrom σ0 (addr + c.length + 1)
      ((c.map encodeLiteral).flatten ++ rest) := by
    obtain ⟨_, htailσ⟩ := bitsFrom_append σ addr (encodeNat c.length)
      ((c.map encodeLiteral).flatten ++ rest) hbits
    intro i hi
    have hcursorAddr : cursorReg < addr :=
      lt_of_lt_of_le hsafety.cursor_below hstart
    have hlengthAddr : lengthReg < addr :=
      lt_of_lt_of_le hsafety.length_below hstart
    have hdoneAddr : doneReg < addr :=
      lt_of_lt_of_le hsafety.done_below hstart
    have hfr := hframeσ0 (addr + c.length + 1 + i)
      (by omega) (by omega) (by omega)
    calc
      σ0 (addr + c.length + 1 + i) = σ (addr + c.length + 1 + i) := hfr
      _ = if ((c.map encodeLiteral).flatten ++ rest)[i] then 1 else 0 := by
        have hi' : addr + c.length + 1 + i =
            addr + (encodeNat c.length).length + i := by
          simp [encodeNat_length]
          omega
        rw [hi']
        exact htailσ i hi
  refine {
    decoded := hσ0
    cursor := by rw [hσ0]; exact hcur0
    length := by rw [hσ0]; simpa using hlen0
    done := by rw [hσ0]; exact hdone0
    input := htail
    writer := hwriter0
    outer_value := ?_
    fresh_value := ?_
    pos_value := ?_
    neg_value := ?_
    frame := hframeσ0
    input_above := by omega
    start_at_input := by omega
    room := hroom
    safety := hsafety
    cur_j_pos := hcurJ
    tmp_j_pos := htmpJ
    bound := hbound
    start_at_base := hstart
    initial_input := hinput
    initial_cursor := hcursor
    initial_length := hlength
    initial_done := hdoneInit
    initial_outer := houter
    initial_fresh := hfresh
    initial_pos := hpos
    initial_neg := hneg
    initial_input_above := hinputAbove
    initial_writer := hs }
  · exact (hframeσ0 outerReg
      (hneq (a := outerReg) (b := cursorReg) (by simp) (by simp))
      (hneq (a := outerReg) (b := lengthReg) (by simp) (by simp))
      (hneq (a := outerReg) (b := doneReg) (by simp) (by simp))).trans houter
  · exact (hframeσ0 freshReg
      (hneq (a := freshReg) (b := cursorReg) (by simp) (by simp))
      (hneq (a := freshReg) (b := lengthReg) (by simp) (by simp))
      (hneq (a := freshReg) (b := doneReg) (by simp) (by simp))).trans hfresh
  · exact (hframeσ0 posPolReg
      (hneq (a := posPolReg) (b := cursorReg) (by simp) (by simp))
      (hneq (a := posPolReg) (b := lengthReg) (by simp) (by simp))
      (hneq (a := posPolReg) (b := doneReg) (by simp) (by simp))).trans hpos
  · exact (hframeσ0 negPolReg
      (hneq (a := negPolReg) (b := cursorReg) (by simp) (by simp))
      (hneq (a := negPolReg) (b := lengthReg) (by simp) (by simp))
      (hneq (a := negPolReg) (b := doneReg) (by simp) (by simp))).trans hneg
  

lemma emitClausePrepState_of_pre
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg outerReg freshReg
      posPolReg negPolReg bound : ℕ)
    (base outer addr : ℕ) (c : List Literal) (rest pref : Bits) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound : c.length + 1 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral c ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base) (hpos : σ posPolReg = 0)
    (hneg : σ negPolReg = 1) (hinputAbove : M + tmpJ < addr)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c).1).length + 2 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base outer addr c rest pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) := by
  exact emitClausePrepState_of_pre_eq M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr c rest pref σ
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) rfl hcurJ htmpJ hbound hstart
    hinput hcursor hlength hdoneInit houter hfresh hpos hneg hinputAbove hs hroom hsafety


end NPComplete.CookLevin

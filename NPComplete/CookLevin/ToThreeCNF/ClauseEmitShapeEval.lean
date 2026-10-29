module

public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitProg

/-!
# Clause-emitter evaluation by shape

The clause program branches on decoded length, so its behavior must be verified
for each short shape. This module establishes the decode and write effects needed
to show that execution emits the intended clause payload.
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
/-- Decoding the length prefix `0` of the empty clause leaves the cursor after it and preserves the
writer, the outer, fresh and polarity registers. -/
lemma emitClauseProgram_nil_eval_decode_length
    (M curJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (rest : Bits) (pref : Bits) (σ : Store)
    (hbound : 1 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base) (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hs : WriterState σ M curJ start pref)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ0, σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ ∧
      σ0 lengthReg = 0 ∧ σ0 cursorReg = addr + 1 ∧
      WriterState σ0 M curJ start pref ∧ σ0 outerReg = outer ∧ σ0 freshReg = base ∧
      σ0 posPolReg = 0 ∧ σ0 negPolReg = 1 := by
  have hbits : BitsFrom σ addr (encodeNat 0 ++ rest) := by
    simpa [encodeList] using hinput
  have hcurA : cursorReg < addr := lt_of_lt_of_le hsafety.cursor_below hstart
  have hlenA : lengthReg < addr := lt_of_lt_of_le hsafety.length_below hstart
  have hdoneA : doneReg < addr := lt_of_lt_of_le hsafety.done_below hstart
  obtain ⟨hcur0, hlen0, -, hf⟩ :=
    decodeNatProgram_encodeNat_append cursorReg lengthReg doneReg 0 bound addr 0 rest σ
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))
      (by omega) hcurA hlenA hdoneA
      hcursor (by simpa using hlength) hdoneInit hbits
  refine ⟨_, rfl, by simpa using hlen0, by simpa using hcur0, ?_, ?_, ?_, ?_, ?_⟩
  · apply writerState_transport_of_frame4 M curJ start pref σ _
      cursorReg lengthReg doneReg polReg hs
      (fun r hcr hlr hdr _ => hf r hcr hlr hdr)
      hsafety.cursor_nonzero hsafety.length_nonzero hsafety.done_nonzero hsafety.pol_nonzero
      hsafety.cursor_below hsafety.length_below hsafety.done_below hsafety.pol_below
  · exact (hf outerReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans houter
  · exact (hf freshReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hfresh
  · exact (hf posPolReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hpos
  · exact (hf negPolReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hneg

/-- The writer tail of the empty clause: append the two unit blocks on a fresh variable, bump the
fresh counter and decrement the outer counter, starting from the decoded registers. -/
lemma emitClauseProgram_nil_eval_write_commit
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg : ℕ)
    (base outer c : ℕ) (pref : Bits) (σ0 : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpos : σ0 posPolReg = 0) (hneg : σ0 negPolReg = 1)
    (hfresh : σ0 freshReg = base) (houter : σ0 outerReg = outer) (hcursor : σ0 cursorReg = c)
    (hs : WriterState σ0 M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ2, σ2 = (emitClauseCommitProg outerReg).eval
        ((emitClauseEmptyFreshProg freshReg).eval
          ((writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0)) ∧
      WriterState σ2 M curJ start
        (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base ++
          encodedThreeLiteralBits 1 base 1 base 1 base) ∧
      σ2 outerReg = outer - 1 ∧ σ2 freshReg = base + 1 ∧ σ2 cursorReg = c := by
  have hw := writerAppendClauseEmptyProg_eval M curJ tmpJ start pref
    posPolReg negPolReg freshReg base σ0 hcurJ htmpJ hpos hneg hfresh
    hsafety.pos_below hsafety.neg_below hsafety.fresh_below hs hroom
  have hwframe : ∀ r, r < start →
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0 r = σ0 r :=
    fun r hr => writerAppendClauseEmptyProg_frame M curJ tmpJ start pref
      posPolReg negPolReg freshReg base σ0 hcurJ htmpJ hpos hneg hfresh
      hsafety.pos_below hsafety.neg_below hsafety.fresh_below hs hroom hr
  generalize (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0 = σ1
    at hw hwframe ⊢
  have hwouter : σ1 outerReg = outer := (hwframe outerReg hsafety.outer_below).trans houter
  have hwfresh : σ1 freshReg = base := (hwframe freshReg hsafety.fresh_below).trans hfresh
  have hwcursor : σ1 cursorReg = c := (hwframe cursorReg hsafety.cursor_below).trans hcursor
  have hfreshState := writerState_assign_value M curJ start _ freshReg (base + 1) σ1 hw
    hsafety.fresh_below hsafety.fresh_nonzero
  generalize hσfresh : (emitClauseEmptyFreshProg freshReg).eval σ1 = σfresh
  have hσfreshVal : σfresh freshReg = base + 1 := by
    rw [← hσfresh]
    simp [emitClauseEmptyFreshProg, eval_assign, Expr.eval, hwfresh]
  have hσfreshOther : ∀ r, r ≠ freshReg → σfresh r = σ1 r := by
    intro r hr
    rw [← hσfresh]
    simp [emitClauseEmptyFreshProg, eval_assign, Expr.eval, writeReg_diff _ freshReg _ r hr]
  have hσfreshWriter : WriterState σfresh M curJ start
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base ++
        encodedThreeLiteralBits 1 base 1 base 1 base) := by
    rw [← hσfresh]
    simpa [emitClauseEmptyFreshProg, eval_assign, Expr.eval, hwfresh] using hfreshState
  have hσfreshOuter : σfresh outerReg = outer :=
    (hσfreshOther outerReg (hsafety.ne_of_pair (by simp))).trans hwouter
  have hσfreshCursor : σfresh cursorReg = c :=
    (hσfreshOther cursorReg (hsafety.ne_of_pair (by simp))).trans hwcursor
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · have h := writerState_assign_value M curJ start _ outerReg (outer - 1) σfresh hσfreshWriter
      hsafety.outer_below hsafety.outer_nonzero
    simp only [emitClauseCommitProg, eval_assign, Expr.eval]
    rw [hσfreshOuter]
    exact h
  · simp only [emitClauseCommitProg, eval_assign, Expr.eval]
    rw [writeReg_same, hσfreshOuter]
  · simp only [emitClauseCommitProg, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hσfreshVal
  · simp only [emitClauseCommitProg, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hσfreshCursor

lemma emitClauseProgram_nil_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest : Bits) (pref : Bits) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound : 1 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0)
    (houter : σ outerReg = outer) (hfresh : σ freshReg = base)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base []).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral []).length ∧
      τ freshReg = base + 1 ∧
      τ outerReg = outer - 1 := by
  obtain ⟨σ0, hσ0, hlen0, hcur0, hw0, hout0, hfr0, hpos0, hneg0⟩ :=
    emitClauseProgram_nil_eval_decode_length M curJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg bound base outer addr rest pref σ
      hbound hstart hinput hcursor hlength hdoneInit houter hfresh hpos hneg hs hsafety
  obtain ⟨σ2, hσ2, hstate2, houter2, hfresh2, hcursor2⟩ :=
    emitClauseProgram_nil_eval_write_commit M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg base outer (addr + 1) pref σ0
      hcurJ htmpJ hpos0 hneg0 hfr0 hout0 hcur0 hw0 hroom hsafety
  have hpayload :
      encodedThreeLiteralBits 0 base 0 base 0 base ++
        encodedThreeLiteralBits 1 base 1 base 1 base =
      encodeThreeClausesPayload (clauseToThree base []).1 := by
    simpa [writerAppendClauseLE3Payload] using
      (writerAppendClauseLE3Payload_zero 0 0 0 0 0 0 base).symm
  refine ⟨σ2, ?_, ?_, ?_, hfresh2, houter2⟩
  · rw [emitClauseProgram, eval_seq, ← hσ0,
      emitClauseDispatchProg_zero_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen0, hσ2]
    simp
  · rw [← hpayload]
    simpa [List.append_assoc] using hstate2
  · simpa [encodeList] using hcursor2

/-- Decoding the length prefix `1` of a one-literal clause leaves the cursor on the literal and
preserves the writer, the input bits and the outer and fresh registers. -/
lemma emitClauseProgram_one_eval_decode_length
    (M curJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hlistBound : 2 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base)
    (hs : WriterState σ M curJ start pref)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ0, σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ ∧
      σ0 lengthReg = 1 ∧ σ0 cursorReg = addr + 2 ∧
      BitsFrom σ0 (addr + 2) (encodeLiteral l ++ rest) ∧
      WriterState σ0 M curJ start pref ∧ σ0 outerReg = outer ∧ σ0 freshReg = base := by
  have hbits : BitsFrom σ addr (encodeNat 1 ++ (encodeLiteral l ++ rest)) := by
    simpa [encodeList, List.append_assoc] using hinput
  have hcurA : cursorReg < addr := lt_of_lt_of_le hsafety.cursor_below hstart
  have hlenA : lengthReg < addr := lt_of_lt_of_le hsafety.length_below hstart
  have hdoneA : doneReg < addr := lt_of_lt_of_le hsafety.done_below hstart
  obtain ⟨hcur0, hlen0, -, hf⟩ :=
    decodeNatProgram_encodeNat_append cursorReg lengthReg doneReg 1 bound addr 0
      (encodeLiteral l ++ rest) σ
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))
      hlistBound hcurA hlenA hdoneA
      hcursor (by simpa using hlength) hdoneInit hbits
  refine ⟨_, rfl, by simpa using hlen0, by simpa using hcur0, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeNat 1) _ hbits
    intro i hi
    have := hf (addr + 2 + i) (by omega) (by omega) (by omega)
    simpa using this.trans (htail i hi)
  · apply writerState_transport_of_frame4 M curJ start pref σ _
      cursorReg lengthReg doneReg polReg hs
      (fun r hcr hlr hdr _ => hf r hcr hlr hdr)
      hsafety.cursor_nonzero hsafety.length_nonzero hsafety.done_nonzero hsafety.pol_nonzero
      hsafety.cursor_below hsafety.length_below hsafety.done_below hsafety.pol_below
  · exact (hf outerReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans houter
  · exact (hf freshReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hfresh

/-- Decoding the literal of a one-literal clause leaves it in the polarity and value registers
and keeps the writer, the outer and fresh registers; the cursor ends after the clause. -/
lemma emitClauseProgram_one_eval_decode_literal
    (M curJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest : Bits) (pref : Bits) (σ0 : Store)
    (hbound : l.var + 1 ≤ bound) (hstart : start ≤ addr)
    (hcursor : σ0 cursorReg = addr + 2)
    (hbits : BitsFrom σ0 (addr + 2) (encodeLiteral l ++ rest))
    (hs : WriterState σ0 M curJ start pref)
    (houter : σ0 outerReg = outer) (hfresh : σ0 freshReg = base)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ1, σ1 = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0 ∧
      σ1 polReg = literalPolarity l ∧ σ1 varReg = l.var ∧
      σ1 freshReg = base ∧ σ1 outerReg = outer ∧
      σ1 cursorReg = addr + l.var + 4 ∧
      WriterState σ1 M curJ start pref := by
  have hstart2 : start ≤ addr + 2 := by omega
  obtain ⟨hcur1, hpol1, hvar1, -, hframe1⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound
      (addr + 2) l rest σ0
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (lt_of_lt_of_le hsafety.cursor_below hstart2)
      (lt_of_lt_of_le hsafety.pol_below hstart2)
      (lt_of_lt_of_le hsafety.var_below hstart2)
      (lt_of_lt_of_le hsafety.done_below hstart2)
      hbound hcursor hbits
  refine ⟨_, rfl, ?_, by simpa using hvar1, ?_, ?_, ?_, ?_⟩
  · cases l <;> simpa [literalPolarity] using hpol1
  · exact (hframe1 freshReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))).trans hfresh
  · exact (hframe1 outerReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))).trans houter
  · calc _ = addr + 2 + l.var + 2 := by simpa using hcur1
      _ = addr + l.var + 4 := by omega
  · exact writerState_transport_of_frame4 M curJ start pref σ0 _ cursorReg polReg varReg
      doneReg hs hframe1 hsafety.cursor_nonzero hsafety.pol_nonzero hsafety.var_nonzero
      hsafety.done_nonzero hsafety.cursor_below hsafety.pol_below hsafety.var_below
      hsafety.done_below

/-- The writer tail of the one-literal clause: append the three-literal block and decrement the
outer counter, starting from the decoded literal registers. -/
lemma emitClauseProgram_one_eval_write_commit
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg : ℕ)
    (base outer c : ℕ) (l : Literal) (pref : Bits) (σ1 : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ1 polReg = literalPolarity l) (hvar : σ1 varReg = l.var)
    (hfresh : σ1 freshReg = base) (houter : σ1 outerReg = outer) (hcursor : σ1 cursorReg = c)
    (hs : WriterState σ1 M curJ start pref)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    let σ3 := (emitClauseCommitProg outerReg).eval
      ((writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1)
    WriterState σ3 M curJ start
      (pref ++ encodedThreeLiteralBits (literalPolarity l) l.var
        (literalPolarity l) l.var (literalPolarity l) l.var) ∧
    σ3 outerReg = outer - 1 ∧ σ3 freshReg = base ∧ σ3 cursorReg = c := by
  dsimp only
  have hpolcases : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hw := writerAppendClauseOneProg_eval M curJ tmpJ start pref
    polReg varReg (literalPolarity l) l.var σ1 hcurJ htmpJ hpol hvar hpolcases
    ⟨hsafety.pol_below, hsafety.var_below⟩ hs hroom
  have hwframe : ∀ r, r < start →
      (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1 r = σ1 r :=
    fun r hr => writerAppendClauseOneProg_frame M curJ tmpJ start pref polReg varReg
      (literalPolarity l) l.var σ1 hcurJ htmpJ hpol hvar hpolcases
      ⟨hsafety.pol_below, hsafety.var_below⟩ hs hroom hr
  generalize (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1 = σ2 at hw hwframe ⊢
  have hwouter : σ2 outerReg = outer := (hwframe outerReg hsafety.outer_below).trans houter
  have hwfresh : σ2 freshReg = base := (hwframe freshReg hsafety.fresh_below).trans hfresh
  have hwcursor : σ2 cursorReg = c := (hwframe cursorReg hsafety.cursor_below).trans hcursor
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := writerState_assign_value M curJ start _ outerReg (outer - 1) σ2 hw
      hsafety.outer_below hsafety.outer_nonzero
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [hwouter]
    exact h
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_same, hwouter]
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwfresh
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwcursor

lemma emitClauseProgram_one_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound : l.var + 1 ≤ bound) (hlistBound : 2 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0)
    (houter : σ outerReg = outer) (hfresh : σ freshReg = base)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l]).length ∧
      τ freshReg = base ∧
      τ outerReg = outer - 1 := by
  obtain ⟨σ0, hσ0, hlen0, hcur0, hbits0, hw0, hout0, hfr0⟩ :=
    emitClauseProgram_one_eval_decode_length M curJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg bound base outer addr l rest pref σ
      hlistBound hstart hinput hcursor hlength hdoneInit houter hfresh hs hsafety
  obtain ⟨σ1, hσ1, hpol1, hvar1, hfresh1, houter1, hcur1, hw1⟩ :=
    emitClauseProgram_one_eval_decode_literal M curJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg bound base outer addr l rest pref σ0
      hbound hstart hcur0 hbits0 hw0 hout0 hfr0 hsafety
  obtain ⟨hstate3, houter3, hfresh3, hcursor3⟩ :=
    emitClauseProgram_one_eval_write_commit M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg base outer
      (addr + l.var + 4) l pref σ1 hcurJ htmpJ hpol1 hvar1 hfresh1 houter1 hcur1 hw1
      (by omega) hsafety
  have hpayload :
      encodedThreeLiteralBits (literalPolarity l) l.var
          (literalPolarity l) l.var (literalPolarity l) l.var =
        encodeThreeClausesPayload (clauseToThree base [l]).1 := by
    cases l <;>
      simp [literalPolarity, clauseToThree,
        encodeThreeClausesPayload, encodeThreeClause, encodedThreeLiteralBits,
        encodedLiteralBits, encodeLiteral, Literal.var, natBit]
  refine ⟨_, ?_, ?_, ?_, hfresh3, houter3⟩
  · rw [emitClauseProgram, eval_seq, ← hσ0, emitClauseDispatchProg_one_eval _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ σ0 hlen0]
    simp only [eval_seq]
    rw [← hσ1]
  · rw [← hpayload]
    simpa [List.append_assoc] using hstate3
  · rw [hcursor3]
    cases l <;>
      simp [encodeList, encodeLiteral, encodeNat_length, Literal.var, List.length_append] <;> omega

/-- Decoding the length prefix `2` of a two-literal clause leaves the cursor on the first
literal and preserves the writer, the input bits and the outer and fresh registers. -/
lemma emitClauseProgram_two_eval_decode_length
    (M curJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hlistBound : 3 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l1, l2] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base)
    (hs : WriterState σ M curJ start pref)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ0, σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ ∧
      σ0 lengthReg = 2 ∧ σ0 cursorReg = addr + 3 ∧
      BitsFrom σ0 (addr + 3) (encodeLiteral l1 ++ encodeLiteral l2 ++ rest) ∧
      WriterState σ0 M curJ start pref ∧ σ0 outerReg = outer ∧ σ0 freshReg = base := by
  have hbits : BitsFrom σ addr
      (encodeNat 2 ++ (encodeLiteral l1 ++ encodeLiteral l2 ++ rest)) := by
    simpa [encodeList, List.append_assoc] using hinput
  have hcurA : cursorReg < addr := lt_of_lt_of_le hsafety.cursor_below hstart
  have hlenA : lengthReg < addr := lt_of_lt_of_le hsafety.length_below hstart
  have hdoneA : doneReg < addr := lt_of_lt_of_le hsafety.done_below hstart
  obtain ⟨hcur0, hlen0, hdone0, hframe0⟩ :=
    decodeNatProgram_encodeNat_append cursorReg lengthReg doneReg 2 bound addr 0
      (encodeLiteral l1 ++ encodeLiteral l2 ++ rest) σ
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))
      hlistBound hcurA hlenA hdoneA
      hcursor (by simpa using hlength) hdoneInit hbits
  have hf : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg →
      (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ r = σ r := hframe0
  refine ⟨_, rfl, by simpa using hlen0, by simpa using hcur0, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeNat 2) _ hbits
    intro i hi
    have := hf (addr + 3 + i) (by omega) (by omega) (by omega)
    simpa using this.trans (htail i hi)
  · apply writerState_transport_of_frame4 M curJ start pref σ _
      cursorReg lengthReg doneReg polReg hs
      (fun r hcr hlr hdr _ => hf r hcr hlr hdr)
      hsafety.cursor_nonzero hsafety.length_nonzero hsafety.done_nonzero hsafety.pol_nonzero
      hsafety.cursor_below hsafety.length_below hsafety.done_below hsafety.pol_below
  · exact (hf outerReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans houter
  · exact (hf freshReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hfresh

/-- Decoding the two literals of a two-literal clause leaves each literal in its value registers
and keeps the writer, the outer and fresh registers; the cursor ends after the clause. -/
lemma emitClauseProgram_two_eval_decode_literals
    (M curJ start cursorReg polReg varReg doneReg pol2Reg var2Reg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest : Bits) (pref : Bits) (σ0 : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound) (hstart : start ≤ addr)
    (hcursor : σ0 cursorReg = addr + 3)
    (hbits : BitsFrom σ0 (addr + 3) (encodeLiteral l1 ++ encodeLiteral l2 ++ rest))
    (hs : WriterState σ0 M curJ start pref)
    (houter : σ0 outerReg = outer) (hfresh : σ0 freshReg = base)
    (hbelow : cursorReg < start ∧ polReg < start ∧ varReg < start ∧ doneReg < start)
    (hnonzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg]) :
    ∃ σ2, σ2 = (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval
        ((decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0) ∧
      σ2 polReg = literalPolarity l1 ∧ σ2 varReg = l1.var ∧
      σ2 pol2Reg = literalPolarity l2 ∧ σ2 var2Reg = l2.var ∧
      σ2 freshReg = base ∧ σ2 outerReg = outer ∧
      σ2 cursorReg = addr + 3 + l1.var + 2 + l2.var + 2 ∧
      WriterState σ2 M curJ start pref := by
  obtain ⟨hcB, hpB, hvB, hdB⟩ := hbelow
  obtain ⟨hcN, hpN, hvN, hdN⟩ := hnonzero
  simp [RegisterPairwise, registerPairs] at hpairSafe
  have hne := fun (a b : ℕ) => @hpairSafe a b
  obtain ⟨σ1, σ2, hσ1, hσ2, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg polReg varReg pol2Reg var2Reg doneReg bound
      (addr + 3) l1 l2 rest σ0
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (by exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
      hbound1 hbound2 hcursor hbits
  have h1 : WriterState σ1 M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ0 σ1 cursorReg polReg varReg doneReg
      hs hframe1 hcN hpN hvN hdN hcB hpB hvB hdB
  refine ⟨σ2, by rw [hσ2, hσ1], ?_, ?_, hpol2, hvar2, ?_, ?_, hcur2, ?_⟩
  · rw [hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))]
    exact hpol1
  · rw [hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))]
    exact hvar1
  · rw [hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)), hframe1 _ (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp))]
    exact hfresh
  · rw [hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)), hframe1 _ (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp))]
    exact houter
  · exact writerState_transport_of_frame4 M curJ start pref σ1 σ2 cursorReg pol2Reg var2Reg
      doneReg h1 hframe2 hcN hpairNonzero.1 hpairNonzero.2 hdN hcB hpairBelow.1
      hpairBelow.2 hdB

/-- The writer tail of the two-literal clause: append the three-literal block and decrement the
outer counter, starting from the decoded literal registers. -/
lemma emitClauseProgram_two_eval_write_commit
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      pol2Reg var2Reg posPolReg negPolReg freshReg outerReg : ℕ)
    (base outer c : ℕ) (l1 l2 : Literal) (pref : Bits) (σ2 : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol1 : σ2 polReg = literalPolarity l1) (hvar1 : σ2 varReg = l1.var)
    (hpol2 : σ2 pol2Reg = literalPolarity l2) (hvar2 : σ2 var2Reg = l2.var)
    (hfresh : σ2 freshReg = base) (houter : σ2 outerReg = outer) (hcursor : σ2 cursorReg = c)
    (hs : WriterState σ2 M curJ start pref)
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start) :
    let σ4 := (emitClauseCommitProg outerReg).eval
      ((writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval σ2)
    WriterState σ4 M curJ start
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var (literalPolarity l2) l2.var) ∧
    σ4 outerReg = outer - 1 ∧ σ4 freshReg = base ∧ σ4 cursorReg = c := by
  dsimp only
  have hpolcases1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpolcases2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hw := writerAppendClauseTwoProg_eval M curJ tmpJ start pref
    polReg varReg pol2Reg var2Reg (literalPolarity l1) l1.var
    (literalPolarity l2) l2.var σ2 hcurJ htmpJ hpol1 hvar1 hpol2 hvar2
    hpolcases1 hpolcases2 hsafety.var_below hpairBelow hs hroom
  have hwframe : ∀ r, r < start →
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval σ2 r = σ2 r :=
    fun r hr => writerAppendClauseTwoProg_frame M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var σ2 hcurJ htmpJ hpol1 hvar1 hpol2 hvar2
      hpolcases1 hpolcases2 hsafety.var_below hpairBelow hs hroom hr
  generalize (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval σ2 = σ3
    at hw hwframe ⊢
  have hwouter : σ3 outerReg = outer := (hwframe outerReg hsafety.outer_below).trans houter
  have hwfresh : σ3 freshReg = base := (hwframe freshReg hsafety.fresh_below).trans hfresh
  have hwcursor : σ3 cursorReg = c := (hwframe cursorReg hsafety.cursor_below).trans hcursor
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := writerState_assign_value M curJ start _ outerReg (outer - 1) σ3 hw
      hsafety.outer_below hsafety.outer_nonzero
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [hwouter]
    exact h
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_same, hwouter]
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwfresh
  · dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwcursor

lemma emitClauseProgram_two_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hlistBound : 3 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l1, l2] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg,
        freshReg, outerReg]) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l1, l2]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l1, l2]).length ∧
      τ freshReg = (clauseToThree base [l1, l2]).2 ∧ τ outerReg = outer - 1 := by
  obtain ⟨σ0, hσ0, hlen0, hcur0, hbits0, hw0, hout0, hfr0⟩ :=
    emitClauseProgram_two_eval_decode_length M curJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg bound base outer addr l1 l2 rest pref σ
      hlistBound hstart hinput hcursor hlength hdoneInit houter hfresh hs hsafety
  obtain ⟨σ2, hσ2, hpol1, hvar1, hpol2, hvar2, hfresh2, houter2, hcur2, hw2⟩ :=
    emitClauseProgram_two_eval_decode_literals M curJ start cursorReg polReg varReg doneReg
      pol2Reg var2Reg freshReg outerReg bound base outer addr l1 l2 rest pref σ0
      hbound1 hbound2 hstart hcur0 hbits0 hw0 hout0 hfr0
      ⟨hsafety.cursor_below, hsafety.pol_below, hsafety.var_below, hsafety.done_below⟩
      ⟨hsafety.cursor_nonzero, hsafety.pol_nonzero, hsafety.var_nonzero, hsafety.done_nonzero⟩
      hpairBelow hpairNonzero hpairSafe
  obtain ⟨hstate4, houter4, hfresh4, hcursor4⟩ :=
    emitClauseProgram_two_eval_write_commit M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg pol2Reg var2Reg posPolReg negPolReg freshReg outerReg base outer
      (addr + 3 + l1.var + 2 + l2.var + 2) l1 l2 pref σ2 hcurJ htmpJ hpol1 hvar1 hpol2 hvar2
      hfresh2 houter2 hcur2 hw2 (by omega) hsafety hpairBelow
  have hpayload :
      encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var (literalPolarity l2) l2.var =
        encodeThreeClausesPayload (clauseToThree base [l1, l2]).1 := by
    cases l1 <;> cases l2 <;>
      simp [literalPolarity, clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
        encodedThreeLiteralBits, encodedLiteralBits, encodeLiteral, Literal.var, natBit]
  refine ⟨_, ?_, ?_, ?_, hfresh4, houter4⟩
  · rw [emitClauseProgram, eval_seq, ← hσ0, emitClauseDispatchProg_two_eval _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ σ0 hlen0]
    simp only [eval_seq]
    rw [← hσ2]
  · rw [← hpayload]
    simpa [List.append_assoc] using hstate4
  · rw [hcursor4]
    cases l1 <;> cases l2 <;>
      simp [encodeList, encodeLiteral, encodeNat_length, Literal.var, List.length_append] <;> omega

/-- Decoding the length prefix `3` of a three-literal clause leaves the cursor on the first
literal and preserves the writer, the input bits and the outer, fresh and polarity registers. -/
lemma emitClauseProgram_three_eval_decode_length
    (M curJ start cursorReg polReg varReg doneReg lengthReg
      posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hlistBound : 4 ≤ bound) (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l1, l2, l3] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base) (hpos : σ posPolReg = 0)
    (hneg : σ negPolReg = 1)
    (hs : WriterState σ M curJ start pref)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    ∃ σ0, σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ ∧
      σ0 lengthReg = 3 ∧ σ0 cursorReg = addr + 4 ∧
      BitsFrom σ0 (addr + 4) (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest) ∧
      WriterState σ0 M curJ start pref ∧ σ0 outerReg = outer ∧ σ0 freshReg = base ∧
      σ0 posPolReg = 0 ∧ σ0 negPolReg = 1 := by
  have hbits : BitsFrom σ addr
      (encodeNat 3 ++ (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest)) := by
    simpa [encodeList, List.append_assoc] using hinput
  have hcurA : cursorReg < addr := lt_of_lt_of_le hsafety.cursor_below hstart
  have hlenA : lengthReg < addr := lt_of_lt_of_le hsafety.length_below hstart
  have hdoneA : doneReg < addr := lt_of_lt_of_le hsafety.done_below hstart
  obtain ⟨hcur0, hlen0, hdone0, hframe0⟩ :=
    decodeNatProgram_encodeNat_append cursorReg lengthReg doneReg 3 bound addr 0
      (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest) σ
      (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))
      hlistBound hcurA hlenA hdoneA
      hcursor (by simpa using hlength) hdoneInit hbits
  have hf : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg →
      (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ r = σ r := hframe0
  refine ⟨_, rfl, by simpa using hlen0, by simpa using hcur0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeNat 3) _ hbits
    intro i hi
    have := hf (addr + 4 + i) (by omega) (by omega) (by omega)
    simpa using this.trans (htail i hi)
  · apply writerState_transport_of_frame4 M curJ start pref σ _
      cursorReg lengthReg doneReg polReg hs
      (fun r hcr hlr hdr _ => hf r hcr hlr hdr)
      hsafety.cursor_nonzero hsafety.length_nonzero hsafety.done_nonzero hsafety.pol_nonzero
      hsafety.cursor_below hsafety.length_below hsafety.done_below hsafety.pol_below
  · exact (hf outerReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans houter
  · exact (hf freshReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hfresh
  · exact (hf posPolReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hpos
  · exact (hf negPolReg (hsafety.ne_of_pair (by simp)) (hsafety.ne_of_pair (by simp))
      (hsafety.ne_of_pair (by simp))).trans hneg

/-- The bits of the third literal and the rest stay readable after the first two literals are
decoded, since the decoders only write registers below the input. -/
lemma emitClauseProgram_three_eval_tail_bits
    (σ0 σ1 σ2 : Store) (cursorReg polReg varReg pol2Reg var2Reg doneReg a : ℕ)
    (l1 l2 l3 : Literal) (rest : Bits)
    (hbits : BitsFrom σ0 a (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest))
    (hframe1 : ∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → σ1 r = σ0 r)
    (hframe2 : ∀ r, r ≠ cursorReg → r ≠ pol2Reg → r ≠ var2Reg → r ≠ doneReg → σ2 r = σ1 r)
    (hlow : cursorReg < a ∧ polReg < a ∧ varReg < a ∧ pol2Reg < a ∧ var2Reg < a ∧
      doneReg < a) :
    BitsFrom σ2 (a + l1.var + 2 + l2.var + 2) (encodeLiteral l3 ++ rest) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlow
  obtain ⟨_, ht1⟩ := bitsFrom_append σ0 a (encodeLiteral l1)
    (encodeLiteral l2 ++ (encodeLiteral l3 ++ rest)) (by simpa [List.append_assoc] using hbits)
  have hlen1 : (encodeLiteral l1).length = l1.var + 2 := by
    cases l1 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  rw [hlen1] at ht1
  obtain ⟨_, ht2⟩ := bitsFrom_append σ1 (a + l1.var + 2)
    (encodeLiteral l2) (encodeLiteral l3 ++ rest) (by
      intro i hi
      have hf := hframe1 (a + l1.var + 2 + i) (by omega) (by omega) (by omega) (by omega)
      exact hf.trans (ht1 i hi))
  have hlen2 : (encodeLiteral l2).length = l2.var + 2 := by
    cases l2 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  rw [hlen2] at ht2
  intro i hi
  have hf := hframe2 (a + l1.var + 2 + l2.var + 2 + i)
    (by omega) (by omega) (by omega) (by omega)
  exact hf.trans (ht2 i hi)

/-- Decoding the three literals of a three-literal clause leaves every literal in its value
registers and keeps the writer and the other registers; the cursor ends after the clause. -/
lemma emitClauseProgram_three_eval_decode_literals
    (M curJ start cursorReg polReg varReg doneReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg bound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest : Bits) (pref : Bits) (σ0 : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound) (hstart : start ≤ addr)
    (hcursor : σ0 cursorReg = addr + 4)
    (hbits : BitsFrom σ0 (addr + 4)
      (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest))
    (hs : WriterState σ0 M curJ start pref)
    (houter : σ0 outerReg = outer) (hfresh : σ0 freshReg = base)
    (hpos : σ0 posPolReg = 0) (hneg : σ0 negPolReg = 1)
    (hbelow : cursorReg < start ∧ polReg < start ∧ varReg < start ∧ doneReg < start)
    (hnonzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg]) :
    ∃ σ3, σ3 = (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval
        ((decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval
          ((decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0)) ∧
      σ3 polReg = literalPolarity l1 ∧ σ3 varReg = l1.var ∧
      σ3 pol2Reg = literalPolarity l2 ∧ σ3 var2Reg = l2.var ∧
      σ3 pol3Reg = literalPolarity l3 ∧ σ3 var3Reg = l3.var ∧
      σ3 posPolReg = 0 ∧ σ3 negPolReg = 1 ∧ σ3 freshReg = base ∧ σ3 outerReg = outer ∧
      σ3 cursorReg = addr + 4 + l1.var + 2 + l2.var + 2 + l3.var + 2 ∧
      WriterState σ3 M curJ start pref := by
  obtain ⟨hcB, hpB, hvB, hdB⟩ := hbelow
  obtain ⟨hcN, hpN, hvN, hdN⟩ := hnonzero
  simp [RegisterPairwise, registerPairs] at htripleSafe
  have hne := fun (a b : ℕ) => @htripleSafe a b
  obtain ⟨σ1, σ2, hσ1, hσ2, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg polReg varReg pol2Reg var2Reg doneReg bound
      (addr + 4) l1 l2 (encodeLiteral l3 ++ rest) σ0
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (by exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
      hbound1 hbound2 hcursor (by simpa [List.append_assoc] using hbits)
  have htail2 := emitClauseProgram_three_eval_tail_bits σ0 σ1 σ2 cursorReg polReg varReg
    pol2Reg var2Reg doneReg (addr + 4) l1 l2 l3 rest hbits hframe1 hframe2
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨hcur3, hpol3, hvar3, hdone3, hframe3⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol3Reg var3Reg doneReg bound
      (addr + 4 + l1.var + 2 + l2.var + 2) l3 rest σ2
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp))
      (by omega) (by omega) (by omega) (by omega) hbound3
      (by simpa [hσ2] using hcur2) htail2
  have hchain : ∀ r, r ≠ cursorReg → r ≠ doneReg → r ≠ polReg → r ≠ varReg → r ≠ pol2Reg →
      r ≠ var2Reg → r ≠ pol3Reg → r ≠ var3Reg →
      (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval σ2 r = σ0 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [hframe3 r h1 h7 h8 h2, hframe2 r h1 h5 h6 h2, hframe1 r h1 h3 h4 h2]
  refine ⟨(decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval σ2,
    by rw [hσ2, hσ1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe3 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)),
      hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))]
    simpa [hσ1] using hpol1
  · rw [hframe3 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)),
      hframe2 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))]
    simpa [hσ1] using hvar1
  · rw [hframe3 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))]
    simpa [hσ2] using hpol2
  · rw [hframe3 _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))]
    simpa [hσ2] using hvar2
  · cases l3 <;> simpa [literalPolarity] using hpol3
  · exact hvar3
  · exact (hchain _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))).trans hpos
  · exact (hchain _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))).trans hneg
  · exact (hchain _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))).trans hfresh
  · exact (hchain _ (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp))).trans houter
  · exact hcur3
  · have h1 : WriterState σ1 M curJ start pref :=
      writerState_transport_of_frame4 M curJ start pref σ0 σ1 cursorReg polReg varReg doneReg
        hs hframe1 hcN hpN hvN hdN hcB hpB hvB hdB
    have h2 : WriterState σ2 M curJ start pref :=
      writerState_transport_of_frame4 M curJ start pref σ1 σ2 cursorReg pol2Reg var2Reg doneReg
        h1 hframe2 hcN htripleNonzero.1 htripleNonzero.2.1 hdN hcB htripleBelow.1
        htripleBelow.2.1 hdB
    exact writerState_transport_of_frame4 M curJ start pref σ2 _ cursorReg pol3Reg var3Reg
      doneReg h2 hframe3 hcN htripleNonzero.2.2.1 htripleNonzero.2.2.2 hdN hcB
      htripleBelow.2.2.1 htripleBelow.2.2.2 hdB

/-- The writer tail of the three-literal clause: append the two three-literal blocks, bump the
fresh counter and decrement the outer counter, starting from the decoded literal registers. -/
lemma emitClauseProgram_three_eval_write_commit
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg : ℕ)
    (base outer c : ℕ) (l1 l2 l3 : Literal) (pref : Bits) (σ3 : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol1 : σ3 polReg = literalPolarity l1) (hvar1 : σ3 varReg = l1.var)
    (hpol2 : σ3 pol2Reg = literalPolarity l2) (hvar2 : σ3 var2Reg = l2.var)
    (hpol3 : σ3 pol3Reg = literalPolarity l3) (hvar3 : σ3 var3Reg = l3.var)
    (hpos : σ3 posPolReg = 0) (hneg : σ3 negPolReg = 1) (hfresh : σ3 freshReg = base)
    (houter : σ3 outerReg = outer) (hcursor : σ3 cursorReg = c)
    (hs : WriterState σ3 M curJ start pref)
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start) :
    let σ5 := (emitClauseCommitProg outerReg).eval
      ((emitClauseEmptyFreshProg freshReg).eval
        ((writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
          pol3Reg var3Reg posPolReg negPolReg freshReg).eval σ3))
    WriterState σ5 M curJ start
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base ++
        encodedThreeLiteralBits 1 base (literalPolarity l3) l3.var
          (literalPolarity l3) l3.var) ∧
    σ5 outerReg = outer - 1 ∧ σ5 freshReg = base + 1 ∧ σ5 cursorReg = c := by
  intro σ5
  have hpolcases1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpolcases2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hpolcases3 : literalPolarity l3 = 0 ∨ literalPolarity l3 = 1 := by
    cases l3 <;> simp [literalPolarity]
  have hw := writerAppendClauseThreeProg_eval M curJ tmpJ start pref
    polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var
    (literalPolarity l3) l3.var base σ3 hcurJ htmpJ hpol1 hvar1 hpol2 hvar2
    hpol3 hvar3 hpolcases1 hpolcases2 hpolcases3 hpos hneg hfresh
    hsafety.var_below ⟨htripleBelow.1, htripleBelow.2.1⟩
    ⟨htripleBelow.2.2.1, htripleBelow.2.2.2⟩
    hsafety.pos_below hsafety.neg_below hsafety.fresh_below hs hroom
  have hwframe : ∀ r, r < start →
      (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval σ3 r = σ3 r := fun r hr =>
    writerAppendClauseThreeProg_frame M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var
      (literalPolarity l3) l3.var base σ3 hcurJ htmpJ hpol1 hvar1 hpol2 hvar2
      hpol3 hvar3 hpolcases1 hpolcases2 hpolcases3 hpos hneg hfresh
      hsafety.var_below ⟨htripleBelow.1, htripleBelow.2.1⟩
      ⟨htripleBelow.2.2.1, htripleBelow.2.2.2⟩
      hsafety.pos_below hsafety.neg_below hsafety.fresh_below hs hroom hr
  set σ4 := (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
    pol3Reg var3Reg posPolReg negPolReg freshReg).eval σ3
  have hw4f : WriterState ((emitClauseEmptyFreshProg freshReg).eval σ4) M curJ start
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base ++
        encodedThreeLiteralBits 1 base (literalPolarity l3) l3.var
          (literalPolarity l3) l3.var) := by
    dsimp [emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    exact writerState_assign_value M curJ start _ freshReg _ σ4 hw
      hsafety.fresh_below hsafety.fresh_nonzero
  have hwouter : σ4 outerReg = outer := (hwframe outerReg hsafety.outer_below).trans houter
  have hwfresh : σ4 freshReg = base := (hwframe freshReg hsafety.fresh_below).trans hfresh
  have hwcursor : σ4 cursorReg = c := (hwframe cursorReg hsafety.cursor_below).trans hcursor
  have hwouterf : (emitClauseEmptyFreshProg freshReg).eval σ4 outerReg = outer := by
    dsimp [emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwouter
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := writerState_assign_value M curJ start _ outerReg (outer - 1) _ hw4f
      hsafety.outer_below hsafety.outer_nonzero
    dsimp [σ5, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [hwouterf]
    exact h
  · dsimp [σ5, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_same, hwouterf]
  · dsimp [σ5, emitClauseCommitProg, emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp)), writeReg_same]
    change σ4 freshReg + 1 = base + 1
    rw [hwfresh]
  · dsimp [σ5, emitClauseCommitProg, emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp)),
      writeReg_diff _ _ _ _ (hsafety.ne_of_pair (by simp))]
    exact hwcursor

lemma emitClauseProgram_three_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest : Bits) (pref : Bits) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound) (hlistBound : 4 ≤ bound)
    (hstart : start ≤ addr)
    (hinput : BitsFrom σ addr (encodeList encodeLiteral [l1, l2, l3] ++ rest))
    (hcursor : σ cursorReg = addr) (hlength : σ lengthReg = 0)
    (hdoneInit : σ doneReg = 0) (houter : σ outerReg = outer)
    (hfresh : σ freshReg = base) (hpos : σ posPolReg = 0)
    (hneg : σ negPolReg = 1)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg]) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l1, l2, l3]).length ∧
      τ freshReg = (clauseToThree base [l1, l2, l3]).2 ∧ τ outerReg = outer - 1 := by
  obtain ⟨σ0, hσ0, hlen0, hcur0, hbits0, hw0, hout0, hfr0, hpos0, hneg0⟩ :=
    emitClauseProgram_three_eval_decode_length M curJ start cursorReg polReg varReg doneReg
      lengthReg posPolReg negPolReg freshReg outerReg bound base outer addr l1 l2 l3 rest pref σ
      hlistBound hstart hinput hcursor hlength hdoneInit houter hfresh hpos hneg hs hsafety
  obtain ⟨σ3, hσ3, hpol1, hvar1, hpol2, hvar2, hpol3, hvar3, hpos3, hneg3, hfresh3, houter3,
      hcur3, hw3⟩ :=
    emitClauseProgram_three_eval_decode_literals M curJ start cursorReg polReg varReg doneReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg bound base outer
      addr l1 l2 l3 rest pref σ0 hbound1 hbound2 hbound3 hstart hcur0 hbits0 hw0 hout0 hfr0
      hpos0 hneg0 ⟨hsafety.cursor_below, hsafety.pol_below, hsafety.var_below, hsafety.done_below⟩
      ⟨hsafety.cursor_nonzero, hsafety.pol_nonzero, hsafety.var_nonzero, hsafety.done_nonzero⟩
      htripleBelow htripleNonzero htripleSafe
  obtain ⟨hstate5, houter5, hfresh5, hcursor5⟩ :=
    emitClauseProgram_three_eval_write_commit M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg base
      outer (addr + 4 + l1.var + 2 + l2.var + 2 + l3.var + 2) l1 l2 l3 pref σ3 hcurJ htmpJ
      hpol1 hvar1 hpol2 hvar2 hpol3 hvar3 hpos3 hneg3 hfresh3 houter3 hcur3 hw3 hroom hsafety
      htripleBelow
  have hpayload :
      encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base ++
        encodedThreeLiteralBits 1 base (literalPolarity l3) l3.var
          (literalPolarity l3) l3.var =
        encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1 := by
    cases l1 <;> cases l2 <;> cases l3 <;>
      simp [literalPolarity, clauseToThree, splitTail_one, encodeThreeClausesPayload,
        encodeThreeClause, encodedThreeLiteralBits, encodedLiteralBits, encodeLiteral,
        Literal.var, natBit]
  refine ⟨_, ?_, ?_, ?_, ?_, houter5⟩
  · rw [emitClauseProgram, eval_seq, ← hσ0, emitClauseDispatchProg_three_eval _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ σ0 hlen0]
    simp only [eval_seq]
    rw [← hσ3]
  · rw [← hpayload]
    simpa [List.append_assoc] using hstate5
  · rw [hcursor5]
    cases l1 <;> cases l2 <;> cases l3 <;>
      simp [encodeList, encodeLiteral, encodeNat_length, Literal.var, List.length_append] <;> omega
  · simpa [clauseToThree, splitTail_one] using hfresh5

lemma emitClauseProgram_long_eval_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (σ σ0 σprep : Store)
    (hσ0 : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ)
    (hlen0 : σ0 lengthReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (.seq (.assign carryPolReg (.const 1))
          (.seq (.assign carryValReg (.reg freshReg))
            (.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0)
    (hinput : BitsFrom σprep (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hstartAtInput : start ≤ addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hwriter : WriterState σprep M curJ start pref)
    (hpos : σprep posPolReg = 0) (hfresh : σprep freshReg = base)
    (hremaining : σprep remainingReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hcursor : σprep cursorReg = addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (houterBelow : outerReg < start) (houterNonzero : outerReg ≠ 0)
    (houterDisjoint : outerReg ≠ freshReg ∧ outerReg ≠ cursorReg)
    (houterLong :
      (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        bound tailBound).eval σprep outerReg = outer)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
      M + curJ) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base
          (l1 :: l2 :: l3 :: l4 :: rest)).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral
        (l1 :: l2 :: l3 :: l4 :: rest)).length ∧
      τ freshReg = (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).2 ∧
      τ outerReg = outer - 1 := by
  obtain ⟨τ, hτ, hwriterR, hremainingR, hfreshR, hcursorR⟩ :=
    splitTailEmitLongClauseProg_eval_end_to_end
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound base l1 l2 l3 l4 rest pref tail
        (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1) σprep
      hbound1 hbound2 hboundTail hls hroom hcapacity
      hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety
  have houterτ : τ outerReg = outer := by
    simpa [hτ] using houterLong
  let σf := (emitClauseCommitProg outerReg).eval τ
  have hwriterf : WriterState σf M curJ start
      (pref ++ encodeThreeClausesPayload (clauseToThree base
        (l1 :: l2 :: l3 :: l4 :: rest)).1) := by
    have h := writerState_assign_value M curJ start
      (pref ++ encodeThreeClausesPayload (clauseToThree base
        (l1 :: l2 :: l3 :: l4 :: rest)).1)
      outerReg (outer - 1) τ hwriterR
      houterBelow houterNonzero
    dsimp [σf, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [houterτ]
    exact h
  have houterf : σf outerReg = outer - 1 := by
    dsimp [σf, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_same, houterτ]
  have hfreshf : σf freshReg =
      (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).2 := by
    dsimp [σf, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    have hdiff : freshReg ≠ outerReg := houterDisjoint.1.symm
    rw [writeReg_diff _ _ _ _ hdiff]
    exact hfreshR
  have hcursorf : σf cursorReg =
      (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1) + (splitTailInputBits
        (l1 :: l2 :: l3 :: l4 :: rest) []).length := by
    dsimp [σf, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    have hdiff : cursorReg ≠ outerReg := houterDisjoint.2.symm
    rw [writeReg_diff _ _ _ _ hdiff]
    exact hcursorR
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 = σf := by
    have hlenGe : 4 ≤ (l1 :: l2 :: l3 :: l4 :: rest).length := by simp
    rw [emitClauseDispatchProg_long_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ0 (by omega)]
    simp [hprep, hτ, σf, emitClauseCommitProg, Expr.eval]
  have hprog :
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ = σf := by
    rw [emitClauseProgram, eval_seq]
    simpa [hσ0] using hdispatch
  refine ⟨σf, hprog.symm, hwriterf, ?_, hfreshf, houterf⟩
  have henc : (encodeList encodeLiteral
      (l1 :: l2 :: l3 :: l4 :: rest)).length =
      (l1 :: l2 :: l3 :: l4 :: rest).length + 1 +
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length := by
    simp [encodeList, splitTailInputBits, List.length_append, encodeNat_length]
  calc
    σf cursorReg = (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1) +
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length := hcursorf
    _ = addr + (encodeList encodeLiteral
        (l1 :: l2 :: l3 :: l4 :: rest)).length := by rw [henc]; omega

def EmitClauseEndpoint
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr : ℕ)
    (pref : Bits) (c : List Literal) (σ τ : Store) : Prop :=
  τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound).eval σ ∧
  WriterState τ M curJ start
    (pref ++ encodeThreeClausesPayload (clauseToThree base c).1) ∧
  τ cursorReg = addr + (encodeList encodeLiteral c).length ∧
  τ freshReg = (clauseToThree base c).2 ∧ τ outerReg = outer - 1

def EmitClauseIterEndpoint
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr : ℕ)
    (pref : Bits) (c : List Literal) (rest : Bits) (σ τ : Store) : Prop :=
  ∃ τ₀, EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr pref c σ τ₀ ∧
    τ = (emitClauseResetProg lengthReg doneReg).eval τ₀ ∧
    BitsFrom τ (addr + (encodeList encodeLiteral c).length) rest ∧
    WriterState τ M curJ start
      (pref ++ encodeThreeClausesPayload (clauseToThree base c).1) ∧
    τ cursorReg = addr + (encodeList encodeLiteral c).length ∧
    τ freshReg = (clauseToThree base c).2 ∧
    τ outerReg = outer - 1 ∧ τ lengthReg = 0 ∧ τ doneReg = 0 ∧
    (∀ r, M + tmpJ < r → τ r = σ r)

lemma emitClauseEndpoint_reset
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr : ℕ)
    (pref : Bits) (c : List Literal) (rest : Bits) (σ τ₀ : Store)
    (hendpoint : EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr pref c σ τ₀)
    (hinput : BitsFrom τ₀ (addr + (encodeList encodeLiteral c).length) rest)
    (hframe : ∀ r, M + tmpJ < r → τ₀ r = σ r)
    (hinputAbove : M + tmpJ < addr)
    (htmpJ : curJ < tmpJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg) :
    EmitClauseIterEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr pref c rest σ
      ((emitClauseResetProg lengthReg doneReg).eval τ₀) := by
  rcases hendpoint with ⟨heval, hwriter, hcursor, hfresh, houter⟩
  have hstart : start < M + curJ := by
    have := hwriter.safe
    omega
  have hstartTmp : start < M + tmpJ := by omega
  have hlenBelow : lengthReg < start := hsafety.length_below
  have hdoneBelow : doneReg < start := hsafety.done_below
  have hlenNZ : lengthReg ≠ 0 := hsafety.length_nonzero
  have hdoneNZ : doneReg ≠ 0 := hsafety.done_nonzero
  have hne : lengthReg ≠ doneReg := by
    intro h
    exact hsafety.ne_of_pair (a := lengthReg) (b := doneReg) (by simp) h
  let τ := (emitClauseResetProg lengthReg doneReg).eval τ₀
  have hwriter' := emitClauseResetProg_writer M curJ start lengthReg doneReg
    (pref ++ encodeThreeClausesPayload (clauseToThree base c).1) τ₀ hwriter
    hlenBelow hdoneBelow hlenNZ hdoneNZ hne
  have hframeReset : ∀ r, M + tmpJ < r → τ r = τ₀ r := by
    intro r hr
    dsimp [τ]
    apply emitClauseResetProg_frame
    · intro h
      have : r < start := by simpa [h] using hlenBelow
      omega
    · intro h
      have : r < start := by simpa [h] using hdoneBelow
      omega
  have hframeResetAll : ∀ r, r ≠ lengthReg → r ≠ doneReg → τ r = τ₀ r := by
    intro r hrl hrd
    dsimp [τ]
    exact emitClauseResetProg_frame lengthReg doneReg τ₀ hrl hrd
  have hinput' : BitsFrom τ (addr + (encodeList encodeLiteral c).length) rest := by
    apply bitsFrom_of_eq_on (hb := hinput)
    intro i hi
    exact hframeReset (addr + (encodeList encodeLiteral c).length + i) (by omega)
  have hwriter' : WriterState τ M curJ start
      (pref ++ encodeThreeClausesPayload (clauseToThree base c).1) := by
    exact hwriter'
  have hcursor' : τ cursorReg = addr + (encodeList encodeLiteral c).length := by
    calc
      τ cursorReg = τ₀ cursorReg := by
        apply hframeResetAll
        · intro h'; exact hsafety.ne_of_pair (a := cursorReg) (b := lengthReg)
            (by simp) h'
        · intro h'; exact hsafety.ne_of_pair (a := cursorReg) (b := doneReg)
            (by simp) h'
      _ = addr + (encodeList encodeLiteral c).length := hcursor
  have hfresh' : τ freshReg = (clauseToThree base c).2 := by
    calc
      τ freshReg = τ₀ freshReg := by
        apply hframeResetAll
        · intro h'; exact hsafety.ne_of_pair (a := freshReg) (b := lengthReg)
            (by simp) h'
        · intro h'; exact hsafety.ne_of_pair (a := freshReg) (b := doneReg)
            (by simp) h'
      _ = _ := hfresh
  have houter' : τ outerReg = outer - 1 := by
    calc
      τ outerReg = τ₀ outerReg := by
        apply hframeResetAll
        · intro h'; exact hsafety.ne_of_pair (a := outerReg) (b := lengthReg)
            (by simp) h'
        · intro h'; exact hsafety.ne_of_pair (a := outerReg) (b := doneReg)
            (by simp) h'
      _ = _ := houter
  have hframe' : ∀ r, M + tmpJ < r → τ r = σ r := by
    intro r hr
    exact (hframeReset r hr).trans (hframe r hr)
  refine ⟨τ₀, ⟨heval, hwriter, hcursor, hfresh, houter⟩, rfl, hinput', hwriter',
    hcursor', hfresh', houter', ?_, ?_, hframe'⟩
  · rw [emitClauseResetProg_eval, writeReg_diff _ doneReg 0 lengthReg hne,
      writeReg_same]
  · rw [emitClauseResetProg_eval, writeReg_same]

lemma emitClauseEndpoint_iter_post_with_polarity
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base outer addr : ℕ)
    (pref : Bits) (c : List Literal) (rest : Bits) (σ τ₀ : Store)
    (hendpoint : EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr pref c σ τ₀)
    (hinput : BitsFrom τ₀ (addr + (encodeList encodeLiteral c).length) rest)
    (hframe : ∀ r, M + tmpJ < r → τ₀ r = σ r)
    (hpos : τ₀ posPolReg = 0) (hneg : τ₀ negPolReg = 1)
    (hinputAbove : M + tmpJ < addr) (htmpJ : curJ < tmpJ)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (hposLength : posPolReg ≠ lengthReg) (hposDone : posPolReg ≠ doneReg)
    (hnegLength : negPolReg ≠ lengthReg) (hnegDone : negPolReg ≠ doneReg) :
    ∃ τ, EmitClauseIterEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr pref c
      rest σ τ ∧ τ posPolReg = 0 ∧ τ negPolReg = 1 := by
  let τ := (emitClauseResetProg lengthReg doneReg).eval τ₀
  have hiter := emitClauseEndpoint_reset M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr pref c rest σ τ₀
    hendpoint hinput hframe hinputAbove htmpJ hsafety
  have hpos' : τ posPolReg = 0 := by
    calc
      τ posPolReg = τ₀ posPolReg := by
        simpa [τ] using
          (emitClauseResetProg_frame lengthReg doneReg τ₀ hposLength hposDone)
      _ = 0 := hpos
  have hneg' : τ negPolReg = 1 := by
    calc
      τ negPolReg = τ₀ negPolReg := by
        simpa [τ] using
          (emitClauseResetProg_frame lengthReg doneReg τ₀ hnegLength hnegDone)
      _ = 1 := hneg
  exact ⟨τ, hiter, hpos', hneg'⟩

lemma emitClauseProgram_long_eval_concrete
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (σ σ0 σprep : Store)
    (hσ0 : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ)
    (hlen0 : σ0 lengthReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (.seq (.assign carryPolReg (.const 1))
          (.seq (.assign carryValReg (.reg freshReg))
            (.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0)
    (hinputPrep : BitsFrom σprep
      (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hstart : start ≤ addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hwriter : WriterState σprep M curJ start pref)
    (hpos : σprep posPolReg = 0) (hfresh : σprep freshReg = base)
    (hremaining : σprep remainingReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hcursor : σprep cursorReg = addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (houterBelow : outerReg < start) (houterNonzero : outerReg ≠ 0)
    (houterDisjoint : outerReg ≠ freshReg ∧ outerReg ≠ cursorReg)
    (houterLong :
      (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        bound tailBound).eval σprep outerReg = outer)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
      M + curJ) :
    ∃ τ,
      EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound base outer addr pref
        (l1 :: l2 :: l3 :: l4 :: rest) σ τ := by
  obtain ⟨τ, hτ, hw, hc, hf, ho⟩ :=
    emitClauseProgram_long_eval_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 l3 l4 rest pref tail
      σ σ0 σprep hσ0 hlen0 hprep hinputPrep hcurJ htmpJ hinputAbove hstart hwriter hpos hfresh
      hremaining hcursor hsafety houterBelow houterNonzero houterDisjoint
      houterLong hbound1 hbound2 hboundTail hls hroom hcapacity
  exact ⟨τ, hτ, hw, hc, hf, ho⟩

lemma emitClauseProgram_nil_eval_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [] rest pref σ σ0)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base []).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral []).length ∧
      τ freshReg = base + 1 ∧ τ outerReg = outer - 1 := by
  have hbound : 1 ≤ bound := by simpa using hprep.bound
  exact emitClauseProgram_nil_eval M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base outer addr rest pref σ
    hprep.cur_j_pos hprep.tmp_j_pos hbound hprep.start_at_base hprep.initial_input
    hprep.initial_cursor hprep.initial_length hprep.initial_done hprep.initial_outer
    hprep.initial_fresh hprep.initial_pos hprep.initial_neg
    hprep.initial_writer hroom hprep.safety


end NPComplete.CookLevin

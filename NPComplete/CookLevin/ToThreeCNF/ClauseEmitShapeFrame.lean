module

public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitShapeEval

/-!
# Clause-emitter frame conditions

Clause dispatch must preserve the parsed input and unrelated store cells while
the selected shape writes to the output window. This module derives low- and
high-memory frame contracts from the shape-specific evaluation facts for use in
the outer emission proofs.
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
lemma emitClauseProgram_nil_frame_of_prep_dispatch
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [] rest pref σ σ0)
    (hσ0r : σ0 r = σ r)
    (hwriterFrame :
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0 r = σ0 r)
    (hfreshR : r ≠ freshReg) (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  let σ1 := (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0
  have hσ1 : σ1 r = σ0 r := by simpa [σ1] using hwriterFrame
  let σfresh := (emitClauseEmptyFreshProg freshReg).eval σ1
  have hfreshFrame : σfresh r = σ1 r := by
    dsimp [σfresh, emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ freshReg _ r hfreshR
  let σ2 := (emitClauseCommitProg outerReg).eval σfresh
  have hcommitFrame : σ2 r = σfresh r := by
    dsimp [σ2, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ outerReg _ r houterR
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 r = σ2 r := by
    rw [emitClauseDispatchProg_zero_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprep.length]
    simp [σ1, σfresh, σ2, emitClauseEmptyFreshProg, emitClauseCommitProg,
      eval_seq, eval_assign, Expr.eval]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hcommitFrame.trans (hfreshFrame.trans (hσ1.trans hσ0r))

lemma emitClauseProgram_nil_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [] rest pref σ σ0)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ) :
    ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr
  have hstartTmp : start < M + tmpJ := by
    have hs := hprep.writer.safe
    have hcurJ := hprep.cur_j_pos
    have htmpJ := hprep.tmp_j_pos
    omega
  have hreg : ∀ q, q ∈ [cursorReg, lengthReg, doneReg] → q < r := by
    intro q hq
    have hq' : q = cursorReg ∨ q = lengthReg ∨ q = doneReg := by simpa using hq
    rcases hq' with hq' | hq' | hq'
    · have hbelow := hprep.safety.cursor_below
      omega
    · have hbelow := hprep.safety.length_below
      omega
    · have hbelow := hprep.safety.done_below
      omega
  have hσ0r : σ0 r = σ r := by
    apply hprep.frame
    · intro h; have hh := hreg cursorReg (by simp); omega
    · intro h; have hh := hreg lengthReg (by simp); omega
    · intro h; have hh := hreg doneReg (by simp); omega
  have hwriterFrame :
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0 r = σ0 r := by
    exact writerAppendClauseEmptyProg_frame_high M curJ tmpJ start pref posPolReg negPolReg
      freshReg base σ0 hprep.cur_j_pos hprep.tmp_j_pos hprep.pos_value hprep.neg_value
      hprep.fresh_value hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below
      hprep.writer hroom hr
  apply emitClauseProgram_nil_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr rest pref σ σ0 r
    hprep hσ0r hwriterFrame
  · have hbelow := hprep.safety.fresh_below
    omega
  · have hbelow := hprep.safety.outer_below
    omega

lemma emitClauseProgram_nil_low_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [] rest pref σ σ0)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    (hr : r < start)
    (hcursorR : r ≠ cursorReg) (hlengthR : r ≠ lengthReg) (hdoneR : r ≠ doneReg)
    (hfreshR : r ≠ freshReg) (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hσ0r : σ0 r = σ r := hprep.frame r hcursorR hlengthR hdoneR
  have hwriterFrame := writerAppendClauseEmptyProg_frame M curJ tmpJ start pref
    posPolReg negPolReg freshReg base σ0 hprep.cur_j_pos hprep.tmp_j_pos hprep.pos_value hprep.neg_value
    hprep.fresh_value hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below
    hprep.writer hroom hr
  exact emitClauseProgram_nil_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr rest pref σ σ0 r
    hprep hσ0r hwriterFrame hfreshR houterR

lemma emitClauseProgram_one_eval_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l] rest pref σ σ0)
    (hbound : l.var + 1 ≤ bound)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l]).length ∧
      τ freshReg = base ∧ τ outerReg = outer - 1 := by
  have hlistBound : 2 ≤ bound := by simpa using hprep.bound
  exact emitClauseProgram_one_eval M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base outer addr l rest pref σ
    hprep.cur_j_pos hprep.tmp_j_pos hbound hlistBound hprep.start_at_base hprep.initial_input
    hprep.initial_cursor hprep.initial_length hprep.initial_done hprep.initial_outer
    hprep.initial_fresh hprep.initial_writer hroom hprep.safety

lemma emitClauseProgram_one_frame_of_prep_dispatch
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l] rest pref σ σ0)
    (hbound : l.var + 1 ≤ bound)
    (hσ0r : σ0 r = σ r)
    (hframeR : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r)
    (hwriterFrame :
      ∀ τ : Store, τ polReg = literalPolarity l → τ varReg = l.var →
        WriterState τ M curJ start pref →
        (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval τ r = τ r)
    (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hwriter0 : WriterState σ0 M curJ start pref := hprep.writer
  have hbits0 : BitsFrom σ0 (addr + 2) (encodeLiteral l ++ rest) := by
    simpa using hprep.input
  have hstart2 : start ≤ addr + 2 := by simpa using hprep.start_at_input
  obtain ⟨hcur1, hpol1, hvar1, hdone1, hframe1⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound
      (addr + 2) l rest σ0
      (hprep.safety.ne_of_pair (by simp)) (hprep.safety.ne_of_pair (by simp))
      (hprep.safety.ne_of_pair (by simp)) (hprep.safety.ne_of_pair (by simp))
      (hprep.safety.ne_of_pair (by simp)) (hprep.safety.ne_of_pair (by simp))
      (lt_of_lt_of_le hprep.safety.cursor_below hstart2)
      (lt_of_lt_of_le hprep.safety.pol_below hstart2)
      (lt_of_lt_of_le hprep.safety.var_below hstart2)
      (lt_of_lt_of_le hprep.safety.done_below hstart2) hbound hprep.cursor hbits0
  let σ1 := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0
  have hσ1pol : σ1 polReg = literalPolarity l := by
    cases l <;> simpa [σ1, literalPolarity] using hpol1
  have hσ1var : σ1 varReg = l.var := by simpa [σ1] using hvar1
  have hwriter1 : WriterState σ1 M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ0 σ1
      cursorReg polReg varReg doneReg hwriter0 hframe1
      hprep.safety.cursor_nonzero hprep.safety.pol_nonzero hprep.safety.var_nonzero
      hprep.safety.done_nonzero hprep.safety.cursor_below hprep.safety.pol_below
      hprep.safety.var_below hprep.safety.done_below
  have hσ1r : σ1 r = σ0 r := by
    apply hframeR σ1
    simpa [σ1] using hframe1
  have hwframe :
      (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1 r = σ1 r :=
    hwriterFrame σ1 hσ1pol hσ1var hwriter1
  let σ2 := (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1
  have hσ2r : σ2 r = σ1 r := by simpa [σ2] using hwframe
  have hcommit : (emitClauseCommitProg outerReg).eval σ2 r = σ2 r := by
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ outerReg _ r houterR
  let σ3 := (emitClauseCommitProg outerReg).eval σ2
  have hσ3r : σ3 r = σ2 r := by simpa [σ3] using hcommit
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 r = σ3 r := by
    rw [emitClauseDispatchProg_one_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprep.length]
    simp [σ1, σ2, σ3, emitClauseCommitProg, Expr.eval]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hσ3r.trans (hσ2r.trans (hσ1r.trans hσ0r))

lemma emitClauseProgram_one_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l] rest pref σ σ0)
    (hbound : l.var + 1 ≤ bound)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ) :
    ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr
  have hstartTmp : start < M + tmpJ := by
    have hs := hprep.writer.safe
    have hc := hprep.cur_j_pos
    have ht := hprep.tmp_j_pos
    omega
  have hreg : ∀ q, q ∈ [cursorReg, lengthReg, doneReg] → q < r := by
    intro q hq
    have hq' : q = cursorReg ∨ q = lengthReg ∨ q = doneReg := by simpa using hq
    rcases hq' with hq' | hq' | hq'
    · have hbelow := hprep.safety.cursor_below
      omega
    · have hbelow := hprep.safety.length_below
      omega
    · have hbelow := hprep.safety.done_below
      omega
  have hσ0r : σ0 r = σ r := by
    apply hprep.frame
    · intro h; have hh := hreg cursorReg (by simp); omega
    · intro h; have hh := hreg lengthReg (by simp); omega
    · intro h; have hh := hreg doneReg (by simp); omega
  have hframeR : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r (by have hbelow := hprep.safety.cursor_below; omega)
      (by have hbelow := hprep.safety.pol_below; omega)
      (by have hbelow := hprep.safety.var_below; omega)
      (by have hbelow := hprep.safety.done_below; omega)
  have hwriterFrame :
      ∀ τ : Store, τ polReg = literalPolarity l → τ varReg = l.var →
        WriterState τ M curJ start pref →
        (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval τ r = τ r := by
    intro τ hpol hvar hstate
    exact writerAppendClauseOneProg_frame_high M curJ tmpJ start pref polReg varReg
      (literalPolarity l) l.var τ hprep.cur_j_pos hprep.tmp_j_pos hpol hvar
      (by cases l <;> simp [literalPolarity])
      ⟨hprep.safety.pol_below, hprep.safety.var_below⟩ hstate hroom hr
  exact emitClauseProgram_one_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l rest pref σ σ0 r
    hprep hbound hσ0r hframeR hwriterFrame (by
      have hbelow := hprep.safety.outer_below
      omega)

lemma emitClauseProgram_one_low_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : Literal) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l] rest pref σ σ0)
    (hbound : l.var + 1 ≤ bound)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ)
    (hr : r < start)
    (hcursorR : r ≠ cursorReg) (hlengthR : r ≠ lengthReg)
    (hpolR : r ≠ polReg) (hvarR : r ≠ varReg)
    (hdoneR : r ≠ doneReg) (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hσ0r : σ0 r = σ r := hprep.frame r hcursorR hlengthR hdoneR
  have hframeR : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r hcursorR hpolR hvarR hdoneR
  have hwriterFrame :
      ∀ τ : Store, τ polReg = literalPolarity l → τ varReg = l.var →
        WriterState τ M curJ start pref →
        (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval τ r = τ r := by
    intro τ hpol hvar hstate
    exact writerAppendClauseOneProg_frame M curJ tmpJ start pref polReg varReg
      (literalPolarity l) l.var τ hprep.cur_j_pos hprep.tmp_j_pos hpol hvar
      (by cases l <;> simp [literalPolarity])
      ⟨hprep.safety.pol_below, hprep.safety.var_below⟩ hstate hroom hr
  exact emitClauseProgram_one_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l rest pref σ σ0 r
    hprep hbound hσ0r hframeR hwriterFrame houterR

lemma emitClauseProgram_two_eval_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l1, l2]
      rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l1, l2]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l1, l2]).length ∧
      τ freshReg = base ∧ τ outerReg = outer - 1 := by
  have hlistBound : 3 ≤ bound := by simpa using hprep.bound
  exact emitClauseProgram_two_eval M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base outer addr l1 l2 rest pref σ
    hprep.cur_j_pos hprep.tmp_j_pos hbound1 hbound2 hlistBound hprep.start_at_base
    hprep.initial_input hprep.initial_cursor hprep.initial_length hprep.initial_done
    hprep.initial_outer hprep.initial_fresh hprep.initial_writer hroom
    hprep.safety hpairBelow hpairNonzero hpairSafe

lemma writerAppendClauseTwoProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 pol1 val1 pol2 val2 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + 2 * val2 + 6 < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2).eval σ r = σ r := by
  simpa [writerAppendClauseTwoProg] using
    (writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
      p1 v1 p2 v2 p2 v2 pol1 val1 pol2 val2 pol2 val2 σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hp2 hv2 hpol1 hpol2 hpol2
      hlow1 hlow2 hlow2 hs (by omega) hr)

lemma writerAppendClauseThreeProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ)
    (pol1 val1 pol2 val2 pol3 val3 base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + 2 * base + 2 * val3 + 12 < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3
      posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + val2 + base + 6 < M + curJ := by
    omega
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2
    posPolReg freshReg).eval σ
  have hσ1state : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg : σ1 negPolReg = 1 := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
      hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlowNeg
    simpa [σ1] using hf.trans hneg
  have hσ1fresh : σ1 freshReg = base := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
      hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlowFresh
    simpa [σ1] using hf.trans hfresh
  have hσ1p3 : σ1 p3 = pol3 := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
      hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlow3.1
    simpa [σ1] using hf.trans hp3
  have hσ1v3 : σ1 v3 = val3 := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
      hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlow3.2
    simpa [σ1] using hf.trans hv3
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base).length +
      base + val3 + val3 + 6 < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
      encodeNat_length]
    omega
  have hsecond := writerAppendThreeRegsProg_frame_high M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base)
    negPolReg freshReg p3 v3 p3 v3 1 base pol3 val3 pol3 val3 σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1p3 hσ1v3 hσ1p3 hσ1v3
    (Or.inr rfl) hpol3 hpol3
    hlowFresh hlow3 hlow3 hσ1state hroom2 hr
  have hfirstHigh := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hr
  rw [writerAppendClauseThreeProg, eval_seq]
  exact hsecond.trans hfirstHigh

lemma emitClauseProgram_two_frame_of_prep_dispatch
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l1, l2]
      rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hσ0r : σ0 r = σ r)
    (hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r)
    (hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r)
    (hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      WriterState τ M curJ start pref →
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval τ r = τ r)
    (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hcursorBelow := hprep.safety.cursor_below
  have hlengthBelow := hprep.safety.length_below
  have hdoneBelow := hprep.safety.done_below
  have hpolBelow := hprep.safety.pol_below
  have hvarBelow := hprep.safety.var_below
  have houterBelow := hprep.safety.outer_below
  have hfreshBelow := hprep.safety.fresh_below
  have hstart3 : start ≤ addr + 3 := by simpa using hprep.start_at_input
  have hbits0 : BitsFrom σ0 (addr + 3) (encodeLiteral l1 ++ encodeLiteral l2 ++ rest) := by
    simpa [List.append_assoc] using hprep.input
  have hpairneq : ∀ {a b : ℕ},
      (a, b) ∈ registerPairs
        [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg] →
      True → a ≠ b := by
    intro a b hp _
    exact hpairSafe hp
  obtain ⟨σ1, σ2, hσ1eq, hσ2eq, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2,
      hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg polReg varReg pol2Reg var2Reg doneReg bound
      (addr + 3) l1 l2 rest σ0
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp))
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      hbound1 hbound2 hprep.cursor hbits0
  have hσ1state : WriterState σ1 M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ0 σ1
      cursorReg polReg varReg doneReg hprep.writer hframe1
      hprep.safety.cursor_nonzero hprep.safety.pol_nonzero hprep.safety.var_nonzero
      hprep.safety.done_nonzero hprep.safety.cursor_below hprep.safety.pol_below
      hprep.safety.var_below hprep.safety.done_below
  have hσ2state : WriterState σ2 M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ1 σ2
      cursorReg pol2Reg var2Reg doneReg hσ1state hframe2
      hprep.safety.cursor_nonzero hpairNonzero.1 hpairNonzero.2 hprep.safety.done_nonzero
      hprep.safety.cursor_below hpairBelow.1 hpairBelow.2 hprep.safety.done_below
  have hσ1r : σ1 r = σ0 r := by
    apply hframeR1 σ1
    exact hframe1
  have hσ2r : σ2 r = σ1 r := by
    apply hframeR2 σ1 σ2 hframe2
  have hσ2pol1 : σ2 polReg = literalPolarity l1 := by
    have hf := hframe2 polReg
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
    calc σ2 polReg = σ1 polReg := hf
      _ = literalPolarity l1 := by cases l1 <;> simpa [hσ1eq, literalPolarity] using hpol1
  have hσ2var1 : σ2 varReg = l1.var := by
    have hf := hframe2 varReg
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
      (hpairneq (by simp) (by simp)) (hpairneq (by simp) (by simp))
    calc σ2 varReg = σ1 varReg := hf
      _ = l1.var := by simpa [hσ1eq] using hvar1
  have hσ2pol2 : σ2 pol2Reg = literalPolarity l2 := by
    cases l2 <;> simpa [hσ2eq, literalPolarity] using hpol2
  have hσ2var2 : σ2 var2Reg = l2.var := by simpa [hσ2eq] using hvar2
  have hwframe :
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval σ2 r = σ2 r :=
    hwriterFrame σ2 hσ2pol1 hσ2var1 hσ2pol2 hσ2var2 hσ2state
  let σ3 := (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval σ2
  have hσ3r : σ3 r = σ2 r := by simpa [σ3] using hwframe
  have hcommit : (emitClauseCommitProg outerReg).eval σ3 r = σ3 r := by
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ outerReg _ r houterR
  let σ4 := (emitClauseCommitProg outerReg).eval σ3
  have hσ4r : σ4 r = σ3 r := by simpa [σ4] using hcommit
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 r = σ4 r := by
    rw [emitClauseDispatchProg_two_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprep.length]
    simp [hσ1eq, hσ2eq, σ3, σ4, emitClauseCommitProg, Expr.eval]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hσ4r.trans (hσ3r.trans (hσ2r.trans (hσ1r.trans hσ0r)))

lemma emitClauseProgram_two_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ) :
    ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr
  have hstartTmp : start < M + tmpJ := by
    have hs := hprep.writer.safe
    have hc := hprep.cur_j_pos
    have ht := hprep.tmp_j_pos
    omega
  have hcursorBelow := hprep.safety.cursor_below
  have hlengthBelow := hprep.safety.length_below
  have hdoneBelow := hprep.safety.done_below
  have hpolBelow := hprep.safety.pol_below
  have hvarBelow := hprep.safety.var_below
  have houterBelow := hprep.safety.outer_below
  have hfreshBelow := hprep.safety.fresh_below
  have hpol2Below := hpairBelow.1
  have hvar2Below := hpairBelow.2
  have hσ0r : σ0 r = σ r := hprep.frame r (by omega) (by omega) (by omega)
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      WriterState τ M curJ start pref →
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hstate
    exact writerAppendClauseTwoProg_frame_high M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var τ hprep.cur_j_pos hprep.tmp_j_pos hpol1 hvar1 hpol2 hvar2
      (by cases l1 <;> simp [literalPolarity]) (by cases l2 <;> simp [literalPolarity])
      hprep.safety.var_below hpairBelow hstate (by omega) hr
  exact emitClauseProgram_two_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 rest pref σ σ0 r
    hprep hbound1 hbound2 hpairBelow hpairNonzero hpairSafe hσ0r hframeR1 hframeR2 hwriterFrame
    (by omega)

lemma emitClauseProgram_two_low_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : Literal) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ)
    (hr : r < start)
    (hcursorR : r ≠ cursorReg) (hlengthR : r ≠ lengthReg)
    (hpolR : r ≠ polReg) (hvarR : r ≠ varReg) (hdoneR : r ≠ doneReg)
    (hpol2R : r ≠ pol2Reg) (hvar2R : r ≠ var2Reg) (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hσ0r : σ0 r = σ r := hprep.frame r hcursorR hlengthR hdoneR
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r hcursorR hpolR hvarR hdoneR
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r hcursorR hpol2R hvar2R hdoneR
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      WriterState τ M curJ start pref →
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hstate
    exact writerAppendClauseTwoProg_frame M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var τ hprep.cur_j_pos hprep.tmp_j_pos hpol1 hvar1 hpol2 hvar2
      (by cases l1 <;> simp [literalPolarity]) (by cases l2 <;> simp [literalPolarity])
      hprep.safety.var_below hpairBelow hstate hroom hr
  exact emitClauseProgram_two_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 rest pref σ σ0 r
    hprep hbound1 hbound2 hpairBelow hpairNonzero hpairSafe hσ0r hframeR1 hframeR2 hwriterFrame
    houterR

lemma emitClauseProgram_three_eval_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2, l3] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ) :
    ∃ τ,
      τ = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1) ∧
      τ cursorReg = addr + (encodeList encodeLiteral [l1, l2, l3]).length ∧
      τ freshReg = (clauseToThree base [l1, l2, l3]).2 ∧ τ outerReg = outer - 1 := by
  have hlistBound : 4 ≤ bound := by simpa using hprep.bound
  exact emitClauseProgram_three_eval M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base outer addr l1 l2 l3 rest pref σ
    hprep.cur_j_pos hprep.tmp_j_pos hbound1 hbound2 hbound3 hlistBound hprep.start_at_base
    hprep.initial_input hprep.initial_cursor hprep.initial_length hprep.initial_done
    hprep.initial_outer hprep.initial_fresh hprep.initial_pos hprep.initial_neg
    hprep.initial_writer hroom hprep.safety htripleBelow htripleNonzero htripleSafe

/-- A register outside the three decoded literals' registers and the cursor and done registers
is untouched by the three literal decoders, whenever each decoder preserves it. -/
lemma emitClauseProgram_three_frame_of_prep_dispatch_decode_r
    (start cursorReg polReg varReg doneReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      freshReg outerReg bound addr r : ℕ)
    (l1 l2 l3 : Literal) (rest : Bits) (σ0 : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound) (hstart : start ≤ addr)
    (hcursor : σ0 cursorReg = addr + 4)
    (hbits : BitsFrom σ0 (addr + 4)
      (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest))
    (hbelow : cursorReg < start ∧ polReg < start ∧ varReg < start ∧ doneReg < start)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧ pol3Reg < start ∧ var3Reg < start)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r)
    (hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r)
    (hframeR3 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol3Reg → q ≠ var3Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r) :
    (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval
        ((decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval
          ((decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0)) r =
      σ0 r := by
  obtain ⟨hcB, hpB, hvB, hdB⟩ := hbelow
  obtain ⟨h2B, h3B, h4B, h5B⟩ := htripleBelow
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
  obtain ⟨_, _, _, _, hframe3⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol3Reg var3Reg doneReg bound
      (addr + 4 + l1.var + 2 + l2.var + 2) l3 rest σ2
      (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp)) (hne _ _ (by simp))
      (hne _ _ (by simp)) (hne _ _ (by simp))
      (by omega) (by omega) (by omega) (by omega) hbound3
      (by simpa [hσ2] using hcur2) htail2
  rw [← hσ1, ← hσ2]
  exact (hframeR3 σ2 _ hframe3).trans ((hframeR2 σ1 σ2 hframe2).trans (hframeR1 σ1 hframe1))

/-- The writer, fresh-counter and outer-counter updates after the literals are decoded leave a
register untouched when the writer leaves it untouched and it is neither fresh nor outer. -/
lemma emitClauseProgram_three_frame_of_prep_dispatch_write_commit_r
    (curJ tmpJ polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      freshReg outerReg r : ℕ) (σ3 : Store)
    (hwframe : (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
      pol3Reg var3Reg posPolReg negPolReg freshReg).eval σ3 r = σ3 r)
    (hfreshR : r ≠ freshReg) (houterR : r ≠ outerReg) :
    (emitClauseCommitProg outerReg).eval ((emitClauseEmptyFreshProg freshReg).eval
      ((writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval σ3)) r = σ3 r := by
  dsimp [emitClauseCommitProg, emitClauseEmptyFreshProg]
  simp only [eval_assign, Expr.eval]
  rw [writeReg_diff _ outerReg _ r houterR, writeReg_diff _ freshReg _ r hfreshR]
  exact hwframe

lemma emitClauseProgram_three_frame_of_prep_dispatch
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest pref : Bits) (σ σ0 : Store) (r : ℕ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2, l3] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hσ0r : σ0 r = σ r)
    (hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r)
    (hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r)
    (hframeR3 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol3Reg → q ≠ var3Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r)
    (hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      τ pol3Reg = literalPolarity l3 → τ var3Reg = l3.var →
      τ posPolReg = 0 → τ negPolReg = 1 → τ freshReg = base →
      WriterState τ M curJ start pref →
      (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval τ r = τ r)
    (hfreshR : r ≠ freshReg) (houterR : r ≠ outerReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hstartAddr : start ≤ addr := hprep.start_at_base
  have hbits0 : BitsFrom σ0 (addr + 4)
      (encodeLiteral l1 ++ encodeLiteral l2 ++ encodeLiteral l3 ++ rest) := by
    simpa [List.append_assoc, Nat.add_assoc] using hprep.input
  have hbelow : cursorReg < start ∧ polReg < start ∧ varReg < start ∧ doneReg < start :=
    ⟨hprep.safety.cursor_below, hprep.safety.pol_below, hprep.safety.var_below,
      hprep.safety.done_below⟩
  obtain ⟨σ3, hσ3, hpol1, hvar1, hpol2, hvar2, hpol3, hvar3, hpos3, hneg3, hfresh3, _,
      _, hw3⟩ :=
    emitClauseProgram_three_eval_decode_literals M curJ start cursorReg polReg varReg doneReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg bound base outer
      addr l1 l2 l3 rest pref σ0 hbound1 hbound2 hbound3 hstartAddr hprep.cursor hbits0
      hprep.writer hprep.outer_value hprep.fresh_value hprep.pos_value hprep.neg_value hbelow
      ⟨hprep.safety.cursor_nonzero, hprep.safety.pol_nonzero, hprep.safety.var_nonzero,
        hprep.safety.done_nonzero⟩
      htripleBelow htripleNonzero htripleSafe
  have hσ3r : σ3 r = σ0 r := by
    rw [hσ3]
    exact emitClauseProgram_three_frame_of_prep_dispatch_decode_r start cursorReg polReg varReg
      doneReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg bound addr r
      l1 l2 l3 rest σ0 hbound1 hbound2 hbound3 hstartAddr hprep.cursor hbits0 hbelow
      htripleBelow htripleSafe hframeR1 hframeR2 hframeR3
  have hcommit := emitClauseProgram_three_frame_of_prep_dispatch_write_commit_r curJ tmpJ
    polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg outerReg r σ3
    (hwriterFrame σ3 hpol1 hvar1 hpol2 hvar2 hpol3 hvar3 hpos3 hneg3 hfresh3 hw3)
    hfreshR houterR
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm,
    emitClauseDispatchProg_three_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ0 hprep.length]
  simp only [eval_seq]
  rw [← hσ3]
  exact hcommit.trans (hσ3r.trans hσ0r)

lemma emitClauseProgram_three_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2, l3] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ) :
    ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr
  have hstartTmp : start < M + tmpJ := by
    have hs := hprep.writer.safe
    have hc := hprep.cur_j_pos
    have ht := hprep.tmp_j_pos
    omega
  have hcursorBelow := hprep.safety.cursor_below
  have hlengthBelow := hprep.safety.length_below
  have hdoneBelow := hprep.safety.done_below
  have hpolBelow := hprep.safety.pol_below
  have hvarBelow := hprep.safety.var_below
  have houterBelow := hprep.safety.outer_below
  have hfreshBelow := hprep.safety.fresh_below
  have hpol2Below := htripleBelow.1
  have hvar2Below := htripleBelow.2.1
  have hpol3Below := htripleBelow.2.2.1
  have hvar3Below := htripleBelow.2.2.2
  have hσ0r : σ0 r = σ r := hprep.frame r (by omega) (by omega) (by omega)
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hframeR3 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol3Reg → q ≠ var3Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      τ pol3Reg = literalPolarity l3 → τ var3Reg = l3.var →
      τ posPolReg = 0 → τ negPolReg = 1 → τ freshReg = base →
      WriterState τ M curJ start pref →
      (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hpol3 hvar3 hpos hneg hfresh hstate
    exact writerAppendClauseThreeProg_frame_high M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var
      (literalPolarity l3) l3.var base τ hprep.cur_j_pos hprep.tmp_j_pos
      hpol1 hvar1 hpol2 hvar2 hpol3 hvar3
      (by cases l1 <;> simp [literalPolarity])
      (by cases l2 <;> simp [literalPolarity])
      (by cases l3 <;> simp [literalPolarity]) hpos hneg hfresh
      hprep.safety.var_below
      ⟨htripleBelow.1, htripleBelow.2.1⟩
      ⟨htripleBelow.2.2.1, htripleBelow.2.2.2⟩
      hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below hstate
      hroom hr
  exact emitClauseProgram_three_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 l3 rest pref
    σ σ0 r hprep hbound1 hbound2 hbound3 htripleBelow htripleNonzero htripleSafe hσ0r
    hframeR1 hframeR2 hframeR3 hwriterFrame
    (by have hbelow := hprep.safety.fresh_below; omega)
    (by have hbelow := hprep.safety.outer_below; omega)

lemma emitClauseProgram_three_low_frame_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : Literal) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2, l3] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ)
    (r : ℕ) (hr : r < start)
    (hcursorR : r ≠ cursorReg) (hlengthR : r ≠ lengthReg)
    (hpolR : r ≠ polReg) (hvarR : r ≠ varReg) (hdoneR : r ≠ doneReg)
    (hpol2R : r ≠ pol2Reg) (hvar2R : r ≠ var2Reg)
    (hpol3R : r ≠ pol3Reg) (hvar3R : r ≠ var3Reg)
    (houterR : r ≠ outerReg) (hfreshR : r ≠ freshReg) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ r = σ r := by
  have hσ0r : σ0 r = σ r := hprep.frame r hcursorR hlengthR hdoneR
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r hcursorR hpolR hvarR hdoneR
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r hcursorR hpol2R hvar2R hdoneR
  have hframeR3 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol3Reg → q ≠ var3Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r hcursorR hpol3R hvar3R hdoneR
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      τ pol3Reg = literalPolarity l3 → τ var3Reg = l3.var →
      τ posPolReg = 0 → τ negPolReg = 1 → τ freshReg = base →
      WriterState τ M curJ start pref →
      (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hpol3 hvar3 hpos hneg hfresh hstate
    exact writerAppendClauseThreeProg_frame M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var
      (literalPolarity l3) l3.var base τ hprep.cur_j_pos hprep.tmp_j_pos
      hpol1 hvar1 hpol2 hvar2 hpol3 hvar3
      (by cases l1 <;> simp [literalPolarity])
      (by cases l2 <;> simp [literalPolarity])
      (by cases l3 <;> simp [literalPolarity]) hpos hneg hfresh
      hprep.safety.var_below
      ⟨htripleBelow.1, htripleBelow.2.1⟩
      ⟨htripleBelow.2.2.1, htripleBelow.2.2.2⟩
      hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below hstate
      hroom hr
  exact emitClauseProgram_three_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 l3 rest pref
    σ σ0 r hprep hbound1 hbound2 hbound3 htripleBelow htripleNonzero htripleSafe hσ0r
    hframeR1 hframeR2 hframeR3 hwriterFrame hfreshR houterR

end NPComplete.CookLevin

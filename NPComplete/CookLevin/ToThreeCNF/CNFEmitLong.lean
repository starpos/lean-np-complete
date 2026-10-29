module

public import NPComplete.CookLevin.ToThreeCNF.CNFEmitStep

/-!
# Long-clause emission step

A long clause is emitted through a split-tail loop rather than one writer call,
so its end state must connect back to the outer clause relation. This module
composes the branch's transition and frame facts while preserving the input and
writer data needed by the next clause.
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
/-- The four register assignments of the long-branch preparation only change
their own targets. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_frame
    {remainingReg lengthReg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (σ0 σprep : Store)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    ∀ r, r ≠ remainingReg → r ≠ carryPolReg → r ≠ carryValReg → r ≠ posPolReg →
      σprep r = σ0 r := by
  intro r hr hcp hcv hpp
  subst hprep
  simp [eval_seq, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hr,
    writeReg_diff _ _ _ _ hcp, writeReg_diff _ _ _ _ hcv,
    writeReg_diff _ _ _ _ hpp]

/-- Preparation preserves the cursor, outer, negation-polarity, and fresh registers. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_untouched
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (σ0 σprep : Store)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    σprep cursorReg = σ0 cursorReg ∧ σprep outerReg = σ0 outerReg ∧
      σprep negPolReg = σ0 negPolReg ∧ σprep freshReg = σ0 freshReg := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn
  have hf := cnfEmitRel_long_step_of_iter_post_concrete_prep_frame σ0 σprep hprep
  refine ⟨hf _ ?_ ?_ ?_ ?_, hf _ ?_ ?_ ?_ ?_, hf _ ?_ ?_ ?_ ?_, hf _ ?_ ?_ ?_ ?_⟩ <;> aesop

/-- The preparation program changes nothing at or above `start`. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_high_frame
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (σ0 σprep : Store)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    ∀ r, start ≤ r → σprep r = σ0 r := by
  intro r hr
  have h1 := hs.below remainingReg (by simp [longClauseRegisterList])
  have h2 := hs.below carryPolReg (by simp [longClauseRegisterList])
  have h3 := hs.below carryValReg (by simp [longClauseRegisterList])
  have h4 := hs.below posPolReg (by simp [longClauseRegisterList])
  exact cnfEmitRel_long_step_of_iter_post_concrete_prep_frame σ0 σprep hprep r
    (by omega) (by omega) (by omega) (by omega)

/-- The preparation program leaves an input window above `start` intact. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_input
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (σ0 σprep : Store) {a : ℕ} {bits : Bits} (hb : BitsFrom σ0 a bits) (hstart : start ≤ a)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    BitsFrom σprep a bits := by
  apply bitsFrom_of_eq_on (hb := hb)
  intro i _
  exact cnfEmitRel_long_step_of_iter_post_concrete_prep_high_frame hs σ0 σprep hprep
    (a + i) (by omega)

/-- Values of the four registers written by the preparation program. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_values
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (σ0 σprep : Store) (base n : ℕ)
    (hlen : σ0 lengthReg = n) (hfresh : σ0 freshReg = base)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    σprep remainingReg = n ∧ σprep carryPolReg = 1 ∧ σprep carryValReg = base ∧
      σprep posPolReg = 0 := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn
  subst hprep
  exact cnf_emit_long_prep_prog_values lengthReg remainingReg carryPolReg carryValReg
    posPolReg freshReg σ0 base n hlen hfresh
    (by aesop) (by aesop) (by aesop) (by aesop) (by aesop) (by aesop) (by aesop) (by aesop)

/-- The writer invariant survives the preparation program. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_prep_writer
    {M curJ start : ℕ} {pref : Bits}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg lengthReg : ℕ}
    (σ0 σprep : Store)
    (hw : WriterState σ0 M curJ start pref)
    (hsafe : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hposNonzero : posPolReg ≠ 0)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    WriterState σprep M curJ start pref := by
  subst hprep
  simp only [eval_seq, eval_assign, Expr.eval, NPComplete.BoundedWhile.eval_skip]
  refine writerState_assign_value M curJ start pref posPolReg 0 _ ?_
    hsafe.writer_below.2.2.1 hposNonzero
  refine writerState_assign_value M curJ start pref carryValReg _ _ ?_
    hsafe.writer_below.2.1 hsafe.writer_nonzero.1
  refine writerState_assign_value M curJ start pref carryPolReg 1 _ ?_
    hsafe.writer_below.1 hsafe.carry_pol_nonzero
  exact writerState_assign_value M curJ start pref remainingReg _ _ hw
    hsafe.writer_below.2.2.2.2 hsafe.remaining_nonzero

/-- Running the split-tail program on the prepared state leaves the outer and
negative-polarity registers untouched, zeroes the positive polarity, and keeps
everything above the temporary window. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_split_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (pref tail : Bits) (addr : ℕ)
    (σprep : Store)
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: litRest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: litRest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base)
        (l3 :: l4 :: litRest)).length + 2 < M + curJ)
    (hinput : BitsFrom σprep addr (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: litRest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σprep M curJ start pref)
    (hpos : σprep posPolReg = 0) (hfresh : σprep freshReg = base)
    (hremaining : σprep remainingReg = (l1 :: l2 :: l3 :: l4 :: litRest).length)
    (hcursor : σprep cursorReg = addr) :
    let τ := (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound).eval σprep
    τ outerReg = σprep outerReg ∧ τ negPolReg = σprep negPolReg ∧ τ posPolReg = 0 ∧
      ∀ r, M + tmpJ < r → τ r = σprep r := by
  have hsafe := hs.to_split_tail_safety
  have hoB : outerReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hnB : negPolReg < start := hs.below _ (by simp [longClauseRegisterList])
  obtain ⟨τo, hτo, ho⟩ := splitTailEmitLongClauseProg_eval_end_to_end_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound base
    l1 l2 l3 l4 litRest pref tail addr σprep hbound1 hbound2 hboundTail hls hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafe
    hoB hs.outer_not_mem_splitTailEmitStepWriteSet
  obtain ⟨τn, hτn, hn⟩ := splitTailEmitLongClauseProg_eval_end_to_end_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound base
    l1 l2 l3 l4 litRest pref tail addr σprep hbound1 hbound2 hboundTail hls hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafe
    hnB hs.neg_pol_not_mem_splitTailEmitStepWriteSet
  obtain ⟨τ, _, _, _, _, _, hτ, hdone, -⟩ := splitTailEmitLongClauseProg_eval_end_to_end_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound base
    l1 l2 l3 l4 litRest pref tail addr σprep hbound1 hbound2 hboundTail hls hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafe
  subst hτo hτn hτ
  exact ⟨ho, hn, hdone.pos, hdone.high_frame⟩

/-- The decode step only changes the cursor, length and done registers, all of
which lie below `start`. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_decode_high_frame
    {M tmpJ start cursorReg lengthReg doneReg : ℕ} {σ σ0 : Store}
    (hframe : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg → σ0 r = σ r)
    (hstart : start < M + tmpJ)
    (hc : cursorReg < start) (hl : lengthReg < start) (hd : doneReg < start) :
    ∀ r, M + tmpJ < r → σ0 r = σ r := by
  intro r hr
  exact hframe r (by omega) (by omega) (by omega)

/-- A clause counter decrement only changes the outer register. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_commit_apply
    (outerReg r : ℕ) (σ : Store) (h : r ≠ outerReg) :
    (emitClauseCommitProg outerReg).eval σ r = σ r := by
  simp [emitClauseCommitProg, eval_assign, Expr.eval, writeReg_diff _ _ _ _ h]

/-- On a long clause the whole clause program is preparation, split-tail, then
the counter decrement. -/
lemma cnfEmitRel_long_step_of_iter_post_concrete_program_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ) (σ σ0 σprep : Store)
    (hσ0 : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ)
    (hlen : 4 ≤ σ0 lengthReg)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0) :
    (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ =
    (emitClauseCommitProg outerReg).eval
      ((splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg bound tailBound).eval σprep) := by
  rw [emitClauseProgram, eval_seq, ← hσ0,
    emitClauseDispatchProg_long_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ0 hlen]
  simp [hprep, eval_seq, eval_assign, Expr.eval]

lemma cnfEmitRel_long_step_of_iter_post_concrete
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (restClauses : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base)
        (l3 :: l4 :: litRest)).length + 2 < M + curJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses) tail pref addr σ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) restClauses tail pref addr σ τ := by
  obtain ⟨σ0, hprepState⟩ := cnfEmitRel_long_prepState M curJ tmpJ start cursorReg polReg
    varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest
    restClauses tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨σprep, hprep⟩ : ∃ σprep : Store, σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0 := ⟨_, rfl⟩
  have hs := hrel.long_safety
  have hsafe := hs.to_split_tail_safety
  have hstart : start < M + tmpJ := by
    have := hrel.capacity
    omega
  obtain ⟨hcurU, houtU, hnegU, hfreshU⟩ :=
    cnfEmitRel_long_step_of_iter_post_concrete_prep_untouched hs σ0 σprep hprep
  obtain ⟨hremaining, hcarryPol, hcarryVal, hpos⟩ :=
    cnfEmitRel_long_step_of_iter_post_concrete_prep_values hs σ0 σprep base _
      hprepState.length hprepState.fresh_value hprep
  have hinputPrep : BitsFrom σprep
      (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: litRest)
        ((restClauses.map encodeClause).flatten ++ tail)) :=
    cnfEmitRel_long_step_of_iter_post_concrete_prep_input hs σ0 σprep hprepState.input
      hprepState.start_at_input hprep
  have hwriterPrep := cnfEmitRel_long_step_of_iter_post_concrete_prep_writer σ0 σprep
    hprepState.writer hsafe hrel.safety.pos_nonzero hprep
  have houterPrep : σprep outerReg =
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length :=
    houtU.trans hprepState.outer_value
  have hcursorPrep : σprep cursorReg = addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1 :=
    hcurU.trans hprepState.cursor
  have hfreshPrep : σprep freshReg = base := hfreshU.trans hprepState.fresh_value
  have hnegPrep : σprep negPolReg = σ negPolReg :=
    hnegU.trans (hprepState.frame negPolReg
      (hrel.safety.ne_of_pair (a := negPolReg) (b := cursorReg) (by simp [clauseEmitPairs]))
      (hrel.safety.ne_of_pair (a := negPolReg) (b := lengthReg) (by simp [clauseEmitPairs]))
      (hrel.safety.ne_of_pair (a := negPolReg) (b := doneReg) (by simp [clauseEmitPairs])))
  have houterBelow : outerReg < start := hs.below _ (by simp [longClauseRegisterList])
  have houterNonzero : outerReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have houterFresh : outerReg ≠ freshReg :=
    hrel.safety.ne_of_pair (a := outerReg) (b := freshReg) (by simp [clauseEmitPairs])
  have houterCursor : outerReg ≠ cursorReg :=
    hrel.safety.ne_of_pair (a := outerReg) (b := cursorReg) (by simp [clauseEmitPairs])
  have hnegOuter : negPolReg ≠ outerReg :=
    hrel.safety.ne_of_pair (a := negPolReg) (b := outerReg) (by simp [clauseEmitPairs])
  have hposOuter : posPolReg ≠ outerReg :=
    hrel.safety.ne_of_pair (a := posPolReg) (b := outerReg) (by simp [clauseEmitPairs])
  have hbound1 : l1.var + 1 ≤ bound :=
    hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ bound :=
    hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l2 (by simp)
  have hboundTail : ∀ l ∈ l3 :: l4 :: litRest, l.var + 1 ≤ bound := fun l hl =>
    hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l
      (by simp [hl])
  have hls : (l3 :: l4 :: litRest).length ≤ tailBound := by
    have h := hrel.tail_bound_ok (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp)
    simp only [List.length_cons] at h ⊢
    omega
  obtain ⟨houtS, hnegS, hposS, hhighS⟩ :=
    cnfEmitRel_long_step_of_iter_post_concrete_split_frame M curJ tmpJ start cursorReg polReg
      varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest pref
      ((restClauses.map encodeClause).flatten ++ tail)
      (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) σprep hs hbound1 hbound2
      hboundTail hls hroom hcapacity hinputPrep hcurJ htmpJ hprepState.input_above
      hprepState.start_at_input hwriterPrep hpos hfreshPrep hremaining hcursorPrep
  have hdecodeFrame := cnfEmitRel_long_step_of_iter_post_concrete_decode_high_frame
    hprepState.frame hstart hrel.safety.cursor_below hrel.safety.length_below
    hrel.safety.done_below
  have hprogEq := cnfEmitRel_long_step_of_iter_post_concrete_program_eval curJ tmpJ cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg
    negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound σ σ0 σprep
    hprepState.decoded
    (by have h := hprepState.length; simp only [List.length_cons] at h; omega) hprep
  have hlongFrame : ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg
        outerReg bound tailBound).eval σ r = σ r := by
    intro r hr
    rw [hprogEq, cnfEmitRel_long_step_of_iter_post_concrete_commit_apply _ _ _ (by omega),
      hhighS r hr,
      cnfEmitRel_long_step_of_iter_post_concrete_prep_high_frame hs σ0 σprep hprep r (by omega)]
    exact hdecodeFrame r hr
  refine cnfEmitRel_long_step_of_iter_post
    M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound
    base l1 l2 l3 l4 litRest restClauses tail pref addr σ σ0 σprep hcurJ htmpJ hprepState.decoded
    hprepState.length hprep hinputPrep hwriterPrep
    hprepState.input_above hprepState.start_at_input hpos
    hfreshPrep hremaining hcursorPrep hsafe houterBelow
    houterNonzero ⟨houterFresh, houterCursor⟩ (houtS.trans houterPrep) hlongFrame ?_ ?_ hrel
    hbound1 hbound2 hboundTail hls hroom hcapacity
  · rw [hprogEq, cnfEmitRel_long_step_of_iter_post_concrete_commit_apply _ _ _ hnegOuter]
    exact hnegS.trans hnegPrep
  · rw [hprogEq, cnfEmitRel_long_step_of_iter_post_concrete_commit_apply _ _ _ hposOuter]
    exact hposS

/-! One outer-loop transition, normalized over all clause shapes.  In the long
    branch, the split-tail workspace bounds are derived from the relation's
    capacity for the current remaining payload; register noncollision facts for
    short branches are projections of the same sound `LongClauseRegisterSafety`.
-/


end NPComplete.CookLevin

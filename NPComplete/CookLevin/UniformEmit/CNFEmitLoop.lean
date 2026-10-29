module

public import NPComplete.CookLevin.UniformEmit.CNFEmitHead

/-!
# Split-tail emission loop

After split-tail preparation, the loop must implement the relation step while leaving unrelated
registers unchanged. This module proves iteration evaluation and frame properties so dispatch can
compose the long-clause case with the other clause paths.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral encodeThreeClause)


lemma emit_clause_long_prep_writer
    (M curJ start remainingReg carryPolReg carryValReg posPolReg lengthReg freshReg : ℕ)
    (pref : Bits) (σ : Store)
    {cursorReg polReg varReg doneReg pol2Reg var2Reg pol3Reg var3Reg : ℕ}
    (hs : WriterState σ M curJ start pref)
    (hsafe : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hpos0 : posPolReg ≠ 0) :
    WriterState
      ((Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ)
      M curJ start pref := by
  have hw1 := writerState_assign_value M curJ start pref remainingReg (σ lengthReg) σ hs
    hsafe.writer_below.2.2.2.2 hsafe.remaining_nonzero
  have hw2 := writerState_assign_value M curJ start pref carryPolReg 1
    (writeReg σ remainingReg (σ lengthReg)) hw1 hsafe.writer_below.1 hsafe.carry_pol_nonzero
  have hw3 := writerState_assign_value M curJ start pref carryValReg
    ((writeReg (writeReg σ remainingReg (σ lengthReg)) carryPolReg 1) freshReg)
    (writeReg (writeReg σ remainingReg (σ lengthReg)) carryPolReg 1)
    hw2 hsafe.writer_below.2.1 hsafe.writer_nonzero.1
  have hw4 := writerState_assign_value M curJ start pref posPolReg 0
    (writeReg (writeReg (writeReg σ remainingReg (σ lengthReg)) carryPolReg 1)
      carryValReg ((writeReg (writeReg σ remainingReg (σ lengthReg)) carryPolReg 1) freshReg))
    hw3 hsafe.writer_below.2.2.1 hpos0
  simpa [eval_seq, eval_assign, eval_skip, Expr.eval] using hw4

lemma emit_clause_long_prep_frame
    (lengthReg remainingReg carryPolReg carryValReg posPolReg freshReg r : ℕ) (σ : Store)
    (hr : r ≠ remainingReg) (hcp : r ≠ carryPolReg)
    (hcv : r ≠ carryValReg) (hpp : r ≠ posPolReg) :
    ((Program.seq (.assign remainingReg (.reg lengthReg))
      (Program.seq (.assign carryPolReg (.const 1))
        (Program.seq (.assign carryValReg (.reg freshReg))
          (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ) r = σ r := by
  simp [eval_seq, eval_assign, eval_skip, Expr.eval, writeReg_diff _ remainingReg _ r hr,
    writeReg_diff _ carryPolReg _ r hcp, writeReg_diff _ carryValReg _ r hcv,
    writeReg_diff _ posPolReg _ r hpp]

lemma emitClauseIterProgramAt_eval_of_rel_nil
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ :=
  emitClauseIterProgramAt_eq_of curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ
    (emitClauseProgramAt_eval_of_rel_nil M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg bound tailBound base cs tail pref addr σ
      hcurJ htmpJ hrel hb)

lemma emitClauseIterProgramAt_eval_of_rel_one
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ :=
  emitClauseIterProgramAt_eq_of curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ
    (emitClauseProgramAt_eval_of_rel_one M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg bound tailBound base l cs tail pref addr σ
      hcurJ htmpJ hrel hb hok)

lemma emitClauseIterProgramAt_eval_of_rel_two
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ :=
  emitClauseIterProgramAt_eq_of curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ
    (emitClauseProgramAt_eval_of_rel_two M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 cs tail pref addr σ
      hcurJ htmpJ hrel hb hok)

lemma emitClauseIterProgramAt_eval_of_rel_three
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ :=
  emitClauseIterProgramAt_eq_of curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ
    (emitClauseProgramAt_eval_of_rel_three M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 cs tail pref addr σ
      hcurJ htmpJ hrel hb hok)

/-- Running the long-clause preparation assignments on the decoded store keeps the writer and the
input, sets the split-tail registers, and moves nothing else. -/
lemma emitClauseProgramAt_eval_of_rel_long_prepared
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store) (σ0 : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs).length addr
      (l1 :: l2 :: l3 :: l4 :: litRest) ((cs.map encodeClause).flatten ++ tail)
      pref σ σ0) :
    ∃ σp, σp = (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0 ∧
      WriterState σp M curJ start pref ∧
      BitsFrom σp (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: litRest)
          ((cs.map encodeClause).flatten ++ tail)) ∧
      σp cursorReg = addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1 ∧
      σp freshReg = base ∧
      σp remainingReg = (l1 :: l2 :: l3 :: l4 :: litRest).length ∧ σp posPolReg = 0 ∧
      (∀ r, r ≠ remainingReg → r ≠ carryPolReg → r ≠ carryValReg → r ≠ posPolReg →
        σp r = σ0 r) := by
  have hsafe := hrel.long_safety.to_split_tail_safety
  have hwd := hsafe.writer_distinct
  have hvals := cnf_emit_long_prep_prog_values lengthReg remainingReg carryPolReg carryValReg
    posPolReg freshReg σ0 base (l1 :: l2 :: l3 :: l4 :: litRest).length
    hprep.length hprep.fresh_value
    hwd.2.2.2.1 hwd.1.symm hwd.2.2.2.2.1.symm
    hwd.2.2.2.2.2.2.1.symm hwd.2.2.2.2.2.2.2.2.1.symm hwd.2.1 hwd.2.2.1.symm
    hwd.2.2.2.2.2.2.2.2.2
  have hframe := fun r hr hcp hcv hpp =>
    emit_clause_long_prep_frame lengthReg remainingReg carryPolReg carryValReg posPolReg freshReg
      r σ0 hr hcp hcv hpp
  refine ⟨_, rfl, emit_clause_long_prep_writer M curJ start remainingReg carryPolReg
    carryValReg posPolReg lengthReg freshReg pref σ0 hprep.writer hsafe hrel.safety.pos_nonzero,
    ?_, ?_, ?_, hvals.1, hvals.2.2.2, hframe⟩
  · apply bitsFrom_of_eq_on (hb := hprep.input)
    intro i _hi
    have hbelowRem : remainingReg < start := hsafe.writer_below.2.2.2.2
    have hbelowCP : carryPolReg < start := hsafe.writer_below.1
    have hbelowCV : carryValReg < start := hsafe.writer_below.2.1
    have hbelowPP : posPolReg < start := hsafe.writer_below.2.2.1
    have hstartLe := hprep.start_at_input
    exact hframe _ (by omega) (by omega) (by omega) (by omega)
  · exact (hframe cursorReg
      (Ne.symm (hsafe.writer_parser remainingReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser carryPolReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser carryValReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser posPolReg (by simp)).1)).trans hprep.cursor
  · exact (hframe freshReg hwd.2.2.2.2.2.2.2.2.2 hwd.2.2.1.symm
      hwd.2.2.2.2.2.1.symm hwd.2.2.2.2.2.2.2.1.symm).trans hprep.fresh_value

/-- The writer room and the capacity left for the split-tail payload of a long head clause, both
read off `CNFEmitRel`. -/
lemma emitClauseProgramAt_eval_of_rel_long_room
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ) :
    start + pref.length + l1.var + l2.var + base + 6 < M + curJ ∧
    start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: litRest)).length + 2 <
      M + curJ := by
  have hr := cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base
    (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) cs tail pref addr σ hrel
  simp only at hr
  have hpay := split_tail_emit_long_clause_payload base l1 l2 l3 (l4 :: litRest)
  refine ⟨?_, ?_⟩
  · have hlenPayload : l1.var + l2.var + base + 6 ≤
        (encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: l4 :: litRest)).1).length + 2 := by
      cases l1 <;> cases l2 <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral, encodeNat_length, List.length_append, Literal.var] <;> omega
    omega
  · have hr' : start + pref.length +
        (encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var 0 base ++
          splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: litRest)).length + 2 <
        M + curJ := by
      rw [hpay]
      exact hr
    simp [List.length_append] at hr' ⊢
    omega

/-- The variable and length bounds that the long-clause split-tail run needs, read off
`CNFEmitRel`. -/
lemma emitClauseProgramAt_eval_of_rel_long_bounds
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ) :
    l1.var + 1 ≤ bound ∧ l2.var + 1 ≤ bound ∧
    (∀ l ∈ l3 :: l4 :: litRest, l.var + 1 ≤ bound) ∧
    (l3 :: l4 :: litRest).length ≤ tailBound := by
  refine ⟨hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l1 (by simp),
    hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l2 (by simp),
    fun l hl => hrel.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp) l
      (by simp [hl]), ?_⟩
  have h := hrel.tail_bound_ok (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) (by simp)
  simp only [List.length_cons] at h ⊢
  omega

lemma emitClauseProgramAt_eval_of_rel_long
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  obtain ⟨σ0, hprep⟩ := cnfEmitRel_long_prepState M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest cs
    tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨σp, hσp, hwriterPrep, hinputPrep, hcursorPrep, hfreshPrep, hremPrep, hposPrep,
      hpframe⟩ :=
    emitClauseProgramAt_eval_of_rel_long_prepared M curJ tmpJ start cursorReg polReg varReg
      doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest cs
      tail pref addr σ σ0 hrel hprep
  obtain ⟨hroom, hcap⟩ := emitClauseProgramAt_eval_of_rel_long_room M curJ tmpJ start cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg
    negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest
    cs tail pref addr σ hrel
  obtain ⟨hbound1, hbound2, hboundTail, hls⟩ := emitClauseProgramAt_eval_of_rel_long_bounds M
    curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound
    tailBound base l1 l2 l3 l4 litRest cs tail pref addr σ hrel
  have hsafe := hrel.long_safety.to_split_tail_safety
  have hlen4 : 4 ≤ σ0 lengthReg := by
    rw [hprep.length]
    exact Nat.le_add_left 4 litRest.length
  have hb0 := emitClausePrepState_bound_frame hprep boundReg bound
    hok.split.ne_cursor hok.ne_length hok.split.ne_done hb
  have hbprep : σp boundReg = bound :=
    (hpframe boundReg hok.split.ne_remaining hok.split.ne_carry_pol
      hok.split.ne_carry_val hok.split.ne_pos_pol).trans hb0
  have hpost :=
    (splitTailEmitLongClauseSetup_eval M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base l1 l2 (l3 :: l4 :: litRest) pref ((cs.map encodeClause).flatten ++ tail)
      (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) σp hbound1 hbound2 hroom hcap
      hinputPrep hcurJ htmpJ hprep.input_above hprep.start_at_input hwriterPrep hposPrep
      hfreshPrep hremPrep hcursorPrep hsafe).1
  have hbsetup :
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval
        σp) boundReg = bound :=
    (splitTailEmitLongClauseSetup_low_frame M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base l1 l2 (l3 :: l4 :: litRest) pref ((cs.map encodeClause).flatten ++ tail)
      (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) σp hbound1 hbound2 hroom hcap
      hinputPrep hcurJ htmpJ hprep.start_at_input hwriterPrep hposPrep
      hfreshPrep hremPrep hcursorPrep hsafe hok.split.below
      ⟨hok.split.ne_cursor, hok.split.ne_pol2, hok.split.ne_var2, hok.split.ne_pol3,
        hok.split.ne_var3, hok.split.ne_done, hok.split.ne_carry_pol, hok.split.ne_carry_val,
        hok.split.ne_pos_pol, hok.split.ne_fresh, hok.split.ne_remaining⟩).trans hbprep
  have hlong := splitTailEmitLongClauseProgAt_eval_of_rel M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg boundReg bound tailBound (base + 1) (Literal.neg base)
    (l3 :: l4 :: litRest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base)
    ((cs.map encodeClause).flatten ++ tail)
    (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1 + l1.var + 2 + l2.var + 2) σp
    hboundTail (by simp) hls hpost hbprep hbsetup hok.split
  subst hσp
  unfold emitClauseProgramAt emitClauseProgram
  rw [eval_seq, eval_seq,
    decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ hb, ← hprep.decoded]
  exact emitClauseDispatchProgAt_long_eq curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ0 hlen4 hlong

lemma emitClauseIterProgramAt_eval_of_rel_long
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ :=
  emitClauseIterProgramAt_eq_of curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound σ
    (emitClauseProgramAt_eval_of_rel_long M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 l4 litRest cs
      tail pref addr σ hcurJ htmpJ hrel hb hok)

lemma emitClauseIterProgramAt_eval_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ)
    (hb : σ boundReg = bound)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  cases c with
  | mk lits =>
    match lits with
    | [] =>
        exact emitClauseIterProgramAt_eval_of_rel_nil M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base cs tail pref
          addr σ hcurJ htmpJ hrel hb
    | [l] =>
        exact emitClauseIterProgramAt_eval_of_rel_one M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l cs tail pref
          addr σ hcurJ htmpJ hrel hb hok
    | [l1, l2] =>
        exact emitClauseIterProgramAt_eval_of_rel_two M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 cs tail
          pref addr σ hcurJ htmpJ hrel hb hok
    | [l1, l2, l3] =>
        exact emitClauseIterProgramAt_eval_of_rel_three M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 cs
          tail pref addr σ hcurJ htmpJ hrel hb hok
    | l1 :: l2 :: l3 :: l4 :: rest =>
        exact emitClauseIterProgramAt_eval_of_rel_long M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 l4 rest
          cs tail pref addr σ hcurJ htmpJ hrel hb hok

lemma emitClauseIterProgram_bound_frame_nil
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  have hroom : start + pref.length + 6 * (base + 2) < M + curJ := by
    have hr := cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[]⟩ : Clause) cs tail pref addr σ hrel
    have hlenPayload :
        (encodeThreeClausesPayload (clauseToThree base (⟨[]⟩ : Clause).lits).1).length =
          6 * (base + 2) := by
      simp [clauseToThree_nil, encodeThreeClausesPayload, encodeThreeClause,
        encodeLiteral, encodeNat_length, List.length_append]
      omega
    omega
  have hp := emitClauseProgram_nil_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    ((⟨[]⟩ : Clause) :: cs).length addr ((cs.map encodeClause).flatten ++ tail) pref σ
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) boundReg hprep hroom
    hok.split.below hok.split.ne_cursor hok.ne_length hok.split.ne_done
    hok.split.ne_fresh hok.ne_outer
  unfold emitClauseIterProgram
  rw [eval_seq, emitClauseResetProg_frame lengthReg doneReg _
    (r := boundReg) hok.ne_length hok.split.ne_done]
  exact hp

lemma emitClauseIterProgram_bound_frame_one
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[l]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  have hlitbound : l.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l]⟩ : Clause) (by simp) l (by simp)
  have hroom : start + pref.length + 3 * (l.var + 2) < M + curJ := by
    have hr := cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l]⟩ : Clause) cs tail pref addr σ hrel
    have hlenPayload :
        (encodeThreeClausesPayload (clauseToThree base (⟨[l]⟩ : Clause).lits).1).length =
          3 * (l.var + 2) := by
      cases l <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral, encodeNat_length, List.length_append, Literal.var] <;>
        omega
    omega
  have hp := emitClauseProgram_one_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    ((⟨[l]⟩ : Clause) :: cs).length addr l ((cs.map encodeClause).flatten ++ tail) pref σ
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) boundReg hprep
    hlitbound hroom hok.split.below hok.split.ne_cursor hok.ne_length
    hok.split.ne_pol hok.split.ne_var hok.split.ne_done hok.ne_outer
  unfold emitClauseIterProgram
  rw [eval_seq, emitClauseResetProg_frame lengthReg doneReg _
    (r := boundReg) hok.ne_length hok.split.ne_done]
  exact hp

lemma emitClauseIterProgram_bound_frame_two
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  have hbound1 : l1.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l1, l2]⟩ : Clause) (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l1, l2]⟩ : Clause) (by simp) l2 (by simp)
  have hpairBelow : pol2Reg < start ∧ var2Reg < start :=
    ⟨hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList])⟩
  have hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 :=
    ⟨hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
  have hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg] :=
    registerPairwise_of_nodup hrel.long_safety.pair_register_nodup
  have hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ := by
    have hr := cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2]⟩ : Clause) cs tail pref
      addr σ hrel
    have hlenPayload :
        l1.var + 2 * l2.var + 6 ≤
          (encodeThreeClausesPayload (clauseToThree base (⟨[l1, l2]⟩ : Clause).lits).1).length +
            2 := by
      cases l1 <;> cases l2 <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral, encodeNat_length, List.length_append, Literal.var] <;> omega
    omega
  have hp := emitClauseProgram_two_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    ((⟨[l1, l2]⟩ : Clause) :: cs).length addr l1 l2
    ((cs.map encodeClause).flatten ++ tail) pref σ
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) boundReg hprep
    hbound1 hbound2 hpairBelow hpairNonzero hpairSafe hroom hok.split.below
    hok.split.ne_cursor hok.ne_length hok.split.ne_pol hok.split.ne_var
    hok.split.ne_done hok.split.ne_pol2 hok.split.ne_var2 hok.ne_outer
  unfold emitClauseIterProgram
  rw [eval_seq, emitClauseResetProg_frame lengthReg doneReg _
    (r := boundReg) hok.ne_length hok.split.ne_done]
  exact hp

lemma emitClauseIterProgram_bound_frame_three
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨[l1, l2, l3]⟩ : Clause) cs tail pref addr σ hcurJ htmpJ hrel
  have hbound1 : l1.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l1, l2, l3]⟩ : Clause) (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l1, l2, l3]⟩ : Clause) (by simp) l2 (by simp)
  have hbound3 : l3.var + 1 ≤ bound :=
    hrel.literal_bound (⟨[l1, l2, l3]⟩ : Clause) (by simp) l3 (by simp)
  have htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start :=
    ⟨hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList])⟩
  have htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0 :=
    ⟨hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
  have htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg] :=
    registerPairwise_of_nodup hrel.long_safety.triple_register_nodup
  have hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 <
      M + curJ := by
    have hr := cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2, l3]⟩ : Clause) cs tail pref
      addr σ hrel
    have hlenPayload :
        l1.var + l2.var + 2 * base + 2 * l3.var + 12 ≤
          (encodeThreeClausesPayload
            (clauseToThree base (⟨[l1, l2, l3]⟩ : Clause).lits).1).length + 2 := by
      cases l1 <;> cases l2 <;> cases l3 <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral, splitTail, encodeNat_length, List.length_append, Literal.var] <;>
        omega
    omega
  have hp := emitClauseProgram_three_low_frame_of_prep M curJ tmpJ start cursorReg polReg
    varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg
    negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    ((⟨[l1, l2, l3]⟩ : Clause) :: cs).length addr l1 l2 l3
    ((cs.map encodeClause).flatten ++ tail) pref σ
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) hprep
    hbound1 hbound2 hbound3 htripleBelow htripleNonzero htripleSafe hroom boundReg
    hok.split.below hok.split.ne_cursor hok.ne_length hok.split.ne_pol hok.split.ne_var
    hok.split.ne_done hok.split.ne_pol2 hok.split.ne_var2 hok.split.ne_pol3
    hok.split.ne_var3 hok.ne_outer hok.split.ne_fresh
  unfold emitClauseIterProgram
  rw [eval_seq, emitClauseResetProg_frame lengthReg doneReg _
    (r := boundReg) hok.ne_length hok.split.ne_done]
  exact hp

lemma emitClauseIterProgram_bound_frame_long
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  obtain ⟨σ0, hprep⟩ := cnfEmitRel_long_prepState M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest cs
    tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨σp, hσp, hwriterPrep, hinputPrep, hcursorPrep, hfreshPrep, hremPrep, hposPrep,
      hpframe⟩ :=
    emitClauseProgramAt_eval_of_rel_long_prepared M curJ tmpJ start cursorReg polReg varReg
      doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest cs
      tail pref addr σ σ0 hrel hprep
  obtain ⟨hroom, hcap⟩ := emitClauseProgramAt_eval_of_rel_long_room M curJ tmpJ start cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg
    negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base l1 l2 l3 l4 litRest
    cs tail pref addr σ hrel
  obtain ⟨hbound1, hbound2, hboundTail, hls⟩ := emitClauseProgramAt_eval_of_rel_long_bounds M
    curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound
    tailBound base l1 l2 l3 l4 litRest cs tail pref addr σ hrel
  have hsafe := hrel.long_safety.to_split_tail_safety
  have hlen4 : 4 ≤ σ0 lengthReg := by
    rw [hprep.length]
    exact Nat.le_add_left 4 litRest.length
  have hnat : σ0 boundReg = σ boundReg :=
    hprep.frame boundReg hok.split.ne_cursor hok.ne_length hok.split.ne_done
  have hbprep : σp boundReg = σ boundReg :=
    (hpframe boundReg hok.split.ne_remaining hok.split.ne_carry_pol
      hok.split.ne_carry_val hok.split.ne_pos_pol).trans hnat
  have hrnot : boundReg ∉ splitTailEmitStepWriteSet cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg := by
    simp [splitTailEmitStepWriteSet]
    exact hok.split.ne_write_set
  obtain ⟨τ, hτ, hτr⟩ := splitTailEmitLongClauseProg_eval_end_to_end_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound base
    l1 l2 l3 l4 litRest pref ((cs.map encodeClause).flatten ++ tail)
    (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) σp
    hbound1 hbound2 hboundTail hls hroom hcap hinputPrep hcurJ htmpJ
    hprep.input_above hprep.start_at_input hwriterPrep hposPrep hfreshPrep hremPrep
    hcursorPrep hsafe hok.split.below hrnot
  unfold emitClauseIterProgram emitClauseProgram
  rw [eval_seq, emitClauseResetProg_frame lengthReg doneReg _
    (r := boundReg) hok.ne_length hok.split.ne_done, eval_seq, ← hprep.decoded,
    emitClauseDispatchProg_long_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ0 hlen4]
  simp only [eval_seq]
  have hcommit :
      (emitClauseCommitProg outerReg).eval
        ((splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          bound tailBound).eval σp) boundReg =
        ((splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          bound tailBound).eval σp) boundReg := by
    simp [emitClauseCommitProg, eval_assign, Expr.eval,
      writeReg_diff _ outerReg _ boundReg hok.ne_outer]
  have hunfold :
      (Program.assign posPolReg (.const 0)).eval
        ((Program.assign carryValReg (.reg freshReg)).eval
          ((Program.assign carryPolReg (.const 1)).eval
            ((Program.assign remainingReg (.reg lengthReg)).eval σ0))) = σp := by
    rw [hσp]
    simp [eval_seq, eval_skip, eval_assign]
  rw [hunfold, hcommit, ← hτ, hτr, hbprep]

lemma emitClauseIterProgram_bound_frame_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ)
    (hok : EmitClauseBoundRegOk boundReg start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg) :
    (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ boundReg = σ boundReg := by
  cases c with
  | mk lits =>
    match lits with
    | [] =>
        exact emitClauseIterProgram_bound_frame_nil M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base cs tail pref
          addr σ hcurJ htmpJ hrel hok
    | [l] =>
        exact emitClauseIterProgram_bound_frame_one M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l cs tail pref
          addr σ hcurJ htmpJ hrel hok
    | [l1, l2] =>
        exact emitClauseIterProgram_bound_frame_two M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 cs tail
          pref addr σ hcurJ htmpJ hrel hok
    | [l1, l2, l3] =>
        exact emitClauseIterProgram_bound_frame_three M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 cs
          tail pref addr σ hcurJ htmpJ hrel hok
    | l1 :: l2 :: l3 :: l4 :: rest =>
        exact emitClauseIterProgram_bound_frame_long M curJ tmpJ start cursorReg polReg varReg
          doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
          carryPolReg carryValReg freshReg outerReg boundReg bound tailBound base l1 l2 l3 l4 rest
          cs tail pref addr σ hcurJ htmpJ hrel hok

end NPComplete.CookLevin

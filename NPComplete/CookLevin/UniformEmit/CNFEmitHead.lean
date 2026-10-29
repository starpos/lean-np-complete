module

public import NPComplete.CookLevin.UniformEmit.StartupTransport

/-!
# CNF emission head state

The CNF emitter needs a common outer relation across branch-specific head clauses.
This module derives preparation, payload-room, and register-safety facts from the
emission relation, and proves the dispatcher agrees with the concrete writer for
each short clause. It also establishes the register safety needed to start
long-clause emission.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral)


/-! ## `CNFEmitRel` transport for the outer iterator -/

lemma cnfEmitRel_head_payload_room
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ) :
    start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c.lits).1).length + 2 < M + curJ := by
  have hc := hrel.capacity
  rw [clausesToThree_payload_cons] at hc
  simp only [List.length_append] at hc
  omega

lemma emitClausePrepState_of_cnfEmitRel
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base (c :: cs).length addr
      c.lits ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) := by
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ hrel
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral c.lits ++ ((cs.map encodeClause).flatten ++ tail)) := by
    simpa [encodeClause] using hhead
  have hbound : c.lits.length + 1 ≤ bound := hrel.clause_bound c (by simp)
  exact emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base (c :: cs).length addr
    c.lits ((cs.map encodeClause).flatten ++ tail) pref σ hcurJ htmpJ hbound
    hrel.start_at_input hinput hrel.cursor hrel.length_zero hrel.done_zero hrel.outer
    hrel.fresh hrel.pos hrel.neg hrel.input_above hrel.writer
    (cnfEmitRel_head_payload_room M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base c cs tail pref addr σ hrel)
    hrel.safety

lemma emitClausePrepState_bound_frame
    {M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg outerReg freshReg
      posPolReg negPolReg bound base outer addr : ℕ}
    {c : List Literal} {rest pref : Bits} {σ σ0 : Store}
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr c rest pref σ σ0)
    (boundReg : ℕ) (N : ℕ)
    (hbc : boundReg ≠ cursorReg) (hbl : boundReg ≠ lengthReg)
    (hbd : boundReg ≠ doneReg) (hb : σ boundReg = N) :
    σ0 boundReg = N :=
  (hprep.frame boundReg hbc hbl hbd).trans hb

lemma emitClauseProgramAt_eval_of_rel_nil
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
    (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  unfold emitClauseProgramAt emitClauseProgram
  rw [eval_seq, eval_seq,
    decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ hb]
  exact emitClauseDispatchProgAt_zero_eq curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) hprep.length

lemma emitClauseProgramAt_eval_of_rel_one
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
    (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[l]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  have hb0 := emitClausePrepState_bound_frame hprep boundReg bound
    hok.split.ne_cursor hok.ne_length hok.split.ne_done hb
  unfold emitClauseProgramAt emitClauseProgram
  rw [eval_seq, eval_seq,
    decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ hb]
  exact emitClauseDispatchProgAt_one_eq curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) hprep.length hb0
    hok.split.ne_cursor hok.split.ne_pol hok.split.ne_var hok.split.ne_done

lemma emitClauseProgramAt_eval_of_rel_two
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
    (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2]⟩ : Clause) cs
    tail pref addr σ hcurJ htmpJ hrel
  have hb0 := emitClausePrepState_bound_frame hprep boundReg bound
    hok.split.ne_cursor hok.ne_length hok.split.ne_done hb
  unfold emitClauseProgramAt emitClauseProgram
  rw [eval_seq, eval_seq,
    decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ hb]
  exact emitClauseDispatchProgAt_two_eq curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) hprep.length hb0
    hok.split.ne_cursor hok.split.ne_pol hok.split.ne_var hok.split.ne_done
    hok.split.ne_pol2 hok.split.ne_var2

lemma emitClauseProgramAt_eval_of_rel_three
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
    (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  have hprep := emitClausePrepState_of_cnfEmitRel M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨[l1, l2, l3]⟩ : Clause) cs tail pref addr σ hcurJ htmpJ hrel
  have hb0 := emitClausePrepState_bound_frame hprep boundReg bound
    hok.split.ne_cursor hok.ne_length hok.split.ne_done hb
  unfold emitClauseProgramAt emitClauseProgram
  rw [eval_seq, eval_seq,
    decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ hb]
  exact emitClauseDispatchProgAt_three_eq curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg bound tailBound
    ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) hprep.length hb0
    hok.split.ne_cursor hok.split.ne_pol hok.split.ne_var hok.split.ne_done
    hok.split.ne_pol2 hok.split.ne_var2 hok.split.ne_pol3 hok.split.ne_var3

end NPComplete.CookLevin

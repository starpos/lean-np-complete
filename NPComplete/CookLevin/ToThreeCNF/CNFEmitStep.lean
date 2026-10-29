module

public import NPComplete.CookLevin.ToThreeCNF.CNFEmitRel

/-!
# Clause-shape transition proofs

The outer CNF loop needs one next-state relation for every head-clause width.
This module proves preparation and transition facts for empty and short clauses,
and establishes the long-clause endpoint from the loop relation. These facts let
each branch feed the common outer-iteration contract.
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
/-- The decode-ready state of an empty head clause, with its writer room and remaining input, all
read off `CNFEmitRel`. -/
lemma cnfEmitRel_nil_step_of_iter_post_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[]⟩ : Clause) :: cs).length addr []
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) ∧
    start + pref.length + 6 * (base + 2) < M + curJ ∧
    BitsFrom σ (addr + (encodeList encodeLiteral []).length)
      ((cs.map encodeClause).flatten ++ tail) := by
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base ⟨[]⟩ cs tail pref addr σ hrel
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral [] ++ ((cs.map encodeClause).flatten ++ tail)) := by
    simpa using hhead
  have hbound : 0 + 1 ≤ bound := by
    simpa using hrel.clause_bound ⟨[]⟩ (by simp)
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base []).1).length + 2 < M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hroom : start + pref.length + 6 * (base + 2) < M + curJ := by
    have hlenPayload :
        6 * (base + 2) ≤ (encodeThreeClausesPayload (clauseToThree base []).1).length := by
      have h := encodeThreeClausesPayload_length_ge (clauseToThree base []).1
      simp only [clauseToThree_nil] at h ⊢
      simp [Literal.var] at h ⊢
      omega
    omega
  refine ⟨?_, hroom, (bitsFrom_append σ addr (encodeList encodeLiteral []) _ hinput).2⟩
  exact emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base _ addr []
    ((cs.map encodeClause).flatten ++ tail) pref σ hcurJ htmpJ hbound hrel.start_at_input hinput
    hrel.cursor hrel.length_zero hrel.done_zero hrel.outer hrel.fresh hrel.pos hrel.neg
    hrel.input_above hrel.writer hroomPayload hrel.safety

/-- After the empty clause program runs, the input beyond the clause is intact, everything above
the temporaries is untouched, and the constant polarity registers still hold `0` and `1`. -/
lemma cnfEmitRel_nil_step_of_iter_post_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τe : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[]⟩ : Clause) :: cs).length addr []
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ))
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    (hrest : BitsFrom σ (addr + (encodeList encodeLiteral []).length)
      ((cs.map encodeClause).flatten ++ tail))
    (hEval : τe = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ) :
    BitsFrom τe (addr + (encodeList encodeLiteral []).length)
      ((cs.map encodeClause).flatten ++ tail) ∧
    (∀ r, M + tmpJ < r → τe r = σ r) ∧ τe posPolReg = 0 ∧ τe negPolReg = 1 := by
  have hFrame := emitClauseProgram_nil_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base _ addr
    ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hroom
  have hlow := fun s (hs : s = posPolReg ∨ s = negPolReg) =>
    emitClauseProgram_nil_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr
      ((cs.map encodeClause).flatten ++ tail) pref σ _ s hprep hroom
      (by rcases hs with rfl | rfl; exacts [hrel.safety.pos_below, hrel.safety.neg_below])
  have hsafe := hrel.safety
  subst hEval
  refine ⟨?_, hFrame, ?_, ?_⟩
  · apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    have haddr := hrel.input_above
    exact hFrame (addr + (encodeList encodeLiteral []).length + i) (by omega)
  · exact (hlow posPolReg (Or.inl rfl) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp))).trans hrel.pos
  · exact (hlow negPolReg (Or.inr rfl) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp))).trans hrel.neg

lemma cnfEmitRel_nil_step_of_iter_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[]⟩ : Clause) cs tail pref addr σ τ := by
  obtain ⟨hprep, hroom, hrest⟩ := cnfEmitRel_nil_step_of_iter_post_prep M curJ tmpJ
    start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    cs tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨τe, hEval, hWriter, hCursor, hFresh, hOuter⟩ :=
    emitClauseProgram_nil_eval_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr
      ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hroom
  obtain ⟨hinputE, hFrameE, hposE, hnegE⟩ := cnfEmitRel_nil_step_of_iter_post_frame M curJ tmpJ
    start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    cs tail pref addr σ τe hrel hprep hroom hrest hEval
  simpa using
    (cnfEmitIterPost_of_endpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base ⟨[]⟩ cs tail pref addr σ τe
      hrel ⟨hEval, hWriter, hCursor, hFresh, hOuter⟩ hinputE hFrameE hposE hnegE htmpJ
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp))
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp)))

/-- The decode-ready state of a one-literal head clause, with its literal-variable bound, writer
room and remaining input, all read off `CNFEmitRel`. -/
lemma cnfEmitRel_one_step_of_iter_post_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[l]⟩ : Clause) :: cs).length addr [l]
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) ∧
    l.var + 1 ≤ bound ∧
    start + pref.length + 3 * (l.var + 2) < M + curJ ∧
    BitsFrom σ (addr + (encodeList encodeLiteral [l]).length)
      ((cs.map encodeClause).flatten ++ tail) := by
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base ⟨[l]⟩ cs tail pref addr σ hrel
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral [l] ++ ((cs.map encodeClause).flatten ++ tail)) := by
    simpa [encodeClause, List.append_assoc] using hhead
  have hbound : 2 ≤ bound := by
    simpa using hrel.clause_bound ⟨[l]⟩ (by simp)
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base [l]).1).length + 2 < M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hroom : start + pref.length + 3 * (l.var + 2) < M + curJ := by
    have hlenPayload :
        3 * (l.var + 2) ≤ (encodeThreeClausesPayload (clauseToThree base [l]).1).length := by
      have h := encodeThreeClausesPayload_length_ge (clauseToThree base [l]).1
      simp only [clauseToThree_one] at h ⊢
      simp [Literal.var] at h ⊢
      omega
    omega
  refine ⟨?_, by simpa using hrel.literal_bound (⟨[l]⟩ : Clause) (by simp) l (by simp), hroom, ?_⟩
  · exact emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base _ addr [l]
      ((cs.map encodeClause).flatten ++ tail) pref σ hcurJ htmpJ hbound hrel.start_at_input hinput
      hrel.cursor hrel.length_zero hrel.done_zero hrel.outer hrel.fresh hrel.pos hrel.neg
      hrel.input_above hrel.writer hroomPayload hrel.safety
  · exact (bitsFrom_append σ addr (encodeList encodeLiteral [l]) _ hinput).2

/-- After the one-literal clause program runs, the input beyond the clause is intact, everything
above the temporaries is untouched, and the constant polarity registers still hold `0` and `1`. -/
lemma cnfEmitRel_one_step_of_iter_post_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τe : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[l]⟩ : Clause) :: cs).length addr [l]
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ))
    (hlitbound : l.var + 1 ≤ bound)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ)
    (hrest : BitsFrom σ (addr + (encodeList encodeLiteral [l]).length)
      ((cs.map encodeClause).flatten ++ tail))
    (hEval : τe = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ) :
    BitsFrom τe (addr + (encodeList encodeLiteral [l]).length)
      ((cs.map encodeClause).flatten ++ tail) ∧
    (∀ r, M + tmpJ < r → τe r = σ r) ∧ τe posPolReg = 0 ∧ τe negPolReg = 1 := by
  have hFrame := emitClauseProgram_one_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base _ addr l
    ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hlitbound hroom
  have hlow := fun s (hs : s = posPolReg ∨ s = negPolReg) =>
    emitClauseProgram_one_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l
      ((cs.map encodeClause).flatten ++ tail) pref σ _ s hprep hlitbound hroom
      (by rcases hs with rfl | rfl; exacts [hrel.safety.pos_below, hrel.safety.neg_below])
  have hsafe := hrel.safety
  subst hEval
  refine ⟨?_, hFrame, ?_, ?_⟩
  · apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    have haddr := hrel.input_above
    exact hFrame (addr + (encodeList encodeLiteral [l]).length + i) (by omega)
  · exact (hlow posPolReg (Or.inl rfl) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp))).trans hrel.pos
  · exact (hlow negPolReg (Or.inr rfl) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp)) (hsafe.ne_of_pair (by simp))
      (hsafe.ne_of_pair (by simp))).trans hrel.neg

lemma cnfEmitRel_one_step_of_iter_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l]⟩ : Clause) cs tail pref addr σ τ := by
  obtain ⟨hprep, hlitbound, hroom, hrest⟩ := cnfEmitRel_one_step_of_iter_post_prep M curJ tmpJ
    start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l cs tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨τe, hEval, hWriter, hCursor, hFresh, hOuter⟩ :=
    emitClauseProgram_one_eval_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l
      ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hlitbound hroom
  obtain ⟨hinputE, hFrameE, hposE, hnegE⟩ := cnfEmitRel_one_step_of_iter_post_frame M curJ tmpJ
    start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l cs tail pref addr σ τe hrel hprep hlitbound hroom hrest hEval
  simpa using
    (cnfEmitIterPost_of_endpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base ⟨[l]⟩ cs tail pref addr σ τe
      hrel ⟨hEval, hWriter, hCursor, hFresh, hOuter⟩ hinputE hFrameE hposE hnegE htmpJ
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp))
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp)))

/-- The decode-ready state of a two-literal head clause, with its literal-variable bounds, writer
room and remaining input, all read off `CNFEmitRel`. -/
lemma cnfEmitRel_two_step_of_iter_post_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[l1, l2]⟩ : Clause) :: cs).length addr
      [l1, l2] ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) ∧
    l1.var + 1 ≤ bound ∧ l2.var + 1 ≤ bound ∧
    start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ ∧
    BitsFrom σ (addr + (encodeList encodeLiteral [l1, l2]).length)
      ((cs.map encodeClause).flatten ++ tail) := by
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base ⟨[l1, l2]⟩ cs tail pref addr σ hrel
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral [l1, l2] ++ ((cs.map encodeClause).flatten ++ tail)) := by
    simpa [encodeClause, List.append_assoc] using hhead
  have hbound : 3 ≤ bound := by
    simpa using hrel.clause_bound ⟨[l1, l2]⟩ (by simp)
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base [l1, l2]).1).length + 2 < M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ := by
    have hlenPayload :
        l1.var + 2 * l2.var + 6 ≤
          (encodeThreeClausesPayload (clauseToThree base [l1, l2]).1).length + 2 := by
      have h := encodeThreeClausesPayload_length_ge (clauseToThree base [l1, l2]).1
      simp only [clauseToThree_two] at h ⊢
      simp only [List.map_cons, List.map_nil, List.sum_cons] at h
      omega
    omega
  refine ⟨?_, hrel.literal_bound ⟨[l1, l2]⟩ (by simp) l1 (by simp),
    hrel.literal_bound ⟨[l1, l2]⟩ (by simp) l2 (by simp), hroom,
    (bitsFrom_append σ addr (encodeList encodeLiteral [l1, l2]) _ hinput).2⟩
  exact emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base _ addr [l1, l2]
    ((cs.map encodeClause).flatten ++ tail) pref σ hcurJ htmpJ hbound hrel.start_at_input hinput
    hrel.cursor hrel.length_zero hrel.done_zero hrel.outer hrel.fresh hrel.pos hrel.neg
    hrel.input_above hrel.writer hroomPayload hrel.safety

/-- After the two-literal clause program runs, the input beyond the clause is intact, everything
above the temporaries is untouched, and the constant polarity registers still hold `0` and `1`. -/
lemma cnfEmitRel_two_step_of_iter_post_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τe : Store)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hpairPosNegSafe : RegisterPairwise
      [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg,
        outerReg, posPolReg, negPolReg])
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base ((⟨[l1, l2]⟩ : Clause) :: cs).length addr
      [l1, l2] ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ))
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ)
    (hrest : BitsFrom σ (addr + (encodeList encodeLiteral [l1, l2]).length)
      ((cs.map encodeClause).flatten ++ tail))
    (hEval : τe = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ) :
    BitsFrom τe (addr + (encodeList encodeLiteral [l1, l2]).length)
      ((cs.map encodeClause).flatten ++ tail) ∧
    (∀ r, M + tmpJ < r → τe r = σ r) ∧ τe posPolReg = 0 ∧ τe negPolReg = 1 := by
  have hFrame := emitClauseProgram_two_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base _ addr l1 l2
    ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hbound1 hbound2
    hpairBelow hpairNonzero hpairSafe hroom
  have hregNe : ∀ (r a : ℕ),
      (r, a) ∈ registerPairs
        [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg,
          freshReg, outerReg, posPolReg, negPolReg] → r ≠ a := fun r a hp => hpairPosNegSafe hp
  have hlow := fun s (hs : s = posPolReg ∨ s = negPolReg) =>
    emitClauseProgram_two_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l1 l2
      ((cs.map encodeClause).flatten ++ tail) pref σ _ s hprep hbound1 hbound2
      hpairBelow hpairNonzero hpairSafe hroom
      (by rcases hs with rfl | rfl; exacts [hrel.safety.pos_below, hrel.safety.neg_below])
  subst hEval
  refine ⟨?_, hFrame, ?_, ?_⟩
  · apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    have haddr := hrel.input_above
    exact hFrame (addr + (encodeList encodeLiteral [l1, l2]).length + i) (by omega)
  · exact (hlow posPolReg (Or.inl rfl) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))).trans hrel.pos
  · exact (hlow negPolReg (Or.inr rfl) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))).trans hrel.neg

lemma cnfEmitRel_two_step_of_iter_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hpairPosNegSafe : RegisterPairwise
      [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg,
        outerReg, posPolReg, negPolReg])
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2]⟩ : Clause) cs tail pref addr σ τ := by
  obtain ⟨hprep, hbound1, hbound2, hroom, hrest⟩ := cnfEmitRel_two_step_of_iter_post_prep M curJ
    tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l1 l2 cs tail pref addr σ hcurJ htmpJ hrel
  obtain ⟨τe, hEval, hWriter, hCursor, hFresh, hOuter⟩ :=
    emitClauseProgram_two_eval_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l1 l2
      ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hbound1 hbound2
      hpairBelow hpairNonzero hpairSafe hroom
  obtain ⟨hinputE, hFrameE, hposE, hnegE⟩ := cnfEmitRel_two_step_of_iter_post_frame M curJ tmpJ
    start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l1 l2 cs tail pref addr σ τe hpairBelow hpairNonzero hpairSafe hpairPosNegSafe hrel hprep
    hbound1 hbound2 hroom hrest hEval
  simpa using
    (cnfEmitIterPost_of_endpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base ⟨[l1, l2]⟩ cs tail pref addr
      σ τe hrel ⟨hEval, hWriter, hCursor, hFresh, hOuter⟩ hinputE hFrameE hposE hnegE htmpJ
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp))
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp)))

/-- The decode-ready state of a three-literal head clause, with its literal-variable bounds, writer
room and remaining input, all read off `CNFEmitRel`. -/
lemma cnfEmitRel_three_step_of_iter_post_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ) :
    EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs).length addr [l1, l2, l3]
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ) ∧
    l1.var + 1 ≤ bound ∧ l2.var + 1 ≤ bound ∧ l3.var + 1 ≤ bound ∧
    start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ ∧
    BitsFrom σ (addr + (encodeList encodeLiteral [l1, l2, l3]).length)
      ((cs.map encodeClause).flatten ++ tail) := by
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base ⟨[l1, l2, l3]⟩ cs tail pref addr σ hrel
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral [l1, l2, l3] ++ ((cs.map encodeClause).flatten ++ tail)) := by
    simpa [encodeClause, List.append_assoc] using hhead
  have hbound : 4 ≤ bound := by
    simpa using hrel.clause_bound ⟨[l1, l2, l3]⟩ (by simp)
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1).length + 2 < M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ := by
    have hlenPayload :
        l1.var + l2.var + 2 * base + 2 * l3.var + 12 ≤
          (encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1).length + 2 := by
      have h := encodeThreeClausesPayload_length_ge (clauseToThree base [l1, l2, l3]).1
      simp only [clauseToThree_cons4, splitTail_one] at h ⊢
      simp [Literal.var] at h ⊢
      omega
    omega
  refine ⟨?_, hrel.literal_bound ⟨[l1, l2, l3]⟩ (by simp) l1 (by simp),
    hrel.literal_bound ⟨[l1, l2, l3]⟩ (by simp) l2 (by simp),
    hrel.literal_bound ⟨[l1, l2, l3]⟩ (by simp) l3 (by simp), hroom,
    (bitsFrom_append σ addr (encodeList encodeLiteral [l1, l2, l3]) _ hinput).2⟩
  exact emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base _ addr [l1, l2, l3]
    ((cs.map encodeClause).flatten ++ tail) pref σ hcurJ htmpJ hbound hrel.start_at_input hinput
    hrel.cursor hrel.length_zero hrel.done_zero hrel.outer hrel.fresh hrel.pos hrel.neg
    hrel.input_above hrel.writer hroomPayload hrel.safety

/-- After the three-literal clause program runs, the input beyond the clause is intact, everything
above the temporaries is untouched, and the constant polarity registers still hold `0` and `1`. -/
lemma cnfEmitRel_three_step_of_iter_post_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τe : Store)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (htriplePosNegSafe : RegisterPairwise
      [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        freshReg, outerReg, posPolReg, negPolReg])
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs).length addr [l1, l2, l3]
      ((cs.map encodeClause).flatten ++ tail) pref σ
      ((decodeNatProgram cursorReg lengthReg doneReg bound).eval σ))
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ)
    (hrest : BitsFrom σ (addr + (encodeList encodeLiteral [l1, l2, l3]).length)
      ((cs.map encodeClause).flatten ++ tail))
    (hEval : τe = (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ) :
    BitsFrom τe (addr + (encodeList encodeLiteral [l1, l2, l3]).length)
      ((cs.map encodeClause).flatten ++ tail) ∧
    (∀ r, M + tmpJ < r → τe r = σ r) ∧ τe posPolReg = 0 ∧ τe negPolReg = 1 := by
  have hFrame := emitClauseProgram_three_frame_of_prep M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base _ addr l1 l2 l3
    ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hbound1 hbound2 hbound3
    htripleBelow htripleNonzero htripleSafe hroom
  have hregNe : ∀ (r a : ℕ),
      (r, a) ∈ registerPairs
        [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg,
          pol3Reg, var3Reg, freshReg, outerReg, posPolReg, negPolReg] → r ≠ a :=
    fun r a hp => htriplePosNegSafe hp
  have hlow := fun s (hs : s = posPolReg ∨ s = negPolReg) =>
    emitClauseProgram_three_low_frame_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l1 l2 l3
      ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hbound1 hbound2 hbound3
      htripleBelow htripleNonzero htripleSafe hroom s
      (by rcases hs with rfl | rfl; exacts [hrel.safety.pos_below, hrel.safety.neg_below])
  subst hEval
  refine ⟨?_, hFrame, ?_, ?_⟩
  · apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    have haddr := hrel.input_above
    exact hFrame (addr + (encodeList encodeLiteral [l1, l2, l3]).length + i) (by omega)
  · exact (hlow posPolReg (Or.inl rfl) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))).trans hrel.pos
  · exact (hlow negPolReg (Or.inr rfl) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))
      (hregNe _ _ (by simp)) (hregNe _ _ (by simp)) (hregNe _ _ (by simp))).trans hrel.neg

lemma cnfEmitRel_three_step_of_iter_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (htriplePosNegSafe : RegisterPairwise
      [cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        freshReg, outerReg, posPolReg, negPolReg])
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l1, l2, l3]⟩ : Clause) cs tail pref addr σ τ := by
  obtain ⟨hprep, hbound1, hbound2, hbound3, hroom, hrest⟩ :=
    cnfEmitRel_three_step_of_iter_post_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base l1 l2 l3 cs tail pref addr σ hcurJ htmpJ
      hrel
  obtain ⟨τe, hEval, hWriter, hCursor, hFresh, hOuter⟩ :=
    emitClauseProgram_three_eval_of_prep M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base _ addr l1 l2 l3
      ((cs.map encodeClause).flatten ++ tail) pref σ _ hprep hbound1 hbound2 hbound3
      htripleBelow htripleNonzero htripleSafe hroom
  obtain ⟨hinputE, hFrameE, hposE, hnegE⟩ := cnfEmitRel_three_step_of_iter_post_frame M curJ
    tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l1 l2 l3 cs tail pref addr σ τe htripleBelow htripleNonzero htripleSafe htriplePosNegSafe
    hrel hprep hbound1 hbound2 hbound3 hroom hrest hEval
  simpa using
    (cnfEmitIterPost_of_endpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base ⟨[l1, l2, l3]⟩ cs tail pref
      addr σ τe hrel ⟨hEval, hWriter, hCursor, hFresh, hOuter⟩ hinputE hFrameE hposE hnegE htmpJ
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp))
      (hrel.safety.ne_of_pair (by simp)) (hrel.safety.ne_of_pair (by simp)))


lemma cnfEmitRel_long_step_of_iter_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (restClauses : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ σ0 σprep : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hσ0 : σ0 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval σ)
    (hlen0 : σ0 lengthReg = (l1 :: l2 :: l3 :: l4 :: litRest).length)
    (hprep : σprep =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ0)
    (hinputPrep : BitsFrom σprep
      (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: litRest)
        ((restClauses.map encodeClause).flatten ++ tail)))
    (hwriterPrep : WriterState σprep M curJ start pref)
    (hinputAbovePrep : M + tmpJ <
      addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
    (hstartPrep : start ≤
      addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
    (hposPrep : σprep posPolReg = 0)
    (hfreshPrep : σprep freshReg = base)
    (hremaining : σprep remainingReg =
      (l1 :: l2 :: l3 :: l4 :: litRest).length)
    (hcursorPrep : σprep cursorReg =
      addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
    (hsplitSafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg)
    (houterBelow : outerReg < start) (houterNonzero : outerReg ≠ 0)
    (houterDisjoint : outerReg ≠ freshReg ∧ outerReg ≠ cursorReg)
    (houterLong :
      (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg bound tailBound).eval σprep outerReg =
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length)
    (hlongFrame : ∀ r, M + tmpJ < r →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
        carryPolReg carryValReg freshReg outerReg bound tailBound).eval σ r = σ r)
    (hnegFrame :
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
        carryPolReg carryValReg freshReg outerReg bound tailBound).eval σ negPolReg =
      σ negPolReg)
    (hposLong :
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
        carryPolReg carryValReg freshReg outerReg bound tailBound).eval σ posPolReg =
      0)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses) tail pref addr σ)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: litRest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: litRest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base)
        (l3 :: l4 :: litRest)).length + 2 < M + curJ) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) restClauses tail pref addr σ τ := by
  obtain ⟨τe, hEval, hWriter, hCursor, hFresh, hOuter⟩ :=
    emitClauseProgram_long_eval_concrete M curJ tmpJ start cursorReg polReg varReg
      doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound
      base ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length addr
      l1 l2 l3 l4 litRest pref ((restClauses.map encodeClause).flatten ++ tail)
      σ σ0 σprep hσ0 hlen0 hprep
      hinputPrep hcurJ htmpJ hinputAbovePrep hstartPrep hwriterPrep
      hposPrep hfreshPrep hremaining hcursorPrep
      hsplitSafety houterBelow houterNonzero houterDisjoint houterLong
      hbound1 hbound2 hboundTail hls hroom hcapacity
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) restClauses tail pref addr σ hrel
  have hrest : BitsFrom σ
      (addr + (encodeList encodeLiteral (l1 :: l2 :: l3 :: l4 :: litRest)).length)
      ((restClauses.map encodeClause).flatten ++ tail) := by
    obtain ⟨_, hsuffix⟩ := bitsFrom_append σ addr
      (encodeList encodeLiteral (l1 :: l2 :: l3 :: l4 :: litRest))
      ((restClauses.map encodeClause).flatten ++ tail) (by
        simpa [encodeClause, List.append_assoc] using hhead)
    exact hsuffix
  have hinputE : BitsFrom τe
      (addr + (encodeList encodeLiteral (l1 :: l2 :: l3 :: l4 :: litRest)).length)
      ((restClauses.map encodeClause).flatten ++ tail) := by
    apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    rw [hEval]
    exact hlongFrame
      (addr + (encodeList encodeLiteral (l1 :: l2 :: l3 :: l4 :: litRest)).length + i)
      (by have := hrel.input_above; omega)
  have hposE : τe posPolReg = 0 := by
    rw [hEval]
    exact hposLong
  have hnegE : τe negPolReg = 1 := by
    calc
      τe negPolReg =
          (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
            remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
            carryValReg freshReg outerReg bound tailBound).eval σ negPolReg := by
              rw [hEval]
      _ = σ negPolReg := hnegFrame
      _ = 1 := hrel.neg
  have hendpoint : EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length
      addr pref (l1 :: l2 :: l3 :: l4 :: litRest) σ τe :=
    ⟨hEval, hWriter, hCursor, hFresh, hOuter⟩
  have hlongFrame' : ∀ r, M + tmpJ < r → τe r = σ r := by
    intro r hr
    rw [hEval]
    exact hlongFrame r hr
  exact cnfEmitIterPost_of_endpoint M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base
    (⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) restClauses tail pref addr σ τe
    hrel hendpoint hinputE hlongFrame' hposE hnegE htmpJ
    (by exact hrel.safety.ne_of_pair (a := posPolReg) (b := lengthReg) (by simp))
    (by exact hrel.safety.ne_of_pair (a := posPolReg) (b := doneReg) (by simp))
    (by exact hrel.safety.ne_of_pair (a := negPolReg) (b := lengthReg) (by simp))
    (by exact hrel.safety.ne_of_pair (a := negPolReg) (b := doneReg) (by simp))


end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ToThreeCNF.CNFEmitLong

/-!
# Per-clause emission steps

The outer loop must account for each input clause while advancing the parser and
extending the output prefix. This module closes the constructor-wise cases and
records workspace limits needed to continue with either short-clause or
split-tail emission.
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
/-- The conclusion of one outer emission step for the head clause `c`: the iteration program
reaches a state satisfying the relation for the rewritten clause, advanced input and extended
writer prefix. -/
def CNFEmitConsStepGoal
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store) : Prop :=
  ∃ τ, τ = (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ ∧
      CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound
      (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ

/-- Outer emission step for a two-literal head clause: the register-safety side conditions of the
two-literal clause program are read off the long-clause safety bundle. -/
lemma cnfEmitRel_cons_step_two
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l l2 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l, l2]⟩ : Clause) :: cs) tail pref addr σ) :
    CNFEmitConsStepGoal M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l, l2]⟩ : Clause) cs tail pref
      addr σ := by
  obtain ⟨τ, hp⟩ := cnfEmitRel_two_step_of_iter_post M curJ tmpJ start cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l l2 cs tail pref addr σ hcurJ htmpJ
    ⟨hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList])⟩
    ⟨hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
    (registerPairwise_of_nodup hrel.long_safety.pair_register_nodup)
    (registerPairwise_of_nodup hrel.long_safety.pair_pos_neg_nodup) hrel
  exact cnfEmitRel_step_of_iter_post_eval M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨[l, l2]⟩ : Clause) cs tail pref addr σ hrel ⟨τ, hp⟩

/-- Outer emission step for a three-literal head clause: the register-safety side conditions of the
three-literal clause program are read off the long-clause safety bundle. -/
lemma cnfEmitRel_cons_step_three
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l l2 l3 : Literal) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨[l, l2, l3]⟩ : Clause) :: cs) tail pref addr σ) :
    CNFEmitConsStepGoal M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (⟨[l, l2, l3]⟩ : Clause) cs tail pref
      addr σ := by
  obtain ⟨τ, hp⟩ := cnfEmitRel_three_step_of_iter_post M curJ tmpJ start cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
    l l2 l3 cs tail pref addr σ hcurJ htmpJ
    ⟨hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList]),
      hrel.long_safety.below _ (by simp [longClauseRegisterList])⟩
    ⟨hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrel.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
    (registerPairwise_of_nodup hrel.long_safety.triple_register_nodup)
    (registerPairwise_of_nodup hrel.long_safety.triple_pos_neg_nodup) hrel
  exact cnfEmitRel_step_of_iter_post_eval M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨[l, l2, l3]⟩ : Clause) cs tail pref addr σ hrel ⟨τ, hp⟩

/-- The writer room and the capacity left after the first two literals of a long head clause,
read off `CNFEmitRel`. -/
lemma cnfEmitRel_cons_step_long_room
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l l2 l3 l4 : Literal) (rest4 : List Literal) (cs : List Clause) (tail pref : Bits)
    (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l :: l2 :: l3 :: l4 :: rest4⟩ : Clause) :: cs) tail pref addr σ) :
    start + pref.length + l.var + l2.var + base + 6 < M + curJ ∧
    start + (pref ++ encodedThreeLiteralBits (literalPolarity l) l.var
      (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest4)).length + 2 <
      M + curJ := by
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload
        (clauseToThree base (l :: l2 :: l3 :: l4 :: rest4)).1).length + 2 < M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  refine ⟨?_, ?_⟩
  · have hlenPayload : l.var + l2.var + base + 6 ≤
        (encodeThreeClausesPayload
          (clauseToThree base (l :: l2 :: l3 :: l4 :: rest4)).1).length + 2 := by
      have h := encodeThreeClausesPayload_length_ge
        (clauseToThree base (l :: l2 :: l3 :: l4 :: rest4)).1
      simp only [clauseToThree_cons4] at h ⊢
      simp [Literal.var] at h ⊢
      omega
    omega
  · have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    rw [← split_tail_emit_long_clause_payload] at hc
    simp only [List.length_append] at hc ⊢
    omega

/-- Outer emission step for a head clause with at least four literals. -/
lemma cnfEmitRel_cons_step_long
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l l2 l3 l4 : Literal) (rest4 : List Literal) (cs : List Clause) (tail pref : Bits)
    (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l :: l2 :: l3 :: l4 :: rest4⟩ : Clause) :: cs) tail pref addr σ) :
    CNFEmitConsStepGoal M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      (⟨l :: l2 :: l3 :: l4 :: rest4⟩ : Clause) cs tail pref addr σ := by
  obtain ⟨hroom, hcapacity⟩ := cnfEmitRel_cons_step_long_room M curJ tmpJ start cursorReg
    polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg
    negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base l l2 l3 l4 rest4
    cs tail pref addr σ hrel
  obtain ⟨τ, hp⟩ := cnfEmitRel_long_step_of_iter_post_concrete
    M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base l l2 l3 l4 rest4 cs tail pref addr σ
    hcurJ htmpJ hroom hcapacity hrel
  exact cnfEmitRel_step_of_iter_post_eval M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base
    (⟨l :: l2 :: l3 :: l4 :: rest4⟩ : Clause) cs tail pref addr σ hrel ⟨τ, hp⟩

lemma cnfEmitRel_cons_step
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ) :
    ∃ τ, τ = (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ ∧
      CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound
      (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ := by
  rcases c with ⟨_ | ⟨l, _ | ⟨l2, _ | ⟨l3, _ | ⟨l4, rest4⟩⟩⟩⟩⟩
  · obtain ⟨τ, hp⟩ := cnfEmitRel_nil_step_of_iter_post M curJ tmpJ start cursorReg
      polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base
      cs tail pref addr σ hcurJ htmpJ hrel
    exact cnfEmitRel_step_of_iter_post_eval M curJ tmpJ start cursorReg polReg varReg
      doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[]⟩ : Clause) cs
      tail pref addr σ hrel ⟨τ, hp⟩
  · obtain ⟨τ, hp⟩ := cnfEmitRel_one_step_of_iter_post M curJ tmpJ start cursorReg
      polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      posPolReg negPolReg carryPolReg carryValReg freshReg outerReg bound tailBound base l
      cs tail pref addr σ hcurJ htmpJ hrel
    exact cnfEmitRel_step_of_iter_post_eval M curJ tmpJ start cursorReg polReg varReg
      doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base (⟨[l]⟩ : Clause) cs
      tail pref addr σ hrel ⟨τ, hp⟩
  · exact cnfEmitRel_cons_step_two M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base l l2 cs tail pref addr σ hcurJ htmpJ hrel
  · exact cnfEmitRel_cons_step_three M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base l l2 l3 cs tail pref addr σ hcurJ htmpJ
      hrel
  · exact cnfEmitRel_cons_step_long M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base l l2 l3 l4 rest4 cs tail pref addr σ
      hcurJ htmpJ hrel

end NPComplete.CookLevin

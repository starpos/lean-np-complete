module

public import NPComplete.CookLevin.NatParser.LengthPrefix

/-!
# Clause length-prefix evaluation

The scanner's cursor and loop counter depend on the unary length prefix before
any literal is processed. This module isolates that setup stage, proving how
decoding establishes the clause length and initializes the remaining-count
register while preserving the rest of the store.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr cost_forN loopCost loopCost_le_of_body_le
    eval_seq eval_assign eval_ifNZ eval_forN loopEval loopEval_succ cost_seq cost_assign
    writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_length)
open NPComplete.SAT (Literal encodeLiteral)

/-- Length-prefix stage: after clearing `doneReg` and `lengthReg` and running the unary decoder,
the cursor sits on the literal payload and `lengthReg` holds the clause length. -/
lemma decodeClauseWithLengthProgram_eval_decode_length
    (cursorReg doneReg maxReg lengthReg bound addr m : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
    (hmc : maxReg ≠ cursorReg) (hmd : maxReg ≠ doneReg) (hlm : lengthReg ≠ maxReg)
    (hbound : xs.length + 1 ≤ bound)
    (hca : cursorReg < addr) (hda : doneReg < addr) (hla : lengthReg < addr)
    (hc : σ cursorReg = addr) (hmax : σ maxReg = m)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest)) :
    ∃ σ1, σ1 = (decodeNatProgram cursorReg lengthReg doneReg bound).eval
        ((Program.assign lengthReg (.const 0)).eval ((Program.assign doneReg (.const 0)).eval σ)) ∧
      σ1 cursorReg = addr + xs.length + 1 ∧ σ1 lengthReg = xs.length ∧ σ1 maxReg = m ∧
      BitsFrom σ1 (addr + xs.length + 1) ((xs.map encodeLiteral).flatten ++ rest) ∧
      ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg → σ1 r = σ r := by
  obtain ⟨σlen, hσlen⟩ : ∃ s, s = (Program.assign lengthReg (.const 0)).eval
      ((Program.assign doneReg (.const 0)).eval σ) := ⟨_, rfl⟩
  have hfr : ∀ r, r ≠ doneReg → r ≠ lengthReg → σlen r = σ r := by
    intro r h1 h2
    subst hσlen
    simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r h1, writeReg_diff _ lengthReg _ r h2]
  have hlen0 : σlen lengthReg = 0 := by
    subst hσlen
    simp [eval_assign, Expr.eval, writeReg_same]
  have hdone0 : σlen doneReg = 0 := by
    subst hσlen
    simp [eval_assign, Expr.eval, writeReg_diff _ lengthReg _ doneReg (Ne.symm hld),
      writeReg_same]
  have hbitsLen : BitsFrom σlen addr (encodeList encodeLiteral xs ++ rest) :=
    bitsFrom_of_eq_on (fun i _ => hfr _ (by omega) (by omega)) hbits
  obtain ⟨hcur, hlen, _, hframe⟩ :=
    decodeNatProgram_encodeList_length_append encodeLiteral cursorReg lengthReg doneReg bound
      addr 0 xs rest σlen (Ne.symm hlc) hcd hld hbound hca hla hda
      ((hfr _ hcd (Ne.symm hlc)).trans hc) hlen0 hdone0 hbitsLen
  have hshape : encodeList encodeLiteral xs ++ rest =
      encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeNat xs.length)
    ((xs.map encodeLiteral).flatten ++ rest) (by rw [← hshape]; exact hbits)
  have hfrAll : ∀ r, r ≠ cursorReg → r ≠ lengthReg → r ≠ doneReg →
      (decodeNatProgram cursorReg lengthReg doneReg bound).eval σlen r = σ r :=
    fun r h1 h2 h3 => (hframe r h1 h2 h3).trans (hfr r h3 h2)
  refine ⟨_, by rw [hσlen], hcur, by simpa using hlen,
    (hframe maxReg hmc (Ne.symm hlm) hmd).trans
      ((hfr maxReg hmd (Ne.symm hlm)).trans hmax), ?_, hfrAll⟩
  have hlenEq : (encodeNat xs.length).length = xs.length + 1 := encodeNat_length _
  intro i hi
  rw [hfrAll _ (by omega) (by omega) (by omega)]
  have := htail i hi
  rwa [hlenEq, ← Nat.add_assoc] at this

/-- Reset-and-copy stage: clearing `doneReg` and copying `lengthReg` into `remainingReg` only
touches those two registers. -/
lemma decodeClauseWithLengthProgram_eval_write_remaining
    (cursorReg doneReg remainingReg maxReg lengthReg n a m b : ℕ) (bits : Bits) (σ1 : Store)
    (hld : lengthReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hrm : remainingReg ≠ maxReg) (hlr : lengthReg ≠ remainingReg)
    (hcd : cursorReg ≠ doneReg) (hmd : maxReg ≠ doneReg)
    (hdb : doneReg < b) (hrb : remainingReg < b)
    (hlen : σ1 lengthReg = n) (hc : σ1 cursorReg = a) (hmax : σ1 maxReg = m)
    (hbits : BitsFrom σ1 b bits) :
    ∃ σ3, σ3 = (Program.assign remainingReg (.reg lengthReg)).eval
        ((Program.assign doneReg (.const 0)).eval σ1) ∧
      σ3 remainingReg = n ∧ σ3 cursorReg = a ∧ σ3 maxReg = m ∧ σ3 lengthReg = n ∧
      BitsFrom σ3 b bits ∧ ∀ r, r ≠ doneReg → r ≠ remainingReg → σ3 r = σ1 r := by
  obtain ⟨σ3, hσ3⟩ : ∃ s, s = (Program.assign remainingReg (.reg lengthReg)).eval
      ((Program.assign doneReg (.const 0)).eval σ1) := ⟨_, rfl⟩
  have hfr : ∀ r, r ≠ doneReg → r ≠ remainingReg → σ3 r = σ1 r := by
    intro r h1 h2
    subst hσ3
    simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r h1,
      writeReg_diff _ remainingReg _ r h2]
  refine ⟨σ3, hσ3, ?_, ?_, ?_, ?_, ?_, hfr⟩
  · subst hσ3
    simp [eval_assign, Expr.eval, writeReg_same,
      writeReg_diff _ doneReg _ lengthReg hld, hlen]
  · exact (hfr _ hcd (Ne.symm hrc)).trans hc
  · exact (hfr _ hmd (Ne.symm hrm)).trans hmax
  · exact (hfr _ hld hlr).trans hlen
  · exact bitsFrom_of_eq_on (fun i _ => hfr _ (by omega) (by omega)) hbits

lemma decodeClauseWithLengthProgram_eval
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound clauseBound addr m : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hrm : remainingReg ≠ maxReg)
    (hmc : maxReg ≠ cursorReg) (hmp : maxReg ≠ polReg)
    (hmv : maxReg ≠ varReg) (hmd : maxReg ≠ doneReg)
    (hlc : lengthReg ≠ cursorReg) (hlp : lengthReg ≠ polReg)
    (hlv : lengthReg ≠ varReg) (hld : lengthReg ≠ doneReg)
    (hlr : lengthReg ≠ remainingReg) (hlm : lengthReg ≠ maxReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr ∧ lengthReg < addr)
    (hc : σ cursorReg = addr) (hmax : σ maxReg = m)
    (hbound : xs.length + 1 ≤ bound)
    (hclause : xs.length ≤ clauseBound)
    (hvarbound : ∀ l ∈ xs, l.var + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest)) :
    (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      bound clauseBound).eval σ cursorReg = addr + (encodeList encodeLiteral xs).length ∧
    (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      bound clauseBound).eval σ remainingReg = 0 ∧
    (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      bound clauseBound).eval σ maxReg = max m (literalVarMax xs) ∧
    (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      bound clauseBound).eval σ lengthReg = xs.length ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg → r ≠ lengthReg →
      (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
        bound clauseBound).eval σ r = σ r) := by
  obtain ⟨σ1, hσ1, hcur1, hlen1, hmax1, hbits1, hfr1⟩ :=
    decodeClauseWithLengthProgram_eval_decode_length cursorReg doneReg maxReg lengthReg bound
      addr m xs rest σ hcd hlc hld hmc hmd hlm hbound hbelow.1 hbelow.2.2.2.1
      hbelow.2.2.2.2.2.2 hc hmax hbits
  obtain ⟨σ3, hσ3, hrem3, hcur3, hmax3, hlen3, hbits3, hfr3⟩ :=
    decodeClauseWithLengthProgram_eval_write_remaining cursorReg doneReg remainingReg maxReg
      lengthReg xs.length (addr + xs.length + 1) m (addr + xs.length + 1) _ σ1 hld hrc hrm hlr
      hcd hmd (by omega) (by omega) hlen1 hcur1 hmax1 hbits1
  obtain ⟨hcurL, hremL, hmaxL, hframeL⟩ :=
    decode_clause_loop_eval cursorReg polReg varReg doneReg remainingReg maxReg bound
      (addr + xs.length + 1) m xs rest σ3 hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hrm
      hmc hmp hmv hmd (by omega) hrem3 hcur3 hmax3 hvarbound hbits3
  have hprog :
      (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg bound clauseBound).eval σ =
        loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
          xs.length σ3 := by
    unfold decodeClauseWithLengthProgram decodeClauseWithLengthPrefix
    rw [eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_forN, ← hσ1, ← hσ3]
    simp only [Expr.eval]
    rw [show clauseBound = xs.length + (clauseBound - xs.length) by omega,
      loopEval_add_right_local]
    rw [decodeClauseStep_loop_zero_local cursorReg polReg varReg doneReg remainingReg maxReg bound
      (clauseBound - xs.length) _ hremL]
  rw [hprog]
  refine ⟨?_, hremL, hmaxL, (hframeL lengthReg hlc hlp hlv hld hlr hlm).trans hlen3, ?_⟩
  · rw [hcurL]
    simp [encodeList, List.length_append, List.length_flatten, encodeNat_length]; omega
  · intro r h1 h2 h3 h4 h5 h6 h7
    exact (hframeL r h1 h2 h3 h4 h5 h6).trans ((hfr3 r h4 h5).trans (hfr1 r h1 h7 h4))

lemma decodeClauseWithLengthProgramDynamic_eval
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound addr m : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hrm : remainingReg ≠ maxReg)
    (hmc : maxReg ≠ cursorReg) (hmp : maxReg ≠ polReg)
    (hmv : maxReg ≠ varReg) (hmd : maxReg ≠ doneReg)
    (hlc : lengthReg ≠ cursorReg) (hlp : lengthReg ≠ polReg)
    (hlv : lengthReg ≠ varReg) (hld : lengthReg ≠ doneReg)
    (hlr : lengthReg ≠ remainingReg) (hlm : lengthReg ≠ maxReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr ∧ lengthReg < addr)
    (hc : σ cursorReg = addr) (hmax : σ maxReg = m)
    (hbound : xs.length + 1 ≤ bound)
    (hvarbound : ∀ l ∈ xs, l.var + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest)) :
    (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound).eval σ cursorReg = addr + (encodeList encodeLiteral xs).length ∧
    (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound).eval σ remainingReg = 0 ∧
    (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound).eval σ maxReg = max m (literalVarMax xs) ∧
    (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound).eval σ lengthReg = xs.length ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg → r ≠ lengthReg →
      (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg bound).eval σ r = σ r) := by
  have hprefix := decodeClauseWithLengthPrefix_remaining_eval cursorReg doneReg remainingReg
    lengthReg bound addr xs rest σ hcd hlc hld
    ⟨hbelow.1, hbelow.2.2.2.1, hbelow.2.2.2.2.2.2⟩ hc hbound hbits
  have heq := decodeClauseWithLengthProgramDynamic_eq_fixed_of_prefix cursorReg polReg varReg
    doneReg remainingReg maxReg lengthReg bound xs.length σ hprefix
  have hfixed := decodeClauseWithLengthProgram_eval cursorReg polReg varReg doneReg remainingReg
    maxReg lengthReg bound xs.length addr m xs rest σ hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hrm
    hmc hmp hmv hmd hlc hlp hlv hld hlr hlm hbelow hc hmax hbound (by simp) hvarbound hbits
  rw [heq]
  exact hfixed

end NPComplete.CookLevin

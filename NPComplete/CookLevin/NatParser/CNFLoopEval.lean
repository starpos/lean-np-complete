module

public import NPComplete.CookLevin.NatParser.CNFStepEval

/-!
# CNF loop evaluation

Clause decoding is proved at the step level, but the whole formula scanner must
preserve its cursor, statistics, and untouched registers across many clauses.
This module lifts those step facts through the bounded loop and connects the
resulting store to outer decoding.
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

lemma decodeCNFStep_eval_from_clause
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound clauseBound addr addrOut m base c k lengthVal baseOut countOut : ℕ) (σ : Store)
    (hcur : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ cursorReg = addrOut)
    (hrem : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ remainingReg = 0)
    (hmax : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ maxReg = m)
    (hlen : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ lengthReg = lengthVal)
    (hfresh : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ freshReg = baseOut)
    (hcount : (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound clauseBound).eval σ countReg = countOut)
    (houter : σ outerReg = k + 1)
    (hframe : ∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg → r ≠ lengthReg → r ≠ freshReg →
      r ≠ countReg → r ≠ tmpReg →
      (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg bound clauseBound).eval σ r = σ r)
    (houterRegs : outerReg ≠ cursorReg ∧ outerReg ≠ polReg ∧ outerReg ≠ varReg ∧
      outerReg ≠ doneReg ∧ outerReg ≠ remainingReg ∧ outerReg ≠ maxReg ∧
      outerReg ≠ lengthReg ∧ outerReg ≠ freshReg ∧ outerReg ≠ countReg ∧
      outerReg ≠ tmpReg) :
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ cursorReg = addrOut ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ outerReg = k ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ remainingReg = 0 ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ maxReg = m ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ lengthReg = lengthVal ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ freshReg = baseOut ∧
    (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound).eval
      σ countReg = countOut ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ outerReg → r ≠ remainingReg → r ≠ maxReg → r ≠ lengthReg →
      r ≠ freshReg → r ≠ countReg → r ≠ tmpReg →
      (Program.eval
      (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg bound clauseBound)
        σ) r = σ r) := by
  have _haddr : 0 ≤ addr := Nat.zero_le _
  have _hbase : 0 ≤ base := Nat.zero_le _
  have _hc : 0 ≤ c := Nat.zero_le _
  unfold decodeCNFStep
  rw [eval_seq]
  set τ := (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg
    lengthReg freshReg countReg tmpReg bound clauseBound).eval σ with hτ
  have htouter : τ outerReg = k + 1 := by
    exact (hframe outerReg houterRegs.1 houterRegs.2.1 houterRegs.2.2.1 houterRegs.2.2.2.1
      houterRegs.2.2.2.2.1 houterRegs.2.2.2.2.2.1 houterRegs.2.2.2.2.2.2.1
      houterRegs.2.2.2.2.2.2.2.1 houterRegs.2.2.2.2.2.2.2.2.1
      houterRegs.2.2.2.2.2.2.2.2.2).trans houter
  have hassign_frame : ∀ r, r ≠ outerReg →
      (Program.assign outerReg (.sub (.reg outerReg) (.const 1))).eval τ r = τ r := by
    intro r hr
    simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ r hr]
  have hassign_outer :
      (Program.assign outerReg (.sub (.reg outerReg) (.const 1))).eval τ outerReg = k := by
    simp [eval_assign, Expr.eval, writeReg_same, htouter]
  refine ⟨?_, hassign_outer, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hassign_frame cursorReg (Ne.symm houterRegs.1)).trans hcur
  · exact (hassign_frame remainingReg (Ne.symm houterRegs.2.2.2.2.1)).trans hrem
  · exact (hassign_frame maxReg (Ne.symm houterRegs.2.2.2.2.2.1)).trans hmax
  · exact (hassign_frame lengthReg (Ne.symm houterRegs.2.2.2.2.2.2.1)).trans hlen
  · exact (hassign_frame freshReg (Ne.symm houterRegs.2.2.2.2.2.2.2.1)).trans hfresh
  · exact (hassign_frame countReg (Ne.symm houterRegs.2.2.2.2.2.2.2.2.1)).trans hcount
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have hs := hframe r h1 h2 h3 h4 h6 h7 h8 h9 h10 h11
    exact (hassign_frame r h5).trans hs

lemma decode_cnf_outer_decode
    (cursorReg outerReg doneReg bound addr : ℕ) (clauses : List (List Literal))
    (rest : Bits) (σ : Store)
    (hco : cursorReg ≠ outerReg) (hcd : cursorReg ≠ doneReg)
    (hod : outerReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ outerReg < addr ∧ doneReg < addr)
    (hc : σ cursorReg = addr) (hbound : clauses.length + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList (encodeList encodeLiteral) clauses ++ rest)) :
    let σ0 := (Program.assign doneReg (.const 0)).eval σ
    let σ1 := (Program.assign outerReg (.const 0)).eval σ0
    let σ2 := (decodeNatProgram cursorReg outerReg doneReg bound).eval σ1
    σ2 cursorReg = addr + clauses.length + 1 ∧
    σ2 outerReg = clauses.length ∧ σ2 doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ outerReg → r ≠ doneReg → σ2 r = σ r) := by
  dsimp
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0
  set σ1 := (Program.assign outerReg (.const 0)).eval σ0 with hσ1
  have hσ0done : σ0 doneReg = 0 := by
    rw [hσ0]
    simp [eval_assign, Expr.eval, writeReg_same]
  have hσ0frame : ∀ r, r ≠ doneReg → σ0 r = σ r := by
    intro r hr
    rw [hσ0]
    simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  have hσ1outer : σ1 outerReg = 0 := by
    rw [hσ1]
    simp [eval_assign, Expr.eval, writeReg_same]
  have hσ1frame : ∀ r, r ≠ outerReg → σ1 r = σ0 r := by
    intro r hr
    rw [hσ1]
    simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ r hr]
  have hbits1 : BitsFrom σ1 addr (encodeList (encodeList encodeLiteral) clauses ++ rest) := by
    intro i hi
    calc
      σ1 (addr + i) = σ0 (addr + i) := hσ1frame _ (by omega)
      _ = σ (addr + i) := hσ0frame _ (by omega)
      _ = if (encodeList (encodeList encodeLiteral) clauses ++ rest)[i]
          then 1 else 0 := hbits i hi
  have hc1 : σ1 cursorReg = addr :=
    (hσ1frame cursorReg hco |>.trans (hσ0frame cursorReg hcd)) |>.trans hc
  have hσ1done : σ1 doneReg = 0 :=
    (hσ1frame doneReg (Ne.symm hod)).trans hσ0done
  obtain ⟨hcur, houter, hdone, hframe⟩ :=
    decodeNatProgram_encodeList_length_append (encodeList encodeLiteral)
      cursorReg outerReg doneReg bound addr 0 clauses rest σ1 hco hcd hod hbound
      hbelow.1 hbelow.2.1 hbelow.2.2 hc1
      hσ1outer hσ1done hbits1
  refine ⟨hcur, by simpa using houter, hdone, ?_⟩
  intro r h1 h2 h3
  exact (hframe r h1 h2 h3).trans (hσ1frame r h2 |>.trans (hσ0frame r h3))

end NPComplete.CookLevin

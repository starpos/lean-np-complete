module

public import NPComplete.CookLevin.NatParser.LengthEval

/-!
# CNF parser step facts

To analyze the whole scanner compositionally, the cost and state changes of one
clause must be established first. This module proves dynamic and fixed
clause-step evaluation facts, register frames, and per-step cost bounds used by
the loop proofs.
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

lemma decodeCNFClauseStepWithStatsDynamic_eq_fixed_of_prefix
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound n : ℕ) (σ : Store)
    (hprefix : (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval
      σ remainingReg = n) :
    (decodeCNFClauseStepWithStatsDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound).eval σ =
      (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg bound n).eval σ := by
  have hscan := decodeClauseWithLengthProgramDynamic_eq_fixed_of_prefix
    cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound n σ hprefix
  unfold decodeCNFClauseStepWithStatsDynamic decodeCNFClauseStepWithStats
  rw [eval_seq, eval_seq, hscan]

lemma decodeCNFStepDynamic_eq_fixed_of_prefix
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound n : ℕ) (σ : Store)
    (hprefix : (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval
      σ remainingReg = n) :
    (decodeCNFStepDynamic cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound).eval σ =
      (decodeCNFStep cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg bound n).eval σ := by
  have hclause := decodeCNFClauseStepWithStatsDynamic_eq_fixed_of_prefix
    cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
    bound n σ hprefix
  unfold decodeCNFStepDynamic decodeCNFStep
  rw [eval_seq, eval_seq, hclause]

lemma decodeCNFClauseStepWithStats_eval
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound clauseBound addr m base c : ℕ)
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
    (hbase : σ freshReg = base) (hcount : σ countReg = c)
    (hbound : xs.length + 1 ≤ bound) (hclause : xs.length ≤ clauseBound)
    (hvarbound : ∀ l ∈ xs, l.var + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest))
    (hcf : lengthReg ≠ freshReg) (hcc : lengthReg ≠ countReg)
    (hct : lengthReg ≠ tmpReg) (hfc : freshReg ≠ countReg)
    (hft : freshReg ≠ tmpReg) (hct' : countReg ≠ tmpReg)
    (hcursor : cursorReg ≠ lengthReg ∧ cursorReg ≠ freshReg ∧
      cursorReg ≠ countReg ∧ cursorReg ≠ tmpReg)
    (hremaining : remainingReg ≠ lengthReg ∧ remainingReg ≠ freshReg ∧
      remainingReg ≠ countReg ∧ remainingReg ≠ tmpReg)
    (hmaxreg : maxReg ≠ lengthReg ∧ maxReg ≠ freshReg ∧
      maxReg ≠ countReg ∧ maxReg ≠ tmpReg)
    (hfresh : freshReg ≠ cursorReg ∧ freshReg ≠ polReg ∧ freshReg ≠ varReg ∧
      freshReg ≠ doneReg ∧ freshReg ≠ remainingReg ∧ freshReg ≠ maxReg ∧
      freshReg ≠ lengthReg)
    (hcountreg : countReg ≠ cursorReg ∧ countReg ≠ polReg ∧ countReg ≠ varReg ∧
      countReg ≠ doneReg ∧ countReg ≠ remainingReg ∧ countReg ≠ maxReg ∧
      countReg ≠ lengthReg) :
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ cursorReg =
        addr + (encodeList encodeLiteral xs).length ∧
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ remainingReg = 0 ∧
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ maxReg =
        max m (literalVarMax xs) ∧
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ lengthReg = xs.length ∧
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ freshReg =
        base + clauseFreshIncByLength xs.length ∧
    (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound).eval σ countReg =
        c + clauseThreeCountByLength xs.length ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg → r ≠ lengthReg → r ≠ freshReg →
      r ≠ countReg → r ≠ tmpReg →
      (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg bound clauseBound).eval σ r = σ r) := by
  obtain ⟨hcur, hrem, hmax', hlen, hframe⟩ :=
    decodeClauseWithLengthProgram_eval cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound clauseBound addr m xs rest σ hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hrm
      hmc hmp hmv hmd hlc hlp hlv hld hlr hlm hbelow hc hmax hbound hclause hvarbound hbits
  set σ1 := (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound clauseBound).eval σ with hσ1
  have hbase1 : σ1 freshReg = base := by
    exact (hframe freshReg hfresh.1 hfresh.2.1 hfresh.2.2.1 hfresh.2.2.2.1
      hfresh.2.2.2.2.1 hfresh.2.2.2.2.2.1 hfresh.2.2.2.2.2.2).trans hbase
  have hcount1 : σ1 countReg = c := by
    exact (hframe countReg hcountreg.1 hcountreg.2.1 hcountreg.2.2.1 hcountreg.2.2.2.1
      hcountreg.2.2.2.2.1 hcountreg.2.2.2.2.2.1 hcountreg.2.2.2.2.2.2).trans hcount
  obtain ⟨hfresh', hcount'⟩ := clauseStatsProgram_outputs lengthReg freshReg countReg tmpReg
    xs.length base c σ1 hcf hcc hct hfc hft hct' hlen hbase1 hcount1
  have hcurS := clauseStatsProgram_frame lengthReg freshReg countReg tmpReg σ1 cursorReg
    hcursor.2.1 hcursor.2.2.1
  have hremS := clauseStatsProgram_frame lengthReg freshReg countReg tmpReg σ1 remainingReg
    hremaining.2.1 hremaining.2.2.1
  have hmaxS := clauseStatsProgram_frame lengthReg freshReg countReg tmpReg σ1 maxReg
    hmaxreg.2.1 hmaxreg.2.2.1
  have hlenS := clauseStatsProgram_frame lengthReg freshReg countReg tmpReg σ1 lengthReg
    hcf hcc
  unfold decodeCNFClauseStepWithStats
  rw [eval_seq, ← hσ1]
  refine ⟨hcurS.trans hcur, hremS.trans hrem, hmaxS.trans hmax', hlenS.trans hlen,
    hfresh', hcount', ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hs := clauseStatsProgram_frame lengthReg freshReg countReg tmpReg σ1 r h8 h9
  have hp := hframe r h1 h2 h3 h4 h5 h6 h7
  exact hs.trans hp

end NPComplete.CookLevin

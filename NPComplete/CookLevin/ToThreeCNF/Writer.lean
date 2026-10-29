module

public import NPComplete.CookLevin.ToThreeCNF.Encode

/-!
# Short-clause payload

The outer transformation needs one description of the bits a clause of length at most
three contributes to the output. `writerAppendClauseLE3Payload` gives that payload as a
function of the clause length and the literal registers, and
`writerAppendClauseLE3Payload_zero` pins down the empty-clause case explicitly.
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
def writerAppendClauseLE3Payload
    (len pol1 val1 pol2 val2 pol3 val3 base : ℕ) : Bits :=
  match len with
  | 0 => encodeThreeClausesPayload (clauseToThree base []).1
  | 1 => encodeThreeClausesPayload
      (clauseToThree base [literalOfPolarity pol1 val1]).1
  | 2 => encodeThreeClausesPayload
      (clauseToThree base [literalOfPolarity pol1 val1,
        literalOfPolarity pol2 val2]).1
  | 3 => encodeThreeClausesPayload
      (clauseToThree base [literalOfPolarity pol1 val1,
        literalOfPolarity pol2 val2, literalOfPolarity pol3 val3]).1
  | _ + 4 => []

lemma writerAppendClauseLE3Payload_zero
    (pol1 val1 pol2 val2 pol3 val3 base : ℕ) :
    writerAppendClauseLE3Payload 0 pol1 val1 pol2 val2 pol3 val3 base =
      encodedThreeLiteralBits 0 base 0 base 0 base ++
        encodedThreeLiteralBits 1 base 1 base 1 base := by
  have h0 := encodedThreeLiteralBits_eq_encodeThreeClause
    0 base 0 base 0 base (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have h1 := encodedThreeLiteralBits_eq_encodeThreeClause
    1 base 1 base 1 base (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have h0' : encodedThreeLiteralBits 0 base 0 base 0 base =
      encodeThreeClause ⟨Literal.pos base, Literal.pos base, Literal.pos base⟩ := by
    simpa [literalOfPolarity] using h0
  have h1' : encodedThreeLiteralBits 1 base 1 base 1 base =
      encodeThreeClause ⟨Literal.neg base, Literal.neg base, Literal.neg base⟩ := by
    simpa [literalOfPolarity] using h1
  simp [writerAppendClauseLE3Payload, encodeThreeClausesPayload,
    clauseToThree_nil]
  rw [← h0', ← h1']

end NPComplete.CookLevin

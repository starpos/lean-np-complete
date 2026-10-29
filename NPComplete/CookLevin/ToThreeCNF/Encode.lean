module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.ToThreeCNF.Rewrite

/-!
# Encoded CNF interface

The semantic rewrite is defined on CNF values, but the bounded RAM producer
consumes encoded input bits. This module connects those representations by
proving parser behavior on `encodeCNF` and size properties of the rewritten
output payload.
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
/-! ## Bit encoding of unbounded CNF -/

@[stable_api] def encodeClause (c : Clause) : Bits :=
  encodeList encodeLiteral c.lits

@[stable_api] def encodeCNF (φ : CNF) : Bits :=
  encodeList encodeClause φ.clauses

/-! ## Encoded three-clause payload

This module defines the flattened encoding of a list of three-literal clauses
and proves a lower bound on its length from the variables in those clauses.  The
bound supplies room estimates for later emitter proofs.
-/

def encodeThreeClausesPayload (cs : List ThreeClause) : Bits :=
  (cs.map encodeThreeClause).flatten

lemma encodeThreeClausesPayload_length_ge (cs : List ThreeClause) :
    (cs.map (fun c => c.l1.var + c.l2.var + c.l3.var + 6)).sum ≤
      (encodeThreeClausesPayload cs).length := by
  induction cs with
  | nil => simp [encodeThreeClausesPayload]
  | cons c cs ih =>
      simp only [encodeThreeClausesPayload, List.map_cons, List.flatten_cons,
        List.length_append, List.sum_cons]
      have hc : c.l1.var + c.l2.var + c.l3.var + 6 ≤
          (encodeThreeClause c).length := by
        cases c with
        | mk l1 l2 l3 =>
          cases l1 <;> cases l2 <;> cases l3 <;>
            simp [encodeThreeClause, encodeLiteral, encodeNat_length, Literal.var] <;> omega
      have ih' : (cs.map (fun c => c.l1.var + c.l2.var + c.l3.var + 6)).sum ≤
          (cs.map encodeThreeClause).flatten.length := by
        simpa [encodeThreeClausesPayload] using ih
      omega

end NPComplete.CookLevin

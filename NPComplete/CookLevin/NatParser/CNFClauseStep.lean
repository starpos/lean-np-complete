module

public import NPComplete.CookLevin.NatParser.CNFLoopEval

/-! A one-clause executable step.  The outer CNF scanner can use this body
without duplicating the length-prefix and literal-loop proof. -/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr cost_forN loopCost loopCost_le_of_body_le
    eval_seq eval_assign eval_ifNZ eval_forN loopEval loopEval_succ cost_seq cost_assign
    writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_length)
open NPComplete.SAT (Literal)

end NPComplete.CookLevin

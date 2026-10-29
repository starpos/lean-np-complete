module

public import NPComplete.CookLevin.ToThreeCNF
public import NPComplete.CookLevin.NatParser.UniformDecode

/-!
# Split-tail scratch state

The uniform producer cannot bake a clause's length into its split-tail programs, so the loop
bound has to be read from a register. This module defines the terminal, intermediate, and step
programs (`splitTailEmitTerminalOneProgAt` and the rest of the `...ProgAt` family) with that bound
register as an argument, which the later modules relate to the fixed-bound programs.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF)


/-! ## Split-tail with a bound register and a dynamic loop count -/

def splitTailEmitTerminalOneProgAt
    (curJ tmpJ cursorReg _polReg _varReg doneReg remainingReg pol2Reg var2Reg carryPolReg
      carryValReg _posPolReg _freshReg boundReg : ℕ) : Program :=
  .seq
    (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
    (.seq
      (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg)
      (.assign remainingReg (.const 0)))

def splitTailEmitTerminalTwoProgAt
    (curJ tmpJ cursorReg _polReg _varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg _posPolReg _freshReg boundReg : ℕ) : Program :=
  .seq
    (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
    (.seq
      (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
      (.seq
        (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg)
        (.assign remainingReg (.const 0))))

def splitTailEmitIntermediateProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg boundReg : ℕ) : Program :=
  .seq
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
    (.seq
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg)
      (.assign remainingReg (.sub (.reg remainingReg) (.const 1))))

def splitTailEmitStepProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) : Program :=
  .ifNZ (.eq (.reg remainingReg) (.const 0))
    Program.skip
    (.ifNZ (.eq (.reg remainingReg) (.const 1))
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      (.ifNZ (.eq (.reg remainingReg) (.const 2))
        (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          carryPolReg carryValReg posPolReg freshReg boundReg)))

end NPComplete.CookLevin

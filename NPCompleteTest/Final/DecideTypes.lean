module

import NPComplete

/-!
# `deriving DecidableEq` types of the library, plain `import NPComplete`

`Literal` and `Instruction`. Expected: `decide` and `decide +kernel` ok.
-/

open NPComplete.SAT NPComplete.BitCostRAM
example : Literal.pos 1 ≠ Literal.neg 1 := by decide
example : Literal.neg 3 = Literal.neg 3 := by decide +kernel
example : Instruction.halt ≠ Instruction.jump 0 := by decide
example : Instruction.add 1 2 3 = Instruction.add 1 2 3 := by decide +kernel

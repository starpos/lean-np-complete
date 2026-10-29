module

import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
# Part of the README example, with plain `import`s of the files it needs

`constProducer_eval` and the `Program.eval` simp of the README example (`Test/ReadmeExample.lean`)
with plain `import`s. The full README example, which needs `CookLevin`, is `Final/ReadmePlain`.
Expected: all ok.
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.RAMToTM NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

def constProducer : Program :=
  (Program.assign 0 (.const 4)).seq <|
  (Program.assign 1 (.const 2)).seq <|
  (Program.assign 4 (.const 0)).seq (Program.assign 5 (.const 1))

lemma constProducer_eval (σ : Store) :
    constProducer.eval σ = writeReg (writeReg (writeReg (writeReg σ 0 4) 1 2) 4 0) 5 1 := by
  simp [constProducer, Expr.eval]

example (x : Bits) : constProducer.eval (bitInputStore x) 1 = 2 := by
  simp [constProducer_eval, writeReg]

example (i : Nat) : bitInputStore [] (i + 1) = 0 := by simp [bitInputStore]

example (bits : Bits) (i : Nat) :
    ProgramBoundedIn (bits.length + 1) (bitInputStore bits) (Program.skip) := by
  trivial

example (bits : Bits) (i : Nat) :
    bitInputStore bits (i + 1) ≤ bits.length + 1 := by
  simp only [bitInputStore]; split <;> omega

example (n : Nat) : bitLen n ≤ n + 1 := bitLen_le_succ n

example (n : Nat) : (encodeNat n).length = n + 1 := NPComplete.BitEncoding.encodeNat_length n

module

public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.RAMToTM.Generic.Machine.DigitAdd

/-!
# `compile` (mutual) and `addRaw` (well-founded) from a `public import`

Expected: `simp [f]`, `unfold f`, `rw [f]` all ok with `public import`.
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.RAMToTM NPComplete.BoundedWhile NPComplete.BitCostRAM

example : compile .skip 0 0 = [] := by simp [compile]
example : compile .skip 0 0 = [] := by simp only [compile]
example (pc sb : Nat) : compile (.seq .skip .skip) pc sb = [] := by
  rw [compile]; simp [compile, codeLenP]
example (pc sb : Nat) : compile (.seq .skip .skip) pc sb = [] := by
  unfold compile; simp [compile, codeLenP]
example (pc sb : Nat) : compileScanList [] 0 .skip pc sb = [] := by simp [compileScanList]
example : addRaw [] [] false = [] := by simp [addRaw]
example : addRaw [] [] false = [] := by rw [addRaw]; simp
example : addRaw [] [] false = [] := by unfold addRaw; simp

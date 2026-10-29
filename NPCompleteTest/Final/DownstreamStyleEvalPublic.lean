module

public import NPComplete

/-!
# The same mutual and well-founded definition checks as `DownstreamStyleEval.lean`, with
`public import NPComplete`. Expected: everything ok (as a module importer).
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM
example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by simp [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by rw [Program.eval]
example (b : Program) (σ : Store) : loopEval b 0 σ = σ := by simp only [loopEval]
example (σ : Store) : (Program.seq .skip .skip).cost σ = 2 := by simp [Program.cost]
example : compile .skip 0 0 = [] := by simp [compile]
example : compile (.assign 2 (.eq (.reg 1) (.const 0))) 0 0 =
    [Instruction.loadImm 3 1, Instruction.load 1 3, Instruction.loadImm 2 0,
     Instruction.setIfEq 0 1 2, Instruction.loadImm 1 2, Instruction.store 0 1] := by
  simp [compile, compileExpr]
example : addRaw [] [] false = [] := by simp [addRaw]
example (pc sb : Nat) : compileScanList [] 0 .skip pc sb = [] := by simp [compileScanList]

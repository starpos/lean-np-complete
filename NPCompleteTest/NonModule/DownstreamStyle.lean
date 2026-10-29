import NPComplete

/-!
# Non-module importer comparison

This file exercises the library from a source file without a `module`
declaration. It serves as a control for separating module-boundary behavior
from ordinary access to the public API.
-/
-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM
example : compile .skip 0 0 = [] := by simp [compile]
example : addRaw [] [] false = [] := by simp [addRaw]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by simp [Program.eval]
example (a s i l : Nat) (h : 0 < s) : a ≤ NPComplete.arenaAddr a s i l := by
  unfold NPComplete.arenaAddr; omega
example (B : Nat) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) ↔ ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q := by
  simp only [ProgramBoundedIn]
def myProg : Program := .seq (.assign 5 (.const 1)) (.forN (.reg 0) (.assign 6 (.reg 5)))
example : myProg.Avoids (· = 7) := of_decide_eq_true (by rfl)
example : NPComplete.SAT.Literal.pos 1 ≠ .neg 1 := by decide

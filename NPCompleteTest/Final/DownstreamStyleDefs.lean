module

import NPComplete

/-!
# Structural and plain definitions through `import NPComplete`

`unfold arenaAddr`, `simp only [ProgramBoundedIn]`, `ExprBoundedIn`,
`ScanFree`, `bitInputStore`, and the `Avoids` + `of_decide_eq_true (by rfl)` certificate on a program
defined in the client (the client module's own definition, private by default, needs no `expose`).
Expected: all ok.
-/

-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM

example (a s i l : Nat) (h : 0 < s) : a ≤ NPComplete.arenaAddr a s i l := by
  unfold NPComplete.arenaAddr; omega
example (a s i l : Nat) : NPComplete.arenaAddr a s i l = a + s * i + l := by
  simp [NPComplete.arenaAddr]
example (B : Nat) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) ↔ ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q := by
  simp only [ProgramBoundedIn]
example (B : Nat) (σ : Store) (n : Nat) (h : n ≤ B) : ExprBoundedIn B σ (.const n) := by
  simp only [ExprBoundedIn]; exact h
example (p q : Program) : ScanFree (.seq p q) ↔ ScanFree p ∧ ScanFree q := by simp only [ScanFree]
example (bits : List Bool) : bitInputStore bits 0 = bits.length := by simp [bitInputStore]
example : NPComplete.SAT.Literal.pos 1 ≠ .neg 1 := by decide

def myProg : Program := .seq (.assign 5 (.const 1)) (.forN (.reg 0) (.assign 6 (.reg 5)))
example : myProg.Avoids (· = 7) := of_decide_eq_true (by rfl)
example : myProg.Avoids (· = 7) := by decide +kernel
example (σ : Store) : myProg.eval σ 7 = σ 7 :=
  (of_decide_eq_true (by rfl) : myProg.Avoids (· = 7)).eval_frame σ rfl

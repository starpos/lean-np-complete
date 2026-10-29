module

import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
import NPComplete.ArenaAddress

/-!
# Structural / non-recursive library definitions under a plain `import`

Expected: all ok for common client-side patterns such as `unfold arenaAddr`,
`simp only [ProgramBoundedIn]`, and `simp [bitInputStore]`. `ProgramBoundedIn` is defined in
`CompileExecBounded`, `arenaAddr` in `ArenaAddress`, and `bitInputStore` in `BoundedWhileDecider`.
-/

open NPComplete.RAMToTM NPComplete.BoundedWhile NPComplete.BitCostRAM

-- arenaAddr: unfold, simp, omega after unfold
example (a s i l : Nat) : NPComplete.arenaAddr a s i l = a + s * i + l := by
  unfold NPComplete.arenaAddr; rfl
example (a s i l : Nat) : NPComplete.arenaAddr a s i l = a + s * i + l := by
  simp [NPComplete.arenaAddr]
example (a s i l : Nat) : 0 ≤ NPComplete.arenaAddr a s i l := by unfold NPComplete.arenaAddr; omega
example : NPComplete.arenaAddr 1 2 3 4 = 11 := by decide
example : NPComplete.arenaAddr 1 2 3 4 = 11 := rfl
-- ProgramBoundedIn / ExprBoundedIn / ScanFree: simp only, show/change, rfl
example (B : Nat) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) ↔ ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q := by
  simp only [ProgramBoundedIn]
example (B : Nat) (σ : Store) (r : Nat) (e : Expr) :
    ProgramBoundedIn B σ (.assign r e) ↔ r ≤ B ∧ ExprBoundedIn B σ e := by
  simp only [ProgramBoundedIn]
example (B : Nat) (σ : Store) (n : Nat) : ExprBoundedIn B σ (.const n) = (n ≤ B) := by
  simp only [ExprBoundedIn]
example (B : Nat) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) = (ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q) :=
  rfl
example (B : Nat) (σ : Store) (p q : Program) (h : ProgramBoundedIn B σ (.seq p q)) :
    ProgramBoundedIn B σ p := h.1
example (p q : Program) : ScanFree (.seq p q) ↔ ScanFree p ∧ ScanFree q := by
  simp only [ScanFree]
-- a concrete boundedness claim
example (B : Nat) (σ : Store) (hB : 3 ≤ B) :
    ProgramBoundedIn B σ (.assign 1 (.const 3)) := by
  simp only [ProgramBoundedIn, ExprBoundedIn]
  omega
-- bitInputStore: a match-defined non-recursive def
example (bits : List Bool) : bitInputStore bits 0 = bits.length := by simp [bitInputStore]
example (bits : List Bool) : bitInputStore bits 0 = bits.length := rfl
example : bitInputStore [] 0 = 0 := by decide
-- Instruction (inductive) and RAM (structure) projections
example (r : RAM) : ({ r with pc := 3 } : RAM).pc = 3 := rfl
-- Bank is a function type
example (b : Bank) : b 0 = b 0 := rfl
example : emptyBank 3 = 0 := rfl

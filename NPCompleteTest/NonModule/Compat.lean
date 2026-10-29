import NPComplete.BoundedWhile.Frame
import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
import NPComplete.RAMToTM.Generic.Machine.DigitAdd
import NPComplete.ArenaAddress
import NPComplete.SAT.ThreeSAT

/-!
# Non-module importer (comparison for the `Pilot` tests)

A file without a `module` header, as a downstream package that has not adopted the module system, importing module-ised library files with
plain `import`. Expected: everything that fails from a plain-import module importer works here
(`simp [Program.eval]`, `simp [compile]`, `simp [addRaw]`), because a non-module importer sees all
bodies. Only the closed-term `decide` on `Program.eval` fails (irreducible, independent of the module system).
-/
-- Some `simp [f]` arguments are unnecessary on purpose: that they are accepted is part of what is tested.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM

example (σ : Store) : Program.skip.eval σ = σ := by simp only [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  simp [Program.eval]
example (σ : Store) (p q : Program) : (Program.seq p q).eval σ = q.eval (p.eval σ) := by
  rw [Program.eval]
example (σ : Store) : Program.skip.eval σ = σ := by unfold Program.eval; rfl
example (b : Program) (σ : Store) : loopEval b 0 σ = σ := by simp only [loopEval]
example (σ : Store) : (Program.seq .skip .skip).cost σ = 2 := by simp [Program.cost]
example : compile .skip 0 0 = [] := by simp [compile]
example : addRaw [] [] false = [] := by simp [addRaw]

def prog : Program :=
  .seq (.assign 5 (.const 1)) (.forN (.reg 0) (.assign 6 (.reg 5)))
example : prog.Avoids (· = 7) := by decide
example : prog.Avoids (· = 7) := by decide +kernel
example : prog.Avoids (· = 7) := of_decide_eq_true (by rfl)

example : NPComplete.SAT.Literal.pos 1 ≠ .neg 1 := by decide
example (a s i l : Nat) : NPComplete.arenaAddr a s i l = a + s * i + l := by unfold NPComplete.arenaAddr; rfl
example (B : Nat) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) ↔ ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q := by
  simp only [ProgramBoundedIn]
example : True := by
  fail_if_success (have _h : (Program.skip.eval emptyStore) 3 = 0 := by decide)
  trivial

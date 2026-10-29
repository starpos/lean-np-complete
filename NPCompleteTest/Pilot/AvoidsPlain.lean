module

import NPComplete.BoundedWhile.Frame
import NPCompleteTest.Pilot.Defs

/-!
# `Program.Avoids` certificates, plain `import` of Frame and of the exposed probe definitions

Expected: all ok: `decide`, `decide +kernel`, `of_decide_eq_true (by rfl)` (a common
downstream proof pattern), and ℕ-constant `decide` work when `Avoids`, its `Decidable` instance,
the program and its constants are all exposed. A program defined in the same module needs no `expose`.
-/

open NPComplete.BoundedWhile
open NPCompleteTest.Pilot.Defs

example : prog.Avoids (· = 7) := by decide
example : prog.Avoids (· = 7) := by decide +kernel
example : prog.Avoids (· = 7) := of_decide_eq_true (by rfl)
example : prog.Avoids (· = 7) := of_decide_eq_true (by decide +kernel)
example : uctCursorReg ≠ uctDoneReg := by decide
example : uctCursorReg ≠ uctDoneReg := by decide +kernel
-- using the certificate in a client-side frame lemma
example (σ : Store) : prog.eval σ 7 = σ 7 :=
  (of_decide_eq_true (by rfl) : prog.Avoids (· = 7)).eval_frame σ rfl
example : prog.WritesAvoid (· = 7) := (by decide +kernel : prog.Avoids (· = 7)).writesAvoid
example (σ : Store) : loopEval prog 3 σ 7 = σ 7 :=
  (by decide +kernel : prog.Avoids (· = 7)).loopEval_frame rfl 3 σ
-- library iff lemmas
example (P : Nat → Prop) (p q : Program) : (Program.seq p q).Avoids P ↔ p.Avoids P ∧ q.Avoids P := by
  simp only [Program.avoids_seq]
-- a program defined in this very module (private by default) and `decide` on it
def localProg : Program := .seq (.assign 1 (.const 2)) (.assign 3 (.reg 1))
example : localProg.Avoids (· = 4) := by decide
example : localProg.Avoids (· = 4) := by decide +kernel
example : localProg.Avoids (· = 4) := of_decide_eq_true (by rfl)
-- AvoidsAbove and directWrites are structural too
example : Program.directWrites (.assign 1 (.const 2)) = some [1] := by simp [Program.directWrites]
example : localProg.directWrites = some [1, 3] := by decide

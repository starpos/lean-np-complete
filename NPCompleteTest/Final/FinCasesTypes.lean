module

import NPComplete
import Mathlib.Tactic.FinCases

/-!
# `fin_cases` on the machine label and stack types, plain `import NPComplete`

Downstream proofs enumerate these label types by `fin_cases`, so a module importer must be able to
reduce their `Fintype` instances. Expected: `fin_cases` enumerates every constructor (for the empty
program, so that `regBound` and the register ranges reduce).
-/

open NPComplete.RAMToTM.Generic

example (x : Kg []) : x = x := by fin_cases x <;> rfl
example (x : CleanupPhase []) : x = x := by fin_cases x <;> rfl
example (x : Λg []) : x = x := by fin_cases x <;> rfl
example (x : EmitK []) : x = x := by fin_cases x <;> rfl
example (x : EmitCleanupPhase []) : x = x := by fin_cases x <;> rfl
example (x : MasterΛ []) : x = x := by fin_cases x <;> rfl

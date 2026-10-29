module

import NPComplete.BoundedWhile.Frame
import NPCompleteTest.Pilot.DefsHidden

/-!
# Certificates for a program whose definition is NOT exposed (`DefsHidden`)

Expected: `decide` / `decide +kernel` / `of_decide_eq_true (by rfl)` all FAIL, and
so does the ℕ-constant `decide`.
-/

open NPComplete.BoundedWhile
open NPCompleteTest.Pilot.Hidden

/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : prog.Avoids (· = 7) := by decide
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : prog.Avoids (· = 7) := by decide +kernel
/-- Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : prog.Avoids (· = 7) := of_decide_eq_true (by rfl)
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : uctCursorReg ≠ uctDoneReg := by decide

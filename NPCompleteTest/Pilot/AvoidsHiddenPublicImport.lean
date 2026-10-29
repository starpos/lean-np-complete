module

public import NPComplete.BoundedWhile.Frame
public import NPCompleteTest.Pilot.DefsHidden

/-!
# The same failing checks as `AvoidsHidden.lean`, but with `public import` of the hidden definitions.
Expected: still FAIL.
-/

open NPComplete.BoundedWhile
open NPCompleteTest.Pilot.Hidden
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : prog.Avoids (· = 7) := by decide +kernel

module

public import NPComplete.BoundedWhile.Frame
public import NPCompleteTest.Pilot.Defs

/-!
# The same `Avoids`-certificate checks as `AvoidsPlain.lean`, but with `public import` for both
imports. Expected: ok (`public import` changes nothing here).
-/

open NPComplete.BoundedWhile
open NPCompleteTest.Pilot.Defs
example : prog.Avoids (· = 7) := by decide +kernel
example : prog.Avoids (· = 7) := of_decide_eq_true (by rfl)
-- a public theorem whose statement names an imported program needs the public import
lemma prog_avoids : prog.Avoids (· = 7) := by decide +kernel

module
/-!
# Exposed deriving declarations

Lean-generated `DecidableEq` instances need to follow the visibility of their
parent declarations. This module isolates the `@[expose]` case across inductive
and structure declarations for a focused interface check.
-/
@[expose] public section
namespace NPCompleteTest.Pilot.DerivExpose
inductive C | r | g | b deriving DecidableEq
structure S where
  x : Nat
  c : C
  deriving DecidableEq
inductive T | leaf : Nat → T | node : T → T → T deriving DecidableEq
end NPCompleteTest.Pilot.DerivExpose

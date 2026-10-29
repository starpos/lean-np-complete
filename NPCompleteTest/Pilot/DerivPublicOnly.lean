module
/-!
# Public deriving without exposure

Without `@[expose]`, public declarations test a different visibility boundary
for compiler-generated instances. This module mirrors the exposed examples so
the section attribute's effect can be isolated across the same declaration
forms.
-/
public section
namespace NPCompleteTest.Pilot.DerivPublicOnly
inductive C | r | g | b deriving DecidableEq
structure S where
  x : Nat
  c : C
  deriving DecidableEq
inductive T | leaf : Nat → T | node : T → T → T deriving DecidableEq
end NPCompleteTest.Pilot.DerivPublicOnly

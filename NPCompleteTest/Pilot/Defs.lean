module

public import NPComplete.BoundedWhile.Basic

/-!
Test-side definitions, all exposed (`@[expose] public section`): the normal case for a client that
wants other modules to `decide` facts about its programs.
-/

@[expose] public section
open NPComplete.BoundedWhile
namespace NPCompleteTest.Pilot.Defs
def uctCursorReg : Nat := 5
def uctDoneReg : Nat := 6
def uctFreshReg : Nat := 7
def prog : Program :=
  .seq (.assign uctCursorReg (.const 1))
    (.forN (.reg 0) (.assign uctDoneReg (.reg uctCursorReg)))
end NPCompleteTest.Pilot.Defs

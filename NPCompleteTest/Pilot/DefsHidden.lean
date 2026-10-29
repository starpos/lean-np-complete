module

public import NPComplete.BoundedWhile.Basic

/-!
Same definitions as `Defs` but in a `public section` WITHOUT `@[expose]`: bodies are invisible to
importers.
-/

public section
open NPComplete.BoundedWhile
namespace NPCompleteTest.Pilot.Hidden
def uctCursorReg : Nat := 5
def uctDoneReg : Nat := 6
def uctFreshReg : Nat := 7
def prog : Program :=
  .seq (.assign uctCursorReg (.const 1))
    (.forN (.reg 0) (.assign uctDoneReg (.reg uctCursorReg)))
end NPCompleteTest.Pilot.Hidden

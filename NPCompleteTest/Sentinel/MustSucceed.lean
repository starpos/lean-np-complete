module

public import NPComplete.BoundedWhile.Basic

/-!
# Sentinel: a trivial module-system file in the library

Builds with the others, so `lake build NPCompleteTest` has at least one module whose whole content is
known to be correct. `scripts/check_importer_tests.sh` also builds it by name.
-/

example : (1 : Nat) = 1 := rfl

module

public import NPComplete.BoundedWhile.Basic

/-!
# Sentinel: an expected error is reported from a module-system file

If the build did not elaborate this file, or elaborated it with a different importer view, the pinned
error text would not match and the build would fail. The unguarded counterparts, which must make the
build fail, are in `NPCompleteTest/ShouldFail/` and are run by `scripts/check_importer_tests.sh`.
-/

/--
error: Tactic `decide` proved that the proposition
  1 = 2
is false
-/
#guard_msgs in
example : (1 : Nat) = 2 := by decide

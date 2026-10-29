module

public import NPComplete.BoundedWhile.Basic

/-!
# Must fail: a false `decide`

`scripts/check_importer_tests.sh` expects this file to be rejected with the text `proved that the
proposition`. A pass would mean that the build does not elaborate test files with a `module` header.
It is outside the globs of `NPCompleteTest`, so `lake build NPCompleteTest` never sees it.
-/

example : (1 : Nat) = 2 := by decide

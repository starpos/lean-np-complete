module

import NPComplete.Meta.ApiLayer

/-!
# The attribute with a plain `import NPComplete.Meta.ApiLayer`

Expected: `Unknown attribute` (the attribute implementation is only registered when
the module is loaded as meta). Checked with `#guard_msgs (substring := true)`.
-/

/-- Unknown attribute `[stable_api]` -/
#guard_msgs (substring := true) in
@[stable_api] def plainTagged : Nat := 1

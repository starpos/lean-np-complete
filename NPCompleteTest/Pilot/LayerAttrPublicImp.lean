module

public import NPComplete.Meta.ApiLayer

/-!
# `public import NPComplete.Meta.ApiLayer` (non-meta) and the attribute

Expected: `Unknown attribute`. A non-meta import, even a `public` one, does not load the attribute
implementation.
-/

/-- Unknown attribute `[stable_api]` -/
#guard_msgs (substring := true) in
@[stable_api] def pubImpTagged : Nat := 1

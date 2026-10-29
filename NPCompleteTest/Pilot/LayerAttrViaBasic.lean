module

public import NPComplete.BoundedWhile.Basic

/-!
# The attribute is not obtained transitively through `public import Basic`

`Basic` itself has `meta import ApiLayer`; a client that only imports `Basic` must add its own
`meta import`. Expected: `Unknown attribute`.
-/

/-- Unknown attribute `[stable_api]` -/
#guard_msgs (substring := true) in
@[stable_api] def viaBasicTagged : Nat := 1

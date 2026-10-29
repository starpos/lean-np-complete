module

meta import NPComplete.Meta.ApiLayer

/-!
# A tagged declaration outside the umbrella closure

`NPComplete` does not import this module. It exists so that `ApiLayersNegative.lean` can show
that `#check_api_umbrella` reports a tagged declaration found in an imported module that the
umbrella does not reach.
-/

@[expose] public section

namespace ApiLayerOutsideUmbrellaTest

/-- Tagged declaration that no umbrella import reaches. -/
@[stable_api] def outsideUmbrella : Nat := 0

end ApiLayerOutsideUmbrellaTest

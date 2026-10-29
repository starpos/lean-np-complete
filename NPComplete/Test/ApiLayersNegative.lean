module

meta import NPComplete.Meta.ApiLayer
public import NPComplete
meta import NPComplete.Meta.ApiLayerCheck
public import NPComplete.Test.ApiLayersOutsideUmbrella

/-!
# The layering checks fire on violations

Each declaration below is tagged and deliberately mentions a declaration of a layer it may not
depend on. `#guard_msgs` asserts the exact errors, so this module builds only while the checker
keeps detecting these three kinds of violation. The dummies live in their own module so that the
global check in `ApiLayers.lean` never sees them.

The umbrella check is exercised on two declarations outside the closure of `NPComplete`: one
defined in this module and one in the imported `ApiLayersOutsideUmbrella`.
-/

@[expose] public section

namespace ApiLayerNegativeTest

/-- Stable declaration whose type mentions an untagged type (reached through a constructor). -/
@[stable_api] lemma stableMentionsUntagged :
    NPComplete.CookLevin.ConstFalseState.start = NPComplete.CookLevin.ConstFalseState.start := rfl

/-- Stable declaration whose type mentions a construction declaration. -/
@[stable_api] def stableMentionsConstruction : Type :=
  NPComplete.RAMToTM.BoundedWhileDecider (fun _ : Unit => []) (fun _ => True) (fun _ => True)

/-- Construction declaration whose type mentions an untagged constant. -/
@[construction_api] def constructionMentionsUntagged : Type :=
  NPComplete.CookLevin.ConstFalseState

end ApiLayerNegativeTest

namespace NPComplete.Test.ApiLayerNegativeTest

private def internalPredicate : Prop := True

@[stable_api] private lemma stableMentionsPrivate : internalPredicate := by
  trivial

end ApiLayerNegativeTest

namespace ApiLayerNegativeTest

/--
error: stable_api declaration `ApiLayerNegativeTest.stableMentionsUntagged` mentions untagged `NPComplete.CookLevin.ConstFalseState` in its type
---
error: stable_api declaration `ApiLayerNegativeTest.stableMentionsConstruction` mentions construction_api `NPComplete.RAMToTM.BoundedWhileDecider` in its body
---
error: construction_api declaration `ApiLayerNegativeTest.constructionMentionsUntagged` mentions untagged `NPComplete.CookLevin.ConstFalseState` in its body
---
error: stable_api declaration `NPComplete.Test.ApiLayerNegativeTest.stableMentionsPrivate` mentions untagged `NPComplete.Test.ApiLayerNegativeTest.internalPredicate` in its type
-/
#guard_msgs in
#check_api_layers ApiLayerNegativeTest.stableMentionsUntagged
  ApiLayerNegativeTest.stableMentionsConstruction
  ApiLayerNegativeTest.constructionMentionsUntagged
  NPComplete.Test.ApiLayerNegativeTest.stableMentionsPrivate

/--
error: tagged declaration `ApiLayerNegativeTest.stableMentionsUntagged` is defined in `NPComplete.Test.ApiLayersNegative`, which `NPComplete` does not import
---
error: tagged declaration `ApiLayerOutsideUmbrellaTest.outsideUmbrella` is defined in `NPComplete.Test.ApiLayersOutsideUmbrella`, which `NPComplete` does not import
-/
#guard_msgs in
#check_api_umbrella ApiLayerNegativeTest.stableMentionsUntagged
  ApiLayerOutsideUmbrellaTest.outsideUmbrella

end ApiLayerNegativeTest

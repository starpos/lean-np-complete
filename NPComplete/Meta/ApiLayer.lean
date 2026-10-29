module

public meta import Lean.Attributes
import Lean.Attributes

/-!
# API layer tags

Declarations of the public surface carry one of two tags; an untagged declaration is internal.

* `stable_api`: a promise that the statement is kept. Changing it is a breaking change, and
  `NPComplete/Test/StableApi.lean` pins every such statement so that a change fails the build.
* `construction_api`: usable by clients but allowed to change. It may mention stable and
  construction declarations in its statement, never internal ones.

This module imports only `Lean.Attributes` so that any module may import it to tag its
declarations. The checker that enforces the layering lives in `ApiLayerCheck.lean`.
-/

open Lean

public section

namespace NPComplete.ApiLayer

initialize stableApiAttr : TagAttribute ←
  registerTagAttribute `stable_api
    "Stable API: the statement is a compatibility promise and is pinned by a test."

initialize constructionApiAttr : TagAttribute ←
  registerTagAttribute `construction_api
    "Construction API: usable by clients, may change; may mention only stable or construction declarations."

end NPComplete.ApiLayer

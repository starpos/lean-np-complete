module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.ApiLayerCheck
public import NPComplete.BoundedWhile.Basic
public import NPComplete.BitCostRAM

/-!
# Using the layer attributes from a client module

Expected: with `meta import NPComplete.Meta.ApiLayer` the attributes `stable_api` /
`construction_api` are available and `#check_api_layers` (from `meta import ApiLayerCheck`)
accepts a compliant client declaration and rejects a stable declaration that mentions a
construction_api declaration (`Bank`).
-/

open NPComplete.BoundedWhile

namespace NPCompleteTest.Pilot.Layer
public section
@[stable_api] def okStable (σ : Store) : Store := writeReg σ 0 1
@[construction_api] def okConstruction (σ : Store) : Store := okStable σ
@[stable_api] def badStable : NPComplete.BitCostRAM.Bank := NPComplete.BitCostRAM.emptyBank
end
end NPCompleteTest.Pilot.Layer

-- compliant: no output
#guard_msgs in
#check_api_layers NPCompleteTest.Pilot.Layer.okStable NPCompleteTest.Pilot.Layer.okConstruction

-- violation: stable mentions a construction_api type
/--
error: stable_api declaration `NPCompleteTest.Pilot.Layer.badStable` mentions construction_api `NPComplete.BitCostRAM.Bank` in its type
-/
#guard_msgs in
#check_api_layers NPCompleteTest.Pilot.Layer.badStable

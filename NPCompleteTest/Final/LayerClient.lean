module

public import NPComplete
meta import NPComplete.Meta.ApiLayer
public meta import NPComplete.Meta.ApiLayerCheck

/-!
# A client that tags its own declarations and runs the checker, via the umbrella

Expected: through `public import NPComplete` the checker really sees the library's tagged declarations
(the count is computed and must be at least 240, so a silent 0-declaration pass cannot go unnoticed);
the global `#check_api_layers` is silent on the clean library; a compliant client declaration passes; a
stable declaration mentioning a construction_api type is reported; `#check_api_umbrella` with explicit
names reports the client declaration as outside the umbrella.

`public import` is needed because the client's own public declarations name `Store` and `Bank`.
-/

open NPComplete.BoundedWhile Lean Elab Command

namespace NPCompleteTest.Final.Layer
public section
@[stable_api] def okStable (σ : Store) : Store := writeReg σ 0 1
@[stable_api] def badStable : NPComplete.BitCostRAM.Bank := NPComplete.BitCostRAM.emptyBank
end
end NPCompleteTest.Final.Layer

/-- Number of tagged declarations the checker sees from this importer. -/
elab "#count_tagged" : command => do
  let env ← getEnv
  let a := NPComplete.ApiLayer.taggedNames NPComplete.ApiLayer.stableApiAttr env
  let b := NPComplete.ApiLayer.taggedNames NPComplete.ApiLayer.constructionApiAttr env
  let lib := (a ++ b).filter fun n => !(`NPCompleteTest.Final.Layer).isPrefixOf n
  if lib.size < 240 then
    throwError "checker sees only {lib.size} tagged library declarations ({a.size} stable, {b.size} construction in total)"
  logInfo m!"tagged library declarations seen: {lib.size} (total stable {a.size}, construction {b.size})"

#count_tagged

-- the library alone is clean: no output (with a non-empty universe, see the count above)
#guard_msgs in
#check_api_layers NPComplete.BoundedWhile.eval_seq NPComplete.CookLevin.sat_NPComplete

#guard_msgs in
#check_api_layers NPCompleteTest.Final.Layer.okStable

/--
error: stable_api declaration `NPCompleteTest.Final.Layer.badStable` mentions construction_api `NPComplete.BitCostRAM.Bank` in its type
-/
#guard_msgs in
#check_api_layers NPCompleteTest.Final.Layer.badStable

/--
error: tagged declaration `NPCompleteTest.Final.Layer.okStable` is defined in `NPCompleteTest.Final.LayerClient`, which `NPComplete` does not import
-/
#guard_msgs in
#check_api_umbrella NPCompleteTest.Final.Layer.okStable

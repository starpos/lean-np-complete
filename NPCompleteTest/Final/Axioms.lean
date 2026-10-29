module

import NPComplete

/-!
# `#print axioms` of the two main theorems from a module importer

Expected: only `propext`, `Classical.choice`, `Quot.sound` (checked with `#guard_msgs`).
-/

open NPComplete.CookLevin

/-- info: 'NPComplete.CookLevin.sat_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sat_NPComplete

/-- info: 'NPComplete.CookLevin.threeSAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threeSAT_NPComplete

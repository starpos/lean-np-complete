module

public import NPComplete
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransWitness
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafAtLeastOneCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafCheck
public import NPComplete.CookLevin.ReductionProg.GeneratorDecider
public import NPComplete.Test.ClauseLayoutWitnesses
public import NPComplete.Test.CookLevinDropWitnesses
public import NPComplete.Test.GeneratorBoundedWitnesses
public import NPComplete.Test.GeneratorWitnesses
public import NPComplete.Test.ThreeSatDecodeWitnesses

/-!
# Modules kept out of the umbrella

Collects modules intentionally outside `NPComplete`'s import closure, including non-vacuity checks,
test witnesses, and packagings unused by main theorems. `Test/ApiLayers.lean` imports this module
so that the API checks see these modules too: an environment contains only the modules in the
import closure of the checking file, so a tagged declaration placed in one of them would otherwise
go unnoticed instead of being reported as lying outside the umbrella.
-/

module

public import NPComplete

--- Non-vacuity checks on the clause-family writers and their leaf combinators, and the clause
--- generator packaged as a `BoundedWhileDecider`; no main theorem imports them. They are listed
--- in `Test/Witnesses.lean` so that the API checks see them as well.
public import NPComplete.Test.Witnesses

--- Enforcement of the API layering: the checker over every tagged declaration, a negative test
--- that the checker fires, and the pinned statements of the stable API. No library module
--- imports these, so library consumers do not build them.
public import NPComplete.Test.ApiLayers
public import NPComplete.Test.ApiLayersNegative
public import NPComplete.Test.ApiLayersOutsideUmbrella
public import NPComplete.Test.StableApi
public import NPComplete.Test.ReadmeExample

/-!
# Additional build coverage

Some witness and test modules lie outside the import closure of `NPComplete`. This module imports
the root plus those remaining checks so `NPComplete.Extra` builds both sets without extending the
library's public import closure.
-/

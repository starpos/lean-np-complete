module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numeral applied to a store in a contract statement

Expected: rejected with `a numeral applied to a `Store``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageStoreNumeralStmt

@[stage_contract] lemma c (σ : Store) : σ 22 = σ 22 := rfl

end NPCompleteTest.ShouldFail.StageStoreNumeralStmt

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageStoreNumeralStmt

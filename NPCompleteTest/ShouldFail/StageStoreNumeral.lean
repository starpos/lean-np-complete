module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numeral applied to a store in a fact

Expected: rejected with `a numeral applied to a `Store``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageStoreNumeral

@[stage_boundary] def accIsTwo : Store → Prop := fun σ => σ 1 = 2

end NPCompleteTest.ShouldFail.StageStoreNumeral

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageStoreNumeral

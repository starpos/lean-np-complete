module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a boundary mentions an unchecked declaration

Expected: rejected with `mentions stage_unchecked`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageUncheckedMention

@[stage_unchecked] def legacy : Program := .assign 1 (.const 2)

@[stage_boundary] def viaLegacy : Program := legacy.seq (bump lay)

end NPCompleteTest.ShouldFail.StageUncheckedMention

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageUncheckedMention

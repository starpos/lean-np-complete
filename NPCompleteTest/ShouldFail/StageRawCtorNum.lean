module

public import NPComplete
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a raw constructor called with numeric registers

Expected: rejected with `mentions the raw constructor `NPComplete.RAMToTM.writeUnaryProgAt``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM

namespace NPCompleteTest.ShouldFail.StageRawCtorNum

@[stage_boundary] def out : Program := writeUnaryProgAt 100 13 21

end NPCompleteTest.ShouldFail.StageRawCtorNum

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageRawCtorNum

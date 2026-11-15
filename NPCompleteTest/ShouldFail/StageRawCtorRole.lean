module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a raw constructor called with layout roles

The arguments are roles of a layout, so no register number appears; the raw constructor itself is
still forbidden at a boundary, which is what the layout wrapper exists for.

Expected: rejected with `mentions the raw constructor `NPComplete.RAMToTM.writeUnaryProgAt``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageRawCtorRole

@[stage_boundary] def out : Program := writeUnaryProgAt 100 (lay.reg .acc) (lay.reg .cnt)

end NPCompleteTest.ShouldFail.StageRawCtorRole

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageRawCtorRole

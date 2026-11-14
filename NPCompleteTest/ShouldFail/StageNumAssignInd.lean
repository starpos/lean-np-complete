module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numeric address of `assignInd` in a boundary program

Expected: rejected with `a numeric address in `Program.assignInd``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageNumAssignInd

@[stage_boundary] def p : Program := .assignInd (.const 200) (.const 2)

end NPCompleteTest.ShouldFail.StageNumAssignInd

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageNumAssignInd

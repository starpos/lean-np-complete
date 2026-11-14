module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numeric assignment target in a boundary program

Expected: rejected with `a numeric register in the target of `Program.assign``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageNumAssign

@[stage_boundary] def p : Program := .assign 1 (.const 2)

end NPCompleteTest.ShouldFail.StageNumAssign

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageNumAssign

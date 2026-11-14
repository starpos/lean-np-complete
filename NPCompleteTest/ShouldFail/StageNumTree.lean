module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numbered program tree re-created in a boundary

Expected: rejected with `a numeric register in the target of `Program.assign``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageNumTree

@[stage_boundary] def numberedBump : Program :=
  .assign 1 (.add (.reg 1) (.const 2))

end NPCompleteTest.ShouldFail.StageNumTree

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageNumTree

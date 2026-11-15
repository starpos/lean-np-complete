module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: conflicting defaults for one namespace

Expected: rejected with `conflicting defaults`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageDefaultConflict

stage_default boundary

stage_default contract

end NPCompleteTest.ShouldFail.StageDefaultConflict

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageDefaultConflict

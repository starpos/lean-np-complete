module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a concrete store passed to a boundary

Expected: rejected with `a closed `Store` passed as an argument`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageConcreteStore

@[stage_boundary] def ready : Prop := (accIs lay 1).holds (fun _ => 1)

end NPCompleteTest.ShouldFail.StageConcreteStore

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageConcreteStore

module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a store built by a lambda in a boundary definition

Expected: rejected with `builds a `Store` by a lambda`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageBuildsStore

@[stage_boundary] def blank : Store := fun _ => 0

end NPCompleteTest.ShouldFail.StageBuildsStore

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageBuildsStore

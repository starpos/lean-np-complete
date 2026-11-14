module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: an implementation evaluation lemma used from a boundary

Expected: rejected with `mentions stage_impl `NPCompleteTest.Final.StageFix.bump_eval``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageImplEval

@[stage_boundary] lemma useEval (σ : Store) : True :=
  (fun _ => trivial) (bump_eval lay σ)

end NPCompleteTest.ShouldFail.StageImplEval

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageImplEval

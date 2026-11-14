module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: an evaluation unfolding lemma in a composition

Expected: rejected with `mentions the raw store operation `NPComplete.BoundedWhile.eval_seq``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageEvalLemma

@[stage_boundary] lemma twiceEval (R : RegLayout Role) (σ : Store) :
    ((bump R).seq (bump R)).eval σ = (bump R).eval ((bump R).eval σ) :=
  eval_seq _ _ _

end NPCompleteTest.ShouldFail.StageEvalLemma

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageEvalLemma

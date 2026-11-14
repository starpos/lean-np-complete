module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: the adapter used from a boundary

Expected: rejected with `mentions stage_adapter `NPComplete.RAMToTM.LayoutStage.ofSpec``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageAdapterBoundary

@[stage_boundary] lemma viaAdapter (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 ≤ B) :
    LayoutStage R B (bump R) (accIs R n) (accIs R (n + 2)) (accFoot R) :=
  LayoutStage.ofSpec (bump_spec R hB hn)

end NPCompleteTest.ShouldFail.StageAdapterBoundary

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageAdapterBoundary

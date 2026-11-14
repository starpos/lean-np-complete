module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a raw contract entry used from a boundary

Expected: rejected with `mentions the raw store operation `NPComplete.RAMToTM.LayoutSpec.assign``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageRawEntry

@[stage_boundary] lemma rawAssign (R : RegLayout Role) {B : ℕ} (hr : R.reg .acc ≤ B) :
    LayoutSpec R B (fun _ => True) (.assign (R.reg .acc) (.const 0)) (accFoot R)
      (fun σ => σ (R.reg .acc) = 0) :=
  LayoutSpec.assign hr (fun _ _ => by simp [ExprBoundedIn]) (fun σ _ => by
    simp [Expr.eval, writeReg])

end NPCompleteTest.ShouldFail.StageRawEntry

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageRawEntry

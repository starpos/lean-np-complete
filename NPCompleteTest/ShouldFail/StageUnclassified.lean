module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a declaration without classification

Expected: rejected with `is not classified`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageUnclassified

def helper : ℕ := 3

end NPCompleteTest.ShouldFail.StageUnclassified

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageUnclassified

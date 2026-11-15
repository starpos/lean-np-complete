module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a lenient default must be spelled `stage_default_free`

Expected: rejected with `stage_default_free`.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageDefaultLenient

stage_default impl

end NPCompleteTest.ShouldFail.StageDefaultLenient

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageDefaultLenient

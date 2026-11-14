module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: `writeReg` in a boundary statement

Expected: rejected with `mentions the raw store operation `NPComplete.BoundedWhile.writeReg``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageWriteReg

@[stage_boundary] def after (σ : Store) : Store := writeReg σ (lay.reg .acc) 3

end NPCompleteTest.ShouldFail.StageWriteReg

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageWriteReg

module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: the same violation moved into a helper definition

Expected: rejected with `a numeral applied to a `Store``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageStoreNumeralHelper

@[stage_boundary] def readAcc (σ : Store) : ℕ := σ 1

@[stage_boundary] def accIsTwo (σ : Store) : Prop := readAcc σ = 2

end NPCompleteTest.ShouldFail.StageStoreNumeralHelper

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageStoreNumeralHelper

module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a boundary declaration under a default mentions an implementation

Expected: rejected with `mentions stage_impl`.  The default classification of the
mentioned declaration is as visible to the mention rule as a tag would be.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageDefaultMention

stage_default_free impl

def legacy : Program := bump lay

end NPCompleteTest.ShouldFail.StageDefaultMention

namespace NPCompleteTest.ShouldFail.StageDefaultMentionBoundary

open NPCompleteTest.ShouldFail.StageDefaultMention

stage_default boundary

def p : Program := legacy.seq legacy

end NPCompleteTest.ShouldFail.StageDefaultMentionBoundary

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageDefaultMention
#check_stage_discipline ns NPCompleteTest.ShouldFail.StageDefaultMentionBoundary

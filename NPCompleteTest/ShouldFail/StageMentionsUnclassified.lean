module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a boundary that uses an unclassified declaration of its namespace

Expected: rejected with `mentions unclassified `NPCompleteTest.ShouldFail.StageMentionsUnclassified.hidden``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageMentionsUnclassified

def hidden : Program := bump lay

@[stage_boundary] def viaHidden : Program := hidden

end NPCompleteTest.ShouldFail.StageMentionsUnclassified

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageMentionsUnclassified

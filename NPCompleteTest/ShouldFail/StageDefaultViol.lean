module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a violation inside a `stage_default boundary` scope

Expected: rejected with `a numeric register in `Expr.reg``.  The default is enforced as
`stage_boundary`, not a way to skip the check.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageDefaultViol

stage_default boundary

def p : Program :=
  .assign (lay.reg .acc) (.add (.reg 1) (.const 2))

end NPCompleteTest.ShouldFail.StageDefaultViol

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageDefaultViol

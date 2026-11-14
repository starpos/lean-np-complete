module

public import NPComplete
public import NPCompleteTest.Final.StageDiscipline
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a numeric `Expr.reg` in a boundary program

Expected: rejected with `a numeric register in `Expr.reg``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout
open NPCompleteTest.Final.StageFix

namespace NPCompleteTest.ShouldFail.StageNumReg

@[stage_boundary] def p : Program :=
  .assign (lay.reg .acc) (.add (.reg 1) (.const 2))

end NPCompleteTest.ShouldFail.StageNumReg

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageNumReg

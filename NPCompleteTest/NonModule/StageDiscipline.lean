import NPComplete
import NPComplete.Meta.StageDiscipline
import NPComplete.Meta.StageDisciplineCheck

/-!
# `#check_stage_discipline` from a non-module importer

The tags and the checker work from a file without a `module` header: a clean layout, program and
contract pass.
-/

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout

namespace NPCompleteTest.NonModule.StageDisc

@[stage_layout] inductive Role | acc | aux
  deriving DecidableEq

@[stage_layout] def Role.list : List Role := [.acc, .aux]

@[stage_layout] lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

@[stage_layout] def lay : RegLayout Role :=
  ⟨4, ⟨fun | .acc => 1 | .aux => 2, pairwise_ne_injective Role.mem_list (by decide)⟩⟩

@[stage_boundary] def clear (R : RegLayout Role) : Program := .assign (R.reg .acc) (.const 0)

@[stage_boundary] def clearStd : Program := clear lay

end NPCompleteTest.NonModule.StageDisc

#check_stage_discipline ns NPCompleteTest.NonModule.StageDisc

module

public import NPComplete
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a raw-constructor lemma called with layout roles

The registers of the call are roles of a layout, so no register number appears and the numeric
checks see nothing; the statement of the lemma still shows the program of the raw constructor,
which is what the check rejects.  The wrapper's restated contract is what a boundary calls.

Expected: rejected with `mentions the raw-constructor lemma `NPComplete.RAMToTM.readUnaryProgAt_frame``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout

namespace NPCompleteTest.ShouldFail.StageRawCtorLemmaRole

@[stage_layout] inductive Role | c | k | d | lr
  deriving DecidableEq

@[stage_layout] def Role.list : List Role := [.c, .k, .d, .lr]

@[stage_layout] lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

@[stage_layout] def lay : RegLayout Role :=
  ⟨20, ⟨fun | .c => 10 | .k => 19 | .d => 13 | .lr => 3,
    pairwise_ne_injective Role.mem_list (by decide)⟩⟩

@[stage_boundary] lemma out {σ : Store} (r : ℕ) (hc : r ≠ lay.reg .c) (hk : r ≠ lay.reg .k)
    (hd : r ≠ lay.reg .d) :
    (readUnaryProgAtL lay .c .k .d .lr).eval σ r = σ r :=
  readUnaryProgAt_frame (lay.reg .c) (lay.reg .k) (lay.reg .d) (lay.reg .lr) r σ hc hk hd

end NPCompleteTest.ShouldFail.StageRawCtorLemmaRole

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageRawCtorLemmaRole

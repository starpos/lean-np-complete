module

public import NPComplete
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Stage discipline: a raw-constructor lemma called with numeric registers

The statement names only the layout wrapper, so the raw-constructor lemma in the proof used to be
invisible: its numeric register arguments are plain data of the proof term.  The statement of the
lemma shows the program of the raw constructor, so the check now rejects the mention.

Expected: rejected with `mentions the raw-constructor lemma `NPComplete.RAMToTM.readUnaryProgAt_frame``.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout

namespace NPCompleteTest.ShouldFail.StageRawCtorLemmaNum

@[stage_layout] inductive Role | c | k | d | lr
  deriving DecidableEq

@[stage_layout] def Role.list : List Role := [.c, .k, .d, .lr]

@[stage_layout] lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

@[stage_layout] def lay : RegLayout Role :=
  ⟨20, ⟨fun | .c => 10 | .k => 19 | .d => 13 | .lr => 3,
    pairwise_ne_injective Role.mem_list (by decide)⟩⟩

@[stage_boundary] lemma out {σ : Store} (r : ℕ) (hc : r ≠ 10) (hk : r ≠ 19) (hd : r ≠ 13) :
    (readUnaryProgAtL lay .c .k .d .lr).eval σ r = σ r :=
  readUnaryProgAt_frame 10 19 13 3 r σ hc hk hd

end NPCompleteTest.ShouldFail.StageRawCtorLemmaNum

#check_stage_discipline ns NPCompleteTest.ShouldFail.StageRawCtorLemmaNum

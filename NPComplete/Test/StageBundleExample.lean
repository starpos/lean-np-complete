module

public import NPComplete
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# A bundled stage construction under `#check_stage_discipline`

One implementation stage (`bump`: add two to a register), a loop that runs it, a framed copy of
it beside a passive fact, and a consequence, all composed as `LayoutStage`s.  The implementation
proves the contract on raw stores and imports it by `LayoutStage.ofSpec`; the compositions name
only facts, footprints and the published stage.  The checker accepts the file as written.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout

namespace NPComplete.Test.StageBundle

@[stage_layout] inductive Role | acc | aux | tmp
  deriving DecidableEq

@[stage_layout] def Role.list : List Role := [.acc, .aux, .tmp]

@[stage_layout] lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

@[stage_layout] def lay : RegLayout Role :=
  ⟨8, ⟨fun | .acc => 3 | .aux => 4 | .tmp => 5,
    pairwise_ne_injective Role.mem_list (by decide)⟩⟩

@[stage_boundary] def bump (R : RegLayout Role) : Program :=
  .assign (R.reg .acc) (.add (.reg (R.reg .acc)) (.const 2))

@[stage_boundary] def accIs (R : RegLayout Role) (v : ℕ) : LayoutFact R := LayoutFact.reg .acc v

@[stage_boundary] def auxIs (R : RegLayout Role) (v : ℕ) : LayoutFact R := LayoutFact.reg .aux v

@[stage_boundary] def accFoot (R : RegLayout Role) : Foot R := Foot.regsOnly {.acc}

@[stage_impl] lemma bump_spec (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B) (hn : n + 2 ≤ B) :
    LayoutSpec R B (accIs R n).holds (bump R) (accFoot R) (accIs R (n + 2)).holds := by
  refine LayoutSpec.assign (by have := R.reg_lt_top .acc; omega) (fun σ h => ?_) (fun σ h => ?_)
  · simp only [accIs, LayoutFact.holds_reg] at h
    have := R.reg_lt_top .acc
    simp [ExprBoundedIn, Expr.eval, h]
    omega
  · simp only [accIs, LayoutFact.holds_reg] at h ⊢
    simp [Expr.eval, writeReg, h]

@[stage_contract] lemma bump_stage (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 ≤ B) :
    LayoutStage R B (bump R) (accIs R n) (accIs R (n + 2)) (accFoot R) :=
  LayoutStage.ofSpec (bump_spec R hB hn)

@[stage_boundary] lemma bump_twice (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 4 ≤ B) :
    LayoutStage R B ((bump R).seq (bump R)) (accIs R n) (accIs R (n + 2 + 2))
      ((accFoot R).union (accFoot R)) :=
  (bump_stage R hB (by omega)).seq (bump_stage R hB hn)

@[stage_boundary] lemma bump_framed (R : RegLayout Role) {B n m : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 ≤ B) :
    LayoutStage R B (bump R) ((accIs R n).and (auxIs R m)) ((accIs R (n + 2)).and (auxIs R m))
      (accFoot R) :=
  (bump_stage R hB hn).frame (auxIs R m) (by
    simp only [auxIs, LayoutFact.reg_foot_sep_iff, accFoot, Foot.regs_regsOnly]
    decide)

@[stage_boundary] lemma bump_loop (R : RegLayout Role) {B n N : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 * N ≤ B) (hN : N ≤ B) :
    LayoutStage R B (Program.forN (.const N) (bump R)) (accIs R n) (accIs R (n + 2 * N))
      (accFoot R) :=
  LayoutStage.forNConst (I := fun j => accIs R (n + 2 * j)) (Wj := fun _ => accFoot R) hN
    (fun _ h => h)
    (fun j hj => (bump_stage R hB (by omega)))
    (fun _ _ => ⟨subset_rfl, subset_rfl⟩)

@[stage_boundary] lemma bump_weakened (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 ≤ B) :
    LayoutStage R B (bump R) (accIs R n) (accIs R (n + 2)) (Foot.regsOnly {.acc, .tmp}) :=
  (bump_stage R hB hn).weaken (fun _ h => h)
    (Foot.regsOnly_le_iff.2 (by simp)) (fun _ h => h)

@[stage_boundary] def bumpStd : Program := bump lay

@[stage_boundary] lemma bumpStd_stage {B n : ℕ} (hB : lay.top ≤ B) (hn : n + 2 ≤ B) :
    LayoutStage lay B bumpStd (accIs lay n) (accIs lay (n + 2)) (accFoot lay) :=
  bump_stage lay hB hn

end NPComplete.Test.StageBundle

#check_stage_discipline ns NPComplete.Test.StageBundle

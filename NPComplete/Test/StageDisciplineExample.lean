module

public import NPComplete
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Example of a stage construction that passes `#check_stage_discipline`

A positive example: a layout, a
program written against it, an evaluation formula and a contract proved in the implementation,
facts and a composition in the boundary.  The canonical program of the numbered store is an alias
of the layout version; the data value `.const 2` and the iteration count are allowed.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BoundedWhile.RegLayout

namespace NPComplete.Test.StageFix

@[stage_layout] inductive Role | cnt | acc | tmp
  deriving DecidableEq

@[stage_layout] def Role.list : List Role := [.cnt, .acc, .tmp]

@[stage_layout] lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

@[stage_layout] def lay : RegLayout Role :=
  ⟨8, ⟨fun | .cnt => 0 | .acc => 1 | .tmp => 2,
    pairwise_ne_injective Role.mem_list (by decide)⟩⟩

@[stage_layout] lemma lay_reg_acc : lay.reg .acc = 1 := rfl

@[stage_boundary] def bump (R : RegLayout Role) : Program :=
  .assign (R.reg .acc) (.add (.reg (R.reg .acc)) (.const 2))

@[stage_boundary] def bumpTwice (R : RegLayout Role) : Program := (bump R).seq (bump R)

@[stage_boundary] def bumpStd : Program := bump lay

@[stage_boundary] def loopStd : Program := .forN (.const 3) (bump lay)

@[stage_boundary] def accIs (R : RegLayout Role) (v : ℕ) : LayoutFact R := LayoutFact.reg .acc v

@[stage_boundary] def accFoot (R : RegLayout Role) : Foot R := Foot.regsOnly {.acc}

@[stage_impl] lemma bump_eval (R : RegLayout Role) (σ : Store) :
    (bump R).eval σ = writeReg σ (R.reg .acc) (σ (R.reg .acc) + 2) := by
  simp [bump, eval_assign, Expr.eval]

@[stage_contract] lemma bump_spec (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 ≤ B) :
    LayoutSpec R B (accIs R n).holds (bump R) (accFoot R) (accIs R (n + 2)).holds := by
  refine LayoutSpec.assign (by have := R.reg_lt_top .acc; omega) (fun σ h => ?_) (fun σ h => ?_)
  · simp only [accIs, LayoutFact.holds_reg] at h
    have := R.reg_lt_top .acc
    simp [ExprBoundedIn, Expr.eval, h]
    omega
  · simp only [accIs, LayoutFact.holds_reg] at h ⊢
    simp [Expr.eval, writeReg, h]

@[stage_boundary] lemma bumpTwice_spec (R : RegLayout Role) {B n : ℕ} (hB : R.top ≤ B)
    (hn : n + 2 + 2 ≤ B) :
    LayoutSpec R B (accIs R n).holds (bumpTwice R) ((accFoot R).union (accFoot R))
      (accIs R (n + 2 + 2)).holds :=
  (bump_spec R hB (by omega)).seq (bump_spec R hB hn)

end NPComplete.Test.StageFix

#check_stage_discipline ns NPComplete.Test.StageFix

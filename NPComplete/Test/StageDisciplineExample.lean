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

@[stage_boundary] def writeStd : Program := writeUnaryProgAtL lay 100 .acc .cnt

@[stage_contract] lemma writeStd_scanFree : ScanFree writeStd :=
  scanFree_writeUnaryProgAtL (R := lay) 100 .acc .cnt

/-- WHY THIS LEMMA: a boundary derives facts from the wrapper's restated contract on layout
roles, never from the raw constructor's lemmas. -/
@[stage_boundary] lemma writeStd_frame {σ : Store} (hck : Role.acc ≠ Role.cnt)
    (hc : lay.reg .acc < 100 + σ (lay.reg .acc)) (hk : lay.reg .cnt < 100 + σ (lay.reg .acc))
    (r : ℕ) (hr : r ≠ lay.reg .acc)
    (hout : r < 100 + σ (lay.reg .acc) ∨ 100 + σ (lay.reg .acc) + σ (lay.reg .cnt) + 1 ≤ r) :
    writeStd.eval σ r = σ r :=
  writeUnaryProgAtL_frame (R := lay) hck hc hk r hr hout

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

namespace NPComplete.Test.StageDefault

open NPComplete.Test.StageFix

/-!
A positive example for `stage_default`: everything untagged below is held to `stage_boundary`,
and the exceptions carry individual tags.  The mention rule sees the default of `twice` exactly
as it would see a `stage_boundary` tag, and the `stage_impl` exception `legacy` is never
mentioned from the boundary.
-/

stage_default boundary

def twice : Program := bumpTwice lay

def composed : Program := twice.seq twice

@[stage_impl] def legacy : Program := bump lay

lemma composed_spec {B n : ℕ} (hB : lay.top ≤ B) (hn : n + 2 + 2 + 2 + 2 ≤ B) :
    LayoutSpec lay B (accIs lay n).holds composed
      (((accFoot lay).union (accFoot lay)).union ((accFoot lay).union (accFoot lay)))
      (accIs lay (n + 2 + 2 + 2 + 2)).holds :=
  (bumpTwice_spec (n := n) lay hB (by omega)).seq
    (bumpTwice_spec (n := n + 2 + 2) lay hB (by omega))

end NPComplete.Test.StageDefault

#check_stage_discipline ns NPComplete.Test.StageDefault

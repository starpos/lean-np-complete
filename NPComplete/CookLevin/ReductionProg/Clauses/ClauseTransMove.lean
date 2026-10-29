module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.Tableau

/-!
`nextIdx` is the one place in the reduction where a clause's *shape* depends on a
run-time comparison rather than on a table entry: a move off either end of the
window has no successor position, and the transition family emits a forbidding
clause instead of an implying one.

A `forN` body cannot branch on `Option`, so the producer needs the same
information as two arithmetic values — a guard saying whether a successor exists,
and the successor itself, read only when the guard holds.  This file establishes
that both are expressible, which is what lets the transition family's innermost
level be an `ifNZ` over the guard.

Directions are numbered as `transArg2` numbers them, left `0` and right `1`, so
the guard and the value are single expressions over that number rather than a
case split the program would have to duplicate.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## The boundary tests are comparisons

Both directions' `none` cases are a single comparison, which is the fragment the
expression language provides. -/

lemma nextIdx_left (W p : ℕ) :
    nextIdx W p Turing.Dir.left = if 0 < p then some (p - 1) else none := by
  unfold nextIdx
  by_cases h : p = 0
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right h]; simp; omega

lemma nextIdx_right (W p : ℕ) :
    nextIdx W p Turing.Dir.right = if p + 1 < W then some (p + 1) else none := rfl

/-- The direction as `transArg2` numbers it. -/
def dirOfNat (k : ℕ) : Turing.Dir := if k = 0 then Turing.Dir.left else Turing.Dir.right

lemma dirOfNat_zero : dirOfNat 0 = Turing.Dir.left := rfl
lemma dirOfNat_one : dirOfNat 1 = Turing.Dir.right := rfl

/-! ## Guard and value as arithmetic

With the direction as a number, the two cases combine into one expression each:
the guard is the direction-weighted sum of the two comparisons, and the value is
the direction-weighted sum of the two successors.  Only the guard's branch is
ever read, so the unused summand's value is irrelevant. -/

/-- Whether a move in direction `dir` from `p` stays inside the window. -/
def moveOk (W p dir : ℕ) : ℕ :=
  (1 - dir) * (if 0 < p then 1 else 0) + dir * (if p + 1 < W then 1 else 0)

/-- The position a move lands on, meaningful when `moveOk` is nonzero. -/
def moveTo (p dir : ℕ) : ℕ := (1 - dir) * (p - 1) + dir * (p + 1)

lemma moveOk_left (W p : ℕ) : moveOk W p 0 = if 0 < p then 1 else 0 := by
  unfold moveOk; omega

lemma moveOk_right (W p : ℕ) : moveOk W p 1 = if p + 1 < W then 1 else 0 := by
  unfold moveOk; omega

lemma moveTo_left (p : ℕ) : moveTo p 0 = p - 1 := by unfold moveTo; omega
lemma moveTo_right (p : ℕ) : moveTo p 1 = p + 1 := by unfold moveTo; omega

/-- When the guard holds, the value is the position `nextIdx` returns. -/
lemma nextIdx_eq_moveTo (W p dir : ℕ) (hdir : dir = 0 ∨ dir = 1) (h : moveOk W p dir ≠ 0) :
    nextIdx W p (dirOfNat dir) = some (moveTo p dir) := by
  rcases hdir with rfl | rfl
  · rw [moveOk_left] at h
    rw [dirOfNat_zero, nextIdx_left, moveTo_left, ite_eq_left (by by_contra hc; simp at hc; simp [hc] at h)]
  · rw [moveOk_right] at h
    rw [dirOfNat_one, nextIdx_right, moveTo_right,
      ite_eq_left (by by_contra hc; rw [ite_eq_right hc] at h; exact h rfl)]

/-- When the guard fails, there is no successor — the case the family answers
with a forbidding clause. -/
lemma nextIdx_none_of_moveOk_zero (W p dir : ℕ) (hdir : dir = 0 ∨ dir = 1)
    (h : moveOk W p dir = 0) : nextIdx W p (dirOfNat dir) = none := by
  rcases hdir with rfl | rfl
  · rw [moveOk_left] at h
    rw [dirOfNat_zero, nextIdx_left, ite_eq_right (by by_contra hc; rw [ite_eq_left hc] at h; omega)]
  · rw [moveOk_right] at h
    rw [dirOfNat_one, nextIdx_right, ite_eq_right (by by_contra hc; rw [ite_eq_left hc] at h; omega)]

/-! ## As expressions

The two quantities above, over a window width fixed at compile time and a
position and direction read from the store. -/

/-- `moveOk` as an expression, over expressions for the position and direction. -/
def moveOkE (W : ℕ) (pE dirE : Expr) : Expr :=
  .add
    (.mul (.sub (.const 1) dirE) (.lt (.const 0) pE))
    (.mul dirE (.lt (.add pE (.const 1)) (.const W)))

lemma moveOkE_eval (W : ℕ) (pE dirE : Expr) (σ : Store) :
    (moveOkE W pE dirE).eval σ = moveOk W (pE.eval σ) (dirE.eval σ) := by
  unfold moveOkE moveOk
  simp only [Expr.eval]
  rfl

/-! ## The successor position, stated additively

`moveTo` weighs the two directions against each other, which is the form that
makes `moveOk` and `moveTo` visibly parallel.  A caller starting from
`nextIdx W p d = some p'` instead has the position in the additive form
`p + dir - (1 - dir)`.  The two agree, so a family may use whichever its
surrounding proof produces. -/

lemma moveTo_eq_add_sub (p dir : ℕ) (hdir : dir = 0 ∨ dir = 1) :
    moveTo p dir = p + dir - (1 - dir) := by
  rcases hdir with rfl | rfl
  · rw [moveTo_left]; omega
  · rw [moveTo_right]; omega

end NPComplete.CookLevin

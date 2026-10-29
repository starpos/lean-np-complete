module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafAtLeastOne
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout

/-!
The run-time-width leaf states its frame obligations against a freeze bound
rather than against a single cell, because the reduction's variable numbers are
dense-layout arithmetic reading several control cells at once.  That reasoning is
only sound if the actual expressions discharge the bound-shaped obligation, so
this file checks the two values supplied by the accept and initial families: a
state number over a pinned time counter and the literal counter, and a cell
number over two pinned counters. Constants would satisfy any frame condition
vacuously.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The accept family's halt-state clause reads its variable number from the
pinned time counter and the literal counter inside the run-time-width loop. -/
lemma denseStateE_ctl_frame_bound (M n W m : ℕ) (σ1 σ2 : Store)
    (h1 : σ1 0 = M) (h2 : σ2 0 = M)
    (hagree : ∀ r, r < M + ctlJmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) :
    (denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell litJ)).eval σ1
      = (denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell litJ)).eval σ2 := by
  rw [denseStateE_eval, denseStateE_eval]
  simp only [Expr.eval, ctlCell_eval, h1, h2]
  rw [hagree (M + lvJ0) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega),
    hagree (M + litJ) (by unfold litJ ctlJmax; omega) (by unfold litJ wpJ; omega)]

/-- The initial family's free-cell clause reads a cell number over the window
index and the literal counter, with the time index fixed at zero. -/
lemma denseCellE_ctl_frame_bound (M n W m : ℕ) (σ1 σ2 : Store)
    (h1 : σ1 0 = M) (h2 : σ2 0 = M)
    (hagree : ∀ r, r < M + ctlJmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) :
    (denseCellE (.const n) (.const W) (.const m) (.const 0)
        (ctlCell lvJ0) (ctlCell litJ)).eval σ1
      = (denseCellE (.const n) (.const W) (.const m) (.const 0)
          (ctlCell lvJ0) (ctlCell litJ)).eval σ2 := by
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval, ctlCell_eval, h1, h2]
  rw [hagree (M + lvJ0) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega),
    hagree (M + litJ) (by unfold litJ ctlJmax; omega) (by unfold litJ wpJ; omega)]

/-- The count obligation additionally forbids reading the literal counter, which
the routine resets; a width read off a pinned cell satisfies it. -/
lemma ctlCell_cnt_frame_bound (M : ℕ) (σ1 σ2 : Store)
    (h1 : σ1 0 = M) (h2 : σ2 0 = M)
    (hagree : ∀ r, r < M + ctlJmax + 1 → r ≠ M + wpJ → r ≠ M + litJ → σ1 r = σ2 r) :
    (ctlCell tmpJ).eval σ1 = (ctlCell tmpJ).eval σ2 := by
  simp only [ctlCell_eval, h1, h2]
  exact hagree (M + tmpJ) (by unfold tmpJ ctlJmax; omega) (by unfold tmpJ wpJ; omega)
    (by unfold tmpJ litJ; omega)

/-- The value obligation on the same expression: inside the run-time-width loop
the literal counter holds the literal index, so the state number is the one the
clause's `k`-th literal should carry. -/
lemma denseStateE_ctl_value_inner (M n W m t : ℕ) (τ : Store) (k : ℕ)
    (hF : PinsHold M (ctlPins1 t) τ) (h0 : τ 0 = M) (hk : τ (M + litJ) = k) :
    (denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell litJ)).eval τ
      = (denseLayout n W m).state t k := by
  have e0 : (ctlCell lvJ0).eval τ = t :=
    ctlCell_eval_of_pin M (ctlPins1 t) lvJ0 t τ (by simp [ctlPins1]) hF h0
  have e1 : (ctlCell litJ).eval τ = k := by rw [ctlCell_eval, h0]; exact hk
  rw [denseStateE_eval, e0, e1]
  simp [Expr.eval]

end NPComplete.CookLevin

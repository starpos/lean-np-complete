module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowLayout

/-!
A family's leaf owes a frame condition and a value condition for each variable expression it
writes. These checks run both obligations on the dense layout's own cell expression, built from
pinned sizes and counters, rather than on constants that would satisfy either vacuously. They show
that the control-cell conventions can carry the assembly. No main construction uses them, so they
stay outside the consumer-facing umbrella.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Frame: a dense cell number built from pinned sizes and counters is unchanged
by any store agreeing on the control block off the write pointer. -/
lemma denseCellE_ctl_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (denseCellE (.const n) (.const W) (.const m)
        (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ2)).eval σ'
      = (denseCellE (.const n) (.const W) (.const m)
          (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ2)).eval σ :=
  denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)

/-- Value: with the two outer counters pinned and the innermost one holding the
iteration index, the same expression is the dense layout's own cell number. -/
lemma denseCellE_ctl_value (M n W m t p : ℕ) (τ : Store) (i : ℕ)
    (hF : PinsHold M (ctlPins2 t p) τ) (h0 : τ 0 = M) (hi : τ (M + lvJ2) = i) :
    (denseCellE (.const n) (.const W) (.const m)
        (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ2)).eval τ
      = (denseLayout n W m).cell t p i :=
  denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p i rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins2 t p) lvJ0 t τ (by simp [ctlPins2]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins2 t p) lvJ1 p τ (by simp [ctlPins2]) hF h0)
    (by rw [ctlCell_eval, h0]; exact hi)

end NPComplete.CookLevin

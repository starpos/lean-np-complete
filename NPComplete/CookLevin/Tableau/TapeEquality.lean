module

public import NPComplete.CookLevin.Tableau.StepsToBridge

/-!
# Tape extensionality

Agreement at every indexed tape position is the final bridge from finite-window facts to equality
of machine tapes. This module proves extensionality and the untouched-cell facts needed to identify
the full tape with its initial snapshot outside the window.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## From per-position cell facts to a full `Tape` equality -/

/-- A tape is determined by its `nth` values at every integer position. -/
lemma tape_ext_of_nth [Inhabited Γ] {T₁ T₂ : Tape Γ}
    (h : ∀ p : ℤ, T₁.nth p = T₂.nth p) : T₁ = T₂ := by
  obtain ⟨a₁, L₁, R₁⟩ := T₁
  obtain ⟨a₂, L₂, R₂⟩ := T₂
  have hhead : a₁ = a₂ := by simpa using h 0
  have hleft : L₁ = L₂ := by
    apply ListBlank.ext
    intro i
    simpa [Tape.nth] using h (Int.negSucc i)
  have hright : R₁ = R₂ := by
    apply ListBlank.ext
    intro i
    simpa [Tape.nth] using h (((i + 1 : ℕ) : ℤ))
  simp [hhead, hleft, hright]

/-- Cells the run cannot yet have reached still hold their initial symbol. -/
lemma absNth_eq_initSymbol_of_untouched [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) :
    ∀ (t : ℕ) (p : ℤ), p < -(t : ℤ) ∨ (t : ℤ) < p →
      absNth (runCfg M input t) (runHead M input t) p = initSymbol input p := by
  intro t
  induction t with
  | zero =>
    intro p _
    show (init input).Tape.nth (p - 0) = initSymbol input p
    simp [init, tape_mk₁_nth]
  | succ t ih =>
    intro p hp
    have hp' : p < -(t : ℤ) ∨ (t : ℤ) < p := by
      rcases hp with h1 | h1 <;> push_cast at h1 ⊢ <;> omega
    have hb := runHead_abs_le M input t
    have hne : p ≠ runHead M input t := by
      rcases hp with h1 | h1 <;> push_cast at h1 <;> omega
    have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
    have hheadc : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rw [hstepc, hheadc, absNth_stepOrStay_of_ne hne]
    exact ih p hp'

/-- Below the start of a list, `initSymbol` always reads as `default`. -/
lemma initSymbol_eq_default_of_neg [Inhabited Γ] {l : List Γ} {p : ℤ} (hp : p < 0) :
    initSymbol l p = default := by
  simp [initSymbol, not_le.mpr hp]

/-- Past the end of a list, `initSymbol` always reads as `default`. -/
lemma initSymbol_eq_default_of_ge [Inhabited Γ] {l : List Γ} {p : ℤ}
    (hp : (l.length : ℤ) ≤ p) : initSymbol l p = default := by
  have h1 : ¬ p.toNat < l.length := by omega
  simp only [initSymbol]
  rw [ite_eq_left (by omega), List.getI_eq_default _ (not_lt.mp h1)]

end NPComplete.CookLevin

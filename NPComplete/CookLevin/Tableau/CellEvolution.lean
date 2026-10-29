module

public import NPComplete.CookLevin.Tableau.RunBounds

/-!
# Local cell evolution

Transition clauses must account for every tape cell, not just the scanned one. This module
establishes the local step-or-stay behavior for cells away from the head, which lets global run
arguments distinguish preserved cells from the written cell.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Cell values evolve exactly according to `step` -/

lemma absNth_stepOrStay_of_ne [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {c : Cfg Γ Λ} {h p : ℤ} (hne : p ≠ h) :
    absNth (stepOrStay M c) (stepHead M c h) p = absNth c h p := by
  unfold stepOrStay stepHead absNth step
  rcases hM : M c.q c.Tape.head with _ | ⟨q', stmt⟩
  · simp [hM]
  · rcases stmt with d | b
    · simp only [hM]
      cases d <;>
        simp [dirDelta, Tape.move_left_nth, Tape.move_right_nth] <;>
        · congr 1
          ring
    · simp only [hM, Option.map_some]
      rw [Tape.write_nth, ite_eq_right (by omega)]

lemma absNth_stepOrStay_write [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {c : Cfg Γ Λ} {h : ℤ} {q' : Λ} {b : Γ}
    (hM : M c.q c.Tape.head = some (q', .write b)) :
    absNth (stepOrStay M c) (stepHead M c h) h = b := by
  simp [stepOrStay, stepHead, absNth, step, hM, Tape.write]

lemma absNth_stepOrStay_not_write [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {c : Cfg Γ Λ} {h : ℤ}
    (hnw : ∀ q' b, M c.q c.Tape.head ≠ some (q', Stmt.write b)) :
    absNth (stepOrStay M c) (stepHead M c h) h = absNth c h h := by
  unfold stepOrStay stepHead absNth step
  rcases hM : M c.q c.Tape.head with _ | ⟨q', stmt⟩
  · simp [hM]
  · rcases stmt with d | b
    · simp only [hM, Option.map_some]
      cases d <;>
        simp [dirDelta, Tape.move_left_nth, Tape.move_right_nth]
    · exact absurd hM (hnw q' b)

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.CellEvolution

/-!
# Window neighbor indices

Moving a head changes its integer position by one, but a bounded tableau uses a finite cell index.
This module proves how each legal move maps between those coordinates and isolates the boundary
checks required by transition clauses.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## The moved-to window index, expressed via `posToIdx` -/

lemma nextIdx_left_eq {T : ℕ} {h : ℤ} {W : ℕ} (hlo : -(T : ℤ) ≤ h - 1) :
    nextIdx W (posToIdx T h) Dir.left = some (posToIdx T (h - 1)) := by
  simp [nextIdx, posToIdx]
  omega

lemma nextIdx_right_eq {T : ℕ} {h : ℤ} {W : ℕ} (hlo : -(T : ℤ) ≤ h)
    (hhi : posToIdx T (h + 1) < W) :
    nextIdx W (posToIdx T h) Dir.right = some (posToIdx T (h + 1)) := by
  have hB : (0:ℤ) ≤ h + 1 + T := by omega
  have hhi' : ((h + 1 + (T:ℤ)).toNat : ℤ) < W := by
    have e := Int.toNat_of_nonneg hB
    simp only [posToIdx] at hhi
    omega
  have key : ((h + (T:ℤ)).toNat + 1 < W) = True := by
    simp
    omega
  simp [nextIdx, posToIdx, key]
  omega

/-- A genuinely-reached head position at time `t < T` always has room to move
in either direction: the window is sized so `nextIdx` never fails there,
regardless of which direction `d` is asked for. -/
lemma nextIdx_move_isSome_of_real [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) {T t p inputLen outputLen : ℕ} (d : Dir) (ht : t < T)
    (hpeq : runHead M input t = idxToPos T p) :
    ∃ p', nextIdx (windowSize inputLen outputLen T) p d = some p' ∧
      idxToPos T p' = runHead M input t + dirDelta d := by
  have hb := runHead_abs_le M input t
  have hpreal : p = posToIdx T (runHead M input t) := by
    rw [hpeq]; exact (posToIdx_idxToPos T p).symm
  subst hpreal
  rcases d with _ | _
  · have hlo : -(T : ℤ) ≤ runHead M input t - 1 := by omega
    exact ⟨posToIdx T (runHead M input t - 1), nextIdx_left_eq hlo, by
      rw [idxToPos_posToIdx hlo]; simp only [dirDelta]; ring⟩
  · have hlo : -(T : ℤ) ≤ runHead M input t := by omega
    have hhi : posToIdx T (runHead M input t + 1) < windowSize inputLen outputLen T :=
      posToIdx_lt_window (by omega)
    exact ⟨posToIdx T (runHead M input t + 1), nextIdx_right_eq hlo hhi, by
      rw [idxToPos_posToIdx (by omega : -(T : ℤ) ≤ runHead M input t + 1)]
      simp [dirDelta]⟩

end NPComplete.CookLevin

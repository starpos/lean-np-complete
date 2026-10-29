module

public import NPComplete.CookLevin.Tableau.RunAdvance

/-!
# Cell persistence

Run consistency must carry every untouched tape symbol from one row to the next. This module proves
persistence from a concrete run so the SAT-run induction can handle all cells, not only the head
position.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Untouched cells persist unchanged -/

/-- The real run's state / head snapshot witnesses persistence: cells the
head doesn't touch at time `t` carry their content forward unchanged. -/
lemma persistClauses_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T : ℕ} :
    ∀ c ∈ persistClauses (Γ := Γ) (windowSize input.length output.length T) T,
      c.Satisfied (runAssign M S input output T) := by
  set τ := runAssign M S input output T with hτdef
  set W := windowSize input.length output.length T with hWdef
  intro c hc
  simp only [persistClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, pHead, hpHead, pCell, hpCell, hc⟩ := hc
  have htT : t < T := List.mem_range.mp ht
  have hpCellW : pCell < W := List.mem_range.mp hpCell
  by_cases hne : pHead = pCell
  · simp [hne] at hc
  · rw [ite_eq_right hne] at hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    refine satisfied_imply2 (fun hhd hcl => ?_)
    have hpeq : runHead M input t = idxToPos T pHead := (runAssign_head_inv hhd).2
    have haeq : absNth (runCfg M input t) (runHead M input t) (idxToPos T pCell) = a :=
      (runAssign_cell_inv hcl).2
    have hne' : idxToPos T pCell ≠ runHead M input t := by
      rw [hpeq]
      intro he
      have hp : posToIdx T (idxToPos T pCell) = posToIdx T (idxToPos T pHead) :=
        congrArg (posToIdx T) he
      simp only [posToIdx_idxToPos] at hp
      exact hne hp.symm
    refine runAssign_cell (by omega) hpCellW ?_
    have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
    have hheadc : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rw [hstepc, hheadc, absNth_stepOrStay_of_ne hne']
    exact haeq

lemma sat_run_persist [Fintype Γ] [DecidableEq Γ]
    {W T t pHead pCell : ℕ} {τ : Literal.Assignment} {a : Γ}
    (hpersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ)
    (ht : t < T) (hpHead : pHead < W) (hpCell : pCell < W) (hne : pHead ≠ pCell)
    (hhd : τ (headVar t pHead) = true)
    (hcl : τ (cellVar t pCell (letterIdx a)) = true) :
    τ (cellVar (t + 1) pCell (letterIdx a)) = true := by
  apply eval_imply2 _ hhd hcl
  apply hpersist
  simp only [persistClauses, List.mem_flatMap]
  refine ⟨t, List.mem_range.mpr ht, pHead, List.mem_range.mpr hpHead, pCell,
    List.mem_range.mpr hpCell, ?_⟩
  rw [ite_eq_right hne]
  exact List.mem_map.mpr ⟨a, mem_letters a, rfl⟩

/-- Advance the full cell snapshot (every window position, not just the head)
one time step, combining `sat_run_step`'s head-cell fact with persistence
elsewhere. -/
lemma sat_run_cell_succ [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {input output : List Γ}
    {T t : ℕ} {τ : Literal.Assignment}
    (hpersist : ∀ c ∈ persistClauses (Γ := Γ) (windowSize input.length output.length T) T,
      c.Satisfied τ)
    (ht : t < T)
    (hhd : τ (headVar t (posToIdx T (runHead M input t))) = true)
    (hclAll : ∀ p, p < windowSize input.length output.length T →
      τ (cellVar t p (letterIdx (absNth (runCfg M input t) (runHead M input t)
        (idxToPos T p)))) = true)
    (hclHead : τ (cellVar (t + 1) (posToIdx T (runHead M input t))
        (letterIdx (absNth (runCfg M input (t + 1)) (runHead M input (t + 1))
          (runHead M input t)))) = true) :
    ∀ p, p < windowSize input.length output.length T →
      τ (cellVar (t + 1) p (letterIdx (absNth (runCfg M input (t + 1))
        (runHead M input (t + 1)) (idxToPos T p)))) = true := by
  intro p hp
  have hboundT : -(T : ℤ) ≤ runHead M input t := by
    have := (runHead_abs_le M input t).1; omega
  have hpHeadEq : idxToPos T (posToIdx T (runHead M input t)) = runHead M input t :=
    idxToPos_posToIdx hboundT
  by_cases hpeq : p = posToIdx T (runHead M input t)
  · subst hpeq
    rwa [hpHeadEq]
  · have hcl_t := hclAll p hp
    have hres := sat_run_persist hpersist ht
      (runHead_posToIdx_lt_window M input ht.le) hp (fun he => hpeq he.symm) hhd hcl_t
    have hne : idxToPos T p ≠ runHead M input t := by
      rw [← hpHeadEq]
      intro he
      apply hpeq
      simp only [idxToPos] at he
      omega
    have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
    have hheadc : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rw [hstepc, hheadc, absNth_stepOrStay_of_ne hne]
    exact hres

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.TransOneWitness

/-!
# One-step run advance

To lift transition clauses to a whole computation, state, head, and scanned-cell facts must
advance together by one step. This module proves that local advancement, separating move-bound
bookkeeping from the later multi-step invariant.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Advancing the run's state / head / cell-at-head facts one step -/

/-- The `.move d` branch of `sat_run_step`: split out because locating the
moved-to window index needs its own bound bookkeeping. -/
lemma sat_run_step_move [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input : List Γ}
    {T t : ℕ} {τ : Literal.Assignment} {q' : Λ} {d : Dir} {W : ℕ}
    (hM : M (runCfg M input t).q (runCfg M input t).Tape.head =
      some (q', Stmt.move d))
    (ht : t < T)
    (hpW' : posToIdx T (runHead M input (t + 1)) < W)
    (hInst : ∀ x ∈ transOne M S W t (posToIdx T (runHead M input t))
        (runCfg M input t).q (runCfg M input t).Tape.head, x.Satisfied τ)
    (hq'S : q' ∈ S)
    (hst : τ (stateVar t (stateIdx S (runCfg M input t).q)) = true)
    (hhd : τ (headVar t (posToIdx T (runHead M input t))) = true)
    (hcl : τ (cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)) = true) :
    τ (stateVar (t + 1) (stateIdx S (runCfg M input (t + 1)).q)) = true ∧
    τ (headVar (t + 1) (posToIdx T (runHead M input (t + 1)))) = true ∧
    τ (cellVar (t + 1) (posToIdx T (runHead M input t))
        (letterIdx (absNth (runCfg M input (t + 1)) (runHead M input (t + 1))
          (runHead M input t)))) = true := by
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
  have hb0 := (runHead_abs_le M input t).1
  have hb1 := (runHead_abs_le M input (t + 1)).1
  have hnw : ∀ q'' b, M (runCfg M input t).q (runCfg M input t).Tape.head ≠
      some (q'', Stmt.write b) := by intro q'' b hcontra; rw [hM] at hcontra; cases hcontra
  have hnext : nextIdx W (posToIdx T (runHead M input t)) d =
      some (posToIdx T (runHead M input (t + 1))) := by
    rcases d with _ | _
    · have hd1 : runHead M input (t + 1) = runHead M input t - 1 := by
        rw [hheadc, stepHead, hM]; simp only [dirDelta]; ring
      have hlo : -(T : ℤ) ≤ runHead M input t - 1 := by
        rw [← hd1]; push_cast at hb1; omega
      rw [nextIdx_left_eq hlo, hd1]
    · have hd1 : runHead M input (t + 1) = runHead M input t + 1 := by
        rw [hheadc, stepHead, hM]; simp only [dirDelta]
      have hlo : -(T : ℤ) ≤ runHead M input t := by omega
      rw [nextIdx_right_eq hlo (by rw [← hd1]; exact hpW'), hd1]
  simp only [transOne, hM, ite_eq_left hq'S, hnext] at hInst
  set st := stateVar t (stateIdx S (runCfg M input t).q)
  set hd := headVar t (posToIdx T (runHead M input t))
  set cl := cellVar t (posToIdx T (runHead M input t))
    (letterIdx (runCfg M input t).Tape.head)
  have h1 : (imply3 st hd cl (stateVar (t + 1) (stateIdx S q'))).Satisfied τ :=
    hInst _ (by simp)
  have h2 : (imply3 st hd cl
      (headVar (t + 1) (posToIdx T (runHead M input (t + 1))))).Satisfied τ :=
    hInst _ (by simp)
  have h3 : (imply3 st hd cl (cellVar (t + 1)
      (posToIdx T (runHead M input t)) (letterIdx (runCfg M input t).Tape.head))
      ).Satisfied τ := hInst _ (by simp)
  replace h1 := eval_imply3 h1 hst hhd hcl
  replace h2 := eval_imply3 h2 hst hhd hcl
  replace h3 := eval_imply3 h3 hst hhd hcl
  refine ⟨?_, ?_, ?_⟩
  · rw [hstepc]; simp only [stepOrStay, step, hM]; exact h1
  · exact h2
  · rw [hstepc, hheadc, absNth_stepOrStay_not_write hnw]
    simpa [absNth, hM] using h3

/-- The transition, write, and move clauses force the next state and head,
together with the next-time cell at the old head position. -/
lemma sat_run_step [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t : ℕ} {τ : Literal.Assignment} (hS : Supports M ↑S)
    (htrans : ∀ c ∈ transClauses M S (windowSize input.length output.length T) T,
      c.Satisfied τ)
    (ht : t < T)
    (hst : τ (stateVar t (stateIdx S (runCfg M input t).q)) = true)
    (hhd : τ (headVar t (posToIdx T (runHead M input t))) = true)
    (hcl : τ (cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)) = true) :
    τ (stateVar (t + 1) (stateIdx S (runCfg M input (t + 1)).q)) = true ∧
    τ (headVar (t + 1) (posToIdx T (runHead M input (t + 1)))) = true ∧
    τ (cellVar (t + 1) (posToIdx T (runHead M input t))
        (letterIdx (absNth (runCfg M input (t + 1)) (runHead M input (t + 1))
          (runHead M input t)))) = true := by
  have hqS : (runCfg M input t).q ∈ S := runCfg_state_mem hS input t
  have haL : (runCfg M input t).Tape.head ∈ letters Γ := mem_letters _
  have hpW : posToIdx T (runHead M input t) < windowSize input.length output.length T :=
    runHead_posToIdx_lt_window M input ht.le
  have hInst : ∀ x ∈ transOne M S (windowSize input.length output.length T) t
      (posToIdx T (runHead M input t)) (runCfg M input t).q
      (runCfg M input t).Tape.head, x.Satisfied τ := by
    intro x hx
    apply htrans
    simp only [transClauses, List.mem_flatMap]
    exact ⟨t, List.mem_range.mpr ht, posToIdx T (runHead M input t),
      List.mem_range.mpr hpW, (runCfg M input t).q, Finset.mem_toList.mpr hqS,
      (runCfg M input t).Tape.head, haL, hx⟩
  have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  rcases hM : M (runCfg M input t).q (runCfg M input t).Tape.head with _ | ⟨q', stmt⟩
  · -- halted
    simp only [transOne, hM] at hInst
    set st := stateVar t (stateIdx S (runCfg M input t).q)
    set hd := headVar t (posToIdx T (runHead M input t))
    set cl := cellVar t (posToIdx T (runHead M input t))
      (letterIdx (runCfg M input t).Tape.head)
    have h1 : (imply3 st hd cl
        (stateVar (t + 1) (stateIdx S (runCfg M input t).q))).Satisfied τ :=
      hInst _ (by simp)
    have h2 : (imply3 st hd cl
        (headVar (t + 1) (posToIdx T (runHead M input t)))).Satisfied τ :=
      hInst _ (by simp)
    have h3 : (imply3 st hd cl (cellVar (t + 1)
        (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head))).Satisfied τ := hInst _ (by simp)
    replace h1 := eval_imply3 h1 hst hhd hcl
    replace h2 := eval_imply3 h2 hst hhd hcl
    replace h3 := eval_imply3 h3 hst hhd hcl
    refine ⟨?_, ?_, ?_⟩
    · rw [hstepc]; simp only [stepOrStay, step, hM]; exact h1
    · rw [hheadc]; simp only [stepHead, hM]; exact h2
    · rw [hstepc, hheadc]
      simp only [stepOrStay, step, stepHead, hM, absNth, Tape.nth_zero, sub_self]
      exact h3
  · have hq'S : q' ∈ S := hS.2 (Option.mem_def.mpr hM) hqS
    rcases stmt with d | b
    · exact sat_run_step_move hM ht
        (runHead_posToIdx_lt_window M input ht) hInst hq'S hst hhd hcl
    · -- write
      simp only [transOne, hM, ite_eq_left hq'S] at hInst
      set st := stateVar t (stateIdx S (runCfg M input t).q)
      set hd := headVar t (posToIdx T (runHead M input t))
      set cl := cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)
      have h1 : (imply3 st hd cl
          (stateVar (t + 1) (stateIdx S q'))).Satisfied τ := hInst _ (by simp)
      have h2 : (imply3 st hd cl
          (headVar (t + 1) (posToIdx T (runHead M input t)))).Satisfied τ :=
        hInst _ (by simp)
      have h3 : (imply3 st hd cl (cellVar (t + 1)
          (posToIdx T (runHead M input t)) (letterIdx b))).Satisfied τ :=
        hInst _ (by simp)
      replace h1 := eval_imply3 h1 hst hhd hcl
      replace h2 := eval_imply3 h2 hst hhd hcl
      replace h3 := eval_imply3 h3 hst hhd hcl
      refine ⟨?_, ?_, ?_⟩
      · rw [hstepc]; simp only [stepOrStay, step, hM]; exact h1
      · rw [hheadc]; simp only [stepHead, hM]; exact h2
      · rw [hstepc, hheadc, absNth_stepOrStay_write hM]; exact h3

end NPComplete.CookLevin

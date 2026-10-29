module

public import NPComplete.CookLevin.Tableau.Persistence

/-!
# SAT run invariant

Local clauses constrain adjacent time steps, but correctness requires agreement with the complete
concrete run through the time bound. This module packages that repeated reasoning as the SAT-run
invariant used by the tableau equivalence.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## The satisfying assignment reproduces the real run, at every time -/

/-- The central forward induction: a satisfying assignment of the uniqueness /
initial / transition / persistence clauses reproduces the real run's state,
head, and full cell snapshot at every time `t ≤ T`. -/
lemma sat_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T : ℕ} {τ : Literal.Assignment} (hS : Supports M ↑S)
    (hinit : ∀ c ∈ initClauses S input (windowSize input.length output.length T) T,
      c.Satisfied τ)
    (htrans : ∀ c ∈ transClauses M S (windowSize input.length output.length T) T,
      c.Satisfied τ)
    (hpersist : ∀ c ∈ persistClauses (Γ := Γ) (windowSize input.length output.length T) T,
      c.Satisfied τ) :
    ∀ t, t ≤ T →
      τ (stateVar t (stateIdx S (runCfg M input t).q)) = true ∧
      τ (headVar t (posToIdx T (runHead M input t))) = true ∧
      ∀ p, p < windowSize input.length output.length T →
        τ (cellVar t p (letterIdx (absNth (runCfg M input t) (runHead M input t)
          (idxToPos T p)))) = true := by
  intro t
  induction t with
  | zero =>
    intro _
    have hdef : (default : Λ) ∈ S := Finset.mem_coe.mp hS.1
    refine ⟨?_, ?_, ?_⟩
    · simpa [runCfg_zero, init] using state_of_initClauses hdef hinit
    · simpa [runHead_zero, posToIdx, originIdx] using head_of_initClauses hinit
    · intro p hp
      simpa [runCfg_zero, runHead_zero, absNth, init, tape_mk₁_nth] using
        initSymbol_of_initClauses hinit hp
  | succ t ih =>
    intro ht1
    have ht : t < T := by omega
    obtain ⟨hst, hhd, hclAll⟩ := ih ht.le
    have hcellhead : τ (cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)) = true := by
      have hb := hclAll (posToIdx T (runHead M input t))
        (runHead_posToIdx_lt_window M input ht.le)
      have heq : idxToPos T (posToIdx T (runHead M input t)) = runHead M input t :=
        idxToPos_posToIdx (by have := (runHead_abs_le M input t).1; omega)
      rw [heq] at hb
      simpa [absNth] using hb
    obtain ⟨hst', hhd', hclhead'⟩ := sat_run_step hS htrans ht hst hhd hcellhead
    exact ⟨hst', hhd', sat_run_cell_succ hpersist ht hhd hclAll hclhead'⟩

end NPComplete.CookLevin

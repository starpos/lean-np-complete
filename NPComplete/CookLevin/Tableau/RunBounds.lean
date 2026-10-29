module

public import NPComplete.CookLevin.Tableau.RunCorrectness

/-!
# Run window bounds

A tableau window must contain every head position reached within the time bound. This module
derives displacement bounds and uses them to justify the run's uniqueness constraints, keeping
range arguments separate from transition semantics.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Head displacement is bounded by elapsed time -/

lemma stepHead_eq_or [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (c : Cfg Γ Λ)
    (h : ℤ) :
    stepHead M c h = h ∨ stepHead M c h = h + 1 ∨ stepHead M c h = h - 1 := by
  unfold stepHead dirDelta
  split <;> first | tauto | (split <;> tauto)

lemma runHead_abs_le [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (input : List Γ)
    (t : ℕ) :
    -(t : ℤ) ≤ runHead M input t ∧ runHead M input t ≤ (t : ℤ) := by
  induction t with
  | zero => simp [runHead_zero]
  | succ t ih =>
    have heq : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rcases stepHead_eq_or M (runCfg M input t) (runHead M input t) with
      hcase | hcase | hcase <;>
      · rw [heq, hcase]; push_cast; omega

/-- The elapsed-time bound on `runHead_abs_le`, widened to the full budget
`T` — the form `idxToPos_posToIdx` and friends actually need. -/
lemma runHead_abs_le_of_le [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) {T t : ℕ} (ht : t ≤ T) : -(T : ℤ) ≤ runHead M input t := by
  have h := (runHead_abs_le M input t).1
  have hcast : (t : ℤ) ≤ (T : ℤ) := by exact_mod_cast ht
  omega

/-- The window is exactly wide enough to hold a `T`-step run's head position
at every intermediate time. -/
lemma runHead_posToIdx_lt_window [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) {inputLen outputLen T t : ℕ} (ht : t ≤ T) :
    posToIdx T (runHead M input t) < windowSize inputLen outputLen T := by
  have hb := runHead_abs_le M input t
  apply posToIdx_lt_window
  push_cast
  omega

/-- The real run's state / head / cell snapshot is, at every time, the unique
witness for its own uniqueness clauses: `runAssign` satisfies them. -/
lemma uniquenessClauses_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T : ℕ} (hS : Supports M ↑S) :
    ∀ c ∈ uniquenessClauses (Γ := Γ) S (windowSize input.length output.length T) T,
      c.Satisfied (runAssign M S input output T) := by
  intro c hc
  set W := windowSize input.length output.length T with hWdef
  simp only [uniquenessClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, hc⟩ := hc
  have htT : t ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht)
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · -- state uniqueness at time `t`
      have hnodup : (S.toList.map fun q => stateVar t (stateIdx S q)).Nodup :=
        List.Nodup.map_on
          (fun q1 hq1 q2 hq2 heq => stateIdx_inj (Finset.mem_toList.mp hq1)
            (Finset.mem_toList.mp hq2) (stateVar_eq_iff.mp heq).2)
          S.nodup_toList
      refine satisfied_exactlyOne_of_unique hnodup
        (List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (runCfg_state_mem hS input t), rfl⟩)
        (runAssign_state htT (runCfg_state_mem hS input t)) ?_ c hc
      intro v hv htv
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
      exact congrArg (fun q' => stateVar t (stateIdx S q'))
        (runAssign_state_inv htv).2.2.symm
    · -- head uniqueness at time `t`
      have hb0 : -(T : ℤ) ≤ runHead M input t := by
        have h := (runHead_abs_le M input t).1
        have hcast : (t : ℤ) ≤ T := by exact_mod_cast htT
        omega
      have hp0W : posToIdx T (runHead M input t) < W :=
        runHead_posToIdx_lt_window M input htT
      have hhd0 : runHead M input t = idxToPos T (posToIdx T (runHead M input t)) :=
        (idxToPos_posToIdx hb0).symm
      have hnodup : ((List.range W).map fun p => headVar t p).Nodup :=
        List.Nodup.map (fun p1 p2 heq => (headVar_eq_iff.mp heq).2) List.nodup_range
      refine satisfied_exactlyOne_of_unique hnodup
        (List.mem_map.mpr ⟨_, List.mem_range.mpr hp0W, rfl⟩)
        (runAssign_head htT hp0W hhd0) ?_ c hc
      intro v hv htv
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
      have hp : runHead M input t = idxToPos T p := (runAssign_head_inv htv).2
      have hpeq : posToIdx T (runHead M input t) = p := by
        have heq := congrArg (posToIdx T) (hhd0.symm.trans hp)
        simpa [posToIdx_idxToPos] using heq
      exact congrArg (headVar t) hpeq.symm
  · -- cell uniqueness at time `t`, window position `p`
    simp only [List.mem_flatMap] at hc
    obtain ⟨p, hp, hc⟩ := hc
    have hpW : p < W := List.mem_range.mp hp
    have hnodup : ((letters Γ).map fun a => cellVar t p (letterIdx a)).Nodup :=
      List.Nodup.map_on
        (fun a1 _ a2 _ heq => letterIdx_inj (cellVar_eq_iff.mp heq).2.2)
        letters_nodup
    refine satisfied_exactlyOne_of_unique hnodup
      (List.mem_map.mpr ⟨_, mem_letters _, rfl⟩)
      (runAssign_cell htT hpW rfl) ?_ c hc
    intro v hv htv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact congrArg (fun x => cellVar t p (letterIdx x))
      (runAssign_cell_inv htv).2.symm

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.FreeSuffix

/-!
# SAT clause implications

A satisfying assignment must be decoded back into the one-hot state, head, and cell facts used by
machine execution. This module proves the semantic consequences of the local clauses and isolates
that inversion from the run induction.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Constructing satisfaction of implication clauses -/

lemma satisfied_implyPos {τ : Literal.Assignment} {a b : ℕ}
    (h : τ a = true → τ b = true) : (implyPos a b).Satisfied τ := by
  cases ha : τ a with
  | false => exact Clause.satisfied_cons_of_left (by simp [Literal.eval, ha])
  | true => exact Clause.satisfied_cons_of_right (Clause.satisfied_pos (h ha))

lemma satisfied_imply2 {τ : Literal.Assignment} {a b d : ℕ}
    (h : τ a = true → τ b = true → τ d = true) : (imply2 a b d).Satisfied τ := by
  cases ha : τ a with
  | false => exact Clause.satisfied_cons_of_left (by simp [Literal.eval, ha])
  | true =>
    cases hb : τ b with
    | false =>
      exact Clause.satisfied_cons_of_right
        (Clause.satisfied_cons_of_left (by simp [Literal.eval, hb]))
    | true =>
      exact Clause.satisfied_cons_of_right
        (Clause.satisfied_cons_of_right (Clause.satisfied_pos (h ha hb)))

lemma satisfied_imply3 {τ : Literal.Assignment} {a b c d : ℕ}
    (h : τ a = true → τ b = true → τ c = true → τ d = true) :
    (imply3 a b c d).Satisfied τ := by
  cases ha : τ a with
  | false => exact Clause.satisfied_cons_of_left (by simp [Literal.eval, ha])
  | true =>
    cases hb : τ b with
    | false =>
      exact Clause.satisfied_cons_of_right
        (Clause.satisfied_cons_of_left (by simp [Literal.eval, hb]))
    | true =>
      cases hc : τ c with
      | false =>
        exact Clause.satisfied_cons_of_right (Clause.satisfied_cons_of_right
          (Clause.satisfied_cons_of_left (by simp [Literal.eval, hc])))
      | true =>
        exact Clause.satisfied_cons_of_right (Clause.satisfied_cons_of_right
          (Clause.satisfied_cons_of_right (Clause.satisfied_pos (h ha hb hc))))

lemma satisfied_forbid3 {τ : Literal.Assignment} {a b c : ℕ}
    (h : τ a = true → τ b = true → τ c = false) : (forbid3 a b c).Satisfied τ := by
  cases ha : τ a with
  | false => exact Clause.satisfied_cons_of_left (by simp [Literal.eval, ha])
  | true =>
    cases hb : τ b with
    | false =>
      exact Clause.satisfied_cons_of_right
        (Clause.satisfied_cons_of_left (by simp [Literal.eval, hb]))
    | true =>
      exact Clause.satisfied_cons_of_right
        (Clause.satisfied_cons_of_right (Clause.satisfied_neg (h ha hb)))

lemma bounded_free_cell_of_clauses [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {S : Finset Λ} {pref : List Γ} {freeLen W T : ℕ}
    {allowed : List Γ} {blank : Γ} {τ : Literal.Assignment}
    (h : ∀ c ∈ boundedPrefixInitClauses S pref freeLen allowed blank W T,
      c.Satisfied τ) {p : ℕ} (hp : p < W)
    (hfree : T + pref.length ≤ p)
    (hfree' : p < T + pref.length + freeLen) :
    ∃ a ∈ blank :: allowed,
      τ (cellVar 0 p (letterIdx a)) = true := by
  have hc : (atLeastOne ((blank :: allowed).map fun a =>
      cellVar 0 p (letterIdx a))).Satisfied τ := by
    apply h
    unfold boundedPrefixInitClauses
    apply List.mem_append.mpr
    left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, by simp [hfree, hfree']⟩))
  obtain ⟨v, hv, hvτ⟩ := atLeastOne_exists hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact ⟨a, ha, hvτ⟩

lemma bounded_no_hole_of_clauses [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {S : Finset Λ} {pref : List Γ} {freeLen W T : ℕ}
    {allowed : List Γ} {blank : Γ} {τ : Literal.Assignment}
    (h : ∀ c ∈ boundedPrefixInitClauses S pref freeLen allowed blank W T,
      c.Satisfied τ) {i : ℕ} (hi : i < freeLen)
    (hblank : τ (cellVar 0 (T + pref.length + i) (letterIdx blank)) = true) :
    τ (cellVar 0 (T + pref.length + i + 1) (letterIdx blank)) = true := by
  apply eval_implyPos (h := h _ ?_) hblank
  simp only [boundedPrefixInitClauses, List.mem_append, List.mem_map]
  exact Or.inr ⟨i, List.mem_range.mpr hi, rfl⟩

lemma bounded_suffix_extract_cons {τ : Literal.Assignment} (base B : ℕ) (b : Bool)
    (hbit : τ (cellVar 0 base (letterIdx (some b))) = true)
    {w : List Bool} (hwlen : w.length ≤ B)
    (hwassign : ∀ i, i < w.length →
      τ (cellVar 0 (base + 1 + i) (letterIdx (some (w.getI i)))) = true)
    (hwblank : ∀ i, w.length ≤ i → i < B →
      τ (cellVar 0 (base + 1 + i) (letterIdx (none : Option Bool))) = true) :
    ∃ w' : List Bool, w'.length ≤ B + 1 ∧
      (∀ i, i < w'.length →
        τ (cellVar 0 (base + i) (letterIdx (some (w'.getI i)))) = true) ∧
      (∀ i, w'.length ≤ i → i < B + 1 →
        τ (cellVar 0 (base + i) (letterIdx (none : Option Bool))) = true) := by
  refine ⟨b :: w, by simp [hwlen], ?_, ?_⟩
  · intro i hi
    rcases i with _ | i
    · simpa using hbit
    · have h' := hwassign i (by simpa using hi)
      have hget : (b :: w).getI (1 + i) = w.getI i := by
        rw [show 1 + i = i + 1 by omega, List.getI_cons_succ]
      simpa [hget, Nat.add_assoc, Nat.add_comm i 1] using h'
  · intro i hiLen hiB
    have hiPos : 1 ≤ i := by simp [List.length_cons] at hiLen; omega
    let j := i - 1
    have hj : w.length ≤ j := by
      dsimp [j]
      simp [List.length_cons] at hiLen
      omega
    have hjB : j < B := by
      dsimp [j]
      omega
    have h' := hwblank j hj hjB
    dsimp [j] at h'
    have hidx : base + 1 + (i - 1) = base + i := by omega
    simpa [hidx] using h'

lemma bounded_suffix_extract {τ : Literal.Assignment} (base B : ℕ)
    (hfree : ∀ i, i < B →
      τ (cellVar 0 (base + i) (letterIdx (none : Option Bool))) = true ∨
      τ (cellVar 0 (base + i) (letterIdx (some false))) = true ∨
      τ (cellVar 0 (base + i) (letterIdx (some true))) = true)
    (hNoHole : ∀ i, i < B →
      τ (cellVar 0 (base + i) (letterIdx (none : Option Bool))) = true →
      τ (cellVar 0 (base + i + 1) (letterIdx (none : Option Bool))) = true) :
    ∃ w : List Bool, w.length ≤ B ∧
      (∀ i, i < w.length →
        τ (cellVar 0 (base + i) (letterIdx (some (w.getI i)))) = true) ∧
      (∀ i, w.length ≤ i → i < B →
        τ (cellVar 0 (base + i) (letterIdx (none : Option Bool))) = true) := by
  induction B generalizing base with
  | zero =>
      refine ⟨[], by simp, ?_, ?_⟩
      · intro i hi
        simp at hi
      · intro i hiB hi
        omega
  | succ B ih =>
      by_cases hnone :
          τ (cellVar 0 base (letterIdx (none : Option Bool))) = true
      · have hall : ∀ i, i < B + 1 →
            τ (cellVar 0 (base + i) (letterIdx (none : Option Bool))) = true := by
          intro i hi
          induction i with
          | zero => simpa using hnone
          | succ i hiInd =>
              exact hNoHole i (by omega) (hiInd (by omega))
        refine ⟨[], by simp, ?_, ?_⟩
        · intro i hi
          simp at hi
        · intro i _ hi
          exact hall i hi
      · obtain hcase := hfree 0 (by omega)
        rcases hcase with hnone' | hbit
        · exact (hnone hnone').elim
        · obtain ⟨w, hwlen, hwassign, hwblank⟩ := ih (base := base + 1)
            (fun i hi => by
              have h := hfree (i + 1) (Nat.succ_lt_succ hi)
              simpa only [Nat.add_assoc, Nat.add_comm i 1] using h)
            (fun i hi h => by
              have hshift :
                  τ (cellVar 0 (base + (i + 1))
                    (letterIdx (none : Option Bool))) = true := by
                simpa only [Nat.add_assoc, Nat.add_comm i 1] using h
              have h' := hNoHole (i + 1) (Nat.succ_lt_succ hi) hshift
              simpa only [Nat.add_assoc, Nat.add_comm i 1] using h')
          rcases hbit with hfalse | htrue
          · exact bounded_suffix_extract_cons base B false hfalse hwlen hwassign hwblank
          · exact bounded_suffix_extract_cons base B true htrue hwlen hwassign hwblank


lemma getI_map_some (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map some).getI i = some (w.getI i) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons b w ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (some b :: w.map some).getI (i + 1) = some (w.getI i)
          rw [List.getI_cons_succ]
          exact ih i (by simpa using hi)

lemma cell_value_false_of_uniqueness [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {S : Finset Λ} {W T p : ℕ} {τ : Literal.Assignment} {a b : Γ}
    (huniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied τ)
    (hp : p < W) (ha : τ (cellVar 0 p (letterIdx a)) = true)
    (hab : a ≠ b) :
    τ (cellVar 0 p (letterIdx b)) = false := by
  cases hb : τ (cellVar 0 p (letterIdx b)) with
  | false => rfl
  | true =>
      have hAtMost : ∀ c ∈ atMostOne
          ((letters Γ).map fun a => cellVar 0 p (letterIdx a)),
          c.Satisfied τ := by
        intro c hc
        apply huniq
        simp only [uniquenessClauses, List.mem_flatMap]
        refine ⟨0, List.mem_range.mpr (Nat.zero_lt_succ T), ?_⟩
        simp only [List.mem_append]
        right
        refine List.mem_flatMap.mpr ?_
        refine ⟨p, List.mem_range.mpr (by omega), ?_⟩
        simpa [exactlyOne] using (List.mem_cons_of_mem _ hc)
      have hmemA : cellVar 0 p (letterIdx a) ∈
          (letters Γ).map (fun a => cellVar 0 p (letterIdx a)) := by
        exact List.mem_map.mpr ⟨a, mem_letters a, rfl⟩
      have hmemB : cellVar 0 p (letterIdx b) ∈
          (letters Γ).map (fun a => cellVar 0 p (letterIdx a)) := by
        exact List.mem_map.mpr ⟨b, mem_letters b, rfl⟩
      have heq := atMostOne_unique τ
        ((letters Γ).map fun a => cellVar 0 p (letterIdx a))
        hAtMost _ _ hmemA hmemB ha hb
      have hidx : letterIdx a = letterIdx b :=
        (cellVar_eq_iff.mp heq).2.2
      exact (hab (letterIdx_inj hidx)).elim

/-- The tableau core parameterized by its initial-configuration clauses. -/
noncomputable def tableauMachineWithInit [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset Λ) (input output : List Γ) (T : ℕ)
    (initial : List Clause) : CNF :=
  let W := windowSize input.length output.length T
  ⟨uniquenessClauses (Γ := Γ) S W T ++
      initial ++
        transClauses M S W T ++
          persistClauses (Γ := Γ) W T ++
            acceptClauses M S output W T⟩

/-- Semantic Cook-Levin tableau: local TM0 constraints as an unbounded CNF. -/
noncomputable def tableauMachine [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (input output : List Γ) (T : ℕ) : CNF :=
  tableauMachineWithInit M S input output T
    (initClauses S input (windowSize input.length output.length T) T)

/-- Boolean-accept tableau whose accepting output is the tape word `tapeSymbols [true]`. -/
noncomputable def tableau [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : Finset Λ) (x : List Bool) (T : ℕ) : CNF :=
  tableauMachine M S (tapeSymbols x) (tapeSymbols [true]) T

noncomputable def TM0ComputableAux.tableau (tm : TM0ComputableAux Bool)
    (x : List Bool) (T : ℕ) : CNF :=
  CookLevin.tableau tm.M tm.S x T

noncomputable def tableauFin (tm : FinTM0) [DecidableEq tm.Γ] [DecidableEq tm.Λ]
    (input output : List tm.Γ) (T : ℕ) : CNF :=
  tableauMachine tm.M tm.S input output T

end NPComplete.CookLevin

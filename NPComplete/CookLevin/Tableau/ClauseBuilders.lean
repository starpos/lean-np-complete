module

public import NPComplete.CookLevin.Tableau.Alphabet

/-!
# Boolean clause builders

Tableau constraints are assembled from small Boolean clauses whose meaning must be explicit. This
module proves the semantics of the unit, implication, exclusion, and exactly-one builders so
machine-specific clause families can reuse them.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Local clause constructors -/

def unitPos (v : ℕ) : Clause := ⟨[Literal.pos v]⟩

def forbid3 (a b c : ℕ) : Clause :=
  ⟨[Literal.neg a, Literal.neg b, Literal.neg c]⟩

def imply2 (a b d : ℕ) : Clause :=
  ⟨[Literal.neg a, Literal.neg b, Literal.pos d]⟩

def imply3 (a b c d : ℕ) : Clause :=
  ⟨[Literal.neg a, Literal.neg b, Literal.neg c, Literal.pos d]⟩

def atLeastOne (vs : List ℕ) : Clause := ⟨vs.map Literal.pos⟩

def implyPos (a b : ℕ) : Clause :=
  ⟨[Literal.neg a, Literal.pos b]⟩

def atMostOne : List ℕ → List Clause
  | [] => []
  | v :: vs => vs.map (fun w => ⟨[Literal.neg v, Literal.neg w]⟩) ++ atMostOne vs

def exactlyOne (vs : List ℕ) : List Clause :=
  atLeastOne vs :: atMostOne vs

lemma atMostOne_cons (v : ℕ) (vs : List ℕ) :
    atMostOne (v :: vs) =
      vs.map (fun w => ⟨[Literal.neg v, Literal.neg w]⟩) ++ atMostOne vs :=
  rfl

lemma satisfied_neg_pair {τ : Literal.Assignment} {v w : ℕ}
    (h : Clause.Satisfied τ ⟨[Literal.neg v, Literal.neg w]⟩) (hv : τ v = true) :
    τ w = false := by
  obtain ⟨l, hmem, he⟩ := h
  simp at hmem
  rcases hmem with rfl | rfl
  · simp [Literal.eval, hv] at he
  · simpa [Literal.eval] using he

lemma atMostOne_unique (τ : Literal.Assignment) (vs : List ℕ)
    (hsat : ∀ c ∈ atMostOne vs, c.Satisfied τ) (i j : ℕ)
    (hi : i ∈ vs) (hj : j ∈ vs) (hti : τ i = true) (htj : τ j = true) :
    i = j := by
  induction vs generalizing i j with
  | nil => cases hi
  | cons v vs ih =>
      have hpair : ∀ w ∈ vs, Clause.Satisfied τ ⟨[Literal.neg v, Literal.neg w]⟩ := by
        intro w hw
        exact hsat _ (by simp [atMostOne_cons, hw])
      have htail : ∀ c ∈ atMostOne vs, c.Satisfied τ := by
        intro c hc
        exact hsat _ (by simp [atMostOne_cons, hc])
      simp only [List.mem_cons] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · rfl
      · have := satisfied_neg_pair (hpair j hj) hti
        simp [htj] at this
      · have := satisfied_neg_pair (hpair i hi) htj
        simp [hti] at this
      · exact ih htail i j hi hj hti htj

lemma satisfied_atMostOne_of_unique {τ : Literal.Assignment} (v₀ : ℕ) :
    ∀ vs : List ℕ, vs.Nodup → (∀ v ∈ vs, τ v = true → v = v₀) →
      ∀ c ∈ atMostOne vs, c.Satisfied τ := by
  intro vs
  induction vs with
  | nil => intro _ _ c hc; simp [atMostOne] at hc
  | cons v vs ih =>
    intro hnodup huniq c hc
    rw [atMostOne_cons] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      have hvw : v ≠ w := fun he => (List.nodup_cons.mp hnodup).1 (he ▸ hw)
      cases htv : τ v with
      | false => exact ⟨Literal.neg v, by simp, by simp [Literal.eval, htv]⟩
      | true =>
        have hveq := huniq v (List.mem_cons_self ..) htv
        cases htw : τ w with
        | false => exact ⟨Literal.neg w, by simp, by simp [Literal.eval, htw]⟩
        | true =>
          exact absurd (hveq.trans (huniq w (List.mem_cons_of_mem _ hw) htw).symm) hvw
    · exact ih (List.nodup_cons.mp hnodup).2
        (fun v' hv' htv' => huniq v' (List.mem_cons_of_mem _ hv') htv') c hc

lemma atLeastOne_exists {τ : Literal.Assignment} {vs : List ℕ}
    (h : (atLeastOne vs).Satisfied τ) : ∃ v ∈ vs, τ v = true := by
  obtain ⟨l, hmem, he⟩ := h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
  exact ⟨v, hv, he⟩

lemma satisfied_atLeastOne {τ : Literal.Assignment} {vs : List ℕ} {v : ℕ}
    (hv : v ∈ vs) (hτ : τ v = true) : (atLeastOne vs).Satisfied τ :=
  ⟨Literal.pos v, List.mem_map.mpr ⟨v, hv, rfl⟩, hτ⟩

/-- `exactlyOne` is satisfied whenever `vs` has a duplicate-free listing and a
designated element `v₀` is the only one `τ` marks true. -/
lemma satisfied_exactlyOne_of_unique {τ : Literal.Assignment} {vs : List ℕ} {v₀ : ℕ}
    (hnodup : vs.Nodup) (hmem : v₀ ∈ vs) (htrue : τ v₀ = true)
    (huniq : ∀ v ∈ vs, τ v = true → v = v₀) :
    ∀ c ∈ exactlyOne vs, c.Satisfied τ := by
  intro c hc
  simp only [exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact satisfied_atLeastOne hmem htrue
  · exact satisfied_atMostOne_of_unique v₀ vs hnodup huniq c hc

lemma satisfied_unitPos {τ : Literal.Assignment} {v : ℕ} (h : τ v = true) :
    (unitPos v).Satisfied τ :=
  Clause.satisfied_pos h

lemma eval_unitPos {τ : Literal.Assignment} {v : ℕ}
    (h : (unitPos v).Satisfied τ) : τ v = true := by
  obtain ⟨l, hmem, he⟩ := h
  simp [unitPos] at hmem
  subst hmem
  exact he

end NPComplete.CookLevin

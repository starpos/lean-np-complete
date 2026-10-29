module

public import NPComplete.CookLevin.Generate.Steps

/-!
# Encoding length bounds

The reduction's running-time analysis needs a concrete bound on serialized CNF
size, not only a bound on clause count. This module supplies length estimates
from variable indices and tableau dimensions, apart from semantic correctness.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

/-! ## Tableau clause / variable size (loose majorants) -/

lemma atMostOne_clause_lits_length_le (vs : List ℕ) {c : Clause}
    (hc : c ∈ atMostOne vs) : c.lits.length ≤ 2 := by
  induction vs with
  | nil => simp [atMostOne] at hc
  | cons v vs ih =>
      rw [atMostOne_cons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
        simp
      · exact ih hc

lemma exactlyOne_clause_lits_length_le (vs : List ℕ) {c : Clause}
    (hc : c ∈ exactlyOne vs) : c.lits.length ≤ vs.length + 2 := by
  simp only [exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp [atLeastOne]
  · exact le_trans (atMostOne_clause_lits_length_le vs hc) (by omega)

end NPComplete.CookLevin

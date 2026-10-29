module

public import NPComplete.CookLevin.Tableau.Layout

/-!
# Tableau alphabet indices

Finite machine symbols and states need collision-free natural indices before tableau clauses can
select them with Boolean variables. This module proves the index properties separately so both
variable layout and local clauses can rely on the same encoding.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Alphabet / state indices -/

noncomputable def letters (Γ : Type*) [Fintype Γ] [DecidableEq Γ] : List Γ :=
  Finset.univ.toList

noncomputable def letterIdx {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (a : Γ) : ℕ :=
  (letters Γ).idxOf a

lemma mem_letters [Fintype Γ] [DecidableEq Γ] (a : Γ) : a ∈ letters Γ := by
  simp [letters]

lemma letterIdx_inj [Fintype Γ] [DecidableEq Γ] {a b : Γ}
    (h : letterIdx a = letterIdx b) : a = b :=
  (List.idxOf_inj (y := b) (mem_letters a)).mp h

lemma letters_nodup [Fintype Γ] [DecidableEq Γ] : (letters Γ).Nodup :=
  Finset.nodup_toList _

noncomputable def stateIdx [DecidableEq Λ] (S : Finset Λ) (q : Λ) : ℕ :=
  S.toList.idxOf q

lemma stateIdx_inj [DecidableEq Λ] {S : Finset Λ} {q₁ q₂ : Λ}
    (h₁ : q₁ ∈ S) (_h₂ : q₂ ∈ S) (he : stateIdx S q₁ = stateIdx S q₂) :
    q₁ = q₂ :=
  (List.idxOf_inj (y := q₂) (Finset.mem_toList.mpr h₁)).mp he

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.VarNumbering

/-!
# Compact tableau layout

Every time, cell, symbol, state, and head choice needs a distinct SAT variable within a computable
bound. This module proves the compact layout's bounds and disjointness once, so clause families can
use it without duplicating index arithmetic.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Explicit compact layout for bounded tableaux -/

lemma div3_mul3 (n : ℕ) : (3 * n) / 3 = n := by omega
lemma div3_mul3_add1 (n : ℕ) : (3 * n + 1) / 3 = n := by omega
lemma div3_mul3_add2 (n : ℕ) : (3 * n + 2) / 3 = n := by omega

lemma cellVar_eq_iff {t₁ p₁ a₁ t₂ p₂ a₂ : ℕ} :
    cellVar t₁ p₁ a₁ = cellVar t₂ p₂ a₂ ↔ t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ := by
  constructor
  · intro h
    have henc : Encodable.encode (t₁, p₁, a₁) = Encodable.encode (t₂, p₂, a₂) := by
      have := congrArg (fun n => n / 3) h
      simpa [cellVar, div3_mul3] using this
    have heq := (Encodable.encode_inj (α := ℕ × ℕ × ℕ)).mp henc
    obtain ⟨rfl, hpa⟩ := Prod.ext_iff.mp heq
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpa
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

lemma stateVar_eq_iff {t₁ q₁ t₂ q₂ : ℕ} :
    stateVar t₁ q₁ = stateVar t₂ q₂ ↔ t₁ = t₂ ∧ q₁ = q₂ := by
  constructor
  · intro h
    have henc : Encodable.encode (t₁, q₁) = Encodable.encode (t₂, q₂) := by
      have := congrArg (fun n => n / 3) h
      simpa [stateVar, div3_mul3_add1] using this
    exact Prod.ext_iff.mp ((Encodable.encode_inj (α := ℕ × ℕ)).mp henc)
  · rintro ⟨rfl, rfl⟩; rfl

lemma headVar_eq_iff {t₁ p₁ t₂ p₂ : ℕ} :
    headVar t₁ p₁ = headVar t₂ p₂ ↔ t₁ = t₂ ∧ p₁ = p₂ := by
  constructor
  · intro h
    have henc : Encodable.encode (t₁, p₁) = Encodable.encode (t₂, p₂) := by
      have := congrArg (fun n => n / 3) h
      simpa [headVar, div3_mul3_add2] using this
    exact Prod.ext_iff.mp ((Encodable.encode_inj (α := ℕ × ℕ)).mp henc)
  · rintro ⟨rfl, rfl⟩; rfl

lemma cellVar_ne_stateVar (t p a t' q : ℕ) : cellVar t p a ≠ stateVar t' q := by
  intro h
  have : cellVar t p a % 3 = stateVar t' q % 3 := congrArg (· % 3) h
  simp [cellVar, stateVar] at this

lemma cellVar_ne_headVar (t p a t' p' : ℕ) : cellVar t p a ≠ headVar t' p' := by
  intro h
  have : cellVar t p a % 3 = headVar t' p' % 3 := congrArg (· % 3) h
  simp [cellVar, headVar] at this

lemma stateVar_ne_headVar (t q t' p : ℕ) : stateVar t q ≠ headVar t' p := by
  intro h
  have : stateVar t q % 3 = headVar t' p % 3 := congrArg (· % 3) h
  simp [stateVar, headVar] at this

end NPComplete.CookLevin

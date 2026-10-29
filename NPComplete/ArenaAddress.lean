module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Data.Nat.Basic

/-!
# Collision-free arithmetic arena addresses

A reduction should be able to reuse the same arithmetic layout without depending on an
operational machine model. Isolating the stride-address function and its injectivity keeps
that layout available to standalone reductions.
-/

@[expose] public section

namespace NPComplete

/-- Denotational address of cell (row `i`, lane `lane`) in a stride-interleaved
    arena based at `arenaBase`.  Lanes below `stride` keep rows disjoint. -/
@[stable_api] def arenaAddr (arenaBase stride i lane : ℕ) : ℕ := arenaBase + stride * i + lane

/-- The arithmetic meaning of `arenaAddr`, stated as an equation so that callers do not depend
    on its definition. -/
@[stable_api] lemma arenaAddr_eq (arenaBase stride i lane : ℕ) :
    arenaAddr arenaBase stride i lane = arenaBase + stride * i + lane := rfl

/-- Distinct `(row, lane)` pairs with lanes below the stride map to distinct
    addresses, so the interleaved arena is collision-free without per-table
    capacity limits. -/
@[stable_api] lemma arenaAddr_ne (arenaBase stride i₁ l₁ i₂ l₂ : ℕ)
    (hl₁ : l₁ < stride) (hl₂ : l₂ < stride) (h : i₁ ≠ i₂ ∨ l₁ ≠ l₂) :
    arenaAddr arenaBase stride i₁ l₁ ≠ arenaAddr arenaBase stride i₂ l₂ := by
  intro heq
  unfold arenaAddr at heq
  rcases Nat.lt_trichotomy i₁ i₂ with hlt | he | hgt
  · have hmul : stride * (i₁ + 1) ≤ stride * i₂ := Nat.mul_le_mul (le_refl stride) hlt
    rw [Nat.mul_succ] at hmul; omega
  · subst he; omega
  · have hmul : stride * (i₂ + 1) ≤ stride * i₁ := Nat.mul_le_mul (le_refl stride) hgt
    rw [Nat.mul_succ] at hmul; omega

end NPComplete

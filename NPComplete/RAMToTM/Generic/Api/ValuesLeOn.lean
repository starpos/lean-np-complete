module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded
public import NPComplete.BoundedWhile.StoreFact
public import Mathlib.Data.Set.Basic

/-!
# Local value bounds with a support

`StoreValuesLe B σ` bounds every cell of the store, but the resource lemmas of a stage only
read a handful of cells.  `ValuesLeOn B S σ` bounds exactly the cells of `S`, so it is a
supported fact (`valuesLeOnFact`) that a stage contract can carry across a footprint, and a
global bound implies it on every support (`valuesLeOn_of_storeValuesLe`).  Resource lemmas
stated over local bounds compose inside stage contracts, while the global bound is restored
only at the packaging boundary.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

/-- **Construction API.** Every cell of `σ` in the support `S` is bounded by `B`. -/
@[construction_api] def ValuesLeOn (B : ℕ) (S : Set ℕ) (σ : Store) : Prop :=
  ∀ a ∈ S, σ a ≤ B

@[construction_api] lemma valuesLeOn_reads_only (B : ℕ) (S : Set ℕ) :
    ReadsOnly (· ∈ S) (ValuesLeOn B S) := by
  intro σ σ' he h a ha
  rw [he a ha]
  exact h a ha

/-- **Construction API.** `ValuesLeOn B S` as a supported fact with support `S`. -/
@[construction_api] def valuesLeOnFact (B : ℕ) (S : Set ℕ) : StoreFact :=
  ⟨ValuesLeOn B S, S, valuesLeOn_reads_only B S⟩

@[construction_api] lemma valuesLeOn_le {B : ℕ} {S : Set ℕ} {σ : Store}
    (h : ValuesLeOn B S σ) {a : ℕ} (ha : a ∈ S) : σ a ≤ B :=
  h a ha

/-- A global bound implies a local bound on every support. -/
@[construction_api] lemma valuesLeOn_of_storeValuesLe {B : ℕ} {S : Set ℕ} {σ : Store}
    (h : StoreValuesLe B σ) : ValuesLeOn B S σ :=
  fun a _ => h a

/-- Support shrinking. -/
@[construction_api] lemma valuesLeOn_mono {B : ℕ} {S S' : Set ℕ} {σ : Store}
    (hsub : S' ⊆ S) (h : ValuesLeOn B S σ) : ValuesLeOn B S' σ :=
  fun a ha => h a (hsub ha)

/-- A union is bounded exactly when both parts are. -/
@[construction_api] lemma valuesLeOn_union {B : ℕ} {S T : Set ℕ} {σ : Store} :
    ValuesLeOn B (S ∪ T) σ ↔ ValuesLeOn B S σ ∧ ValuesLeOn B T σ := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · intro ⟨hS, hT⟩ a ha
    rcases ha with ha | ha
    · exact hS a ha
    · exact hT a ha

@[construction_api] lemma valuesLeOn_singleton {B a : ℕ} {σ : Store} :
    ValuesLeOn B {a} σ ↔ σ a ≤ B := by
  constructor
  · intro h
    exact h a (by simp)
  · intro h b hb
    have : b = a := by simpa using hb
    subst this
    exact h

@[construction_api] lemma valuesLeOn_empty {B : ℕ} {σ : Store} : ValuesLeOn B ∅ σ := by
  intro a ha
  simp at ha

/-- Updating one cell keeps every support bounded when the written value is `≤ B`. -/
@[construction_api] lemma valuesLeOn_writeReg {B r v : ℕ} {S : Set ℕ} {σ : Store}
    (h : ValuesLeOn B S σ) (hv : v ≤ B) : ValuesLeOn B S (writeReg σ r v) := by
  intro a ha
  by_cases heq : a = r
  · subst heq
    simpa [writeReg] using hv
  · rw [writeReg_diff _ _ _ _ heq]
    exact h a ha

/-- A fresh cell joined to the support is bounded after writing a value `≤ B` to it. -/
@[construction_api] lemma valuesLeOn_writeReg_insert {B r v : ℕ} {S : Set ℕ} {σ : Store}
    (h : ValuesLeOn B S σ) (hv : v ≤ B) :
    ValuesLeOn B (insert r S) (writeReg σ r v) := by
  have hS : ValuesLeOn B S (writeReg σ r v) := valuesLeOn_writeReg h hv
  have hr : ValuesLeOn B {r} (writeReg σ r v) := by
    rw [valuesLeOn_singleton]
    simp [writeReg]
    exact hv
  rw [Set.insert_eq, valuesLeOn_union]
  exact ⟨hr, hS⟩

end NPComplete.RAMToTM

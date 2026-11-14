module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BoundedWhile.Frame
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Order.Interval.Set.Basic

/-!
# Store facts with a support

A frame rule needs, for every fact it carries across a stage, a proof that the fact reads only
outside the stage's write footprint.  `StoreFact` bundles the predicate with its support and the
`ReadsOnly` certificate, so the certificate is proved once where a fact is built and is composed
by set algebra afterwards.  The atoms are register-layout independent: a cell, a block of cells,
and conjunction.  Facts about a specific encoding or memory layout are built by the client from
the structure's fields.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

/-- A predicate on stores together with a set of addresses it reads only.

`supp` is an over-approximation of what `holds` depends on, not an exact dependency set. -/
@[construction_api] structure StoreFact where
  holds : Store → Prop
  supp : Set ℕ
  reads_only : ReadsOnly (· ∈ supp) holds

namespace StoreFact

/-- The cell `a` holds `v`. -/
@[construction_api] def cell (a v : ℕ) : StoreFact :=
  ⟨fun σ => σ a = v, {a}, fun _ _ he hσ => (he a rfl).trans hσ⟩

/-- The cells `b, …, b + n - 1` hold `f 0, …, f (n - 1)`. -/
@[construction_api] def block (b n : ℕ) (f : ℕ → ℕ) : StoreFact :=
  ⟨fun σ => ∀ k, k < n → σ (b + k) = f k, Set.Ico b (b + n), fun _ _ he hσ k hk =>
    (he (b + k) ⟨by omega, by omega⟩).trans (hσ k hk)⟩

/-- The trivial fact, with empty support. -/
@[construction_api] def top : StoreFact := ⟨fun _ => True, ∅, fun _ _ _ _ => trivial⟩

/-- Conjunction, with the union of the supports. -/
@[construction_api] def and (F G : StoreFact) : StoreFact :=
  ⟨fun σ => F.holds σ ∧ G.holds σ, F.supp ∪ G.supp, fun σ σ' he ⟨h₁, h₂⟩ =>
    ⟨F.reads_only σ σ' (fun r hr => he r (Or.inl hr)) h₁,
     G.reads_only σ σ' (fun r hr => he r (Or.inr hr)) h₂⟩⟩

/-- Conjunction of a list of facts, associating to the right. -/
@[construction_api] def bigAnd : List StoreFact → StoreFact
  | [] => top
  | [F] => F
  | F :: G :: Fs => F.and (bigAnd (G :: Fs))

@[construction_api] lemma holds_bigAnd : ∀ (Fs : List StoreFact) (σ : Store),
    (bigAnd Fs).holds σ ↔ ∀ F ∈ Fs, F.holds σ
  | [], σ => by simp [bigAnd, top]
  | [F], σ => by simp [bigAnd]
  | F :: G :: Fs, σ => by
    have := holds_bigAnd (G :: Fs) σ
    simp only [bigAnd, and, List.mem_cons, forall_eq_or_imp] at this ⊢
    rw [this]

/-- Disjointness of a list of facts from a footprint reduces to the atoms. -/
@[construction_api] lemma disjoint_bigAnd : ∀ (Fs : List StoreFact) (W : Set ℕ),
    (∀ F ∈ Fs, Disjoint F.supp W) → Disjoint (bigAnd Fs).supp W
  | [], W, _ => by simp [bigAnd, top]
  | [F], W, h => h F (by simp)
  | F :: G :: Fs, W, h => by
    have h2 := disjoint_bigAnd (G :: Fs) W (fun F' hF' => h F' (List.mem_cons_of_mem _ hF'))
    exact Set.disjoint_union_left.mpr ⟨h F (by simp), h2⟩

@[construction_api] lemma disjoint_cell {a v : ℕ} {W : Set ℕ} (h : a ∉ W) :
    Disjoint (cell a v).supp W :=
  Set.disjoint_singleton_left.mpr h

@[construction_api] lemma disjoint_block {b n : ℕ} {f : ℕ → ℕ} {W : Set ℕ}
    (h : ∀ k, k < n → b + k ∉ W) : Disjoint (block b n f).supp W := by
  rw [Set.disjoint_left]
  intro r hr hW
  obtain ⟨h1, h2⟩ := hr
  exact h (r - b) (by omega) (by simpa [Nat.add_sub_cancel' h1] using hW)

/-- A cell whose address lies in the footprint is not disjoint from it. -/
@[construction_api] lemma not_disjoint_cell {a v : ℕ} {W : Set ℕ} (h : a ∈ W) :
    ¬ Disjoint (cell a v).supp W :=
  fun hd => Set.disjoint_singleton_left.mp hd h

end StoreFact

end NPComplete.BoundedWhile

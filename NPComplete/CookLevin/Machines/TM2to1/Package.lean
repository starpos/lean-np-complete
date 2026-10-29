module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range

/-!
A raw `FinTM2` only carries `Fintype` on the input stack alphabet. The Mathlib
translator `TM2to1.tr` itself needs no more, but `TM2to1.Γ'.fintype` does: the
multiplexed tape letter is a product over every stack.
Every non-input symbol that can appear is the image of a `push` from the finite
state type `σ`, so a subtype wrapper supplies the required instances and reuses
`tr` unchanged.
-/

@[expose] public section

namespace NPComplete.CookLevin.TM2to1

open Turing TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K]

/-- Symbols a statement can write onto stack `k`. Only `push` contributes. -/
def stmtPushRange (k : K) : Stmt Γ Λ σ → Set (Γ k)
  | .push k' f q =>
      (if h : k' = k then Set.range (fun s => h ▸ f s) else ∅) ∪ stmtPushRange k q
  | .peek _ _ q => stmtPushRange k q
  | .pop _ _ q => stmtPushRange k q
  | .load _ q => stmtPushRange k q
  | .branch _ q₁ q₂ => stmtPushRange k q₁ ∪ stmtPushRange k q₂
  | .goto _ => ∅
  | .halt => ∅

lemma stmtPushRange_finite [Finite σ] (k : K) (q : Stmt Γ Λ σ) :
    (stmtPushRange k q).Finite := by
  induction q with
  | push k' f q ih =>
    refine Set.Finite.union ?_ ih
    split_ifs
    · exact Set.finite_range _
    · exact Set.finite_empty
  | peek _ _ _ ih => exact ih
  | pop _ _ _ ih => exact ih
  | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

lemma stmtPushRange_push_subset (k k' : K) (f : σ → Γ k') (q : Stmt Γ Λ σ) :
    stmtPushRange k q ⊆ stmtPushRange k (.push k' f q) :=
  Set.subset_union_right

lemma stmtPushRange_peek_eq (k k' : K) (f : σ → Option (Γ k') → σ) (q : Stmt Γ Λ σ) :
    stmtPushRange k (.peek k' f q) = stmtPushRange k q :=
  rfl

lemma stmtPushRange_pop_eq (k k' : K) (f : σ → Option (Γ k') → σ) (q : Stmt Γ Λ σ) :
    stmtPushRange k (.pop k' f q) = stmtPushRange k q :=
  rfl

lemma stmtPushRange_load_eq (k : K) (a : σ → σ) (q : Stmt Γ Λ σ) :
    stmtPushRange k (.load a q) = stmtPushRange k q :=
  rfl

lemma stmtPushRange_branch_left (k : K) (p : σ → Bool) (q₁ q₂ : Stmt Γ Λ σ) :
    stmtPushRange k q₁ ⊆ stmtPushRange k (.branch p q₁ q₂) :=
  Set.subset_union_left

lemma stmtPushRange_branch_right (k : K) (p : σ → Bool) (q₁ q₂ : Stmt Γ Λ σ) :
    stmtPushRange k q₂ ⊆ stmtPushRange k (.branch p q₁ q₂) :=
  Set.subset_union_right

lemma push_mem_stmtPushRange (k : K) (f : σ → Γ k) (q : Stmt Γ Λ σ) (s : σ) :
    f s ∈ stmtPushRange k (.push k f q) := by
  refine Or.inl ?_
  simp only [↓reduceDIte]
  exact ⟨s, rfl⟩

/-- Input letters together with every `push` image of the machine. -/
def usedSymbols (tm : FinTM2) (k : tm.K) : Set (tm.Γ k) :=
  (if k = tm.k₀ then Set.univ else ∅) ∪ ⋃ l, stmtPushRange k (tm.m l)

lemma usedSymbols_finite (tm : FinTM2) (k : tm.K) : (usedSymbols tm k).Finite := by
  let := tm.ΛFin
  let := tm.σFin
  refine Set.Finite.union ?_ ?_
  · split_ifs with h
    · subst h
      let := tm.Γk₀Fin
      exact Set.finite_univ
    · exact Set.finite_empty
  · exact Set.finite_iUnion fun l => stmtPushRange_finite k (tm.m l)

lemma usedSymbols_covers (tm : FinTM2) (l : tm.Λ) (k : tm.K) :
    stmtPushRange k (tm.m l) ⊆ usedSymbols tm k := by
  intro x hx
  exact Or.inr ⟨_, ⟨l, rfl⟩, hx⟩

/-- Finite-support alphabet for stack `k`. -/
def PackΓ (tm : FinTM2) (k : tm.K) : Type :=
  { x : tm.Γ k // x ∈ usedSymbols tm k }

instance packΓ_finite (tm : FinTM2) (k : tm.K) : Finite (PackΓ tm k) :=
  (usedSymbols_finite tm k).to_subtype

noncomputable instance packΓ_fintype (tm : FinTM2) (k : tm.K) : Fintype (PackΓ tm k) :=
  Fintype.ofFinite _

/-- Restrict a statement to the used-symbol subtype. Subterm ranges stay inside
    `usedSymbols` by construction of `stmtPushRange`. -/
def packStmt (tm : FinTM2) :
    (q : Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushRange k q ⊆ usedSymbols tm k) →
    Stmt (PackΓ tm) tm.Λ tm.σ
  | .push k f q, hq =>
      .push k (fun s => ⟨f s, hq k (push_mem_stmtPushRange k f q s)⟩)
        (packStmt tm q fun k' => (stmtPushRange_push_subset k' k f q).trans (hq k'))
  | .peek k f q, hq =>
      .peek k (fun s o => f s (o.map Subtype.val))
        (packStmt tm q fun k' => (stmtPushRange_peek_eq k' k f q).symm ▸ hq k')
  | .pop k f q, hq =>
      .pop k (fun s o => f s (o.map Subtype.val))
        (packStmt tm q fun k' => (stmtPushRange_pop_eq k' k f q).symm ▸ hq k')
  | .load a q, hq =>
      .load a (packStmt tm q fun k' => (stmtPushRange_load_eq k' a q).symm ▸ hq k')
  | .branch p q₁ q₂, hq =>
      .branch p
        (packStmt tm q₁ fun k' => (stmtPushRange_branch_left k' p q₁ q₂).trans (hq k'))
        (packStmt tm q₂ fun k' => (stmtPushRange_branch_right k' p q₁ q₂).trans (hq k'))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- Same machine, every stack alphabet replaced by its used-symbol subtype. -/
noncomputable def packFinTM2 (tm : FinTM2) : FinTM2 :=
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI := packΓ_fintype tm tm.k₀
  FinTM2.mk tm.k₀ tm.k₁ (PackΓ tm) tm.Λ tm.main tm.σ tm.initialState
    (fun l => packStmt tm (tm.m l) (usedSymbols_covers tm l))

/-- Extra data a raw `FinTM2` does not carry. `TM2to1.Γ'.fintype` needs it. -/
abbrev AllStackAlphabetsFinite (tm : FinTM2) : Type :=
  ∀ k, Fintype (tm.Γ k)

/-- Restoring `Fintype K` from the `FinTM2` field plus this extra data makes `Γ'` finite. -/
instance allStackAlphabetsFinite_Γ' (tm : FinTM2) [h : AllStackAlphabetsFinite tm] :
    Fintype (TM2to1.Γ' tm.K tm.Γ) :=
  letI := tm.kFin
  inferInstance

/-- After packaging, the multiplexed TM1 alphabet is finite. `tr` is reused as-is. -/
noncomputable instance pack_Γ'_fintype (tm : FinTM2) :
    Fintype (TM2to1.Γ' tm.K (PackΓ tm)) :=
  letI := tm.kFin
  inferInstance

/-- The packaged program can be fed to the existing translator. -/
noncomputable def packTr (tm : FinTM2) :
    TM2to1.Λ' tm.K (PackΓ tm) tm.Λ tm.σ →
      TM1.Stmt (TM2to1.Γ' tm.K (PackΓ tm))
        (TM2to1.Λ' tm.K (PackΓ tm) tm.Λ tm.σ) tm.σ :=
  TM2to1.tr (packFinTM2 tm).m

end NPComplete.CookLevin.TM2to1

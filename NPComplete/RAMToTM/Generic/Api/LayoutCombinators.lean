module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.LayoutSpec

/-!
# Combinators for layout facts and layout contracts

`LayoutSpec` fixes the contract and the frame rule; a client still has to build memory facts and
discharge the footprint side conditions of `frame_fact` and `weaken`.  Left to each client, those
obligations are rewritten at every stage and every boundary, and a new fact reaches every proof that
mentions the fact's conjunction.  This module states them once:

* `LayoutFact.ofMem` builds a fact over an arbitrary set of memory addresses, so the `mem_above`
  obligation and the `ReadsOnly` certificate are paid at the construction site and nowhere else.
* `Foot.Sep` and `Foot.Le` compose along `union`, and over `LayoutFact.bigAnd` they reduce to a
  statement about each member of the list.  The unfolding lemmas of `and`, `top` and `bigAnd` are
  `rfl` simp lemmas, so a client unfolds a fact with `simp only` instead of `simp [bigAnd]`, which
  would unfold through auxiliary matchers outside the tagged API.
* `LayoutSpec.forN` takes a window per iteration, for loops whose footprint grows with the counter.
* `LayoutSpec.assignCell` writes one cell at or above the layout top, which has no role.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

namespace RegLayout.Foot

variable {Role : Type} {R : RegLayout Role}

@[construction_api] lemma Le.refl (F : Foot R) : F.Le F := ⟨subset_rfl, subset_rfl⟩

@[construction_api] lemma Le.trans {F G H : Foot R} (h₁ : F.Le G) (h₂ : G.Le H) : F.Le H :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

@[construction_api] lemma Sep.symm {F G : Foot R} (h : F.Sep G) : G.Sep F :=
  ⟨h.1.symm, h.2.symm⟩

/-- Footprints that are separated from `H` stay separated after `union`. -/
@[construction_api] lemma Sep.union_left [DecidableEq Role] {F G H : Foot R} (hF : F.Sep H)
    (hG : G.Sep H) : (F.union G).Sep H :=
  ⟨Finset.disjoint_union_left.2 ⟨hF.1, hG.1⟩, Set.disjoint_union_left.2 ⟨hF.2, hG.2⟩⟩

/-- A part of a separated footprint is separated. -/
@[construction_api] lemma Sep.of_le {F G H : Foot R} (hF : F.Le G) (hG : G.Sep H) : F.Sep H :=
  ⟨Finset.disjoint_of_subset_left hF.1 hG.1, Set.disjoint_of_subset_left hF.2 hG.2⟩

@[construction_api] lemma Le.union [DecidableEq Role] {F G H : Foot R} (hF : F.Le H)
    (hG : G.Le H) : (F.union G).Le H :=
  ⟨Finset.union_subset hF.1 hG.1, Set.union_subset hF.2 hG.2⟩

@[construction_api] lemma union_le_iff [DecidableEq Role] {F G H : Foot R} :
    (F.union G).Le H ↔ F.Le H ∧ G.Le H :=
  ⟨fun h => ⟨⟨(Finset.union_subset_iff.1 h.1).1, (Set.union_subset_iff.1 h.2).1⟩,
    ⟨(Finset.union_subset_iff.1 h.1).2, (Set.union_subset_iff.1 h.2).2⟩⟩,
    fun h => Le.union h.1 h.2⟩

@[construction_api] lemma sep_union_left_iff [DecidableEq Role] {F G H : Foot R} :
    (F.union G).Sep H ↔ F.Sep H ∧ G.Sep H :=
  ⟨fun h => ⟨⟨(Finset.disjoint_union_left.1 h.1).1, (Set.disjoint_union_left.1 h.2).1⟩,
    ⟨(Finset.disjoint_union_left.1 h.1).2, (Set.disjoint_union_left.1 h.2).2⟩⟩,
    fun h => Sep.union_left h.1 h.2⟩

@[simp, construction_api] lemma regs_union [DecidableEq Role] (F G : Foot R) :
    (F.union G).regs = F.regs ∪ G.regs := rfl

@[simp, construction_api] lemma mem_union [DecidableEq Role] (F G : Foot R) :
    (F.union G).mem = F.mem ∪ G.mem := rfl

@[simp, construction_api] lemma regs_regsOnly (s : Finset Role) :
    (regsOnly s : Foot R).regs = s := rfl

@[simp, construction_api] lemma mem_regsOnly (s : Finset Role) :
    (regsOnly s : Foot R).mem = ∅ := rfl

@[construction_api] lemma regsOnly_le_iff {s : Finset Role} {H : Foot R} :
    (regsOnly s : Foot R).Le H ↔ s ⊆ H.regs :=
  ⟨fun h => h.1, fun h => ⟨h, Set.empty_subset _⟩⟩

@[construction_api] lemma regsOnly_sep_iff {s : Finset Role} {H : Foot R} :
    (regsOnly s : Foot R).Sep H ↔ Disjoint s H.regs :=
  ⟨fun h => h.1, fun h => ⟨h, Set.empty_disjoint _⟩⟩

/-- A footprint of one cell at or above the layout top. -/
@[construction_api] def cell (a : ℕ) (ha : R.top ≤ a) : Foot R :=
  ⟨∅, {a}, fun _ h => (Set.mem_singleton_iff.1 h) ▸ ha⟩

@[construction_api] lemma denote_cell (a : ℕ) (ha : R.top ≤ a) :
    (cell a ha : Foot R).denote = {a} := by
  simp [denote, cell]

end RegLayout.Foot

namespace LayoutFact

open RegLayout

variable {Role : Type} {R : RegLayout Role}

/-- A fact over the addresses of `S`, all at or above the layout top, from a predicate that reads
only `S`.  Any memory fact whose shape is not an existing constructor is built here. -/
@[construction_api] def ofMem (S : Set ℕ) (above : ∀ a ∈ S, R.top ≤ a) (p : Store → Prop)
    (hp : ReadsOnly (· ∈ S) p) : LayoutFact R :=
  ⟨p, ⟨∅, S, above⟩, by
    have h : (⟨∅, S, above⟩ : Foot R).denote = S := by simp [Foot.denote]
    rw [h]
    exact hp⟩

@[simp, construction_api] lemma holds_ofMem (S : Set ℕ) (above : ∀ a ∈ S, R.top ≤ a)
    (p : Store → Prop) (hp : ReadsOnly (· ∈ S) p) (σ : Store) :
    (ofMem S above p hp : LayoutFact R).holds σ ↔ p σ := Iff.rfl

@[simp, construction_api] lemma regs_foot_ofMem (S : Set ℕ) (above : ∀ a ∈ S, R.top ≤ a)
    (p : Store → Prop) (hp : ReadsOnly (· ∈ S) p) :
    (ofMem S above p hp : LayoutFact R).foot.regs = ∅ := rfl

@[simp, construction_api] lemma mem_foot_ofMem (S : Set ℕ) (above : ∀ a ∈ S, R.top ≤ a)
    (p : Store → Prop) (hp : ReadsOnly (· ∈ S) p) :
    (ofMem S above p hp : LayoutFact R).foot.mem = S := rfl

@[construction_api] lemma ofMem_foot_le_iff {S : Set ℕ} {above : ∀ a ∈ S, R.top ≤ a}
    {p : Store → Prop} {hp : ReadsOnly (· ∈ S) p} {H : Foot R} :
    (ofMem S above p hp).foot.Le H ↔ S ⊆ H.mem :=
  ⟨fun h => h.2, fun h => ⟨Finset.empty_subset _, h⟩⟩

@[construction_api] lemma ofMem_foot_sep_iff {S : Set ℕ} {above : ∀ a ∈ S, R.top ≤ a}
    {p : Store → Prop} {hp : ReadsOnly (· ∈ S) p} {H : Foot R} :
    (ofMem S above p hp).foot.Sep H ↔ Disjoint S H.mem :=
  ⟨fun h => h.2, fun h => ⟨Finset.disjoint_empty_left _, h⟩⟩

@[simp, construction_api] lemma holds_reg (r : Role) (v : ℕ) (σ : Store) :
    (reg r v : LayoutFact R).holds σ ↔ σ (R.reg r) = v := Iff.rfl

@[simp, construction_api] lemma foot_reg (r : Role) (v : ℕ) :
    (reg r v : LayoutFact R).foot = Foot.regsOnly {r} := rfl

@[construction_api] lemma reg_foot_sep_iff {r : Role} {v : ℕ} {H : Foot R} :
    (reg r v : LayoutFact R).foot.Sep H ↔ r ∉ H.regs := by
  rw [foot_reg, Foot.regsOnly_sep_iff]
  simp

@[construction_api] lemma reg_foot_le_iff {r : Role} {v : ℕ} {H : Foot R} :
    (reg r v : LayoutFact R).foot.Le H ↔ r ∈ H.regs := by
  rw [foot_reg, Foot.regsOnly_le_iff]
  simp

@[simp, construction_api] lemma holds_top (σ : Store) : (top : LayoutFact R).holds σ ↔ True :=
  Iff.rfl

@[simp, construction_api] lemma foot_top : (top : LayoutFact R).foot = Foot.regsOnly ∅ := rfl

section BigAnd

variable [DecidableEq Role]

@[simp, construction_api] lemma holds_and (F G : LayoutFact R) (σ : Store) :
    (F.and G).holds σ ↔ F.holds σ ∧ G.holds σ := Iff.rfl

@[simp, construction_api] lemma foot_and (F G : LayoutFact R) :
    (F.and G).foot = F.foot.union G.foot := rfl

@[simp, construction_api] lemma bigAnd_nil : bigAnd ([] : List (LayoutFact R)) = top := rfl

@[simp, construction_api] lemma bigAnd_singleton (F : LayoutFact R) : bigAnd [F] = F := rfl

@[simp, construction_api] lemma bigAnd_cons_cons (F G : LayoutFact R) (Fs : List (LayoutFact R)) :
    bigAnd (F :: G :: Fs) = F.and (bigAnd (G :: Fs)) := rfl

@[construction_api] lemma holds_bigAnd_iff : ∀ (Fs : List (LayoutFact R)) (σ : Store),
    (bigAnd Fs).holds σ ↔ ∀ F ∈ Fs, F.holds σ
  | [], σ => by simp
  | [F], σ => by simp
  | F :: G :: Fs, σ => by
    rw [bigAnd_cons_cons, holds_and, holds_bigAnd_iff (G :: Fs) σ]
    simp

/-- A footprint bounds a conjunction when it bounds every member. -/
@[construction_api] lemma foot_bigAnd_le_iff {H : Foot R} : ∀ Fs : List (LayoutFact R),
    (bigAnd Fs).foot.Le H ↔ ∀ F ∈ Fs, F.foot.Le H
  | [] => by simp [Foot.Le]
  | [F] => by simp
  | F :: G :: Fs => by
    rw [bigAnd_cons_cons, foot_and, Foot.union_le_iff, foot_bigAnd_le_iff (G :: Fs)]
    simp

/-- A footprint is separated from a conjunction when it is separated from every member. -/
@[construction_api] lemma foot_bigAnd_sep_iff {H : Foot R} : ∀ Fs : List (LayoutFact R),
    (bigAnd Fs).foot.Sep H ↔ ∀ F ∈ Fs, F.foot.Sep H
  | [] => by simp [Foot.Sep]
  | [F] => by simp
  | F :: G :: Fs => by
    rw [bigAnd_cons_cons, foot_and, Foot.sep_union_left_iff, foot_bigAnd_sep_iff (G :: Fs)]
    simp

end BigAnd

end LayoutFact

end NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout

namespace LayoutSpec

variable {Role : Type} {R : RegLayout Role}

/-- A loop whose iteration `j` has its own footprint `Wj j`, all inside the loop's `W`. -/
@[construction_api] lemma forN {B N : ℕ} {P : Store → Prop} {n : Expr} {body : Program}
    {I : ℕ → Store → Prop} {Wj : ℕ → Foot R} {W : Foot R} (hN : ∀ σ, P σ → n.eval σ = N)
    (hn : ∀ σ, P σ → ExprBoundedIn B σ n) (hinit : ∀ σ, P σ → I 0 σ)
    (hbody : ∀ j < N, LayoutSpec R B (I j) body (Wj j) (I (j + 1)))
    (hsub : ∀ j < N, (Wj j).Le W) : LayoutSpec R B P (Program.forN n body) W (I N) :=
  StageSpec.forN (Wj := fun j => (Wj j).denote) hN hn hinit hbody
    fun j hj => Foot.denote_mono (hsub j hj)

/-- Writing a cell at or above the layout top, which has no role. -/
@[construction_api] lemma assignCell {B a : ℕ} {P Q : Store → Prop} {e : Expr}
    (ha : R.top ≤ a) (hB : a ≤ B) (he : ∀ σ, P σ → ExprBoundedIn B σ e)
    (hQ : ∀ σ, P σ → Q (writeReg σ a (e.eval σ))) :
    LayoutSpec R B P (.assign a e) (Foot.cell a ha) Q := by
  show StageSpec B P (.assign a e) (Foot.cell a ha : Foot R).denote Q
  rw [Foot.denote_cell]
  exact StageSpec.assign hB he hQ

end LayoutSpec

end NPComplete.RAMToTM

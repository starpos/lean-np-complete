module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BoundedWhile.RegLayout
public import NPComplete.BoundedWhile.StoreFact
public import NPComplete.RAMToTM.Generic.Api.StageSpec
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union

/-!
# Stage contracts over a register layout

A stage footprint over a layout has two parts that are separated for different reasons: the roles
it may write, whose registers are distinct by injectivity of the layout, and the memory cells it
may write, which lie at or above the layout top and so never meet a register.  Splitting the
footprint this way turns the side condition of the frame rule into a role-set separation (decided
on concrete finite sets) and an interval separation, and the register/memory separation holds by
construction.

The semantics stays in `StageSpec`; this module only changes how footprints and supported facts
are written.  The guarantee is that of `StageSpec`: the footprint is a reserved region, and the
final store agrees with the initial one outside it.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

namespace RegLayout

/-- A reserved region over a layout: some roles and some addresses at or above the layout top. -/
@[construction_api] structure Foot {Role : Type} (R : RegLayout Role) where
  regs : Finset Role
  mem : Set ℕ
  mem_above : ∀ a ∈ mem, R.top ≤ a

namespace Foot

variable {Role : Type} {R : RegLayout Role}

/-- The addresses a footprint stands for. -/
@[construction_api] def denote (F : Foot R) : Set ℕ :=
  ((F.regs.image R.reg : Finset ℕ) : Set ℕ) ∪ F.mem

/-- Separation, componentwise. -/
@[construction_api] def Sep (F G : Foot R) : Prop :=
  Disjoint F.regs G.regs ∧ Disjoint F.mem G.mem

/-- Inclusion, componentwise. -/
@[construction_api] def Le (F G : Foot R) : Prop := F.regs ⊆ G.regs ∧ F.mem ⊆ G.mem

@[construction_api] def union [DecidableEq Role] (F G : Foot R) : Foot R :=
  ⟨F.regs ∪ G.regs, F.mem ∪ G.mem, fun a ha => ha.elim (F.mem_above a) (G.mem_above a)⟩

/-- A footprint of registers only. -/
@[construction_api] def regsOnly (s : Finset Role) : Foot R := ⟨s, ∅, by simp⟩

@[construction_api] lemma mem_denote {F : Foot R} {x : ℕ} :
    x ∈ F.denote ↔ (∃ r ∈ F.regs, R.reg r = x) ∨ x ∈ F.mem := by
  simp [denote]

@[construction_api] lemma reg_mem_denote {F : Foot R} {r : Role} (h : r ∈ F.regs) :
    R.reg r ∈ F.denote :=
  mem_denote.2 (Or.inl ⟨r, h, rfl⟩)

@[construction_api] lemma denote_regsOnly_singleton (r : Role) :
    (regsOnly {r} : Foot R).denote = {R.reg r} := by
  ext x
  simp [mem_denote, regsOnly, eq_comm]

@[construction_api] lemma denote_union [DecidableEq Role] (F G : Foot R) :
    (F.union G).denote = F.denote ∪ G.denote := by
  ext x
  simp only [mem_denote, union, Finset.mem_union, Set.mem_union]
  constructor
  · rintro (⟨r, hr | hr, he⟩ | h | h)
    · exact Or.inl (Or.inl ⟨r, hr, he⟩)
    · exact Or.inr (Or.inl ⟨r, hr, he⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((⟨r, hr, he⟩ | h) | (⟨r, hr, he⟩ | h))
    · exact Or.inl ⟨r, Or.inl hr, he⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨r, Or.inr hr, he⟩
    · exact Or.inr (Or.inr h)

@[construction_api] lemma denote_mono {F G : Foot R} (h : F.Le G) : F.denote ⊆ G.denote := by
  intro x hx
  rcases mem_denote.1 hx with ⟨r, hr, he⟩ | hm
  · exact mem_denote.2 (Or.inl ⟨r, h.1 hr, he⟩)
  · exact mem_denote.2 (Or.inr (h.2 hm))

/-- Separation of footprints is exactly disjointness of the addresses they stand for. -/
@[construction_api] lemma disjoint_denote_iff {F G : Foot R} :
    Disjoint F.denote G.denote ↔ F.Sep G := by
  constructor
  · intro h
    refine ⟨Finset.disjoint_left.2 fun r hF hG => ?_, Set.disjoint_left.2 fun a hF hG => ?_⟩
    · exact h.le_bot ⟨reg_mem_denote hF, reg_mem_denote hG⟩
    · exact h.le_bot ⟨mem_denote.2 (Or.inr hF), mem_denote.2 (Or.inr hG)⟩
  · rintro ⟨hr, hm⟩
    refine Set.disjoint_left.2 fun x hF hG => ?_
    rcases mem_denote.1 hF with ⟨r, hrF, rfl⟩ | haF <;>
      rcases mem_denote.1 hG with ⟨r', hrG, he⟩ | haG
    · exact Finset.disjoint_left.1 hr hrF (R.reg_injective he ▸ hrG)
    · exact absurd (R.reg_lt_of_top_le r (G.mem_above _ haG)) (Nat.lt_irrefl _)
    · exact absurd (R.reg_lt_of_top_le r' (F.mem_above _ haF)) (he ▸ Nat.lt_irrefl _)
    · exact Set.disjoint_left.1 hm haF haG

end Foot

end RegLayout

open RegLayout

/-- A store fact with a footprint over the layout and the certificate that it reads nothing
else. -/
@[construction_api] structure LayoutFact {Role : Type} (R : RegLayout Role) where
  holds : Store → Prop
  foot : Foot R
  reads_only : ReadsOnly (· ∈ foot.denote) holds

namespace LayoutFact

variable {Role : Type} {R : RegLayout Role}

/-- Forget the layout structure; the support is the denotation of the footprint. -/
@[construction_api] def toStoreFact (F : LayoutFact R) : StoreFact :=
  ⟨F.holds, F.foot.denote, F.reads_only⟩

/-- The register of a role holds a value. -/
@[construction_api] def reg (r : Role) (v : ℕ) : LayoutFact R :=
  ⟨fun σ => σ (R.reg r) = v, Foot.regsOnly {r}, by
    rw [Foot.denote_regsOnly_singleton]
    exact (StoreFact.cell (R.reg r) v).reads_only⟩

/-- The cells `b, …, b + n - 1` hold `f 0, …, f (n - 1)`; the interval must lie at or above the
layout top. -/
@[construction_api] def block (b n : ℕ) (f : ℕ → ℕ) (hb : R.top ≤ b) : LayoutFact R :=
  ⟨fun σ => ∀ k, k < n → σ (b + k) = f k, ⟨∅, Set.Ico b (b + n), fun _ ha => hb.trans ha.1⟩, by
    have h : (⟨∅, Set.Ico b (b + n), fun _ ha => hb.trans ha.1⟩ : Foot R).denote =
        Set.Ico b (b + n) := by
      simp [Foot.denote]
    rw [h]
    exact (StoreFact.block b n f).reads_only⟩

/-- The trivial fact, with empty footprint. -/
@[construction_api] def top : LayoutFact R :=
  ⟨fun _ => True, Foot.regsOnly ∅, fun _ _ _ _ => trivial⟩

/-- Conjunction, with the union of the footprints. -/
@[construction_api] def and [DecidableEq Role] (F G : LayoutFact R) : LayoutFact R :=
  ⟨fun σ => F.holds σ ∧ G.holds σ, F.foot.union G.foot, by
    rw [Foot.denote_union]
    exact (F.toStoreFact.and G.toStoreFact).reads_only⟩

/-- Conjunction of a list of facts, associating to the right. -/
@[construction_api] def bigAnd [DecidableEq Role] : List (LayoutFact R) → LayoutFact R
  | [] => top
  | [F] => F
  | F :: G :: Fs => F.and (bigAnd (G :: Fs))

end LayoutFact

end NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout

/-- A stage contract whose footprint is a `Foot` of the layout. -/
@[construction_api] abbrev LayoutSpec {Role : Type} (R : RegLayout Role) (B : ℕ)
    (P : Store → Prop) (p : Program) (W : Foot R) (Q : Store → Prop) : Prop :=
  StageSpec B P p W.denote Q

namespace LayoutSpec

variable {Role : Type} {R : RegLayout Role}

@[construction_api] lemma seq [DecidableEq Role] {B : ℕ} {P M Q : Store → Prop}
    {W₁ W₂ : Foot R} {p q : Program} (h₁ : LayoutSpec R B P p W₁ M)
    (h₂ : LayoutSpec R B M q W₂ Q) : LayoutSpec R B P (p.seq q) (W₁.union W₂) Q := by
  show StageSpec B P (p.seq q) (W₁.union W₂).denote Q
  rw [Foot.denote_union]
  exact StageSpec.seq h₁ h₂

@[construction_api] lemma weaken {B : ℕ} {P P' Q Q' : Store → Prop} {p : Program}
    {W W' : Foot R} (h : LayoutSpec R B P p W Q) (hP : ∀ σ, P' σ → P σ) (hW : W.Le W')
    (hQ : ∀ σ, Q σ → Q' σ) : LayoutSpec R B P' p W' Q' :=
  StageSpec.weaken h hP (Foot.denote_mono hW) hQ

/-- The frame rule: a fact survives a stage whose footprint is separated from the fact's. -/
@[construction_api] lemma frame_fact {B : ℕ} {P Q : Store → Prop} {W : Foot R} {p : Program}
    (h : LayoutSpec R B P p W Q) (F : LayoutFact R) (hd : F.foot.Sep W) :
    LayoutSpec R B (fun σ => P σ ∧ F.holds σ) p W (fun σ => Q σ ∧ F.holds σ) :=
  StageSpec.frame_fact h F.toStoreFact (Foot.disjoint_denote_iff.2 hd)

/-- The frame rule for a stage that writes registers only: the single condition is the separation
of role sets, which `decide` checks on a concrete layout. -/
@[construction_api] lemma frame_fact_regs {B : ℕ} {P Q : Store → Prop} {A : Finset Role}
    {p : Program} (h : LayoutSpec R B P p (Foot.regsOnly A) Q) (F : LayoutFact R)
    (hd : Disjoint F.foot.regs A) :
    LayoutSpec R B (fun σ => P σ ∧ F.holds σ) p (Foot.regsOnly A) (fun σ => Q σ ∧ F.holds σ) :=
  frame_fact h F ⟨hd, Set.disjoint_empty _⟩

@[construction_api] lemma assign {B : ℕ} {r : Role} {P Q : Store → Prop} {e : Expr}
    (hr : R.reg r ≤ B) (he : ∀ σ, P σ → ExprBoundedIn B σ e)
    (hQ : ∀ σ, P σ → Q (writeReg σ (R.reg r) (e.eval σ))) :
    LayoutSpec R B P (.assign (R.reg r) e) (Foot.regsOnly {r}) Q := by
  show StageSpec B P (.assign (R.reg r) e) (Foot.regsOnly {r}).denote Q
  rw [Foot.denote_regsOnly_singleton]
  exact StageSpec.assign hr he hQ

/-- Entry for a stage written as a plain program: the footprint comes from an `Avoids`
certificate, correctness and the resource bound from a direct argument. -/
@[construction_api] lemma of_direct {B : ℕ} {P Q : Store → Prop} {p : Program} {W : Foot R}
    (hc : p.Avoids (· ∉ W.denote)) (hQ : ∀ σ, P σ → Q (p.eval σ))
    (hb : ∀ σ, P σ → ProgramBoundedIn B σ p) : LayoutSpec R B P p W Q :=
  StageSpec.of_avoids hc hQ hb

/-- A loop whose body has the loop's own footprint. -/
@[construction_api] lemma forN_fixed {B N : ℕ} {P : Store → Prop} {n : Expr} {body : Program}
    {I : ℕ → Store → Prop} {W : Foot R} (hN : ∀ σ, P σ → n.eval σ = N)
    (hn : ∀ σ, P σ → ExprBoundedIn B σ n) (hinit : ∀ σ, P σ → I 0 σ)
    (hbody : ∀ j < N, LayoutSpec R B (I j) body W (I (j + 1))) :
    LayoutSpec R B P (Program.forN n body) W (I N) :=
  StageSpec.forN hN hn hinit hbody fun _ _ => subset_rfl

end LayoutSpec

end NPComplete.RAMToTM

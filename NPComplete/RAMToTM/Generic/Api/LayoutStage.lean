module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
public import NPComplete.RAMToTM.Generic.Api.LayoutCombinators

/-!
# Stages that bundle a program with its contract

`LayoutSpec` states a contract over raw stores: its pre- and postcondition are predicates on
`Store`, and the combinators ask for the facts that tie a loop count or an invariant to a store.  A
client that composes stages with it ends up writing store formulas at every composition.
`LayoutStage R B p P Q W` is the same contract with the program `p`, the facts `P`, `Q` and the
reserved footprint `W` as indices, so a composition is stated by naming facts and footprints and
never mentions a store.

The semantics is `LayoutSpec`.  The combinators `seq`, `frame`, `weaken`, `forNConst` and
`forNReg` are the corresponding `LayoutSpec` lemmas with the store-level obligations replaced by
obligations on facts.  In a loop every iteration is a contract of the same body program, which is
fixed by the type.

`LayoutStage.ofSpec` is the one entry that imports a contract proved on raw stores.  It is
marked `stage_adapter`, so `#check_stage_discipline` lets only implementation-side declarations
use it.  The guarantee is that of `LayoutSpec`: the footprint is a reserved region, not an exact
write set.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout

/-- The program `p` takes a store satisfying the fact `P` to one satisfying `Q`, within the reserved
footprint `W` and the resource bound `B`. -/
@[construction_api] structure LayoutStage {Role : Type} (R : RegLayout Role) (B : ℕ)
    (p : Program) (P Q : LayoutFact R) (W : Foot R) : Prop where
  spec : LayoutSpec R B P.holds p W Q.holds

namespace LayoutStage

variable {Role : Type} {R : RegLayout Role}

/-- The entry for a contract proved on raw stores. -/
@[construction_api, stage_adapter] lemma ofSpec {B : ℕ} {p : Program} {P Q : LayoutFact R}
    {W : Foot R} (h : LayoutSpec R B P.holds p W Q.holds) : LayoutStage R B p P Q W :=
  ⟨h⟩

@[construction_api] lemma seq [DecidableEq Role] {B : ℕ} {p q : Program} {P M Q : LayoutFact R}
    {W₁ W₂ : Foot R} (h₁ : LayoutStage R B p P M W₁) (h₂ : LayoutStage R B q M Q W₂) :
    LayoutStage R B (p.seq q) P Q (W₁.union W₂) :=
  ⟨h₁.spec.seq h₂.spec⟩

/-- Consequence: a stronger precondition, a larger footprint and a weaker postcondition. -/
@[construction_api] lemma weaken {B : ℕ} {p : Program} {P P' Q Q' : LayoutFact R}
    {W W' : Foot R} (h : LayoutStage R B p P Q W) (hP : ∀ σ, P'.holds σ → P.holds σ)
    (hW : W.Le W') (hQ : ∀ σ, Q.holds σ → Q'.holds σ) : LayoutStage R B p P' Q' W' :=
  ⟨h.spec.weaken hP hW hQ⟩

/-- The frame rule: a fact whose footprint is separated from the stage's survives it. -/
@[construction_api] lemma frame [DecidableEq Role] {B : ℕ} {p : Program} {P Q : LayoutFact R}
    {W : Foot R} (h : LayoutStage R B p P Q W) (F : LayoutFact R) (hd : F.foot.Sep W) :
    LayoutStage R B p (P.and F) (Q.and F) W :=
  ⟨h.spec.frame_fact F hd⟩

/-- A loop that runs `N` times, the same body at every iteration.  The invariant `I j` is a fact, the
body of iteration `j` stays in the window `Wj j`, and the loop reserves `W`. -/
@[construction_api] lemma forNConst {B N : ℕ} {body : Program} {P : LayoutFact R}
    {I : ℕ → LayoutFact R} {Wj : ℕ → Foot R} {W : Foot R} (hN : N ≤ B)
    (hinit : ∀ σ, P.holds σ → (I 0).holds σ)
    (hbody : ∀ j < N, LayoutStage R B body (I j) (I (j + 1)) (Wj j))
    (hsub : ∀ j < N, (Wj j).Le W) :
    LayoutStage R B (Program.forN (.const N) body) P (I N) W :=
  ⟨LayoutSpec.forN (I := fun j => (I j).holds) (fun _ _ => rfl) (fun _ _ => hN) hinit
    (fun j hj => (hbody j hj).spec) hsub⟩

/-- A loop whose count is held in the register of a role, as the fact `LayoutFact.reg r N`. -/
@[construction_api] lemma forNReg {B N : ℕ} {r : Role} {body : Program} {P : LayoutFact R}
    {I : ℕ → LayoutFact R} {Wj : ℕ → Foot R} {W : Foot R} (hB : R.top ≤ B)
    (hcount : ∀ σ, P.holds σ → (LayoutFact.reg r N : LayoutFact R).holds σ)
    (hinit : ∀ σ, P.holds σ → (I 0).holds σ)
    (hbody : ∀ j < N, LayoutStage R B body (I j) (I (j + 1)) (Wj j))
    (hsub : ∀ j < N, (Wj j).Le W) :
    LayoutStage R B (Program.forN (.reg (R.reg r)) body) P (I N) W :=
  ⟨LayoutSpec.forN (I := fun j => (I j).holds) hcount
    (fun _ _ => Nat.le_of_lt (Nat.lt_of_lt_of_le (R.reg_lt_top r) hB)) hinit
    (fun j hj => (hbody j hj).spec) hsub⟩

end LayoutStage

end NPComplete.RAMToTM

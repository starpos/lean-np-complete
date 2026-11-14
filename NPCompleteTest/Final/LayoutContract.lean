module

import NPComplete

/-!
# Layout layer of the stage contract, plain `import NPComplete` from a module

Expected: a client builds a layout over its own role type and checks injectivity with `decide`,
builds footprints and layout facts, separates them (roles by `decide`, memory by `simp`), and
composes `LayoutSpec` without touching a program body, with no `public import`.
-/

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout NPComplete.RAMToTM

inductive ImpRole | a | b | c
  deriving DecidableEq

def ImpRole.list : List ImpRole := [.a, .b, .c]

lemma ImpRole.mem_list (r : ImpRole) : r ∈ ImpRole.list := by
  cases r <;> simp [ImpRole.list]

def impL : RegLayout ImpRole :=
  ⟨4, ⟨fun | .a => 0 | .b => 1 | .c => 2,
    pairwise_ne_injective ImpRole.mem_list (by decide)⟩⟩

example : impL.reg .a ≠ impL.reg .b := impL.reg_ne (by decide)

example : impL.reg .c < impL.top := impL.reg_lt_top .c

def impFoot : impL.Foot := ⟨{.a}, {10}, by simp [impL]⟩

def impOther : impL.Foot := ⟨{.b}, {20}, by simp [impL]⟩

example : impOther.Sep impFoot := ⟨by decide, by simp [impOther, impFoot]⟩

example : Disjoint impOther.denote impFoot.denote :=
  Foot.disjoint_denote_iff.2 ⟨by decide, by simp [impOther, impFoot]⟩

example : ¬ impFoot.Sep impFoot := fun ⟨h, _⟩ => absurd h (by decide)

def impFact : LayoutFact impL :=
  (LayoutFact.reg .b 3).and (LayoutFact.block 20 1 (fun _ => 4) (by simp [impL]))

example (σ : Store) (h : impFact.holds σ) : σ (impL.reg .b) = 3 := h.1

example : impFact.toStoreFact.supp = impFact.foot.denote := rfl

example (σ : Store) : impFact.toStoreFact.holds σ ↔ impFact.holds σ := Iff.rfl

example (σ : Store) (h : (LayoutFact.bigAnd [LayoutFact.reg .a 1, LayoutFact.reg .b 2,
    (LayoutFact.reg .c 3 : LayoutFact impL)]).holds σ) : σ (impL.reg .c) = 3 := h.2.2

example {B : ℕ} (hB : impL.reg .a ≤ B) (hB1 : 1 ≤ B) :
    LayoutSpec impL B (fun _ => True) (.assign (impL.reg .a) (.const 1)) (Foot.regsOnly {.a})
      (fun σ => σ (impL.reg .a) = 1) :=
  LayoutSpec.assign hB (fun _ _ => by simpa [ExprBoundedIn] using hB1) (by simp [Expr.eval])

example {B : ℕ} {P Q M : Store → Prop} {p q : Program} {W₁ W₂ : Foot impL}
    (h₁ : LayoutSpec impL B P p W₁ M) (h₂ : LayoutSpec impL B M q W₂ Q) :
    LayoutSpec impL B P (p.seq q) (W₁.union W₂) Q := h₁.seq h₂

example {B : ℕ} {P Q : Store → Prop} {p : Program}
    (h : LayoutSpec impL B P p (Foot.regsOnly {.a}) Q) :
    LayoutSpec impL B (fun σ => P σ ∧ impFact.holds σ) p (Foot.regsOnly {.a})
      (fun σ => Q σ ∧ impFact.holds σ) :=
  h.frame_fact impFact ⟨by decide, Set.disjoint_empty _⟩

example {B : ℕ} {P Q : Store → Prop} {p : Program}
    (h : LayoutSpec impL B P p (Foot.regsOnly {.a}) Q) :
    LayoutSpec impL B (fun σ => P σ ∧ impFact.holds σ) p (Foot.regsOnly {.a})
      (fun σ => Q σ ∧ impFact.holds σ) :=
  h.frame_fact_regs impFact (by decide)

example {B : ℕ} {P Q : Store → Prop} {p : Program} {W W' : Foot impL}
    (h : LayoutSpec impL B P p W Q) (hW : W.Le W') : LayoutSpec impL B P p W' Q :=
  h.weaken (fun _ h => h) hW (fun _ h => h)

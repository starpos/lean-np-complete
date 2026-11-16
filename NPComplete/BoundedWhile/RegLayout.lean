module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Pairwise

/-!
# Register layouts

A register layout is one embedding of a role type into `Fin top`, so every distinctness and
below-`top` fact about registers follows from injectivity instead of being re-derived in each
statement.  The role type is a parameter and no resource or program family is mentioned, so the
same mechanism serves any construction.

Injectivity of a concrete placement is established by `decide` on a pairwise list, because
`Function.Injective` itself is not decidable and `deriving Fintype` is not available for the role
types here.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

/-- One register per role, all below `top`. -/
@[construction_api] structure RegLayout (Role : Type) where
  top : ℕ
  regs : Role ↪ Fin top

namespace RegLayout

/-- The register number of a role. -/
@[construction_api] def reg {Role : Type} (R : RegLayout Role) (role : Role) : ℕ := R.regs role

@[construction_api] lemma reg_injective {Role : Type} (R : RegLayout Role) :
    Function.Injective R.reg :=
  fun _ _ h => R.regs.injective (Fin.val_inj.mp h)

@[construction_api] lemma reg_ne {Role : Type} (R : RegLayout Role) {a b : Role} (h : a ≠ b) :
    R.reg a ≠ R.reg b :=
  fun he => h (R.reg_injective he)

@[construction_api] lemma reg_lt_top {Role : Type} (R : RegLayout Role) (role : Role) :
    R.reg role < R.top :=
  (R.regs role).isLt

@[construction_api] lemma reg_lt_of_top_le {Role : Type} (R : RegLayout Role) (role : Role) {x : ℕ}
    (hx : R.top ≤ x) : R.reg role < x :=
  Nat.lt_of_lt_of_le (R.reg_lt_top role) hx

@[construction_api] lemma ne_reg_of_top_le {Role : Type} (R : RegLayout Role) (role : Role)
    {x : ℕ} (hx : R.top ≤ x) {y : ℕ} (hy : x ≤ y) : y ≠ R.reg role :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (R.reg_lt_of_top_le role hx) hy)

/-- A list containing every element and pairwise separated by `f` makes `f` injective; `decide`
checks the list for a concrete placement. -/
@[construction_api] lemma pairwise_ne_injective {α β : Type*} {f : α → β} {l : List α}
    (hall : ∀ x, x ∈ l) (hp : l.Pairwise (fun a b => f a ≠ f b)) : Function.Injective f := by
  have hsymm : Std.Symm (fun a b : α => f a ≠ f b) := ⟨fun _ _ h => h.symm⟩
  intro a b hab
  by_contra hne
  exact hp.forall (hall a) (hall b) hne hab

end RegLayout

/-! ## Necessary separation and index bounds

A layout gives every pairwise distinctness and below-`top` fact, but a proof body uses only a
short list of pairs and a set of used roles.  The thin core below takes exactly those: an
assignment `reg`, the pairs it separates and the roles it indexes.  This keeps one proof body
valid for placements where some registers coincide (a layout cannot express those), while the
layout side supplies the evidence wholesale. -/

/-- The assignment `reg` separates the two registers of every pair of `pairs`. -/
@[construction_api] def Separates {Role : Type} (reg : Role → ℕ) (pairs : List (Role × Role)) :
    Prop :=
  ∀ a b, (a, b) ∈ pairs → reg a ≠ reg b

/-- Every register of a used-role set is at most `B`. -/
@[construction_api] def RegsLe {Role : Type} (reg : Role → ℕ) (used : Set Role) (B : ℕ) : Prop :=
  ∀ r ∈ used, reg r ≤ B

/-- Separation restricts to a sublist of the pairs. -/
@[construction_api] lemma Separates.of_subset {Role : Type} {reg : Role → ℕ}
    {pairs pairs' : List (Role × Role)} (h : Separates reg pairs') (hsub : pairs ⊆ pairs') :
    Separates reg pairs :=
  fun a b hab => h a b (hsub hab)

/-- Separation of two pair lists gives separation of their append. -/
@[construction_api] lemma Separates.append {Role : Type} {reg : Role → ℕ}
    {pairs pairs' : List (Role × Role)} (h : Separates reg pairs) (h' : Separates reg pairs') :
    Separates reg (pairs ++ pairs') := by
  intro a b hab
  rcases List.mem_append.1 hab with hab | hab
  · exact h a b hab
  · exact h' a b hab

/-- Index bounds restrict to a subset of the roles. -/
@[construction_api] lemma RegsLe.mono {Role : Type} {reg : Role → ℕ} {used used' : Set Role}
    {B : ℕ} (h : used ⊆ used') (hidx : RegsLe reg used' B) : RegsLe reg used B :=
  fun r hr => hidx r (h hr)

namespace RegLayout

/-- A layout separates any pair list of distinct roles, wholesale from `reg_ne`. -/
@[construction_api] lemma separates {Role : Type} (R : RegLayout Role) (pairs : List (Role × Role))
    (hp : ∀ a b, (a, b) ∈ pairs → a ≠ b) : Separates R.reg pairs :=
  fun a b hab => R.reg_ne (hp a b hab)

/-- Every register of a used-role set is at most `B` when `top` is at most `B + 1`. -/
@[construction_api] lemma regsLe {Role : Type} (R : RegLayout Role) (used : Set Role) {B : ℕ}
    (h : R.top ≤ B + 1) : RegsLe R.reg used B :=
  fun r _ => Nat.le_of_lt_succ (R.reg_lt_of_top_le r h)

end RegLayout

end NPComplete.BoundedWhile

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

end NPComplete.BoundedWhile

module

public import NPComplete.BoundedWhile.Frame
meta import NPComplete.Meta.ApiLayer

/-!
Stores agreeing outside a write set provide a semantic frame contract that can be composed
without exposing the implementation of a program.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- Two stores that agree outside a set of addresses. -/
@[construction_api] def SameOff (S : ℕ → Prop) (σ τ : Store) : Prop :=
  ∀ r, ¬ S r → τ r = σ r

@[construction_api] lemma SameOff.refl (S : ℕ → Prop) (σ : Store) : SameOff S σ σ := fun _ _ => rfl

@[construction_api] lemma SameOff.trans {S : ℕ → Prop} {σ τ υ : Store}
    (h1 : SameOff S σ τ) (h2 : SameOff S τ υ) : SameOff S σ υ :=
  fun r hr => (h2 r hr).trans (h1 r hr)

@[construction_api] lemma SameOff.mono {S T : ℕ → Prop} {σ τ : Store}
    (h : SameOff S σ τ) (hST : ∀ r, S r → T r) : SameOff T σ τ :=
  fun r hr => h r fun hs => hr (hST r hs)

@[construction_api] lemma SameOff.symm {S : ℕ → Prop} {σ τ : Store}
    (h : SameOff S σ τ) : SameOff S τ σ := fun r hr => (h r hr).symm

@[construction_api] lemma SameOff.writeReg {S : ℕ → Prop} {σ : Store} {r : ℕ}
    (hr : S r) (v : ℕ) : SameOff S σ (writeReg σ r v) := by
  intro x hx
  exact writeReg_diff _ _ _ _ fun h => hx (h ▸ hr)

end NPComplete.RAMToTM

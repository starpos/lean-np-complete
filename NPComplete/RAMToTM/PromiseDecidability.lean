module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.PromisePolyDecidable
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.RAMToTM.Generic.Api.TransducerMachine

/-!
# Bridge from generic RAM→TM realizability to promise decidability

The RAM→TM compiler layer is generic and should not depend on Cook-Levin's promise predicate.
These connecting declarations therefore live between the generic realizability results and that
upper-layer decision API, preserving the one-way dependency while exposing their composition.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BitEncoding (Bits)
open NPComplete.CookLevin (PromisePolyDecidable)

/-- The target API: a realizable `BoundedWhileDecider` is a
    `PromisePolyDecidable` instance. Independent of how `TMRealizable` was proved. -/
@[construction_api] lemma promisePolyDecidable_of_tmRealizable {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (h : d.TMRealizable) :
    PromisePolyDecidable enc D L := by
  refine ⟨d.result, h, fun x => ?_⟩
  show decide ((d.p.eval (bitInputStore (enc x.1))) d.outReg = 1) = true ↔ L x.1
  rw [decide_eq_true_eq]
  exact d.correct x.1 x.2

/-- The target API, now unconditional: every `BoundedWhileDecider` gives a
    `PromisePolyDecidable` instance — the realizability-to-promise bridge only needed
    `TMRealizable`, which `TransducerMachine.lean` supplies for free. This completes the
    generic RAM-to-TM bridge for the decider API. -/
lemma promisePolyDecidable_of_boundedWhileDecider {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : PromisePolyDecidable enc D L :=
  promisePolyDecidable_of_tmRealizable d (tmRealizable_of_boundedWhileDecider d)

end NPComplete.RAMToTM

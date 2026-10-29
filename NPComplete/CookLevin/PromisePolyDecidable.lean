module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BitEncoding
public import Mathlib.Computability.TuringMachine.Computable

/-!
# TM2 poly-time decidability under a promise

Mathlib's Turing-machine time layer (`Turing.TM2ComputableInPolyTime`) states function
computability. This module defines promise-restricted language decidability as a correctness
wrapper around that structure. Its guarantees are stated on an explicit promise domain, without
relying on general TM2 polynomial-time composition or reduction-style pullbacks.

The promise domain `D` is an explicit parameter, so each application specifies the subset of
inputs on which its decision guarantee is required.

The module sits at the stable layer and imports only the bit-encoding basics, so the TM0 class
definitions stay independent of it. The bridge into `InP` for the trivial promise
`D = fun _ => True` is `promisePolyDecidable_to_InP` (`Main.lean`).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BitEncoding (Bits encodeBool)
open Turing

/-- **Stable API.** `L` is poly-time decidable under encoding `enc`, restricted to the promise
    domain `D`: some `Bool`-valued function on `{x // D x}` is `TM2ComputableInPolyTime` and
    agrees with `L` on that domain. This is the TM2-side decision notion; for the trivial
    promise `D = fun _ => True`, `promisePolyDecidable_to_InP` converts it to the TM0 class
    `InP`. -/
@[stable_api] def PromisePolyDecidable {α : Type} (enc : α → Bits) (D L : α → Prop) : Prop :=
  ∃ f : {x // D x} → Bool,
    Nonempty (TM2ComputableInPolyTime (enc ∘ Subtype.val) encodeBool f) ∧
    ∀ x : {x // D x}, f x = true ↔ L x.val

/-- `PromisePolyDecidable` is trivially satisfiable when the promise domain is empty (`D`
    everywhere `False`): there is no input to decide, so any machine discharges the vacuous
    `outputsFun` obligation. -/
@[stable_api] lemma promisePolyDecidable_of_false {α : Type} (enc : α → Bits) (L : α → Prop) :
    PromisePolyDecidable enc (fun _ => False) L := by
  refine ⟨fun x => False.elim x.2, ⟨?_⟩, fun x => absurd x.2 id⟩
  exact { (Turing.idComputableInPolyTime encodeBool).toTM2ComputableAux with
          time := 1
          outputsFun := fun a => absurd a.2 id }

/-- `PromisePolyDecidable` depends only on `L`'s values on the promise domain `D`: predicates
    that agree there have the same promise-decidability status. -/
lemma PromisePolyDecidable.congr {α : Type} {enc : α → Bits} {D L₁ L₂ : α → Prop}
    (h : ∀ x, D x → (L₁ x ↔ L₂ x)) :
    PromisePolyDecidable enc D L₁ ↔ PromisePolyDecidable enc D L₂ := by
  constructor
  · rintro ⟨f, hf, hcorrect⟩
    exact ⟨f, hf, fun x => (hcorrect x).trans (h x.1 x.2)⟩
  · rintro ⟨f, hf, hcorrect⟩
    exact ⟨f, hf, fun x => (hcorrect x).trans (h x.1 x.2).symm⟩

end NPComplete.CookLevin

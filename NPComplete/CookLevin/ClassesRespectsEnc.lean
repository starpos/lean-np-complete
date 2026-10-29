module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Classes
public import NPComplete.CookLevin.Generate.Steps

/-!
`InP` and `InNP` do not require `enc` to be injective, because a machine only
reads `enc x` from the tape. This module proves that consequence. It sits above
`Generate/Steps.lean`, which supplies the uniqueness of a halting run and which
itself depends on `Classes.lean`, so the lemmas cannot live in `Classes.lean`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Computability (encodeBool)

/-- A language in `P` under `enc` cannot distinguish inputs with equal encodings,
    since the decider reads only the tape contents `enc x`; injectivity of `enc`
    is therefore not needed. -/
@[stable_api] lemma InP.respects_enc {α : Type} {enc : α → List Bool} {L : α → Prop}
    (h : InP enc L) {x y : α} (hxy : enc x = enc y) : L x ↔ L y := by
  obtain ⟨f, ⟨hf⟩, hdec⟩ := h
  have hfxy : f x = f y := by
    have htape := machineOutputsInTime_unique_tape (hf.outputsFun x)
      (hxy ▸ hf.outputsFun y)
    exact tape_mk₁_bool_injective (by simpa [encodeBool] using htape)
  rw [← hdec, ← hdec, hfxy]

/-- For a language in `InNP` under `enc`, inputs with equal encodings have the same membership,
    since the verifier reads only `pairBits (enc x) w`; injectivity of `enc`
    is therefore not needed. -/
@[stable_api] lemma InNP.respects_enc {α : Type} {enc : α → List Bool} {L : α → Prop}
    (h : InNP enc L) {x y : α} (hxy : enc x = enc y) : L x ↔ L y := by
  obtain ⟨p, V, hL, ⟨hV⟩⟩ := h
  have hVxy : ∀ w, V x w = V y w := fun w => by
    have htape := machineOutputsInTime_unique_tape (hV.outputsFun (x, w))
      (by simpa [hxy] using hV.outputsFun (y, w))
    exact tape_mk₁_bool_injective (by simpa [encodeBool] using htape)
  simp only [hL, hxy, hVxy]

end NPComplete.CookLevin

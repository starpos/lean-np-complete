module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiTm0

/-!
# Encoded-input application

The bit-level ABI result is independent of the input type, but a reduction must run on an encoded
source value. This module specializes that result to an arbitrary encoding so the computation
statement has the input signature required by the complexity interface.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

lemma generator_abi_computable_of_enc {α : Type}
    (enc : α → List Bool)
    (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout0 : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    Nonempty
      (TM0ComputableInPolyTime enc encodeCNF
        (fun x => descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval (enc x).length)
            (d.numLetters + 1))
          d (prefixWord d (enc x)) (p.eval (enc x).length) allowedIdx outIdx
          ((cookWindowPoly p time).eval (enc x).length)
          ((timePoly p time).eval (enc x).length))) := by
  let hcopy : TM0ComputableInPolyTime enc (id : Bits → Bits) enc :=
    TM0ComputableInPolyTime.congr_map
      (fun x => by simp)
      (idComputableInPolyTime enc)
  obtain ⟨hgen⟩ := generator_abi_computable p time d allowedIdx outIdx
    hwrite hblank hfalse htrue hallowed hout0
  exact ⟨TM0ComputableInPolyTime.congr_map
    (fun x => by simp [Function.comp]) (hcopy.comp hgen)⟩

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiTm2
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseEmitShape
public import NPComplete.CookLevin.Machines.RawDecodePackaging

/-! The generator's raw simulator output can be packaged as a TM0 computation
because its CNF encoding has a stable terminator and a nontrivial length. -/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

lemma generator_abi_computable_of_raw_decode
    (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout0 : ∀ a ∈ outIdx, a < d.numLetters + 1)
    (hraw : ∀ bits : Bits,
      dropTrailingFalse (decodePackedOutputList
        (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout0).tm
        (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout0).outputAlphabet
        (simFn (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout0)
          (encodePackedInput
            (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
              hallowed hout0).tm
            (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
              hallowed hout0).inputAlphabet bits))) =
        encodeCNF (descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
            (d.numLetters + 1))
          d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
          ((cookWindowPoly p time).eval bits.length)
          ((timePoly p time).eval bits.length))) :
    Nonempty
      (TM0ComputableInPolyTime (id : Bits → Bits) encodeCNF
        (fun bits => descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
            (d.numLetters + 1))
          d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
          ((cookWindowPoly p time).eval bits.length)
          ((timePoly p time).eval bits.length))) := by
  have h0 : TM0ComputableInPolyTime (id : Bits → Bits) (fun l : List Bool => l)
      (fun bits => encodeCNF (descTableauCNF
        (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
          (d.numLetters + 1))
        d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))) := by
    apply TM2ComputableInPolyTime.toTM0WithRawDecoderAny
      (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
        hallowed hout0)
      (decodePackedOutputListTrailingFalseComputableInPolyTime
        (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout0).tm
        (generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout0).outputAlphabet)
      (fun bits => encodeCNF (descTableauCNF
        (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
          (d.numLetters + 1))
        d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length)))
    exact hraw
  exact ⟨TM0ComputableInPolyTime.congr_map (β := List Bool)
    (β' := CNF) (eb := fun l : List Bool => l) (eb' := encodeCNF)
    (f := fun bits => encodeCNF (descTableauCNF
      (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
        (d.numLetters + 1))
      d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
      ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length)))
    (f' := fun bits => descTableauCNF
      (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
        (d.numLetters + 1))
      d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
      ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length))
    (fun _ => rfl) h0⟩

lemma generator_abi_computable
    (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout0 : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    Nonempty
      (TM0ComputableInPolyTime (id : Bits → Bits) encodeCNF
        (fun bits => descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
            (d.numLetters + 1))
          d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
          ((cookWindowPoly p time).eval bits.length)
          ((timePoly p time).eval bits.length))) := by
  apply generator_abi_computable_of_raw_decode p time d allowedIdx outIdx hwrite hblank
    hfalse htrue hallowed hout0
  apply computable_of_raw_decode_generic
    (ea := id)
    (eb := fun l : List Bool => l)
    (f := fun bits => encodeCNF (descTableauCNF
      (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
        (d.numLetters + 1))
      d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
      ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length)))
    (h := generatorAbi_tm2_computable p time d allowedIdx outIdx hwrite hblank hfalse htrue
      hallowed hout0)
  · intro bits
    exact encodeCNF_ends_true _
  · intro bits
    exact encodeCNF_length_two_of_ne_nil
      (descTableauCNF_clauses_ne_nil
        (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
          (d.numLetters + 1))
        d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))

end NPComplete.CookLevin

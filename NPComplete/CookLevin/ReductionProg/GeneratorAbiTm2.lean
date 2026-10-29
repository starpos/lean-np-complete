module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiDecider

/-!
# TM2 realization

The decider's certified output is the input needed to obtain a polynomial-time TM2 realization.
This module isolates that model conversion from the ABI and cost proofs, so the encoded-input layer
can use one machine-level result.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-- The ABI decider exposes the generator's bounded output as a polynomial-time TM2 computation. -/
noncomputable def generatorAbi_tm2_computable
    (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout0 : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    Turing.TM2ComputableInPolyTime (id : Bits → Bits)
      (fun l : List Bool => l)
      (fun bits => (encodeCNF (descTableauCNF
        (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval bits.length)
          (d.numLetters + 1))
        d (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))).reverse) := by
  let dec := generatorProgAbiDecider p time d allowedIdx outIdx hwrite hblank hfalse htrue
    hallowed hout0
  refine tm2ComputableInPolyTime_of_abiBitProducer_forward (d := dec) (fun _ => trivial)
    emitOutputStart
    (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length) ?_ ?_ ?_
  · intro bits
    exact generatorProgAbi_reductionOutput p time d allowedIdx outIdx bits hwrite hblank
      (prefixWord_valid_of_true_false d bits hfalse htrue) hallowed hout0
  · intro bits log hlog
    exact generatorProgAbi_hBits p time d allowedIdx outIdx bits hwrite hblank
      (prefixWord_valid_of_true_false d bits hfalse htrue) hallowed hout0 log hlog
  · intro bits
    exact generatorProgAbi_houtLen p time d allowedIdx outIdx bits hwrite hblank
      (prefixWord_valid_of_true_false d bits hfalse htrue) hallowed hout0

end NPComplete.CookLevin

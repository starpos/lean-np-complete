module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiCost

/-!
# Polynomial-time decider

An ABI computation becomes usable by the machine bridge only after its bounded output and input
cost are packaged as a decider. This module constructs that decider from the established cost
bound, keeping the machine-model translation out of generator analysis.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## The `BoundedWhileDecider` instance -/

noncomputable def generatorProgAbiInputCostC (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) : ℕ :=
  Classical.choose (generatorProgAbi_cost_le_input_power p time d allowedIdx outIdx
    hwrite hblank hfalse htrue hallowed hout)

lemma generatorProgAbiInputCostC_spec (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
      generatorProgAbiInputCostC p time d allowedIdx outIdx hwrite hblank hfalse htrue
        hallowed hout * (bits.length + 1) ^
        generatorProgAbiInputCostC p time d allowedIdx outIdx hwrite hblank hfalse htrue
          hallowed hout := by
  exact Classical.choose_spec
    (generatorProgAbi_cost_le_input_power p time d allowedIdx outIdx
      hwrite hblank hfalse htrue hallowed hout) bits

noncomputable def generatorProgAbiDecider (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    BoundedWhileDecider (id : Bits → Bits) (fun _ : Bits => True)
      (fun bits => (generatorProgAbi p time d allowedIdx outIdx).eval
        (bitInputStore bits) 0 = 1) where
  p := generatorProgAbi p time d allowedIdx outIdx
  outReg := 0
  c := generatorProgAbiInputCostC p time d allowedIdx outIdx
    hwrite hblank hfalse htrue hallowed hout
  correct := by
    intro bits _
    rfl
  cost_le := by
    intro bits _
    exact generatorProgAbiInputCostC_spec p time d allowedIdx outIdx bits
      hwrite hblank hfalse htrue hallowed hout
  bit_c := generatorEnvBExponent p time d allowedIdx outIdx + 1
  compiled_operands_le := by
    intro bits _
    exact generatorProgAbi_compiled_operands_le_for p time d allowedIdx outIdx bits
      hwrite hblank hfalse htrue hallowed hout

end NPComplete.CookLevin

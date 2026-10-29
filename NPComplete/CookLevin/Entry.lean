module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Classes
public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.CookLevin.Machines.RawDecodeGeneric
public import NPComplete.RAMToTM.Generic.Api.TransducerMachine
public import NPComplete.RAMToTM.Generic.Api.AbiBitProducerMachine

/-!
# Upper entry points from `BoundedWhileDecider` to the TM0 classes

A user who writes a `BoundedWhile` program and proves its cost and operand bounds should not
have to repeat the four-step RAM-to-TM wiring (realize on a `FinTM2`, drop the trivial promise,
reconcile the output alphabet, descend to TM0). This module states that wiring once, at the
level of the TM0 classes `InP`, `InNP`, `PolyTimeReduction`:

* Boolean entries `InP.of_boundedWhileDecider` and `InNP.of_bounded_while_verifier`;
* a producer entry `PolyTimeReduction.of_forwardBitProducer` whose hypotheses are plain facts
  about the final store of the program (output base in cell `0`, output length in cell `1`,
  output bits as `0`/`1` cells), so that none of the ABI types (`WriteLog`, `OutputSlice`,
  `ReductionOutput`) appears in a statement.

The module imports the RAM-to-TM bridge, so it sits above `Classes.lean` and is deliberately
kept out of it; it imports no SAT-specific module.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store)
open NPComplete.BitEncoding (Bits)

/-- **Construction API.** Package a program with its cost and operand bounds as a
    `BoundedWhileDecider` whose promise is trivial and whose language is simply "the answer
    register is `1`". Producers have no meaningful decision language, so this fills it in
    trivially and leaves only the two quantitative obligations. -/
@[construction_api] def BoundedWhileDecider.ofBounds {α : Type} (ea : α → Bits) (p : Program) (outReg c bit_c : ℕ)
    (cost_le : ∀ x, p.cost (bitInputStore (ea x)) ≤ c * ((ea x).length + 1) ^ c)
    (compiled_operands_le : ∀ x, ∃ W, W ≤ bit_c * ((ea x).length + 1) ^ bit_c ∧
      CompiledOperandBound p (ea x) W) :
    BoundedWhileDecider ea (fun _ => True)
      (fun x => p.eval (bitInputStore (ea x)) outReg = 1) where
  p := p
  outReg := outReg
  c := c
  correct := fun _ _ => Iff.rfl
  cost_le := fun x _ => cost_le x
  bit_c := bit_c
  compiled_operands_le := fun x _ => compiled_operands_le x

namespace Generic

/-- **Internal (ABI bridge).** Output bits stored as `0`/`1` cells of a store determine the physical
    bit list read off any write log that agrees with that store. -/
lemma physicalBits_eq_of_store_bits (log : WriteLog) (σ : Store) (base : ℕ)
    (bits : Bits) (hlog : ∀ a, lookupD log a 0 = σ a)
    (hbits : ∀ i, (h : i < bits.length) → σ (base + i) = if bits[i] then 1 else 0) :
    OutputSlice.physicalBits log ⟨base, bits.length⟩ = bits := by
  rw [physicalBits_eq_range]
  apply List.ext_getElem
  · simp
  · intro i hiRange hiBits
    have hi : i < bits.length := by simpa using hiBits
    rw [List.getElem_map, List.getElem_range, hlog, hbits i hi]
    cases bits[i] <;> simp

end Generic

end NPComplete.RAMToTM

namespace NPComplete.CookLevin

open Turing
open NPComplete.RAMToTM
open NPComplete.BitEncoding (Bits)
open NPComplete.BoundedWhile (Program Store)

/-! ## Boolean entries -/

/-- **Construction API.** A `BoundedWhileDecider` (trivial promise) whose answer register is
    correct for `L` yields a TM0 poly-time computer of any Boolean function `f` agreeing with
    `L`. The common packaging step behind `InP.of_boundedWhileDecider` and
    `InNP.of_bounded_while_verifier`. -/
@[construction_api] lemma TM0ComputableInPolyTime.nonempty_of_boundedWhileDecider
    {α : Type} {ea : α → Bits} {L : α → Prop} {f : α → Bool}
    (d : BoundedWhileDecider ea (fun _ => True) L)
    (hf : ∀ x, f x = true ↔ L x) :
    Nonempty (TM0ComputableInPolyTime ea Computability.encodeBool f) := by
  obtain ⟨h⟩ := tmRealizable_of_boundedWhileDecider d
  have h2 : TM2ComputableInPolyTime ea Computability.encodeBool
      (fun x => d.result ⟨x, trivial⟩) := TM2ComputableInPolyTime.subtype_true h
  have hfun : (fun x => d.result ⟨x, trivial⟩) = f := by
    funext x
    show decide ((d.p.eval (bitInputStore (ea x))) d.outReg = 1) = _
    have hc := d.correct x trivial
    have := hf x
    cases hb : f x <;> simp_all
  rw [← hfun]
  exact ⟨TM2ComputableInPolyTime.toTM0 h2⟩

/-- **Construction API (Boolean entry for `InP`).** A `BoundedWhileDecider` with trivial
    promise puts its language in `InP`. -/
@[construction_api] lemma InP.of_boundedWhileDecider {α : Type} {ea : α → Bits} {L : α → Prop}
    (d : BoundedWhileDecider ea (fun _ => True) L) : InP ea L :=
  ⟨fun x => d.result ⟨x, trivial⟩,
    TM0ComputableInPolyTime.nonempty_of_boundedWhileDecider d (fun _ => by
      show decide _ = true ↔ _
      rw [decide_eq_true_eq]
      exact d.correct _ trivial),
    fun x => by
      show decide _ = true ↔ _
      rw [decide_eq_true_eq]
      exact d.correct _ trivial⟩

/-- **Construction API (Boolean entry for `InNP`).** `L` is in NP if membership is witnessed by
    certificates of polynomially bounded length checked by a `BoundedWhileDecider` on the
    paired input `pairBits (enc x) w`. The verifier relation is given as a proposition `R`;
    the verifier function is `d.result`. -/
@[construction_api] lemma InNP.of_bounded_while_verifier {α : Type} (enc : α → Bits) (L : α → Prop)
    (p : Polynomial ℕ) (R : α → List Bool → Prop)
    (hspec : ∀ x, L x ↔ ∃ w, w.length ≤ p.eval (enc x).length ∧ R x w)
    (d : BoundedWhileDecider (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      (fun _ => True) (fun xw => R xw.1 xw.2)) :
    InNP enc L := by
  have hV : ∀ x w, d.result ⟨(x, w), trivial⟩ = true ↔ R x w := fun x w => by
    show decide _ = true ↔ _
    rw [decide_eq_true_eq]
    exact d.correct (x, w) trivial
  refine ⟨p, fun x w => d.result ⟨(x, w), trivial⟩, fun x => ?_,
    TM0ComputableInPolyTime.nonempty_of_boundedWhileDecider d
      (f := fun xw => d.result ⟨(xw.1, xw.2), trivial⟩) (fun xw => hV xw.1 xw.2)⟩
  rw [hspec x]
  exact exists_congr fun w => and_congr_right fun _ => (hV x w).symm

/-! ## Producer entries -/

/-- **Construction API (producer entry, TM0 computer).** If the final store of a
    `BoundedWhileDecider`'s program holds the output `eb (f x)` as `0`/`1` cells starting at
    `outputBase` (cell `0` is `outputBase`, cell `1` is the length, cell `outputBase + i` is the
    `i`-th bit), the output length is polynomially bounded, the output ends with `true` and has
    at least two bits, then `f` is TM0 poly-time computable under `ea`/`eb`. The side
    conditions `hends` and `hlen2` are what the raw tape decode needs: they hold for the
    length-prefixed encodings of this development. -/
@[construction_api] noncomputable def TM0ComputableInPolyTime.of_forwardBitProducer
    {α β : Type} {ea : α → Bits} {eb : β → Bits} {Lp : α → Prop} {f : α → β}
    (d : BoundedWhileDecider ea (fun _ => True) Lp) (outputBase : ℕ) (outP : Polynomial ℕ)
    (hbase : ∀ x, d.p.eval (bitInputStore (ea x)) 0 = outputBase)
    (hlen : ∀ x, d.p.eval (bitInputStore (ea x)) 1 = (eb (f x)).length)
    (hbits : ∀ x i, (h : i < (eb (f x)).length) →
      d.p.eval (bitInputStore (ea x)) (outputBase + i) = if (eb (f x))[i] then 1 else 0)
    (houtLen : ∀ x, (eb (f x)).length ≤ outP.eval (ea x).length)
    (hends : ∀ x, ∃ xs, eb (f x) = xs ++ [true])
    (hlen2 : ∀ x, 2 ≤ (eb (f x)).length) :
    TM0ComputableInPolyTime ea eb f := by
  let h := tm2ComputableInPolyTime_of_abiBitProducer_forward (d := d) (fun _ => trivial)
    outputBase outP
    (fun x => ⟨hbase x, hlen x, fun i hi => by
      rw [hbits x i hi]; split <;> simp⟩)
    (fun x log hlog => Generic.physicalBits_eq_of_store_bits log _ outputBase _ (congrFun hlog)
      (hbits x))
    houtLen
  have h0 : TM0ComputableInPolyTime ea (fun l : List Bool => l) (fun x => eb (f x)) :=
    TM2ComputableInPolyTime.toTM0WithRawDecoderAny h
      (decodePackedOutputListTrailingFalseComputableInPolyTime h.tm h.outputAlphabet)
      (fun x => eb (f x))
      (computable_of_raw_decode_generic ea eb f h hends hlen2)
  exact TM0ComputableInPolyTime.congr_map (β := List Bool) (β' := β) (eb := fun l => l)
    (eb' := eb) (f := fun x => eb (f x)) (f' := f) (fun _ => rfl) h0

/-- **Construction API (producer entry, reduction).** `TM0ComputableInPolyTime.of_forwardBitProducer`
    packaged with a correctness proof as a `PolyTimeReduction`. -/
@[construction_api] noncomputable def PolyTimeReduction.of_forwardBitProducer
    {α β : Type} {ea : α → Bits} {eb : β → Bits} {Lp : α → Prop} {f : α → β}
    {Lα : α → Prop} {Lβ : β → Prop}
    (d : BoundedWhileDecider ea (fun _ => True) Lp) (outputBase : ℕ) (outP : Polynomial ℕ)
    (hbase : ∀ x, d.p.eval (bitInputStore (ea x)) 0 = outputBase)
    (hlen : ∀ x, d.p.eval (bitInputStore (ea x)) 1 = (eb (f x)).length)
    (hbits : ∀ x i, (h : i < (eb (f x)).length) →
      d.p.eval (bitInputStore (ea x)) (outputBase + i) = if (eb (f x))[i] then 1 else 0)
    (houtLen : ∀ x, (eb (f x)).length ≤ outP.eval (ea x).length)
    (hends : ∀ x, ∃ xs, eb (f x) = xs ++ [true])
    (hlen2 : ∀ x, 2 ≤ (eb (f x)).length)
    (hcorrect : ∀ x, Lα x ↔ Lβ (f x)) :
    PolyTimeReduction ea eb Lα Lβ where
  map := f
  computable := ⟨TM0ComputableInPolyTime.of_forwardBitProducer d outputBase outP hbase hlen
    hbits houtLen hends hlen2⟩
  correct := hcorrect

end NPComplete.CookLevin

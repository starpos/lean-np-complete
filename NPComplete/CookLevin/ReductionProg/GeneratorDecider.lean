module

public import NPComplete.CookLevin.ReductionProg.GeneratorCost

/-!
# `generatorProgFromBits` as a `BoundedWhileDecider`

`generatorProgFromBits` is a fixed `Program` that, run against the canonical
`bitInputStore bits` loader, materializes the clause table for `bits`'s
tableau instance (`generatorProgFromBits_meets_emitter_precondition`,
`GeneratorLoad.lean`) with no leftover hypothesis, is `ProgramBoundedIn` at
`envB.eval bits.length` unconditionally (`programBoundedIn_generatorProgFromBits`,
`GeneratorBoundedTop.lean`), and has operation-count cost polynomial in
`bits.length` (`generatorProgFromBits_cost_le_input_power`, `GeneratorCost.lean`).
This file assembles those three facts into a `BoundedWhileDecider` instance.

`generatorProgFromBits` is a *producer*, not a decider: it has no single-bit
answer, only a table it writes into the store.  Mirroring
`satToThreeCNFProducerDecider` (`SATToThreeCNF.lean`), the `L` predicate is
therefore phrased against the producer's own store (`outReg`'s cell reads back
`1`), which makes `correct` `rfl` by construction rather than a real
correctness theorem — the mathematical content lives in
`generatorProgFromBits_meets_emitter_precondition`, not in this `Prop`.

## `bit_c` is a `bitLen` bound, not a value bound

`compiled_operands_le` asks for a bound on `bitLen (envB.eval N)`, not on
`envB.eval N` itself: `CompiledOperandBound p bits (bitLen B)` is the shape
`compiledOperandBound_generatorProgFromBits_of_programBoundedIn` produces. Since
`envB` is a fixed polynomial in `N`, `bitLen_le_succ` gives
`bitLen (envB.eval N) ≤ envB.eval N + 1`, again a polynomial in `N` — the
direction that is always available. The reverse (bounding a *value* by a
polynomial in its own `bitLen`) is false in general (a store cell can be `2 ^ k`
against a `bitLen` of `k + 1`) and is not what is needed here.

`bit_c` and `c` are separate naturals so the operand bound avoids a needless
`costBoundMajorPoly`-shaped term. That extra polynomial expression makes kernel
reduction heavier. Here `c` is `generatorProgFromBits_cost_le_input_power`'s
existential witness (built from `generatorProgFromBitsCostExponent` and
`generatorEnvBExponent`), and `bit_c` is `generatorEnvBExponent + 1`; the two
are computed independently and never multiplied together.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

/-! ## `cost_le`'s witness, named -/

/-- `generatorProgFromBits_cost_le_input_power`'s existential exponent/coefficient,
    named so `BoundedWhileDecider.c` can cite it directly. -/
noncomputable def generatorProgFromBitsInputCostC (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : ℕ :=
  Classical.choose (generatorProgFromBits_cost_le_input_power p time d allowedIdx outIdx)

/-- The defining property of `generatorProgFromBitsInputCostC`, extracted once. -/
lemma generatorProgFromBitsInputCostC_spec (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
      generatorProgFromBitsInputCostC p time d allowedIdx outIdx * (bits.length + 1) ^
        generatorProgFromBitsInputCostC p time d allowedIdx outIdx :=
  Classical.choose_spec
    (generatorProgFromBits_cost_le_input_power p time d allowedIdx outIdx) bits

/-! ## `bit_c`'s witness: `bitLen (envB.eval N)` is polynomial in `N`

`generatorEnvB_eval_le_power` (`GeneratorCost.lean`) already bounds
`envB.eval N` itself by `b * (N+1)^b` for `b := generatorEnvBExponent`;
`bitLen_le_succ` turns that value bound into a `bitLen` bound at exponent
`b + 1`, one power higher to absorb the `+ 1` from `bitLen_le_succ`. -/

/-- `bitLen (envB.eval N)` (via the prefix bound `envB_eval_le_prefix_bound`) is
    dominated by `(b + 1) * (N + 1) ^ (b + 1)`, where `b` is the exponent
    `generatorEnvB_eval_le_power` already supplies for the value itself. -/
lemma bitLen_generatorEnvB_le_power (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    bitLen (Polynomial.eval bits.length
        (envB p time d (prefixWord d bits) allowedIdx outIdx)) ≤
      (generatorEnvBExponent p time d allowedIdx outIdx + 1) *
        (bits.length + 1) ^ (generatorEnvBExponent p time d allowedIdx outIdx + 1) := by
  let N := bits.length
  let b := generatorEnvBExponent p time d allowedIdx outIdx
  let B := (envB p time d (prefixWord d bits) allowedIdx outIdx).eval N
  let Q := (envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N
  have hBQ : B ≤ Q := envB_eval_le_prefix_bound p time d allowedIdx outIdx bits N
  have hQpoly : Q ≤ b * (N + 1) ^ b :=
    generatorEnvB_eval_le_power p time d allowedIdx outIdx N
  have hbl : bitLen B ≤ B + 1 := bitLen_le_succ B
  have hpow1 : 1 ≤ (N + 1) ^ b := Nat.one_le_pow b _ (by omega)
  have hstep : B + 1 ≤ (b + 1) * (N + 1) ^ b := by
    calc B + 1 ≤ Q + 1 := by omega
      _ ≤ b * (N + 1) ^ b + (N + 1) ^ b := by omega
      _ = (b + 1) * (N + 1) ^ b := by ring
  have hpow2 : (N + 1) ^ b ≤ (N + 1) ^ (b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hfinal : (b + 1) * (N + 1) ^ b ≤ (b + 1) * (N + 1) ^ (b + 1) :=
    Nat.mul_le_mul_left _ hpow2
  exact hbl.trans (hstep.trans hfinal)

/-- The `compiled_operands_le` obligation for `generatorProgFromBits`, at the
    exponent `generatorEnvBExponent + 1`: instantiate `envB.eval N` itself as
    the bound `B`, discharge `1 ≤ B` and `StoreValuesLe B (bitInputStore
    bits)` from the same `envK`/`envB`/`setupM` inequalities `GeneratorCost.lean`
    already uses, then convert the resulting `CompiledOperandBound _ _ (bitLen
    B)` witness to the polynomial bound via `bitLen_generatorEnvB_le_power`. -/
lemma generatorProgFromBits_compiled_operands_le_for (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    ∃ W, W ≤ (generatorEnvBExponent p time d allowedIdx outIdx + 1) *
        (bits.length + 1) ^ (generatorEnvBExponent p time d allowedIdx outIdx + 1) ∧
      CompiledOperandBound (generatorProgFromBits p time d allowedIdx outIdx) bits W := by
  let N := bits.length
  let B := (envB p time d (prefixWord d bits) allowedIdx outIdx).eval N
  have hB1 : 1 ≤ B := by
    have hK := envK_ge_one p time d (prefixWord d bits) allowedIdx outIdx N
    have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx N
    omega
  have hN : bits.length ≤ B := by
    have hsetup := setupM_gt p time d allowedIdx N
    have hK := envK_ge_setupM p time d (prefixWord d bits) allowedIdx outIdx N
    have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx N
    omega
  have hσ : StoreValuesLe B (bitInputStore bits) := bitInputStore_storeValuesLe bits B hB1 hN
  refine ⟨bitLen B, ?_, ?_⟩
  · exact bitLen_generatorEnvB_le_power p time d allowedIdx outIdx bits
  · exact compiledOperandBound_generatorProgFromBits_of_programBoundedIn p time d allowedIdx outIdx bits
      B hB1 hσ (programBoundedIn_generatorProgFromBits p time d allowedIdx outIdx bits)

/-! ## The `BoundedWhileDecider` instance

`enc := id`, `D := fun _ => True`: `generatorProgFromBits` runs on raw
`bitInputStore bits` with no promise beyond what `bitInputStore` itself
provides, matching `satToThreeCNFProducerDecider`'s `(fun _ => True)`. `L` is
the producer's own store predicate at `outReg := 0` (register `0` holds
`bits.length` after the loader stage, then gets overwritten by `setupME`, so
reading it back for `= 1` is a bookkeeping predicate, not a semantic claim);
`correct` is `rfl` for the same reason `satToThreeCNFProducerDecider.correct`
is. -/

/-- `generatorProgFromBits` packaged as a `BoundedWhileDecider`, mirroring
    `satToThreeCNFProducerDecider`. Non-vacuous: instantiated below at
    `loadConstTestDescriptor`. -/
noncomputable def generatorAbiDecider (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    BoundedWhileDecider (id : Bits → Bits) (fun _ : Bits => True)
      (fun bits => (generatorProgFromBits p time d allowedIdx outIdx).eval
        (bitInputStore bits) 0 = 1) where
  p := generatorProgFromBits p time d allowedIdx outIdx
  outReg := 0
  c := generatorProgFromBitsInputCostC p time d allowedIdx outIdx
  correct := by
    intro bits _
    rfl
  cost_le := by
    intro bits _
    exact generatorProgFromBitsInputCostC_spec p time d allowedIdx outIdx bits
  bit_c := generatorEnvBExponent p time d allowedIdx outIdx + 1
  compiled_operands_le := by
    intro bits _
    exact generatorProgFromBits_compiled_operands_le_for p time d allowedIdx outIdx bits

/-! ## Non-vacuity

Instantiating `generatorAbiDecider` at `loadConstTestDescriptor` (whose table
is non-empty, `GeneratorLoadConst.lean`) forces every field's proof obligation
to actually discharge, not just typecheck against an unconstrained descriptor. -/

/-- Non-vacuity: `generatorAbiDecider` builds at a concrete non-empty-table
    descriptor. Building this `example` at all is the content — a
    `BoundedWhileDecider` is a structure, so producing one instance already
    proves every field. -/
noncomputable example : BoundedWhileDecider (id : Bits → Bits) (fun _ : Bits => True)
    (fun bits => (generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
      (bitInputStore bits) 0 = 1) :=
  generatorAbiDecider 0 0 loadConstTestDescriptor [] [5, 7, 9]

end NPComplete.CookLevin

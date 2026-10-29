module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiCore
public import NPComplete.CookLevin.UniformPackaging

/-!
# ABI generator costs

Polynomial-time classification needs quantitative bounds for the completed ABI generator and its
compiled operands. This module derives those estimates from the core invariants without mixing cost
arithmetic into program correctness.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

/-! ## Cost bounds for the ABI program -/

lemma loopBounded_generatorProgAbi (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    LoopBounded (generatorProgAbi p time d allowedIdx outIdx)
      (Polynomial.eval bits.length
        (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (bitInputStore bits) := by
  let N := bits.length
  let pref := prefixWord d bits
  let B := (envB p time d pref allowedIdx outIdx).eval N
  have hB1 : 1 ≤ B := by
    have hK := envK_ge_one p time d pref allowedIdx outIdx N
    have hKB := envB_ge_envK p time d pref allowedIdx outIdx N
    omega
  have hN : bits.length ≤ B := by
    have hsetup := setupM_gt p time d allowedIdx N
    have hK := envK_ge_setupM p time d pref allowedIdx outIdx N
    have hKB := envB_ge_envK p time d pref allowedIdx outIdx N
    omega
  have hσ : StoreBounded B (bitInputStore bits) := by
    exact bitInputStore_storeValuesLe bits B hB1 hN
  have hpb := programBoundedIn_generatorProgAbi_valid p time d allowedIdx outIdx bits
    hwrite hblank hfalse htrue hallowed hout
  have hnt := scanFree_to_noCompileTimeTables _
    (scanFree_generatorProgAbi p time d allowedIdx outIdx)
  exact programBoundedIn_to_g6_loopBounded _ B B hB1 _ hσ hpb hnt le_rfl

lemma generatorProgAbi_cost_le_CostEnvelope (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
      CostEnvelope (generatorProgAbi p time d allowedIdx outIdx)
        (Polynomial.eval bits.length
          (envB p time d (prefixWord d bits) allowedIdx outIdx)) := by
  exact g6_cost_le_envelope _ _ _
    (loopBounded_generatorProgAbi p time d allowedIdx outIdx bits
      hwrite hblank hfalse htrue hallowed hout)

noncomputable def generatorProgAbiCostExponent (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : ℕ :=
  let q := uniformCostEnvelopePoly (generatorProgAbi p time d allowedIdx outIdx)
  (q.support.card + 1) * (q.support.sup (fun n => q.coeff n) + 1) *
    (q.support.sup id + 1)

lemma generatorProgAbi_cost_le_input_power (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    ∃ c, ∀ bits : Bits,
      (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        c * (bits.length + 1) ^ c := by
  let a := generatorProgAbiCostExponent p time d allowedIdx outIdx
  let b := generatorEnvBExponent p time d allowedIdx outIdx
  let c := a * (b + 1) ^ a + b * a + 1
  refine ⟨c, ?_⟩
  intro bits
  let N := bits.length
  let B := (envB p time d (prefixWord d bits) allowedIdx outIdx).eval N
  let Q := (envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N
  have hBQ : B ≤ Q := by
    dsimp [B, Q]
    exact envB_eval_le_prefix_bound p time d allowedIdx outIdx bits N
  have hcostQ :
      (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        CostEnvelope (generatorProgAbi p time d allowedIdx outIdx) Q := by
    calc
      (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
          CostEnvelope (generatorProgAbi p time d allowedIdx outIdx) B := by
        simpa [B] using generatorProgAbi_cost_le_CostEnvelope p time d allowedIdx outIdx bits
          hwrite hblank hfalse htrue hallowed hout
      _ ≤ CostEnvelope (generatorProgAbi p time d allowedIdx outIdx) Q :=
        CostEnvelope_mono _ hBQ
  have hcostPolyQ :
      (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        a * (Q + 1) ^ a := by
    calc
      _ ≤ CostEnvelope (generatorProgAbi p time d allowedIdx outIdx) Q := hcostQ
      _ = (uniformCostEnvelopePoly (generatorProgAbi p time d allowedIdx outIdx)).eval Q := by
        symm; exact uniformCostEnvelopePoly_eval _ _
      _ ≤ a * (Q + 1) ^ a := by
        simpa [a, generatorProgAbiCostExponent] using
          (polynomial_nat_eval_le_power
            (uniformCostEnvelopePoly (generatorProgAbi p time d allowedIdx outIdx)) Q)
  have hQpoly : Q ≤ b * (N + 1) ^ b := by
    simpa [b] using generatorEnvB_eval_le_power p time d allowedIdx outIdx N
  have hQ1 : Q + 1 ≤ (b + 1) * (N + 1) ^ b := by
    have hpow : 1 ≤ (N + 1) ^ b := Nat.one_le_pow b _ (by omega)
    calc
      Q + 1 ≤ b * (N + 1) ^ b + (N + 1) ^ b := by omega
      _ = (b + 1) * (N + 1) ^ b := by ring
  have hQpow : (Q + 1) ^ a ≤ ((b + 1) * (N + 1) ^ b) ^ a :=
    Nat.pow_le_pow_left hQ1 _
  have hcostBound :
      (generatorProgAbi p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        a * ((b + 1) ^ a * (N + 1) ^ (b * a)) := by
    calc
      _ ≤ a * (Q + 1) ^ a := hcostPolyQ
      _ ≤ a * ((b + 1) * (N + 1) ^ b) ^ a := Nat.mul_le_mul_left _ hQpow
      _ = a * ((b + 1) ^ a * (N + 1) ^ (b * a)) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]

  have hcoef : a * (b + 1) ^ a ≤ c := by
    change a * (b + 1) ^ a ≤ a * (b + 1) ^ a + b * a + 1
    omega
  have hexp : b * a ≤ c := by
    change b * a ≤ a * (b + 1) ^ a + b * a + 1
    omega
  have htpow : (N + 1) ^ (b * a) ≤ (N + 1) ^ c :=
    Nat.pow_le_pow_right (by omega) hexp
  have hmul :
      a * (b + 1) ^ a * (N + 1) ^ (b * a) ≤ c * (N + 1) ^ c := by
    calc
      a * (b + 1) ^ a * (N + 1) ^ (b * a) ≤
          a * (b + 1) ^ a * (N + 1) ^ c :=
        Nat.mul_le_mul_left _ htpow
      _ ≤ c * (N + 1) ^ c := Nat.mul_le_mul_right _ hcoef
  have hfinal :
      a * ((b + 1) ^ a * (N + 1) ^ (b * a)) ≤ c * (N + 1) ^ c := by
    simpa [Nat.mul_assoc] using hmul
  simpa [N] using hcostBound.trans hfinal

/-! ## Compiled operand bound -/

lemma bitLen_generatorProgAbi_envB_le_power (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
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
    calc
      B + 1 ≤ Q + 1 := by omega
      _ ≤ b * (N + 1) ^ b + (N + 1) ^ b := by omega
      _ = (b + 1) * (N + 1) ^ b := by ring
  have hpow2 : (N + 1) ^ b ≤ (N + 1) ^ (b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hfinal : (b + 1) * (N + 1) ^ b ≤
      (b + 1) * (N + 1) ^ (b + 1) := Nat.mul_le_mul_left _ hpow2
  exact hbl.trans (hstep.trans hfinal)

lemma generatorProgAbi_compiled_operands_le_for (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    ∃ W, W ≤ (generatorEnvBExponent p time d allowedIdx outIdx + 1) *
        (bits.length + 1) ^ (generatorEnvBExponent p time d allowedIdx outIdx + 1) ∧
      CompiledOperandBound (generatorProgAbi p time d allowedIdx outIdx) bits W := by
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
  have hσ : StoreValuesLe B (bitInputStore bits) :=
    bitInputStore_storeValuesLe bits B hB1 hN
  refine ⟨bitLen B, bitLen_generatorProgAbi_envB_le_power p time d allowedIdx outIdx bits, ?_⟩
  exact compiledOperandBound_of_programBoundedIn _ bits B hB1 hσ
    (programBoundedIn_generatorProgAbi_valid p time d allowedIdx outIdx bits
      hwrite hblank hfalse htrue hallowed hout)
    (scanFree_generatorProgAbi p time d allowedIdx outIdx)


end NPComplete.CookLevin

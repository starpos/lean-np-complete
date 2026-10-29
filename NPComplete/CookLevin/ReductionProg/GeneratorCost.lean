module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedTop
public import NPComplete.RAMToTM.Generic.Api.ProgramCostBounds

/-!
# Generator cost envelope

Resource bounds for the raw bit-input generator are needed before its ABI wrapper can inherit
polynomial cost. This module proves the loop and envelope estimates at the bit-program level,
keeping output packaging separate from the generator's repeated-work analysis.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

lemma scanFree_to_noCompileTimeTables (p : Program) (h : ScanFree p) :
    NoCompileTimeTables p := by
  induction p with
  | skip => trivial
  | assign => trivial
  | assignInd => trivial
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ifNZ e a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | forN e body ih => exact ih h
  | scanList => exact h.elim
  | lookup => exact h.elim

lemma loopBounded_generatorProgFromBits (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    LoopBounded (generatorProgFromBits p time d allowedIdx outIdx)
      (Polynomial.eval bits.length
        (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (bitInputStore bits) := by
  let B := Polynomial.eval bits.length
    (envB p time d (prefixWord d bits) allowedIdx outIdx)
  have hB1 : 1 ≤ B := by
    have hK := envK_ge_one p time d (prefixWord d bits) allowedIdx outIdx bits.length
    have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx bits.length
    omega
  have hN : bits.length ≤ B := by
    have hsetup := setupM_gt p time d allowedIdx bits.length
    have hK := envK_ge_setupM p time d (prefixWord d bits) allowedIdx outIdx bits.length
    have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx bits.length
    omega
  have hσ : StoreBounded B (bitInputStore bits) := by
    exact bitInputStore_storeValuesLe bits B hB1 hN
  have hpb := programBoundedIn_generatorProgFromBits p time d allowedIdx outIdx bits
  have hnt := scanFree_to_noCompileTimeTables _
    (scanFree_generatorProgFromBits p time d allowedIdx outIdx)
  exact programBoundedIn_to_g6_loopBounded _ B B hB1 _ hσ hpb hnt le_rfl

lemma generatorProgFromBits_cost_le_CostEnvelope (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
      CostEnvelope (generatorProgFromBits p time d allowedIdx outIdx)
        (Polynomial.eval bits.length
          (envB p time d (prefixWord d bits) allowedIdx outIdx)) := by
  exact g6_cost_le_envelope _ _ _
    (loopBounded_generatorProgFromBits p time d allowedIdx outIdx bits)

noncomputable def generatorProgFromBitsCostExponent (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : ℕ :=
  let q := uniformCostEnvelopePoly (generatorProgFromBits p time d allowedIdx outIdx)
  (q.support.card + 1) * (q.support.sup (fun n => q.coeff n) + 1) *
    (q.support.sup id + 1)

lemma generator_foldr_max_le_of_forall {l : List ℕ} {B : ℕ}
    (h : ∀ v ∈ l, v ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldr]
      exact max_le (h a (by simp)) (ih (fun v hv => h v (by simp [hv])))

lemma prefixWord_mem_true_false (d : TableauDescriptor) (bits : Bits) {v : ℕ}
    (hv : v ∈ prefixWord d bits) : v = d.trueIdx ∨ v = d.falseIdx := by
  induction bits with
  | nil =>
      have hv' : v = d.falseIdx := by
        change v ∈ ([d.falseIdx] : List ℕ) at hv
        simpa using hv
      exact Or.inr hv'
  | cons b bs ih =>
      rw [prefixWord_cons] at hv
      simp only [List.mem_cons] at hv
      rcases hv with h0 | h1 | htail
      · exact Or.inl h0
      · cases b with
        | false => exact Or.inr (by simpa using h1)
        | true => exact Or.inl (by simpa using h1)
      · exact ih htail

lemma envIdxMax_le_of_prefix (d : TableauDescriptor)
    (pref pref' allowedIdx outIdx : List ℕ)
    (hpref : ∀ v ∈ pref, v ≤ envIdxMax d pref' allowedIdx outIdx) :
    envIdxMax d pref allowedIdx outIdx ≤ envIdxMax d pref' allowedIdx outIdx := by
  unfold envIdxMax
  apply generator_foldr_max_le_of_forall
  intro v hv
  simp only [List.mem_append, or_assoc] at hv
  rcases hv with hp | (ha | (ho | (hk | (h1 | (h2 | hh)))))
  · exact hpref v hp
  · exact envIdxMax_ge_allowed (prefIdx := pref') (outIdx := outIdx) ha
  · exact envIdxMax_ge_out (prefIdx := pref') ho
  · exact envIdxMax_ge_kind (prefIdx := pref') (allowedIdx := allowedIdx)
      (outIdx := outIdx) hk
  · exact envIdxMax_ge_arg1 (prefIdx := pref') (allowedIdx := allowedIdx)
      (outIdx := outIdx) h1
  · exact envIdxMax_ge_arg2 (prefIdx := pref') (allowedIdx := allowedIdx) h2
  · exact envIdxMax_ge_halt (prefIdx := pref') (allowedIdx := allowedIdx)
      (outIdx := outIdx) hh

lemma envK_eval_le_prefix_bound (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) (N : ℕ) :
    (envK p time d (prefixWord d bits) allowedIdx outIdx).eval N ≤
      (envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N := by
  rw [envK_eval, envK_eval]
  have hm := envIdxMax_le_of_prefix d (prefixWord d bits)
    [d.trueIdx, d.falseIdx] allowedIdx outIdx (by
      intro v hv
      have h := prefixWord_mem_true_false d bits hv
      rcases h with h | h
      · rw [h]
        exact envIdxMax_ge_pref (prefIdx := [d.trueIdx, d.falseIdx])
          (allowedIdx := allowedIdx) (outIdx := outIdx) (by simp)
      · rw [h]
        exact envIdxMax_ge_pref (prefIdx := [d.trueIdx, d.falseIdx])
          (allowedIdx := allowedIdx) (outIdx := outIdx) (by simp))
  unfold envKConst at hm ⊢
  omega


lemma envB_eval_le_prefix_bound (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) (N : ℕ) :
    (envB p time d (prefixWord d bits) allowedIdx outIdx).eval N ≤
      (envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N := by
  have hK := envK_eval_le_prefix_bound p time d allowedIdx outIdx bits N
  have hquad :
      (envK p time d (prefixWord d bits) allowedIdx outIdx).eval N *
          ((envK p time d (prefixWord d bits) allowedIdx outIdx).eval N *
            (4 + 3 * d.numLetters)) ≤
      (envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N *
          ((envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N *
            (4 + 3 * d.numLetters)) := by
    exact Nat.mul_le_mul hK (Nat.mul_le_mul hK le_rfl)
  have hWid :
      (envK p time d (prefixWord d bits) allowedIdx outIdx).eval N *
        ((envK p time d (prefixWord d bits) allowedIdx outIdx).eval N *
          ((envK p time d (prefixWord d bits) allowedIdx outIdx).eval N *
            envWidConst d allowedIdx)) ≤
      (envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N *
        ((envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N *
          ((envK p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N *
            envWidConst d allowedIdx)) := by
    exact Nat.mul_le_mul hK (Nat.mul_le_mul hK (Nat.mul_le_mul hK le_rfl))
  simp only [envB_eval, envS_eval, envWid_eval]
  omega


noncomputable def generatorEnvBExponent (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : ℕ :=
  let q := envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx
  (q.support.card + 1) * (q.support.sup (fun n => q.coeff n) + 1) *
    (q.support.sup id + 1)

lemma generatorEnvB_eval_le_power (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx).eval N ≤
      generatorEnvBExponent p time d allowedIdx outIdx * (N + 1) ^
        generatorEnvBExponent p time d allowedIdx outIdx := by
  simpa [generatorEnvBExponent] using
    (polynomial_nat_eval_le_power
      (envB p time d [d.trueIdx, d.falseIdx] allowedIdx outIdx) N)

lemma generatorProgFromBits_cost_le_input_power (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) :
    ∃ c, ∀ bits : Bits,
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        c * (bits.length + 1) ^ c := by
  let a := generatorProgFromBitsCostExponent p time d allowedIdx outIdx
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
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        CostEnvelope (generatorProgFromBits p time d allowedIdx outIdx) Q := by
    calc
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
          CostEnvelope (generatorProgFromBits p time d allowedIdx outIdx) B := by
        simpa [B] using
          (generatorProgFromBits_cost_le_CostEnvelope p time d allowedIdx outIdx bits)
      _ ≤ CostEnvelope (generatorProgFromBits p time d allowedIdx outIdx) Q :=
        CostEnvelope_mono _ hBQ
  have hcostPolyQ :
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        a * (Q + 1) ^ a := by
    calc
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
          CostEnvelope (generatorProgFromBits p time d allowedIdx outIdx) Q := hcostQ
      _ = (uniformCostEnvelopePoly
          (generatorProgFromBits p time d allowedIdx outIdx)).eval Q := by
        symm
        exact uniformCostEnvelopePoly_eval _ _
      _ ≤ a * (Q + 1) ^ a := by
        simpa [a, generatorProgFromBitsCostExponent] using
          (polynomial_nat_eval_le_power
            (uniformCostEnvelopePoly
              (generatorProgFromBits p time d allowedIdx outIdx)) Q)
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
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
        a * ((b + 1) ^ a * (N + 1) ^ (b * a)) := by
    calc
      (generatorProgFromBits p time d allowedIdx outIdx).cost (bitInputStore bits) ≤
          a * (Q + 1) ^ a := hcostPolyQ
      _ ≤ a * ((b + 1) * (N + 1) ^ b) ^ a :=
        Nat.mul_le_mul_left _ hQpow
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

end NPComplete.CookLevin

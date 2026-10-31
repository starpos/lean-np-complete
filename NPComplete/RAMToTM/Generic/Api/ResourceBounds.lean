module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.ProgramCostBounds
public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded
public import NPComplete.RAMToTM.Generic.Api.BoundedInMono

/-!
Resource bounds let clients construct deciders without reasoning about compiled execution.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile Polynomial

noncomputable def costEnvelopePoly : Program → Polynomial ℕ
  | .skip => C 1
  | .assign _ e => C (e.cost + 1)
  | .assignInd eA eV => C (eA.cost + eV.cost + 1)
  | .seq p q => costEnvelopePoly p + costEnvelopePoly q
  | .ifNZ e p q => C (e.cost + 1) + costEnvelopePoly p + costEnvelopePoly q
  | .forN e body => C (e.cost + 1) + X * costEnvelopePoly body
  | .scanList _ _ body => C 1 + X * costEnvelopePoly body
  | .lookup xs _ _ => C (xs.length + 1)

lemma costEnvelopePoly_eval (p : Program) (L : ℕ) :
    (costEnvelopePoly p).eval L = CostEnvelope p L := by
  induction p with
  | skip => simp [costEnvelopePoly, CostEnvelope]
  | assign => simp [costEnvelopePoly, CostEnvelope]
  | assignInd => simp [costEnvelopePoly, CostEnvelope]
  | seq p q ihp ihq => simp [costEnvelopePoly, CostEnvelope, ihp, ihq]
  | ifNZ e p q ihp ihq => simp [costEnvelopePoly, CostEnvelope, ihp, ihq]
  | forN e body ih => simp [costEnvelopePoly, CostEnvelope, ih]
  | scanList xs r body ih => simp [costEnvelopePoly, CostEnvelope, ih]
  | lookup => simp [costEnvelopePoly, CostEnvelope]

lemma noCompileTimeTables_of_scanFree (p : Program) (h : ScanFree p) : NoCompileTimeTables p := by
  induction p with
  | skip | assign | assignInd => trivial
  | seq p q ihp ihq | ifNZ _ p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | forN _ body ih => exact ih h
  | scanList | lookup => cases h

lemma exists_cost_le_of_storeBounded (p : Program) (hsf : ScanFree p) :
    ∃ c, ∀ B σ, 1 ≤ B → StoreBounded B σ → ProgramBoundedIn B σ p →
      p.cost σ ≤ c * (B + 1) ^ c := by
  let q := costEnvelopePoly p
  let c := (q.support.card + 1) * (q.support.sup (fun n => q.coeff n) + 1) *
    (q.support.sup id + 1)
  refine ⟨c, fun B σ hB hσ hp => ?_⟩
  have h := g6_cost_le_envelope p B σ (programBoundedIn_to_g6_loopBounded p B B hB σ hσ hp
    (noCompileTimeTables_of_scanFree p hsf) le_rfl)
  rw [← costEnvelopePoly_eval] at h
  exact h.trans (polynomial_nat_eval_le_power q B)

/-- A scan-free bounded execution has polynomial cost in its value bound. -/
@[construction_api] lemma exists_cost_le_of_programBoundedIn (p : Program) (hsf : ScanFree p) :
    ∃ c, ∀ B σ, 1 ≤ B → StoreValuesLe B σ → ProgramBoundedIn B σ p →
      p.cost σ ≤ c * (B + 1) ^ c :=
  exists_cost_le_of_storeBounded p hsf

open NPComplete.BitEncoding (Bits)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

lemma storeValuesLe_bitInputStore_length (bits : Bits) :
    StoreValuesLe (bits.length + 1) (bitInputStore bits) := by
  intro i
  cases i with
  | zero => simp [bitInputStore]
  | succ i => simp only [bitInputStore]; split <;> omega

@[construction_api] lemma storeValuesLe_bitInputStore (bits : Bits) {B : ℕ}
    (hB : 1 ≤ B) (hbits : bits.length ≤ B) :
    StoreValuesLe B (bitInputStore bits) := by
  intro i
  cases i with
  | zero => simpa [bitInputStore] using hbits
  | succ i => simp only [bitInputStore]; split <;> omega

/-- A polynomial value bound yields both resource bounds required by a decider. -/
@[construction_api] lemma exists_resources_of_programBoundedIn {α : Type} (enc : α → Bits)
    (p : Program) (B : ℕ → ℕ) (q : Polynomial ℕ)
    (hq : ∀ L, B L ≤ q.eval L) (hsf : ScanFree p)
    (hp : ∀ x, ProgramBoundedIn (B (enc x).length) (bitInputStore (enc x)) p) :
    ∃ c bit_c, (∀ x, p.cost (bitInputStore (enc x)) ≤ c * ((enc x).length + 1) ^ c) ∧
      (∀ x, ∃ W, W ≤ bit_c * ((enc x).length + 1) ^ bit_c ∧
        CompiledOperandBound p (enc x) W) := by
  obtain ⟨d, hd⟩ := exists_cost_le_of_programBoundedIn p hsf
  let Q : Polynomial ℕ := q + X + C 1
  let qc : Polynomial ℕ := C d * (Q + 1) ^ d
  let qw : Polynomial ℕ := Q + 1
  let c := (qc.support.card + 1) * (qc.support.sup (fun n => qc.coeff n) + 1) *
    (qc.support.sup id + 1)
  let bit_c := (qw.support.card + 1) * (qw.support.sup (fun n => qw.coeff n) + 1) *
    (qw.support.sup id + 1)
  refine ⟨c, bit_c, ?_, ?_⟩
  · intro x
    let L := (enc x).length
    let M := B L + L + 1
    have hM : M ≤ Q.eval L := by simp [M, Q]; have := hq L; omega
    have hstore : StoreValuesLe M (bitInputStore (enc x)) := fun i =>
      (storeValuesLe_bitInputStore_length (enc x) i).trans (by dsimp [M, L]; omega)
    have hprog := programBoundedIn_mono p (show B L ≤ M by dsimp [M]; omega) (hp x)
    calc p.cost (bitInputStore (enc x)) ≤ d * (M + 1) ^ d :=
        hd M _ (by dsimp [M]; omega) hstore hprog
      _ ≤ qc.eval L := by
        simp only [qc, eval_mul, eval_C, eval_pow, eval_add, eval_one]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ ≤ c * (L + 1) ^ c := polynomial_nat_eval_le_power qc L
  · intro x
    let L := (enc x).length
    let M := B L + L + 1
    have hM : M ≤ Q.eval L := by simp [M, Q]; have := hq L; omega
    have hstore : StoreValuesLe M (bitInputStore (enc x)) := fun i =>
      (storeValuesLe_bitInputStore_length (enc x) i).trans (by dsimp [M, L]; omega)
    have hprog := programBoundedIn_mono p (show B L ≤ M by dsimp [M]; omega) (hp x)
    refine ⟨bitLen M, ?_, compiledOperandBound_of_programBoundedIn p (enc x) M
      (by dsimp [M]; omega) hstore hprog hsf⟩
    calc bitLen M ≤ M + 1 := bitLen_le_succ _
      _ ≤ qw.eval L := by simp [qw]; omega
      _ ≤ bit_c * (L + 1) ^ bit_c := polynomial_nat_eval_le_power qw L

/-- The resource bounds for a monomial value bound, including the zero case. -/
@[construction_api] lemma exists_resources_of_monomial_bound {α : Type} (enc : α → Bits)
    (p : Program) (k : ℕ) (hsf : ScanFree p)
    (hp : ∀ x, ProgramBoundedIn (k * ((enc x).length + 1) ^ k) (bitInputStore (enc x)) p) :
    ∃ c bit_c, (∀ x, p.cost (bitInputStore (enc x)) ≤ c * ((enc x).length + 1) ^ c) ∧
      (∀ x, ∃ W, W ≤ bit_c * ((enc x).length + 1) ^ bit_c ∧
        CompiledOperandBound p (enc x) W) := by
  apply exists_resources_of_programBoundedIn enc p (fun L => k * (L + 1) ^ k)
    (C k * (X + 1) ^ k) _ hsf hp
  intro L
  simp

/-- Construct a decider directly from a polynomial value bound. -/
@[construction_api] noncomputable def BoundedWhileDecider.ofProgramBoundedIn {α : Type}
    (enc : α → Bits) (p : Program) (outReg : ℕ) (B : ℕ → ℕ) (q : Polynomial ℕ)
    (hq : ∀ L, B L ≤ q.eval L) (hsf : ScanFree p)
    (hp : ∀ x, ProgramBoundedIn (B (enc x).length) (bitInputStore (enc x)) p) :
    BoundedWhileDecider enc (fun _ => True)
      (fun x => p.eval (bitInputStore (enc x)) outReg = 1) :=
  let h := exists_resources_of_programBoundedIn enc p B q hq hsf hp
  BoundedWhileDecider.ofBounds enc p outReg h.choose h.choose_spec.choose
    h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2

end NPComplete.RAMToTM

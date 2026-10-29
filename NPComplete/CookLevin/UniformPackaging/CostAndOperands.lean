module

public import NPComplete.CookLevin.UniformPackaging.ProducerSetupBounds
public import NPComplete.RAMToTM.Generic.Api.ProgramCostBounds

/-!
# Cost envelopes and operands

The outer emitter composes branches and loops whose sizes depend on parsed
clauses. This module derives structural cost envelopes and bounds program
operands from bounded execution, providing reusable resource estimates for the
producer.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

/-! ## Structural cost envelopes

The cost envelope charges both branches of a conditional and uses one common entry bound for every
dynamic loop.  The latter is deliberately proved from `ProgramBoundedIn` at every visited store;
the semantic emitter invariant supplies that bound for the actual remaining suffix clauses. -/

lemma loopEval_storeValuesLe_of_programBoundedIn
    (p : Program) (B k : ℕ) (σ : Store) (hB1 : 1 ≤ B)
    (hσ : StoreValuesLe B σ)
    (hp : ∀ m < k, ProgramBoundedIn B (loopEval p m σ) p)
    (hsf : ScanFree p) :
    ∀ m ≤ k, StoreValuesLe B (loopEval p m σ) := by
  intro m
  induction m with
  | zero => intro _; simpa using hσ
  | succ m ih =>
      intro hm
      rw [uniform_loopEval_succ_right]
      exact program_eval_storeValuesLe (loopEval p m σ) p hB1 (ih (by omega))
        (hp m (by omega)) hsf

lemma loopBounded_of_programBoundedIn
    (p : Program) (B : ℕ) (σ : Store) (hB1 : 1 ≤ B)
    (hσ : StoreValuesLe B σ) (hp : ProgramBoundedIn B σ p) (hsf : ScanFree p) :
    LoopBounded p B σ := by
  induction p generalizing σ with
  | skip => trivial
  | assign => trivial
  | assignInd => trivial
  | seq p q ihp ihq =>
      exact ⟨ihp σ hσ hp.1 hsf.1,
        ihq (p.eval σ)
          (program_eval_storeValuesLe σ p hB1 hσ hp.1 hsf.1) hp.2 hsf.2⟩
  | ifNZ e p q ihp ihq =>
      exact ⟨ihp σ hσ hp.2.1 hsf.1, ihq σ hσ hp.2.2 hsf.2⟩
  | forN n body ih =>
      have hn : n.eval σ ≤ B := expr_eval_le_of_bounded_in hσ hB1 n hp.1
      have hstores := loopEval_storeValuesLe_of_programBoundedIn body B (n.eval σ) σ hB1 hσ
        (fun m hm => hp.2 m hm) hsf
      refine ⟨hn, ?_⟩
      intro m hm
      exact ih (loopEval body m σ) (hstores m (by omega)) (hp.2 m hm) hsf
  | scanList => cases hsf
  | lookup => cases hsf

lemma program_cost_le_CostEnvelope_of_bounded
    (p : Program) (B : ℕ) (σ : Store) (hB1 : 1 ≤ B)
    (hσ : StoreValuesLe B σ) (hp : ProgramBoundedIn B σ p) (hsf : ScanFree p) :
    p.cost σ ≤ CostEnvelope p B := by
  exact g6_cost_le_envelope p B σ
    (loopBounded_of_programBoundedIn p B σ hB1 hσ hp hsf)

noncomputable def uniformCostEnvelopePoly : Program → Polynomial ℕ
  | .skip => C 1
  | .assign _ e => C (e.cost + 1)
  | .assignInd eA eV => C (eA.cost + eV.cost + 1)
  | .seq p q => uniformCostEnvelopePoly p + uniformCostEnvelopePoly q
  | .ifNZ e p q => C (e.cost + 1) + uniformCostEnvelopePoly p + uniformCostEnvelopePoly q
  | .forN e body => C (e.cost + 1) + X * uniformCostEnvelopePoly body
  | .scanList _ _ body => C 1 + X * uniformCostEnvelopePoly body
  | .lookup xs _ _ => C (xs.length + 1)

lemma uniformCostEnvelopePoly_eval (p : Program) (L : ℕ) :
    (uniformCostEnvelopePoly p).eval L = CostEnvelope p L := by
  induction p with
  | skip => simp [uniformCostEnvelopePoly, CostEnvelope]
  | assign => simp [uniformCostEnvelopePoly, CostEnvelope]
  | assignInd => simp [uniformCostEnvelopePoly, CostEnvelope]
  | seq p q ihp ihq => simp [uniformCostEnvelopePoly, CostEnvelope, ihp, ihq]
  | ifNZ e p q ihp ihq => simp [uniformCostEnvelopePoly, CostEnvelope, ihp, ihq]
  | forN e body ih => simp [uniformCostEnvelopePoly, CostEnvelope, ih]
  | scanList xs r body ih => simp [uniformCostEnvelopePoly, CostEnvelope, ih]
  | lookup => simp [uniformCostEnvelopePoly, CostEnvelope]

noncomputable def uniformEmitDispatchPoly : Polynomial ℕ :=
  C 14348907 * ((X + 1) ^ 3 + 3 * X + C 142) + C 22054801

lemma uniformEmitDispatchPoly_eval (N : ℕ) :
    uniformEmitDispatchPoly.eval N = uniformEmitDispatchEnvelope N := by
  simp [uniformEmitDispatchPoly, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitSyntaxEnvelope,
    uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
    uniformSlackNat, uctCurJ, relocateControlGap]
  ring_nf

def uniformSatToThreeCNFCostEnvelope (φ : CNF) : ℕ :=
  CostEnvelope uniformSatToThreeCNFProg (uniformEmitDispatchEnvelope (encodeCNF φ).length)

noncomputable def uniformSatToThreeCNFCostPoly : Polynomial ℕ :=
  (uniformCostEnvelopePoly uniformSatToThreeCNFProg).comp uniformEmitDispatchPoly

lemma uniformSatToThreeCNFProg_cost_le_costEnvelope (φ : CNF) :
    uniformSatToThreeCNFProg.cost (bitInputStore (encodeCNF φ)) ≤
      uniformSatToThreeCNFCostEnvelope φ := by
  let N := (encodeCNF φ).length
  let B := uniformEmitDispatchEnvelope N
  have hB1 : 1 ≤ B := by
    have h25 : 25 ≤ B := uniformEmitDispatchEnvelope_ge_25 N
    omega
  have hN : N ≤ B := by
    exact (uniform_emit_n_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N)
  have hσ : StoreValuesLe B (bitInputStore (encodeCNF φ)) := by
    intro r
    cases r with
    | zero => simpa [bitInputStore, N] using hN
    | succ r =>
        simp [bitInputStore]
        split <;> omega
  have hp := programBoundedIn_uniformSatToThreeCNFProg φ B (by simp [B, N])
  have hc := program_cost_le_CostEnvelope_of_bounded uniformSatToThreeCNFProg B
    (bitInputStore (encodeCNF φ)) hB1 hσ hp scanFree_uniformSatToThreeCNFProg
  simpa [uniformSatToThreeCNFCostEnvelope, B, N] using hc

lemma uniformSatToThreeCNFCostEnvelope_le_poly (φ : CNF) :
    uniformSatToThreeCNFCostEnvelope φ ≤
      uniformSatToThreeCNFCostPoly.eval (encodeCNF φ).length := by
  unfold uniformSatToThreeCNFCostEnvelope
  have he := uniformCostEnvelopePoly_eval uniformSatToThreeCNFProg
    (uniformEmitDispatchEnvelope (encodeCNF φ).length)
  rw [← he]
  change (uniformCostEnvelopePoly uniformSatToThreeCNFProg).eval
      (uniformEmitDispatchEnvelope (encodeCNF φ).length) ≤
    ((uniformCostEnvelopePoly uniformSatToThreeCNFProg).comp uniformEmitDispatchPoly).eval
      (encodeCNF φ).length
  rw [Polynomial.eval_comp, uniformEmitDispatchPoly_eval]

lemma uniformSatToThreeCNFProg_cost_le_poly (φ : CNF) :
    uniformSatToThreeCNFProg.cost (bitInputStore (encodeCNF φ)) ≤
      uniformSatToThreeCNFCostPoly.eval (encodeCNF φ).length :=
  (uniformSatToThreeCNFProg_cost_le_costEnvelope φ).trans
    (uniformSatToThreeCNFCostEnvelope_le_poly φ)

noncomputable def uniformSatToThreeCNFCostC : ℕ :=
  let p := uniformSatToThreeCNFCostPoly
  (p.support.card + 1) * (p.support.sup (fun n => p.coeff n) + 1) *
    (p.support.sup id + 1)

lemma uniformSatToThreeCNFCostPoly_le_power (N : ℕ) :
    uniformSatToThreeCNFCostPoly.eval N ≤
      uniformSatToThreeCNFCostC * (N + 1) ^ uniformSatToThreeCNFCostC := by
  have h := polynomial_nat_eval_le_power uniformSatToThreeCNFCostPoly N
  simpa [uniformSatToThreeCNFCostC] using h

lemma uniformSatToThreeCNFProg_cost_le_power (φ : CNF) :
    uniformSatToThreeCNFProg.cost (bitInputStore (encodeCNF φ)) ≤
      uniformSatToThreeCNFCostC * ((encodeCNF φ).length + 1) ^
        uniformSatToThreeCNFCostC := by
  exact (uniformSatToThreeCNFProg_cost_le_poly φ).trans
    (uniformSatToThreeCNFCostPoly_le_power (encodeCNF φ).length)

/-! ## Compiled operand bounds

`compile_exec_bounded` supplies the intermediate `RegsMemLe` invariant for the complete compiled
program.  Once its endpoint reaches the end of the compiled list, the RAM is halted; this avoids
any inspection or enumeration of the compiled instruction list. -/

def uniformSatToThreeCNFOperandC : ℕ := 4000000000

lemma uniformEmitDispatchEnvelope_plus_one_le_operand_poly (N : ℕ) :
    uniformEmitDispatchEnvelope N + 1 ≤
      uniformSatToThreeCNFOperandC * (N + 1) ^ 4 := by
  rw [← uniformEmitDispatchPoly_eval N]
  simp [uniformEmitDispatchPoly, uniformSatToThreeCNFOperandC]
  nlinarith [sq_nonneg (N : ℤ), sq_nonneg (N + 1 : ℤ)]

lemma uniform_sat_to_three_cnf_operand_envelope_le_poly (N : ℕ) :
    bitLen (uniformEmitDispatchEnvelope N) ≤
      uniformSatToThreeCNFOperandC * (N + 1) ^ 4 := by
  exact (bitLen_le_succ _).trans
    (uniformEmitDispatchEnvelope_plus_one_le_operand_poly N)

lemma uniformSatToThreeCNFProg_compiledOperandBound (φ : CNF) :
    CompiledOperandBound uniformSatToThreeCNFProg (encodeCNF φ)
      (bitLen (uniformEmitDispatchEnvelope (encodeCNF φ).length)) := by
  let bits := encodeCNF φ
  let B := uniformEmitDispatchEnvelope bits.length
  have hB1 : 1 ≤ B := by
    have h25 := uniformEmitDispatchEnvelope_ge_25 bits.length
    omega
  have hN : bits.length ≤ B := by
    exact (uniform_emit_n_le_long_value_envelope bits.length).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope bits.length)
  have hσ : StoreValuesLe B (bitInputStore bits) := by
    intro r
    cases r with
    | zero => exact hN
    | succ r =>
        simp [bitInputStore]
        split <;> omega
  have hp : ProgramBoundedIn B (bitInputStore bits) uniformSatToThreeCNFProg := by
    simpa [bits, B] using
      programBoundedIn_uniformSatToThreeCNFProg φ B (by simp [B, bits])
  simpa [bits, B] using compiledOperandBound_of_programBoundedIn
    uniformSatToThreeCNFProg bits B hB1 hσ hp scanFree_uniformSatToThreeCNFProg

end NPComplete.CookLevin

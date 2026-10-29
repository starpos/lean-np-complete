module

public import NPComplete.CookLevin.UniformPackaging
public import NPComplete.CookLevin.Machines.RawDecodePackaging
public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.CookLevin.Entry

/-!
# SAT-to-three-CNF reduction

The transformation crosses from semantic CNF rewriting to a bounded RAM
producer, so its output, runtime, and compiled-memory interfaces must agree.
This module composes those contracts into the computability result for the
reduction, separate from the clause-level proof modules.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BitCostRAM
open Turing

lemma uniformSatToThreeCNFProg_compiled_operands_le_for (φ : CNF) :
    ∃ W, W ≤ uniformSatToThreeCNFOperandC * ((encodeCNF φ).length + 1) ^
        uniformSatToThreeCNFOperandC ∧
      CompiledOperandBound uniformSatToThreeCNFProg (encodeCNF φ) W := by
  let N := (encodeCNF φ).length
  let B := uniformEmitDispatchEnvelope N
  refine ⟨bitLen B, ?_, ?_⟩
  · have hsmall := uniform_sat_to_three_cnf_operand_envelope_le_poly N
    have hpow : (N + 1) ^ 4 ≤ (N + 1) ^ uniformSatToThreeCNFOperandC := by
      apply Nat.pow_le_pow_right
      · omega
      · norm_num [uniformSatToThreeCNFOperandC]
    have hmul := Nat.mul_le_mul_left uniformSatToThreeCNFOperandC hpow
    simpa [B] using hsmall.trans hmul
  · simpa [N, B] using uniformSatToThreeCNFProg_compiledOperandBound φ

noncomputable def satToThreeCNFProducerDecider :
    BoundedWhileDecider encodeCNF (fun _ : CNF => True)
      (fun φ => uniformSatToThreeCNFProg.eval
        (bitInputStore (encodeCNF φ)) 0 = 1) :=
  BoundedWhileDecider.ofBounds encodeCNF uniformSatToThreeCNFProg 0 uniformSatToThreeCNFCostC
    uniformSatToThreeCNFOperandC
    (fun φ => uniformSatToThreeCNFProg_cost_le_power φ)
    (fun φ => uniformSatToThreeCNFProg_compiled_operands_le_for φ)

lemma encodeThreeClause_ends_true (c : ThreeClause) :
    ∃ xs, NPComplete.SAT.encodeThreeClause c = xs ++ [true] := by
  cases c with
  | mk l1 l2 l3 =>
      obtain ⟨xs, hxs⟩ := encodeLiteral_ends_true l3
      refine ⟨NPComplete.SAT.encodeLiteral l1 ++ NPComplete.SAT.encodeLiteral l2 ++ xs, ?_⟩
      simp [NPComplete.SAT.encodeThreeClause, hxs, List.append_assoc]

lemma encodeList_threeClause_ends_true (cs : List ThreeClause) :
    ∃ xs, NPComplete.BitEncoding.encodeList
        NPComplete.SAT.encodeThreeClause cs = xs ++ [true] := by
  exact encodeList_ends_true NPComplete.SAT.encodeThreeClause
    encodeThreeClause_ends_true cs

lemma encodeThreeCNF_ends_true (f : ThreeCNF) :
    ∃ xs, NPComplete.SAT.encodeThreeCNF f = xs ++ [true] := by
  obtain ⟨xnat, hnat⟩ := encodeNat_ends_true f.numVars
  obtain ⟨xlist, hlist⟩ := encodeList_threeClause_ends_true f.clauses
  refine ⟨xnat ++ [true] ++ xlist, ?_⟩
  rw [NPComplete.SAT.encodeThreeCNF, hnat, hlist]
  simp [List.append_assoc]

lemma satToThreeCNF_computable :
    Nonempty
      (TM0ComputableInPolyTime encodeCNF NPComplete.SAT.ValidThreeCNF.encode toValidThreeCNF) := by
  have h := fun φ => uniformSatToThreeCNFProg_eval_encode φ
  refine ⟨TM0ComputableInPolyTime.of_forwardBitProducer satToThreeCNFProducerDecider
    uniformStartNat uniformSatToThreeCNFOutPoly
    (fun φ => (h φ).1) ?_ ?_ ?_ ?_ ?_⟩
  · intro φ
    rw [toValidThreeCNF_encode]
    exact (h φ).2.1
  · intro φ i hi
    simp only [toValidThreeCNF_encode] at hi ⊢
    exact (h φ).2.2.1 i hi
  · intro φ
    rw [toValidThreeCNF_encode]
    exact uniformSatToThreeCNFProg_outLen_le φ
  · intro φ
    rw [toValidThreeCNF_encode]
    exact encodeThreeCNF_ends_true (toThreeCNF φ)
  · intro φ
    rw [toValidThreeCNF_encode]
    unfold NPComplete.SAT.encodeThreeCNF
    simp only [List.length_append]
    have hnat := NPComplete.BitEncoding.encodeNat_length
      (toThreeCNF φ).numVars
    have hlist := NPComplete.BitEncoding.encodeList_length_ge
      NPComplete.SAT.encodeThreeClause (toThreeCNF φ).clauses
    omega

def satToThreeCNF :
    PolyTimeReduction encodeCNF NPComplete.SAT.ValidThreeCNF.encode
      SAT (ThreeSAT ∘ Subtype.val) where
  map := toValidThreeCNF
  computable := satToThreeCNF_computable
  correct := by
    intro φ
    simpa [Function.comp_apply, toValidThreeCNF] using sat_iff_threeSAT φ

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbiCompApp
public import NPComplete.CookLevin.Tableau.DescriptorAbiPremises
public import NPComplete.CookLevin.ReductionProg.GeneratorLoadPrefix
public import NPComplete.CookLevin.ReductionProg.GeneratorSizePoly

/-!
`inNP_has_reduction_of_sat_equivalent_map`'s `hgen` obligation only needs some
SAT-equivalent CNF, not `boundedCookLevinCNFMap` itself.  The dense-layout
descriptor CNF is instantiated at descriptor `d` induced by a verifier machine;
the ABI generator emits it in polynomial time, with the four ABI premises needed
for `d`.  This file composes the descriptor CNF, the verifier-derived descriptor,
and the ABI generator.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)

/-- The generator's dense descriptor CNF, at the descriptor a verifier machine
induces and the generator's own window, is a poly-time-computable CNF
satisfiability-equivalent to `boundedCookLevinCNFMap`. -/
lemma hgen_of_abi_parts {α : Type} (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      Computability.encodeBool (fun xw => V xw.1 xw.2)) :
    ∃ g : α → CNF,
      (∀ x, SAT (g x) ↔ SAT (boundedCookLevinCNFMap enc p hV x)) ∧
      Nonempty (TM0ComputableInPolyTime enc encodeCNF g) := by
  set aux := executableTableauAuxOf hV.toTM0ComputableAux with haux
  set d := descriptorOf hV.toTM0ComputableAux.M aux.stateList aux.letterList with hd
  set allowedIdx := ([some false, some true] : List (Option Bool)).map
    (execLetterIdx aux.letterList) with hAllowed
  set outIdx := (tapeSymbols [true] : List (Option Bool)).map
    (execLetterIdx aux.letterList) with hOutIdx
  have hfalse_eq : d.falseIdx = execLetterIdx aux.letterList (some false) := rfl
  have htrue_eq : d.trueIdx = execLetterIdx aux.letterList (some true) := rfl
  have hwrite := descriptorOf_abi_write hV.toTM0ComputableAux.M aux.stateList aux.letterList
  have hblank := descriptorOf_abi_blank hV.toTM0ComputableAux.M aux.stateList aux.letterList
  have hfalse := descriptorOf_abi_false hV.toTM0ComputableAux.M aux.stateList aux.letterList
  have htrue := descriptorOf_abi_true hV.toTM0ComputableAux.M aux.stateList aux.letterList
  have hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1 := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact execLetterIdx_lt aux.letterList b
  have hout0 : ∀ a ∈ outIdx, a < d.numLetters + 1 := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact execLetterIdx_lt aux.letterList b
  refine ⟨fun x => descTableauCNF
    (denseLayout (d.numStates + 1) ((cookWindowPoly p hV.time).eval (enc x).length)
      (d.numLetters + 1))
    d (prefixWord d (enc x)) (p.eval (enc x).length) allowedIdx outIdx
    ((cookWindowPoly p hV.time).eval (enc x).length)
    ((timePoly p hV.time).eval (enc x).length), ?_, ?_⟩
  · intro x
    dsimp only
    have hW : windowSize ((pairBits (enc x) []).length + boundedCertificateBound enc p x)
        (tapeSymbols [true] : List (Option Bool)).length
        (boundedVerifierTimeBound enc p hV x) ≤ (cookWindowPoly p hV.time).eval (enc x).length :=
      cookWindowPoly_ge_target enc p hV x
    have hB := descTableauCNF_dense_boundedCookLevinCNFMap_sat_iff_at_window enc p hV x
      ((cookWindowPoly p hV.time).eval (enc x).length) hW
    have hpref : prefixWord d (enc x) =
        ((pairBits (enc x) []).map some).map (execLetterIdx aux.letterList) :=
      prefixWord_eq_pairBits_execLetterIdx aux.letterList (enc x) d hfalse_eq htrue_eq
    have hT : (timePoly p hV.time).eval (enc x).length = boundedVerifierTimeBound enc p hV x := by
      rw [timePoly_eval]
      rfl
    rw [hpref, hT]
    exact hB
  · exact generator_abi_computable_of_enc enc p hV.time d allowedIdx outIdx
      hwrite hblank hfalse htrue hallowed hout0

end NPComplete.CookLevin

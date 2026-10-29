module

public import NPComplete.CookLevin.Generate.BoundedMap

/-!
# Exact certificate characterization

The fixed-length verifier CNF must exclude padding from its witness. This
module proves that satisfiability is equivalent to an accepting run with a
certificate of exactly the prescribed length, and packages the general output
as a valid 3CNF.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

lemma generateVerifierCNF_sat_of_exact_certificate
    (tm : TM0ComputableAux Bool) (x w : List Bool) (T : ℕ)
    (hRun : MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
      (tapeSymbols [true]) T) :
    SAT (generateVerifierCNF tm x w.length T) := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let suffix : List (Option Bool) := w.map some
  have hinput : pref ++ suffix = tapeSymbols (pairBits x w) := by
    simp [pref, suffix, tapeSymbols, pairBits, List.map_append]
  have hsuffix : ∀ a ∈ suffix, a ∈ ([some false, some true] : List (Option Bool)) := by
    intro a ha
    have ha' : a ∈ w.map some := by simpa [suffix] using ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha'
    cases b <;> simp
  have hsat := tableauMachineWithInit_sat_of_run
    (M := tm.M) (S := tm.S) (input := pref ++ suffix)
    (output := tapeSymbols [true]) (pref := pref)
    (freeLen := suffix.length) (allowed := [some false, some true]) (T := T)
    tm.supports (by simpa [hinput] using hRun)
    (by
      intro p hp
      exact initSymbol_append_idxToPos_prefix pref suffix T p hp)
    (by
      intro p hp hp'
      let i := p - (T + pref.length)
      have hi : i < suffix.length := by omega
      refine ⟨suffix.getI i, ?_, ?_⟩
      · apply hsuffix
        rw [List.getI_eq_getElem _ hi]
        exact List.getElem_mem _
      · exact initSymbol_append_idxToPos_suffix pref suffix T p hp hp')
    (by
      intro p hp
      exact initSymbol_append_idxToPos_default pref suffix T p hp)
  simpa [generateVerifierCNF, tableauMachineWithInit, pref, suffix, tapeSymbols, pairBits,
    List.map_append] using hsat

lemma generateVerifierCNF_sat_implies_exact_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool) (certificateBound T : ℕ)
    (hSat : SAT (generateVerifierCNF tm x certificateBound T)) :
    ∃ w : List Bool, w.length = certificateBound ∧
      MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
        (tapeSymbols [true]) T := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let output : List (Option Bool) := tapeSymbols [true]
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length output.length T
  obtain ⟨τ, hτ⟩ := hSat
  have hτ' : ∀ c ∈
      (tableauMachineWithInit tm.M tm.S shape output T
        (prefixInitClauses tm.S pref certificateBound
          [some false, some true] W T)).clauses,
      c.Satisfied τ := by
    simpa [generateVerifierCNF, pref, output, shape, W] using hτ
  have hshape : shape.length = pref.length + certificateBound := by
    simp [shape]
  have hW : ∀ i, i < certificateBound →
      T + pref.length + i < W := by
    intro i hi
    dsimp [W]
    unfold windowSize
    have hm : shape.length ≤ max shape.length output.length := Nat.le_max_left _ _
    omega
  have hfreeBool : ∀ i, i < certificateBound →
      ∃ b : Bool,
        τ (cellVar 0 (T + pref.length + i) (letterIdx (some b))) = true := by
    intro i hi
    have hc : (atLeastOne
        ([cellVar 0 (T + pref.length + i) (letterIdx (some false)),
          cellVar 0 (T + pref.length + i) (letterIdx (some true))])).Satisfied τ := by
      apply hτ'
      simp only [tableauMachineWithInit, List.mem_append]
      have hp : T + pref.length + i < W := hW i hi
      have hpcert : T + pref.length + i < T + pref.length + certificateBound := by
        omega
      have hmem : atLeastOne
          [cellVar 0 (T + pref.length + i) (letterIdx (some false)),
            cellVar 0 (T + pref.length + i) (letterIdx (some true))] ∈
          prefixInitClauses tm.S pref certificateBound
            [some false, some true] W T := by
        refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
        exact List.mem_map.mpr ⟨T + pref.length + i,
          List.mem_range.mpr hp, by simp [hpcert]⟩
      aesop
    obtain ⟨v, hv, hval⟩ := atLeastOne_exists hc
    simp only [List.mem_cons] at hv
    rcases hv with hfalse | htrue
    · subst v
      exact ⟨false, hval⟩
    · have htrue' : v =
          cellVar 0 (T + pref.length + i) (letterIdx (some true)) := by
        simpa using htrue
      subst v
      exact ⟨true, hval⟩
  let chooseB : ℕ → Bool := fun i =>
    if hi : i < certificateBound then Classical.choose (hfreeBool i hi) else false
  let suffix : List (Option Bool) :=
    (List.range certificateBound).map (fun i => some (chooseB i))
  have hsuffixLen : suffix.length = certificateBound := by
    simp [suffix]
  have hsuffix_get : ∀ i, i < certificateBound →
      suffix.getI i = some (chooseB i) := by
    intro i hi
    rw [List.getI_eq_getElem _ (by simp [suffix, hi])]
    simp [suffix]
  have hfreeSuffix : ∀ i, i < certificateBound →
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (suffix.getI i))) = true := by
    intro i hi
    rw [hsuffix_get i hi]
    have hchoose : chooseB i = Classical.choose (hfreeBool i hi) := by
      simp [chooseB, hi]
    rw [hchoose]
    exact Classical.choose_spec (hfreeBool i hi)
  have hτSuffix : ∀ c ∈
      (tableauMachineWithInit tm.M tm.S (pref ++ suffix) output T
        (prefixInitClauses tm.S pref certificateBound
          [some false, some true]
          (windowSize (pref ++ suffix).length output.length T) T)).clauses,
      c.Satisfied τ := by
    intro c hc
    apply hτ'
    simpa [tableauMachineWithInit, shape, suffix, W, hsuffixLen,
      List.length_map] using hc
  have hout := machineOutputs_of_prefixInitClauses_sat
    (M := tm.M) (S := tm.S) (pref := pref) (suffix := suffix)
    (output := output) (freeLen := certificateBound)
    (allowed := [some false, some true]) (T := T) tm.supports hsuffixLen
    hτSuffix hfreeSuffix
  let w : List Bool := (List.range certificateBound).map chooseB
  have hpair : pref ++ suffix = tapeSymbols (pairBits x w) := by
    simp [pref, suffix, w, tapeSymbols, pairBits, List.map_append,
      chooseB]
  refine ⟨w, by simp [w], ?_⟩
  simpa [hpair] using hout

lemma generateVerifierCNF_sat_iff_exact_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool) (certificateBound T : ℕ) :
    SAT (generateVerifierCNF tm x certificateBound T) ↔
      ∃ w : List Bool, w.length = certificateBound ∧
        MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
          (tapeSymbols [true]) T := by
  constructor
  · exact generateVerifierCNF_sat_implies_exact_certificate tm x certificateBound T
  · rintro ⟨w, hw, hRun⟩
    have h := generateVerifierCNF_sat_of_exact_certificate tm x w T hRun
    simpa [hw] using h

end NPComplete.CookLevin

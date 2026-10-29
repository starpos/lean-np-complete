module

public import NPComplete.CookLevin.Generate.BoundedSATCore

/-!
# Bounded verifier semantics

The standard bounded CNF is useful only when its models match accepting runs
with certificates no longer than the chosen limit. This module proves both
directions and packages that correspondence as a single satisfiability theorem.
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

lemma generateBoundedVerifierCNF_sat_implies_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T : ℕ)
    (hSat : SAT (generateBoundedVerifierCNF tm x certificateBound T)) :
    ∃ w : List Bool, w.length ≤ certificateBound ∧
      MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
        (tapeSymbols [true]) T := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let output : List (Option Bool) := tapeSymbols [true]
  let W := windowSize shape.length output.length T
  obtain ⟨τ, hτ⟩ := hSat
  have hτBound : ∀ c ∈
      (tableauMachineWithInit tm.M tm.S shape output T
        (boundedPrefixInitClauses tm.S pref certificateBound
          [some false, some true] none W T)).clauses,
      c.Satisfied τ := by
    simpa [generateBoundedVerifierCNF, pref, shape, output, W] using hτ
  refine bounded_sat_implies_certificate_core tm x pref shape output certificateBound T W
    (fun input output T _ initial =>
      tableauMachineWithInit tm.M tm.S input output T initial)
    (boundedPrefixInitClauses tm.S pref certificateBound
      [some false, some true] none W T)
    (fun suffix => prefixInitClauses tm.S pref certificateBound
      [none, some false, some true]
      (windowSize (pref ++ suffix).length output.length T) T)
    τ rfl rfl hτBound ?_ ?_ ?_ ?_
  · intro c hc
    simp only [tableauMachineWithInit, List.mem_append]
    aesop
  · intro i hi
    dsimp [W, shape]
    simp only [List.length_append, List.length_replicate]
    unfold windowSize
    omega
  · intro suffix hsuffix c hc
    have hc' : c ∈
        (tableauMachineWithInit tm.M tm.S shape output T
          (prefixInitClauses tm.S pref certificateBound
            [none, some false, some true] W T)).clauses := by
      simpa [tableauMachineWithInit, shape, output, W, hsuffix] using hc
    simp only [tableauMachineWithInit, List.mem_append] at hc' ⊢
    have hsubset : ∀ d ∈ prefixInitClauses tm.S pref certificateBound
        [none, some false, some true] W T,
        d ∈ boundedPrefixInitClauses tm.S pref certificateBound
          [some false, some true] none W T := by
      intro d hd
      exact prefixInitClauses_mem_boundedPrefixInitClauses rfl hd
    aesop
  · intro suffix hsuffix hτFull hfree
    exact machineOutputs_of_prefixInitClauses_sat
      (M := tm.M) (S := tm.S) (pref := pref) (suffix := suffix)
      (output := output) (freeLen := certificateBound)
      (allowed := [none, some false, some true]) (T := T)
      tm.supports hsuffix hτFull hfree

lemma generateBoundedVerifierCNF_sat_of_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T : ℕ) (w : List Bool)
    (hw : w.length ≤ certificateBound)
    (hRun : MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
      (tapeSymbols [true]) T) :
    SAT (generateBoundedVerifierCNF tm x certificateBound T) := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let suffix : List (Option Bool) := w.map some
  let fullSuffix : List (Option Bool) :=
    suffix ++ List.replicate (certificateBound - w.length) none
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let output : List (Option Bool) := tapeSymbols [true]
  let W := windowSize shape.length output.length T
  have hfullLen : fullSuffix.length = certificateBound := by
    simp [fullSuffix, suffix]
    omega
  have hW : W = windowSize (pref ++ fullSuffix).length output.length T := by
    dsimp [W, shape]
    simp [hfullLen]
  have hspan : T + pref.length + certificateBound + 1 ≤ W := by
    dsimp [W, shape]
    simp only [List.length_append, List.length_replicate]
    unfold windowSize
    omega
  have hInit : ∀ τ : Literal.Assignment,
      (∀ c ∈ (tableauMachine tm.M tm.S (pref ++ fullSuffix) output T).clauses,
        c.Satisfied τ) →
      ∀ c ∈ boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T, c.Satisfied τ := by
    apply bounded_prefix_init_sat_core pref fullSuffix output
      certificateBound T W w
      (fun input output T _ => tableauMachine tm.M tm.S input output T)
      (boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T)
      rfl hfullLen hw
    intro τ hstd hprefix hfree htail hw'
    exact boundedPrefixInitClauses_of_standard_sat
      (M := tm.M) (S := tm.S) (input := pref ++ fullSuffix)
      (pref := pref) (output := output) (freeLen := certificateBound)
      (W := W) (T := T)
      (allowed := [some false, some true]) (blank := none)
      hW hspan hstd hprefix hfree htail
  have hsat := bounded_sat_of_certificate_core tm x pref fullSuffix output
      certificateBound T W w
      (fun input output T _ initial =>
        tableauMachineWithInit tm.M tm.S input output T initial)
      (fun input output T _ => tableauMachine tm.M tm.S input output T)
      (boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T)
      rfl rfl rfl hRun hInit
      (by
        intro hinputRun hInit
        exact tableauMachineWithInit_sat_of_run_of_initial
          (M := tm.M) (S := tm.S) (input := pref ++ fullSuffix)
          (output := output) (T := T)
          (initial := boundedPrefixInitClauses tm.S pref certificateBound
            [some false, some true] none W T)
          tm.supports hinputRun hInit)
  have hshapeLen : (pref ++ fullSuffix).length = shape.length := by
    simp [shape, hfullLen]
  simpa [generateBoundedVerifierCNF, tableauMachineWithInit, pref, shape, output,
    W, hshapeLen] using hsat

lemma generateBoundedVerifierCNF_sat_iff
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T : ℕ) :
    SAT (generateBoundedVerifierCNF tm x certificateBound T) ↔
      ∃ w : List Bool, w.length ≤ certificateBound ∧
        MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
          (tapeSymbols [true]) T := by
  constructor
  · exact generateBoundedVerifierCNF_sat_implies_certificate tm x
      certificateBound T
  · rintro ⟨w, hw, hRun⟩
    exact generateBoundedVerifierCNF_sat_of_certificate tm x
      certificateBound T w hw hRun

end NPComplete.CookLevin

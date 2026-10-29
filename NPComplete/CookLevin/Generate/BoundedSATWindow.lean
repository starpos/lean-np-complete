module

public import NPComplete.CookLevin.Generate.BoundedSAT

/-!
# Explicit-window verifier semantics

A producer may choose a tableau width larger than the canonical minimum while
keeping the same certificate bound. This module proves the satisfiability
correspondence for any admissible supplied width, separating layout choice from
certificate semantics.
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

/-- `generateBoundedVerifierCNF` with the window supplied directly instead of
pinned to the tight `windowSize`, so a producer may lay out a larger grid. -/
noncomputable def generateBoundedVerifierCNFAtWindow (tm : TM0ComputableAux Bool)
    (x : List Bool) (certificateBound T W : ℕ) : CNF :=
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  tableauMachineWithInitAtWindow tm.M tm.S shape (tapeSymbols [true]) T W
    (boundedPrefixInitClauses tm.S pref certificateBound
      [some false, some true] none W T)

lemma execGenerateBoundedVerifierCNFAtWindow_eq (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T W : ℕ) :
    execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W =
    generateBoundedVerifierCNFAtWindow tm.base x certificateBound T W := by
  simp only [execGenerateBoundedVerifierCNFAtWindow, generateBoundedVerifierCNFAtWindow,
    execEncodableTableauMachineWithInitAtWindow, tableauMachineWithInitAtWindow]
  rw [tm.stateList_eq, tm.letterList_eq]
  simp [execUniquenessClauses,
    execInitStateClause, execTransClauses, execTransOne,
    execPersistClauses, execAcceptClauses, execHaltStates,
    execBoundedPrefixInitClauses, uniquenessClauses, initStateClause,
    transClauses, transOne, persistClauses, acceptClauses,
    boundedPrefixInitClauses, stateIdx, letterIdx, letters, haltStates,
    List.map_map, Function.comp_def]
  rfl

/-- `generateBoundedVerifierCNF_sat_implies_certificate` generalized past the
tight window: any `W ≥ windowSize ...` still lets the certificate be read off
a satisfying assignment. -/
lemma generateBoundedVerifierCNFAtWindow_sat_implies_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T W : ℕ)
    (hW : windowSize ((pairBits x []).length + certificateBound)
      (tapeSymbols [true] : List (Option Bool)).length T ≤ W)
    (hSat : SAT (generateBoundedVerifierCNFAtWindow tm x certificateBound T W)) :
    ∃ w : List Bool, w.length ≤ certificateBound ∧
      MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
        (tapeSymbols [true]) T := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let output : List (Option Bool) := tapeSymbols [true]
  have hshapeLen : shape.length = (pairBits x []).length + certificateBound := by
    simp [shape, pref]
  have hW' : windowSize shape.length output.length T ≤ W := by
    rw [hshapeLen]; exact hW
  obtain ⟨τ, hτ⟩ := hSat
  have hτBound : ∀ c ∈
      (tableauMachineWithInitAtWindow tm.M tm.S shape output T W
        (boundedPrefixInitClauses tm.S pref certificateBound
          [some false, some true] none W T)).clauses,
      c.Satisfied τ := by
    simpa [generateBoundedVerifierCNFAtWindow, pref, shape, output] using hτ
  refine bounded_sat_implies_certificate_core tm x pref shape output certificateBound T W
    (fun input output T W initial =>
      tableauMachineWithInitAtWindow tm.M tm.S input output T W initial)
    (boundedPrefixInitClauses tm.S pref certificateBound
      [some false, some true] none W T)
    (fun _ => prefixInitClauses tm.S pref certificateBound
      [none, some false, some true] W T)
    τ rfl rfl hτBound ?_ ?_ ?_ ?_
  · intro c hc
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  · intro i hi
    have hlt : T + pref.length + i < windowSize shape.length output.length T := by
      dsimp [shape]
      simp only [List.length_append, List.length_replicate]
      unfold windowSize
      omega
    exact lt_of_lt_of_le hlt hW'
  · intro suffix hsuffix c hc
    simp only [tableauMachineWithInitAtWindow, List.mem_append] at hc ⊢
    have hsubset : ∀ d ∈ prefixInitClauses tm.S pref certificateBound
        [none, some false, some true] W T,
        d ∈ boundedPrefixInitClauses tm.S pref certificateBound
          [some false, some true] none W T := by
      intro d hd
      exact prefixInitClauses_mem_boundedPrefixInitClauses rfl hd
    aesop
  · intro suffix hsuffix hτFull hfree
    apply machineOutputs_of_prefixInitClauses_at_window_sat
      (M := tm.M) (S := tm.S) (pref := pref) (suffix := suffix)
      (output := output) (freeLen := certificateBound) (W := W)
      (allowed := [none, some false, some true]) (T := T)
      tm.supports ?_ hsuffix hτFull hfree
    have hlen : (pref ++ suffix).length = shape.length := by
      simp [shape, hsuffix]
    rw [hlen]
    exact hW'

/-- `generateBoundedVerifierCNF_sat_of_certificate` generalized past the tight
window: any `W ≥ windowSize ...` still lets a certificate witness a
satisfying assignment. -/
lemma generateBoundedVerifierCNFAtWindow_sat_of_certificate
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T W : ℕ) (w : List Bool)
    (hW : windowSize ((pairBits x []).length + certificateBound)
      (tapeSymbols [true] : List (Option Bool)).length T ≤ W)
    (hw : w.length ≤ certificateBound)
    (hRun : MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
      (tapeSymbols [true]) T) :
    SAT (generateBoundedVerifierCNFAtWindow tm x certificateBound T W) := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let suffix : List (Option Bool) := w.map some
  let fullSuffix : List (Option Bool) :=
    suffix ++ List.replicate (certificateBound - w.length) none
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let output : List (Option Bool) := tapeSymbols [true]
  have hfullLen : fullSuffix.length = certificateBound := by
    simp [fullSuffix, suffix]
    omega
  have hWSpan : windowSize shape.length output.length T ≤ W := by
    have hlen2 : shape.length = (pairBits x []).length + certificateBound := by
      simp [shape, pref]
    rw [hlen2]
    exact hW
  have hWSpan' : windowSize (pref ++ fullSuffix).length output.length T ≤ W := by
    have hlen : (pref ++ fullSuffix).length = shape.length := by
      simp [shape, hfullLen]
    rw [hlen]
    exact hWSpan
  have hspan : T + pref.length + certificateBound + 1 ≤ W := by
    have hlt : T + pref.length + certificateBound + 1 ≤
        windowSize (pref ++ fullSuffix).length output.length T := by
      have hlen : (pref ++ fullSuffix).length = pref.length + fullSuffix.length := by
        simp
      rw [hlen, hfullLen]
      unfold windowSize
      omega
    exact hlt.trans hWSpan'
  have hInit : ∀ τ : Literal.Assignment,
      (∀ c ∈ (tableauMachineAtWindow tm.M tm.S (pref ++ fullSuffix) output T W).clauses,
        c.Satisfied τ) →
      ∀ c ∈ boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T, c.Satisfied τ := by
    apply bounded_prefix_init_sat_core pref fullSuffix output
      certificateBound T W w
      (fun input output T W => tableauMachineAtWindow tm.M tm.S input output T W)
      (boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T)
      rfl hfullLen hw
    intro τ hstd hprefix hfree htail hw'
    exact boundedPrefixInitClauses_of_at_window_sat
      (M := tm.M) (S := tm.S) (input := pref ++ fullSuffix)
      (pref := pref) (output := output) (freeLen := certificateBound)
      (W := W) (T := T)
      (allowed := [some false, some true]) (blank := none)
      hspan hstd hprefix hfree htail
  have hsat := bounded_sat_of_certificate_core tm x pref fullSuffix output
      certificateBound T W w
      (fun input output T W initial =>
        tableauMachineWithInitAtWindow tm.M tm.S input output T W initial)
      (fun input output T W => tableauMachineAtWindow tm.M tm.S input output T W)
      (boundedPrefixInitClauses tm.S pref certificateBound
        [some false, some true] none W T)
      rfl rfl rfl hRun hInit
      (by
        intro hinputRun hInit
        exact tableauMachineWithInitAtWindow_sat_of_run_of_initial
          (M := tm.M) (S := tm.S) (input := pref ++ fullSuffix)
          (output := output) (T := T) (W := W)
          (initial := boundedPrefixInitClauses tm.S pref certificateBound
            [some false, some true] none W T)
          tm.supports hWSpan' hinputRun hInit)
  have hshapeLen : (pref ++ fullSuffix).length = shape.length := by
    simp [shape, hfullLen]
  simpa [generateBoundedVerifierCNFAtWindow, tableauMachineWithInitAtWindow, pref,
    shape, output, hshapeLen] using hsat

/-- `generateBoundedVerifierCNF_sat_iff` generalized past the tight window:
any `W ≥ windowSize ...` gives the same certificate-existence equivalence. -/
lemma generateBoundedVerifierCNFAtWindow_sat_iff
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (certificateBound T W : ℕ)
    (hW : windowSize ((pairBits x []).length + certificateBound)
      (tapeSymbols [true] : List (Option Bool)).length T ≤ W) :
    SAT (generateBoundedVerifierCNFAtWindow tm x certificateBound T W) ↔
      ∃ w : List Bool, w.length ≤ certificateBound ∧
        MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
          (tapeSymbols [true]) T := by
  constructor
  · exact generateBoundedVerifierCNFAtWindow_sat_implies_certificate tm x
      certificateBound T W hW
  · rintro ⟨w, hw, hRun⟩
    exact generateBoundedVerifierCNFAtWindow_sat_of_certificate tm x
      certificateBound T W w hW hw hRun

lemma execCompactGenerateBoundedVerifierCNF_sat_iff
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T : ℕ) :
    SAT (execCompactGenerateBoundedVerifierCNF
      (executableTableauMachineOf tm) x certificateBound T) ↔
      ∃ w : List Bool, w.length ≤ certificateBound ∧
        MachineOutputsInTime tm.base.M (tapeSymbols (pairBits x w))
          (tapeSymbols [true]) T := by
  unfold execCompactGenerateBoundedVerifierCNF
  rw [compactCNF_sat_iff]
  rw [execPairGenerateBoundedVerifierCNF_sat_iff]
  rw [execGenerateBoundedVerifierCNF_eq]
  exact generateBoundedVerifierCNF_sat_iff tm.base x certificateBound T

lemma semanticCompactGenerateBoundedVerifierCNF_sat_iff
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T : ℕ) :
    SAT (semanticCompactGenerateBoundedVerifierCNF tm x certificateBound T) ↔
      ∃ w : List Bool, w.length ≤ certificateBound ∧
        MachineOutputsInTime tm.base.M (tapeSymbols (pairBits x w))
          (tapeSymbols [true]) T := by
  unfold semanticCompactGenerateBoundedVerifierCNF
  rw [compactCNF_sat_iff, execGenerateBoundedVerifierCNF_eq]
  exact generateBoundedVerifierCNF_sat_iff tm.base x certificateBound T

end NPComplete.CookLevin

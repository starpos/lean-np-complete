module

public import NPComplete.CookLevin.Generate.ExecCompiler

/-!
# Verifier tableau generators

The reduction needs a common representation for an input-only computation and
for one with a free certificate suffix. This module defines those tableau CNFs
and the acceptance predicate, leaving model-to-run arguments to correctness
modules.
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

/-! ## Generator surface -/

/-- Tableau for a verifier with a fixed instance prefix and a free certificate
suffix of the prescribed length. -/
noncomputable def generateVerifierCNF (tm : TM0ComputableAux Bool)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  let pref : List (Option Bool) := (pairBits x []).map some
  let output : List (Option Bool) := tapeSymbols [true]
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length output.length T
  tableauMachineWithInit tm.M tm.S shape output T
    (prefixInitClauses tm.S pref certificateBound
      [some false, some true] W T)

/-- Tableau for a verifier with a bounded, blank-terminated certificate.

The certificate cells may contain either Boolean symbol or `none`; the
no-hole clauses in `boundedPrefixInitClauses` force all cells after the first
blank to remain blank. -/
noncomputable def generateBoundedVerifierCNF (tm : TM0ComputableAux Bool)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length (tapeSymbols [true]).length T
  tableauMachineWithInit tm.M tm.S shape (tapeSymbols [true]) T
    (boundedPrefixInitClauses tm.S pref certificateBound
      [some false, some true] none W T)

lemma execGenerateBoundedVerifierCNF_eq (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T : ℕ) :
    execGenerateBoundedVerifierCNF tm x certificateBound T =
    generateBoundedVerifierCNF tm.base x certificateBound T := by
  simp only [execGenerateBoundedVerifierCNF, generateBoundedVerifierCNF]
  rw [tm.stateList_eq, tm.letterList_eq]
  simp [execTableauMachineWithInit, tableauMachineWithInit,
    execUniquenessClauses,
    execInitStateClause, execTransClauses, execTransOne,
    execPersistClauses, execAcceptClauses, execHaltStates,
    execBoundedPrefixInitClauses, uniquenessClauses, initStateClause,
    transClauses, transOne, persistClauses, acceptClauses,
    boundedPrefixInitClauses, stateIdx, letterIdx, letters, haltStates,
    List.map_map, Function.comp_def]
  rfl

/-- `execGenerateBoundedVerifierCNF` with the window supplied directly instead
of pinned to the tight `windowSize`. -/
def execGenerateBoundedVerifierCNFAtWindow (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T W : ℕ) : CNF :=
  letI : Inhabited tm.base.Λ := tm.base.ΛInhabited
  letI : DecidableEq tm.base.Λ := tm.base.ΛDecidableEq
  let pref : List (Option Bool) := (pairBits x []).map some
  execEncodableTableauMachineWithInitAtWindow tm.base.M tm.stateList tm.letterList
    (tapeSymbols [true]) T W
    (execBoundedPrefixInitClauses tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T)

end NPComplete.CookLevin

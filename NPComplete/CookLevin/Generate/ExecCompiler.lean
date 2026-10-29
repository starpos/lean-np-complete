module

public import NPComplete.CookLevin.Generate.EncodeLength

/-!
# Executable tableau compiler

The semantic tableau uses finite-set enumerations and generic indices, while an
executable reduction needs explicit lists and computable variable indices. This
module defines that list-based compiler and carries the enumeration evidence
needed to compare its output with the semantic construction.
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

/-! ## Executable generator surface -/

/-!
`TM0ComputableAux` expresses state support as a `Finset`, while the list-based
tableau compiler needs explicit enumerations.  This wrapper carries the state
and letter lists, with their nodup and completeness properties and their
equality to the `Finset` enumerations, alongside the semantic machine.
-/
structure ExecutableTableauAux where
  base : TM0ComputableAux Bool
  stateList : List base.Λ
  stateList_eq : stateList = base.S.toList
  stateList_nodup : stateList.Nodup
  stateList_complete : ∀ q, q ∈ stateList ↔ q ∈ base.S
  letterList : List (Option Bool)
  letterList_eq : letterList = letters (Option Bool)
  letterList_nodup : letterList.Nodup
  letterList_complete : ∀ a, a ∈ letterList ↔ a ∈ (Finset.univ : Finset (Option Bool))

noncomputable def executableTableauAuxOf (tm : TM0ComputableAux Bool) :
    ExecutableTableauAux where
  base := tm
  stateList := tm.S.toList
  stateList_eq := rfl
  stateList_nodup := Finset.nodup_toList tm.S
  stateList_complete := by simp
  letterList := letters (Option Bool)
  letterList_eq := rfl
  letterList_nodup := Finset.nodup_toList Finset.univ
  letterList_complete := by
    intro a
    simp [letters]

def execStateIdx {Λ : Type} [DecidableEq Λ] (S : List Λ) (q : Λ) : ℕ := S.idxOf q

def execLetterIdx {Δ : Type} [DecidableEq Δ] (A : List Δ) (a : Δ) : ℕ := A.idxOf a

def execUniquenessClauses (stateVars letterVars : List ℕ) (W T : ℕ) : List Clause :=
  (List.range (T + 1)).flatMap fun t =>
    exactlyOne (stateVars.map fun q => stateVar t q) ++
      exactlyOne ((List.range W).map fun p => headVar t p) ++
        (List.range W).flatMap fun p =>
          exactlyOne (letterVars.map fun a => cellVar t p a)

def execInitStateClause {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (S : List Λ) : Clause :=
  if default ∈ S then unitPos (stateVar 0 (execStateIdx S default)) else ⟨[]⟩

def execTransOne {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W t p : ℕ) (q : Λ) (a : Δ) : List Clause :=
  let st := stateVar t (execStateIdx S q)
  let hd := headVar t p
  let cl := cellVar t p (execLetterIdx A a)
  match M q a with
  | none =>
      [imply3 st hd cl (stateVar (t + 1) (execStateIdx S q)),
        imply3 st hd cl (headVar (t + 1) p),
        imply3 st hd cl (cellVar (t + 1) p (execLetterIdx A a))]
  | some (q', stmt) =>
      if q' ∈ S then
        match stmt with
        | .write b =>
            [imply3 st hd cl (stateVar (t + 1) (execStateIdx S q')),
              imply3 st hd cl (headVar (t + 1) p),
              imply3 st hd cl (cellVar (t + 1) p (execLetterIdx A b))]
        | .move d =>
            match nextIdx W p d with
            | none => [forbid3 st hd cl]
            | some p' =>
                [imply3 st hd cl (stateVar (t + 1) (execStateIdx S q')),
                  imply3 st hd cl (headVar (t + 1) p'),
                  imply3 st hd cl (cellVar (t + 1) p (execLetterIdx A a))]
      else
        [forbid3 st hd cl]

def execTransClauses {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ) (W T : ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun p =>
      S.flatMap fun q => A.flatMap fun a => execTransOne M S A W t p q a

def execPersistClauses (letterVars : List ℕ) (W T : ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else letterVars.map fun a =>
          imply2 (headVar t pHead) (cellVar t pCell a)
            (cellVar (t + 1) pCell a)

def execHaltStates {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Λ] (M : Machine Δ Λ) (S : List Λ) (a : Δ) : List Λ :=
  S.filter fun q =>
    match M q a with
    | none => true
    | some _ => false

def execAcceptClauses {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (W T : ℕ) : List Clause :=
  ((List.range W).flatMap fun pHead =>
      (List.range W).map fun p =>
        implyPos (headVar T pHead)
          (cellVar T p (execLetterIdx A
            (initSymbol output ((p : ℤ) - (pHead : ℤ)))))) ++
    [atLeastOne ((execHaltStates M S (initSymbol output 0)).map fun q =>
      stateVar T (execStateIdx S q))]

def execBoundedPrefixInitClauses {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (S : List Λ) (A : List Δ) (pref : List Δ)
    (freeLen : ℕ) (allowed : List Δ) (blank : Δ) (W T : ℕ) : List Clause :=
  (execInitStateClause S ::
      unitPos (headVar 0 (originIdx T)) ::
        (List.range W).map fun p =>
          if p < T + pref.length then
            unitPos (cellVar 0 p (execLetterIdx A (initSymbol pref (idxToPos T p))))
          else if p < T + pref.length + freeLen then
            atLeastOne ((blank :: allowed).map fun a =>
              cellVar 0 p (execLetterIdx A a))
          else
            unitPos (cellVar 0 p (execLetterIdx A blank))) ++
    (List.range freeLen).map fun i =>
      implyPos
        (cellVar 0 (T + pref.length + i) (execLetterIdx A blank))
        (cellVar 0 (T + pref.length + i + 1) (execLetterIdx A blank))

def execTableauMachineWithInit {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (input output : List Δ) (T : ℕ) (initial : List Clause) : CNF :=
  let W := windowSize input.length output.length T
  ⟨execUniquenessClauses (S.map (execStateIdx S))
      (A.map (execLetterIdx A)) W T ++
      initial ++
        execTransClauses M S A W T ++
          execPersistClauses (A.map (execLetterIdx A)) W T ++
            execAcceptClauses M S A output W T⟩

/-- The Encodable-numbered encoding underlying `execTableauMachineWithInit`,
with the window supplied directly instead of pinned to
`windowSize input.length output.length T`. -/
def execEncodableTableauMachineWithInitAtWindow {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (T W : ℕ) (initial : List Clause) : CNF :=
  ⟨execUniquenessClauses (S.map (execStateIdx S))
      (A.map (execLetterIdx A)) W T ++
      initial ++
        execTransClauses M S A W T ++
          execPersistClauses (A.map (execLetterIdx A)) W T ++
            execAcceptClauses M S A output W T⟩

def execGenerateBoundedVerifierCNF (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  letI : Inhabited tm.base.Λ := tm.base.ΛInhabited
  letI : DecidableEq tm.base.Λ := tm.base.ΛDecidableEq
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length (tapeSymbols [true]).length T
  execTableauMachineWithInit tm.base.M tm.stateList tm.letterList shape
    (tapeSymbols [true]) T
    (execBoundedPrefixInitClauses tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T)

end NPComplete.CookLevin

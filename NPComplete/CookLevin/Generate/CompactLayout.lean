module

public import NPComplete.CookLevin.Generate.VerifierCNF

/-!
# Executable Tableau Layout

The runtime compiler needs variable numbers that do not depend on a classical finite-set enumeration.
This module gives the executable tableau path an arithmetic pairing-and-residue layout, with a
window-parametric form so callers can choose a wider grid without changing the clauses.
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

/-! ## Fully executable compact variable layout

`execCompactLayout` uses `Nat.pair` for tuple indices and disjoint residue
classes for state, head, and cell variables.  This arithmetic numbering makes
the compiler's runtime layout independent of classical `Encodable` enumeration. -/
def execPair (a b : ℕ) : ℕ := Nat.pair a b

lemma execPair_injective :
    Function.Injective (fun x : ℕ × ℕ => execPair x.1 x.2) := by
  intro x y h
  have hp : Nat.pair x.1 x.2 = Nat.pair y.1 y.2 := by
    simpa [execPair] using h
  have he : Nat.pairEquiv x = Nat.pairEquiv y := by
    rw [Nat.pairEquiv_apply]
    exact hp
  exact Nat.pairEquiv.injective he

lemma execPair_inj {a b c d : ℕ} (h : execPair a b = execPair c d) :
    a = c ∧ b = d := by
  have h' : (a, b) = (c, d) := execPair_injective h
  exact Prod.ext_iff.mp h'

structure ExecVarLayout where
  state : ℕ → ℕ → ℕ
  head : ℕ → ℕ → ℕ
  cell : ℕ → ℕ → ℕ → ℕ

def execCompactLayout : ExecVarLayout where
  state t q := 3 * execPair t q + 1
  head t p := 3 * execPair t p + 2
  cell t p a := 3 * execPair (execPair t p) a

lemma execCompactLayout_cell_injective :
    Function.Injective
      (fun x : ℕ × ℕ × ℕ =>
        execCompactLayout.cell x.1 x.2.1 x.2.2) := by
  intro ⟨t₁, p₁, a₁⟩ ⟨t₂, p₂, a₂⟩ h
  have hpair : execPair (execPair t₁ p₁) a₁ =
      execPair (execPair t₂ p₂) a₂ := by
    have := congrArg (fun n => n / 3) h
    simpa [execCompactLayout, div3_mul3] using this
  have houter := execPair_inj hpair
  have hinner := execPair_inj houter.1
  exact Prod.ext hinner.1 (Prod.ext hinner.2 houter.2)

lemma execCompactLayout_state_injective :
    Function.Injective
      (fun x : ℕ × ℕ => execCompactLayout.state x.1 x.2) := by
  intro ⟨t₁, q₁⟩ ⟨t₂, q₂⟩ h
  have hpair : execPair t₁ q₁ = execPair t₂ q₂ := by
    have := congrArg (fun n => n / 3) h
    simpa [execCompactLayout, div3_mul3_add1] using this
  exact execPair_injective hpair

lemma execCompactLayout_head_injective :
    Function.Injective
      (fun x : ℕ × ℕ => execCompactLayout.head x.1 x.2) := by
  intro ⟨t₁, p₁⟩ ⟨t₂, p₂⟩ h
  have hpair : execPair t₁ p₁ = execPair t₂ p₂ := by
    have := congrArg (fun n => n / 3) h
    simpa [execCompactLayout, div3_mul3_add2] using this
  exact execPair_injective hpair

lemma execCompactLayout_cell_ne_state (t p a t' q : ℕ) :
    execCompactLayout.cell t p a ≠ execCompactLayout.state t' q := by
  intro h
  have := congrArg (fun n => n % 3) h
  simp [execCompactLayout] at this

lemma execCompactLayout_cell_ne_head (t p a t' p' : ℕ) :
    execCompactLayout.cell t p a ≠ execCompactLayout.head t' p' := by
  intro h
  have := congrArg (fun n => n % 3) h
  simp [execCompactLayout] at this

lemma execCompactLayout_state_ne_head (t q t' p : ℕ) :
    execCompactLayout.state t q ≠ execCompactLayout.head t' p := by
  intro h
  have := congrArg (fun n => n % 3) h
  simp [execCompactLayout] at this

/-!
`ExecutableTableauMachine` is the data-only compiler input: it stores the
machine and explicit state and letter lists, without a `Finset` support field
or proof fields in its runtime record.
-/
structure ExecutableTableauMachine where
  Λ : Type
  [ΛInhabited : Inhabited Λ]
  [ΛDecidableEq : DecidableEq Λ]
  M : Machine (Option Bool) Λ
  stateList : List Λ
  letterList : List (Option Bool)

attribute [instance] ExecutableTableauMachine.ΛInhabited
  ExecutableTableauMachine.ΛDecidableEq

def execUniquenessClausesAt (v : ExecVarLayout) (S A : List ℕ) (W T : ℕ) : List Clause :=
  (List.range (T + 1)).flatMap fun t =>
    exactlyOne (S.map fun q => v.state t q) ++
      exactlyOne ((List.range W).map fun p => v.head t p) ++
        (List.range W).flatMap fun p =>
          exactlyOne (A.map fun a => v.cell t p a)

def execInitStateClauseAt (v : ExecVarLayout) {Λ : Type}
    [Inhabited Λ] [DecidableEq Λ] (S : List Λ) : Clause :=
  if default ∈ S then unitPos (v.state 0 (S.idxOf default)) else ⟨[]⟩

def execTransOneAt {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W t p : ℕ) (q : Λ) (a : Δ) : List Clause :=
  let st := v.state t (S.idxOf q)
  let hd := v.head t p
  let cl := v.cell t p (A.idxOf a)
  match M q a with
  | none =>
      [imply3 st hd cl (v.state (t + 1) (S.idxOf q)),
        imply3 st hd cl (v.head (t + 1) p),
        imply3 st hd cl (v.cell (t + 1) p (A.idxOf a))]
  | some (q', stmt) =>
      if q' ∈ S then
        match stmt with
        | .write b =>
            [imply3 st hd cl (v.state (t + 1) (S.idxOf q')),
              imply3 st hd cl (v.head (t + 1) p),
              imply3 st hd cl (v.cell (t + 1) p (A.idxOf b))]
        | .move d =>
            match nextIdx W p d with
            | none => [forbid3 st hd cl]
            | some p' =>
                [imply3 st hd cl (v.state (t + 1) (S.idxOf q')),
                  imply3 st hd cl (v.head (t + 1) p'),
                  imply3 st hd cl (v.cell (t + 1) p (A.idxOf a))]
      else [forbid3 st hd cl]

def execTransClausesAt {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W T : ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun p =>
      S.flatMap fun q => A.flatMap fun a => execTransOneAt v M S A W t p q a

def execPersistClausesAt (v : ExecVarLayout) (A : List ℕ) (W T : ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else A.map fun a =>
          imply2 (v.head t pHead) (v.cell t pCell a) (v.cell (t + 1) pCell a)

def execAcceptClausesAt {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (W T : ℕ) : List Clause :=
  ((List.range W).flatMap fun pHead =>
      (List.range W).map fun p =>
        implyPos (v.head T pHead)
          (v.cell T p (A.idxOf (initSymbol output ((p : ℤ) - (pHead : ℤ)))))) ++
    [atLeastOne ((execHaltStates M S (initSymbol output 0)).map
      (fun q => v.state T (S.idxOf q)))]

def execBoundedPrefixInitClausesAt {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (S : List Λ) (A : List Δ) (pref : List Δ)
    (freeLen : ℕ) (allowed : List Δ) (blank : Δ) (W T : ℕ) : List Clause :=
  (execInitStateClauseAt v S ::
      unitPos (v.head 0 (originIdx T)) ::
        (List.range W).map fun p =>
          if p < T + pref.length then
            unitPos (v.cell 0 p (A.idxOf (initSymbol pref (idxToPos T p))))
          else if p < T + pref.length + freeLen then
            atLeastOne ((blank :: allowed).map fun a => v.cell 0 p (A.idxOf a))
          else unitPos (v.cell 0 p (A.idxOf blank))) ++
    (List.range freeLen).map fun i =>
      implyPos (v.cell 0 (T + pref.length + i) (A.idxOf blank))
        (v.cell 0 (T + pref.length + i + 1) (A.idxOf blank))

def execTableauMachineWithInitAt {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (input output : List Δ) (T : ℕ) (initial : List Clause) : CNF :=
  let W := windowSize input.length output.length T
  ⟨execUniquenessClausesAt v (S.map fun q => S.idxOf q)
      (A.map fun a => A.idxOf a) W T ++ initial ++
      execTransClausesAt v M S A W T ++
      execPersistClausesAt v (A.map fun a => A.idxOf a) W T ++
      execAcceptClausesAt v M S A output W T⟩

/-- `execTableauMachineWithInitAt` with the window supplied directly instead
of pinned to `windowSize input.length output.length T`, so a caller can lay
out a larger rectangular grid while keeping the same local clauses. -/
def execTableauMachineWithInitAtWindow {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (T W : ℕ) (initial : List Clause) : CNF :=
  ⟨execUniquenessClausesAt v (S.map fun q => S.idxOf q)
      (A.map fun a => A.idxOf a) W T ++ initial ++
      execTransClausesAt v M S A W T ++
      execPersistClausesAt v (A.map fun a => A.idxOf a) W T ++
      execAcceptClausesAt v M S A output W T⟩

def execPairGenerateBoundedVerifierCNF (tm : ExecutableTableauMachine)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  let v := execCompactLayout
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length (tapeSymbols [true]).length T
  execTableauMachineWithInitAt v tm.M tm.stateList tm.letterList shape
    (tapeSymbols [true]) T
    (execBoundedPrefixInitClausesAt v tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T)

/-- `execPairGenerateBoundedVerifierCNF` with the window supplied directly
instead of pinned to the tight `windowSize`. -/
def execPairGenerateBoundedVerifierCNFAtWindow (tm : ExecutableTableauMachine)
    (x : List Bool) (certificateBound T W : ℕ) : CNF :=
  let v := execCompactLayout
  let pref : List (Option Bool) := (pairBits x []).map some
  execTableauMachineWithInitAtWindow v tm.M tm.stateList tm.letterList
    (tapeSymbols [true]) T W
    (execBoundedPrefixInitClausesAt v tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T)

/-!
The semantic compact compiler is the executable list compiler followed by the
first-occurrence renaming from `compactCNF`.  This is the canonical
assignment-transport implementation: `compactCNF_sat_iff` supplies both
directions without any finite-choice enumeration.
-/
def semanticCompactGenerateBoundedVerifierCNF (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  compactCNF (execGenerateBoundedVerifierCNF tm x certificateBound T)

def execCompactGenerateBoundedVerifierCNF (tm : ExecutableTableauMachine)
    (x : List Bool) (certificateBound T : ℕ) : CNF :=
  compactCNF (execPairGenerateBoundedVerifierCNF tm x certificateBound T)

end NPComplete.CookLevin

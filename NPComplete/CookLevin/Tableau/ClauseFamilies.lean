module

public import NPComplete.CookLevin.Tableau.InitialSnapshot

/-!
# Tableau clause families

The tableau CNF is the concatenation of a few clause families: uniqueness of the state, head, and
cell selectors, the initial row, local transitions, persistence of untouched cells, and acceptance.
Defining them together, over one variable layout and with the shared window helper `nextIdx`, gives
the correctness proofs a single definition of the CNF to reason about.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Clause families -/

def nextIdx (W p : ℕ) : Dir → Option ℕ
  | .left => if p = 0 then none else some (p - 1)
  | .right => if p + 1 < W then some (p + 1) else none

noncomputable def uniquenessClauses [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ]
    (S : Finset Λ) (W T : ℕ) : List Clause :=
  (List.range (T + 1)).flatMap fun t =>
    exactlyOne (S.toList.map fun q => stateVar t (stateIdx S q)) ++
      exactlyOne ((List.range W).map fun p => headVar t p) ++
        (List.range W).flatMap fun p =>
          exactlyOne ((letters Γ).map fun a => cellVar t p (letterIdx a))

noncomputable def initStateClause [Inhabited Λ] [DecidableEq Λ] (S : Finset Λ) :
    Clause :=
  if default ∈ S then unitPos (stateVar 0 (stateIdx S default)) else ⟨[]⟩

noncomputable def initClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (S : Finset Λ) (input : List Γ) (W T : ℕ) :
    List Clause :=
  initStateClause S ::
    unitPos (headVar 0 (originIdx T)) ::
      (List.range W).map fun p =>
        unitPos (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p))))

noncomputable def transOne [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [DecidableEq Γ]
    [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ) (W t p : ℕ) (q : Λ)
    (a : Γ) : List Clause :=
  let st := stateVar t (stateIdx S q)
  let hd := headVar t p
  let cl := cellVar t p (letterIdx a)
  match M q a with
  | none =>
      [imply3 st hd cl (stateVar (t + 1) (stateIdx S q)),
        imply3 st hd cl (headVar (t + 1) p),
        imply3 st hd cl (cellVar (t + 1) p (letterIdx a))]
  | some (q', stmt) =>
      if q' ∈ S then
        match stmt with
        | .write b =>
            [imply3 st hd cl (stateVar (t + 1) (stateIdx S q')),
              imply3 st hd cl (headVar (t + 1) p),
              imply3 st hd cl (cellVar (t + 1) p (letterIdx b))]
        | .move d =>
            match nextIdx W p d with
            | none => [forbid3 st hd cl]
            | some p' =>
                [imply3 st hd cl (stateVar (t + 1) (stateIdx S q')),
                  imply3 st hd cl (headVar (t + 1) p'),
                  imply3 st hd cl (cellVar (t + 1) p (letterIdx a))]
      else
        [forbid3 st hd cl]

noncomputable def transClauses [Inhabited Γ] [Inhabited Λ] [Fintype Γ]
    [DecidableEq Γ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (W T : ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun p =>
      S.toList.flatMap fun q =>
        (letters Γ).flatMap fun a => transOne M S W t p q a

noncomputable def persistClauses [Fintype Γ] [DecidableEq Γ] (W T : ℕ) :
    List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else
          (letters Γ).map fun a =>
            imply2 (headVar t pHead) (cellVar t pCell (letterIdx a))
              (cellVar (t + 1) pCell (letterIdx a))

noncomputable def haltStates [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset Λ) (a : Γ) : List Λ :=
  S.toList.filter fun q =>
    match M q a with
    | none => true
    | some _ => false

/-- Accept clauses, phrased relative to wherever the head actually stops.

`MachineOutputsInTime` only records the halting *tape value* (`Turing.Tape`
has no absolute position), so it can't distinguish "head at 0" from "head
drifted to `h` but the tape still reads `Tape.mk₁ output`". Pinning the
accept clauses to `headVar T (originIdx T)` is a strictly stronger
requirement and makes `MachineOutputsInTime ⟹ SAT` false in general.

Instead, for every candidate head window index `pHead`, an implication says
what the tape must look like *relative to that head*: the cell at window
index `p` must read `output`'s symbol at offset `p - pHead`. Since
`initSymbol` already returns `default` outside `[0, output.length)`, this one
family also expresses "everything left of the head, and past the end of
`output`, is blank" — no separate clause is needed for that. Exactly one
`headVar T pHead` holds (`uniquenessClauses`), so this pins down the same
single tape shape that a fixed origin would, just without assuming which
window index the head lands on. -/
noncomputable def acceptClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (output : List Γ) (W T : ℕ) : List Clause :=
  ((List.range W).flatMap fun pHead =>
      (List.range W).map fun p =>
        implyPos (headVar T pHead)
          (cellVar T p (letterIdx (initSymbol output ((p : ℤ) - (pHead : ℤ)))))) ++
    [atLeastOne
        ((haltStates M S (initSymbol output 0)).map fun q =>
          stateVar T (stateIdx S q))]

end NPComplete.CookLevin

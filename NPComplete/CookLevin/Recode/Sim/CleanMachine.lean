module

public import NPComplete.CookLevin.Recode.Sim.Machine

/-! Markers distinguish the simulator's growing left history from the blank
boundary.  Removing that history after the source halts preserves its output
while leaving the head in a canonical position. -/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

inductive SimCleanPhase (n : ℕ) (Λ : Type)
  | run (p : SimPhase n Λ)
  | markMove (p : SimPhase n Λ) (d : Dir)
  | returnMarker
  | rewindLeft
  | eraseLeft
  | eraseLeftMove
  | final
  deriving DecidableEq

instance {n : ℕ} {Λ : Type} [Inhabited Λ] : Inhabited (SimCleanPhase n Λ) :=
  ⟨SimCleanPhase.run default⟩

/-! A visited block is given a physical marker in its first cell. When the cell is blank,
`simMarkCell` replaces it with `some false`; existing `some _` cells are preserved.
The marker is observationally equal to a blank cell for `BlockEnc`; this lets cleanup
distinguish visited history from the true blank boundary without changing the simulated
source symbol. -/

def simMarkCell (x : Option Bool) : Option Bool :=
  if x.isSome then x else some false

lemma simMarkCell_getD (x : Option Bool) :
    (simMarkCell x).getD false = x.getD false := by
  cases x <;> simp [simMarkCell]

noncomputable def simCleanMachine {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ) :
    TM0.Machine (Option Bool) (SimCleanPhase e.n Λ) :=
  fun phase cell =>
    match phase with
    | SimCleanPhase.run p =>
        match simMachine M e p cell with
        | none =>
            some (SimCleanPhase.rewindLeft,
              TM0.Stmt.write cell)
        | some (p', TM0.Stmt.move d) =>
            match p with
            | SimPhase.read _ _ _ =>
                some (SimCleanPhase.markMove p' d, TM0.Stmt.write (simMarkCell cell))
            | _ => some (SimCleanPhase.run p', TM0.Stmt.move d)
        | some (p', TM0.Stmt.write x) =>
            some (SimCleanPhase.run p', TM0.Stmt.write (simMarkCell x))
    | SimCleanPhase.markMove p d =>
        some (SimCleanPhase.run p, TM0.Stmt.move d)
    | SimCleanPhase.returnMarker =>
        if cell.isSome then
          some (SimCleanPhase.final,
            TM0.Stmt.write cell)
        else
          some (SimCleanPhase.returnMarker, TM0.Stmt.move Dir.right)
    | SimCleanPhase.rewindLeft =>
        if cell.isSome then
          some (SimCleanPhase.eraseLeft, TM0.Stmt.move Dir.left)
        else
          some (SimCleanPhase.returnMarker, TM0.Stmt.move Dir.right)
    | SimCleanPhase.eraseLeft =>
        if cell.isSome then
          some (SimCleanPhase.eraseLeftMove, TM0.Stmt.write none)
        else
          some (SimCleanPhase.returnMarker, TM0.Stmt.move Dir.right)
    | SimCleanPhase.eraseLeftMove =>
        some (SimCleanPhase.eraseLeft, TM0.Stmt.move Dir.left)
    | SimCleanPhase.final => none


end NPComplete.CookLevin

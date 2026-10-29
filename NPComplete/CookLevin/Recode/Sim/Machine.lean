module

public import NPComplete.CookLevin.Recode.Sim.Foundation

/-!
# Fixed-width block machine

A finite-alphabet tape machine can run over a Boolean tape by storing each symbol
in a fixed-width block and expanding each transition into scan, rewind, and write
phases. This module defines the bounded phase state and the machine whose
behavior the surrounding proofs establish.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

/-- Phase of the block simulator. Every list is replaced by a `Fin`-index
    into a block so the reachable fragment is finite when `Λ` is. -/
inductive SimPhase (n : ℕ) (Λ : Type)
  | ready (q : Λ)
  | read (q : Λ) (i : Fin n.succ) (acc : List.Vector Bool i.val)
  | rewind (q : Λ) (left : Fin n.succ) (bits : List.Vector Bool n)
  | write (q' : Λ) (i : Fin n.succ) (bits : List.Vector Bool n)
  | writeMove (q' : Λ) (i : Fin n.succ) (bits : List.Vector Bool n)
  | writeBack (q' : Λ) (left : Fin n.succ)
  | move (q' : Λ) (d : Dir) (left : Fin n.succ)
  | done
  deriving DecidableEq

instance {n : ℕ} {Λ : Type} [Inhabited Λ] : Inhabited (SimPhase n Λ) :=
  ⟨SimPhase.ready default⟩

/-- One TM0 step of `M` becomes a bounded scan / write / move over a block. -/
noncomputable def simMachine {Γ Λ : Type} [Inhabited Γ] [Finite Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (e : BlockEnc Γ) :
    TM0.Machine (Option Bool) (SimPhase e.n Λ) :=
  fun phase cell =>
    match phase with
    | SimPhase.ready q =>
        if h : 0 < e.n.succ then
          some (SimPhase.read q ⟨0, h⟩ .nil, TM0.Stmt.write cell)
        else
          some (SimPhase.done, TM0.Stmt.write cell)
    | SimPhase.read q i acc =>
        let b := Option.getD cell false
        if h : i.val + 1 < e.n.succ then
          some (SimPhase.read q ⟨i.val + 1, h⟩ (acc.cons b), TM0.Stmt.move Dir.right)
        else
          if hb : i.val = e.n then
            let bits : List.Vector Bool e.n :=
              ⟨acc.toList.reverse, by
                simp [List.length_reverse, List.Vector.toList_length, hb]⟩
            some (SimPhase.rewind q ⟨i.val, by omega⟩ bits, TM0.Stmt.write cell)
          else
            some (SimPhase.done, TM0.Stmt.write cell)
    | SimPhase.rewind q left bits =>
        if h : 0 < left.val then
          some (SimPhase.rewind q ⟨left.val - 1, by omega⟩
            bits, TM0.Stmt.move Dir.left)
        else
          match M q (e.dec bits) with
          | none => some (SimPhase.done, TM0.Stmt.write cell)
          | some (q', TM0.Stmt.write s) =>
              if hz : 0 < e.n.succ then
                some (SimPhase.write q' ⟨0, hz⟩ (e.enc s), TM0.Stmt.write cell)
              else
                some (SimPhase.done, TM0.Stmt.write cell)
          | some (q', TM0.Stmt.move d) =>
              if hz : 0 < e.n.succ then
                some (SimPhase.move q' d ⟨e.n, Nat.lt_succ_self _⟩, TM0.Stmt.write cell)
              else
                some (SimPhase.done, TM0.Stmt.write cell)
    | SimPhase.write q' i bits =>
        if h : i.val < e.n then
          let bit := bits.get ⟨i.val, h⟩
          some (SimPhase.writeMove q' i bits, TM0.Stmt.write (some bit))
        else
          some (SimPhase.ready q', TM0.Stmt.write cell)
    | SimPhase.writeMove q' i bits =>
        if hi : i.val < e.n then
          if h : i.val + 1 < e.n then
            some (SimPhase.write q' ⟨i.val + 1, by omega⟩ bits,
              TM0.Stmt.move Dir.right)
          else
            some (SimPhase.writeBack q' ⟨e.n, Nat.lt_succ_self _⟩,
              TM0.Stmt.move Dir.right)
        else
          some (SimPhase.ready q', TM0.Stmt.write cell)
    | SimPhase.writeBack q' left =>
        if h : 0 < left.val then
          some (SimPhase.writeBack q' ⟨left.val - 1, by omega⟩, TM0.Stmt.move Dir.left)
        else
          some (SimPhase.ready q', TM0.Stmt.write cell)
    | SimPhase.move q' d left =>
        if h : 0 < left.val then
          some (SimPhase.move q' d ⟨left.val - 1, by omega⟩,
            TM0.Stmt.move d)
        else
          some (SimPhase.ready q', TM0.Stmt.write cell)
    | SimPhase.done => none


end NPComplete.CookLevin

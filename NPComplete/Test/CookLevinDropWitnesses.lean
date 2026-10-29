module

public import NPComplete.CookLevin.Machines.PackedOutputDecode

/-!
These counterexamples document that tail occupancy is weaker than full-block
marking. They remain outside the consumer-facing umbrella because no main
construction requires them.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

def partialBlockCounterexampleEncEnc (b : Bool) : List.Vector Bool 2 :=
  if b then ⟨[true, false], by simp⟩ else ⟨[false, false], by simp⟩

def partialBlockCounterexampleDec (v : List.Vector Bool 2) : Bool :=
  v.toList[0]'(by simp [List.Vector.toList_length])

noncomputable def partialBlockCounterexampleEnc : BlockEnc Bool where
  n := 2
  enc := partialBlockCounterexampleEncEnc
  dec := partialBlockCounterexampleDec
  enc_default := by
    apply List.Vector.eq
    simp [partialBlockCounterexampleEncEnc]
  dec_enc := by
    intro b
    cases b <;> rfl

lemma rawTailOccupied_does_not_imply_full_block :
    BlockDecodes partialBlockCounterexampleEnc [some true, none] true ∧
    SimCleanTailOccupied (ListBlank.mk [some true, none]) ∧
    ¬ BlockMarked [some true, none] := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [partialBlockCounterexampleEnc], ?_⟩
    change partialBlockCounterexampleDec ⟨[true, false], by simp⟩ = true
    rfl
  · refine ⟨[some true], ?_, ?_⟩
    · apply Quotient.sound
      exact Or.inr ⟨1, by simp [default]⟩
    · intro x hx
      simp at hx
      subst x
      simp
  · intro h
    have hh := h none (by simp)
    simp at hh

end NPComplete.CookLevin

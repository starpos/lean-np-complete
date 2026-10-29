module

public import NPComplete.CookLevin.Tableau.TableauVarRange

/-!
# Descriptor ABI premises

The generic reduction generator requires descriptor entries and distinguished symbols to remain
within their encoded ranges. This module proves those descriptor-specific premises so the ABI
construction can consume them without reopening the tableau encoding.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing.TM0

lemma descriptorOf_abi_write {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool)) :
    ∀ qi ai qi' bi, (descriptorOf M S A).entry qi ai = .write qi' bi →
      bi < (descriptorOf M S A).numLetters + 1 := by
  intro qi ai qi' bi h
  change bi < A.length + 1
  let tbl := (List.range S.length).flatMap fun q =>
        (List.range A.length).map fun a =>
          match S[q]?, A[a]? with
          | some q, some a => transOf M S A q a
          | _, _ => NatTrans.halt
  change (tbl[qi * A.length + ai]?).getD NatTrans.halt = .write qi' bi at h
  have hmem : NatTrans.write qi' bi ∈ tbl := by
    cases hget : tbl[qi * A.length + ai]? with
    | none => simp [hget] at h
    | some e =>
        have he : e = .write qi' bi := by simpa [hget] using h
        subst e
        obtain ⟨hidx, hval⟩ := List.getElem?_eq_some_iff.mp hget
        exact hval ▸ List.getElem_mem hidx
  obtain ⟨q, hq, hrow⟩ := List.mem_flatMap.mp hmem
  obtain ⟨a, ha, hentry⟩ := List.mem_map.mp hrow
  have hq_lt : q < S.length := List.mem_range.mp hq
  have ha_lt : a < A.length := List.mem_range.mp ha
  rw [List.getElem?_eq_getElem hq_lt, List.getElem?_eq_getElem ha_lt] at hentry
  simp only at hentry
  exact transOf_write_bound M S A S[q] A[a] qi' bi hentry

lemma descriptorOf_abi_blank {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool)) :
    (descriptorOf M S A).blankIdx < (descriptorOf M S A).numLetters + 1 := by
  unfold descriptorOf
  exact execLetterIdx_lt A none

lemma descriptorOf_abi_false {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool)) :
    (descriptorOf M S A).falseIdx < (descriptorOf M S A).numLetters + 1 := by
  unfold descriptorOf
  exact execLetterIdx_lt A (some false)

lemma descriptorOf_abi_true {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool)) :
    (descriptorOf M S A).trueIdx < (descriptorOf M S A).numLetters + 1 := by
  unfold descriptorOf
  exact execLetterIdx_lt A (some true)

end NPComplete.CookLevin

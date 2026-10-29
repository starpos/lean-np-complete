module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Recode
public import NPComplete.CookLevin.Recode.Enc
public import NPComplete.CookLevin.Machines.TM2to1
public import NPComplete.CookLevin.Machines.TM1to0
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Reachability foundations

The encoding proofs use both exact step counts and reflexive-transitive
reachability, so the simulator needs a bridge between those views. This base
layer proves that bridge before the encoding-specific simulation files build on
it.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)


@[stable_api] lemma stepsTo_of_reaches {α : Type} {f : α → Option α} {a b : α}
    (h : StateTransition.Reaches f a b) : ∃ t, StepsTo f a b t := by
  induction h with
  | refl => exact ⟨0, stepsTo_zero _ _⟩
  | @tail b' c' hab hbc ih =>
      obtain ⟨t, ht⟩ := ih
      have hstep : f b' = some c' := by
        simpa only [Option.mem_def] using hbc
      exact ⟨t + 1, stepsTo_succ f ht hstep⟩

lemma reaches_of_stepsTo {α : Type} {f : α → Option α} {a b : α} {t : ℕ}
    (h : StepsTo f a b t) : StateTransition.Reaches f a b := by
  induction t generalizing a with
  | zero =>
      simp only [StepsTo, Function.iterate_zero_apply, Option.some.injEq] at h
      subst b
      exact Relation.ReflTransGen.refl
  | succ t ih =>
      rw [StepsTo, Function.iterate_succ, Function.comp_apply] at h
      change (flip bind f)^[t] (f a) = some b at h
      cases ha : f a with
      | none =>
          have hnone : ∀ n, (flip bind f)^[n] none = none := by
            intro n
            induction n with
            | zero => rfl
            | succ n ih =>
                rw [Function.iterate_succ, Function.comp_apply]
                change (flip bind f)^[n] none = none
                exact ih
          rw [ha] at h
          rw [hnone t] at h
          cases h
      | some a' =>
          rw [ha] at h
          exact Relation.ReflTransGen.head ha (ih h)

end NPComplete.CookLevin

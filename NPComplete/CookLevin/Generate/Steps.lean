module

public import NPComplete.CookLevin.ToThreeCNF.SATToThreeCNF
public import NPComplete.CookLevin.Tableau
public import NPComplete.CookLevin.Tableau.TableauAtWindow
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Uniqueness of halting runs

Cook–Levin correctness arguments sometimes produce runs with different time
bounds and need to identify their terminal configurations. This module isolates
the deterministic-step reasoning that yields unique halting states and equal
output tapes.
-/

@[expose] public section

namespace NPComplete.CookLevin

lemma stepsTo_cons_iff {α : Type*} {f : α → Option α}
    {a c : α} {t : ℕ} :
    TM2to1.StepsTo f a c (t + 1) ↔
      ∃ b, f a = some b ∧ TM2to1.StepsTo f b c t := by
  simp only [TM2to1.StepsTo, Function.iterate_succ_apply,
    Option.bind_some]
  cases hfa : f a with
  | none =>
      have hnone : ∀ n : ℕ,
          (fun s : Option α => s.bind f)^[n] none = none := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [Function.iterate_succ_apply]
            simp [ih]
      simp [hnone]
  | some b =>
      simp

lemma stepsTo_none_start {α : Type*} {f : α → Option α}
    {a b : α} {t : ℕ} (hf : f a = none)
    (h : TM2to1.StepsTo f a b (t + 1)) : False := by
  obtain ⟨c, hfirst, _⟩ := stepsTo_cons_iff.mp h
  rw [hf] at hfirst
  cases hfirst

lemma stepsTo_halt_unique {α : Type*} {f : α → Option α}
    {s a b : α} {t₁ t₂ : ℕ}
    (h₁ : TM2to1.StepsTo f s a t₁)
    (h₂ : TM2to1.StepsTo f s b t₂)
    (ha : f a = none) (hb : f b = none) : a = b := by
  induction t₁ generalizing s t₂ b with
  | zero =>
      simp only [TM2to1.StepsTo] at h₁
      cases h₁
      cases t₂ with
      | zero =>
          simp only [TM2to1.StepsTo] at h₂
          cases h₂
          rfl
      | succ t₂ =>
          exact (stepsTo_none_start ha h₂).elim
  | succ t₁ ih =>
      cases t₂ with
      | zero =>
          simp only [TM2to1.StepsTo] at h₂
          cases h₂
          exact (stepsTo_none_start hb h₁).elim
      | succ t₂ =>
          obtain ⟨a', hfa, h₁'⟩ := stepsTo_cons_iff.mp h₁
          obtain ⟨b', hfb, h₂'⟩ := stepsTo_cons_iff.mp h₂
          have hab : a' = b' := by
            exact Option.some.inj (hfa.symm.trans hfb)
          cases hab
          apply ih h₁' h₂'
          exact hb

lemma machineOutputsInTime_unique_tape [Inhabited Γ] [Inhabited Λ]
    {M : Turing.TM0.Machine Γ Λ} {input output₁ output₂ : List Γ}
    {m₁ m₂ : ℕ}
    (h₁ : MachineOutputsInTime M input output₁ m₁)
    (h₂ : MachineOutputsInTime M input output₂ m₂) :
    Turing.Tape.mk₁ output₁ = Turing.Tape.mk₁ output₂ := by
  obtain ⟨q₁, t₁, _, hs₁, hh₁⟩ := h₁
  obtain ⟨q₂, t₂, _, hs₂, hh₂⟩ := h₂
  have hcfg := stepsTo_halt_unique hs₁ hs₂ hh₁ hh₂
  exact congrArg
    (fun c : Turing.TM0.Cfg Γ Λ => c.Tape) hcfg

lemma tape_mk₁_bool_injective {a b : Bool}
    (h : Turing.Tape.mk₁ (tapeSymbols [a]) =
      Turing.Tape.mk₁ (tapeSymbols [b])) : a = b := by
  have hh := congrArg
    (fun T : Turing.Tape (Option Bool) => T.head) h
  simpa [tapeSymbols, Turing.Tape.mk₁, Turing.Tape.mk₂,
    Turing.Tape.mk'] using hh

end NPComplete.CookLevin

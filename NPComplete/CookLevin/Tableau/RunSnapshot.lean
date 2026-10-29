module

public import NPComplete.CookLevin.Tableau.SATImplication

/-!
# Run snapshot

The forward correctness proof needs one shared representation of the machine state at every time
and tape position. This module defines that run snapshot so local SAT implications and global
induction use the same observable configuration.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Run snapshot used by the forward direction -/

def dirDelta : Dir → ℤ
  | .left => -1
  | .right => 1

def stepOrStay [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    Cfg Γ Λ :=
  match step M c with
  | some c' => c'
  | none => c

def stepHead [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (c : Cfg Γ Λ)
    (h : ℤ) : ℤ :=
  match M c.q c.Tape.head with
  | some (_, .move d) => h + dirDelta d
  | _ => h

def runCfg [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (input : List Γ) :
    ℕ → Cfg Γ Λ
  | 0 => init input
  | t + 1 => stepOrStay M (runCfg M input t)

def runHead [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (input : List Γ) :
    ℕ → ℤ
  | 0 => 0
  | t + 1 => stepHead M (runCfg M input t) (runHead M input t)

def absNth [Inhabited Γ] (c : Cfg Γ Λ) (head p : ℤ) : Γ :=
  c.Tape.nth (p - head)

noncomputable def runAssign [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (input output : List Γ) (T : ℕ) : Literal.Assignment :=
  fun v =>
    let W := windowSize input.length output.length T
    (List.range (T + 1)).any fun t =>
      let c := runCfg M input t
      let hd := runHead M input t
      S.toList.any (fun q => decide (v = stateVar t (stateIdx S q) ∧ c.q = q)) ||
        (List.range W).any fun p =>
          decide (v = headVar t p ∧ hd = idxToPos T p) ||
            (letters Γ).any fun a =>
              decide (v = cellVar t p (letterIdx a) ∧
                absNth c hd (idxToPos T p) = a)

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.SAT
public import NPComplete.CookLevin.TM0
public import Mathlib.Logic.Encodable.Basic

/-!
# Tableau variable numbering

The tableau needs a finite coordinate system for tape positions and a stable numbering for each
SAT selector. This module defines the window conversions and variable maps that the compact layout
and clause families build on.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Window and variable numbering -/

/-- Cells that a `T`-step run can touch, plus the output support of `mk₁`. -/
def windowSize (inputLen outputLen T : ℕ) : ℕ :=
  max inputLen outputLen + 2 * T + 1

/-- Integer cell coordinate of window index `i`, with the origin at index `T`. -/
def idxToPos (T i : ℕ) : ℤ := (i : ℤ) - (T : ℤ)

def posToIdx (T : ℕ) (p : ℤ) : ℕ := Int.toNat (p + T)

def originIdx (T : ℕ) : ℕ := T

lemma originIdx_lt_window (inputLen outputLen T : ℕ) :
    originIdx T < windowSize inputLen outputLen T := by
  simp [originIdx, windowSize]
  omega

lemma posToIdx_idxToPos (T i : ℕ) : posToIdx T (idxToPos T i) = i := by
  simp [posToIdx, idxToPos]

lemma idxToPos_posToIdx {T : ℕ} {p : ℤ} (hp : - (T : ℤ) ≤ p) :
    idxToPos T (posToIdx T p) = p := by
  simp [idxToPos, posToIdx]
  omega

lemma posToIdx_lt_window {inputLen outputLen T : ℕ} {p : ℤ}
    (hhi : p < (max inputLen outputLen + T : ℤ) + 1) :
    posToIdx T p < windowSize inputLen outputLen T := by
  simp [posToIdx, windowSize]
  omega

/-- Cell / state / head variables occupy residue classes 0 / 1 / 2 mod 3. -/
def cellVar (t p a : ℕ) : ℕ := 3 * Encodable.encode (t, p, a)
def stateVar (t q : ℕ) : ℕ := 3 * Encodable.encode (t, q) + 1
def headVar (t p : ℕ) : ℕ := 3 * Encodable.encode (t, p) + 2

end NPComplete.CookLevin

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Machine.GenericDispatcher
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The `Turing.FinTM2` bridge: every `BoundedWhileDecider` is `TMRealizable`

For any `d : BoundedWhileDecider enc D L`, the site dispatcher has a bounded run from the promise
input to a fully determined halted configuration. This module packages that dispatcher as a
`Turing.FinTM2`, constructs a polynomial majorant for the step bound, and provides a
`TMRealizable` witness connecting bounded-while deciders to polynomial-time Turing-machine
computation.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.RAMToTM.Generic
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)
open NPComplete.BitEncoding (Bits encodeBool)
open Polynomial

/-! ## The bundled machine -/

/-- The `Turing.FinTM2` for a `BoundedWhileDecider`: the site dispatcher `Mg` for `d`'s
    `fullProgram`, reading and writing its single `Bool` through the same `Kg.io` channel
    (prologue scans it for input, cleanup leaves the answer there, `GenericDispatcher.lean`'s
    module doc). Marked `@[reducible]` so `rw`/`simp` can see through it when unifying e.g.
    `(answerMachine d).Γ (answerMachine d).k₀` with `Bool` — without it, every field projection is
    opaque to tactic-level matching even though everything below is definitionally transparent. -/
@[reducible] noncomputable def answerMachine {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : Turing.FinTM2 where
  K := Kg (fullProgram d.p d.outReg)
  k₀ := Kg.io
  k₁ := Kg.io
  Γ := Γg (fullProgram d.p d.outReg)
  Λ := Λg (fullProgram d.p d.outReg)
  main := Λg.prologue .scanInput
  σ := AllInstrState
  initialState := AllInstrState.canonical
  m := Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)

/-- `TM2ComputableInPolyTime`'s input alphabet equivalence: `answerMachine`'s input stack is
    literally `Bool` (`Kg.io`'s alphabet), so the identity works. -/
noncomputable def ioEquivIn {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : (answerMachine d).Γ (answerMachine d).k₀ ≃ Bool :=
  Equiv.refl Bool

/-- `ioEquivIn`'s output-side counterpart (`k₁` is the same `Kg.io` channel). -/
noncomputable def ioEquivOut {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : (answerMachine d).Γ (answerMachine d).k₁ ≃ Bool :=
  Equiv.refl Bool

/-- `Turing.initList` on `answerMachine` lands exactly on `answer_run_full_bound_of_boundedWhileDecider`'s
    own starting configuration — both put the raw input bits on `Kg.io` and leave every other stack
    empty (`initialSg`'s definition). -/
lemma initList_answerMachine {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (bits : Bits) :
    Turing.initList (answerMachine d) bits =
      ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
        initialSg (fullProgram d.p d.outReg) bits⟩ := by
  have hl : (Turing.initList (answerMachine d) bits).l = some (Λg.prologue .scanInput) := rfl
  have hvar : (Turing.initList (answerMachine d) bits).var = AllInstrState.canonical := rfl
  have hstk : (Turing.initList (answerMachine d) bits).stk =
      initialSg (fullProgram d.p d.outReg) bits := by
    funext k
    cases k <;> simp [Turing.initList, answerMachine, initialSg]
  rw [show Turing.initList (answerMachine d) bits =
      ⟨(Turing.initList (answerMachine d) bits).l, (Turing.initList (answerMachine d) bits).var,
        (Turing.initList (answerMachine d) bits).stk⟩ from rfl, hl, hvar, hstk]

/-! ## A polynomial majorant for the step-count bound

`answer_run_full_bound_of_boundedWhileDecider`'s bound mentions `bitLen (enc x).length` (twice) and,
inside `costBound`, a `max` of two of `d`'s fixed constants against a polynomial-in-`(enc x).length`
term — neither `bitLen` nor `max` is itself a `Polynomial ℕ` term, so both need a majorant before a
`Polynomial ℕ` can be built at all (`bitLen n ≤ n + 1`, `max a b ≤ a + b`). -/

/-- Polynomial majorant for `GenericDispatcher.lean`'s `mem0Bound` (`bitLen`-free). -/
def mem0BoundMajor (N : ℕ) : ℕ := (N + 1) * (2 * (N + 1) + 2)

/-- Polynomial majorant for `GenericDispatcher.lean`'s `costBound` (`bitLen`/`max`-free). -/
def costBoundMajor {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (N : ℕ) : ℕ :=
  8 * d.c * (N + 1) ^ d.c *
    (2 * (d.bit_c * (N + 1) ^ d.bit_c + programImmBound d.p + bitLen d.outReg) + 1)

/-- Polynomial majorant for `answer_run_full_bound_of_boundedWhileDecider`'s own step-count bound. -/
def answerBoundMajor {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (N : ℕ) : ℕ :=
  ((N + 1) + N * (4 * (N + 1) + 10) + 3) +
    siteCsup d * (2 * siteGsup d + 1) ^ 2 * (mem0BoundMajor N + costBoundMajor d N + 1) ^ 3 +
    siteCsup d * (2 * siteGsup d + 1) ^ 2 *
      (mem0BoundMajor N + 2 * siteGsup d * costBoundMajor d N +
        (2 * bitLen d.outReg + 4 * (mem0BoundMajor N + 2 * siteGsup d * costBoundMajor d N) + 3) +
        1) ^ 3 +
    (mem0BoundMajor N + 2 * siteGsup d * costBoundMajor d N +
      2 * siteGsup d *
        (2 * bitLen d.outReg + 4 * (mem0BoundMajor N + 2 * siteGsup d * costBoundMajor d N) + 3) +
      regBound (fullProgram d.p d.outReg) + 17)

lemma mem0Bound_le_major {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    mem0Bound d x ≤ mem0BoundMajor (enc x).length := by
  unfold mem0Bound mem0BoundMajor
  gcongr
  exact bitLen_le_succ _

lemma costBound_le_major {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    costBound d x ≤ costBoundMajor d (enc x).length := by
  unfold costBound costBoundMajor
  gcongr
  omega

/-- The majorization step: `answer_run_full_bound_of_boundedWhileDecider`'s Nat bound is at most
    `answerBoundMajor d (enc x).length`. -/
lemma answer_bound_le_major {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    (bitLen (enc x).length + (enc x).length * (4 * bitLen (enc x).length + 10) + 3) +
      siteCsup d * (2 * siteGsup d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 +
      siteCsup d * (2 * siteGsup d + 1) ^ 2 *
        (mem0Bound d x + 2 * siteGsup d * costBound d x +
          (2 * bitLen d.outReg + 4 * (mem0Bound d x + 2 * siteGsup d * costBound d x) + 3) +
          1) ^ 3 +
      (mem0Bound d x + 2 * siteGsup d * costBound d x +
        2 * siteGsup d *
          (2 * bitLen d.outReg + 4 * (mem0Bound d x + 2 * siteGsup d * costBound d x) + 3) +
        regBound (fullProgram d.p d.outReg) + 17)
    ≤ answerBoundMajor d (enc x).length := by
  have hmem := mem0Bound_le_major d x
  have hcost := costBound_le_major d x
  have hbl := bitLen_le_succ (enc x).length
  unfold answerBoundMajor
  gcongr

/-! ## The `Polynomial ℕ` itself -/

/-- `mem0BoundMajor`, restated as a `Polynomial ℕ` term. -/
noncomputable def mem0BoundMajorPoly : Polynomial ℕ := (X + 1) * (2 * (X + 1) + 2)

/-- `costBoundMajor`, restated as a `Polynomial ℕ` term. -/
noncomputable def costBoundMajorPoly {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : Polynomial ℕ :=
  C (8 * d.c) * (X + 1) ^ d.c *
    (2 * (C d.bit_c * (X + 1) ^ d.bit_c + C (programImmBound d.p) + C (bitLen d.outReg)) + 1)

/-- `answerBoundMajor`, restated as a `Polynomial ℕ` term — the `time` field of the
    `TM2ComputableInPolyTime` witness below. -/
noncomputable def timePoly {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : Polynomial ℕ :=
  ((X + 1) + X * (4 * (X + 1) + 10) + 3) +
    C (siteCsup d) * (2 * C (siteGsup d) + 1) ^ 2 *
      (mem0BoundMajorPoly + costBoundMajorPoly d + 1) ^ 3 +
    C (siteCsup d) * (2 * C (siteGsup d) + 1) ^ 2 *
      (mem0BoundMajorPoly + 2 * C (siteGsup d) * costBoundMajorPoly d +
        (2 * C (bitLen d.outReg) +
          4 * (mem0BoundMajorPoly + 2 * C (siteGsup d) * costBoundMajorPoly d) + 3) +
        1) ^ 3 +
    (mem0BoundMajorPoly + 2 * C (siteGsup d) * costBoundMajorPoly d +
      2 * C (siteGsup d) *
        (2 * C (bitLen d.outReg) +
          4 * (mem0BoundMajorPoly + 2 * C (siteGsup d) * costBoundMajorPoly d) + 3) +
      C (regBound (fullProgram d.p d.outReg)) + 17)

/-- `timePoly`'s evaluation at `N` recovers `answerBoundMajor d N` exactly — the two are the same
    Nat expression, one written with `Polynomial.C`/`X`, the other with plain `ℕ` variables. -/
lemma timePoly_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (N : ℕ) :
    (timePoly d).eval N = answerBoundMajor d N := by
  unfold timePoly costBoundMajorPoly mem0BoundMajorPoly answerBoundMajor costBoundMajor
    mem0BoundMajor
  simp

/-! ## Closing `TMRealizable` -/

/-- Every `BoundedWhileDecider` is realizable by a poly-time `FinTM2`.
    Assembles `answerMachine` + `timePoly` + `answer_run_full_bound_of_boundedWhileDecider` into a
    `Turing.TM2ComputableInPolyTime` witness for `d.result` — `initList_answerMachine` matches the
    machine's start state to the run's, and `answer_run_full_bound_of_boundedWhileDecider`'s full
    final-config conjuncts (`cfg'.var`/every non-`Kg.io` stack) pin the halted config down to
    exactly `Turing.haltList (answerMachine d) [d.result ⟨x, hx⟩]`, closing the `EvalsToInTime`
    equation on the nose. -/
@[construction_api] lemma tmRealizable_of_boundedWhileDecider {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : d.TMRealizable := by
  refine ⟨{
    tm := answerMachine d
    inputAlphabet := ioEquivIn d
    outputAlphabet := ioEquivOut d
    time := timePoly d
    outputsFun := ?_ }⟩
  rintro ⟨x, hx⟩
  simp [ioEquivIn, ioEquivOut, BoundedWhileDecider.result, encodeBool]
  choose n cfg' hrun hl hvar hreg hmem hscr hio hn using
    answer_run_full_bound_of_boundedWhileDecider d x hx
  have hbound : n ≤ (timePoly d).eval (enc x).length := by
    rw [timePoly_eval]
    exact hn.trans (answer_bound_le_major d x)
  refine ⟨⟨n, ?_⟩, hbound⟩
  show (flip Bind.bind (Turing.TM2.step (Mg (fullProgram d.p d.outReg)
      (programSupported_any _) (outReg0 d))))^[n]
      (some (Turing.initList (answerMachine d) (enc x))) = _
  have hstep : (flip Bind.bind (Turing.TM2.step (Mg (fullProgram d.p d.outReg)
      (programSupported_any _) (outReg0 d)))) =
      flipBindG (fullProgram d.p d.outReg)
        (Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)) := rfl
  rw [initList_answerMachine, hstep, hrun]
  have hcfg'eq : cfg' = Turing.haltList (answerMachine d)
      [decide (d.p.eval (bitInputStore (enc x)) d.outReg = 1)] := by
    have heta : cfg' = ⟨cfg'.l, cfg'.var, cfg'.stk⟩ := rfl
    rw [heta, hl, hvar]
    congr 1
    funext k
    cases k with
    | reg i => exact hreg i
    | mem => exact hmem
    | io => exact hio
    | scratch s => exact hscr s
  rw [hcfg'eq]
  rfl


end NPComplete.RAMToTM

module

public import NPComplete.CookLevin.ReductionProg.GeneratorLoad
public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelopeAgg

/-!
`GeneratorLoad.lean` builds `loadWordsProg`, the load stage that stages all five words
`generatorProg` reads from the store, but proves no `ProgramBoundedIn` bound for it.
This file supplies that bound for the two load-stage programs (`loadPrefixProg`,
`loadConstWordsProg`) and their composite `loadWordsProg`, mirroring the discharge style
`GeneratorBoundedSetup.lean` uses for the core generator's own setup layer: every address
expression's `ExprBoundedIn` is threaded through the store chain a store-modifying `.seq`
produces, not merely asserted at the entry store, because `.sub`'s `ExprBoundedIn` clause demands
a raw evaluated value (`e1.eval σ ≤ B`) that a `Reg0Expr` equality does not transport on its own.

The `.forN` loop inside `loadPrefixProg` is bounded via the general lemma
`programBoundedIn_loopEval_of_indexed_inv` (`CanonicalStoreFinalizeBody.lean`), instantiated with
the counter-value invariant `Inv m τ := τ (generatorPrefBase p N - 2) = m`. The loop's own
iteration count (`.reg 0`, evaluated once at loop entry per `eval_forN`) needs no arithmetic
bound at all — `ExprBoundedIn` on `.reg r` only constrains the register index `r`, not its runtime
value — the real content is that each iteration's *body* stays bounded, which requires the write
window `generatorPrefBase p N + 2 * m + 1` to fit `B` for every `m < N`, hence the loop-wide
`hloopBound : generatorPrefBase p N + 2 * N + 1 ≤ B` hypothesis threaded throughout.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## `loadPrefixProg`

Following `GeneratorBoundedSetup.lean`'s own caveat (`Reg0Expr` gives an evaluated-value equality,
but `ExprBoundedIn` on `.sub`/`.regInd` needs the raw evaluated value, not merely that equality):
every helper below takes `generatorPrefBaseE p`'s bound at *every* store agreeing with `N` on
register `0`, not just at one fixed store. -/

lemma exprBoundedIn_loadPrefixCounterE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (hτ0 : τ 0 = N)
    (hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B) :
    ExprBoundedIn B τ (loadPrefixCounterE p time d allowedIdx) := by
  have hge := generatorPrefBase_ge p time d allowedIdx N
  unfold loadPrefixCounterE
  refine ⟨hprefB, by simp only [ExprBoundedIn]; omega, ?_⟩
  rw [generator_pref_base_e_eval p time d allowedIdx τ N hτ0]
  omega

lemma exprBoundedIn_loadPrefixCounterCell (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (hτ0 : τ 0 = N)
    (hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B) :
    ExprBoundedIn B τ (loadPrefixCounterCell p time d allowedIdx) := by
  unfold loadPrefixCounterCell
  refine ⟨exprBoundedIn_loadPrefixCounterE B N p time d allowedIdx τ hτ0 hprefB hprefBound, ?_⟩
  rw [loadPrefixCounterE_eval p time d allowedIdx N τ hτ0]
  have hge := generatorPrefBase_ge p time d allowedIdx N
  omega

/-- The write-address expression's `.mul` node needs the intermediate product `2 * i` bounded on
top of the sum — the one place this program family's `.mul` shows up. -/
lemma exprBoundedIn_loadPrefixWriteAddrE (B N i : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (hτ0 : τ 0 = N)
    (hictr : τ (generatorPrefBase p time d allowedIdx N - 2) = i)
    (hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B)
    (hsum : generatorPrefBase p time d allowedIdx N + 2 * i ≤ B) :
    ExprBoundedIn B τ (loadPrefixWriteAddrE p time d allowedIdx) := by
  unfold loadPrefixWriteAddrE
  have hge := generatorPrefBase_ge p time d allowedIdx N
  have hcellB := exprBoundedIn_loadPrefixCounterCell B N p time d allowedIdx τ hτ0 hprefB hprefBound
  have hcelleval : (loadPrefixCounterCell p time d allowedIdx).eval τ = i := by
    rw [loadPrefixCounterCell_eval p time d allowedIdx N τ hτ0]; exact hictr
  have hprefEval := generator_pref_base_e_eval p time d allowedIdx τ N hτ0
  simp only [ExprBoundedIn, Expr.eval]
  rw [hcelleval, hprefEval]
  refine ⟨hprefB, ⟨by omega, hcellB, by omega⟩, by omega⟩

lemma exprBoundedIn_loadPrefixTestE (B N i : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (hτ0 : τ 0 = N)
    (hictr : τ (generatorPrefBase p time d allowedIdx N - 2) = i)
    (hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B)
    (hi1B : i + 1 ≤ B) :
    ExprBoundedIn B τ (loadPrefixTestE p time d allowedIdx) := by
  unfold loadPrefixTestE
  have hcellB := exprBoundedIn_loadPrefixCounterCell B N p time d allowedIdx τ hτ0 hprefB hprefBound
  have hcelleval : (loadPrefixCounterCell p time d allowedIdx).eval τ = i := by
    rw [loadPrefixCounterCell_eval p time d allowedIdx N τ hτ0]; exact hictr
  simp only [ExprBoundedIn, Expr.eval]
  rw [hcelleval]
  exact ⟨⟨by omega, hcellB, by omega⟩, by omega⟩

/-- One `ifNZ` branch of `loadPrefixStep`, writing a constant `v` (`trueIdx` or `falseIdx`) at
`writeAddr + 1`. Kept generic in `v` so both branches close from one lemma. -/
lemma programBoundedIn_load_prefix_write_branch (B N i v : ℕ) (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) (σ1 : Store)
    (hσ1_0 : σ1 0 = N) (hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = i)
    (hprefB : ExprBoundedIn B σ1 (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B)
    (hsum1 : generatorPrefBase p time d allowedIdx N + 2 * i + 1 ≤ B) (hvB : v ≤ B) :
    ProgramBoundedIn B σ1
      (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const v)) := by
  have hwriteB := exprBoundedIn_loadPrefixWriteAddrE B N i p time d allowedIdx σ1 hσ1_0 hσ1_ctr
    hprefB hprefBound (by omega)
  have hwriteEval := loadPrefixWriteAddrE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr
  refine ⟨⟨hwriteB, ?_⟩, hvB, ?_⟩ <;>
    (simp only [ExprBoundedIn, Expr.eval]; rw [hwriteEval]; omega)

/-- The counter-bump write at the end of `loadPrefixStep`: needs only that register `0` and the
counter cell still hold `N`/`i` (true after either `ifNZ` branch), plus `i + 1 ≤ B` — the fact that
the bumped counter's own upper bound (`hloopBound`, via the caller) must exceed the *old* value by
at least one, not merely dominate it. -/
lemma programBoundedIn_load_prefix_counter_bump (B N i : ℕ) (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) (σ2 : Store)
    (hσ2_0 : σ2 0 = N) (hσ2_ctr : σ2 (generatorPrefBase p time d allowedIdx N - 2) = i)
    (hprefB : ExprBoundedIn B σ2 (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B) (hi1B : i + 1 ≤ B) :
    ProgramBoundedIn B σ2
      (Program.assignInd (loadPrefixCounterE p time d allowedIdx)
        (Expr.add (loadPrefixCounterCell p time d allowedIdx) (Expr.const 1))) := by
  have hcellB := exprBoundedIn_loadPrefixCounterCell B N p time d allowedIdx σ2 hσ2_0 hprefB
    hprefBound
  have hcelleval : (loadPrefixCounterCell p time d allowedIdx).eval σ2 = i := by
    rw [loadPrefixCounterCell_eval p time d allowedIdx N σ2 hσ2_0]; exact hσ2_ctr
  have hcounterEeval : (loadPrefixCounterE p time d allowedIdx).eval σ2
      = generatorPrefBase p time d allowedIdx N - 2 :=
    loadPrefixCounterE_eval p time d allowedIdx N σ2 hσ2_0
  refine ⟨exprBoundedIn_loadPrefixCounterE B N p time d allowedIdx σ2 hσ2_0 hprefB hprefBound,
    ?_, ?_⟩
  · simp only [ExprBoundedIn, Expr.eval]
    rw [hcelleval]
    exact ⟨hcellB, by omega, by omega⟩
  · rw [hcounterEeval]; omega

/-- `ProgramBoundedIn` for one full iteration of `loadPrefixStep`, at the store the `i`-th
iteration starts from: given `N`/`i` at the marker cells and the write window `base + 2i + 1`
fits `B`, all three writes (the even cell, the `ifNZ`'d odd cell, the counter bump) stay `≤ B`,
whichever branch the `ifNZ` takes. -/
lemma programBoundedIn_loadPrefixStep (B N i : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (σ : Store) (hσ0 : σ 0 = N) (hσctr : σ (generatorPrefBase p time d allowedIdx N - 2) = i)
    (hprefB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B)
    (hsum1 : generatorPrefBase p time d allowedIdx N + 2 * i + 1 ≤ B) (hi1B : i + 1 ≤ B)
    (htB : d.trueIdx ≤ B) (hfB : d.falseIdx ≤ B) :
    ProgramBoundedIn B σ (loadPrefixStep p time d allowedIdx) := by
  unfold loadPrefixStep
  have hge := generatorPrefBase_ge p time d allowedIdx N
  have hwriteB := exprBoundedIn_loadPrefixWriteAddrE B N i p time d allowedIdx σ hσ0 hσctr
    (hprefB σ hσ0) hprefBound (by omega)
  have hwriteEval := loadPrefixWriteAddrE_eval p time d allowedIdx N i σ hσ0 hσctr
  have hstep1 : ProgramBoundedIn B σ
      (Program.assignInd (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const d.trueIdx)) :=
    ⟨hwriteB, htB, by rw [hwriteEval]; omega⟩
  refine ⟨hstep1, ?_⟩
  simp only [eval_assignInd]
  set σ1 := writeReg σ ((loadPrefixWriteAddrE p time d allowedIdx).eval σ)
    ((Expr.const d.trueIdx).eval σ) with hσ1def
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def, writeReg_diff σ _ _ 0 (by rw [hwriteEval]; omega)]; exact hσ0
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = i := by
    rw [hσ1def, writeReg_diff σ _ _ (generatorPrefBase p time d allowedIdx N - 2)
      (by rw [hwriteEval]; omega)]
    exact hσctr
  have htestB := exprBoundedIn_loadPrefixTestE B N i p time d allowedIdx σ1 hσ1_0 hσ1_ctr
    (hprefB σ1 hσ1_0) hprefBound (by omega)
  have hstepBranch : ProgramBoundedIn B σ1
      (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.trueIdx))
    ∧ ProgramBoundedIn B σ1
      (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.falseIdx)) :=
    ⟨programBoundedIn_load_prefix_write_branch B N i d.trueIdx p time d allowedIdx σ1 hσ1_0 hσ1_ctr
        (hprefB σ1 hσ1_0) hprefBound (by omega) htB,
     programBoundedIn_load_prefix_write_branch B N i d.falseIdx p time d allowedIdx σ1 hσ1_0 hσ1_ctr
        (hprefB σ1 hσ1_0) hprefBound (by omega) hfB⟩
  have hstep2 : ProgramBoundedIn B σ1
      (Program.ifNZ (loadPrefixTestE p time d allowedIdx)
        (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
          (Expr.const d.trueIdx))
        (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
          (Expr.const d.falseIdx))) :=
    ⟨htestB, hstepBranch.1, hstepBranch.2⟩
  refine ⟨hstep2, ?_⟩
  simp only [eval_ifNZ]
  set σ2 := (if (loadPrefixTestE p time d allowedIdx).eval σ1 ≠ 0
      then (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.trueIdx)).eval σ1
      else (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.falseIdx)).eval σ1)
    with hσ2def
  have hσ2_0 : σ2 0 = N := by
    rw [hσ2def]
    split <;>
      · rw [eval_assignInd, writeReg_diff σ1 _ _ 0 (by
          simp only [Expr.eval]
          rw [loadPrefixWriteAddrE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr]; omega)]
        exact hσ1_0
  have hσ2_ctr : σ2 (generatorPrefBase p time d allowedIdx N - 2) = i := by
    rw [hσ2def]
    split <;>
      · rw [eval_assignInd,
          writeReg_diff σ1 _ _ (generatorPrefBase p time d allowedIdx N - 2) (by
            simp only [Expr.eval]
            rw [loadPrefixWriteAddrE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr]; omega)]
        exact hσ1_ctr
  exact programBoundedIn_load_prefix_counter_bump B N i p time d allowedIdx σ2 hσ2_0 hσ2_ctr
    (hprefB σ2 hσ2_0) hprefBound hi1B

/-- `programBoundedIn_loopEval_of_indexed_inv`'s per-step hypothesis, instantiated at
`Inv m τ := τ (generatorPrefBase p N - 2) = m`: the loop's per-iteration invariant (the counter
reads the iteration index) advances by one and the body stays bounded. This is the fact
`ProgramBoundedIn`'s own `.forN` clause needs (`∀ m' < n.eval σ, ProgramBoundedIn B (loopEval body
m' σ) body`), read off `programBoundedIn_loadPrefixStep` at each generation `m`. -/
lemma programBoundedIn_load_prefix_loop_body (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (hprefB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hloopBound : generatorPrefBase p time d allowedIdx N + 2 * N + 1 ≤ B)
    (htB : d.trueIdx ≤ B) (hfB : d.falseIdx ≤ B) :
    ∀ m, m < N → ∀ τ : Store, τ (generatorPrefBase p time d allowedIdx N - 2) = m → τ 0 = N →
      (loadPrefixStep p time d allowedIdx).eval τ (generatorPrefBase p time d allowedIdx N - 2)
        = m + 1 ∧
      (loadPrefixStep p time d allowedIdx).eval τ 0 = N ∧
      ProgramBoundedIn B τ (loadPrefixStep p time d allowedIdx) := by
  intro m hmN τ hτctr hτ0
  have hge := generatorPrefBase_ge p time d allowedIdx N
  have hstep := loadPrefixStep_eval p time d allowedIdx N m τ hτ0 hτctr
  refine ⟨?_, ?_, ?_⟩
  · rw [hstep, writeReg_same]
  · rw [hstep]
    rw [writeReg_diff _ _ _ 0 (by omega), writeReg_diff _ _ _ 0 (by omega),
      writeReg_diff _ _ _ 0 (by omega)]
    exact hτ0
  · exact programBoundedIn_loadPrefixStep B N m p time d allowedIdx τ hτ0 hτctr hprefB
      (by omega) (by omega) (by omega) htB hfB

/-- Every store `loopEval (loadPrefixStep p time d allowedIdx) m' σ1` visits, for `m' < N`, keeps
`loadPrefixStep` bounded — the `∀ m' < n.eval σ, ProgramBoundedIn B (loopEval body m' σ) body`
clause `ProgramBoundedIn` demands of `.forN`. Built from the general
`programBoundedIn_loopEval_of_indexed_inv` (`CanonicalStoreFinalizeBody.lean`), reused as-is: its
signature already carries the `loopEval`-indexed generation structure this loop needs, no new
invariant machinery required beyond instantiating `Inv`. -/
lemma programBoundedIn_load_prefix_loop (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (σ1 : Store) (hσ1_0 : σ1 0 = N) (hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = 0)
    (hprefB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hloopBound : generatorPrefBase p time d allowedIdx N + 2 * N + 1 ≤ B)
    (htB : d.trueIdx ≤ B) (hfB : d.falseIdx ≤ B) :
    ∀ m', m' < N →
      ProgramBoundedIn B (loopEval (loadPrefixStep p time d allowedIdx) m' σ1)
        (loadPrefixStep p time d allowedIdx) :=
  programBoundedIn_loopEval_of_indexed_inv N (loadPrefixStep p time d allowedIdx)
    (fun m τ => τ (generatorPrefBase p time d allowedIdx N - 2) = m) B N
    (fun m hmN τ hInv hτ0 => programBoundedIn_load_prefix_loop_body B N p time d allowedIdx hprefB
      hloopBound htB hfB m hmN τ hInv hτ0)
    N 0 (by omega) σ1 hσ1_ctr hσ1_0

/-- Register `0` and the counter cell after `n ≤ N` iterations of `loadPrefixStep` — the fragment
of `load_prefix_loop_inv` boundedness actually needs (no `bits`/`hinput` dependency, since
boundedness never reads the written data, only the marker cells the loop threads). Kept separate
from `load_prefix_loop_inv` rather than reusing it directly, since that lemma additionally demands
`bits.length = N` and an input-agreement hypothesis this file's `B`-only concern does not have. -/
lemma load_prefix_loop_ctr_only (N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ0 : Store)
    (hσ0_0 : σ0 0 = N) (hσ0_ctr : σ0 (generatorPrefBase p time d allowedIdx N - 2) = 0) :
    ∀ n, n ≤ N →
      (loopEval (loadPrefixStep p time d allowedIdx) n σ0) 0 = N ∧
      (loopEval (loadPrefixStep p time d allowedIdx) n σ0)
        (generatorPrefBase p time d allowedIdx N - 2) = n := by
  intro n
  induction n with
  | zero => intro _; rw [loopEval_zero]; exact ⟨hσ0_0, hσ0_ctr⟩
  | succ n ih =>
    intro hnN
    obtain ⟨ih0, ihctr⟩ := ih (by omega)
    rw [loopEval_succ_snoc]
    set s := loopEval (loadPrefixStep p time d allowedIdx) n σ0 with hsdef
    have hstep := loadPrefixStep_eval p time d allowedIdx N n s ih0 ihctr
    have hge := generatorPrefBase_ge p time d allowedIdx N
    refine ⟨?_, ?_⟩
    · rw [hstep, writeReg_diff _ _ _ 0 (by omega), writeReg_diff _ _ _ 0 (by omega),
        writeReg_diff _ _ _ 0 (by omega)]
      exact ih0
    · rw [hstep, writeReg_same]

lemma exprBoundedIn_loadPrefixLenAddrE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (hτ0 : τ 0 = N)
    (hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx N ≤ B) :
    ExprBoundedIn B τ (loadPrefixLenAddrE p time d allowedIdx) := by
  have hge := generatorPrefBase_ge p time d allowedIdx N
  unfold loadPrefixLenAddrE
  refine ⟨hprefB, by simp only [ExprBoundedIn]; omega, ?_⟩
  rw [generator_pref_base_e_eval p time d allowedIdx τ N hτ0]
  omega

/-- `loadPrefixProg`'s three-`.seq` chain (zero the counter, run the loop, write the trailing
separator and the length cell) stays bounded by `B`, given `B` large enough for the loop's write
window (`hloopBound`) and the two written constants. -/
lemma programBoundedIn_loadPrefixProg (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (σ : Store) (hσ0 : σ 0 = N)
    (hprefB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hloopBound : generatorPrefBase p time d allowedIdx N + 2 * N + 1 ≤ B)
    (hB2 : 2 ≤ B) (htB : d.trueIdx ≤ B) (hfB : d.falseIdx ≤ B) :
    ProgramBoundedIn B σ (loadPrefixProg p time d allowedIdx) := by
  have hge := generatorPrefBase_ge p time d allowedIdx N
  have hprefBound : generatorPrefBase p time d allowedIdx N ≤ B := by omega
  unfold loadPrefixProg
  have hstep0 : ProgramBoundedIn B σ
      (Program.assignInd (loadPrefixCounterE p time d allowedIdx) (Expr.const 0)) :=
    ⟨exprBoundedIn_loadPrefixCounterE B N p time d allowedIdx σ hσ0 (hprefB σ hσ0) hprefBound,
      by simp only [ExprBoundedIn]; omega,
      by rw [loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]; omega⟩
  refine ⟨hstep0, ?_⟩
  simp only [eval_assignInd]
  set σ0 := writeReg σ ((loadPrefixCounterE p time d allowedIdx).eval σ)
    ((Expr.const (0 : ℕ)).eval σ) with hσ0def
  have hσ0_0 : σ0 0 = N := by
    rw [hσ0def, writeReg_diff σ _ _ 0
      (by rw [loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]; omega)]
    exact hσ0
  have hσ0_ctr : σ0 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ0def, loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]
    show writeReg σ (generatorPrefBase p time d allowedIdx N - 2) 0
      (generatorPrefBase p time d allowedIdx N - 2) = 0
    rw [writeReg_same]
  have hforNB : ExprBoundedIn B σ0 (Expr.reg 0) := by simp only [ExprBoundedIn]; omega
  refine ⟨?_, ?_⟩
  · simp only [ProgramBoundedIn]
    refine ⟨hforNB, ?_⟩
    simp only [Expr.eval, hσ0_0]
    exact programBoundedIn_load_prefix_loop B N p time d allowedIdx σ0 hσ0_0 hσ0_ctr hprefB
      hloopBound htB hfB
  · simp only [eval_forN, Expr.eval, hσ0_0]
    obtain ⟨hres0, hresctr⟩ := load_prefix_loop_ctr_only N p time d allowedIdx σ0 hσ0_0 hσ0_ctr N
      le_rfl
    set result := loopEval (loadPrefixStep p time d allowedIdx) N σ0 with hresultdef
    have hwriteB := exprBoundedIn_loadPrefixWriteAddrE B N N p time d allowedIdx result hres0
      hresctr (hprefB result hres0) hprefBound (by omega)
    have hwriteEval := loadPrefixWriteAddrE_eval p time d allowedIdx N N result hres0 hresctr
    have hstepF : ProgramBoundedIn B result
        (Program.assignInd (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const d.falseIdx)) :=
      ⟨hwriteB, hfB, by rw [hwriteEval]; omega⟩
    refine ⟨hstepF, ?_⟩
    simp only [eval_assignInd]
    set σ3 := writeReg result ((loadPrefixWriteAddrE p time d allowedIdx).eval result)
      ((Expr.const d.falseIdx).eval result) with hσ3def
    have hσ3_0 : σ3 0 = N := by
      rw [hσ3def, writeReg_diff result _ _ 0 (by rw [hwriteEval]; omega)]; exact hres0
    exact ⟨exprBoundedIn_loadPrefixLenAddrE B N p time d allowedIdx σ3 hσ3_0 (hprefB σ3 hσ3_0)
      hprefBound,
      exprBoundedIn_generatorPrefLenE B N σ3 hσ3_0 (by omega) (by omega),
      by
        have := generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0
        unfold loadPrefixLenAddrE
        simp only [Expr.eval]
        rw [this]; omega⟩

/-! ## `loadConstWordsProg`

Bounded, generically in `baseE`/`xs`, then specialized to `loadConstWordsProg`'s four calls. Since
every value written is a compile-time constant, only the address arithmetic needs bounding — no
`.mul` and no `ifNZ` this time, so the proofs are shorter than the prefix loop's. -/

/-- `constCellAssign`'s single write stays bounded, given `baseE` bounded and its address
`baseE.eval σ + j` (before the truncated `- 1`) fits `B` along with the value `v`. -/
lemma programBoundedIn_constCellAssign (B j v : ℕ) (baseE : Expr) (σ : Store) (hB1 : 1 ≤ B)
    (hbaseB : ExprBoundedIn B σ baseE) (hjB : j ≤ B) (hsum : baseE.eval σ + j ≤ B) (hvB : v ≤ B) :
    ProgramBoundedIn B σ (constCellAssign baseE j v) := by
  unfold constCellAssign ProgramBoundedIn
  simp only [ExprBoundedIn, Expr.eval]
  refine ⟨⟨⟨hbaseB, hjB, hsum⟩, hB1, hsum⟩, hvB, by omega⟩

/-- `constCellsFrom`'s chain of writes stays bounded, given `baseE` bounded at every store
whose register `0` holds `N` (the same `Reg0Expr`-vs-`ExprBoundedIn` transport gap as for
`loadPrefixProg`).
`hbaseVal : 1 ≤ baseE.eval σ` is what `writeConstWordProg_wordAt`'s own correctness proof needs
too: without it cell `0` could coincide with a write address and the frame argument would fail. -/
lemma programBoundedIn_constCellsFrom (B N j : ℕ) (baseE : Expr) (hb : Reg0Expr baseE) (hj : 1 ≤ j)
    (xs : List ℕ) (σ : Store) (hσ0 : σ 0 = N) (hbaseVal : 1 ≤ baseE.eval σ)
    (hbaseB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ baseE) (hB1 : 1 ≤ B)
    (hjB : ∀ k, k < xs.length → j + k ≤ B)
    (hsum : ∀ k, k < xs.length → baseE.eval σ + (j + k) ≤ B)
    (hvB : ∀ k, k < xs.length → xs.getD k 0 ≤ B) :
    ProgramBoundedIn B σ (constCellsFrom baseE j xs) := by
  induction xs generalizing σ j with
  | nil => simp [constCellsFrom, ProgramBoundedIn]
  | cons x rest ih =>
    have hhead : ProgramBoundedIn B σ (constCellAssign baseE j x) :=
      programBoundedIn_constCellAssign B j x baseE σ hB1 (hbaseB σ hσ0)
        (by have := hjB 0 (by simp); omega) (by have := hsum 0 (by simp); omega) (hvB 0 (by simp))
    refine ⟨hhead, ?_⟩
    have hz : (constCellAssign baseE j x).eval σ 0 = σ 0 :=
      constCellAssign_eval_diff baseE j x σ 0 (by omega)
    have hz' : (constCellAssign baseE j x).eval σ 0 = N := by rw [hz]; exact hσ0
    have hbaseEq : baseE.eval ((constCellAssign baseE j x).eval σ) = baseE.eval σ := hb _ _ hz
    exact ih (j + 1) (by omega) ((constCellAssign baseE j x).eval σ) hz'
      (by rw [hbaseEq]; exact hbaseVal)
      (fun k hk => by have := hjB (k + 1) (by simp [hk]); omega)
      (fun k hk => by rw [hbaseEq]; have := hsum (k + 1) (by simp [hk]); omega)
      (fun k hk => hvB (k + 1) (by simp [hk]))

/-- `writeConstWordProg`'s whole word (the length cell at `baseE - 1`, then `xs.length` data cells
from `baseE`) stays bounded, given `baseE` bounded (at every store agreeing on register `0`) and
the word's own address window `baseE.eval σ + xs.length` fits `B`. `hNbase : N < baseE.eval σ - 1`
mirrors `writeConstWordProg_wordAt`'s own `h0 : σ 0 < base - 1` precondition. -/
lemma programBoundedIn_writeConstWordProg (B N : ℕ) (baseE : Expr) (hb : Reg0Expr baseE)
    (xs : List ℕ) (σ : Store) (hσ0 : σ 0 = N)
    (hbaseB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ baseE) (hB1 : 1 ≤ B)
    (hNbase : N < baseE.eval σ - 1)
    (hsum : baseE.eval σ + xs.length ≤ B)
    (hvB : ∀ k, k < xs.length → xs.getD k 0 ≤ B) :
    ProgramBoundedIn B σ (writeConstWordProg baseE xs) := by
  unfold writeConstWordProg
  have hlenB : xs.length ≤ B := by omega
  refine ⟨programBoundedIn_constCellAssign B 0 xs.length baseE σ hB1 (hbaseB σ hσ0)
    (by omega) (by omega) hlenB, ?_⟩
  set σ0 := (constCellAssign baseE 0 xs.length).eval σ with hσ0def
  have hz : σ0 0 = σ 0 :=
    constCellAssign_eval_diff baseE 0 xs.length σ 0 (by omega)
  have hz' : σ0 0 = N := by rw [hz]; exact hσ0
  have hbaseEq : baseE.eval σ0 = baseE.eval σ := hb _ _ hz
  exact programBoundedIn_constCellsFrom B N 1 baseE hb (by omega) xs σ0 hz'
    (by rw [hbaseEq]; omega)
    (fun τ hτ => hbaseB τ hτ) hB1
    (fun k hk => by omega)
    (fun k hk => by rw [hbaseEq]; omega)
    hvB

/-- `loadConstWordsProg`'s four `writeConstWordProg` calls stay bounded, chained through
`writeConstWordProg_zero`'s register-`0` preservation exactly as `loadConstWordsProg_zero` itself
does. Each stage's base is bounded at every store agreeing on register `0` (the same transport gap
as for `loadPrefixProg`). -/
lemma programBoundedIn_loadConstWordsProg (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (hσ0 : σ 0 = N) (hB1 : 1 ≤ B)
    (hkindB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorKindBaseE p time d allowedIdx))
    (harg1B : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg1BaseE p time d allowedIdx))
    (harg2B : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg2BaseE p time d allowedIdx))
    (houtB : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorOutBaseE p time d allowedIdx))
    (hkindSum : generatorKindBase p time d allowedIdx N + (d.table.map transKind).length ≤ B)
    (harg1Sum : generatorArg1Base p time d allowedIdx N + (d.table.map transArg1).length ≤ B)
    (harg2Sum : generatorArg2Base p time d allowedIdx N + (d.table.map transArg2).length ≤ B)
    (houtSum : generatorOutBase p time d allowedIdx N + outIdx.length ≤ B)
    (hkindVB : ∀ k, k < (d.table.map transKind).length → (d.table.map transKind).getD k 0 ≤ B)
    (harg1VB : ∀ k, k < (d.table.map transArg1).length → (d.table.map transArg1).getD k 0 ≤ B)
    (harg2VB : ∀ k, k < (d.table.map transArg2).length → (d.table.map transArg2).getD k 0 ≤ B)
    (houtVB : ∀ k, k < outIdx.length → outIdx.getD k 0 ≤ B) :
    ProgramBoundedIn B σ (loadConstWordsProg p time d allowedIdx outIdx) := by
  have hlt := lt_setupM p time d allowedIdx N
  have hk0 : (generatorKindBaseE p time d allowedIdx).eval σ
      = generatorKindBase p time d allowedIdx N :=
    generator_kind_base_e_eval p time d allowedIdx σ N hσ0
  have hN1 : σ 0 < generatorKindBase p time d allowedIdx N - 1 := by
    rw [hσ0]; unfold generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset; omega
  have hb1 : ProgramBoundedIn B σ
      (writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)) :=
    programBoundedIn_writeConstWordProg B N (generatorKindBaseE p time d allowedIdx)
      (generator_kind_base_e_reg0 p time d allowedIdx) (d.table.map transKind) σ hσ0 hkindB hB1
      (by rw [hk0]; omega) (by rw [hk0]; exact hkindSum) hkindVB
  refine ⟨hb1, ?_⟩
  set σ1 := (writeConstWordProg (generatorKindBaseE p time d allowedIdx)
    (d.table.map transKind)).eval σ with hσ1def
  have w1 := writeConstWordProg_zero (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ _ hk0 hN1
  have hσ1_0 : σ1 0 = N := by rw [hσ1def, w1, hσ0]
  have ha1 : (generatorArg1BaseE p time d allowedIdx).eval σ1
      = generatorArg1Base p time d allowedIdx N :=
    generator_arg1_base_e_eval p time d allowedIdx σ1 N hσ1_0
  have hN2 : σ1 0 < generatorArg1Base p time d allowedIdx N - 1 := by
    rw [hσ1_0]
    unfold generatorArg1Base generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hb2 : ProgramBoundedIn B σ1
      (writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)) :=
    programBoundedIn_writeConstWordProg B N (generatorArg1BaseE p time d allowedIdx)
      (generator_arg1_base_e_reg0 p time d allowedIdx) (d.table.map transArg1) σ1 hσ1_0 harg1B hB1
      (by rw [ha1]; omega) (by rw [ha1]; exact harg1Sum) harg1VB
  refine ⟨hb2, ?_⟩
  set σ2 := (writeConstWordProg (generatorArg1BaseE p time d allowedIdx)
    (d.table.map transArg1)).eval σ1 with hσ2def
  have w2 := writeConstWordProg_zero (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) σ1 _ ha1 hN2
  have hσ2_0 : σ2 0 = N := by rw [hσ2def, w2, hσ1_0]
  have ha2 : (generatorArg2BaseE p time d allowedIdx).eval σ2
      = generatorArg2Base p time d allowedIdx N :=
    generator_arg2_base_e_eval p time d allowedIdx σ2 N hσ2_0
  have hN3 : σ2 0 < generatorArg2Base p time d allowedIdx N - 1 := by
    rw [hσ2_0]
    unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hb3 : ProgramBoundedIn B σ2
      (writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)) :=
    programBoundedIn_writeConstWordProg B N (generatorArg2BaseE p time d allowedIdx)
      (generator_arg2_base_e_reg0 p time d allowedIdx) (d.table.map transArg2) σ2 hσ2_0 harg2B hB1
      (by rw [ha2]; omega) (by rw [ha2]; exact harg2Sum) harg2VB
  refine ⟨hb3, ?_⟩
  set σ3 := (writeConstWordProg (generatorArg2BaseE p time d allowedIdx)
    (d.table.map transArg2)).eval σ2 with hσ3def
  have w3 := writeConstWordProg_zero (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) σ2 _ ha2 hN3
  have hσ3_0 : σ3 0 = N := by rw [hσ3def, w3, hσ2_0]
  have ho : (generatorOutBaseE p time d allowedIdx).eval σ3
      = generatorOutBase p time d allowedIdx N :=
    generator_out_base_e_eval p time d allowedIdx σ3 N hσ3_0
  have hN4 : σ3 0 < generatorOutBase p time d allowedIdx N - 1 := by
    rw [hσ3_0]
    unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
      generatorKindOffset generatorPrefLen generatorPrefOffset
    omega
  exact programBoundedIn_writeConstWordProg B N (generatorOutBaseE p time d allowedIdx)
    (generator_out_base_e_reg0 p time d allowedIdx) outIdx σ3 hσ3_0 houtB hB1
    (by rw [ho]; omega) (by rw [ho]; exact houtSum) houtVB

/-! ## `loadWordsProg`, and its `envB` instance -/

/-- The five staged-word base expressions all stay `ExprBoundedIn B` at *every* store agreeing
with `N` on register `0` — the uniform-in-`τ` form `loadWordsProg`'s two stages need. Mirrors the
discharge chain inside `programBoundedIn_generatorLayoutProg`, generalized to arbitrary `τ`. -/
lemma exprBoundedIn_loadWordsProg_bases (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (h1p : p.eval 1 ≤ B) (hsp : p.eval (N + 1) ≤ B) (hmp : N * p.eval (N + 1) ≤ B)
    (hspan : setupSpan p N ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hmule : N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hpref30 : setupM p time d allowedIdx N + generatorPrefOffset ≤ B)
    (hpref2b : 2 * N + 1 ≤ B)
    (hkindsum : generatorPrefBase p time d allowedIdx N + generatorPrefLen N + 2 ≤ B)
    (harg1sum : generatorKindBase p time d allowedIdx N + (d.table.length + 2) ≤ B)
    (harg2sum : generatorArg1Base p time d allowedIdx N + (d.table.length + 2) ≤ B)
    (houtsum : generatorArg2Base p time d allowedIdx N + (d.table.length + 2) ≤ B) :
    (∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx)) ∧
    (∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorKindBaseE p time d allowedIdx)) ∧
    (∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg1BaseE p time d allowedIdx)) ∧
    (∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg2BaseE p time d allowedIdx)) ∧
    (∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorOutBaseE p time d allowedIdx)) := by
  have hpref : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx) :=
    by
    intro τ hτ
    exact exprBoundedIn_generatorPrefBaseE B N p time d allowedIdx τ
      (exprBoundedIn_setupME B N p time d allowedIdx τ
        (exprBoundedIn_setupSpanE B N p τ hτ h1p hsp hmp hspan) (setupSpanE_eval p τ N hτ) hτ
        h1e hshifte hmule (by omega))
      (setupME_eval p time d allowedIdx τ N hτ) hpref30
  have hlen : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ generatorPrefLenE := by
    intro τ hτ; exact exprBoundedIn_generatorPrefLenE B N τ hτ (by omega) hpref2b
  have hkind : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorKindBaseE p time d allowedIdx) :=
    by
    intro τ hτ
    exact exprBoundedIn_generatorKindBaseE B N p time d allowedIdx τ hτ (hpref τ hτ) (hlen τ hτ)
      hkindsum
  have harg1 :
      ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg1BaseE p time d allowedIdx) := by
    intro τ hτ
    exact exprBoundedIn_generatorArg1BaseE B N p time d allowedIdx τ hτ (hkind τ hτ) harg1sum
  have harg2 :
      ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorArg2BaseE p time d allowedIdx) := by
    intro τ hτ
    exact exprBoundedIn_generatorArg2BaseE B N p time d allowedIdx τ hτ (harg1 τ hτ) harg2sum
  have hout : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ (generatorOutBaseE p time d allowedIdx) :=
    by
    intro τ hτ
    exact exprBoundedIn_generatorOutBaseE B N p time d allowedIdx τ hτ (harg2 τ hτ) houtsum
  exact ⟨hpref, hkind, harg1, harg2, hout⟩

/-- `loadWordsProg`'s two stages stay bounded by `B` on `bitInputStore bits`, given `B` large
enough for every arithmetic obligation the prefix loop and the four constant words impose. This
composes `programBoundedIn_loadPrefixProg` (`.seq`'s first half) with
`programBoundedIn_loadConstWordsProg` (`.seq`'s second half, at the store the prefix load
produces — `loadPrefixProg_reg0` supplies its register-`0` value). -/
lemma programBoundedIn_loadWordsProg (B : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : List Bool) (hB1 : 1 ≤ B)
    (h1p : p.eval 1 ≤ B) (hsp : p.eval (bits.length + 1) ≤ B)
    (hmp : bits.length * p.eval (bits.length + 1) ≤ B) (hspan : setupSpan p bits.length ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (bits.length + 1) ≤ B)
    (hmule : bits.length * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (bits.length + 1) ≤ B)
    (hpref30 : setupM p time d allowedIdx bits.length + generatorPrefOffset ≤ B)
    (hpref2b : 2 * bits.length + 1 ≤ B)
    (hkindsum : generatorPrefBase p time d allowedIdx bits.length + generatorPrefLen bits.length
      + 2 ≤ B)
    (harg1sum : generatorKindBase p time d allowedIdx bits.length + (d.table.length + 2) ≤ B)
    (harg2sum : generatorArg1Base p time d allowedIdx bits.length + (d.table.length + 2) ≤ B)
    (houtsum : generatorArg2Base p time d allowedIdx bits.length + (d.table.length + 2) ≤ B)
    (hloopBound : generatorPrefBase p time d allowedIdx bits.length + 2 * bits.length + 1 ≤ B)
    (htB : d.trueIdx ≤ B) (hfB : d.falseIdx ≤ B)
    (hkindSum : generatorKindBase p time d allowedIdx bits.length
      + (d.table.map transKind).length ≤ B)
    (harg1Sum : generatorArg1Base p time d allowedIdx bits.length
      + (d.table.map transArg1).length ≤ B)
    (harg2Sum : generatorArg2Base p time d allowedIdx bits.length
      + (d.table.map transArg2).length ≤ B)
    (houtSum : generatorOutBase p time d allowedIdx bits.length + outIdx.length ≤ B)
    (hkindVB : ∀ k, k < (d.table.map transKind).length → (d.table.map transKind).getD k 0 ≤ B)
    (harg1VB : ∀ k, k < (d.table.map transArg1).length → (d.table.map transArg1).getD k 0 ≤ B)
    (harg2VB : ∀ k, k < (d.table.map transArg2).length → (d.table.map transArg2).getD k 0 ≤ B)
    (houtVB : ∀ k, k < outIdx.length → outIdx.getD k 0 ≤ B) :
    ProgramBoundedIn B (bitInputStore bits) (loadWordsProg p time d allowedIdx outIdx) := by
  set N := bits.length with hN
  obtain ⟨hprefB, hkindB, harg1B, harg2B, houtB⟩ :=
    exprBoundedIn_loadWordsProg_bases B N p time d allowedIdx h1p hsp hmp hspan h1e hshifte hmule
      hpref30 hpref2b hkindsum harg1sum harg2sum houtsum
  have h0init : (bitInputStore bits) 0 = N := rfl
  unfold loadWordsProg
  refine ⟨programBoundedIn_loadPrefixProg B N p time d allowedIdx (bitInputStore bits) h0init
    hprefB hloopBound (by omega) htB hfB, ?_⟩
  have h0mid : (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) 0 = N :=
    loadPrefixProg_reg0 p time d allowedIdx bits
  exact programBoundedIn_loadConstWordsProg B N p time d allowedIdx outIdx _ h0mid hB1
    hkindB harg1B harg2B houtB hkindSum harg1Sum harg2Sum houtSum
    hkindVB harg1VB harg2VB houtVB

/-! ## Connecting to `envB`

The load stage writes `d.trueIdx`, `d.falseIdx`, the descriptor's table columns,
and `outIdx` directly into the store, so their values need explicit bounds.
`envK_ge_trueIdx` and `envK_ge_falseIdx` bound the two indices through
`prefixWord d bits`; `envIdxMax_ge_kind`, `_arg1`, `_arg2`, and `_ge_out` bound
the table columns and `outIdx`. -/

lemma falseIdx_mem_prefixWord (d : TableauDescriptor) (bits : List Bool) :
    d.falseIdx ∈ prefixWord d bits := by
  unfold prefixWord
  simp

lemma trueIdx_mem_prefixWord (d : TableauDescriptor) (b : Bool) (rest : List Bool) :
    d.trueIdx ∈ prefixWord d (b :: rest) := by
  rw [prefixWord_cons]
  simp

/-- `envIdxMax` sits inside `envKConst` additively, so its bound transports without unfolding
`envIdxMax` itself.  Keeping `envIdxMax d prefIdx allowedIdx outIdx` opaque avoids expanding the
recursively defined `descHaltStates` and `natInitSymbol`; unfolding only `envKConst` exposes the
additive structure needed by the proof. -/
lemma envIdxMax_le_envKConst (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) :
    envIdxMax d prefIdx allowedIdx outIdx ≤ envKConst d prefIdx allowedIdx outIdx := by
  unfold envKConst
  omega

/-- `envK` bounds `d.trueIdx` when `prefIdx = prefixWord d bits` for nonempty `bits`, since
`trueIdx` belongs to that prefix word. -/
lemma envK_ge_trueIdx (p time : Polynomial ℕ) (d : TableauDescriptor) (b : Bool) (rest : List Bool)
    (allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.trueIdx ≤ (envK p time d (prefixWord d (b :: rest)) allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h := envIdxMax_ge_pref (d := d) (prefIdx := prefixWord d (b :: rest))
    (allowedIdx := allowedIdx) (outIdx := outIdx) (trueIdx_mem_prefixWord d b rest)
  have hle := envIdxMax_le_envKConst d (prefixWord d (b :: rest)) allowedIdx outIdx
  omega

/-- `envK` bounds `d.falseIdx` for every `bits`, including `[]`, because the trailing separator is
always present in `prefixWord d bits`. -/
lemma envK_ge_falseIdx (p time : Polynomial ℕ) (d : TableauDescriptor) (bits : List Bool)
    (allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.falseIdx ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h := envIdxMax_ge_pref (d := d) (prefIdx := prefixWord d bits)
    (allowedIdx := allowedIdx) (outIdx := outIdx) (falseIdx_mem_prefixWord d bits)
  have hle := envIdxMax_le_envKConst d (prefixWord d bits) allowedIdx outIdx
  omega

/-- `loadWordsProg` stays bounded by `envB.eval N` on `bitInputStore bits`, at
`prefIdx = prefixWord d bits` matching the envelope's own indexing. Since `envK ≤ envB`
(`envB_ge_envK`), it suffices to majorize `trueIdx`/`falseIdx`/every table-column and `outIdx`
entry by `envK` — the caller's job, since it holds `d`/`outIdx` and can call `List.getD_eq_getElem`
+ `List.getElem_mem` + `envIdxMax_ge_kind`/`_arg1`/`_arg2`/`_ge_out` directly. -/
lemma programBoundedIn_loadWordsProg_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : List Bool)
    (htB : d.trueIdx ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval bits.length)
    (hfB : d.falseIdx ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval bits.length)
    (hkindVB : ∀ k, k < (d.table.map transKind).length →
      (d.table.map transKind).getD k 0 ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval
        bits.length)
    (harg1VB : ∀ k, k < (d.table.map transArg1).length →
      (d.table.map transArg1).getD k 0 ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval
        bits.length)
    (harg2VB : ∀ k, k < (d.table.map transArg2).length →
      (d.table.map transArg2).getD k 0 ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval
        bits.length)
    (houtVB : ∀ k, k < outIdx.length →
      outIdx.getD k 0 ≤ (envK p time d (prefixWord d bits) allowedIdx outIdx).eval bits.length) :
    ProgramBoundedIn (Polynomial.eval bits.length
        (envB p time d (prefixWord d bits) allowedIdx outIdx)) (bitInputStore bits)
      (loadWordsProg p time d allowedIdx outIdx) := by
  have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx bits.length
  apply programBoundedIn_loadWordsProg (Polynomial.eval bits.length
      (envB p time d (prefixWord d bits) allowedIdx outIdx)) p time d allowedIdx outIdx bits
  · have hK1 := envK_ge_one p time d (prefixWord d bits) allowedIdx outIdx bits.length; omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · have hspanM : setupSpan p bits.length ≤ setupM p time d allowedIdx bits.length := by
      unfold setupM setupSpan
      have h1 : (0 : ℕ) ≤ p.eval bits.length := Nat.zero_le _
      have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval bits.length := Nat.zero_le _
      nlinarith [sq_nonneg (2 * bits.length + 3 + p.eval bits.length)]
    have hK := envK_ge_setupM p time d (prefixWord d bits) allowedIdx outIdx bits.length
    omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · have hK := envK_eval_ge_setupM_add_70 p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorPrefOffset]
    omega
  · have hK := envK_ge_two_n p time d (prefixWord d bits) allowedIdx outIdx bits.length
    omega
  · have hK := envK_ge_kindBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorKindBase, generatorKindOffset, generatorPrefBase] at hK ⊢
    omega
  · have hK := envK_ge_arg1Base p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorArg1Base, generatorArg1Offset, generatorKindBase] at hK ⊢
    omega
  · have hK := envK_ge_arg2Base p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorArg2Base, generatorArg2Offset, generatorArg1Base] at hK ⊢
    omega
  · have hK := envK_ge_outBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorOutBase, generatorOutOffset, generatorArg2Base] at hK ⊢
    omega
  · have hK := envK_ge_kindBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorKindBase, generatorKindOffset, generatorPrefBase, generatorPrefLen] at hK ⊢
    omega
  · omega
  · omega
  · have hK := envK_ge_arg1Base p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorArg1Base, generatorArg1Offset, generatorKindBase, List.length_map] at hK ⊢
    omega
  · have hK := envK_ge_arg2Base p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorArg2Base, generatorArg2Offset, generatorArg1Base, List.length_map] at hK ⊢
    omega
  · have hK := envK_ge_outBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorOutBase, generatorOutOffset, generatorArg2Base, List.length_map] at hK ⊢
    omega
  · have hK := envK_ge_tableBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    simp only [generatorTableBase, generatorJmax, generatorOutOffset, generatorOutBase] at hK ⊢
    omega
  · intro k hk; have := hkindVB k hk; omega
  · intro k hk; have := harg1VB k hk; omega
  · intro k hk; have := harg2VB k hk; omega
  · intro k hk; have := houtVB k hk; omega

end NPComplete.CookLevin

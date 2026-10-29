module

public import NPComplete.CookLevin.ReductionProg.GeneratorScanFree

/-!
The core generator assumes the five staged words already sit in the store, so
the entry condition is unreachable from a raw input unless a load phase builds
them first.  Four of the five words are input-independent: the kind, arg1, and
arg2 columns are determined by the tableau descriptor, while the output index
list is a separate argument.  These four words contain compile-time constants,
so loading them needs no loop — one straight-line write per cell, exactly the
fixed-arity shape the rest of this development uses for array writes.

The address of every write is the expression `baseE + j - 1`, which depends on
register `0` only through `baseE`.  Since no written address equals zero (all
four bases sit far above the workspace origin), register `0` — hence
`baseE.eval` — is preserved at every step, and each write's address stays the
same through the whole chain.  That invariance is what lets later words leave
earlier ones intact: consecutive words are `length + 2` apart while occupying
`length + 1` cells, so one spare cell separates each pair.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open Polynomial

/-! ## One constant word as a straight line of writes -/

/-- Write the constant `v` into the cell at `baseE + j - 1`. -/
def constCellAssign (baseE : Expr) (j : ℕ) (v : ℕ) : Program :=
  .assignInd (.sub (.add baseE (.const j)) (.const 1)) (.const v)

lemma constCellAssign_eval_same (baseE : Expr) (j : ℕ) (v : ℕ) (σ : Store) :
    ((constCellAssign baseE j v).eval σ) (baseE.eval σ + j - 1) = v := by
  simp only [constCellAssign, eval_assignInd, Expr.eval, writeReg_same]

lemma constCellAssign_eval_diff (baseE : Expr) (j : ℕ) (v : ℕ) (σ : Store) (r : ℕ)
    (hr : r ≠ baseE.eval σ + j - 1) :
    ((constCellAssign baseE j v).eval σ) r = σ r := by
  simp only [constCellAssign, eval_assignInd, Expr.eval]
  exact writeReg_diff σ (baseE.eval σ + j - 1) v r hr

/-- The data writes: entry `i` of `xs` into cell `baseE + (j + i) - 1`. -/
def constCellsFrom (baseE : Expr) : ℕ → List ℕ → Program
  | _, [] => .skip
  | j, x :: xs => .seq (constCellAssign baseE j x) (constCellsFrom baseE (j + 1) xs)

lemma constCellsFrom_zero (hb : Reg0Expr baseE) (j : ℕ) (hj : 1 ≤ j) (xs : List ℕ)
    (σ : Store) (h1 : 1 ≤ baseE.eval σ) :
    ((constCellsFrom baseE j xs).eval σ) 0 = σ 0 := by
  induction xs generalizing σ j with
  | nil => simp [constCellsFrom]
  | cons x rest ih =>
      have hhead : ((constCellAssign baseE j x).eval σ) 0 = σ 0 :=
        constCellAssign_eval_diff baseE j x σ 0 (by omega)
      have h1' : 1 ≤ baseE.eval ((constCellAssign baseE j x).eval σ) := by
        rw [hb _ _ hhead]; exact h1
      have hnext := ih (j + 1) (by omega) ((constCellAssign baseE j x).eval σ) h1'
      simp only [constCellsFrom, eval_seq]
      rw [hnext, hhead]

lemma constCellsFrom_frame (hb : Reg0Expr baseE) (j : ℕ) (hj : 1 ≤ j) (xs : List ℕ)
    (σ : Store) (base r : ℕ) (hbase : baseE.eval σ = base) (h1 : 1 ≤ base)
    (hr : ∀ k, k < xs.length → r ≠ base + (j + k) - 1) :
    ((constCellsFrom baseE j xs).eval σ) r = σ r := by
  induction xs generalizing σ j base r with
  | nil => simp [constCellsFrom]
  | cons x rest ih =>
      have hhead := constCellAssign_eval_diff baseE j x σ r (by rw [hbase]; exact hr 0 (by simp))
      have hz : ((constCellAssign baseE j x).eval σ) 0 = σ 0 :=
        constCellAssign_eval_diff baseE j x σ 0 (by omega)
      have hbase' : baseE.eval ((constCellAssign baseE j x).eval σ) = base := by
        rw [hb _ _ hz, hbase]
      have hnext := ih (j + 1) (by omega)
        ((constCellAssign baseE j x).eval σ) base r hbase' h1
        (fun k hk => by
          intro hc
          exact hr (k + 1) (by simp [hk]) (by omega))
      simp only [constCellsFrom, eval_seq]
      rw [hnext, hhead]

lemma constCellsFrom_data (hb : Reg0Expr baseE) (j : ℕ) (hj : 1 ≤ j) (xs : List ℕ)
    (σ : Store) (base k : ℕ) (hbase : baseE.eval σ = base) (h1 : 1 ≤ base)
    (hk : k < xs.length) :
    ((constCellsFrom baseE j xs).eval σ) (base + (j + k) - 1) = xs.getD k 0 := by
  induction xs generalizing σ j base k with
  | nil => exact absurd hk (by simp)
  | cons x rest ih =>
      by_cases hk0 : k = 0
      · subst hk0
        have hz : ((constCellAssign baseE j x).eval σ) 0 = σ 0 :=
          constCellAssign_eval_diff baseE j x σ 0 (by omega)
        have hbase' : baseE.eval ((constCellAssign baseE j x).eval σ) = base := by
          rw [hb _ _ hz, hbase]
        have hfr : ((constCellsFrom baseE (j + 1) rest).eval
            ((constCellAssign baseE j x).eval σ)) (base + j - 1)
            = ((constCellAssign baseE j x).eval σ) (base + j - 1) := by
          refine constCellsFrom_frame hb (j + 1) (by omega) rest
            ((constCellAssign baseE j x).eval σ) base (base + j - 1) hbase' h1 ?_
          intro k' _
          omega
        have hhead := constCellAssign_eval_same baseE j x σ
        rw [hbase] at hhead
        simp only [constCellsFrom, eval_seq, Nat.add_zero]
        rw [hfr]
        simpa using hhead
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hz : ((constCellAssign baseE j x).eval σ) 0 = σ 0 :=
          constCellAssign_eval_diff baseE j x σ 0 (by omega)
        have hbase' : baseE.eval ((constCellAssign baseE j x).eval σ) = base := by
          rw [hb _ _ hz, hbase]
        have hnext := ih (j + 1) (by omega)
          ((constCellAssign baseE j x).eval σ) base k' hbase' h1
          (by simp at hk; omega)
        simp only [constCellsFrom, eval_seq]
        rw [show base + (j + (k' + 1)) - 1 = base + (j + 1 + k') - 1 from by omega]
        simpa using hnext

/-! ## One constant word -/

/-- Write the whole word `xs` at `baseE`: its length into `baseE - 1`, then each
entry `xs.getD k 0` into `baseE + k`.  Every value is a compile-time constant,
so the program is a straight line with `xs.length + 1` writes. -/
def writeConstWordProg (baseE : Expr) (xs : List ℕ) : Program :=
  .seq (constCellAssign baseE 0 xs.length) (constCellsFrom baseE 1 xs)

lemma writeConstWordProg_wordAt (hb : Reg0Expr baseE) (xs : List ℕ) (σ : Store)
    (base : ℕ) (hbase : baseE.eval σ = base) (h1 : 1 ≤ base)
    (h0 : σ 0 < base - 1) :
    WordAt ((writeConstWordProg baseE xs).eval σ) base xs := by
  have hz : ((constCellAssign baseE 0 xs.length).eval σ) 0 = σ 0 := by
    refine constCellAssign_eval_diff baseE 0 xs.length σ 0 ?_
    simp only [Nat.add_zero]
    rw [hbase]
    omega
  have hbase' : baseE.eval ((constCellAssign baseE 0 xs.length).eval σ) = base := by
    rw [hb _ _ hz, hbase]
  have hlen := constCellAssign_eval_same baseE 0 xs.length σ
  rw [hbase, Nat.add_zero] at hlen
  have hframe : ((constCellsFrom baseE 1 xs).eval ((constCellAssign baseE 0 xs.length).eval σ))
      (base - 1) = ((constCellAssign baseE 0 xs.length).eval σ) (base - 1) := by
    refine constCellsFrom_frame hb 1 (by omega) xs
      ((constCellAssign baseE 0 xs.length).eval σ) base (base - 1) hbase' h1 ?_
    intro k _
    omega
  have hdata := fun (k : ℕ) (hk : k < xs.length) =>
    constCellsFrom_data hb 1 (by omega) xs
      ((constCellAssign baseE 0 xs.length).eval σ) base k hbase' h1 hk
  unfold WordAt writeConstWordProg
  simp only [eval_seq]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hframe, hlen]
  · rw [show base + k = base + (1 + k) - 1 from by omega]
    exact hdata k hk

lemma writeConstWordProg_zero (hb : Reg0Expr baseE) (xs : List ℕ) (σ : Store)
    (base : ℕ) (hbase : baseE.eval σ = base) (h0 : σ 0 < base - 1) :
    ((writeConstWordProg baseE xs).eval σ) 0 = σ 0 := by
  have hz : ((constCellAssign baseE 0 xs.length).eval σ) 0 = σ 0 := by
    refine constCellAssign_eval_diff baseE 0 xs.length σ 0 ?_
    simp only [Nat.add_zero]
    rw [hbase]
    omega
  have hz' : 1 ≤ baseE.eval ((constCellAssign baseE 0 xs.length).eval σ) := by
    rw [hb _ _ hz, hbase]; omega
  have htail := constCellsFrom_zero hb 1 (by omega) xs
    ((constCellAssign baseE 0 xs.length).eval σ) hz'
  simp only [writeConstWordProg, eval_seq]
  rw [htail, hz]

lemma writeConstWordProg_frame (hb : Reg0Expr baseE) (xs : List ℕ) (σ : Store)
    (base r : ℕ) (hbase : baseE.eval σ = base) (h1 : 1 ≤ base)
    (h0 : σ 0 < base - 1)
    (hr : r < base - 1 ∨ base + xs.length ≤ r) :
    ((writeConstWordProg baseE xs).eval σ) r = σ r := by
  have hz : ((constCellAssign baseE 0 xs.length).eval σ) 0 = σ 0 := by
    refine constCellAssign_eval_diff baseE 0 xs.length σ 0 ?_
    simp only [Nat.add_zero]
    rw [hbase]
    omega
  have hbase' : baseE.eval ((constCellAssign baseE 0 xs.length).eval σ) = base := by
    rw [hb _ _ hz, hbase]
  have hhead := constCellAssign_eval_diff baseE 0 xs.length σ r (by
    simp only [Nat.add_zero]
    rw [hbase]
    rcases hr with hr | hr
    · intro hc; omega
    · intro hc; omega)
  have htail := constCellsFrom_frame hb 1 (by omega) xs
    ((constCellAssign baseE 0 xs.length).eval σ) base r hbase' h1 (fun k hk => by
      rcases hr with hr | hr
      · intro hc; omega
      · intro hc; omega)
  simp only [writeConstWordProg, eval_seq]
  rw [htail, hhead]

/-! ## The four constant words of the generator

Kind, arg1 and arg2 columns come from the descriptor's table; the fourth word
is the output index list.  The staged-word layout leaves `length + 2` cells
between consecutive bases while a word occupies its length cell plus `length`
data cells, so one spare cell separates each pair of words. -/

/-- Pure arithmetic of the staged-word gaps: consecutive bases are `L + 2`
apart with `L = d.table.length`, hence strictly increasing with room for the
whole word below the next base's length cell. -/
lemma generator_const_word_gaps (L : ℕ)
    (k a1 a2 o : ℕ)
    (hk : a1 = k + L + 2) (h1 : a2 = a1 + L + 2) (h2 : o = a2 + L + 2) :
    k + (L + 1) ≤ a1 ∧ a1 + (L + 1) ≤ a2 ∧ a2 + (L + 1) ≤ o := by
  omega

noncomputable def loadConstWordsProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind))
  (.seq (writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1))
  (.seq (writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2))
    (writeConstWordProg (generatorOutBaseE p time d allowedIdx) outIdx)))

/-! ## Correctness of the load phase -/

/-- The workspace base is at least `30`, hence each of the four staged-word
bases is at least `31`. -/
lemma generator_load_base_floor (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) :
    31 ≤ generatorKindBase p time d allowedIdx N ∧ 31 ≤ generatorArg1Base p time d allowedIdx N ∧
    31 ≤ generatorArg2Base p time d allowedIdx N ∧ 31 ≤ generatorOutBase p time d allowedIdx N := by
  simp only [generatorKindBase, generatorArg1Base, generatorArg2Base,
    generatorOutBase, generatorKindOffset, generatorArg1Offset,
    generatorArg2Offset, generatorOutOffset, generatorPrefOffset, generatorPrefLen]
  omega

/-- The four bases in increasing order, each word of length `L + 1` (its data
plus its length cell) fitting strictly below the next base. -/
lemma generator_load_base_order (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) :
    generatorKindBase p time d allowedIdx N + (d.table.length + 1) ≤ generatorArg1Base p time d allowedIdx N ∧
    generatorArg1Base p time d allowedIdx N + (d.table.length + 1) ≤ generatorArg2Base p time d allowedIdx N ∧
    generatorArg2Base p time d allowedIdx N + (d.table.length + 1) ≤ generatorOutBase p time d allowedIdx N := by
  have h := generator_const_word_gaps d.table.length
    (generatorKindBase p time d allowedIdx N) (generatorArg1Base p time d allowedIdx N)
    (generatorArg2Base p time d allowedIdx N) (generatorOutBase p time d allowedIdx N)
    (by simp [generatorKindBase, generatorArg1Base, generatorKindOffset,
      generatorArg1Offset, generatorPrefOffset, generatorPrefLen]; omega)
    (by simp [generatorArg1Base, generatorArg2Base, generatorArg1Offset,
      generatorArg2Offset]; omega)
    (by simp [generatorArg2Base, generatorOutBase, generatorArg2Offset,
      generatorOutOffset]; omega)
  simpa using h

/-- `setupM` cubes the span, which is at least `2N + 3`, so it strictly exceeds
`N` itself — the fact `omega` cannot see through the cube on its own. -/
lemma lt_setupM (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) (N : ℕ) :
    N < setupM p time d allowedIdx N := by
  unfold setupM setupSpan
  nlinarith [Nat.zero_le (p.eval N),
    Nat.zero_le ((emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval N)]

/-- Register `0` is preserved: it holds `N`, which is below every length cell
the writes target. -/
lemma loadConstWordsProg_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ((loadConstWordsProg p time d allowedIdx outIdx).eval σ) 0 = σ 0 := by
  have hlt := lt_setupM p time d allowedIdx N
  have hk0 : (generatorKindBaseE p time d allowedIdx).eval σ = generatorKindBase p time d allowedIdx N :=
    generator_kind_base_e_eval p time d allowedIdx σ N h0
  have hN1 : σ 0 < generatorKindBase p time d allowedIdx N - 1 := by
    rw [h0]; unfold generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset; omega
  have w1 := writeConstWordProg_zero (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ _ hk0 hN1
  have ha1 : (generatorArg1BaseE p time d allowedIdx).eval ((writeConstWordProg (generatorKindBaseE p time d allowedIdx)
      (d.table.map transKind)).eval σ) = generatorArg1Base p time d allowedIdx N :=
    generator_arg1_base_e_eval p time d allowedIdx _ N (by rw [w1, h0])
  have hN2 : ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ) 0
      < generatorArg1Base p time d allowedIdx N - 1 := by
    rw [w1, h0]
    unfold generatorArg1Base generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have w2 := writeConstWordProg_zero (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) _ _ ha1 hN2
  have ha2 : (generatorArg2BaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))
      = generatorArg2Base p time d allowedIdx N :=
    generator_arg2_base_e_eval p time d allowedIdx _ N (by rw [w2, w1, h0])
  have hN3 : ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
      ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)) 0
      < generatorArg2Base p time d allowedIdx N - 1 := by
    rw [w2, w1, h0]
    unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have w3 := writeConstWordProg_zero (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) _ _ ha2 hN3
  have ho : (generatorOutBaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
        ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
          ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)))
      = generatorOutBase p time d allowedIdx N :=
    generator_out_base_e_eval p time d allowedIdx _ N (by rw [w3, w2, w1, h0])
  have hN4 : ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))) 0
      < generatorOutBase p time d allowedIdx N - 1 := by
    rw [w3, w2, w1, h0]
    unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
      generatorKindOffset generatorPrefLen generatorPrefOffset
    omega
  have w4 := writeConstWordProg_zero (generator_out_base_e_reg0 p time d allowedIdx) outIdx _ _ ho hN4
  simp only [loadConstWordsProg, eval_seq]
  rw [w4, w3, w2, w1]

/-- A finished word survives a later constant word's writes: the two words'
regions are disjoint by `generator_load_base_order`, so `writeConstWordProg_frame`
leaves every cell of an earlier word untouched. -/
lemma writeConstWordProg_preserves_wordAt (baseE : Expr) (hb : Reg0Expr baseE)
    (xs : List ℕ) (σ : Store) (wbase : ℕ) (hbase : baseE.eval σ = wbase) (h1 : 1 ≤ wbase)
    (h0 : σ 0 < wbase - 1) (base : ℕ) (ys : List ℕ) (hw : WordAt σ base ys)
    (hsep : base + ys.length ≤ wbase - 1 ∨ wbase + xs.length ≤ base - 1) :
    WordAt ((writeConstWordProg baseE xs).eval σ) base ys := by
  obtain ⟨hlen, hdata⟩ := hw
  refine ⟨?_, fun k hk => ?_⟩
  · rw [writeConstWordProg_frame hb xs σ wbase (base - 1) hbase h1 h0 (by omega)]
    exact hlen
  · rw [writeConstWordProg_frame hb xs σ wbase (base + k) hbase h1 h0 (by omega)]
    exact hdata k hk

/-- The four staged words land exactly where the layout says, each surviving
every write that comes after it: `writeConstWordProg_wordAt` places a word the
moment its own write runs, and `writeConstWordProg_preserves_wordAt` (fed by
`generator_load_base_order`'s gaps) carries it through the remaining writes
unchanged. -/
lemma loadConstWordsProg_words (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    let τ := (loadConstWordsProg p time d allowedIdx outIdx).eval σ
    WordAt τ (generatorKindBase p time d allowedIdx N) (d.table.map transKind) ∧
    WordAt τ (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1) ∧
    WordAt τ (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2) ∧
    WordAt τ (generatorOutBase p time d allowedIdx N) outIdx := by
  have hlt := lt_setupM p time d allowedIdx N
  have hfloor := generator_load_base_floor p time d allowedIdx N
  have horder := generator_load_base_order p time d allowedIdx N
  have hlen1 : (d.table.map transKind).length = d.table.length := List.length_map ..
  have hlen2 : (d.table.map transArg1).length = d.table.length := List.length_map ..
  have hlen3 : (d.table.map transArg2).length = d.table.length := List.length_map ..
  -- Stage 1: kind
  have hk0 : (generatorKindBaseE p time d allowedIdx).eval σ = generatorKindBase p time d allowedIdx N :=
    generator_kind_base_e_eval p time d allowedIdx σ N h0
  have hN1 : σ 0 < generatorKindBase p time d allowedIdx N - 1 := by
    rw [h0]; unfold generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset; omega
  have hw1 := writeConstWordProg_wordAt (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ _ hk0 (by omega) hN1
  have w1 := writeConstWordProg_zero (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ _ hk0 hN1
  -- Stage 2: arg1
  have ha1 : (generatorArg1BaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)
      = generatorArg1Base p time d allowedIdx N :=
    generator_arg1_base_e_eval p time d allowedIdx _ N (by rw [w1, h0])
  have hN2 : ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ) 0
      < generatorArg1Base p time d allowedIdx N - 1 := by
    rw [w1, h0]
    unfold generatorArg1Base generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hw2 := writeConstWordProg_wordAt (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) _ _ ha1 (by omega) hN2
  have w2 := writeConstWordProg_zero (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) _ _ ha1 hN2
  have hw1' := writeConstWordProg_preserves_wordAt (generatorArg1BaseE p time d allowedIdx)
    (generator_arg1_base_e_reg0 p time d allowedIdx) (d.table.map transArg1) _ _ ha1 (by omega) hN2
    (generatorKindBase p time d allowedIdx N) (d.table.map transKind) hw1 (Or.inl (by omega))
  -- Stage 3: arg2
  have ha2 : (generatorArg2BaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))
      = generatorArg2Base p time d allowedIdx N :=
    generator_arg2_base_e_eval p time d allowedIdx _ N (by rw [w2, w1, h0])
  have hN3 : ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
      ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)) 0
      < generatorArg2Base p time d allowedIdx N - 1 := by
    rw [w2, w1, h0]
    unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hw3 := writeConstWordProg_wordAt (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) _ _ ha2 (by omega) hN3
  have w3 := writeConstWordProg_zero (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) _ _ ha2 hN3
  have hw1'' := writeConstWordProg_preserves_wordAt (generatorArg2BaseE p time d allowedIdx)
    (generator_arg2_base_e_reg0 p time d allowedIdx) (d.table.map transArg2) _ _ ha2 (by omega) hN3
    (generatorKindBase p time d allowedIdx N) (d.table.map transKind) hw1' (Or.inl (by omega))
  have hw2' := writeConstWordProg_preserves_wordAt (generatorArg2BaseE p time d allowedIdx)
    (generator_arg2_base_e_reg0 p time d allowedIdx) (d.table.map transArg2) _ _ ha2 (by omega) hN3
    (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1) hw2 (Or.inl (by omega))
  -- Stage 4: out
  have hoB : (generatorOutBaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
        ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
          ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)))
      = generatorOutBase p time d allowedIdx N :=
    generator_out_base_e_eval p time d allowedIdx _ N (by rw [w3, w2, w1, h0])
  have hN4 : ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))) 0
      < generatorOutBase p time d allowedIdx N - 1 := by
    rw [w3, w2, w1, h0]
    unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
      generatorKindOffset generatorPrefLen generatorPrefOffset
    omega
  have hw4 := writeConstWordProg_wordAt (generator_out_base_e_reg0 p time d allowedIdx)
    outIdx _ _ hoB (by omega) hN4
  have hw1''' := writeConstWordProg_preserves_wordAt (generatorOutBaseE p time d allowedIdx)
    (generator_out_base_e_reg0 p time d allowedIdx) outIdx _ _ hoB (by omega) hN4
    (generatorKindBase p time d allowedIdx N) (d.table.map transKind) hw1'' (Or.inl (by omega))
  have hw2'' := writeConstWordProg_preserves_wordAt (generatorOutBaseE p time d allowedIdx)
    (generator_out_base_e_reg0 p time d allowedIdx) outIdx _ _ hoB (by omega) hN4
    (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1) hw2' (Or.inl (by omega))
  have hw3' := writeConstWordProg_preserves_wordAt (generatorOutBaseE p time d allowedIdx)
    (generator_out_base_e_reg0 p time d allowedIdx) outIdx _ _ hoB (by omega) hN4
    (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2) hw3 (Or.inl (by omega))
  simp only [loadConstWordsProg, eval_seq]
  exact ⟨hw1''', hw2'', hw3', hw4⟩

/-- Everything strictly below the kind word's length cell survives the whole
load unchanged, which is what the input-bit region — sitting far below every
staged-word base — needs when chained with the prefix loader. -/
lemma loadConstWordsProg_preserves_below (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (N r : ℕ) (h0 : σ 0 = N)
    (hr : r < generatorKindBase p time d allowedIdx N - 1) :
    ((loadConstWordsProg p time d allowedIdx outIdx).eval σ) r = σ r := by
  have hlt := lt_setupM p time d allowedIdx N
  have hfloor := generator_load_base_floor p time d allowedIdx N
  have horder := generator_load_base_order p time d allowedIdx N
  -- Stage 1: kind
  have hk0 : (generatorKindBaseE p time d allowedIdx).eval σ = generatorKindBase p time d allowedIdx N :=
    generator_kind_base_e_eval p time d allowedIdx σ N h0
  have hN1 : σ 0 < generatorKindBase p time d allowedIdx N - 1 := by
    rw [h0]; unfold generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset; omega
  have hf1 := writeConstWordProg_frame (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ (generatorKindBase p time d allowedIdx N) r hk0 (by omega) hN1
    (Or.inl (by omega))
  have w1 := writeConstWordProg_zero (generator_kind_base_e_reg0 p time d allowedIdx)
    (d.table.map transKind) σ _ hk0 hN1
  -- Stage 2: arg1
  have ha1 : (generatorArg1BaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)
      = generatorArg1Base p time d allowedIdx N :=
    generator_arg1_base_e_eval p time d allowedIdx _ N (by rw [w1, h0])
  have hN2 : ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ) 0
      < generatorArg1Base p time d allowedIdx N - 1 := by
    rw [w1, h0]
    unfold generatorArg1Base generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hf2 := writeConstWordProg_frame (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) _ (generatorArg1Base p time d allowedIdx N) r ha1 (by omega) hN2
    (Or.inl (by omega))
  have w2 := writeConstWordProg_zero (generator_arg1_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg1) _ _ ha1 hN2
  -- Stage 3: arg2
  have ha2 : (generatorArg2BaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))
      = generatorArg2Base p time d allowedIdx N :=
    generator_arg2_base_e_eval p time d allowedIdx _ N (by rw [w2, w1, h0])
  have hN3 : ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
      ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)) 0
      < generatorArg2Base p time d allowedIdx N - 1 := by
    rw [w2, w1, h0]
    unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
      generatorPrefLen generatorPrefOffset
    omega
  have hf3 := writeConstWordProg_frame (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) _ (generatorArg2Base p time d allowedIdx N) r ha2 (by omega) hN3
    (Or.inl (by omega))
  have w3 := writeConstWordProg_zero (generator_arg2_base_e_reg0 p time d allowedIdx)
    (d.table.map transArg2) _ _ ha2 hN3
  -- Stage 4: out
  have hoB : (generatorOutBaseE p time d allowedIdx).eval
      ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
        ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
          ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ)))
      = generatorOutBase p time d allowedIdx N :=
    generator_out_base_e_eval p time d allowedIdx _ N (by rw [w3, w2, w1, h0])
  have hN4 : ((writeConstWordProg (generatorArg2BaseE p time d allowedIdx) (d.table.map transArg2)).eval
      ((writeConstWordProg (generatorArg1BaseE p time d allowedIdx) (d.table.map transArg1)).eval
        ((writeConstWordProg (generatorKindBaseE p time d allowedIdx) (d.table.map transKind)).eval σ))) 0
      < generatorOutBase p time d allowedIdx N - 1 := by
    rw [w3, w2, w1, h0]
    unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
      generatorKindOffset generatorPrefLen generatorPrefOffset
    omega
  have hf4 := writeConstWordProg_frame (generator_out_base_e_reg0 p time d allowedIdx)
    outIdx _ (generatorOutBase p time d allowedIdx N) r hoB (by omega) hN4 (Or.inl (by omega))
  simp only [loadConstWordsProg, eval_seq]
  rw [hf4, hf3, hf2, hf1]

/-! ## A descriptor with a non-constant table

`loadConstTestDescriptor` has a genuinely non-constant table — one `write` and
one `move` transition — so its three columns are not all equal. -/

/-- A test descriptor with a two-entry table: a `write` and a `move`
    transition, so the kind/arg1/arg2 columns are not all constant. -/
def loadConstTestDescriptor : TableauDescriptor :=
  { numStates := 0, startState := 0, numLetters := 0, blankIdx := 0
    falseIdx := 0, trueIdx := 1
    table := [NatTrans.write 2 1, NatTrans.move 3 Turing.Dir.right] }

end NPComplete.CookLevin

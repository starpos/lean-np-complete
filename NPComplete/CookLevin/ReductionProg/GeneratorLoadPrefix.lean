module

public import NPComplete.CookLevin.ReductionProg.GeneratorProg
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider

/-!
`generatorProg` assumes five words already sit in the store; it has no stage
that puts them there.  `tableWriterEntryUnreachable` (`Test/GeneratorBoundedWitnesses.lean`)
shows this concretely: on `bitInputStore bits`, the cell just below the
generator's own certificate-prefix base is provably `0`, forcing the prefix
word's declared length to `0` and contradicting the placement contract every
call site demands.

This file supplies the missing load stage for one of the five words: the
input-dependent certificate prefix.  The other four are input-independent:
the three transition-table columns are determined by `d`, and the output index
list is passed as a separate argument.  They are staged elsewhere.

The prefix the spec calls for is `((pairBits (enc x) []).map some).map
(execLetterIdx letterList)`.  Since `pairBits x [] = (x.flatMap fun b => [true,
b]) ++ [false]` (`Classes.lean`), each input bit doubles into two cells — an
always-`true` marker followed by the bit itself — with a trailing `false`
separator.  Composed with `execLetterIdx letterList`, `true` becomes
`d.trueIdx` and `false` becomes `d.falseIdx` (`descriptorOf`'s own definition of
those two fields), so the target word never mentions `letterList` or `Option
Bool` at all: it is built purely from the two descriptor scalars and the raw
bits.  `prefixWord_eq_pairBits_execLetterIdx` below is the bridge that makes
this precise.

The write loop mirrors that shape one bit at a time: for `i = 0, …, N-1` it
writes `d.trueIdx` at the even cell and `d.trueIdx`/`d.falseIdx` (by an `ifNZ`
on the input bit, never a truncated subtraction) at the odd cell, then appends
the trailing `d.falseIdx` and the length cell once the loop ends. The counter
that drives the loop lives in the store itself, at `generatorPrefBase - 2` —
two cells below the prefix's own length cell (`generatorPrefBase - 1`) — so no
fixed absolute register has to be reserved for it and the whole program stays a
single expression in `N` (register `0`), matching every other stage's
`Reg0Expr`-only discipline.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## The prefix word, and its equality with the spec's target -/

/-- The certificate-prefix word a producer must stage: each input bit `b`
    expands to `[d.trueIdx, if b then d.trueIdx else d.falseIdx]`, followed by
    a trailing `d.falseIdx` separator. -/
def prefixWord (d : TableauDescriptor) (bits : List Bool) : List ℕ :=
  bits.flatMap (fun b => [d.trueIdx, if b then d.trueIdx else d.falseIdx]) ++ [d.falseIdx]

lemma prefixWord_cons (d : TableauDescriptor) (b : Bool) (rest : List Bool) :
    prefixWord d (b :: rest)
      = d.trueIdx :: (if b then d.trueIdx else d.falseIdx) :: prefixWord d rest := by
  unfold prefixWord
  simp [List.flatMap_cons]

/-- `prefixWord` matches the spec's own target exactly, given the descriptor's
    two letter indices come from `execLetterIdx` on the same `letterList` the
    spec uses. This is the bridge `descTableauCNF_boundedCookLevinCNFMap_sat_iff_at_window`
    (`TableauVarRange.lean`) needs to accept a producer built from `prefixWord`. -/
lemma prefixWord_eq_pairBits_execLetterIdx (letterList : List (Option Bool))
    (bits : List Bool) (d : TableauDescriptor)
    (hf : d.falseIdx = execLetterIdx letterList (some false))
    (ht : d.trueIdx = execLetterIdx letterList (some true)) :
    prefixWord d bits = ((pairBits bits []).map some).map (execLetterIdx letterList) := by
  unfold prefixWord pairBits
  rw [List.map_map]
  simp only [List.append_nil]
  rw [List.map_append, List.map_flatMap]
  simp only [List.map_cons, List.map_nil]
  congr 1
  · apply List.flatMap_congr
    intro b _
    rcases b with _ | _ <;> simp [hf, ht]
  · simp [hf]

lemma prefixWord_getD_even (d : TableauDescriptor) (bits : List Bool) (i : ℕ)
    (hi : i < bits.length) : (prefixWord d bits).getD (2 * i) 0 = d.trueIdx := by
  induction bits generalizing i with
  | nil => simp at hi
  | cons b rest ih =>
      rw [prefixWord_cons]
      rcases i with _ | i
      · simp
      · simp only [List.length_cons] at hi
        have hi' : i < rest.length := by omega
        rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega]
        simpa [List.getD_cons_succ] using ih i hi'

lemma prefixWord_getD_odd (d : TableauDescriptor) (bits : List Bool) (i : ℕ)
    (hi : i < bits.length) :
    (prefixWord d bits).getD (2 * i + 1) 0
      = (if bits.getD i false then d.trueIdx else d.falseIdx) := by
  induction bits generalizing i with
  | nil => simp at hi
  | cons b rest ih =>
      rw [prefixWord_cons]
      rcases i with _ | i
      · simp
      · simp only [List.length_cons] at hi
        have hi' : i < rest.length := by omega
        rw [show 2 * (i + 1) + 1 = (2 * i + 1 + 1) + 1 by omega]
        simpa [List.getD_cons_succ] using ih i hi'

/-- A boolean's `0`/`1` indicator drives an `ifNZ` exactly the way the boolean
    itself would drive an `if` — the bridge `loadPrefixStep_eval`'s `ifNZ` on
    an input-bit cell needs to line up with `prefixWord`'s own `if b then ⋯`. -/
lemma ifNZ_of_bool_indicator (b : Bool) (x y : ℕ) :
    (if (if b then (1 : ℕ) else 0) ≠ 0 then x else y) = (if b then x else y) := by
  by_cases hb : b <;> simp

lemma prefixWord_getD_last (d : TableauDescriptor) (bits : List Bool) :
    (prefixWord d bits).getD (2 * bits.length) 0 = d.falseIdx := by
  induction bits with
  | nil => simp [prefixWord]
  | cons b rest ih =>
      rw [prefixWord_cons]
      simp only [List.length_cons]
      rw [show 2 * (rest.length + 1) = (2 * rest.length + 1) + 1 by omega]
      simpa [List.getD_cons_succ] using ih

/-- `prefixWord`'s length matches `generatorPrefLen`, the length the generator's
    own layout reserves for this word. -/
lemma prefixWord_length (d : TableauDescriptor) (bits : List Bool) :
    (prefixWord d bits).length = 2 * bits.length + 1 := by
  unfold prefixWord
  simp [List.length_flatMap]
  omega

/-! ## The write loop -/

/-- `setupM p time d allowedIdx N` strictly exceeds `N + 2`: the workspace base
    always clears the input region by at least three cells, room for the
    prefix's counter cell, length cell, and first data cell. -/
lemma generatorPrefBase_ge (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) :
    N + 3 ≤ generatorPrefBase p time d allowedIdx N := by
  unfold generatorPrefBase generatorPrefOffset setupM setupSpan
  set s := 2 * N + 3 + p.eval N with hs
  have h1 : N + 3 ≤ s := by omega
  have h2 : (1 : ℕ) ≤ s := by omega
  nlinarith [sq_nonneg s, h2,
    Nat.zero_le ((emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval N)]

/-- The loop counter lives two cells below the prefix's own length cell, so it
    needs no fixed absolute register. -/
noncomputable def loadPrefixCounterE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .sub (generatorPrefBaseE p time d allowedIdx) (.const 2)

lemma loadPrefixCounterE_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) (σ : Store) (h0 : σ 0 = N) :
    (loadPrefixCounterE p time d allowedIdx).eval σ
      = generatorPrefBase p time d allowedIdx N - 2 := by
  simp only [loadPrefixCounterE, Expr.eval]
  rw [generator_pref_base_e_eval p time d allowedIdx σ N h0]

noncomputable def loadPrefixCounterCell (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .regInd (loadPrefixCounterE p time d allowedIdx)

lemma loadPrefixCounterCell_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) (σ : Store) (h0 : σ 0 = N) :
    (loadPrefixCounterCell p time d allowedIdx).eval σ
      = σ (generatorPrefBase p time d allowedIdx N - 2) := by
  simp only [loadPrefixCounterCell, Expr.eval]
  rw [loadPrefixCounterE_eval p time d allowedIdx N σ h0]

/-- The address the current iteration writes: `generatorPrefBase + 2 * counter`. -/
noncomputable def loadPrefixWriteAddrE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .add (generatorPrefBaseE p time d allowedIdx)
    (.mul (.const 2) (loadPrefixCounterCell p time d allowedIdx))

lemma loadPrefixWriteAddrE_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N i : ℕ) (σ : Store) (h0 : σ 0 = N)
    (hi : σ (generatorPrefBase p time d allowedIdx N - 2) = i) :
    (loadPrefixWriteAddrE p time d allowedIdx).eval σ
      = generatorPrefBase p time d allowedIdx N + 2 * i := by
  simp only [loadPrefixWriteAddrE, Expr.eval]
  rw [generator_pref_base_e_eval p time d allowedIdx σ N h0,
    loadPrefixCounterCell_eval p time d allowedIdx N σ h0, hi]

/-- The current iteration's input bit, read at cell `counter + 1`. -/
noncomputable def loadPrefixTestE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .regInd (.add (.const 1) (loadPrefixCounterCell p time d allowedIdx))

lemma loadPrefixTestE_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N i : ℕ) (σ : Store) (h0 : σ 0 = N)
    (hi : σ (generatorPrefBase p time d allowedIdx N - 2) = i) :
    (loadPrefixTestE p time d allowedIdx).eval σ = σ (i + 1) := by
  simp only [loadPrefixTestE, Expr.eval]
  rw [loadPrefixCounterCell_eval p time d allowedIdx N σ h0, hi]
  congr 1
  omega

/-- One iteration: write `d.trueIdx` at the even cell, `d.trueIdx`/`d.falseIdx`
    (by `ifNZ` on the input bit) at the odd cell, then bump the counter. -/
noncomputable def loadPrefixStep (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Program :=
  .seq
    (.assignInd (loadPrefixWriteAddrE p time d allowedIdx) (.const d.trueIdx))
    (.seq
      (.ifNZ (loadPrefixTestE p time d allowedIdx)
        (.assignInd (.add (loadPrefixWriteAddrE p time d allowedIdx) (.const 1)) (.const d.trueIdx))
        (.assignInd (.add (loadPrefixWriteAddrE p time d allowedIdx) (.const 1)) (.const d.falseIdx)))
      (.assignInd (loadPrefixCounterE p time d allowedIdx)
        (.add (loadPrefixCounterCell p time d allowedIdx) (.const 1))))

/-- One iteration's exact effect, given register `0` holds `N` and the counter
    cell holds `i` before the step: it writes the two cells at `base + 2i` and
    bumps the counter to `i + 1`, leaving everything else alone. -/
lemma loadPrefixStep_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N i : ℕ) (τ : Store)
    (h0 : τ 0 = N) (hi : τ (generatorPrefBase p time d allowedIdx N - 2) = i) :
    (loadPrefixStep p time d allowedIdx).eval τ
      = writeReg
          (writeReg
            (writeReg τ (generatorPrefBase p time d allowedIdx N + 2 * i) d.trueIdx)
            (generatorPrefBase p time d allowedIdx N + 2 * i + 1)
            (if τ (i + 1) ≠ 0 then d.trueIdx else d.falseIdx))
          (generatorPrefBase p time d allowedIdx N - 2) (i + 1) := by
  have hb := generatorPrefBase_ge p time d allowedIdx N
  have step1 : (Program.assignInd (loadPrefixWriteAddrE p time d allowedIdx)
      (Expr.const d.trueIdx)).eval τ
      = writeReg τ (generatorPrefBase p time d allowedIdx N + 2 * i) d.trueIdx := by
    rw [eval_assignInd]
    congr 1
    exact loadPrefixWriteAddrE_eval p time d allowedIdx N i τ h0 hi
  unfold loadPrefixStep
  rw [eval_seq, step1]
  set σ1 : Store := writeReg τ (generatorPrefBase p time d allowedIdx N + 2 * i) d.trueIdx
    with hσ1def
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def]; rw [writeReg_diff τ _ d.trueIdx 0 (by omega)]; exact h0
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = i := by
    rw [hσ1def]
    rw [writeReg_diff τ _ d.trueIdx (generatorPrefBase p time d allowedIdx N - 2) (by omega)]
    exact hi
  have hσ1i1 : σ1 (i + 1) = τ (i + 1) := by
    rw [hσ1def]; apply writeReg_diff; omega
  have step2 : (Program.ifNZ (loadPrefixTestE p time d allowedIdx)
      (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.trueIdx))
      (Program.assignInd (Expr.add (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const 1))
        (Expr.const d.falseIdx))).eval σ1
      = writeReg σ1 (generatorPrefBase p time d allowedIdx N + 2 * i + 1)
          (if τ (i + 1) ≠ 0 then d.trueIdx else d.falseIdx) := by
    rw [eval_ifNZ, loadPrefixTestE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr, hσ1i1]
    by_cases hbitv : τ (i + 1) ≠ 0
    · rw [ite_eq_left hbitv, ite_eq_left hbitv, eval_assignInd]
      congr 1
      simp only [Expr.eval]
      rw [loadPrefixWriteAddrE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr]
    · rw [ite_eq_right hbitv, ite_eq_right hbitv, eval_assignInd]
      congr 1
      simp only [Expr.eval]
      rw [loadPrefixWriteAddrE_eval p time d allowedIdx N i σ1 hσ1_0 hσ1_ctr]
  rw [eval_seq, step2]
  set σ2 : Store := writeReg σ1 (generatorPrefBase p time d allowedIdx N + 2 * i + 1)
    (if τ (i + 1) ≠ 0 then d.trueIdx else d.falseIdx) with hσ2def
  have hσ2_0 : σ2 0 = N := by
    rw [hσ2def]; rw [writeReg_diff σ1 _ _ 0 (by omega)]; exact hσ1_0
  have hσ2_ctr : σ2 (generatorPrefBase p time d allowedIdx N - 2) = i := by
    rw [hσ2def]
    rw [writeReg_diff σ1 _ _ (generatorPrefBase p time d allowedIdx N - 2) (by omega)]
    exact hσ1_ctr
  rw [eval_assignInd]
  congr 1
  · exact loadPrefixCounterE_eval p time d allowedIdx N σ2 hσ2_0
  · simp only [Expr.eval]
    rw [loadPrefixCounterCell_eval p time d allowedIdx N σ2 hσ2_0, hσ2_ctr]

/-- After `n` iterations (`n ≤ N`): register `0` and cells below the counter
    (in particular the whole input region) are unchanged from the loop's own
    entry store, the counter cell reads `n`, and the first `2n` prefix cells
    already hold `prefixWord`'s first `2n` entries. Generalizing the length
    bound to `n ≤ N` (rather than fixing `n = N`) is what lets the induction
    peel one iteration at a time via `loopEval_succ_snoc`. -/
lemma load_prefix_loop_inv (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (N : ℕ) (bits : List Bool)
    (hbits : bits.length = N) (σ : Store) (h0 : σ 0 = N)
    (hσctr : σ (generatorPrefBase p time d allowedIdx N - 2) = 0)
    (hinput : ∀ i, i < N → σ (i + 1) = if bits.getD i false then 1 else 0) :
    ∀ n, n ≤ N →
      (loopEval (loadPrefixStep p time d allowedIdx) n σ) 0 = N ∧
      (loopEval (loadPrefixStep p time d allowedIdx) n σ)
        (generatorPrefBase p time d allowedIdx N - 2) = n ∧
      (∀ q, q < 2 * n →
        (loopEval (loadPrefixStep p time d allowedIdx) n σ)
          (generatorPrefBase p time d allowedIdx N + q)
          = (prefixWord d bits).getD q 0) ∧
      (∀ r, r < generatorPrefBase p time d allowedIdx N - 2 →
        (loopEval (loadPrefixStep p time d allowedIdx) n σ) r = σ r) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [loopEval_zero]
      refine ⟨h0, hσctr, ?_, ?_⟩
      · intro q hq; omega
      · intro r _; rfl
  | succ n ih =>
      intro hnN
      obtain ⟨ih0, ihctr, ihword, ihframe⟩ := ih (by omega)
      rw [loopEval_succ_snoc]
      set s := loopEval (loadPrefixStep p time d allowedIdx) n σ with hsdef
      have hnN' : n < N := by omega
      have hstep := loadPrefixStep_eval p time d allowedIdx N n s ih0 ihctr
      have hb := generatorPrefBase_ge p time d allowedIdx N
      have hbinp : s (n + 1) = if bits.getD n false then 1 else 0 := by
        rw [ihframe (n + 1) (by omega)]
        exact hinput n hnN'
      have hnbits : n < bits.length := by rw [hbits]; exact hnN'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hstep]
        rw [writeReg_diff _ _ _ 0 (by omega), writeReg_diff _ _ _ 0 (by omega),
          writeReg_diff _ _ _ 0 (by omega)]
        exact ih0
      · rw [hstep]
        rw [writeReg_same]
      · intro q hq
        rw [hstep]
        by_cases hq2n : q < 2 * n
        · rw [writeReg_diff _ _ _ _ (by omega), writeReg_diff _ _ _ _ (by omega),
            writeReg_diff _ _ _ _ (by omega)]
          exact ihword q hq2n
        · have hqcases : q = 2 * n ∨ q = 2 * n + 1 := by omega
          rcases hqcases with hq0 | hq1
          · subst hq0
            rw [writeReg_diff _ _ _ _ (by omega), writeReg_diff _ _ _ _ (by omega), writeReg_same]
            rw [prefixWord_getD_even d bits n hnbits]
          · subst hq1
            rw [show generatorPrefBase p time d allowedIdx N + (2 * n + 1)
                = generatorPrefBase p time d allowedIdx N + 2 * n + 1 by
              ring]
            rw [writeReg_diff _ _ _ _ (by omega), writeReg_same]
            rw [prefixWord_getD_odd d bits n hnbits]
            rw [hbinp, ifNZ_of_bool_indicator]
      · intro r hr
        rw [hstep]
        rw [writeReg_diff _ _ _ r (by omega), writeReg_diff _ _ _ r (by omega),
          writeReg_diff _ _ _ r (by omega)]
        exact ihframe r hr

/-- The cell holding the prefix's length, `generatorPrefBase - 1`. -/
noncomputable def loadPrefixLenAddrE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .sub (generatorPrefBaseE p time d allowedIdx) (.const 1)

/-- Zero the counter, run the loop for `N` (register `0`) iterations, then
    append the trailing `falseIdx` separator and write the length cell. -/
noncomputable def loadPrefixProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Program :=
  .seq
    (.assignInd (loadPrefixCounterE p time d allowedIdx) (.const 0))
    (.seq
      (.forN (.reg 0) (loadPrefixStep p time d allowedIdx))
      (.seq
        (.assignInd (loadPrefixWriteAddrE p time d allowedIdx) (.const d.falseIdx))
        (.assignInd (loadPrefixLenAddrE p time d allowedIdx) generatorPrefLenE)))

/-! ## Main correctness -/

/-- `loadPrefixProg` stages `prefixWord d bits` at the generator's own prefix
    base, on the canonical loader `bitInputStore`. -/
lemma loadPrefixProg_wordAt (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (bits : List Bool) :
    WordAt ((loadPrefixProg p time d allowedIdx).eval (bitInputStore bits))
      (generatorPrefBase p time d allowedIdx bits.length) (prefixWord d bits) := by
  set N := bits.length with hN
  have hb := generatorPrefBase_ge p time d allowedIdx N
  have h0init : (bitInputStore bits) 0 = N := rfl
  unfold loadPrefixProg
  rw [eval_seq, eval_assignInd]
  set σ1 : Store := writeReg (bitInputStore bits)
    ((loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits))
    ((Expr.const 0).eval (bitInputStore bits)) with hσ1def
  have haddr1 : (loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits)
      = generatorPrefBase p time d allowedIdx N - 2 :=
    loadPrefixCounterE_eval p time d allowedIdx N (bitInputStore bits) h0init
  have hval1 : (Expr.const (0 : ℕ)).eval (bitInputStore bits) = 0 := rfl
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 0 (by omega)]
    exact h0init
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ1def, haddr1, hval1, writeReg_same]
  have hσ1_input : ∀ i, i < N → σ1 (i + 1) = if bits.getD i false then 1 else 0 := by
    intro i hi
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 (i + 1) (by omega)]
    show (if bits.getD i false then 1 else 0) = _
    rfl
  rw [eval_seq, eval_forN]
  simp only [Expr.eval]
  rw [hσ1_0]
  set result : Store := loopEval (loadPrefixStep p time d allowedIdx) N σ1 with hresultdef
  obtain ⟨hres0, hresctr, hresword, hresframe⟩ :=
    load_prefix_loop_inv p time d allowedIdx N bits hN σ1 hσ1_0 hσ1_ctr hσ1_input N (le_refl N)
  rw [eval_seq]
  simp only [eval_assignInd]
  have haddr3 : (loadPrefixWriteAddrE p time d allowedIdx).eval result
      = generatorPrefBase p time d allowedIdx N + 2 * N :=
    loadPrefixWriteAddrE_eval p time d allowedIdx N N result hres0 hresctr
  have hval3 : (Expr.const d.falseIdx).eval result = d.falseIdx := rfl
  rw [haddr3, hval3]
  set σ3 : Store := writeReg result (generatorPrefBase p time d allowedIdx N + 2 * N) d.falseIdx
    with hσ3def
  have hσ3_0 : σ3 0 = N := by
    rw [hσ3def, writeReg_diff result _ _ 0 (by omega)]
    exact hres0
  have haddr4 : (loadPrefixLenAddrE p time d allowedIdx).eval σ3
      = generatorPrefBase p time d allowedIdx N - 1 := by
    unfold loadPrefixLenAddrE
    simp only [Expr.eval]
    rw [generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0]
  have hval4 : generatorPrefLenE.eval σ3 = 2 * N + 1 := by
    rw [generator_pref_len_e_eval σ3 N hσ3_0]
    unfold generatorPrefLen
    ring
  rw [haddr4, hval4]
  constructor
  · rw [writeReg_same]
    rw [prefixWord_length]
  · intro k hk
    rw [prefixWord_length] at hk
    rw [writeReg_diff _ _ _ _ (by omega)]
    by_cases hk2N : k < 2 * N
    · rw [hσ3def]
      rw [writeReg_diff _ _ _ _ (by omega)]
      exact hresword k hk2N
    · have hkeq : k = 2 * N := by omega
      subst hkeq
      rw [hσ3def, writeReg_same]
      rw [prefixWord_getD_last]

/-! ## Frame: register `0` and the input region survive -/

/-- Register `0` (the input length) is never written by `loadPrefixProg`. -/
lemma loadPrefixProg_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (bits : List Bool) :
    (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) 0 = bits.length := by
  set N := bits.length with hN
  have hb := generatorPrefBase_ge p time d allowedIdx N
  have h0init : (bitInputStore bits) 0 = N := rfl
  unfold loadPrefixProg
  rw [eval_seq, eval_assignInd]
  set σ1 : Store := writeReg (bitInputStore bits)
    ((loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits))
    ((Expr.const 0).eval (bitInputStore bits)) with hσ1def
  have haddr1 : (loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits)
      = generatorPrefBase p time d allowedIdx N - 2 :=
    loadPrefixCounterE_eval p time d allowedIdx N (bitInputStore bits) h0init
  have hval1 : (Expr.const (0 : ℕ)).eval (bitInputStore bits) = 0 := rfl
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 0 (by omega)]
    exact h0init
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ1def, haddr1, hval1, writeReg_same]
  have hσ1_input : ∀ i, i < N → σ1 (i + 1) = if bits.getD i false then 1 else 0 := by
    intro i hi
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 (i + 1) (by omega)]
    show (if bits.getD i false then 1 else 0) = _
    rfl
  rw [eval_seq, eval_forN]
  simp only [Expr.eval]
  rw [hσ1_0]
  set result : Store := loopEval (loadPrefixStep p time d allowedIdx) N σ1 with hresultdef
  obtain ⟨hres0, hresctr, _, _⟩ :=
    load_prefix_loop_inv p time d allowedIdx N bits hN σ1 hσ1_0 hσ1_ctr hσ1_input N (le_refl N)
  rw [eval_seq]
  simp only [eval_assignInd]
  have haddr3 : (loadPrefixWriteAddrE p time d allowedIdx).eval result
      = generatorPrefBase p time d allowedIdx N + 2 * N :=
    loadPrefixWriteAddrE_eval p time d allowedIdx N N result hres0 hresctr
  have hval3 : (Expr.const d.falseIdx).eval result = d.falseIdx := rfl
  rw [haddr3, hval3]
  set σ3 : Store := writeReg result (generatorPrefBase p time d allowedIdx N + 2 * N) d.falseIdx
    with hσ3def
  have hσ3_0 : σ3 0 = N := by
    rw [hσ3def, writeReg_diff result _ _ 0 (by omega)]
    exact hres0
  have haddr4 : (loadPrefixLenAddrE p time d allowedIdx).eval σ3
      = generatorPrefBase p time d allowedIdx N - 1 := by
    unfold loadPrefixLenAddrE
    simp only [Expr.eval]
    rw [generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0]
  rw [haddr4]
  rw [writeReg_diff _ _ _ 0 (by omega)]
  exact hσ3_0

/-- Every input cell `1 .. N` survives `loadPrefixProg` unchanged: the loop
    only ever touches the prefix region `generatorPrefBase - 2 ..
    generatorPrefBase + 2N`, which sits strictly above the input by
    `generatorPrefBase_ge`. -/
lemma loadPrefixProg_input_frame (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (bits : List Bool)
    (i : ℕ) (hi : i < bits.length) :
    (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) (i + 1)
      = bitInputStore bits (i + 1) := by
  set N := bits.length with hN
  have hb := generatorPrefBase_ge p time d allowedIdx N
  have h0init : (bitInputStore bits) 0 = N := rfl
  unfold loadPrefixProg
  rw [eval_seq, eval_assignInd]
  set σ1 : Store := writeReg (bitInputStore bits)
    ((loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits))
    ((Expr.const 0).eval (bitInputStore bits)) with hσ1def
  have haddr1 : (loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits)
      = generatorPrefBase p time d allowedIdx N - 2 :=
    loadPrefixCounterE_eval p time d allowedIdx N (bitInputStore bits) h0init
  have hval1 : (Expr.const (0 : ℕ)).eval (bitInputStore bits) = 0 := rfl
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 0 (by omega)]
    exact h0init
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ1def, haddr1, hval1, writeReg_same]
  have hσ1_input : ∀ j, j < N → σ1 (j + 1) = if bits.getD j false then 1 else 0 := by
    intro j hj
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 (j + 1) (by omega)]
    show (if bits.getD j false then 1 else 0) = _
    rfl
  have hσ1_i1 : σ1 (i + 1) = bitInputStore bits (i + 1) := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 (i + 1) (by omega)]
  rw [eval_seq, eval_forN]
  simp only [Expr.eval]
  rw [hσ1_0]
  set result : Store := loopEval (loadPrefixStep p time d allowedIdx) N σ1 with hresultdef
  obtain ⟨hres0, hresctr, _, hresframe⟩ :=
    load_prefix_loop_inv p time d allowedIdx N bits hN σ1 hσ1_0 hσ1_ctr hσ1_input N (le_refl N)
  have hresi1 : result (i + 1) = σ1 (i + 1) := hresframe (i + 1) (by omega)
  rw [eval_seq]
  simp only [eval_assignInd]
  have haddr3 : (loadPrefixWriteAddrE p time d allowedIdx).eval result
      = generatorPrefBase p time d allowedIdx N + 2 * N :=
    loadPrefixWriteAddrE_eval p time d allowedIdx N N result hres0 hresctr
  have hval3 : (Expr.const d.falseIdx).eval result = d.falseIdx := rfl
  rw [haddr3, hval3]
  set σ3 : Store := writeReg result (generatorPrefBase p time d allowedIdx N + 2 * N) d.falseIdx
    with hσ3def
  have hσ3_i1 : σ3 (i + 1) = result (i + 1) := by
    rw [hσ3def, writeReg_diff result _ _ (i + 1) (by omega)]
  have hσ3_0 : σ3 0 = N := by
    rw [hσ3def, writeReg_diff result _ _ 0 (by omega)]
    exact hres0
  have haddr4 : (loadPrefixLenAddrE p time d allowedIdx).eval σ3
      = generatorPrefBase p time d allowedIdx N - 1 := by
    unfold loadPrefixLenAddrE
    simp only [Expr.eval]
    rw [generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0]
  rw [haddr4]
  rw [writeReg_diff _ _ _ (i + 1) (by omega)]
  rw [hσ3_i1, hresi1, hσ1_i1]

end NPComplete.CookLevin

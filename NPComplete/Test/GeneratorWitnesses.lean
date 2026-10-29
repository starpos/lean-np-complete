module

public import NPComplete.CookLevin.ReductionProg.GeneratorCost
public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelopeAgg
public import NPComplete.CookLevin.ReductionProg.GeneratorLoad
public import NPComplete.CookLevin.ReductionProg.GeneratorLoadConst
public import NPComplete.CookLevin.ReductionProg.GeneratorLoadPrefix

/-!
These checks run the generator's loader, cost bound and envelopes on concrete inputs
(`[true, false, true]`, a two-entry table), where the general statements are only proved over
abstract parameters. They show that the statements apply to an actual run and name the cells it
produces. No main construction uses them, so they stay outside the consumer-facing umbrella.
-/

@[expose] public section

namespace NPComplete.CookLevin

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

example :
    ∃ c, (generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]).cost
        (bitInputStore [true, false, true]) ≤
      c * ([true, false, true].length + 1) ^ c := by
  obtain ⟨c, h⟩ := generatorProgFromBits_cost_le_input_power
    0 0 loadConstTestDescriptor [] [5, 7, 9]
  exact ⟨c, h [true, false, true]⟩

end

section
open Polynomial
open NPComplete.RAMToTM

/-! ## Non-vacuity: the four envelopes at one concrete instance

At `p = time = X`, `d = initCheckDesc`, `prefIdx = replicate 7 0`,
`allowedIdx = outIdx = [0]`, `N = 3`, the four evaluations are four distinct
numbers in the order `K < wid < S ≤ B` — the nesting is real, not collapsed
onto one value. -/

lemma aggInstanceK :
    Polynomial.eval 3 (envK Polynomial.X Polynomial.X initCheckDesc
      (List.replicate (generatorPrefLen 3) 0) [0] [0]) = 1847750849 := by
  rw [envK_eval]
  have h1 : setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0] 3
      = 1847750595 := by
    unfold setupM setupSpan
    simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  have h2 : ((cookWindowPoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 32 := by
    rw [cookWindowPoly_eval]; simp
  have h3 : ((timePoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 10 := by
    simp [timePoly_eval]
  have h4 : envKConst initCheckDesc (List.replicate (generatorPrefLen 3) 0) [0] [0] = 211 := by
    unfold envKConst envIdxMax generatorPrefLen initCheckDesc
    simp [descHaltStates, natInitSymbol, TableauDescriptor.entry, transKind, transArg1,
      transArg2, List.range]
    decide
  omega

lemma aggInstanceWid :
    Polynomial.eval 3 (envWid Polynomial.X Polynomial.X initCheckDesc
      (List.replicate (generatorPrefLen 3) 0) [0] [0]) = 794878548207028710800156466174 := by
  rw [envWid_eval, aggInstanceK]
  have hwc : envWidConst initCheckDesc [0] = 126 := by
    unfold envWidConst initCheckDesc
    norm_num
  rw [hwc]

lemma aggInstanceS :
    Polynomial.eval 3 (envS Polynomial.X Polynomial.X initCheckDesc
      (List.replicate (generatorPrefLen 3) 0) [0] [0]) = 794878548207028710802004218105 := by
  rw [envS_eval, aggInstanceK, aggInstanceWid, varBoundPoly_eval]
  have h2 : ((cookWindowPoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 32 := by
    rw [cookWindowPoly_eval]; simp
  have h3 : ((timePoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 10 := by
    simp [timePoly_eval]
  have hn : (initCheckDesc.numStates + 1 : ℕ) = 2 := rfl
  have hm : (initCheckDesc.numLetters + 1 : ℕ) = 2 := rfl
  simp only [hn, hm, h2, h3]

lemma aggInstanceB :
    Polynomial.eval 3 (envB Polynomial.X Polynomial.X initCheckDesc
      (List.replicate (generatorPrefLen 3) 0) [0] [0]) = 794878548230927993233066615887 := by
  rw [envB_eval, aggInstanceS, aggInstanceK]
  have h1 : setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0] 3
      = 1847750595 := by
    unfold setupM setupSpan
    simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  have h2 : ((cookWindowPoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 32 := by
    rw [cookWindowPoly_eval]; simp
  have h3 : ((timePoly Polynomial.X Polynomial.X).eval 3 : ℕ) = 10 := by
    simp [timePoly_eval]
  have h4 : ((cookWindowPoly Polynomial.X Polynomial.X).eval 4 : ℕ) = 41 := by
    rw [cookWindowPoly_eval]; simp
  have h5 : ((timePoly Polynomial.X Polynomial.X).eval 4 : ℕ) = 13 := by
    simp [timePoly_eval]
  have h6 : ((cookWindowPoly Polynomial.X Polynomial.X).eval 1 : ℕ) = 14 := by
    rw [cookWindowPoly_eval]; simp
  have h7 : ((timePoly Polynomial.X Polynomial.X).eval 1 : ℕ) = 4 := by
    simp [timePoly_eval]
  have hm : (initCheckDesc.numLetters : ℕ) = 1 := rfl
  have h4' : ((cookWindowPoly Polynomial.X Polynomial.X).eval (3 + 1) : ℕ) = 41 := by
    rw [cookWindowPoly_eval]; simp
  have h5' : ((timePoly Polynomial.X Polynomial.X).eval (3 + 1) : ℕ) = 13 := by
    simp [timePoly_eval]
  have hx : ((Polynomial.X : Polynomial ℕ).eval (3 + 1)) = 4 := by simp
  have hx1 : ((Polynomial.X : Polynomial ℕ).eval 1) = 1 := by simp
  have he1 : (emitLenPoly Polynomial.X Polynomial.X (initCheckDesc.numStates + 1)
      (initCheckDesc.numLetters + 1) ([0] : List ℕ).length).eval 1 = 22585201 := by
    simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  have he4 : (emitLenPoly Polynomial.X Polynomial.X (initCheckDesc.numStates + 1)
      (initCheckDesc.numLetters + 1) ([0] : List ℕ).length).eval (3 + 1) = 7332629032 := by
    simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  rw [he1, he4, hm, h4', h5', hx, h1, hx1, h6, h7]

/-- The four evaluations are distinct and nested: `K < wid < S ≤ B`. -/
example :
    (1847750849 : ℕ) < Polynomial.eval 3 (envWid Polynomial.X Polynomial.X initCheckDesc
        (List.replicate (generatorPrefLen 3) 0) [0] [0]) ∧
      Polynomial.eval 3 (envWid Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) <
        Polynomial.eval 3 (envS Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) ∧
      Polynomial.eval 3 (envS Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) ≤
        Polynomial.eval 3 (envB Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) ∧
      Polynomial.eval 3 (envK Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) <
        Polynomial.eval 3 (envS Polynomial.X Polynomial.X initCheckDesc
          (List.replicate (generatorPrefLen 3) 0) [0] [0]) := by
  rw [aggInstanceK, aggInstanceWid, aggInstanceS, aggInstanceB]
  norm_num

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open Polynomial

/-! ## Non-vacuity: a two-entry table on the mixed-bit input `[true, false, true]`

`loadConstTestDescriptor` has a genuinely non-constant table — one `write` and
one `move` transition — so its three columns are not all equal, and the fourth
word `[5, 7, 9]` stands in for an arbitrary output index list. -/

/-- `loadConstTestDescriptor`'s table has exactly two entries. -/
lemma loadConstTestDescriptor_table_length :
    loadConstTestDescriptor.table.length = 2 := by
  unfold loadConstTestDescriptor
  simp

/-- `setupM` at `p = time = 0`, `d = loadConstTestDescriptor`, `allowedIdx = []`,
    `N = 3`: the concrete workspace base the rest of the non-vacuity
    computation rewrites against. -/
lemma loadConstTestDescriptor_setupM :
    setupM (0 : Polynomial ℕ) 0 loadConstTestDescriptor ([] : List ℕ) 3 = 82748 := by
  unfold setupM setupSpan
  simp only [loadConstTestDescriptor]
  unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
  simp [cookWindowPoly_eval, timePoly_eval]

lemma loadConstTestDescriptor_kindBase :
    generatorKindBase (0 : Polynomial ℕ) 0 loadConstTestDescriptor ([] : List ℕ) 3 = 82787 := by
  unfold generatorKindBase generatorKindOffset generatorPrefLen generatorPrefOffset
  rw [loadConstTestDescriptor_setupM]

lemma loadConstTestDescriptor_arg1Base :
    generatorArg1Base (0 : Polynomial ℕ) 0 loadConstTestDescriptor ([] : List ℕ) 3 = 82791 := by
  unfold generatorArg1Base generatorArg1Offset generatorKindOffset generatorPrefLen
    generatorPrefOffset
  rw [loadConstTestDescriptor_setupM, loadConstTestDescriptor_table_length]

lemma loadConstTestDescriptor_arg2Base :
    generatorArg2Base (0 : Polynomial ℕ) 0 loadConstTestDescriptor ([] : List ℕ) 3 = 82795 := by
  unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
    generatorPrefLen generatorPrefOffset
  rw [loadConstTestDescriptor_setupM, loadConstTestDescriptor_table_length]

lemma loadConstTestDescriptor_outBase :
    generatorOutBase (0 : Polynomial ℕ) 0 loadConstTestDescriptor ([] : List ℕ) 3 = 82799 := by
  unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
    generatorKindOffset generatorPrefLen generatorPrefOffset
  rw [loadConstTestDescriptor_setupM, loadConstTestDescriptor_table_length]

/-- Non-vacuity: `loadConstWordsProg_words` at a concrete descriptor, output
    list and input names an actual store and produces all four `WordAt`
    facts — not just an abstract existence claim. -/
example :
    WordAt ((loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true]))
      (generatorKindBase 0 0 loadConstTestDescriptor [] 3)
      (loadConstTestDescriptor.table.map transKind) ∧
    WordAt ((loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true]))
      (generatorArg1Base 0 0 loadConstTestDescriptor [] 3)
      (loadConstTestDescriptor.table.map transArg1) ∧
    WordAt ((loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true]))
      (generatorArg2Base 0 0 loadConstTestDescriptor [] 3)
      (loadConstTestDescriptor.table.map transArg2) ∧
    WordAt ((loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true]))
      (generatorOutBase 0 0 loadConstTestDescriptor [] 3) [5, 7, 9] :=
  loadConstWordsProg_words 0 0 loadConstTestDescriptor [] [5, 7, 9]
    (bitInputStore [true, false, true]) 3 rfl

/-- Reading the thirteen written cells by name: each word's length cell and its
    data cells, all as concrete numerals — `loadConstTestDescriptor`'s table
    columns `[1, 2]`, `[2, 3]`, `[1, 1]` and the output list `[5, 7, 9]`. -/
example :
    let σ := (loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
      (bitInputStore [true, false, true])
    σ 82786 = 2 ∧ σ 82787 = 1 ∧ σ 82788 = 2 ∧
      σ 82790 = 2 ∧ σ 82791 = 2 ∧ σ 82792 = 3 ∧
      σ 82794 = 2 ∧ σ 82795 = 1 ∧ σ 82796 = 1 ∧
      σ 82798 = 3 ∧ σ 82799 = 5 ∧ σ 82800 = 7 ∧ σ 82801 = 9 := by
  obtain ⟨⟨hlen1, hdata1⟩, ⟨hlen2, hdata2⟩, ⟨hlen3, hdata3⟩, ⟨hlen4, hdata4⟩⟩ :=
    loadConstWordsProg_words 0 0 loadConstTestDescriptor [] [5, 7, 9]
      (bitInputStore [true, false, true]) 3 rfl
  rw [loadConstTestDescriptor_kindBase] at hlen1 hdata1
  rw [loadConstTestDescriptor_arg1Base] at hlen2 hdata2
  rw [loadConstTestDescriptor_arg2Base] at hlen3 hdata3
  rw [loadConstTestDescriptor_outBase] at hlen4 hdata4
  refine ⟨hlen1, ?_, ?_, hlen2, ?_, ?_, hlen3, ?_, ?_, hlen4, ?_, ?_, ?_⟩
  · exact hdata1 0 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata1 1 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata2 0 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata2 1 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata3 0 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata3 1 (by rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdata4 0 (by norm_num)
  · exact hdata4 1 (by norm_num)
  · exact hdata4 2 (by norm_num)

/-- Input preservation, named cell by cell: bits `1, 2, 3` (the three input
    bits `[true, false, true]`) still hold their original `1`/`0`/`1` values
    after `loadConstWordsProg` runs. -/
example :
    let σ := (loadConstWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
      (bitInputStore [true, false, true])
    σ 1 = 1 ∧ σ 2 = 0 ∧ σ 3 = 1 := by
  have hb : (3 : ℕ) < generatorKindBase 0 0 loadConstTestDescriptor [] 3 - 1 := by
    rw [loadConstTestDescriptor_kindBase]; omega
  have h1 := loadConstWordsProg_preserves_below 0 0 loadConstTestDescriptor [] [5, 7, 9]
    (bitInputStore [true, false, true]) 3 1 rfl (by omega)
  have h2 := loadConstWordsProg_preserves_below 0 0 loadConstTestDescriptor [] [5, 7, 9]
    (bitInputStore [true, false, true]) 3 2 rfl (by omega)
  have h3 := loadConstWordsProg_preserves_below 0 0 loadConstTestDescriptor [] [5, 7, 9]
    (bitInputStore [true, false, true]) 3 3 rfl (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl

end

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The prefix word for `[true, false, true]` under `loadConstTestDescriptor`,
    matching `loadPrefixTestDescriptor_prefixWord`'s pattern for the same
    `trueIdx`/`falseIdx` pair. -/
lemma loadConstTestDescriptor_prefixWord :
    prefixWord loadConstTestDescriptor [true, false, true]
      = [1, 1, 1, 0, 1, 1, 0] := by
  unfold prefixWord loadConstTestDescriptor
  simp

lemma loadConstTestDescriptor_prefBase :
    generatorPrefBase (0 : Polynomial ℕ) 0 loadConstTestDescriptor [] 3 = 82778 := by
  unfold generatorPrefBase generatorPrefOffset
  rw [loadConstTestDescriptor_setupM]

/-- Non-vacuity: `generatorProgFromBits_meets_emitter_precondition` at concrete
    values names an actual run and produces the `ClauseTableAt`/emitter-base
    pair with no leftover hypothesis. -/
example :
    ClauseTableAt ((generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true]))
        (generatorTableBase 0 0 loadConstTestDescriptor [] [5, 7, 9] 3)
        (descTableauCNF (denseLayout (loadConstTestDescriptor.numStates + 1)
            ((cookWindowPoly 0 0).eval 3) (loadConstTestDescriptor.numLetters + 1))
          loadConstTestDescriptor
          (prefixWord loadConstTestDescriptor [true, false, true])
          ((0 : Polynomial ℕ).eval 3) [] [5, 7, 9]
          ((cookWindowPoly 0 0).eval 3) ((timePoly 0 0).eval 3)) ∧
      (generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
        (bitInputStore [true, false, true])
        (setupM 0 0 loadConstTestDescriptor [] 3 + emTblJ)
        = generatorTableBase 0 0 loadConstTestDescriptor [] [5, 7, 9] 3 :=
  generatorProgFromBits_meets_emitter_precondition 0 0 loadConstTestDescriptor [] [5, 7, 9]
    [true, false, true]

/-- Concrete cells of the prefix and kind words after `loadWordsProg`: the
    prefix length cell and seven data cells, and the kind length cell and two
    data cells. -/
example :
    let σ := (loadWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]).eval
      (bitInputStore [true, false, true])
    σ 82777 = 7 ∧ σ 82778 = 1 ∧ σ 82779 = 1 ∧ σ 82780 = 1 ∧ σ 82781 = 0 ∧
      σ 82782 = 1 ∧ σ 82783 = 1 ∧ σ 82784 = 0 ∧
      σ 82786 = 2 ∧ σ 82787 = 1 ∧ σ 82788 = 2 := by
  have hlen3 : ([true, false, true] : List Bool).length = 3 := by norm_num
  obtain ⟨⟨⟨⟨hpref, hk⟩, _⟩, _⟩, _⟩ :=
    loadWordsProg_words 0 0 loadConstTestDescriptor [] [5, 7, 9] [true, false, true]
  rw [hlen3] at hpref hk
  rw [loadConstTestDescriptor_prefixWord, loadConstTestDescriptor_prefBase] at hpref
  rw [loadConstTestDescriptor_kindBase] at hk
  obtain ⟨hlenp, hdatap⟩ := hpref
  obtain ⟨hlenk, hdatak⟩ := hk
  refine ⟨hlenp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlenk, ?_, ?_⟩
  · exact hdatap 0 (by norm_num)
  · exact hdatap 1 (by norm_num)
  · exact hdatap 2 (by norm_num)
  · exact hdatap 3 (by norm_num)
  · exact hdatap 4 (by norm_num)
  · exact hdatap 5 (by norm_num)
  · exact hdatap 6 (by norm_num)
  · exact hdatak 0 (by
      rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)
  · exact hdatak 1 (by
      rw [List.length_map, loadConstTestDescriptor_table_length]; norm_num)

end

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## Non-vacuity: mixed bits `[true, false, true]`

`d0` has distinct `trueIdx`/`falseIdx`, and the bit pattern mixes `true` and
`false` so both branches of the `ifNZ` in `loadPrefixStep` are exercised. -/

/-- A test descriptor with distinct letter indices; the other fields are
    irrelevant to `loadPrefixProg` and left at `0`/`[]`. -/
def loadPrefixTestDescriptor : TableauDescriptor :=
  { numStates := 0, startState := 0, numLetters := 0, blankIdx := 0
    falseIdx := 0, trueIdx := 1, table := [] }

/-- The prefix word for `[true, false, true]` expands each bit to `[trueIdx, ⋯]`
    and ends with the separator `falseIdx`. -/
lemma loadPrefixTestDescriptor_prefixWord :
    prefixWord loadPrefixTestDescriptor [true, false, true]
      = [1, 1, 1, 0, 1, 1, 0] := by
  unfold prefixWord loadPrefixTestDescriptor
  simp

/-- Non-vacuity: `loadPrefixProg_wordAt` at these concrete values names an
    actual store and produces `WordAt`, whose length and data cells are then
    read off individually — not just asserted to hold abstractly. -/
example :
    WordAt ((loadPrefixProg 0 0 loadPrefixTestDescriptor []).eval
        (bitInputStore [true, false, true]))
      (generatorPrefBase 0 0 loadPrefixTestDescriptor [] 3) [1, 1, 1, 0, 1, 1, 0] := by
  have h := loadPrefixProg_wordAt 0 0 loadPrefixTestDescriptor [] [true, false, true]
  rwa [loadPrefixTestDescriptor_prefixWord] at h

/-- Reading the length cell and seven data cells by name: the marker/data
    pairing per bit, and the trailing separator, all as concrete numerals. -/
example :
    let σ := (loadPrefixProg 0 0 loadPrefixTestDescriptor []).eval
      (bitInputStore [true, false, true])
    let base := generatorPrefBase 0 0 loadPrefixTestDescriptor [] 3
    σ (base - 1) = 7 ∧
      σ base = 1 ∧ σ (base + 1) = 1 ∧
      σ (base + 2) = 1 ∧ σ (base + 3) = 0 ∧
      σ (base + 4) = 1 ∧ σ (base + 5) = 1 ∧
      σ (base + 6) = 0 := by
  have h := loadPrefixProg_wordAt 0 0 loadPrefixTestDescriptor [] [true, false, true]
  rw [loadPrefixTestDescriptor_prefixWord] at h
  obtain ⟨hlen, hdata⟩ := h
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdata 0 (by norm_num)
  · exact hdata 1 (by norm_num)
  · exact hdata 2 (by norm_num)
  · exact hdata 3 (by norm_num)
  · exact hdata 4 (by norm_num)
  · exact hdata 5 (by norm_num)
  · exact hdata 6 (by norm_num)

/-- Input preservation, named cell by cell: bits `1, 2, 3` (the three input
    bits `[true, false, true]`) still hold their original `0`/`1` values after
    `loadPrefixProg` runs. -/
example :
    let σ := (loadPrefixProg 0 0 loadPrefixTestDescriptor []).eval
      (bitInputStore [true, false, true])
    σ 1 = 1 ∧ σ 2 = 0 ∧ σ 3 = 1 := by
  have h0 := loadPrefixProg_input_frame 0 0 loadPrefixTestDescriptor [] [true, false, true]
    0 (by norm_num)
  have h1 := loadPrefixProg_input_frame 0 0 loadPrefixTestDescriptor [] [true, false, true]
    1 (by norm_num)
  have h2 := loadPrefixProg_input_frame 0 0 loadPrefixTestDescriptor [] [true, false, true]
    2 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact h0
  · exact h1
  · exact h2

end

end NPComplete.CookLevin

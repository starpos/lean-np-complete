module

public import NPComplete.CookLevin.ReductionProg.GeneratorLoadConst
public import NPComplete.CookLevin.ReductionProg.GeneratorLoadPrefix

/-!
`generatorProg` assumes all five staged words already sit in the store; on a
raw `bitInputStore` none of them do, so its entry condition is unreachable
without a load phase in front of it.  `GeneratorLoadPrefix.lean` builds the
one input-dependent word (the certificate prefix) and `GeneratorLoadConst.lean`
builds the four input-independent words: the three transition-table columns
from `d`, and the output-index list supplied separately as `outIdx`.  This file
composes the two into a single
loader and prepends it to `generatorProg`, so that `generatorProgFromBits`
writes the clause table starting from nothing but the canonical loader
`bitInputStore` — no `GeneratorWordsAt` hypothesis left to discharge.

The composition order matters: `loadPrefixProg_wordAt` fixes its entry store to
`bitInputStore bits`, while `loadConstWordsProg_words` accepts any store whose
cell `0` holds the input length.  Running the prefix loader first and the
constant-word loader second lets the latter's general entry condition absorb
whatever store the former produces.  The prefix word then has to survive the
four constant-word writes that follow it; `generator_load_base_floor` already
proves the layout keeps the four constant bases at or above
`generatorKindBase`, and the prefix length formula
(`prefixWord_length` matched against `generatorKindOffset`) shows the prefix
word's own cells sit strictly below that base — so the two regions never
overlap.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The composed loader -/

/-- Stage the certificate prefix, then the four constant words, on top of
    `bitInputStore`. Order matters: `loadPrefixProg_wordAt` fixes its entry
    store to `bitInputStore bits`, while `loadConstWordsProg_words` accepts any
    store agreeing with it on cell `0`. -/
noncomputable def loadWordsProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (loadPrefixProg p time d allowedIdx) (loadConstWordsProg p time d allowedIdx outIdx)

/-- Register `0` (the input length) survives the whole load: neither stage
    touches it, `loadPrefixProg_reg0` for the first and
    `loadConstWordsProg_zero` for the second. -/
lemma loadWordsProg_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : List Bool) :
    ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)) 0 = bits.length := by
  unfold loadWordsProg
  simp only [eval_seq]
  have h0 : (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) 0 = bits.length :=
    loadPrefixProg_reg0 p time d allowedIdx bits
  rw [loadConstWordsProg_zero p time d allowedIdx outIdx _ bits.length h0]
  exact h0

/-- The prefix word, once staged, survives every write `loadConstWordsProg`
    makes afterwards: its cells sit strictly below `generatorKindBase - 1`,
    the floor every constant-word write respects
    (`loadConstWordsProg_preserves_below`). -/
lemma loadConstWordsProg_preserves_prefix_wordAt (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (xs : List ℕ) (hlen : xs.length = generatorPrefLen N)
    (hw : WordAt σ (generatorPrefBase p time d allowedIdx N) xs) :
    WordAt ((loadConstWordsProg p time d allowedIdx outIdx).eval σ)
      (generatorPrefBase p time d allowedIdx N) xs := by
  obtain ⟨hlenCell, hdata⟩ := hw
  have hbound : generatorPrefBase p time d allowedIdx N + xs.length
      ≤ generatorKindBase p time d allowedIdx N - 1 := by
    rw [hlen]
    unfold generatorPrefBase generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset
    omega
  have hk1 : generatorPrefBase p time d allowedIdx N - 1
      < generatorKindBase p time d allowedIdx N - 1 := by
    unfold generatorPrefBase generatorKindBase generatorKindOffset generatorPrefLen
      generatorPrefOffset
    omega
  refine ⟨?_, ?_⟩
  · rw [loadConstWordsProg_preserves_below p time d allowedIdx outIdx σ N
      (generatorPrefBase p time d allowedIdx N - 1) h0 hk1]
    exact hlenCell
  · intro k hk
    have hk2 : generatorPrefBase p time d allowedIdx N + k
        < generatorKindBase p time d allowedIdx N - 1 := by omega
    rw [loadConstWordsProg_preserves_below p time d allowedIdx outIdx σ N
      (generatorPrefBase p time d allowedIdx N + k) h0 hk2]
    exact hdata k hk

/-- The full staging contract `generatorProg` needs (`GeneratorWordsAt`), now
    established from raw input bits alone. -/
lemma loadWordsProg_words (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : List Bool) :
    GeneratorWordsAt p time d allowedIdx outIdx (prefixWord d bits) bits.length
      ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)) := by
  unfold loadWordsProg
  simp only [eval_seq]
  unfold GeneratorWordsAt
  have hpre := loadPrefixProg_wordAt p time d allowedIdx bits
  have h0 : (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) 0 = bits.length :=
    loadPrefixProg_reg0 p time d allowedIdx bits
  obtain ⟨hk, h1, h2, ho⟩ := loadConstWordsProg_words p time d allowedIdx outIdx _ _ h0
  refine ⟨⟨⟨⟨?_, hk⟩, h1⟩, h2⟩, ho⟩
  exact loadConstWordsProg_preserves_prefix_wordAt p time d allowedIdx outIdx _ bits.length h0
    (prefixWord d bits) (prefixWord_length d bits) hpre

/-! ## Prepending the loader to `generatorProg` -/

/-- Compose the word loader with `generatorProg` so execution can start from
    `bitInputStore bits`; the loader establishes the staged-word data required
    by the generator. -/
noncomputable def generatorProgFromBits (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (loadWordsProg p time d allowedIdx outIdx) (generatorProg p time d allowedIdx outIdx)

/-- `generatorProgFromBits` writes the clause table and exposes its base at
    the emitter's expected register, starting from `bitInputStore bits` alone
    — no `GeneratorWordsAt` hypothesis remains, unlike
    `generator_prog_meets_emitter_precondition`. -/
lemma generatorProgFromBits_meets_emitter_precondition (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : List Bool) :
    ClauseTableAt ((generatorProgFromBits p time d allowedIdx outIdx).eval
        (bitInputStore bits))
        (generatorTableBase p time d allowedIdx outIdx bits.length)
        (descTableauCNF (denseLayout (d.numStates + 1)
            ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
          (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
          ((cookWindowPoly p time).eval bits.length)
          ((timePoly p time).eval bits.length)) ∧
      (generatorProgFromBits p time d allowedIdx outIdx).eval (bitInputStore bits)
        (setupM p time d allowedIdx bits.length + emTblJ)
        = generatorTableBase p time d allowedIdx outIdx bits.length := by
  unfold generatorProgFromBits
  simp only [eval_seq]
  exact generator_prog_meets_emitter_precondition p time d allowedIdx outIdx
    (prefixWord d bits) _ bits.length (loadWordsProg_reg0 p time d allowedIdx outIdx bits)
    (prefixWord_length d bits) (loadWordsProg_words p time d allowedIdx outIdx bits)

/-! ## `ScanFree` -/

/-- `loadPrefixStep` (the per-bit loop body) never scans a list. -/
lemma scanFree_loadPrefixStep (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    ScanFree (loadPrefixStep p time d allowedIdx) := by
  simp [loadPrefixStep, ScanFree]

/-- `loadPrefixProg` wraps `loadPrefixStep` in a `.forN`, which `ScanFree`
    permits. -/
lemma scanFree_loadPrefixProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    ScanFree (loadPrefixProg p time d allowedIdx) := by
  simp [loadPrefixProg, ScanFree, scanFree_loadPrefixStep]

/-- `constCellsFrom` is a straight-line chain of `.assignInd` writes. -/
lemma scanFree_constCellsFrom (baseE : Expr) : ∀ (j : ℕ) (xs : List ℕ),
    ScanFree (constCellsFrom baseE j xs)
  | _, [] => by simp [constCellsFrom, ScanFree]
  | j, x :: xs => by
      simp [constCellsFrom, ScanFree, constCellAssign,
        scanFree_constCellsFrom baseE (j + 1) xs]

lemma scanFree_writeConstWordProg (baseE : Expr) (xs : List ℕ) :
    ScanFree (writeConstWordProg baseE xs) := by
  simp [writeConstWordProg, ScanFree, constCellAssign, scanFree_constCellsFrom]

lemma scanFree_loadConstWordsProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : ScanFree (loadConstWordsProg p time d allowedIdx outIdx) := by
  simp [loadConstWordsProg, ScanFree, scanFree_writeConstWordProg]

lemma scanFree_loadWordsProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : ScanFree (loadWordsProg p time d allowedIdx outIdx) := by
  simp [loadWordsProg, ScanFree, scanFree_loadPrefixProg, scanFree_loadConstWordsProg]

/-- `generatorProgFromBits` is `ScanFree`: both the loader
    (`scanFree_loadWordsProg`) and the core generator
    (`scanFree_generatorProg`) are. -/
lemma scanFree_generatorProgFromBits (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ScanFree (generatorProgFromBits p time d allowedIdx outIdx) := by
  simp [generatorProgFromBits, ScanFree, scanFree_loadWordsProg, scanFree_generatorProg]

end NPComplete.CookLevin

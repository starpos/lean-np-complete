module

public import NPComplete.CookLevin.ReductionProg.GeneratorLoad
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableEmit
public import NPComplete.CookLevin.ReductionProg.GeneratorRowCountCarry

/-!
# Clause-table generator

The clause-table generator must preserve its row count and forward-writer state as it emits each
clause. This module defines that streaming program and its invariants so the output ABI can be
attached without entangling it with clause assembly.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-- The output ABI starts at a fixed low address; this value is unrelated to the
emitter's cursor-register address `emCurJ`, even though both happen to be `8`. -/
def emitOutputStart : ℕ := 8

/-- The raw-input generator followed by the explicit output-cursor setup and the
clause-table emitter.  The assignment makes the ABI cursor independent of the
fresh input store's blank-cell convention. -/
noncomputable def generatorProgFull (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (generatorProgFromBits p time d allowedIdx outIdx)
    (.seq (ctlAssign emCurJ (.const emitOutputStart))
      (emitClauseTableProg emCurJ emTmpJ emCntJ emPtrJ emRowJ rowCountReg emTblJ))

/-- The generator core keeps cell `0` at the workspace base after its setup,
count, and five writer stages. -/
lemma generatorProg_zero_of_words (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    (generatorProg p time d allowedIdx outIdx).eval σ 0 =
      setupM p time d allowedIdx N := by
  have hh := generator_count_stage_handoff p time d allowedIdx outIdx prefIdx σ N
    h0 hlen hw
  dsimp at hh
  obtain ⟨hκFC, hκ0, hκwp, hio⟩ := hh
  have hsep : setupM p time d allowedIdx N + generatorJmax d outIdx N <
      generatorTableBase p time d allowedIdx outIdx N := by
    simp [generatorTableBase]
  have hexit := hio _ (generatorTableBase p time d allowedIdx outIdx N)
    hκFC hκ0 hκwp hsep
  simpa only [generatorProg, eval_seq] using hexit.2.1

/-- The raw-input generator preserves the workspace-base cell through its
loader before the core generator starts. -/
lemma generatorProgFromBits_zero (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    (generatorProgFromBits p time d allowedIdx outIdx).eval (bitInputStore bits) 0 =
      setupM p time d allowedIdx bits.length := by
  have h0 := loadWordsProg_reg0 p time d allowedIdx outIdx bits
  have hlen := prefixWord_length d bits
  have hw := loadWordsProg_words p time d allowedIdx outIdx bits
  have h := generatorProg_zero_of_words p time d allowedIdx outIdx
      (prefixWord d bits) ((loadWordsProg p time d allowedIdx outIdx).eval
        (bitInputStore bits)) bits.length h0 hlen hw
  simpa only [generatorProgFromBits, eval_seq] using h

/-- The bits-input generator leaves the clause count in the emitter's row-count
cell, already rewritten from the closed-form count to the CNF's length. -/
lemma generatorProgFromBits_row_count (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    (generatorProgFromBits p time d allowedIdx outIdx).eval (bitInputStore bits)
      (setupM p time d allowedIdx bits.length + rowCountReg) =
    (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
      (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
      ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length)).clauses.length := by
  let τ := (loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)
  have hτ0 := loadWordsProg_reg0 p time d allowedIdx outIdx bits
  have hwords := loadWordsProg_words p time d allowedIdx outIdx bits
  have hr := generator_prog_row_count p time d allowedIdx outIdx
      (prefixWord d bits) τ bits.length hτ0 (prefixWord_length d bits) hwords
  have heq := clauseCount_eq (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
    (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
    ((cookWindowPoly p time).eval bits.length)
    ((timePoly p time).eval bits.length)
  rw [heq] at hr
  simpa [τ, generatorProgFromBits, eval_seq] using hr

/-- The emitter's live registers plus the generator's row-count cell are pairwise
distinct, which is the distinctness bundle the emitter lemmas take. -/
lemma emitter_rowCountReg_regs_distinct :
    1 ≤ emCurJ ∧ 1 ≤ emTmpJ ∧
    emCurJ ≠ emTmpJ ∧ emCurJ ≠ emCntJ ∧ emCurJ ≠ emPtrJ ∧ emCurJ ≠ emRowJ ∧
    emCurJ ≠ rowCountReg ∧ emCurJ ≠ emTblJ ∧
    emTmpJ ≠ emCntJ ∧ emTmpJ ≠ emPtrJ ∧ emTmpJ ≠ emRowJ ∧
    emTmpJ ≠ rowCountReg ∧ emTmpJ ≠ emTblJ ∧
    emCntJ ≠ emPtrJ ∧ emCntJ ≠ emRowJ ∧ emCntJ ≠ rowCountReg ∧
    emCntJ ≠ emTblJ ∧ emPtrJ ≠ emRowJ ∧ emPtrJ ≠ rowCountReg ∧
    emPtrJ ≠ emTblJ ∧ emRowJ ≠ rowCountReg ∧ emRowJ ≠ emTblJ := by
  norm_num [emCurJ, emTmpJ, emCntJ, emPtrJ, emRowJ, rowCountReg, emTblJ]

/-- Every emitter register sits below the staged table, because the table starts
past `generatorJmax` and that extent already clears `emRowJ`. -/
lemma generator_em_reg_lt_table (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (N j : ℕ) (hj : j ≤ emRowJ) :
    setupM p time d allowedIdx N + j <
      generatorTableBase p time d allowedIdx outIdx N := by
  simp [generatorTableBase, generatorJmax, generatorOutOffset,
    generatorArg2Offset, generatorArg1Offset, generatorKindOffset,
    generatorPrefOffset, generatorPrefLen, emRowJ] at hj ⊢
  omega

/-- The encoding fits in the workspace below `M`, so the ABI output range cannot
collide with the emitter's control cells. -/
lemma emit_output_sep_bounds (M : ℕ) (φ : CNF)
    (hM : (encodeCNF φ).length ≤ M) :
    emitOutputStart + φ.clauses.length + 1 ≤ M + rowCountReg ∧
    emitOutputStart + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + emCurJ ∧
    emitOutputStart + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + emTmpJ ∧
    emitOutputStart + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + emCntJ ∧
    emitOutputStart + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + emPtrJ ∧
    emitOutputStart + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + emRowJ := by
  have hfull := clausePrefixBitsLen_full φ
  simp [emitOutputStart, rowCountReg, emCurJ, emTmpJ, emCntJ, emPtrJ, emRowJ]
  omega

/-- A control-cell assignment for the output cursor leaves a table at a higher
address unchanged. -/
lemma ctlAssign_preserves_clauseTableAt (M curJ tbl : ℕ) (φ : CNF) (σ : Store)
    (hM : σ 0 = M) (hlo : M + curJ < tbl) (htable : ClauseTableAt σ tbl φ) :
    ClauseTableAt ((ctlAssign curJ (.const emitOutputStart)).eval σ) tbl φ := by
  unfold ClauseTableAt at htable ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [ctlAssign_eval_diff curJ _ σ (tbl + rowTableWidth (cnfCnt φ) q + 1) (by
      rw [hM]
      omega)]
    exact htable.1 q hq
  · intro q hq i hi
    rw [ctlAssign_eval_diff curJ _ σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) (by
      rw [hM]
      omega)]
    exact htable.2.1 q hq i hi
  · intro q hq i hi
    rw [ctlAssign_eval_diff curJ _ σ
      (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) (by
        rw [hM]
        omega)]
    exact htable.2.2 q hq i hi

/-! ## Correctness of the composed producer -/

/-- Running the full producer materializes the target CNF's bit encoding at the
fixed ABI output address.  The five range hypotheses are precisely those needed
by the polynomial output-length certificate. -/
lemma generatorProgFull_meets_emitter_output (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefixWord d bits, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    BitsAt ((generatorProgFull p time d allowedIdx outIdx).eval
        (bitInputStore bits))
      emitOutputStart
      (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
          ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
        (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))) ∧
    ((generatorProgFull p time d allowedIdx outIdx).eval
        (bitInputStore bits))
      (setupM p time d allowedIdx bits.length + emCurJ) =
      emitOutputStart + (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
          ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
        (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))).length ∧
    ((generatorProgFull p time d allowedIdx outIdx).eval
        (bitInputStore bits)) 0 = setupM p time d allowedIdx bits.length := by
  let N := bits.length
  let M := setupM p time d allowedIdx N
  let φ := descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d
    (prefixWord d bits) (p.eval N) allowedIdx outIdx
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
  let tbl := generatorTableBase p time d allowedIdx outIdx N
  let σ := (generatorProgFromBits p time d allowedIdx outIdx).eval
    (bitInputStore bits)
  let σ' := (ctlAssign emCurJ (.const emitOutputStart)).eval σ
  have hpre := generatorProgFromBits_meets_emitter_precondition
    p time d allowedIdx outIdx bits
  have htable : ClauseTableAt σ tbl φ := by
    simpa [σ, tbl, φ, N] using hpre.1
  have htbl : σ (M + emTblJ) = tbl := by
    simpa [σ, tbl, M, N] using hpre.2
  have hcore0 : σ 0 = M := by
    simpa [σ, M, N] using generatorProgFromBits_zero p time d allowedIdx outIdx bits
  have hrow : σ (M + rowCountReg) = φ.clauses.length := by
    simpa [σ, M, φ, N] using
      generatorProgFromBits_row_count p time d allowedIdx outIdx bits
  have hloCur : M + emCurJ < tbl :=
    generator_em_reg_lt_table p time d allowedIdx outIdx N emCurJ
      (by norm_num [emCurJ, emRowJ])
  have hloTmp : M + emTmpJ < tbl :=
    generator_em_reg_lt_table p time d allowedIdx outIdx N emTmpJ
      (by norm_num [emTmpJ, emRowJ])
  have hloCnt : M + emCntJ < tbl :=
    generator_em_reg_lt_table p time d allowedIdx outIdx N emCntJ
      (by norm_num [emCntJ, emRowJ])
  have hloPtr : M + emPtrJ < tbl :=
    generator_em_reg_lt_table p time d allowedIdx outIdx N emPtrJ
      (by norm_num [emPtrJ, emRowJ])
  have hloRow : M + emRowJ < tbl :=
    generator_em_reg_lt_table p time d allowedIdx outIdx N emRowJ (by omega)
  have hM' : σ' 0 = M := by
    dsimp [σ']
    rw [ctlAssign_zero emCurJ _ σ (by norm_num [emCurJ]), hcore0]
  have hcur' : σ' (M + emCurJ) = emitOutputStart := by
    dsimp [σ']
    have h := ctlAssign_eval_same emCurJ (.const emitOutputStart) σ
    rw [hcore0] at h
    simpa [Expr.eval] using h
  have hrow' : σ' (M + rowCountReg) = φ.clauses.length := by
    dsimp [σ']
    rw [ctlAssign_eval_diff emCurJ _ σ (M + rowCountReg) (by
      rw [hcore0]
      norm_num [emCurJ, rowCountReg])]
    exact hrow
  have htbl' : σ' (M + emTblJ) = tbl := by
    dsimp [σ']
    rw [ctlAssign_eval_diff emCurJ _ σ (M + emTblJ) (by
      rw [hcore0]
      norm_num [emCurJ, emTblJ])]
    exact htbl
  have htable' : ClauseTableAt σ' tbl φ :=
    ctlAssign_preserves_clauseTableAt M emCurJ tbl φ σ hcore0 hloCur htable
  have hprefixLen : (prefixWord d bits).length ≤ 2 * N + 1 := by
    rw [prefixWord_length]
  have hencode := emitLenPoly_ge_encodeCNF p time d (prefixWord d bits)
    allowedIdx outIdx N hwrite hblank hpref hallowed hout hprefixLen
  let E := (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
    allowedIdx.length).eval N
  have hE : E ≤ M := by
    simp [E, M, setupM]
  have hencodeM : (encodeCNF φ).length ≤ M := hencode.trans hE
  obtain ⟨hsepCnt, hsepFull, hsepTmpAll, hsepCntAll, hsepPtrAll, hsepRowAll⟩ :=
    emit_output_sep_bounds M φ hencodeM
  obtain ⟨hreg1, hreg2, hCurTmp, hCurCnt, hCurPtr, hCurRow, hCurRowCnt,
      _, hTmpCnt, hTmpPtr, hTmpRow, hTmpRowCnt, _, hCntPtr,
      hCntRow, _, _, hPtrRow, _, _, hRowRowCnt, _⟩ := emitter_rowCountReg_regs_distinct
  have hout := emitClauseTableProg_of_table_at emCurJ emTmpJ emCntJ emPtrJ emRowJ
      rowCountReg emTblJ M emitOutputStart tbl φ σ'
      hreg1 hreg2 hCurTmp hCurCnt hCurPtr hCurRow hCurRowCnt hTmpCnt
      hTmpPtr hTmpRow hTmpRowCnt hCntPtr hCntRow hPtrRow hRowRowCnt hM' hcur' (by
        norm_num [emitOutputStart]) hrow' htbl' htable' hsepCnt hsepFull
      hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll hloCur hloTmp hloCnt hloPtr hloRow
  simpa [generatorProgFull, σ, σ', M, φ, tbl, N, eval_seq] using hout

/-! ## Scan-free composition -/

/-- The full producer contains only assignments and bounded loops, so it remains
eligible for the scan-free compiler path after adding the clause emitter. -/
lemma scanFree_emitClauseTableProg :
    ScanFree (emitClauseTableProg emCurJ emTmpJ emCntJ emPtrJ emRowJ rowCountReg emTblJ) := by
  simp [emitClauseTableProg, emitListProg, emitClauseBody, emitOpsListProg,
    emitRawOpBody, emitNatProg, emitBitProg, ScanFree, ctlAssign]

lemma scanFree_generatorProgFull (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : ScanFree (generatorProgFull p time d allowedIdx outIdx) := by
  simp [generatorProgFull, ScanFree, ctlAssign, scanFree_generatorProgFromBits,
    scanFree_emitClauseTableProg]

end NPComplete.CookLevin

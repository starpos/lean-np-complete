module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedEmit
public import NPComplete.CookLevin.ReductionProg.GeneratorCost
public import NPComplete.CookLevin.UniformPackaging

/-!
# ABI generator invariants

Validity, memory bounds, and scan-freeness must hold for the fully assembled ABI generator, not
only its clause emitter. This module collects those execution invariants so cost estimates can be
proved separately against a single certified program.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)


lemma prefixWord_valid_of_true_false (d : TableauDescriptor) (bits : Bits)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1) :
    ∀ a ∈ prefixWord d bits, a < d.numLetters + 1 := by
  intro a ha
  rcases prefixWord_mem_true_false d bits ha with h | h
  · simpa [h] using htrue
  · simpa [h] using hfalse

lemma programBoundedIn_finalizeOutputProg (B outBaseReg outLenReg : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hbase : outBaseReg ≤ B) (hlen : outLenReg ≤ B) :
    ProgramBoundedIn B σ (finalizeOutputProg outBaseReg outLenReg) := by
  unfold finalizeOutputProg ProgramBoundedIn
  simp only [outLenCell, outAddrCell]
  constructor
  · constructor
    · omega
    · exact hlen
  · constructor
    · omega
    · exact hbase

/-- Every control cell `M + j` with `j ≤ 70` lies below the generator envelope. -/
lemma programBoundedIn_generatorProgFull_valid_ctl_le (p time : Polynomial ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    ∀ j ≤ 70, setupM p time d allowedIdx N + j ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  intro j hj
  have hK := envK_eval_ge_setupM_add_70 p time d prefIdx allowedIdx outIdx N
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

/-- Resetting the output cursor keeps the clause table and the row-count and table cells,
    which is the state the emitter starts from. -/
lemma programBoundedIn_generatorProgFull_valid_ctl_state (M tbl : ℕ) (φ : CNF) (σ : Store)
    (hcore0 : σ 0 = M) (htable : ClauseTableAt σ tbl φ) (htbl : σ (M + emTblJ) = tbl)
    (hrow : σ (M + rowCountReg) = φ.clauses.length) (hlo : ∀ j, j ≤ 12 → M + j < tbl) :
    ∃ σ', σ' = (ctlAssign emCurJ (.const emitOutputStart)).eval σ ∧ σ' 0 = M ∧
      σ' (M + emCurJ) = emitOutputStart ∧ σ' (M + rowCountReg) = φ.clauses.length ∧
      σ' (M + emTblJ) = tbl ∧ ClauseTableAt σ' tbl φ := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ctlAssign_zero emCurJ _ σ (by norm_num [emCurJ]), hcore0]
  · have h := ctlAssign_eval_same emCurJ (.const emitOutputStart) σ
    rw [hcore0] at h
    simpa [Expr.eval] using h
  · rw [ctlAssign_eval_diff emCurJ _ σ (M + rowCountReg)
      (by rw [hcore0]; norm_num [emCurJ, rowCountReg])]
    exact hrow
  · rw [ctlAssign_eval_diff emCurJ _ σ (M + emTblJ)
      (by rw [hcore0]; norm_num [emCurJ, emTblJ])]
    exact htbl
  · exact ctlAssign_preserves_clauseTableAt M emCurJ tbl φ σ hcore0
      (hlo emCurJ (by norm_num [emCurJ])) htable

/-- The encoded tableau CNF fits below the setup offset `M`. -/
lemma programBoundedIn_generatorProgFull_valid_encode_le_setupM (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) (φ : CNF)
    (hφ : φ = descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d (prefixWord d bits)
      (p.eval bits.length) allowedIdx outIdx ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length)) :
    (encodeCNF φ).length ≤ setupM p time d allowedIdx bits.length := by
  subst hφ
  have hpref := prefixWord_valid_of_true_false d bits hfalse htrue
  have hprefixLen : (prefixWord d bits).length ≤ 2 * bits.length + 1 := by
    simp [prefixWord_length]
  have hencode := emitLenPoly_ge_encodeCNF p time d (prefixWord d bits) allowedIdx outIdx
    bits.length hwrite hblank hpref hallowed hout hprefixLen
  have hE : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval bits.length ≤ setupM p time d allowedIdx bits.length := by
    simp [setupM]
  exact hencode.trans hE

/-- The staged clause table, including its row widths, fits below the generator envelope. -/
lemma programBoundedIn_generatorProgFull_valid_table_width (p time : Polynomial ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (φ : CNF)
    (hφ : φ = descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d prefIdx (p.eval N)
      allowedIdx outIdx ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)) :
    generatorTableBase p time d allowedIdx outIdx N +
      rowTableWidth (cnfCnt φ) φ.clauses.length ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  subst hφ
  have hw := rowTableWidth_descTableauCNF_le_emitLenPoly p time d prefIdx allowedIdx outIdx N
  have hEsetup : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval N ≤ setupM p time d allowedIdx N := by
    simp [setupM]
  have htbK := envK_ge_tableBase p time d prefIdx allowedIdx outIdx N
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  have hBE := envB_eval p time d prefIdx allowedIdx outIdx N
  rw [hBE]
  omega

lemma programBoundedIn_generatorProgFull_valid (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    ProgramBoundedIn
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (bitInputStore bits) (generatorProgFull p time d allowedIdx outIdx) := by
  let N := bits.length
  let pref := prefixWord d bits
  let M := setupM p time d allowedIdx N
  let φ := descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d pref (p.eval N)
      allowedIdx outIdx ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
  let tbl := generatorTableBase p time d allowedIdx outIdx N
  let B := (envB p time d pref allowedIdx outIdx).eval N
  let σ := (generatorProgFromBits p time d allowedIdx outIdx).eval (bitInputStore bits)
  have hcore0 : σ 0 = M := by
    simpa [σ, M, N] using generatorProgFromBits_zero p time d allowedIdx outIdx bits
  have hpre := generatorProgFromBits_meets_emitter_precondition p time d allowedIdx outIdx bits
  have hrow : σ (M + rowCountReg) = φ.clauses.length := by
    simpa [σ, M, φ, N] using
      generatorProgFromBits_row_count p time d allowedIdx outIdx bits
  have hlo_of : ∀ j, j ≤ 12 → M + j < tbl := fun j hj => by
    simpa [M, tbl] using
      generator_em_reg_lt_table p time d allowedIdx outIdx N j (by simpa [emRowJ] using hj)
  obtain ⟨σ', hσ', hM', hcur', hrow', htbl', htable'⟩ :=
    programBoundedIn_generatorProgFull_valid_ctl_state M tbl φ σ hcore0
      (by simpa [σ, tbl, φ, pref, M, N] using hpre.1) (by simpa [σ, tbl, M, N] using hpre.2)
      hrow hlo_of
  have hencodeM := programBoundedIn_generatorProgFull_valid_encode_le_setupM p time d
    allowedIdx outIdx bits hwrite hblank hfalse htrue hallowed hout φ rfl
  obtain ⟨hsepCnt, hsepFull, hsepTmpAll, hsepCntAll, hsepPtrAll, hsepRowAll⟩ :=
    emit_output_sep_bounds M φ hencodeM
  obtain ⟨hreg1, hreg2, hCurTmp, hCurCnt, hCurPtr, hCurRow, hCurRowCnt,
      _, hTmpCnt, hTmpPtr, hTmpRow, hTmpRowCnt, _, hCntPtr,
      hCntRow, _, _, hPtrRow, _, _, hRowRowCnt, _⟩ := emitter_rowCountReg_regs_distinct
  have hctl := programBoundedIn_generatorProgFull_valid_ctl_le p time d pref allowedIdx outIdx N
  have hreg : ∀ j ≤ 70, j ≤ B ∧ M + j ≤ B := fun j hj =>
    ⟨(Nat.le_add_left _ _).trans (hctl j hj), hctl j hj⟩
  obtain ⟨hbaseJ, hσ0B⟩ := hreg emCurJ (by norm_num [emCurJ])
  obtain ⟨htmpJ, hσ1B⟩ := hreg emTmpJ (by norm_num [emTmpJ])
  obtain ⟨hcntJ, hσ2B⟩ := hreg emCntJ (by norm_num [emCntJ])
  obtain ⟨hptrJ, hσ3B⟩ := hreg emPtrJ (by norm_num [emPtrJ])
  obtain ⟨hrowJ, hσ4B⟩ := hreg emRowJ (by norm_num [emRowJ])
  obtain ⟨hrowCntJ, hσ5B⟩ := hreg rowCountReg (by norm_num [rowCountReg])
  obtain ⟨htblJ, hσ6B⟩ := hreg emTblJ (by norm_num [emTblJ])
  have hCurStart : emitOutputStart ≤ B := by
    simpa [emitOutputStart, emCurJ] using hbaseJ
  have hbasePB : ProgramBoundedIn B σ (ctlAssign emCurJ (.const emitOutputStart)) :=
    programBoundedIn_ctlAssign_const B M emCurJ emitOutputStart σ hcore0 hσ0B hCurStart
  subst hσ'
  refine ⟨programBoundedIn_generatorProgFromBits p time d allowedIdx outIdx bits, hbasePB, ?_⟩
  exact programBoundedIn_emitClauseTableProg B emCurJ emTmpJ emCntJ emPtrJ emRowJ
      rowCountReg emTblJ M emitOutputStart tbl φ _
      hreg1 hreg2 hCurTmp hCurCnt hCurPtr hCurRow hCurRowCnt
      hTmpCnt hTmpPtr hTmpRow hTmpRowCnt hCntPtr hCntRow hPtrRow hRowRowCnt
      hM' hcur' (by norm_num [emitOutputStart])
      hrow' htbl' htable'.1 htable'.2.1 htable'.2.2
      hsepCnt hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
      (hlo_of emCurJ (by norm_num [emCurJ]))
      (hlo_of emTmpJ (by norm_num [emTmpJ]))
      (hlo_of emCntJ (by norm_num [emCntJ]))
      (hlo_of emPtrJ (by norm_num [emPtrJ]))
      (hlo_of emRowJ (by norm_num [emRowJ]))
      hbaseJ htmpJ hcntJ hptrJ hrowJ hrowCntJ htblJ hσ0B hσ1B hσ2B hσ3B hσ4B hσ5B hσ6B
      (hsepCnt.trans hσ5B)
      (programBoundedIn_generatorProgFull_valid_table_width p time d pref allowedIdx outIdx N φ rfl)

/-! ## Boundedness of the ABI suffix -/

/-- The ABI metadata writes and finalizer fit when the output cursor and slots are bounded. -/
lemma programBoundedIn_generatorProgAbi_valid_suffix
    (B M : ℕ) (σ : Store) (hB1 : 1 ≤ B) (hMcurB : M + emCurJ ≤ B)
    (hStartB : emitOutputStart ≤ B) (hIdx2 : abiOutBaseReg ≤ B)
    (hIdx3 : abiOutLenReg ≤ B) (hσ0 : σ 0 = M)
    (hσcurB : σ (M + emCurJ) ≤ B) :
    ProgramBoundedIn B σ
      ((Program.assign abiOutBaseReg (.const emitOutputStart)).seq
        ((Program.assign abiOutLenReg (.sub (ctlCell emCurJ) (.const emitOutputStart))).seq
          (finalizeOutputProg abiOutBaseReg abiOutLenReg))) := by
  have hStartNat : 8 ≤ B := by simpa [emitOutputStart] using hStartB
  have hbase : ProgramBoundedIn B σ
      (Program.assign abiOutBaseReg (.const emitOutputStart)) := by
    apply programBoundedIn_assign
    · exact hIdx2
    · simp [ExprBoundedIn, emitOutputStart]
      exact hStartNat
  let σ1 := (Program.assign abiOutBaseReg (.const emitOutputStart)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    rw [eval_assign, writeReg_diff _ abiOutBaseReg _ 0 (by norm_num [abiOutBaseReg]), hσ0]
  have hσ1cur : σ1 (M + emCurJ) = σ (M + emCurJ) := by
    dsimp [σ1]
    have hne : M + emCurJ ≠ abiOutBaseReg := by
      norm_num [abiOutBaseReg, emCurJ]
    rw [eval_assign, writeReg_diff _ abiOutBaseReg _ _ hne]
  have hctl : ExprBoundedIn B σ1 (ctlCell emCurJ) :=
    exprBoundedIn_ctlCell B M emCurJ σ1 hσ10 hMcurB
  have hctlVal : (ctlCell emCurJ).eval σ1 ≤ B := by
    calc
      (ctlCell emCurJ).eval σ1 = σ1 (M + emCurJ) := by simp [ctlCell_eval, hσ10]
      _ = σ (M + emCurJ) := hσ1cur
      _ ≤ B := hσcurB
  have hsub : ExprBoundedIn B σ1
      (.sub (ctlCell emCurJ) (.const emitOutputStart)) := by
    refine ⟨hctl, ?_, hctlVal⟩
    simp [ExprBoundedIn, emitOutputStart]
    exact hStartNat
  have hlen : ProgramBoundedIn B σ1
      (Program.assign abiOutLenReg (.sub (ctlCell emCurJ) (.const emitOutputStart))) := by
    apply programBoundedIn_assign
    · exact hIdx3
    · exact hsub
  let σ2 := (Program.assign abiOutLenReg
      (.sub (ctlCell emCurJ) (.const emitOutputStart))).eval σ1
  have hfin : ProgramBoundedIn B σ2 (finalizeOutputProg abiOutBaseReg abiOutLenReg) :=
    programBoundedIn_finalizeOutputProg B abiOutBaseReg abiOutLenReg σ2 hB1 hIdx2 hIdx3
  exact ⟨hbase, ⟨hlen, hfin⟩⟩

/-- The generator followed by the ABI metadata writes and finalizer remains
    bounded by the same envelope as the emitted producer. -/
lemma programBoundedIn_generatorProgAbi_valid (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hfalse : d.falseIdx < d.numLetters + 1)
    (htrue : d.trueIdx < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    ProgramBoundedIn
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (bitInputStore bits) (generatorProgAbi p time d allowedIdx outIdx) := by
  let N := bits.length
  let pref := prefixWord d bits
  let M := setupM p time d allowedIdx N
  let φ := descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d pref (p.eval N)
      allowedIdx outIdx ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
  let out := encodeCNF φ
  let B := (envB p time d pref allowedIdx outIdx).eval N
  let σ := (generatorProgFull p time d allowedIdx outIdx).eval (bitInputStore bits)
  have hpref : ∀ a ∈ pref, a < d.numLetters + 1 := by
    exact prefixWord_valid_of_true_false d bits hfalse htrue
  have hfullPB := programBoundedIn_generatorProgFull_valid p time d allowedIdx outIdx bits
    hwrite hblank hfalse htrue hallowed hout
  have hfull := generatorProgFull_meets_emitter_output p time d allowedIdx outIdx bits
    hwrite hblank hpref hallowed hout
  have hσ0 : σ 0 = M := by simpa [σ, M, N] using hfull.2.2
  have hσcur : σ (M + emCurJ) = emitOutputStart + out.length := by
    simpa [σ, out, φ, M, N] using hfull.2.1
  have hB1 : 1 ≤ B := by
    have hK := envK_ge_one p time d pref allowedIdx outIdx N
    have hKB := envB_ge_envK p time d pref allowedIdx outIdx N
    omega
  have hctl := programBoundedIn_generatorProgFull_valid_ctl_le p time d pref allowedIdx outIdx N
  have hMcurB : M + emCurJ ≤ B := by
    simpa [M, B] using hctl emCurJ (by norm_num [emCurJ])
  have hStartB : emitOutputStart ≤ B := by
    norm_num [emitOutputStart, emCurJ] at hMcurB ⊢
    omega
  have hStartNat : 8 ≤ B := by simpa [emitOutputStart] using hStartB
  have hIdx2 : abiOutBaseReg ≤ B := by
    norm_num [abiOutBaseReg]
    omega
  have hIdx3 : abiOutLenReg ≤ B := by
    norm_num [abiOutLenReg]
    omega
  have hencodeM : out.length ≤ M := by
    simpa [out, M, N] using
      programBoundedIn_generatorProgFull_valid_encode_le_setupM p time d allowedIdx outIdx bits
        hwrite hblank hfalse htrue hallowed hout φ rfl
  have hσcurB : σ (M + emCurJ) ≤ B := by
    rw [hσcur]
    calc
      emitOutputStart + out.length ≤ emitOutputStart + M := Nat.add_le_add_left hencodeM _
      _ = M + emCurJ := by norm_num [emitOutputStart, emCurJ]; omega
      _ ≤ B := hMcurB
  have htail := programBoundedIn_generatorProgAbi_valid_suffix B M σ hB1 hMcurB
    hStartB hIdx2 hIdx3 hσ0 hσcurB
  unfold generatorProgAbi
  change ProgramBoundedIn B (bitInputStore bits)
    (generatorProgFull p time d allowedIdx outIdx |>.seq
      ((Program.assign abiOutBaseReg (.const emitOutputStart)).seq
        ((Program.assign abiOutLenReg (.sub (ctlCell emCurJ) (.const emitOutputStart))).seq
          (finalizeOutputProg abiOutBaseReg abiOutLenReg))))
  exact ⟨hfullPB, htail⟩

/-! ## Scan-free composition -/

lemma scanFree_finalizeOutputProg_abi :
    ScanFree (finalizeOutputProg abiOutBaseReg abiOutLenReg) := by
  unfold finalizeOutputProg
  simp [ScanFree]

lemma scanFree_generator_prog_abi_suffix :
    ScanFree ((Program.assign abiOutBaseReg (.const emitOutputStart)).seq
      ((Program.assign abiOutLenReg (.sub (ctlCell emCurJ) (.const emitOutputStart))).seq
        (finalizeOutputProg abiOutBaseReg abiOutLenReg))) := by
  unfold ScanFree
  exact ⟨trivial, ⟨trivial, scanFree_finalizeOutputProg_abi⟩⟩

lemma scanFree_generatorProgAbi (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ScanFree (generatorProgAbi p time d allowedIdx outIdx) := by
  unfold generatorProgAbi
  exact ⟨scanFree_generatorProgFull p time d allowedIdx outIdx,
    scanFree_generator_prog_abi_suffix⟩


end NPComplete.CookLevin

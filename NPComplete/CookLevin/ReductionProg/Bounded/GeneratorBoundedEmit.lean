module

public import NPComplete.CookLevin.ReductionProg.GeneratorAbi
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedRowCount
public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalizeBody

/-!
# Bounded clause emission

Each clause must fit inside the generator's bounded store before the outer program can be certified.
This module isolates bounds for one emitted clause and the clause table so later generator proofs
can reuse these local memory estimates.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat encodeNat_length)

/-! ## Boundedness of one emitted clause -/

lemma programBoundedIn_emitClauseBody (Bp curJ tmpJ cntJ ptrJ rowJ M cur row cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ)
    (hCurRow : curJ ≠ rowJ) (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ)
    (hTmpRow : tmpJ ≠ rowJ) (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMcntJBp : M + cntJ ≤ Bp) (hMptrJBp : M + ptrJ ≤ Bp)
    (hMrowJBp : M + rowJ ≤ Bp)
    (hrowWidthBp : row + 2 * cnt + 2 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitClauseBody curJ tmpJ cntJ ptrJ rowJ) := by
  obtain ⟨σC, hCcur, hC0, hCcnt, hCptr, hCtag, hCdata, hCeq, hCframe⟩ :=
    emitClauseBody_state_upto_ptr_two_sided curJ tmpJ cntJ ptrJ rowJ M cur row cnt tag d σ
      hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur hcur1 hrowCell hcntCell htagAll hdataAll hloCnt hloPtr hsepCntAll hsepPtrAll
  have hvalA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    simp [Expr.eval, ctlCell_eval, hM, hrowCell, hcntCell]
  have heA : ExprBoundedIn Bp σ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) := by
    refine ⟨⟨RAMToTM.exprBoundedIn_ctlCell Bp rowJ σ hrowJBp (by rw [hM]; omega),
      by simp only [ExprBoundedIn]; omega, ?_⟩, ?_⟩
    · simp [Expr.eval, ctlCell_eval, hM, hrowCell]
      omega
    · simp [Expr.eval, ctlCell_eval, hM, hrowCell]
      omega
  have hPB1 : ProgramBoundedIn Bp σ
      (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))) := by
    unfold ctlAssign ProgramBoundedIn
    refine ⟨RAMToTM.exprBoundedIn_ctlAddr Bp cntJ σ hcntJBp (by rw [hM]; omega), heA, ?_⟩
    rw [ctlAddr_eval, hM]
    omega
  let σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
  have hσA0 : σA 0 = M := by
    dsimp [σA]
    rw [ctlAssign_eval_diff cntJ _ σ 0 (by rw [hM]; omega), hM]
  have hσAcur : σA (M + curJ) = cur := by
    dsimp [σA]
    rw [ctlAssign_eval_diff cntJ _ σ (M + curJ) (by rw [hM]; omega), hcur]
  have hσArow : σA (M + rowJ) = row := by
    dsimp [σA]
    rw [ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by rw [hM]; omega), hrowCell]
  have hσAcnt : σA (M + cntJ) = cnt := by
    dsimp [σA]
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]
    exact hvalA
  have heB : ExprBoundedIn Bp σA (Expr.add (ctlCell rowJ) (Expr.const 2)) := by
    refine ⟨RAMToTM.exprBoundedIn_ctlCell Bp rowJ σA hrowJBp (by rw [hσA0]; omega),
      by simp only [ExprBoundedIn]; omega, ?_⟩
    simp [Expr.eval, ctlCell_eval, hσA0, hσArow]
    omega
  have hPB2 : ProgramBoundedIn Bp σA
      (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))) := by
    unfold ctlAssign ProgramBoundedIn
    refine ⟨RAMToTM.exprBoundedIn_ctlAddr Bp ptrJ σA hptrJBp (by rw [hσA0]; omega), heB, ?_⟩
    rw [ctlAddr_eval, hσA0]
    omega
  have hCcnt' : σC (M + cntJ) = cnt := hCcnt
  have hCptr' : σC (M + ptrJ) = row + 2 := hCptr
  have hCtag' : ∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0 := hCtag
  have hCdata' : ∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i := hCdata
  have hcurNBp : cur + cnt + 1 ≤ Bp := by
    have hnonneg : 0 ≤ ((List.range cnt).flatMap
        (fun i => [tag i] ++ encodeNat (d i))).length := Nat.zero_le _
    omega
  have hPB3 : ProgramBoundedIn Bp σC (emitOpsListProg curJ tmpJ cntJ ptrJ) :=
    programBoundedIn_emitOpsListProg Bp curJ tmpJ cntJ ptrJ M cur row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hC0 hCcur hcur1 hCcnt' hCptr' hCtag' hCdata'
      (by omega) hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
      hcurJBp htmpJBp hcntJBp hptrJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp
      hcurNBp hrowWidthBp
  have hOps := emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M cur row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hC0 hCcur hcur1 hCcnt' hCptr' hCtag' hCdata'
      (by omega) hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
  have hctlD : (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC 0 = M := hOps.2.2.1
  let σD := (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC
  have hσD0 : σD 0 = M := hctlD
  have hPB4 : ProgramBoundedIn Bp σD (ctlAssign rowJ (ctlCell ptrJ)) := by
    unfold ctlAssign ProgramBoundedIn
    refine ⟨RAMToTM.exprBoundedIn_ctlAddr Bp rowJ σD hrowJBp (by rw [hσD0]; omega),
      RAMToTM.exprBoundedIn_ctlCell Bp ptrJ σD hptrJBp (by rw [hσD0]; omega), ?_⟩
    rw [ctlAddr_eval, hσD0]
    omega
  unfold emitClauseBody ProgramBoundedIn
  refine ⟨⟨⟨hPB1, ?_⟩, ?_⟩, ?_⟩
  · exact hPB2
  · rw [eval_seq, ← show σA =
        (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ by rfl,
      hCeq]
    exact hPB3
  · rw [eval_seq, eval_seq,
      ← show σA =
        (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ by rfl,
      hCeq]
    exact hPB4

/-! ## Boundedness of one clause-loop iteration -/

lemma programBoundedIn_emitClauseBody_of_inv (Bp curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt : ℕ)
    (φ : CNF) (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ)
    (hCurRow : curJ ≠ rowJ) (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ)
    (hTmpRow : tmpJ ≠ rowJ) (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ) (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + curJ)
    (hsepTmpAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + tmpJ)
    (hsepCntAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + cntJ)
    (hsepPtrAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + ptrJ)
    (hsepRowAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMcntJBp : M + cntJ ≤ Bp) (hMptrJBp : M + ptrJ ≤ Bp)
    (hMrowJBp : M + rowJ ≤ Bp)
    (hTableWidthBp : tbl + rowTableWidth (cnfCnt φ) rowCnt ≤ Bp)
    (hrowCntEq : rowCnt = φ.clauses.length)
    (m : ℕ) (hmrowCnt : m < rowCnt) (τ : Store)
    (hInv : ClauseTableInv curJ rowJ M cur0 tbl φ m τ) (hM : τ 0 = M) :
    ClauseTableInv curJ rowJ M cur0 tbl φ (m + 1)
      ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) ∧
    (emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ 0 = M ∧
    ProgramBoundedIn Bp τ (emitClauseBody curJ tmpJ cntJ ptrJ rowJ) := by
  obtain ⟨hrowPos, hcurPos, hcntAll, htagAll, hdataAll⟩ := hInv
  have hmφ : m < φ.clauses.length := by omega
  let row := tbl + rowTableWidth (cnfCnt φ) m
  have hrowCell : τ (M + rowJ) = row := hrowPos
  have hcntCell : τ (row + 1) = cnfCnt φ m := by
    simpa [row] using hcntAll m hmφ
  have htagRow : ∀ i, i < cnfCnt φ m →
      τ (row + 2 + 2 * i) = if cnfTag φ m i then 1 else 0 := by
    intro i hi
    simpa [row] using htagAll m hmφ i hi
  have hdataRow : ∀ i, i < cnfCnt φ m →
      τ (row + 2 + 2 * i + 1) = cnfVar φ m i := by
    intro i hi
    simpa [row] using hdataAll m hmφ i hi
  have hloCurRow : M + curJ < row := by omega
  have hloTmpRow : M + tmpJ < row := by omega
  have hloCntRow : M + cntJ < row := by omega
  have hloPtrRow : M + ptrJ < row := by omega
  have hcur'1 : 1 ≤ τ (M + curJ) := by rw [hcurPos]; omega
  have hkey : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length
      ≤ cur0 + clausePrefixBitsLen φ φ.clauses.length := by
    rw [hcurPos]
    have hp := clausePrefixBitsLen_clause_le φ m hmφ
    have hl := emitClauseBody_len_eq φ m
    omega
  have hsepFullRow : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + curJ := by
    omega
  have hsepTmpRow : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + tmpJ := by
    omega
  have hsepCntRow : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + cntJ := by
    omega
  have hsepPtrRow : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + ptrJ := by
    omega
  have hsepRowRow : τ (M + curJ) + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + rowJ := by
    omega
  have hrowWidthBp : row + 2 * cnfCnt φ m + 2 ≤ Bp := by
    have hmono : rowTableWidth (cnfCnt φ) (m + 1) ≤ rowTableWidth (cnfCnt φ) rowCnt := by
      unfold rowTableWidth
      have hs := flatMap_range_length_split
        (fun q => List.replicate (2 + 2 * cnfCnt φ q) false) rowCnt (m + 1)
        (by omega)
      omega
    have hs := rowTableWidth_succ (cnfCnt φ) m
    dsimp [row]
    omega
  have hbody := emitClauseTableProg_hbody curJ tmpJ cntJ ptrJ rowJ M cur0 tbl φ
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
    hcur01 hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow
    m hmφ τ (τ (M + curJ)) ⟨hrowPos, hcurPos, hcntAll, htagAll, hdataAll⟩ hM rfl
  obtain ⟨_, _, hctl0, _, hInv'⟩ := hbody
  have hPB := programBoundedIn_emitClauseBody Bp curJ tmpJ cntJ ptrJ rowJ M
      (τ (M + curJ)) row (cnfCnt φ m) (fun i => cnfTag φ m i) (fun i => cnfVar φ m i) τ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM rfl hcur'1 hrowCell hcntCell htagRow hdataRow
      hloCurRow hloTmpRow hloCntRow hloPtrRow hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
      hcurJBp htmpJBp hcntJBp hptrJBp hrowJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp hMrowJBp
      hrowWidthBp
  exact ⟨hInv', hctl0, hPB⟩

lemma programBoundedIn_emitClauseTableProg (Bp curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl : ℕ)
    (φ : CNF) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ)
    (hCurRow : curJ ≠ rowJ) (hCurRowCnt : curJ ≠ rowCntJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hTmpRowCnt : tmpJ ≠ rowCntJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ)
    (hRowRowCnt : rowJ ≠ rowCntJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCnt : σ (M + rowCntJ) = φ.clauses.length) (htbl : σ (M + tblJ) = tbl)
    (hcntAll : ∀ q, q < φ.clauses.length →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 1) = cnfCnt φ q)
    (htagAll : ∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) = if cnfTag φ q i then 1 else 0)
    (hdataAll : ∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) = cnfVar φ q i)
    (hsepCnt : cur + φ.clauses.length + 1 ≤ M + rowCntJ)
    (hsepFull : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + curJ)
    (hsepTmpAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + tmpJ)
    (hsepCntAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + cntJ)
    (hsepPtrAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + ptrJ)
    (hsepRowAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp) (hrowCntJBp : rowCntJ ≤ Bp)
    (htblJBp : tblJ ≤ Bp) (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMcntJBp : M + cntJ ≤ Bp) (hMptrJBp : M + ptrJ ≤ Bp)
    (hMrowJBp : M + rowJ ≤ Bp) (hMrowCntJBp : M + rowCntJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp)
    (hcurNBp : cur + φ.clauses.length + 1 ≤ Bp)
    (hTableWidthBp : tbl + rowTableWidth (cnfCnt φ) φ.clauses.length ≤ Bp) :
    ProgramBoundedIn Bp σ
      (emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ) := by
  unfold emitClauseTableProg ProgramBoundedIn
  have hexprTbl : (ctlCell tblJ).eval σ = tbl := by
    rw [ctlCell_eval, hM, htbl]
  have hσ0row : (ctlAssign rowJ (ctlCell tblJ)).eval σ (M + rowJ) = tbl := by
    have h := ctlAssign_eval_same rowJ (ctlCell tblJ) σ
    rw [hM] at h
    rw [h]
    exact hexprTbl
  have hPB0 : ProgramBoundedIn Bp σ (ctlAssign rowJ (ctlCell tblJ)) := by
    unfold ProgramBoundedIn ctlAssign
    refine ⟨RAMToTM.exprBoundedIn_ctlAddr Bp rowJ σ hrowJBp (by rw [hM]; omega),
      RAMToTM.exprBoundedIn_ctlCell Bp tblJ σ htblJBp (by rw [hM]; omega), ?_⟩
    rw [ctlAddr_eval, hM]
    omega
  refine ⟨hPB0, ?_⟩
  let σ0 := (ctlAssign rowJ (ctlCell tblJ)).eval σ
  have hσ0row' : σ0 (M + rowJ) = tbl := by
    dsimp [σ0]
    exact hσ0row
  have hσ0frame : ∀ r, r ≠ M + rowJ → σ0 r = σ r :=
    fun r hr => ctlAssign_eval_diff rowJ _ σ r (by rw [hM]; exact hr)
  obtain ⟨hσ00, hσ0cur, hσ0rowCnt, hInv0⟩ :=
    emitClauseTableProg_eval_state_inv0 curJ tmpJ rowJ rowCntJ M cur tbl φ σ σ0
      hc1 hc2 hCurTmp hCurRow hTmpRow hRowRowCnt hM hcur hcur1 hrowCnt
      hcntAll htagAll hdataAll hsepFull hsepRowAll hloCur hloTmp hloRow hσ0frame hσ0row'
  have hsepBodyFull : cur + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + curJ := by exact hsepFull
  have hsepBodyTmp : cur + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + tmpJ := by exact hsepTmpAll
  have hsepBodyCnt : cur + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + cntJ := by exact hsepCntAll
  have hsepBodyPtr : cur + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + ptrJ := by exact hsepPtrAll
  have hsepBodyRow : cur + φ.clauses.length + 1
      + clausePrefixBitsLen φ φ.clauses.length ≤ M + rowJ := by exact hsepRowAll
  have hbody : ∀ m, m < φ.clauses.length → ∀ τ,
      ClauseTableInv curJ rowJ M (cur + φ.clauses.length + 1) tbl φ m τ →
      τ 0 = M →
      ClauseTableInv curJ rowJ M (cur + φ.clauses.length + 1) tbl φ (m + 1)
        ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) ∧
      (emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ 0 = M ∧
      ProgramBoundedIn Bp τ (emitClauseBody curJ tmpJ cntJ ptrJ rowJ) := by
    intro m hm τ hInv hτ0
    exact programBoundedIn_emitClauseBody_of_inv Bp curJ tmpJ cntJ ptrJ rowJ M
      (cur + φ.clauses.length + 1) tbl φ.clauses.length φ hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      (by omega) hsepBodyFull hsepBodyTmp hsepBodyCnt hsepBodyPtr hsepBodyRow
      hloCur hloTmp hloCnt hloPtr hloRow hcurJBp htmpJBp hcntJBp hptrJBp hrowJBp
      hMcurJBp hMtmpJBp hMcntJBp hMptrJBp hMrowJBp hTableWidthBp rfl m hm τ hInv hτ0
  have hsepFull' : cur + φ.clauses.length + 1 ≤ M + curJ := by omega
  exact programBoundedIn_emitListProg Bp curJ tmpJ rowCntJ M cur φ.clauses.length
    (emitClauseBody curJ tmpJ cntJ ptrJ rowJ)
    (ClauseTableInv curJ rowJ M (cur + φ.clauses.length + 1) tbl φ) σ0
    hc1 hc2 hCurTmp hCurRowCnt.symm hTmpRowCnt.symm hσ00 hσ0cur hcur1 hσ0rowCnt
    hsepCnt hsepFull' hcurJBp htmpJBp hrowCntJBp hMcurJBp hMtmpJBp hMrowCntJBp
    hcurNBp hbody hInv0

lemma rowTableWidth_descTableauCNF_le_emitLenPoly (p time : Polynomial ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    let φ := descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d prefIdx (p.eval N)
      allowedIdx outIdx ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
    rowTableWidth (cnfCnt φ) φ.clauses.length ≤
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N := by
  let W := (cookWindowPoly p time).eval N
  let T := (timePoly p time).eval N
  let P := p.eval N
  let n := d.numStates + 1
  let m := d.numLetters + 1
  let al := allowedIdx.length
  let φ := descTableauCNF (denseLayout n W m) d prefIdx P allowedIdx outIdx W T
  have heq := clauseCount_eq (denseLayout n W m) d prefIdx P allowedIdx outIdx W T
  have hCpoly : φ.clauses.length ≤
      (clauseCountPoly p time n m).eval N := by
    rw [← heq]
    exact clauseCount_le_poly p time d.numStates d.numLetters N
  have hW : ∀ q, q < φ.clauses.length → cnfCnt φ q ≤
      (emitWidthPoly p time n m al).eval N := by
    intro q hq
    have hmem : φ.clauses.getD q default ∈ φ.clauses := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    have hw := descTableauCNF_width_le (denseLayout n W m) d prefIdx P allowedIdx outIdx W T _ hmem
    change (φ.clauses.getD q default).lits.length ≤
      (emitWidthPoly p time n m al).eval N
    rw [show (emitWidthPoly p time n m al).eval N = n + W + m + al + 7 by
      simp [emitWidthPoly, W, n, m, al]]
    exact hw.trans (by omega)
  have hrow := rowTableWidth_le_count_mul (cnfCnt φ) φ.clauses.length
    ((emitWidthPoly p time n m al).eval N) hW
  have hE : 1 ≤ (emitWidthPoly p time n m al).eval N := by
    simp [emitWidthPoly, n, m, al]
  have hEV : 2 * (emitWidthPoly p time n m al).eval N ≤
      (emitWidthPoly p time n m al).eval N *
        ((varBoundPoly p time n m).eval N + 2) := by
    calc
      2 * (emitWidthPoly p time n m al).eval N =
          (emitWidthPoly p time n m al).eval N * 2 := by ring
      _ ≤ (emitWidthPoly p time n m al).eval N *
          ((varBoundPoly p time n m).eval N + 2) :=
        Nat.mul_le_mul_left _ (by omega)
  have hinner : 2 + 2 * (emitWidthPoly p time n m al).eval N ≤
      (emitWidthPoly p time n m al).eval N + 1 +
        (emitWidthPoly p time n m al).eval N *
          ((varBoundPoly p time n m).eval N + 2) := by omega
  have hmul : φ.clauses.length * (2 + 2 * (emitWidthPoly p time n m al).eval N) ≤
      (clauseCountPoly p time n m).eval N *
        ((emitWidthPoly p time n m al).eval N + 1 +
          (emitWidthPoly p time n m al).eval N *
            ((varBoundPoly p time n m).eval N + 2)) := by
    exact Nat.mul_le_mul hCpoly hinner
  have hfinal : φ.clauses.length * (2 + 2 * (emitWidthPoly p time n m al).eval N) ≤
      (emitLenPoly p time n m al).eval N := by
    rw [show (emitLenPoly p time n m al).eval N =
        (clauseCountPoly p time n m).eval N + 1 +
          (clauseCountPoly p time n m).eval N *
            ((emitWidthPoly p time n m al).eval N + 1 +
              (emitWidthPoly p time n m al).eval N *
                ((varBoundPoly p time n m).eval N + 2)) by
      simp [emitLenPoly]]
    omega
  have htotal := hrow.trans hfinal
  simpa [φ, n, m, W, T, P, al] using htotal

end NPComplete.CookLevin

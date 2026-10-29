module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseEmitProg

/-!
The generic row-table emitter (`emitRowTableProg`) writes variable-length rows with a unary row key
before each count-prefixed payload. Clause rows omit that key because `emitClauseBody` emits only
the clause payload. The outer loop therefore follows the same assembly pattern without a row-key
field in its invariant, per-iteration obligation, or final `emitListProg` chain.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr writeReg eval_seq eval_assign eval_assignInd
    eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits encodeNat encodeNat_length)

/-- Emit a whole clause table: stage `rowJ` at the table's base, then loop `emitClauseBody` once
    per clause via `emitListProg`, exactly as `emitRowTableProg` loops `emitRowBody` once per
    row. -/
def emitClauseTableProg (curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ : ℕ) : Program :=
  .seq (ctlAssign rowJ (ctlCell tblJ))
    (emitListProg curJ tmpJ rowCntJ (emitClauseBody curJ tmpJ cntJ ptrJ rowJ))

/-- Invariant for `emitClauseTableProg`'s clause loop after `m` clauses have been emitted from a
    table whose rows start at `tbl`: `rowJ` sits at the `m`-th clause's physical address (the
    prefix sum of earlier clauses' variable widths), the cursor sits exactly the combined encoded
    length of the first `m` clauses past `cur0`, and every clause's raw data (payload count and
    every literal's tag/data cells) is untouched — for *every* clause, not just the ones not yet
    emitted, since `emitClauseBody` never writes into the table region at all — mirroring
    `EmitRowTableInv` with the row-key conjunct dropped. -/
def ClauseTableInv (curJ rowJ M cur0 tbl : ℕ) (φ : CNF) (m : ℕ) (τ : Store) : Prop :=
  τ (M + rowJ) = tbl + rowTableWidth (cnfCnt φ) m ∧
  τ (M + curJ) = cur0 + clausePrefixBitsLen φ m ∧
  (∀ q, q < φ.clauses.length → τ (tbl + rowTableWidth (cnfCnt φ) q + 1) = cnfCnt φ q) ∧
  (∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
    τ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) = if cnfTag φ q i then 1 else 0) ∧
  (∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
    τ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) = cnfVar φ q i)

/-- `clausePrefixBitsLen`'s peel-off companion to `rowTableBitsLen_row_le`: the `m`-th clause's
    own encoded length fits between the prefix sum at `m` and the prefix sum at the table's full
    length, letting a per-iteration separation bound be read off a single global one. -/
lemma clausePrefixBitsLen_clause_le (φ : CNF) (m : ℕ) (hm : m < φ.clauses.length) :
    clausePrefixBitsLen φ m + (encodeClause (φ.clauses.getD m default)).length
      ≤ clausePrefixBitsLen φ φ.clauses.length := by
  have hsplit := flatMap_range_length_split
    (fun k => encodeClause (φ.clauses.getD k default)) φ.clauses.length (m + 1) (by omega)
  have heq1 : clausePrefixBitsLen φ (m + 1)
      = ((List.range (m + 1)).flatMap (fun k => encodeClause (φ.clauses.getD k default))).length
      := rfl
  have heq2 : clausePrefixBitsLen φ φ.clauses.length
      = ((List.range φ.clauses.length).flatMap
          (fun k => encodeClause (φ.clauses.getD k default))).length := rfl
  have hsucc := clausePrefixBitsLen_succ φ m
  omega

/-- A clause's encoded length, read off in the count/tag/datum shape `emitClauseBody` actually
    produces — the bridge between `encodeClause_eq_ops`'s list equality and the arithmetic the
    per-iteration proof needs. -/
lemma emitClauseBody_len_eq (φ : CNF) (m : ℕ) :
    (encodeClause (φ.clauses.getD m default)).length
      = (cnfCnt φ m + 1)
        + ((List.range (cnfCnt φ m)).flatMap
            (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length := by
  rw [encodeClause_eq_ops, List.length_append, encodeNat_length]; rfl

/-- The per-iteration correctness `emitListProg_eval_state`/`emit_loop_flatMap` need from
    `emitClauseBody`, under `ClauseTableInv`. The five separation bounds (`hsepFull` through
    `hsepRowAll`) all compare `cur0 + (the whole table's encoded length)` against a control-cell
    wall; `clausePrefixBitsLen_clause_le` peels the current clause's own bound off that global
    one, and `emitClauseBody_frame_two_sided`'s two-sided frame is what lets every clause's raw
    data — not just the current one — survive each iteration. It parallels
    `emitRowTableProg_hbody`, minus the row-key stage. -/
lemma emitClauseTableProg_hbody (curJ tmpJ cntJ ptrJ rowJ M cur0 tbl : ℕ) (φ : CNF)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + curJ)
    (hsepTmpAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + tmpJ)
    (hsepCntAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + cntJ)
    (hsepPtrAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + ptrJ)
    (hsepRowAll : cur0 + clausePrefixBitsLen φ φ.clauses.length ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    ∀ m, m < φ.clauses.length → ∀ (τ : Store) (cur' : ℕ),
      ClauseTableInv curJ rowJ M cur0 tbl φ m τ →
      τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) cur'
        (encodeClause (φ.clauses.getD m default)) ∧
      ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) (M + curJ)
        = cur' + (encodeClause (φ.clauses.getD m default)).length ∧
      ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ →
        (emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ r = τ r) ∧
      ClauseTableInv curJ rowJ M cur0 tbl φ (m + 1)
        ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) := by
  intro m hm τ cur' hInv hM hcur'
  obtain ⟨hrowPos, hcurPos, hcntAll, htagAll2, hdataAll2⟩ := hInv
  set row := tbl + rowTableWidth (cnfCnt φ) m with hrowdef
  have hrowCell : τ (M + rowJ) = row := hrowPos
  have hcntCell : τ (row + 1) = cnfCnt φ m := hcntAll m hm
  have htagAllRow : ∀ i, i < cnfCnt φ m → τ (row + 2 + 2 * i) = if cnfTag φ m i then 1 else 0 :=
    fun i hi => htagAll2 m hm i hi
  have hdataAllRow : ∀ i, i < cnfCnt φ m → τ (row + 2 + 2 * i + 1) = cnfVar φ m i :=
    fun i hi => hdataAll2 m hm i hi
  have hloCurRow : M + curJ < row := by omega
  have hloTmpRow : M + tmpJ < row := by omega
  have hloCntRow : M + cntJ < row := by omega
  have hloPtrRow : M + ptrJ < row := by omega
  have hcur'eq : cur' = cur0 + clausePrefixBitsLen φ m := hcur'.symm.trans hcurPos
  have hkey := clausePrefixBitsLen_clause_le φ m hm
  have hlenEq := emitClauseBody_len_eq φ m
  have hsepFullRow : cur' + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + curJ := by omega
  have hsepTmpRow : cur' + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + tmpJ := by omega
  have hsepCntRow : cur' + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + cntJ := by omega
  have hsepPtrRow : cur' + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + ptrJ := by omega
  have hsepRowRow : cur' + (cnfCnt φ m + 1)
      + ((List.range (cnfCnt φ m)).flatMap
          (fun i => [cnfTag φ m i] ++ encodeNat (cnfVar φ m i))).length ≤ M + rowJ := by omega
  obtain ⟨hbits, hcursor, hctl0, hrowFinal⟩ :=
    emitClauseBody_eval_state curJ tmpJ cntJ ptrJ rowJ M cur' row (cnfCnt φ m)
      (cnfTag φ m) (cnfVar φ m) τ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur' (by omega) hrowCell hcntCell htagAllRow hdataAllRow
      hloCurRow hloTmpRow hloCntRow hloPtrRow
      hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
  have hframe2 :=
    emitClauseBody_frame_two_sided curJ tmpJ cntJ ptrJ rowJ M cur' row
      (cnfCnt φ m) (cnfTag φ m) (cnfVar φ m) τ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur' (by omega) hrowCell hcntCell htagAllRow hdataAllRow
      hloCurRow hloTmpRow hloCntRow hloPtrRow
      hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
  have hbitsClause : BitsAt ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) cur'
      (encodeClause (φ.clauses.getD m default)) := by
    rw [encodeClause_eq_ops]; exact hbits
  have hcursorClause : ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval τ) (M + curJ)
      = cur' + (encodeClause (φ.clauses.getD m default)).length := by omega
  refine ⟨hbitsClause, hcursorClause, hctl0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr1 hr2
    exact hframe2 r hr2 (by omega) (by omega) (by omega) (by omega) (Or.inl hr1)
  · rw [hrowFinal, hrowdef]
    have hsucc := rowTableWidth_succ (cnfCnt φ) m
    omega
  · rw [hcursor, hcur'eq]
    have hsucc := clausePrefixBitsLen_succ φ m
    omega
  · intro q hq
    exact (hframe2 (tbl + rowTableWidth (cnfCnt φ) q + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega))).trans (hcntAll q hq)
  · intro q hq i hi
    exact (hframe2 (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega))).trans (htagAll2 q hq i hi)
  · intro q hq i hi
    exact (hframe2 (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega) (Or.inr (by omega))).trans (hdataAll2 q hq i hi)

/-- Initial clause-loop invariant for `emitClauseTableProg`: after staging `rowJ := tbl` (the
    store `σ0`, which differs from `σ` only at `M + rowJ`) and emitting the clause count, the
    invariant holds at clause `0`. Isolates the "everything else is unchanged" bookkeeping from
    the loop itself. -/
lemma emitClauseTableProg_eval_state_inv0 (curJ tmpJ rowJ rowCntJ M cur tbl : ℕ)
    (φ : CNF) (σ σ0 : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurRow : curJ ≠ rowJ) (hTmpRow : tmpJ ≠ rowJ)
    (hRowRowCnt : rowJ ≠ rowCntJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCnt : σ (M + rowCntJ) = φ.clauses.length)
    (hcntAll : ∀ q, q < φ.clauses.length →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 1) = cnfCnt φ q)
    (htagAll : ∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) = if cnfTag φ q i then 1 else 0)
    (hdataAll : ∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
      σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) = cnfVar φ q i)
    (hsepFull : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length
      ≤ M + curJ)
    (hsepRowAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length
      ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloRow : M + rowJ < tbl)
    (hσ0frame : ∀ r, r ≠ M + rowJ → σ0 r = σ r) (hσ0row : σ0 (M + rowJ) = tbl) :
    σ0 0 = M ∧ σ0 (M + curJ) = cur ∧ σ0 (M + rowCntJ) = φ.clauses.length ∧
    ClauseTableInv curJ rowJ M (cur + φ.clauses.length + 1) tbl φ 0
      ((emitNatProg curJ tmpJ (ctlCell rowCntJ)).eval σ0) := by
  have hσ00 : σ0 0 = M := by rw [hσ0frame 0 (by omega)]; exact hM
  have hσ0cur : σ0 (M + curJ) = cur := by rw [hσ0frame _ (by omega)]; exact hcur
  have hσ0rowCnt : σ0 (M + rowCntJ) = φ.clauses.length := by
    rw [hσ0frame _ (by omega)]; exact hrowCnt
  have hrowCntEval : (ctlCell rowCntJ).eval σ0 = φ.clauses.length := by
    rw [ctlCell_eval, hσ00, hσ0rowCnt]
  have hsep1 : cur + (ctlCell rowCntJ).eval σ0 < M + curJ := by rw [hrowCntEval]; omega
  obtain ⟨-, hcursor1, hframe1, -⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell rowCntJ) σ0 hc1 hc2 hCurTmp hσ00 hσ0cur
      hcur1 hsep1
  rw [hrowCntEval] at hcursor1 hframe1
  refine ⟨hσ00, hσ0cur, hσ0rowCnt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe1 (M + rowJ) (by omega) (by omega) (Or.inr (by omega)), hσ0row]
    simp [rowTableWidth]
  · rw [hcursor1]; simp [clausePrefixBitsLen]
  · intro q hq
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact hcntAll q hq
  · intro q hq i hi
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact htagAll q hq i hi
  · intro q hq i hi
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact hdataAll q hq i hi

/-- Bundled correctness of `emitClauseTableProg`: the store after running it holds the CNF's own
    encoding at the entry cursor, the cursor has advanced past the whole encoding, and cell `0`
    still holds `M`. Chains staging `rowJ := tbl` with `emitListProg_eval_state`, instantiated at
    `emitClauseTableProg_hbody` for the per-clause obligation, then converts the resulting
    `range`-indexed shape to `encodeCNF φ` via `encodeCNF_eq_rows` and `clausePrefixBitsLen_full`
    — mirroring `emitRowTableProg_eval_state`'s own top-level chaining. -/
lemma emitClauseTableProg_eval_state (curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl : ℕ)
    (φ : CNF) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hCurRowCnt : curJ ≠ rowCntJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hTmpRowCnt : tmpJ ≠ rowCntJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ)
    (hRowRowCnt : rowJ ≠ rowCntJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCnt : σ (M + rowCntJ) = φ.clauses.length) (htbl : σ (M + tblJ) = tbl)
    (hcntAll : ∀ q, q < φ.clauses.length → σ (tbl + rowTableWidth (cnfCnt φ) q + 1) = cnfCnt φ q)
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
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    BitsAt ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) cur
      (encodeCNF φ) ∧
    ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) (M + curJ)
      = cur + (encodeCNF φ).length ∧
    ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) 0 = M := by
  have hσ0frame : ∀ r, r ≠ M + rowJ →
      (ctlAssign rowJ (ctlCell tblJ)).eval σ r = σ r :=
    fun r hr => ctlAssign_eval_diff rowJ _ σ r (by rw [hM]; exact hr)
  have hσ0row : (ctlAssign rowJ (ctlCell tblJ)).eval σ (M + rowJ) = tbl := by
    have h := ctlAssign_eval_same rowJ (ctlCell tblJ) σ
    rw [hM, ctlCell_eval, hM, htbl] at h
    exact h
  obtain ⟨hσ00, hσ0cur, hσ0rowCnt, hInv0⟩ :=
    emitClauseTableProg_eval_state_inv0 curJ tmpJ rowJ rowCntJ M cur tbl φ σ _
      hc1 hc2 hCurTmp hCurRow hTmpRow hRowRowCnt hM hcur hcur1 hrowCnt
      hcntAll htagAll hdataAll hsepFull hsepRowAll hloCur hloTmp hloRow hσ0frame hσ0row
  have hbody := emitClauseTableProg_hbody curJ tmpJ cntJ ptrJ rowJ M
    (cur + φ.clauses.length + 1) tbl φ
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
    (by omega) hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow
  have hsepFull' : cur + φ.clauses.length + 1
      + ((List.range φ.clauses.length).flatMap
          (fun m => encodeClause (φ.clauses.getD m default))).length ≤ M + curJ := by
    have hlenEq : clausePrefixBitsLen φ φ.clauses.length
        = ((List.range φ.clauses.length).flatMap
            (fun m => encodeClause (φ.clauses.getD m default))).length := rfl
    rw [← hlenEq]; exact hsepFull
  have hstate := emitListProg_eval_state curJ tmpJ rowCntJ M cur φ.clauses.length
    (emitClauseBody curJ tmpJ cntJ ptrJ rowJ)
    (fun m => encodeClause (φ.clauses.getD m default))
    (ClauseTableInv curJ rowJ M (cur + φ.clauses.length + 1) tbl φ)
    ((ctlAssign rowJ (ctlCell tblJ)).eval σ)
    hc1 hc2 hCurTmp hCurRowCnt.symm hTmpRowCnt.symm
    hσ00 hσ0cur hcur1 hσ0rowCnt hsepCnt hsepFull' hbody hInv0
  have htop : (emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ
      = (emitListProg curJ tmpJ rowCntJ (emitClauseBody curJ tmpJ cntJ ptrJ rowJ)).eval
        ((ctlAssign rowJ (ctlCell tblJ)).eval σ) := by
    unfold emitClauseTableProg
    rw [eval_seq]
  refine ⟨?_, ?_, ?_⟩
  · rw [htop, encodeCNF_eq_rows]; exact hstate.1
  · rw [htop]
    have hlen : (encodeCNF φ).length
        = φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length := by
      have h := clausePrefixBitsLen_full φ
      omega
    rw [hlen]
    have hcursorState := hstate.2.1
    have hlenEq : ((List.range φ.clauses.length).flatMap
        (fun m => encodeClause (φ.clauses.getD m default))).length
        = clausePrefixBitsLen φ φ.clauses.length := rfl
    omega
  · rw [htop]; exact hstate.2.2.1

/-! ## The contract between the two halves of the producer

Naming the table's contents as one predicate fixes what the materializing half
has to achieve and what the emitting half may assume, so neither half has to
mention the other's loop structure. -/

/-- The clause table holds `φ`'s three columns at base `tbl`. -/
def ClauseTableAt (σ : Store) (tbl : ℕ) (φ : CNF) : Prop :=
  (∀ q, q < φ.clauses.length → σ (tbl + rowTableWidth (cnfCnt φ) q + 1) = cnfCnt φ q) ∧
  (∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
    σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i) = if cnfTag φ q i then 1 else 0) ∧
  (∀ q, q < φ.clauses.length → ∀ i, i < cnfCnt φ q →
    σ (tbl + rowTableWidth (cnfCnt φ) q + 2 + 2 * i + 1) = cnfVar φ q i)

/-- Under the table contract, the emitter writes the CNF encoding at the cursor,
advances the cursor by its length, and preserves cell 0. -/
lemma emitClauseTableProg_of_table_at (curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl : ℕ)
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
    (htable : ClauseTableAt σ tbl φ)
    (hsepCnt : cur + φ.clauses.length + 1 ≤ M + rowCntJ)
    (hsepFull : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + curJ)
    (hsepTmpAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + tmpJ)
    (hsepCntAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + cntJ)
    (hsepPtrAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + ptrJ)
    (hsepRowAll : cur + φ.clauses.length + 1 + clausePrefixBitsLen φ φ.clauses.length ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    BitsAt ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) cur
      (encodeCNF φ) ∧
    ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) (M + curJ)
      = cur + (encodeCNF φ).length ∧
    ((emitClauseTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) 0 = M :=
  emitClauseTableProg_eval_state curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl φ σ
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hCurRowCnt hTmpCnt hTmpPtr hTmpRow
    hTmpRowCnt hCntPtr hCntRow hPtrRow hRowRowCnt hM hcur hcur1 hrowCnt htbl
    htable.1 htable.2.1 htable.2.2
    hsepCnt hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseEmitShape
public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalize

/-!
# Clause Emission Program

The table writer needs a clause-level contract, whereas the underlying row machinery emits generic
tagged literals and values. This module connects that representation to each clause's own encoding so
the outer emission proofs can state their result in terms of the CNF being built.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr writeReg eval_seq eval_assign eval_assignInd
    eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits encodeNat encodeNat_length)

def emitClauseBody (curJ tmpJ cntJ ptrJ rowJ : ℕ) : Program :=
  .seq (.seq (.seq
    (ctlAssign cntJ (.regInd (.add (ctlCell rowJ) (.const 1))))
    (ctlAssign ptrJ (.add (ctlCell rowJ) (.const 2))))
    (emitOpsListProg curJ tmpJ cntJ ptrJ))
    (ctlAssign rowJ (ctlCell ptrJ))

lemma emitClauseBody_state_upto_ptr_two_sided (curJ tmpJ cntJ ptrJ rowJ M cur row cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepCntAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ) :
    ∃ σC : Store,
      σC (M + curJ) = cur ∧
      σC 0 = M ∧
      σC (M + cntJ) = cnt ∧
      σC (M + ptrJ) = row + 2 ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0) ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i) ∧
      ((ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval
        ((ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ)
        = σC) ∧
      (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + cntJ → r ≠ M + ptrJ → σC r = σ r) := by
  have hexprA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    have h1 : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ
        = σ (σ (σ 0 + rowJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hrowCell]; exact hcntCell
  have hσAcnt : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + cntJ) = cnt := by
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]; exact hexprA
  set σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
    with hσAdef
  have hσArow : σA (M + rowJ) = row := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by rw [hM]; omega)]
    exact hrowCell
  have hσAcur : σA (M + curJ) = cur := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + curJ) (by rw [hM]; omega)]
    exact hcur
  have hσA0 : σA 0 = M := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ 0 (by rw [hM]; omega)]
    exact hM
  have hσAtagAll : ∀ i, i < cnt → σA (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i) (by rw [hM]; omega)]
    exact htagAll i hi
  have hσAdataAll : ∀ i, i < cnt → σA (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i + 1) (by rw [hM]; omega)]
    exact hdataAll i hi
  have hexprC : (Expr.add (ctlCell rowJ) (Expr.const 2)).eval σA = row + 2 := by
    simp [Expr.eval, ctlCell_eval, hσA0, hσArow]
  have hσCptr : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σA
      (M + ptrJ) = row + 2 := by
    have h := ctlAssign_eval_same ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2)) σA
    rw [hσA0] at h
    rw [h]; exact hexprC
  refine ⟨(ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σA,
    ?_, ?_, ?_, hσCptr, ?_, ?_, rfl, ?_⟩
  · rw [ctlAssign_eval_diff ptrJ _ σA (M + curJ) (by rw [hσA0]; omega)]; exact hσAcur
  · rw [ctlAssign_eval_diff ptrJ _ σA 0 (by rw [hσA0]; omega)]; exact hσA0
  · rw [ctlAssign_eval_diff ptrJ _ σA (M + cntJ) (by rw [hσA0]; omega)]; exact hσAcnt
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σA (row + 2 + 2 * i) (by rw [hσA0]; omega)]
    exact hσAtagAll i hi
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σA (row + 2 + 2 * i + 1) (by rw [hσA0]; omega)]
    exact hσAdataAll i hi
  · intro r hrC hrT hrCnt hrP
    have e3 : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σA r = σA r :=
      ctlAssign_eval_diff ptrJ _ σA r (by rw [hσA0]; omega)
    have e5 : σA r = σ r := by
      rw [hσAdef, ctlAssign_eval_diff cntJ _ σ r (by rw [hM]; omega)]
    rw [e3, e5]

/-- Bundled correctness of `emitClauseBody`: the store after running it holds
    `encodeNat cnt ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))` at the
    entry cursor — the canonical variable-row shape once `tag i`/`d i` are supplied, without the
    unary row key carried by `emitRowBody`. The cursor has advanced past the whole row, cell `0`
    still holds `M`, and `rowJ` now points at the next row's head. The state sequence follows
    `emitRowBody_eval_state` without its row-key update: `σ → σA (cnt staged) → σC (ptr staged) →
    σD (ops emitted) → σE (rowJ advanced)`. -/
lemma emitClauseBody_eval_state (curJ tmpJ cntJ ptrJ rowJ M cur row cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
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
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    BitsAt ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ) cur
      (encodeNat cnt ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))) ∧
    ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ) (M + curJ)
      = cur + (cnt + 1) + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ∧
    ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ) 0 = M ∧
    ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ) (M + rowJ) = row + 2 * cnt + 2 := by
  have hexprA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    have h1 : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ
        = σ (σ (σ 0 + rowJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hrowCell]; exact hcntCell
  have hσAcnt : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + cntJ) = cnt := by
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]; exact hexprA
  set σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
    with hσAdef
  have hσArow : σA (M + rowJ) = row := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by omega)]; exact hrowCell
  have hσAcur : σA (M + curJ) = cur := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + curJ) (by omega)]; exact hcur
  have hσA0 : σA 0 = M := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ 0 (by omega)]; exact hM
  have hσAtagAll : ∀ i, i < cnt → σA (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i) (by omega)]
    exact htagAll i hi
  have hσAdataAll : ∀ i, i < cnt → σA (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i + 1) (by omega)]
    exact hdataAll i hi
  have hexprC : (Expr.add (ctlCell rowJ) (Expr.const 2)).eval σA = row + 2 := by
    simp [Expr.eval, ctlCell_eval, hσA0, hσArow]
  have hσCptr : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σA
      (M + ptrJ) = row + 2 := by
    have h := ctlAssign_eval_same ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2)) σA
    rw [hσA0] at h
    rw [h]; exact hexprC
  set σC := (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σA with hσCdef
  have hσCcur : σC (M + curJ) = cur := by
    rw [hσCdef, ctlAssign_eval_diff ptrJ _ σA (M + curJ) (by omega)]; exact hσAcur
  have hσC0 : σC 0 = M := by
    rw [hσCdef, ctlAssign_eval_diff ptrJ _ σA 0 (by omega)]; exact hσA0
  have hσCcnt : σC (M + cntJ) = cnt := by
    rw [hσCdef, ctlAssign_eval_diff ptrJ _ σA (M + cntJ) (by omega)]; exact hσAcnt
  have hσCtagAll : ∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hσCdef, ctlAssign_eval_diff ptrJ _ σA (row + 2 + 2 * i) (by omega)]
    exact hσAtagAll i hi
  have hσCdataAll : ∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hσCdef, ctlAssign_eval_diff ptrJ _ σA (row + 2 + 2 * i + 1) (by omega)]
    exact hσAdataAll i hi
  have hsepCnt : cur + cnt + 1 ≤ M + cntJ := by omega
  obtain ⟨hbitsD, hcursorD, hctlD, hptrD, hframeD⟩ :=
    emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M cur row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hσC0 hσCcur hcur1 hσCcnt hσCptr hσCtagAll hσCdataAll
      hsepCnt hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
  set σD := (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC with hσDdef
  have hexprE : (ctlCell ptrJ).eval σD = row + 2 + 2 * cnt := by
    rw [ctlCell_eval, hctlD, hptrD]
  have hσEptr : (ctlAssign rowJ (ctlCell ptrJ)).eval σD (M + rowJ) = row + 2 + 2 * cnt := by
    have h := ctlAssign_eval_same rowJ (ctlCell ptrJ) σD
    rw [hctlD] at h
    rw [h]; exact hexprE
  set σE := (ctlAssign rowJ (ctlCell ptrJ)).eval σD with hσEdef
  have hσEcur : σE (M + curJ) = cur + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    rw [hσEdef, ctlAssign_eval_diff rowJ _ σD (M + curJ) (by omega)]; exact hcursorD
  have hσE0 : σE 0 = M := by
    rw [hσEdef, ctlAssign_eval_diff rowJ _ σD 0 (by omega)]; exact hctlD
  have hlenCntOps : (encodeNat cnt ++ (List.range cnt).flatMap
      (fun i => [tag i] ++ encodeNat (d i))).length
      = cnt + 1 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    rw [List.length_append, encodeNat_length]
  have htop : (emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ = σE := by
    unfold emitClauseBody
    rw [eval_seq, eval_seq, eval_seq, ← hσAdef, ← hσCdef, ← hσDdef, ← hσEdef]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htop]
    apply bitsAt_of_frame σD _ cur (encodeNat cnt ++ (List.range cnt).flatMap
      (fun i => [tag i] ++ encodeNat (d i))) hbitsD
    intro r hr1 hr2
    rw [hlenCntOps] at hr2
    rw [hσEdef, ctlAssign_eval_diff rowJ _ σD r (by omega)]
  · rw [htop]; exact hσEcur
  · rw [htop]; exact hσE0
  · rw [htop, hσEptr]; ring

/-- `emitClauseBody`'s own two-sided frame: cells other than the five control cells, outside the
    whole row's write window, survive. Chains `emitClauseBody_state_upto_ptr_two_sided` with
    `emitOpsListProg_frame_two_sided`, then one more `ctlAssign` frame link for the final `rowJ`
    copy — the analogue of `emitRowBody_frame_two_sided` with the `rowKey` stage deleted. -/
lemma emitClauseBody_frame_two_sided (curJ tmpJ cntJ ptrJ rowJ M cur row cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
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
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    ∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + cntJ → r ≠ M + ptrJ → r ≠ M + rowJ →
      (r < cur ∨ cur + (cnt + 1)
        + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ r) →
      ((emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ) r = σ r := by
  obtain ⟨σC, hσCcur, hσC0, hσCcnt, hσCptr, hσCtagAll, hσCdataAll, hEq, hframeC⟩ :=
    emitClauseBody_state_upto_ptr_two_sided curJ tmpJ cntJ ptrJ rowJ M cur row cnt tag d σ
      hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur hcur1 hrowCell hcntCell htagAll hdataAll hloCnt hloPtr hsepCntAll hsepPtrAll
  have hsepCnt : cur + cnt + 1 ≤ M + cntJ := by omega
  have hframeD :=
    emitOpsListProg_frame_two_sided curJ tmpJ cntJ ptrJ M cur row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hσC0 hσCcur hcur1 hσCcnt hσCptr hσCtagAll hσCdataAll
      hsepCnt hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
  have hctlD : ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC) 0 = M := by
    obtain ⟨-, -, hctl0, -, -⟩ :=
      emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M cur row cnt tag d σC
        hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
        hσC0 hσCcur hcur1 hσCcnt hσCptr hσCtagAll hσCdataAll
        hsepCnt hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
    exact hctl0
  set σD := (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC with hσDdef
  set σE := (ctlAssign rowJ (ctlCell ptrJ)).eval σD with hσEdef
  have htop : (emitClauseBody curJ tmpJ cntJ ptrJ rowJ).eval σ = σE := by
    unfold emitClauseBody
    rw [eval_seq, eval_seq, eval_seq, hEq, ← hσDdef, ← hσEdef]
  intro r hrC hrT hrCnt hrP hrRow hr
  rw [htop]
  have e1 : σE r = σD r := by
    rw [hσEdef, ctlAssign_eval_diff rowJ _ σD r (by omega)]
  rcases hr with hlt | hge
  · have e2 : σD r = σC r := hframeD r hrC hrT hrP (Or.inl (by omega))
    rw [e1, e2, hframeC r hrC hrT hrCnt hrP]
  · have e2 : σD r = σC r := hframeD r hrC hrT hrP (Or.inr (by omega))
    rw [e1, e2, hframeC r hrC hrT hrCnt hrP]

end NPComplete.CookLevin

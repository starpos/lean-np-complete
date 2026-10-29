module

public import NPComplete.CookLevin.ReductionProg.GeneratorProg
public import NPComplete.CookLevin.ReductionProg.GeneratorRowCount

/-!
# Preserving the Generated Row Count

The generated row count must survive stages whose programs write through a wider control region. This
module proves a structural frame for its cell and carries the closed-form count through generator
contracts and the table-writer handoff.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A single control-cell value can be carried across a wider writer extent.
    Unlike a staged word, the cell is represented directly, so only its offset's
    position between the two extents is needed. -/
lemma clauseWriterIO_carry_cell_widen (prog : Program) (M J1 J2 j v : ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause)
    (hj1 : J1 < j) (hj2 : j ≤ J2)
    (h : ClauseWriterIO prog M J1 wpJ Entry Exit cs) :
    ClauseWriterIO prog M J2 wpJ
      (fun τ => Entry τ ∧ τ (M + j) = v)
      (fun τ => Exit τ ∧ τ (M + j) = v) cs := by
  intro τ wp hF h0 hw hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h τ wp hF.1 h0 hw (by omega)
  refine ⟨⟨a1, ?_⟩, a2, a3, a4, ?_⟩
  · rw [a5 (M + j) (by omega) (Or.inr (by omega))]
    exact hF.2
  · intro r hr1 hr2
    exact a5 r hr1 (by
      unfold CtlFree at hr2 ⊢
      omega)

/-- Upgrade a writer contract with a cell-preservation fact that is specific to
    the writer program.  This is used when the cell lies inside the widened
    control extent and therefore cannot be obtained from `CtlFree`. -/
lemma clauseWriterIO_add_cell_of_frame (prog : Program) (M J j v : ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause)
    (hframe : ∀ (τ : Store) (wp : ℕ), Entry τ → τ 0 = M →
      τ (M + wpJ) = wp → M + J < wp →
      (prog.eval τ) (M + j) = τ (M + j))
    (h : ClauseWriterIO prog M J wpJ Entry Exit cs) :
    ClauseWriterIO prog M J wpJ
      (fun τ => Entry τ ∧ τ (M + j) = v)
      (fun τ => Exit τ ∧ τ (M + j) = v) cs := by
  intro τ wp hF h0 hw hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h τ wp hF.1 h0 hw hsep
  refine ⟨⟨a1, (hframe τ wp hF.1 h0 hw hsep).trans hF.2⟩, a2, a3, a4, a5⟩


/-! ## A structural frame for an interior control cell

`CtlFree` cannot frame `M + 25` once a family is run at a wider extent.  The
following relation records the extra fact needed by the writer transport: a
program leaves one fixed cell alone while keeping register zero and the write
pointer in the writer region.  Its constructors cover the control DSL used by
the clause families (`assignInd`, `seq`, `ifNZ`, and `forN`), while the
specialized primitive lemmas below discharge their concrete write addresses.
-/

def CellSafe (M J r wpJ : ℕ) (p : Program) : Prop :=
  ∀ σ : Store, σ 0 = M → M + J < σ (M + wpJ) →
    p.eval σ (M + r) = σ (M + r) ∧
    p.eval σ 0 = M ∧ M + J < p.eval σ (M + wpJ)

lemma cellSafe_seq (M J r wpJ : ℕ) (p q : Program)
    (hp : CellSafe M J r wpJ p) (hq : CellSafe M J r wpJ q) :
    CellSafe M J r wpJ (.seq p q) := by
  intro σ h0 hptr
  obtain ⟨hpr, hp0, hpp⟩ := hp σ h0 hptr
  obtain ⟨hqr, hq0, hqp⟩ := hq (p.eval σ) hp0 hpp
  rw [eval_seq]
  exact ⟨hqr.trans hpr, hq0, hqp⟩

lemma cellSafe_ifNZ (M J r wpJ : ℕ) (e : Expr) (p q : Program)
    (hp : CellSafe M J r wpJ p) (hq : CellSafe M J r wpJ q) :
    CellSafe M J r wpJ (.ifNZ e p q) := by
  intro σ h0 hptr
  rw [eval_ifNZ]
  split
  · exact hp σ h0 hptr
  · exact hq σ h0 hptr

lemma cellSafe_forN (M J r wpJ : ℕ) (e : Expr) (body : Program)
    (hb : CellSafe M J r wpJ body) :
    CellSafe M J r wpJ (.forN e body) := by
  intro σ h0 hptr
  rw [eval_forN]
  generalize he : e.eval σ = k
  clear he
  induction k generalizing σ with
  | zero => rw [loopEval_zero]; exact ⟨rfl, h0, hptr⟩
  | succ k ih =>
      rw [loopEval_succ]
      obtain ⟨hr, hzero, hptr'⟩ := hb σ h0 hptr
      obtain ⟨hr', hzero', hptr''⟩ := ih (σ := body.eval σ) hzero hptr'
      exact ⟨hr'.trans hr, hzero', hptr''⟩

lemma cellSafe_row_count_frame (M J : ℕ) (p : Program)
    (h : CellSafe M J 25 1 p) :
    ∀ (τ : Store) (wp : ℕ), τ 0 = M → τ (M + wpJ) = wp →
      M + J < wp → (p.eval τ) (M + rowCountReg) = τ (M + rowCountReg) := by
  intro τ wp h0 hw hsep
  have hptr : τ (M + 1) = wp := by simpa [wpJ] using hw
  exact (h τ h0 (by rw [hptr]; exact hsep)).1

lemma cellSafe_skip (M J r wpJ : ℕ) : CellSafe M J r wpJ .skip := by
  intro σ h0 hptr
  rw [eval_skip]
  exact ⟨rfl, h0, hptr⟩

lemma cellSafe_assignInd_above (M J r wpJ : ℕ) (eA eV : Expr)
    (hrJ : r ≤ J) (hJwp : wpJ ≤ J)
    (habove : ∀ σ : Store, σ 0 = M → M + J < σ (M + wpJ) →
      M + J < eA.eval σ) :
    CellSafe M J r wpJ (.assignInd eA eV) := by
  intro σ h0 hptr
  rw [eval_assignInd]
  have haddr := habove σ h0 hptr
  have hrow : M + r ≠ eA.eval σ := by omega
  have hzero : 0 ≠ eA.eval σ := by omega
  have hwp : M + wpJ ≠ eA.eval σ := by omega
  refine ⟨writeReg_diff σ (eA.eval σ) _ (M + r) hrow, ?_, ?_⟩
  · rw [writeReg_diff σ (eA.eval σ) _ 0 hzero]
    exact h0
  · rw [writeReg_diff σ (eA.eval σ) _ (M + wpJ) hwp]
    exact hptr

lemma cellSafe_ctlAssign_nonptr (M J r wpJ j : ℕ) (e : Expr)
    (hjpos : 1 ≤ j) (hjr : j ≠ r) (hjp : j ≠ wpJ) :
    CellSafe M J r wpJ (ctlAssign j e) := by
  intro σ h0 hptr
  unfold ctlAssign
  rw [eval_assignInd, ctlAddr_eval]
  have hrow : M + r ≠ σ 0 + j := by rw [h0]; omega
  have hzero : 0 ≠ σ 0 + j := by rw [h0]; omega
  have hwp : M + wpJ ≠ σ 0 + j := by rw [h0]; omega
  refine ⟨writeReg_diff σ (σ 0 + j) (e.eval σ) (M + r) hrow, ?_, ?_⟩
  · rw [writeReg_diff σ (σ 0 + j) (e.eval σ) 0 hzero]
    exact h0
  · rw [writeReg_diff σ (σ 0 + j) (e.eval σ) (M + wpJ) hwp]
    exact hptr

lemma cellSafe_ctlAssign_ptr_add (M J r wpJ c : ℕ) (hwpJ : 1 ≤ wpJ)
    (hjr : r ≠ wpJ) :
    CellSafe M J r wpJ (ctlAssign wpJ (.add (ctlCell wpJ) (.const c))) := by
  intro σ h0 hptr
  unfold ctlAssign
  rw [eval_assignInd, ctlAddr_eval]
  have hrow : M + r ≠ σ 0 + wpJ := by
    intro he
    apply hjr
    rw [h0] at he
    omega
  have hzero : 0 ≠ σ 0 + wpJ := by rw [h0]; omega
  have hval : (Expr.add (ctlCell wpJ) (.const c)).eval σ = σ (M + wpJ) + c := by
    simp [Expr.eval, ctlCell_eval, h0]
  rw [hval]
  refine ⟨writeReg_diff σ (σ 0 + wpJ) _ (M + r) hrow, ?_, ?_⟩
  · rw [writeReg_diff σ (σ 0 + wpJ) _ 0 hzero]
    exact h0
  · have hs : M + wpJ = σ 0 + wpJ := by rw [h0]
    calc
      M + J < σ (M + wpJ) + c := by omega
      _ = writeReg σ (σ 0 + wpJ) (σ (M + wpJ) + c) (M + wpJ) := by
        rw [hs, writeReg_same]

lemma cellSafe_writeLitProg (M J r wpJ : ℕ) (tagE varE : Expr)
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J) (hrwp : r ≠ wpJ) :
    CellSafe M J r wpJ (writeLitProg wpJ tagE varE) := by
  intro σ h0 hptr
  unfold writeLitProg
  rw [eval_seq, eval_seq]
  set σ1 := (Program.assignInd (ctlCell wpJ) tagE).eval σ
  set σ2 := (Program.assignInd (Expr.add (ctlCell wpJ) (.const 1)) varE).eval σ1
  have haddr : (ctlCell wpJ).eval σ = σ (M + wpJ) := by rw [ctlCell_eval, h0]
  have hσ1 : σ1 = writeReg σ (σ (M + wpJ)) (tagE.eval σ) := by
    dsimp [σ1]
    rw [eval_assignInd, haddr]
  have hσ10 : σ1 0 = M := by
    rw [hσ1, writeReg_diff σ (σ (M + wpJ)) _ 0 (by omega), h0]
  have hσ1row : σ1 (M + r) = σ (M + r) := by
    rw [hσ1, writeReg_diff σ (σ (M + wpJ)) _ (M + r) (by omega)]
  have hσ1wp : σ1 (M + wpJ) = σ (M + wpJ) := by
    rw [hσ1, writeReg_diff σ (σ (M + wpJ)) _ (M + wpJ) (by omega)]
  have haddr2 : (Expr.add (ctlCell wpJ) (.const 1)).eval σ1 = σ (M + wpJ) + 1 := by
    simp [Expr.eval, ctlCell_eval, hσ10, hσ1wp]
  have hσ2 : σ2 = writeReg σ1 (σ (M + wpJ) + 1) (varE.eval σ1) := by
    dsimp [σ2]
    rw [eval_assignInd, haddr2]
  have hσ20 : σ2 0 = M := by
    rw [hσ2, writeReg_diff σ1 (σ (M + wpJ) + 1) _ 0 (by omega), hσ10]
  have hσ2row : σ2 (M + r) = σ (M + r) := by
    rw [hσ2, writeReg_diff σ1 (σ (M + wpJ) + 1) _ (M + r) (by omega), hσ1row]
  have hσ2wp : σ2 (M + wpJ) = σ (M + wpJ) := by
    rw [hσ2, writeReg_diff σ1 (σ (M + wpJ) + 1) _ (M + wpJ) (by omega), hσ1wp]
  have hval3 : (Expr.add (ctlCell wpJ) (.const 2)).eval σ2 = σ (M + wpJ) + 2 := by
    simp [Expr.eval, ctlCell_eval, hσ20, hσ2wp]
  unfold ctlAssign
  rw [eval_assignInd, ctlAddr_eval, hσ20, hval3]
  have hrow : M + r ≠ M + wpJ := by omega
  have hzero : 0 ≠ M + wpJ := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [writeReg_diff σ2 (M + wpJ) _ (M + r) hrow]
    exact hσ2row
  · rw [writeReg_diff σ2 (M + wpJ) _ 0 hzero]
    exact hσ20
  · rw [writeReg_same]
    omega

lemma cellSafe_writeLitsProg (M J r wpJ : ℕ) (lits : List (Expr × Expr))
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J) (hrwp : r ≠ wpJ) :
    CellSafe M J r wpJ (writeLitsProg wpJ lits) := by
  induction lits with
  | nil => simpa [writeLitsProg] using cellSafe_skip M J r wpJ
  | cons hd tail ih =>
      simpa [writeLitsProg] using cellSafe_seq M J r wpJ
        (writeLitProg wpJ hd.1 hd.2) (writeLitsProg wpJ tail)
        (cellSafe_writeLitProg M J r wpJ hd.1 hd.2 hrJ hwpJ hJwp hrwp) ih

lemma cellSafe_writeClauseProg (M J r wpJ : ℕ) (lits : List (Expr × Expr))
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J) (hrwp : r ≠ wpJ) :
    CellSafe M J r wpJ (writeClauseProg wpJ lits) := by
  have h1 : CellSafe M J r wpJ
      (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const lits.length)) :=
    cellSafe_assignInd_above M J r wpJ _ _ hrJ hJwp (by
      intro σ h0 hptr
      simp [Expr.eval, ctlCell_eval, h0]
      omega)
  have h2 : CellSafe M J r wpJ
      (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))) :=
    cellSafe_ctlAssign_ptr_add M J r wpJ 2 hwpJ hrwp
  have h3 : CellSafe M J r wpJ (writeLitsProg wpJ lits) :=
    cellSafe_writeLitsProg M J r wpJ lits hrJ hwpJ hJwp hrwp
  simpa [writeClauseProg] using
    cellSafe_seq M J r wpJ
      (.seq (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const lits.length))
        (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))))
      (writeLitsProg wpJ lits)
      (cellSafe_seq M J r wpJ
        (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const lits.length))
        (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))) h1 h2) h3

lemma cellSafe_writeAtLeastOneBody (M J r wpJ iJ : ℕ) (varE : Expr)
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J)
    (hiJ : 1 ≤ iJ) (hrwp : r ≠ wpJ) (hri : iJ ≠ r)
    (hwi : iJ ≠ wpJ) :
    CellSafe M J r wpJ (writeAtLeastOneBody wpJ iJ varE) := by
  have h1 := cellSafe_writeLitProg M J r wpJ (.const 0) varE hrJ hwpJ hJwp hrwp
  have h2 := cellSafe_ctlAssign_nonptr M J r wpJ iJ
    (.add (ctlCell iJ) (.const 1)) hiJ hri hwi
  simpa [writeAtLeastOneBody] using
    cellSafe_seq M J r wpJ (writeLitProg wpJ (.const 0) varE)
      (ctlAssign iJ (.add (ctlCell iJ) (.const 1))) h1 h2

lemma cellSafe_writeAtLeastOneProg (M J r wpJ iJ : ℕ) (cntE varE : Expr)
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J)
    (hiJ : 1 ≤ iJ) (hrwp : r ≠ wpJ) (hri : iJ ≠ r)
    (hwi : iJ ≠ wpJ) :
    CellSafe M J r wpJ (writeAtLeastOneProg wpJ iJ cntE varE) := by
  have h1 : CellSafe M J r wpJ
      (.assignInd (.add (ctlCell wpJ) (.const 1)) cntE) :=
    cellSafe_assignInd_above M J r wpJ _ _ hrJ hJwp (by
      intro σ h0 hptr
      simp [Expr.eval, ctlCell_eval, h0]
      omega)
  have h2 : CellSafe M J r wpJ
      (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))) :=
    cellSafe_ctlAssign_ptr_add M J r wpJ 2 hwpJ hrwp
  have h3 : CellSafe M J r wpJ (ctlAssign iJ (.const 0)) :=
    cellSafe_ctlAssign_nonptr M J r wpJ iJ (.const 0) hiJ hri hwi
  have hb := cellSafe_writeAtLeastOneBody M J r wpJ iJ varE hrJ hwpJ hJwp
    hiJ hrwp hri hwi
  have h4 := cellSafe_forN M J r wpJ cntE
    (writeAtLeastOneBody wpJ iJ varE) hb
  simpa [writeAtLeastOneProg] using
    cellSafe_seq M J r wpJ
      (.assignInd (.add (ctlCell wpJ) (.const 1)) cntE)
      (.seq (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))
        (.seq (ctlAssign iJ (.const 0))
          (.forN cntE (writeAtLeastOneBody wpJ iJ varE)))) h1
      (cellSafe_seq M J r wpJ
        (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))
        (.seq (ctlAssign iJ (.const 0))
          (.forN cntE (writeAtLeastOneBody wpJ iJ varE))) h2
        (cellSafe_seq M J r wpJ (ctlAssign iJ (.const 0))
          (.forN cntE (writeAtLeastOneBody wpJ iJ varE)) h3 h4))

lemma cellSafe_leaf (M J r wpJ iJ : ℕ) (lits : List (Expr × Expr))
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J)
    (hiJ : 1 ≤ iJ) (hrwp : r ≠ wpJ) (hri : iJ ≠ r)
    (hwi : iJ ≠ wpJ) : CellSafe M J r wpJ (leafProg wpJ iJ lits) := by
  have h1 := cellSafe_writeClauseProg M J r wpJ lits hrJ hwpJ hJwp hrwp
  have h2 := cellSafe_ctlAssign_nonptr M J r wpJ iJ
    (.add (ctlCell iJ) (.const 1)) hiJ hri hwi
  simpa [leafProg] using cellSafe_seq M J r wpJ
    (writeClauseProg wpJ lits) (ctlAssign iJ (.add (ctlCell iJ) (.const 1))) h1 h2

lemma cellSafe_loopProg (M J r wpJ iJ : ℕ) (cntE : Expr) (body : Program)
    (hiJ : 1 ≤ iJ) (hri : iJ ≠ r)
    (hwi : iJ ≠ wpJ) (hb : CellSafe M J r wpJ body) :
    CellSafe M J r wpJ (loopProg iJ cntE body) := by
  have hreset := cellSafe_ctlAssign_nonptr M J r wpJ iJ (.const 0) hiJ hri hwi
  have hfor := cellSafe_forN M J r wpJ cntE body hb
  simpa [loopProg] using cellSafe_seq M J r wpJ
    (ctlAssign iJ (.const 0)) (.forN cntE body) hreset hfor


/-! ## Initial-stage frame

The initial family reads the staged prefix but writes only its clause rows and the
control cells below offset `25`.  The following specializations assemble the
structural frame from the primitive lemmas above; no literal expression values
are needed for this part of the argument.
-/

lemma cellSafe_loop_block
    (M J r wpJ iJ innerJ : ℕ) (cntE innerCntE varE : Expr)
    (lits : List (Expr × Expr))
    (hrJ : r ≤ J) (hwpJ : 1 ≤ wpJ) (hJwp : wpJ ≤ J)
    (hiJ : 1 ≤ iJ) (hrwp : r ≠ wpJ) (hri : iJ ≠ r) (hwi : iJ ≠ wpJ)
    (hinnerJ : 1 ≤ innerJ) (hinnerr : innerJ ≠ r) (hinnerwp : innerJ ≠ wpJ) :
    CellSafe M J r wpJ
      (.seq (writeAtLeastOneProg wpJ iJ cntE varE)
        (loopProg iJ cntE
          (.seq (loopProg innerJ innerCntE (leafProg wpJ innerJ lits))
            (ctlAssign iJ (.add (ctlCell iJ) (.const 1)))))) := by
  have hwrite := cellSafe_writeAtLeastOneProg M J r wpJ iJ cntE varE
    hrJ hwpJ hJwp hiJ hrwp hri hwi
  have hleaf := cellSafe_leaf M J r wpJ innerJ lits
    hrJ hwpJ hJwp hinnerJ hrwp hinnerr hinnerwp
  have hinner := cellSafe_loopProg M J r wpJ innerJ innerCntE
    (leafProg wpJ innerJ lits)
    hinnerJ hinnerr hinnerwp hleaf
  have hbump := cellSafe_ctlAssign_nonptr M J r wpJ iJ
    (.add (ctlCell iJ) (.const 1)) hiJ hri hwi
  have hbody := cellSafe_seq M J r wpJ
    (loopProg innerJ innerCntE (leafProg wpJ innerJ lits))
    (ctlAssign iJ (.add (ctlCell iJ) (.const 1))) hinner hbump
  have houter := cellSafe_loopProg M J r wpJ iJ cntE _
    hiJ hri hwi hbody
  exact cellSafe_seq M J r wpJ
    (writeAtLeastOneProg wpJ iJ cntE varE)
    (loopProg iJ cntE _) hwrite houter

lemma cellSafe_initStateProgParam (M J n m wReg : ℕ) (d : TableauDescriptor)
    (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (initStateProgParam n m wReg d) := by
  unfold initStateProgParam
  split
  · exact cellSafe_writeClauseProg M J 25 1 _ (by omega) (by norm_num [wpJ])
      (by omega) (by norm_num [wpJ, rowCountReg])
  · exact cellSafe_writeClauseProg M J 25 1 _ (by omega) (by norm_num [wpJ])
      (by omega) (by norm_num [wpJ, rowCountReg])

lemma cellSafe_initHeadProgParam (M J n m wReg tReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (initHeadProgParam n m wReg tReg) := by
  exact cellSafe_writeClauseProg M J 25 1 _ (by omega) (by norm_num [wpJ])
    (by omega) (by norm_num [wpJ, rowCountReg])

lemma cellSafe_initWindowLeafProgParam
    (M J n m blank wReg tReg fReg plReg pbReg : ℕ)
    (allowedIdx : List ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx) := by
  have hprefixWrite := cellSafe_writeClauseProg M J 25 1
    (unitPosLits (initPrefixCellStagedEParam n m wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have hprefixCtl := cellSafe_ctlAssign_nonptr M J 25 1 tmpJ
    (initPrefixSymbolEParam tReg plReg pbReg blank) (by norm_num [tmpJ])
    (by norm_num [tmpJ, rowCountReg]) (by norm_num [tmpJ, wpJ])
  have hprefix := cellSafe_seq M J 25 1
    (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
    (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg)))
    hprefixCtl hprefixWrite
  have hfree := cellSafe_writeAtLeastOneProg M J 25 1 litJ
    (.const (allowedIdx.length + 1))
    (initFreeCellVarEParam n m wReg blank allowedIdx)
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [litJ])
    (by norm_num [wpJ, rowCountReg]) (by norm_num [litJ, rowCountReg])
    (by norm_num [litJ, wpJ])
  have hblank := cellSafe_writeClauseProg M J 25 1
    (unitPosLits (initBlankCellEParam n m wReg blank))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  simpa [initWindowLeafProgParam] using
    cellSafe_ifNZ M J 25 1 (initInPrefixEParam tReg plReg)
      (.seq (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
        (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg))))
      (.ifNZ (initInFreeEParam tReg plReg fReg)
        (writeAtLeastOneProg wpJ litJ (.const (allowedIdx.length + 1))
          (initFreeCellVarEParam n m wReg blank allowedIdx))
        (writeClauseProg wpJ (unitPosLits (initBlankCellEParam n m wReg blank))))
      hprefix (cellSafe_ifNZ M J 25 1 (initInFreeEParam tReg plReg fReg)
        (writeAtLeastOneProg wpJ litJ (.const (allowedIdx.length + 1))
          (initFreeCellVarEParam n m wReg blank allowedIdx))
        (writeClauseProg wpJ (unitPosLits (initBlankCellEParam n m wReg blank)))
        hfree hblank)

lemma cellSafe_initWindowProgParam
    (M J n m blank wReg tReg fReg plReg pbReg : ℕ)
    (allowedIdx : List ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (initWindowProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx) := by
  have hleaf := cellSafe_initWindowLeafProgParam M J n m blank wReg tReg fReg plReg pbReg
    allowedIdx hJ
  have hbump := cellSafe_ctlAssign_nonptr M J 25 1 lvJ0
    (.add (ctlCell lvJ0) (.const 1)) (by norm_num [lvJ0])
    (by norm_num [lvJ0, rowCountReg]) (by norm_num [lvJ0, wpJ])
  have hbody := cellSafe_seq M J 25 1
    (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
    (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))) hleaf hbump
  exact cellSafe_loopProg M J 25 1 lvJ0 (ctlCell wReg) _
    (by norm_num [lvJ0]) (by norm_num [lvJ0, rowCountReg])
    (by norm_num [lvJ0, wpJ]) hbody

lemma cellSafe_initTailProgParam
    (M J n m blank wReg tReg fReg plReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (initTailProgParam n m blank wReg tReg fReg plReg) := by
  have hwrite := cellSafe_writeClauseProg M J 25 1
    (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
      (initTailCellNextEParam n m wReg tReg plReg blank))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have hbump := cellSafe_ctlAssign_nonptr M J 25 1 lvJ0
    (.add (ctlCell lvJ0) (.const 1)) (by norm_num [lvJ0])
    (by norm_num [lvJ0, rowCountReg]) (by norm_num [lvJ0, wpJ])
  have hbody := cellSafe_seq M J 25 1
    (writeClauseProg wpJ (implyPosLits
      (initTailCellEParam n m wReg tReg plReg blank)
      (initTailCellNextEParam n m wReg tReg plReg blank)))
    (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))) hwrite hbump
  exact cellSafe_loopProg M J 25 1 lvJ0 (ctlCell fReg) _
    (by norm_num [lvJ0]) (by norm_num [lvJ0, rowCountReg])
    (by norm_num [lvJ0, wpJ]) hbody

lemma cellSafe_initFamilyProgParam
    (M J n m : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (wReg tReg fReg plReg pbReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg) := by
  have hstate := cellSafe_initStateProgParam M J n m wReg d hJ
  have hhead := cellSafe_initHeadProgParam M J n m wReg tReg hJ
  have hwindow := cellSafe_initWindowProgParam M J n m d.blankIdx wReg tReg fReg plReg pbReg
    allowedIdx hJ
  have htail := cellSafe_initTailProgParam M J n m d.blankIdx wReg tReg fReg plReg hJ
  have hwt := cellSafe_seq M J 25 1
    (initWindowProgParam n m d.blankIdx wReg tReg fReg plReg pbReg allowedIdx)
    (initTailProgParam n m d.blankIdx wReg tReg fReg plReg) hwindow htail
  have hht := cellSafe_seq M J 25 1
    (initHeadProgParam n m wReg tReg)
    (.seq (initWindowProgParam n m d.blankIdx wReg tReg fReg plReg pbReg allowedIdx)
      (initTailProgParam n m d.blankIdx wReg tReg fReg plReg)) hhead hwt
  have hall := cellSafe_seq M J 25 1
    (initStateProgParam n m wReg d)
    (.seq (initHeadProgParam n m wReg tReg)
      (.seq (initWindowProgParam n m d.blankIdx wReg tReg fReg plReg pbReg allowedIdx)
        (initTailProgParam n m d.blankIdx wReg tReg fReg plReg))) hstate hht
  simpa [initFamilyProgParam] using hall

lemma cellSafe_loadTransParamsProg (M J : ℕ) (d : TableauDescriptor)
     : CellSafe M J 25 1 (loadTransParamsProg d) := by
  have hkind := cellSafe_ctlAssign_nonptr M J 25 1 transKindBaseReg
    (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2))
    (by norm_num [transKindBaseReg]) (by norm_num [transKindBaseReg, rowCountReg])
    (by norm_num [transKindBaseReg, wpJ])
  have harg1 := cellSafe_ctlAssign_nonptr M J 25 1 transArg1BaseReg
    (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2)))
    (by norm_num [transArg1BaseReg]) (by norm_num [transArg1BaseReg, rowCountReg])
    (by norm_num [transArg1BaseReg, wpJ])
  have harg2 := cellSafe_ctlAssign_nonptr M J 25 1 transArg2BaseReg
    (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2)))
    (by norm_num [transArg2BaseReg]) (by norm_num [transArg2BaseReg, rowCountReg])
    (by norm_num [transArg2BaseReg, wpJ])
  simpa [loadTransParamsProg] using
    cellSafe_seq M J 25 1
      (ctlAssign transKindBaseReg
        (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2)))
      (.seq
        (ctlAssign transArg1BaseReg
          (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2))))
        (ctlAssign transArg2BaseReg
          (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2))))) hkind
      (cellSafe_seq M J 25 1
        (ctlAssign transArg1BaseReg
          (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2))))
        (ctlAssign transArg2BaseReg
          (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2))))
        harg1 harg2)

lemma cellSafe_initStageProgParam
    (M J : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (initStageProgParam d allowedIdx) := by
  have hfamily := cellSafe_initFamilyProgParam M J (d.numStates + 1) (d.numLetters + 1)
    d allowedIdx initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg hJ
  have hload := cellSafe_loadTransParamsProg M J d
  simpa [initStageProgParam] using cellSafe_seq M J 25 1
    (initFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d allowedIdx
      initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg)
    (loadTransParamsProg d) hfamily hload



lemma cellSafe_uniquenessFamilyProgParam
    (M J nS mS nC mC wReg tReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (uniquenessFamilyProgParam nS mS nC mC wReg tReg) := by
  have hsBlock := cellSafe_loop_block M J 25 1 lvJ1 lvJ2
    (.const nC)
    (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
    (uniqStateBaseEParam nS mS wReg)
    (negPairLits (uniqStateBaseEParam nS mS wReg)
      (uniqStateShiftEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [lvJ1])
    (by norm_num [rowCountReg, wpJ]) (by norm_num [lvJ1, rowCountReg])
    (by norm_num [lvJ1, wpJ])
    (by norm_num [lvJ2]) (by norm_num [lvJ2, rowCountReg])
    (by norm_num [lvJ2, wpJ])
  have hhBlock := cellSafe_loop_block M J 25 1 lvJ1 lvJ2
    (ctlCell wReg)
    (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
    (uniqHeadBaseEParam nS mS wReg)
    (negPairLits (uniqHeadBaseEParam nS mS wReg)
      (uniqHeadShiftEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [lvJ1])
    (by norm_num [rowCountReg, wpJ]) (by norm_num [lvJ1, rowCountReg])
    (by norm_num [lvJ1, wpJ])
    (by norm_num [lvJ2]) (by norm_num [lvJ2, rowCountReg])
    (by norm_num [lvJ2, wpJ])
  have hcBlock := cellSafe_loop_block M J 25 1 lvJ2 lvJ3
    (.const mC)
    (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
    (uniqCellBaseEParam nS mS wReg)
    (negPairLits (uniqCellBaseEParam nS mS wReg)
      (uniqCellShiftEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [lvJ2])
    (by norm_num [rowCountReg, wpJ]) (by norm_num [lvJ2, rowCountReg])
    (by norm_num [lvJ2, wpJ])
    (by norm_num [lvJ3]) (by norm_num [lvJ3, rowCountReg])
    (by norm_num [lvJ3, wpJ])
  have hcBump1 := cellSafe_ctlAssign_nonptr M J 25 1 lvJ1
    (.add (ctlCell lvJ1) (.const 1)) (by norm_num [lvJ1])
    (by norm_num [lvJ1, rowCountReg]) (by norm_num [lvJ1, wpJ])
  have hcBody1 := cellSafe_seq M J 25 1 _
    (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))) hcBlock hcBump1
  have hcOuter1 := cellSafe_loopProg M J 25 1 lvJ1 (ctlCell wReg) _
    (by norm_num [lvJ1]) (by norm_num [lvJ1, rowCountReg])
    (by norm_num [lvJ1, wpJ]) hcBody1
  have hfirst := cellSafe_seq M J 25 1
    (.seq (writeAtLeastOneProg wpJ lvJ1 (.const nC)
      (uniqStateBaseEParam nS mS wReg)) (loopProg lvJ1 (.const nC) _))
    (.seq (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg)
      (uniqHeadBaseEParam nS mS wReg)) (loopProg lvJ1 (ctlCell wReg) _))
    hsBlock hhBlock
  have hsecond := cellSafe_seq M J 25 1 _
    (loopProg lvJ1 (ctlCell wReg) _) hfirst hcOuter1
  have houterBump := cellSafe_ctlAssign_nonptr M J 25 1 lvJ0
    (.add (ctlCell lvJ0) (.const 1)) (by norm_num [lvJ0])
    (by norm_num [lvJ0, rowCountReg]) (by norm_num [lvJ0, wpJ])
  have hbody := cellSafe_seq M J 25 1 _
    (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))) hsecond houterBump
  exact cellSafe_loopProg M J 25 1 lvJ0
    (.add (ctlCell tReg) (.const 1)) _
    (by norm_num [lvJ0]) (by norm_num [lvJ0, rowCountReg])
    (by norm_num [lvJ0, wpJ]) hbody


lemma cellSafe_transStageArgsProgParam
    (M J a1Reg a2Reg len1 len2 mC : ℕ)  :
    CellSafe M J 25 1 (transStageArgsProgParam a1Reg a2Reg len1 len2 mC) := by
  have h1 := cellSafe_ctlAssign_nonptr M J 25 1 litJ
    (transArg1EParam a1Reg len1 mC) (by norm_num [litJ])
    (by norm_num [litJ, rowCountReg]) (by norm_num [litJ, wpJ])
  have h2 := cellSafe_ctlAssign_nonptr M J 25 1 tmpJ
    (transArg2EParam a2Reg len2 mC) (by norm_num [tmpJ])
    (by norm_num [tmpJ, rowCountReg]) (by norm_num [tmpJ, wpJ])
  simpa [transStageArgsProgParam] using cellSafe_seq M J 25 1
    (ctlAssign litJ (transArg1EParam a1Reg len1 mC))
    (ctlAssign tmpJ (transArg2EParam a2Reg len2 mC)) h1 h2

lemma cellSafe_transForbidBlockProgParam
    (M J nS mS wReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (transForbidBlockProgParam nS mS wReg) := by
  have h1 := cellSafe_writeClauseProg M J 25 1
    (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h2 := h1
  have h3 := h1
  have h12 := cellSafe_seq M J 25 1
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)))
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))) h1 h2
  have hall := cellSafe_seq M J 25 1 _
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))) h12 h3
  simpa [transForbidBlockProgParam, wpJ] using hall

lemma cellSafe_transHaltBlockProgParam
    (M J nS mS wReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (transHaltBlockProgParam nS mS wReg) := by
  have h1 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateSameEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h2 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadSameEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h3 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellSameEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h12 := cellSafe_seq M J 25 1 _ _ h1 h2
  have hall := cellSafe_seq M J 25 1 _ _ h12 h3
  simpa [transHaltBlockProgParam, wpJ] using hall

lemma cellSafe_transWriteBlockProgParam
    (M J nS mS wReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (transWriteBlockProgParam nS mS wReg) := by
  have h1 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateNextEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h2 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadSameEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h3 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellWriteEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h12 := cellSafe_seq M J 25 1 _ _ h1 h2
  have hall := cellSafe_seq M J 25 1 _ _ h12 h3
  simpa [transWriteBlockProgParam, wpJ] using hall

lemma cellSafe_transMoveBlockProgParam
    (M J nS mS wReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (transMoveBlockProgParam nS mS wReg) := by
  have h1 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateNextEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h2 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadMoveEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h3 := cellSafe_writeClauseProg M J 25 1
    (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellSameEParam nS mS wReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  have h12 := cellSafe_seq M J 25 1 _ _ h1 h2
  have hall := cellSafe_seq M J 25 1 _ _ h12 h3
  simpa [transMoveBlockProgParam, wpJ] using hall

lemma cellSafe_transAcceptWriteProgParam
    (M J nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2) := by
  have hargs := cellSafe_transStageArgsProgParam M J a1Reg a2Reg len1 len2 mC
  have hblock := cellSafe_transWriteBlockProgParam M J nS mS wReg hJ
  simpa [transAcceptWriteProgParam] using cellSafe_seq M J 25 1
    (transStageArgsProgParam a1Reg a2Reg len1 len2 mC)
    (transWriteBlockProgParam nS mS wReg) hargs hblock

lemma cellSafe_transAcceptMoveProgParam
    (M J nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2) := by
  have hargs := cellSafe_transStageArgsProgParam M J a1Reg a2Reg len1 len2 mC
  have hblock := cellSafe_transMoveBlockProgParam M J nS mS wReg hJ
  simpa [transAcceptMoveProgParam] using cellSafe_seq M J 25 1
    (transStageArgsProgParam a1Reg a2Reg len1 len2 mC)
    (transMoveBlockProgParam nS mS wReg) hargs hblock

lemma cellSafe_transLeafProgParam
    (M J nS mS nC mC wReg kbReg a1Reg a2Reg lenk len1 len2 : ℕ)
    (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg lenk len1 len2) := by
  have hhalt := cellSafe_transHaltBlockProgParam M J nS mS wReg hJ
  have hwrite := cellSafe_transAcceptWriteProgParam M J nS mS mC wReg a1Reg a2Reg
    len1 len2 hJ
  have hmove := cellSafe_transAcceptMoveProgParam M J nS mS mC wReg a1Reg a2Reg
    len1 len2 hJ
  have hforbid := cellSafe_transForbidBlockProgParam M J nS mS wReg hJ
  have hwriteBranch := cellSafe_ifNZ M J 25 1
    (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
    (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
    (transForbidBlockProgParam nS mS wReg) hwrite hforbid
  have hmoveInner := cellSafe_ifNZ M J 25 1
    (moveOkEParam wReg (ctlCell lvJ1) (transArg2EParam a2Reg len2 mC))
    (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
    (transForbidBlockProgParam nS mS wReg) hmove hforbid
  have hmoveBranch := cellSafe_ifNZ M J 25 1
    (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
    (.ifNZ (moveOkEParam wReg (ctlCell lvJ1) (transArg2EParam a2Reg len2 mC))
      (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
      (transForbidBlockProgParam nS mS wReg))
    (transForbidBlockProgParam nS mS wReg) hmoveInner hforbid
  have hkind1 := cellSafe_ifNZ M J 25 1
    (.eq (transKindEParam kbReg lenk mC) (.const 1))
    (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
      (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
      (transForbidBlockProgParam nS mS wReg))
    (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
      (.ifNZ (moveOkEParam wReg (ctlCell lvJ1) (transArg2EParam a2Reg len2 mC))
        (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
        (transForbidBlockProgParam nS mS wReg))
      (transForbidBlockProgParam nS mS wReg)) hwriteBranch hmoveBranch
  simpa [transLeafProgParam] using cellSafe_ifNZ M J 25 1
    (.eq (transKindEParam kbReg lenk mC) (.const 0))
    (transHaltBlockProgParam nS mS wReg)
    (.ifNZ (.eq (transKindEParam kbReg lenk mC) (.const 1))
      (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
        (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
        (transForbidBlockProgParam nS mS wReg))
      (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
        (.ifNZ (moveOkEParam wReg (ctlCell lvJ1) (transArg2EParam a2Reg len2 mC))
          (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
          (transForbidBlockProgParam nS mS wReg))
        (transForbidBlockProgParam nS mS wReg))) hhalt hkind1

lemma cellSafe_transFamilyProgParam
    (M J nS mS nC mC : ℕ) (d : TableauDescriptor)
    (wReg tReg kbReg a1Reg a2Reg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg) := by
  have hleaf := cellSafe_transLeafProgParam M J nS mS nC mC wReg kbReg a1Reg a2Reg
    (d.table.map transKind).length (d.table.map transArg1).length
    (d.table.map transArg2).length hJ
  have hbump3 := cellSafe_ctlAssign_nonptr M J 25 1 lvJ3
    (.add (ctlCell lvJ3) (.const 1)) (by norm_num [lvJ3])
    (by norm_num [lvJ3, rowCountReg]) (by norm_num [lvJ3, wpJ])
  have hbump2 := cellSafe_ctlAssign_nonptr M J 25 1 lvJ2
    (.add (ctlCell lvJ2) (.const 1)) (by norm_num [lvJ2])
    (by norm_num [lvJ2, rowCountReg]) (by norm_num [lvJ2, wpJ])
  have hbump1 := cellSafe_ctlAssign_nonptr M J 25 1 lvJ1
    (.add (ctlCell lvJ1) (.const 1)) (by norm_num [lvJ1])
    (by norm_num [lvJ1, rowCountReg]) (by norm_num [lvJ1, wpJ])
  have hbump0 := cellSafe_ctlAssign_nonptr M J 25 1 lvJ0
    (.add (ctlCell lvJ0) (.const 1)) (by norm_num [lvJ0])
    (by norm_num [lvJ0, rowCountReg]) (by norm_num [lvJ0, wpJ])
  have hbody3 := cellSafe_seq M J 25 1
    (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
      (d.table.map transKind).length (d.table.map transArg1).length
      (d.table.map transArg2).length)
    (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1))) hleaf hbump3
  have hloop3 := cellSafe_loopProg M J 25 1 lvJ3 (.const mC) _
    (by norm_num [lvJ3]) (by norm_num [lvJ3, rowCountReg])
    (by norm_num [lvJ3, wpJ]) hbody3
  have hbody2 := cellSafe_seq M J 25 1
    (loopProg lvJ3 (.const mC) _)
    (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))) hloop3 hbump2
  have hloop2 := cellSafe_loopProg M J 25 1 lvJ2 (.const nC) _
    (by norm_num [lvJ2]) (by norm_num [lvJ2, rowCountReg])
    (by norm_num [lvJ2, wpJ]) hbody2
  have hbody1 := cellSafe_seq M J 25 1
    (loopProg lvJ2 (.const nC) _)
    (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))) hloop2 hbump1
  have hloop1 := cellSafe_loopProg M J 25 1 lvJ1 (ctlCell wReg) _
    (by norm_num [lvJ1]) (by norm_num [lvJ1, rowCountReg])
    (by norm_num [lvJ1, wpJ]) hbody1
  have hbody0 := cellSafe_seq M J 25 1
    (loopProg lvJ1 (ctlCell wReg) _)
    (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))) hloop1 hbump0
  have hloop0 := cellSafe_loopProg M J 25 1 lvJ0 (ctlCell tReg) _
    (by norm_num [lvJ0]) (by norm_num [lvJ0, rowCountReg])
    (by norm_num [lvJ0, wpJ]) hbody0
  simpa [transFamilyProgParam] using hloop0

lemma cellSafe_loadAcceptParamProg (M J : ℕ) (d : TableauDescriptor)
     : CellSafe M J 25 1 (loadAcceptParamProg d) := by
  exact cellSafe_ctlAssign_nonptr M J 25 1 acceptOutBaseReg
    (.add (ctlCell transArg2BaseReg) (.const (d.table.length + 2)))
    (by norm_num [acceptOutBaseReg]) (by norm_num [acceptOutBaseReg, rowCountReg])
    (by norm_num [acceptOutBaseReg, wpJ])

lemma cellSafe_transStageProgParam (M J : ℕ) (d : TableauDescriptor)
    (hJ : 25 ≤ J) : CellSafe M J 25 1 (transStageProgParam d) := by
  have hfamily := cellSafe_transFamilyProgParam M J (d.numStates + 1)
    (d.numLetters + 1) d.numStates d.numLetters d transWReg transTReg transKindBaseReg
    transArg1BaseReg transArg2BaseReg hJ
  have hload := cellSafe_loadAcceptParamProg M J d
  simpa [transStageProgParam] using cellSafe_seq M J 25 1
    (transFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
      d.numStates d.numLetters d transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg)
    (loadAcceptParamProg d) hfamily hload

lemma cellSafe_acceptLeafProgParam
    (M J n m blank outLen wReg tReg obReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (acceptLeafProgParam n m blank outLen wReg tReg obReg) := by
  have hctl := cellSafe_ctlAssign_nonptr M J 25 1 tmpJ
    (acceptOutputSymbolEParam obReg blank outLen) (by norm_num [tmpJ])
    (by norm_num [tmpJ, rowCountReg]) (by norm_num [tmpJ, wpJ])
  have hwrite := cellSafe_writeClauseProg M J 25 1
    (implyPosLits (acceptHeadEParam n m wReg tReg)
      (acceptCellStagedEParam n m wReg tReg))
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [wpJ, rowCountReg])
  simpa [acceptLeafProgParam] using cellSafe_seq M J 25 1
    (ctlAssign tmpJ (acceptOutputSymbolEParam obReg blank outLen))
    (writeClauseProg wpJ (implyPosLits
      (acceptHeadEParam n m wReg tReg)
      (acceptCellStagedEParam n m wReg tReg))) hctl hwrite

lemma cellSafe_acceptInnerProgParam
    (M J n m blank outLen wReg tReg obReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (acceptInnerProgParam n m blank outLen wReg tReg obReg) := by
  have hleaf := cellSafe_acceptLeafProgParam M J n m blank outLen wReg tReg obReg hJ
  have hbump := cellSafe_ctlAssign_nonptr M J 25 1 lvJ1
    (.add (ctlCell lvJ1) (.const 1)) (by norm_num [lvJ1])
    (by norm_num [lvJ1, rowCountReg]) (by norm_num [lvJ1, wpJ])
  have hbody := cellSafe_seq M J 25 1
    (acceptLeafProgParam n m blank outLen wReg tReg obReg)
    (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))) hleaf hbump
  exact cellSafe_loopProg M J 25 1 lvJ1 (ctlCell wReg) _
    (by norm_num [lvJ1]) (by norm_num [lvJ1, rowCountReg])
    (by norm_num [lvJ1, wpJ]) hbody

lemma cellSafe_acceptOuterProgParam
    (M J n m blank outLen wReg tReg obReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (acceptOuterProgParam n m blank outLen wReg tReg obReg) := by
  have hinner := cellSafe_acceptInnerProgParam M J n m blank outLen wReg tReg obReg hJ
  have hbump := cellSafe_ctlAssign_nonptr M J 25 1 lvJ0
    (.add (ctlCell lvJ0) (.const 1)) (by norm_num [lvJ0])
    (by norm_num [lvJ0, rowCountReg]) (by norm_num [lvJ0, wpJ])
  have hbody := cellSafe_seq M J 25 1
    (acceptInnerProgParam n m blank outLen wReg tReg obReg)
    (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))) hinner hbump
  exact cellSafe_loopProg M J 25 1 lvJ0 (ctlCell wReg) _
    (by norm_num [lvJ0]) (by norm_num [lvJ0, rowCountReg])
    (by norm_num [lvJ0, wpJ]) hbody

lemma cellSafe_acceptHaltProgParam
    (M J n m wReg tReg : ℕ) (qs : List ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (acceptHaltProgParam n m wReg tReg qs) := by
  exact cellSafe_writeAtLeastOneProg M J 25 1 litJ
    (.const qs.length) (acceptHaltVarEParam n m wReg tReg qs)
    (by omega) (by norm_num [wpJ]) (by omega) (by norm_num [litJ])
    (by norm_num [rowCountReg, wpJ]) (by norm_num [litJ, rowCountReg])
    (by norm_num [litJ, wpJ])

lemma cellSafe_acceptFamilyProgParam
    (M J n m : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (wReg tReg obReg : ℕ) (hJ : 25 ≤ J) :
    CellSafe M J 25 1
      (acceptFamilyProgParam n m d outIdx wReg tReg obReg) := by
  have houter := cellSafe_acceptOuterProgParam M J n m d.blankIdx outIdx.length
    wReg tReg obReg hJ
  set qs := descHaltStates d (natInitSymbol d.blankIdx outIdx 0)
  have hhalt := cellSafe_acceptHaltProgParam M J n m wReg tReg qs hJ
  simpa [acceptFamilyProgParam, qs] using cellSafe_seq M J 25 1
    (acceptOuterProgParam n m d.blankIdx outIdx.length wReg tReg obReg)
    (acceptHaltProgParam n m wReg tReg qs) houter hhalt

lemma cellSafe_loadEmitterTableProg
    (M J : ℕ) (outIdx : List ℕ)  :
    CellSafe M J 25 1 (loadEmitterTableProg outIdx) := by
  exact cellSafe_ctlAssign_nonptr M J 25 1 emTblJ
    (.add (ctlCell acceptOutBaseReg) (.const (outIdx.length + 1)))
    (by norm_num [emTblJ]) (by norm_num [emTblJ, rowCountReg])
    (by norm_num [emTblJ, wpJ])

lemma cellSafe_acceptStageProgParam
    (M J : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (hJ : 25 ≤ J) :
    CellSafe M J 25 1 (acceptStageProgParam d outIdx) := by
  have hfamily := cellSafe_acceptFamilyProgParam M J (d.numStates + 1)
    (d.numLetters + 1) d outIdx acceptWReg acceptTReg acceptOutBaseReg hJ
  have hload := cellSafe_loadEmitterTableProg M J outIdx
  simpa [acceptStageProgParam] using cellSafe_seq M J 25 1
    (acceptFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d outIdx
      acceptWReg acceptTReg acceptOutBaseReg) (loadEmitterTableProg outIdx) hfamily hload

/-! ## Layout lower bound for the count cell -/

lemma generator_placement_row_count_le
    (M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    rowCountReg ≤ Jmax := by
  have hp := h.pref_base
  have hlen := h.pref_len
  have hk := h.kind_eq
  have h1 := h.arg1_eq
  have h2 := h.arg2_eq
  have ho := h.out_eq
  have hf := h.out_fit
  simp [rowCountReg, initPrefBaseReg] at *
  omega

def GeneratorTableFrozenCount (M W T freeLen prefLen prefBase count : ℕ)
    (prefIdx : List ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (outBase : ℕ) (outIdx : List ℕ) (τ : Store) : Prop :=
  GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase colk
    arg1Base col1 arg2Base col2 outBase outIdx τ ∧
    τ (M + rowCountReg) = count

def TransWithOutFrozenCount (M W T kindBase arg1Base arg2Base count : ℕ)
    (colk col1 col2 : List ℕ) (outBase : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  TransWithOutFrozen M W T kindBase arg1Base arg2Base colk col1 col2 outBase outIdx τ ∧
    τ (M + rowCountReg) = count

lemma uniqueness_stage_io_param_with_count
    (M Jmax W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (uniquenessStageProgParam d) M Jmax wpJ
      (GeneratorTableFrozenCount M W T freeLen prefLen prefBase count prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (GeneratorTableFrozenCount M W T freeLen prefLen prefBase count prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (execUniquenessClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numStates) (List.range d.numLetters) W T) := by
  have hJ := generator_placement_row_count_le M Jmax prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hsafe := cellSafe_uniquenessFamilyProgParam M Jmax
    (d.numStates + 1) (d.numLetters + 1) d.numStates d.numLetters
    uniquenessWReg uniquenessTReg hJ
  have hframe := cellSafe_row_count_frame M Jmax (uniquenessStageProgParam d)
    hsafe
  have hbase := uniqueness_stage_io_param M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  unfold GeneratorTableFrozenCount
  exact clauseWriterIO_add_cell_of_frame _ M Jmax rowCountReg count _ _ _
    (fun τ wp _ => hframe τ wp) hbase

/-! ## Count-carrying initial-stage contract -/

lemma init_stage_io_param_with_count
    (M Jmax W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (initStageProgParam d allowedIdx) M Jmax wpJ
      (GeneratorTableFrozenCount M W T freeLen prefLen prefBase count prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (TransWithOutFrozenCount M W T kindBase arg1Base arg2Base count
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (descBoundedPrefixInitClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx W T) := by
  have hJ : 25 ≤ Jmax := by
    have hp := h.pref_base
    have hlen := h.pref_len
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    have ho := h.out_eq
    have hf := h.out_fit
    simp [initPrefBaseReg] at *
    omega
  have hsafe := cellSafe_initStageProgParam M Jmax d allowedIdx hJ
  have hframe := cellSafe_row_count_frame M Jmax (initStageProgParam d allowedIdx)
    hsafe
  have hbase := init_stage_io_param M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx allowedIdx outIdx h
  exact clauseWriterIO_add_cell_of_frame _ M Jmax rowCountReg count _ _ _
    (fun τ wp _ => hframe τ wp) hbase


def AcceptParamFrozenCount
    (M wReg tReg obReg W T outBase count : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  AcceptParamFrozen M wReg tReg obReg W T outBase outIdx τ ∧
    τ (M + rowCountReg) = count

def EmitterTableReadyCount
    (M W T outBase tableBase count : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  EmitterTableReady M W T outBase tableBase outIdx τ ∧
    τ (M + rowCountReg) = count

lemma trans_stage_io_param_with_count
    (M Jmax W T prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (transStageProgParam d) M Jmax wpJ
      (TransWithOutFrozenCount M W T kindBase arg1Base arg2Base count
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (AcceptParamFrozenCount M acceptWReg acceptTReg acceptOutBaseReg W T outBase count
        outIdx)
      (transClausesTripleFamily
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        d.numStates W d.numLetters T (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2)) := by
  have hJ := generator_placement_row_count_le M Jmax prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hsafe := cellSafe_transStageProgParam M Jmax d hJ
  have hframe := cellSafe_row_count_frame M Jmax (transStageProgParam d)
    hsafe
  have hbase := trans_stage_io_param M Jmax W T prefLen prefBase kindBase arg1Base
    arg2Base outBase d prefIdx outIdx h
  unfold TransWithOutFrozenCount AcceptParamFrozenCount
  exact clauseWriterIO_add_cell_of_frame _ M Jmax rowCountReg count _ _ _
    (fun τ wp _ => hframe τ wp) hbase

lemma persist_stage_io_param_with_count
    (M Jmax W T prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (persistStageProgParam d) M Jmax wpJ
      (AcceptParamFrozenCount M acceptWReg acceptTReg acceptOutBaseReg W T outBase count
        outIdx)
      (AcceptParamFrozenCount M acceptWReg acceptTReg acceptOutBaseReg W T outBase count
        outIdx)
      (execPersistClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numLetters) W T) := by
  let pins := [(persistWReg, W), (persistTReg, T)]
  let extra := [(acceptOutBaseReg, outBase)]
  have h0 : ClauseWriterIO (persistStageProgParam d) M persistParamJmax wpJ
      (PinsHold M pins) (PinsHold M pins)
      (execPersistClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numLetters) W T) := by
    exact clauseWriterIO_of_writer _ M persistParamJmax wpJ _ _
      (persistFamilyProgParam_writer_param M persistParamJmax (d.numStates + 1) W
        (d.numLetters + 1) d.numLetters T persistWReg persistTReg
        persist_param_fixed_placement)
  have hp := clauseWriterIO_pins_widen _ M persistParamJmax acceptOutBaseReg
    pins extra _ (by simp [persistParamJmax, acceptOutBaseReg])
    (by
      intro q hq
      simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl
      simp [persistParamJmax, acceptOutBaseReg])
    (by
      intro q hq
      simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl
      rfl) h0
  have hp' : ClauseWriterIO (persistStageProgParam d) M acceptOutBaseReg wpJ
      (PinsHold M (acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg W T outBase))
      (PinsHold M (acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg W T outBase))
      (execPersistClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numLetters) W T) := by
    simpa [pins, extra, acceptParamPins0, persistWReg, persistTReg,
      acceptWReg, acceptTReg] using hp
  have houtAbove : M + acceptOutBaseReg + 1 < outBase := by
    have hb := h.pref_base
    have hp' := h.pref_pos
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    have ho := h.out_eq
    simp [acceptOutBaseReg, initPrefBaseReg] at hb ⊢
    omega
  have hcount := clauseWriterIO_carry_cell_widen _ M acceptOutBaseReg rowCountReg
      rowCountReg count _ _ _ (by norm_num [acceptOutBaseReg, rowCountReg])
      (by norm_num [rowCountReg]) hp'
  have houtAbove25 : M + rowCountReg + 1 < outBase := by
    have hb := h.pref_base
    have hp' := h.pref_pos
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    have ho := h.out_eq
    simp [initPrefBaseReg, rowCountReg] at hb ⊢
    omega
  have hword := clauseWriterIO_carry_widen _ M rowCountReg Jmax _ _ outBase outIdx _
    houtAbove25 h.out_fit hcount
  let pins' := acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg W T outBase
  let EntryS : Store → Prop := fun τ => (PinsHold M pins' τ ∧
    τ (M + rowCountReg) = count) ∧ WordAt τ outBase outIdx
  let EntryD : Store → Prop := fun τ => (PinsHold M pins' τ ∧
    WordAt τ outBase outIdx) ∧ τ (M + rowCountReg) = count
  have hswap : ∀ τ, EntryD τ → EntryS τ := by
    intro τ hτ
    exact ⟨⟨hτ.1.1, hτ.2⟩, hτ.1.2⟩
  have hword' : ClauseWriterIO (persistStageProgParam d) M Jmax wpJ
      EntryD EntryS
      (execPersistClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numLetters) W T) := by
    apply clauseWriterIO_strengthen_entry _ M Jmax wpJ EntryS EntryD EntryS _ hswap
    simpa [EntryS, pins', AcceptParamFrozen, acceptParamPins0] using hword
  have hword'' := clauseWriterIO_weaken_exit _ M Jmax wpJ EntryD EntryS EntryD _
    (by
      intro τ hτ
      exact ⟨⟨hτ.1.1, hτ.2⟩, hτ.1.2⟩) hword'
  unfold AcceptParamFrozenCount AcceptParamFrozen PinsAndWord
  exact hword''

lemma accept_stage_io_param_with_count
    (M Jmax W T prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (acceptStageProgParam d outIdx) M Jmax wpJ
      (AcceptParamFrozenCount M acceptWReg acceptTReg acceptOutBaseReg W T outBase count
        outIdx)
      (EmitterTableReadyCount M W T outBase (outBase + outIdx.length + 1) count outIdx)
      (descAcceptClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d outIdx W T) := by
  have hJ := generator_placement_row_count_le M Jmax prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hsafe := cellSafe_acceptStageProgParam M Jmax d outIdx hJ
  have hframe := cellSafe_row_count_frame M Jmax (acceptStageProgParam d outIdx)
    hsafe
  have hbase := accept_stage_io_param M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  unfold AcceptParamFrozenCount EmitterTableReadyCount
  exact clauseWriterIO_add_cell_of_frame _ M Jmax rowCountReg count _ _ _
    (fun τ wp _ => hframe τ wp) hbase

lemma tableWriterProgParam_io_param_with_count
    (M Jmax W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase count : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (tableWriterProgParam d allowedIdx outIdx) M Jmax wpJ
      (GeneratorTableFrozenCount M W T freeLen prefLen prefBase count prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (EmitterTableReadyCount M W T outBase (outBase + outIdx.length + 1) count outIdx)
      (descTableauCNF
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx outIdx W T).clauses := by
  have hU := uniqueness_stage_io_param_with_count M Jmax W T freeLen prefLen prefBase
    kindBase arg1Base arg2Base outBase count d prefIdx outIdx h
  have hI := init_stage_io_param_with_count M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase count d prefIdx allowedIdx outIdx h
  have hT := trans_stage_io_param_with_count M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase count d prefIdx outIdx h
  have hP := persist_stage_io_param_with_count M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase count d prefIdx outIdx h
  have hA := accept_stage_io_param_with_count M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase count d prefIdx outIdx h
  have hUI := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hU hI
  have hUIT := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUI hT
  have hUITP := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUIT hP
  have hall := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUITP hA
  have hgen : ClauseWriterIO (tableWriterProgParam d allowedIdx outIdx)
      M Jmax wpJ
      (GeneratorTableFrozenCount M W T freeLen prefLen prefBase count prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (EmitterTableReadyCount M W T outBase (outBase + outIdx.length + 1) count outIdx)
      (tableWriterClausesGen (d.numStates + 1) W (d.numLetters + 1)
        d.numStates d.numLetters T d prefIdx freeLen allowedIdx outIdx) := by
    simpa [tableWriterProgParam, tableWriterClausesGen] using hall
  rw [table_writer_clauses_gen_eq_desc] at hgen
  exact hgen

/-- The clause-count stage leaves the closed-form row count in its count cell. -/
lemma generator_count_stage_handoff_count_cell (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ) (ρ : Store)
    (hρ0 : ρ 0 = setupM p time d allowedIdx N)
    (hF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ) :
    (clauseCountProg d.numStates d.numLetters).eval ρ
        (setupM p time d allowedIdx N + rowCountReg) =
      clauseCount d.numStates d.numLetters ((timePoly p time).eval N)
        ((cookWindowPoly p time).eval N) (p.eval N) := by
  have hT : ρ (setupM p time d allowedIdx N + persistTReg) =
      (timePoly p time).eval N :=
    hF.1.1.1.1.1 (persistTReg, (timePoly p time).eval N)
      (by simp [initParamPins0, initWReg, initTReg, initFreeLenReg,
        initPrefLenReg, initPrefBaseReg, persistTReg])
  have hW : ρ (setupM p time d allowedIdx N + persistWReg) =
      (cookWindowPoly p time).eval N :=
    hF.1.1.1.1.1 (persistWReg, (cookWindowPoly p time).eval N)
      (by simp [initParamPins0, initWReg, initTReg, initFreeLenReg,
        initPrefLenReg, initPrefBaseReg, persistWReg])
  have hfree : ρ (setupM p time d allowedIdx N + initFreeLenReg) = p.eval N :=
    hF.1.1.1.1.1 (initFreeLenReg, p.eval N)
      (by simp [initParamPins0, initWReg, initTReg, initFreeLenReg,
        initPrefLenReg, initPrefBaseReg])
  exact clauseCountProg_eval (setupM p time d allowedIdx N)
    d.numStates d.numLetters ((timePoly p time).eval N)
    ((cookWindowPoly p time).eval N) (p.eval N) ρ hρ0 hT hW hfree

/-- The clause-count stage keeps the frozen table parameters and adds the row count. -/
lemma generator_count_stage_handoff_frozen_count (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ) (ρ : Store)
    (hρ0 : ρ 0 = setupM p time d allowedIdx N)
    (hF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ) :
    GeneratorTableFrozenCount (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      (clauseCount d.numStates d.numLetters ((timePoly p time).eval N)
        ((cookWindowPoly p time).eval N) (p.eval N))
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx
      ((clauseCountProg d.numStates d.numLetters).eval ρ) := by
  have hbases := generator_staged_bases_above_count_cells p time d allowedIdx N
  exact ⟨clauseCountProg_preserves_generatorTableFrozen
      d.numStates d.numLetters (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
      (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N) prefIdx
      (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ hρ0 hbases.1
      hbases.2.1 hbases.2.2.1 hbases.2.2.2.1 hbases.2.2.2.2 hF,
    generator_count_stage_handoff_count_cell p time d allowedIdx outIdx prefIdx N ρ hρ0 hF⟩

/-- The clause-count stage does not touch the table-base pin. -/
lemma generator_count_stage_handoff_table_base (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (N : ℕ) (ρ : Store)
    (hρ0 : ρ 0 = setupM p time d allowedIdx N)
    (hwp : ρ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N) :
    (clauseCountProg d.numStates d.numLetters).eval ρ
        (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N := by
  rw [clauseCountProg_frame d.numStates d.numLetters
    (setupM p time d allowedIdx N)
    (setupM p time d allowedIdx N + wpJ) ρ hρ0 (by omega)
    (by norm_num [wpJ, rowCountReg]) (by norm_num [wpJ, iterReg])]
  exact hwp

lemma generator_count_stage_handoff (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
    let ρ := (Program.assign 0 (setupME p time d allowedIdx)).eval τ
    let κ := (clauseCountProg d.numStates d.numLetters).eval ρ
    GeneratorTableFrozenCount (setupM p time d allowedIdx N)
        ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
        (p.eval N) (generatorPrefLen N)
        (generatorPrefBase p time d allowedIdx N)
        (clauseCount d.numStates d.numLetters ((timePoly p time).eval N)
          ((cookWindowPoly p time).eval N) (p.eval N)) prefIdx
        (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
        (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
        (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
        (generatorOutBase p time d allowedIdx N) outIdx κ ∧
      κ 0 = setupM p time d allowedIdx N ∧
      κ (setupM p time d allowedIdx N + wpJ) =
        generatorTableBase p time d allowedIdx outIdx N ∧
      ClauseWriterIO (tableWriterProgParam d allowedIdx outIdx)
        (setupM p time d allowedIdx N) (generatorJmax d outIdx N) wpJ
        (GeneratorTableFrozenCount (setupM p time d allowedIdx N)
          ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
          (p.eval N) (generatorPrefLen N)
          (generatorPrefBase p time d allowedIdx N)
          (clauseCount d.numStates d.numLetters
            ((timePoly p time).eval N) ((cookWindowPoly p time).eval N)
            (p.eval N)) prefIdx
          (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
          (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
          (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
          (generatorOutBase p time d allowedIdx N) outIdx)
        (EmitterTableReadyCount (setupM p time d allowedIdx N)
          ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
          (generatorOutBase p time d allowedIdx N)
          (generatorOutBase p time d allowedIdx N + outIdx.length + 1)
          (clauseCount d.numStates d.numLetters
            ((timePoly p time).eval N) ((cookWindowPoly p time).eval N)
            (p.eval N)) outIdx)
        (descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval N)
            (d.numLetters + 1)) d prefIdx (p.eval N) allowedIdx outIdx
          ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)).clauses := by
  have he := generator_setup_handoff_entry p time d allowedIdx outIdx prefIdx σ N h0 hw
  obtain ⟨hF, hρ0, hwp, _, _⟩ := he
  have hp := generator_placement_of_layout p time d allowedIdx outIdx prefIdx N hlen
  have hio := tableWriterProgParam_io_param_with_count
    (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
    (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
    (generatorKindBase p time d allowedIdx N)
    (generatorArg1Base p time d allowedIdx N)
    (generatorArg2Base p time d allowedIdx N)
    (generatorOutBase p time d allowedIdx N)
    (clauseCount d.numStates d.numLetters
      ((timePoly p time).eval N) ((cookWindowPoly p time).eval N) (p.eval N)) d
    prefIdx allowedIdx outIdx hp
  exact ⟨generator_count_stage_handoff_frozen_count p time d allowedIdx outIdx prefIdx N _
      hρ0 hF,
    clauseCountProg_zero d.numStates d.numLetters (setupM p time d allowedIdx N) _ hρ0,
    generator_count_stage_handoff_table_base p time d allowedIdx outIdx N _ hρ0 hwp, hio⟩

lemma generator_prog_row_count (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    (generatorProg p time d allowedIdx outIdx).eval σ
        (setupM p time d allowedIdx N + rowCountReg) =
      clauseCount d.numStates d.numLetters
        ((timePoly p time).eval N) ((cookWindowPoly p time).eval N) (p.eval N) := by
  have hh := generator_count_stage_handoff p time d allowedIdx outIdx prefIdx σ N
    h0 hlen hw
  dsimp at hh
  obtain ⟨hκFC, hκ0, hκwp, hio⟩ := hh
  have hsep : setupM p time d allowedIdx N + generatorJmax d outIdx N <
      generatorTableBase p time d allowedIdx outIdx N := by
    simp [generatorTableBase]
  have hexit := hio _ (generatorTableBase p time d allowedIdx outIdx N)
    hκFC hκ0 hκwp hsep
  have hrow := hexit.1.2
  simpa only [generatorProg, eval_seq] using hrow

end NPComplete.CookLevin

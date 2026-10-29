module

public import NPComplete.CookLevin.ReductionProg.GeneratorProg
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
`generatorProg` is built purely from `assign`/`assignInd`/`seq`/`ifNZ`/`forN`, so it
is `ScanFree` by construction — the packaging lemma
`compiledOperandBound_of_programBoundedIn` needs this as one of its hypotheses.  The
program has too many `.seq` layers to unfold in one pass, so the proof climbs the
same build order as `GeneratorProg.lean`: primitives first (`writeLitsProg`,
`writeClauseProg`, `leafProg`, `loopProg`, `writeAtLeastOneProg`), then each of the
five clause families, then the setup and stage layers, and finally the top-level
`.seq` that assembles `generatorProg`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Shared primitives (`ClauseWriteSeq`, `ClauseWriteLoop`, `ClauseRowWrite`, `ParamSetup`) -/

lemma scanFree_paramSetupWrites (mE : Expr) (pairs : List (ℕ × Expr)) :
    ScanFree (paramSetupWrites mE pairs) := by
  induction pairs with
  | nil => simp [paramSetupWrites, ScanFree]
  | cons q rest ih => simp [paramSetupWrites, ScanFree, paramSetupAssign, ih]

lemma scanFree_writeLitsProg (wpJ : ℕ) (lits : List (Expr × Expr)) :
    ScanFree (writeLitsProg wpJ lits) := by
  induction lits with
  | nil => simp [writeLitsProg, ScanFree]
  | cons q rest ih =>
    simp only [writeLitsProg, ScanFree]
    exact ⟨by simp [writeLitProg, ScanFree, ctlAssign], ih⟩

lemma scanFree_writeClauseProg (wpJ : ℕ) (lits : List (Expr × Expr)) :
    ScanFree (writeClauseProg wpJ lits) := by
  simp [writeClauseProg, ScanFree, ctlAssign, scanFree_writeLitsProg]

lemma scanFree_leafProg (wpJ iJ : ℕ) (lits : List (Expr × Expr)) :
    ScanFree (leafProg wpJ iJ lits) := by
  simp [leafProg, ScanFree, ctlAssign, scanFree_writeClauseProg]

lemma scanFree_loopProg (iJ : ℕ) (cntE : Expr) (body : Program) (hbody : ScanFree body) :
    ScanFree (loopProg iJ cntE body) := by
  simp [loopProg, ScanFree, ctlAssign, hbody]

lemma scanFree_ctlAssign_bump (iJ : ℕ) :
    ScanFree (ctlAssign iJ (.add (ctlCell iJ) (.const 1))) := by
  simp [ctlAssign, ScanFree]

lemma scanFree_writeAtLeastOneBody (wpJ iJ : ℕ) (varE : Expr) :
    ScanFree (writeAtLeastOneBody wpJ iJ varE) := by
  simp [writeAtLeastOneBody, ScanFree, ctlAssign, writeLitProg]

lemma scanFree_writeAtLeastOneProg (wpJ iJ : ℕ) (cntE varE : Expr) :
    ScanFree (writeAtLeastOneProg wpJ iJ cntE varE) := by
  simp [writeAtLeastOneProg, ScanFree, ctlAssign, scanFree_writeAtLeastOneBody]

/-! ## The uniqueness family (`ClauseFamilyUniqueness`) -/

lemma scanFree_uniquenessFamilyProgParam (nS mS nC mC wReg tReg : ℕ) :
    ScanFree (uniquenessFamilyProgParam nS mS nC mC wReg tReg) := by
  unfold uniquenessFamilyProgParam
  refine scanFree_loopProg _ _ _
    (And.intro (And.intro (And.intro ?_ ?_) ?_) (scanFree_ctlAssign_bump _))
  · exact And.intro (scanFree_writeAtLeastOneProg _ _ _ _)
      (scanFree_loopProg _ _ _ (And.intro
        (scanFree_loopProg _ _ _ (scanFree_leafProg _ _ _)) (scanFree_ctlAssign_bump _)))
  · exact And.intro (scanFree_writeAtLeastOneProg _ _ _ _)
      (scanFree_loopProg _ _ _ (And.intro
        (scanFree_loopProg _ _ _ (scanFree_leafProg _ _ _)) (scanFree_ctlAssign_bump _)))
  · exact scanFree_loopProg _ _ _ (And.intro (And.intro
      (scanFree_writeAtLeastOneProg _ _ _ _)
      (scanFree_loopProg _ _ _ (And.intro
        (scanFree_loopProg _ _ _ (scanFree_leafProg _ _ _)) (scanFree_ctlAssign_bump _))))
      (scanFree_ctlAssign_bump _))

/-! ## The init family (`ClauseFamilyInitTail`, `ClauseFamilyInitWindow`, `ClauseFamilyInit`) -/

lemma scanFree_initStateProgParam (n m wReg : ℕ) (d : TableauDescriptor) :
    ScanFree (initStateProgParam n m wReg d) := by
  unfold initStateProgParam
  split <;> exact scanFree_writeClauseProg _ _

lemma scanFree_initHeadProgParam (n m wReg tReg : ℕ) :
    ScanFree (initHeadProgParam n m wReg tReg) := by
  simp [initHeadProgParam, scanFree_writeClauseProg]

lemma scanFree_initWindowLeafProgParam
    (n m blank wReg tReg fReg plReg pbReg : ℕ) (allowedIdx : List ℕ) :
    ScanFree (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx) := by
  unfold initWindowLeafProgParam
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by simp [ctlAssign, ScanFree], scanFree_writeClauseProg _ _⟩
  · exact scanFree_writeAtLeastOneProg _ _ _ _
  · exact scanFree_writeClauseProg _ _

lemma scanFree_initWindowProgParam
    (n m blank wReg tReg fReg plReg pbReg : ℕ) (allowedIdx : List ℕ) :
    ScanFree (initWindowProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx) := by
  unfold initWindowProgParam
  apply scanFree_loopProg
  simp [ScanFree, ctlAssign, scanFree_initWindowLeafProgParam]

lemma scanFree_initTailProgParam (n m blank wReg tReg fReg plReg : ℕ) :
    ScanFree (initTailProgParam n m blank wReg tReg fReg plReg) := by
  unfold initTailProgParam
  apply scanFree_loopProg
  simp [ScanFree, ctlAssign, scanFree_writeClauseProg]

lemma scanFree_initFamilyProgParam
    (n m : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) (wReg tReg fReg plReg pbReg : ℕ) :
    ScanFree (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg) := by
  simp [initFamilyProgParam, ScanFree, scanFree_initStateProgParam, scanFree_initHeadProgParam,
    scanFree_initWindowProgParam, scanFree_initTailProgParam]

/-! ## The trans family (`ClauseFamilyTransParam`) -/

lemma scanFree_transForbidBlockProgParam (nS mS wReg : ℕ) :
    ScanFree (transForbidBlockProgParam nS mS wReg) := by
  simp [transForbidBlockProgParam, ScanFree, scanFree_writeClauseProg]

lemma scanFree_transHaltBlockProgParam (nS mS wReg : ℕ) :
    ScanFree (transHaltBlockProgParam nS mS wReg) := by
  simp [transHaltBlockProgParam, ScanFree, scanFree_writeClauseProg]

lemma scanFree_transWriteBlockProgParam (nS mS wReg : ℕ) :
    ScanFree (transWriteBlockProgParam nS mS wReg) := by
  simp [transWriteBlockProgParam, ScanFree, scanFree_writeClauseProg]

lemma scanFree_transMoveBlockProgParam (nS mS wReg : ℕ) :
    ScanFree (transMoveBlockProgParam nS mS wReg) := by
  simp [transMoveBlockProgParam, ScanFree, scanFree_writeClauseProg]

lemma scanFree_transStageArgsProgParam (a1Reg a2Reg len1 len2 mC : ℕ) :
    ScanFree (transStageArgsProgParam a1Reg a2Reg len1 len2 mC) := by
  simp [transStageArgsProgParam, ScanFree, ctlAssign]

lemma scanFree_transAcceptWriteProgParam (nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) :
    ScanFree (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2) := by
  simp [transAcceptWriteProgParam, ScanFree, scanFree_transStageArgsProgParam,
    scanFree_transWriteBlockProgParam]

lemma scanFree_transAcceptMoveProgParam (nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) :
    ScanFree (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2) := by
  simp [transAcceptMoveProgParam, ScanFree, scanFree_transStageArgsProgParam,
    scanFree_transMoveBlockProgParam]

lemma scanFree_transLeafProgParam
    (nS mS nC mC wReg kbReg a1Reg a2Reg lenk len1 len2 : ℕ) :
    ScanFree (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg lenk len1 len2) := by
  unfold transLeafProgParam
  refine ⟨scanFree_transHaltBlockProgParam _ _ _, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨scanFree_transAcceptWriteProgParam _ _ _ _ _ _ _ _,
      scanFree_transForbidBlockProgParam _ _ _⟩
  · exact ⟨⟨scanFree_transAcceptMoveProgParam _ _ _ _ _ _ _ _,
      scanFree_transForbidBlockProgParam _ _ _⟩, scanFree_transForbidBlockProgParam _ _ _⟩

lemma scanFree_transFamilyProgParam (nS mS nC mC : ℕ) (d : TableauDescriptor)
    (wReg tReg kbReg a1Reg a2Reg : ℕ) :
    ScanFree (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg) := by
  unfold transFamilyProgParam
  refine scanFree_loopProg _ _ _ (And.intro ?_ (scanFree_ctlAssign_bump _))
  refine scanFree_loopProg _ _ _ (And.intro ?_ (scanFree_ctlAssign_bump _))
  refine scanFree_loopProg _ _ _ (And.intro ?_ (scanFree_ctlAssign_bump _))
  refine scanFree_loopProg _ _ _ (And.intro ?_ (scanFree_ctlAssign_bump _))
  exact scanFree_transLeafProgParam _ _ _ _ _ _ _ _ _ _ _

/-! ## The persist family (`ClauseFamilyPersist`) -/

lemma scanFree_persistFamilyProgParam (n m mC wReg tReg : ℕ) :
    ScanFree (persistFamilyProgParam n m mC wReg tReg) := by
  unfold persistFamilyProgParam
  refine scanFree_loopProg _ _ _ (And.intro ?_ (scanFree_ctlAssign_bump _))
  refine scanFree_loopProg _ _ _ (And.intro (And.intro ?_ ?_) (scanFree_ctlAssign_bump _))
  · exact scanFree_loopProg _ _ _
      (And.intro (scanFree_loopProg _ _ _ (scanFree_leafProg _ _ _)) (scanFree_ctlAssign_bump _))
  · exact scanFree_loopProg _ _ _
      (And.intro (scanFree_loopProg _ _ _ (scanFree_leafProg _ _ _)) (scanFree_ctlAssign_bump _))

/-! ## The accept family (`ClauseFamilyAcceptParam`) -/

lemma scanFree_acceptLeafProgParam (n m blank outLen wReg tReg obReg : ℕ) :
    ScanFree (acceptLeafProgParam n m blank outLen wReg tReg obReg) := by
  simp [acceptLeafProgParam, ScanFree, ctlAssign, scanFree_writeClauseProg]

lemma scanFree_acceptInnerProgParam (n m blank outLen wReg tReg obReg : ℕ) :
    ScanFree (acceptInnerProgParam n m blank outLen wReg tReg obReg) := by
  unfold acceptInnerProgParam
  apply scanFree_loopProg
  simp [ScanFree, ctlAssign, scanFree_acceptLeafProgParam]

lemma scanFree_acceptOuterProgParam (n m blank outLen wReg tReg obReg : ℕ) :
    ScanFree (acceptOuterProgParam n m blank outLen wReg tReg obReg) := by
  unfold acceptOuterProgParam
  apply scanFree_loopProg
  simp [ScanFree, ctlAssign, scanFree_acceptInnerProgParam]

lemma scanFree_acceptHaltProgParam (n m wReg tReg : ℕ) (qs : List ℕ) :
    ScanFree (acceptHaltProgParam n m wReg tReg qs) := by
  simp [acceptHaltProgParam, scanFree_writeAtLeastOneProg]

lemma scanFree_acceptFamilyProgParam
    (n m : ℕ) (d : TableauDescriptor) (outIdx : List ℕ) (wReg tReg obReg : ℕ) :
    ScanFree (acceptFamilyProgParam n m d outIdx wReg tReg obReg) := by
  simp [acceptFamilyProgParam, ScanFree, scanFree_acceptOuterProgParam,
    scanFree_acceptHaltProgParam]

/-! ## Setup, stage, and top-level composition (`GeneratorProg`) -/

lemma scanFree_setupProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : ScanFree (setupProg p time d allowedIdx) := by
  simp [setupProg, scanFree_paramSetupWrites]

lemma scanFree_generatorLayoutProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ScanFree (generatorLayoutProg p time d allowedIdx outIdx) := by
  simp [generatorLayoutProg, scanFree_paramSetupWrites]

lemma scanFree_generatorSetupProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ScanFree (generatorSetupProg p time d allowedIdx outIdx) := by
  simp [generatorSetupProg, ScanFree, scanFree_setupProg, scanFree_generatorLayoutProg]

lemma scanFree_triAccStep (rowCountReg iterReg : ℕ) :
    ScanFree (triAccStep rowCountReg iterReg) := by
  simp [triAccStep, ScanFree, ctlAssign]

lemma scanFree_triAccLoop (rowCountReg iterReg widthJ : ℕ) :
    ScanFree (triAccLoop rowCountReg iterReg widthJ) := by
  simp [triAccLoop, ScanFree, ctlAssign, scanFree_triAccStep]

lemma scanFree_clauseCountProg (n m : ℕ) :
    ScanFree (clauseCountProg n m) := by
  simp [clauseCountProg, ScanFree, ctlAssign, scanFree_triAccLoop]

lemma scanFree_loadTransParamsProg (d : TableauDescriptor) :
    ScanFree (loadTransParamsProg d) := by
  simp [loadTransParamsProg, ScanFree, ctlAssign]

lemma scanFree_loadAcceptParamProg (d : TableauDescriptor) :
    ScanFree (loadAcceptParamProg d) := by
  simp [loadAcceptParamProg, ctlAssign, ScanFree]

lemma scanFree_loadEmitterTableProg (outIdx : List ℕ) :
    ScanFree (loadEmitterTableProg outIdx) := by
  simp [loadEmitterTableProg, ctlAssign, ScanFree]

lemma scanFree_uniquenessStageProgParam (d : TableauDescriptor) :
    ScanFree (uniquenessStageProgParam d) := by
  simp [uniquenessStageProgParam, scanFree_uniquenessFamilyProgParam]

lemma scanFree_initStageProgParam (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ScanFree (initStageProgParam d allowedIdx) := by
  simp [initStageProgParam, ScanFree, scanFree_initFamilyProgParam, scanFree_loadTransParamsProg]

lemma scanFree_transStageProgParam (d : TableauDescriptor) :
    ScanFree (transStageProgParam d) := by
  simp [transStageProgParam, ScanFree, scanFree_transFamilyProgParam,
    scanFree_loadAcceptParamProg]

lemma scanFree_persistStageProgParam (d : TableauDescriptor) :
    ScanFree (persistStageProgParam d) := by
  simp [persistStageProgParam, scanFree_persistFamilyProgParam]

lemma scanFree_acceptStageProgParam (d : TableauDescriptor) (outIdx : List ℕ) :
    ScanFree (acceptStageProgParam d outIdx) := by
  simp [acceptStageProgParam, ScanFree, scanFree_acceptFamilyProgParam,
    scanFree_loadEmitterTableProg]

lemma scanFree_tableWriterProgParam (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) :
    ScanFree (tableWriterProgParam d allowedIdx outIdx) := by
  simp [tableWriterProgParam, ScanFree, scanFree_uniquenessStageProgParam,
    scanFree_initStageProgParam, scanFree_transStageProgParam, scanFree_persistStageProgParam,
    scanFree_acceptStageProgParam]

/-- `generatorProg` is built purely from `assign`/`assignInd`/`seq`/`ifNZ`/`forN`, never
    `scanList`/`lookup`, so `ScanFree` follows by unfolding its three-way `.seq` and its whole
    construction tree down to the primitives above. -/
lemma scanFree_generatorProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ScanFree (generatorProg p time d allowedIdx outIdx) := by
  simp [generatorProg, ScanFree, scanFree_generatorSetupProg,
    scanFree_clauseCountProg, scanFree_tableWriterProgParam]

end NPComplete.CookLevin

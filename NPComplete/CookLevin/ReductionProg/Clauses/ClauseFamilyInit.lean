module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitWindow
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitTail

/-!
The initial family is a concatenation rather than a single nest: two fixed
clauses, then one clause per window position, then one per free-suffix index.
Its two loops run over different counts and write different shapes, so neither
can be folded into the other — which is precisely the situation `ClauseWriter`
exists for, since a `.seq` of writers concatenates what they write.

Everything the four pieces need is already proved; what remains is that the
family's own definition *is* the concatenation of their four lists.  It is, by
`rfl`: the `++` in `descBoundedPrefixInitClauses` associates the same way once
the two leading clauses are read as singleton lists.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The initial family's program: the start-state clause, the head clause, the
    window loop, and the blank-propagation loop, in that order. -/
def initFamilyProg (n W m T : ℕ) (d : TableauDescriptor) (prefBase prefLen freeLen : ℕ)
    (allowedIdx : List ℕ) : Program :=
  .seq (initStateProg n W m d)
    (.seq (initHeadProg n W m T)
      (.seq (initWindowProg n W m T d.blankIdx prefBase prefLen freeLen W allowedIdx)
        (initTailProg n W m T prefLen d.blankIdx freeLen)))

/-- The full initial family, as a `ClauseWriter`.  Its clause list is
`descBoundedPrefixInitClauses` at the dense layout — the family's own definition,
not a restatement.  The `PinsAndWord` entry condition requires the prefix word at
`prefBase`, which the writer preserves. -/
lemma initFamilyProg_writer (M Jmax n W m T prefBase freeLen : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initFamilyProg n W m T d prefBase prefIdx.length freeLen allowedIdx)
      M Jmax wpJ (PinsAndWord M ctlPins0 prefBase prefIdx)
      (descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T) := by
  have heq : descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T
      = [descInitStateClause (denseLayout n W m) d] ++
        ([unitPos ((denseLayout n W m).head 0 (originIdx T))] ++
          (((List.range W).map fun p =>
              initWindowClause n W m T d.blankIdx prefIdx allowedIdx freeLen p) ++
            ((List.range freeLen).map fun i =>
              implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
                ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)))) := rfl
  rw [heq]
  unfold initFamilyProg
  refine clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_state_writer M Jmax n W m prefBase d prefIdx hJ hbase hfit) ?_
  refine clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_head_writer M Jmax n W m T prefBase prefIdx hJ hbase hfit) ?_
  exact clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_window_loop_writer M Jmax n W m T d.blankIdx prefBase freeLen prefIdx allowedIdx
      hJ hbase hfit)
    (init_tail_loop_writer M Jmax n W m T d.blankIdx prefBase freeLen prefIdx hJ hbase hfit)

/-! ## Run-time-parameter initial family -/

/-- The initial-family program whose syntax contains parameter addresses but not
    the five values stored in those cells. -/
def initFamilyProgParam (n m : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (wReg tReg fReg plReg pbReg : ℕ) : Program :=
  .seq (initStateProgParam n m wReg d)
    (.seq (initHeadProgParam n m wReg tReg)
      (.seq (initWindowProgParam n m d.blankIdx wReg tReg fReg plReg pbReg allowedIdx)
        (initTailProgParam n m d.blankIdx wReg tReg fReg plReg)))

lemma initFamilyProgParam_writer_param
    (M Jmax n W m T prefBase prefLen freeLen : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx : List ℕ) (wReg tReg fReg plReg pbReg : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length)
    (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg)
      M Jmax wpJ
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx)
      (descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T) := by
  have heq : descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T
      = [descInitStateClause (denseLayout n W m) d] ++
        ([unitPos ((denseLayout n W m).head 0 (originIdx T))] ++
          (((List.range W).map fun p =>
              initWindowClause n W m T d.blankIdx prefIdx allowedIdx freeLen p) ++
            ((List.range freeLen).map fun i =>
              implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
                ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)))) := rfl
  rw [heq]
  unfold initFamilyProgParam
  refine clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_state_writer_param M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg
      pbReg d prefIdx hplace hbase hfit) ?_
  refine clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_head_writer_param M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg
      pbReg prefIdx hplace hbase hfit) ?_
  exact clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (init_window_loop_writer_param M Jmax n W m T d.blankIdx prefBase prefLen freeLen
      wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hbase hfit)
    (init_tail_loop_writer_param M Jmax n W m T d.blankIdx prefBase prefLen freeLen
      wReg tReg fReg plReg pbReg prefIdx hplace hlen hbase hfit)

end NPComplete.CookLevin

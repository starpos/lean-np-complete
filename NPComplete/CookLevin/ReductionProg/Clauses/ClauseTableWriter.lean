module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteFrozen
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyUniquenessCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTrans
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyPersistCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptExpr

/-!
The five family writers cannot be concatenated by `clauseWriter_seq`, and the
reason is geometric rather than bookkeeping.  A family that *reads* a staged
word needs that word inside its control extent, while the frame promise that
carries a word *past* a family covers only cells above that family's extent —
so no single predicate, and no single extent, serves all five.  Sharing one
extent would force each family's read words below it and its carried words
above it, and with two families reading different words the two demands close
into a circle.

The way out is to let every stage run at its own extent and to lay the staged
words out in the order the families consume them (prefix, kind, arg1, arg2,
output).  A stage's extent then sits in the gap between the words it has
already read and the words it still carries, `ClauseWriterIO` drops each word
at the family that reads it, and `clauseWriterIO_carry_widen` widens a stage
across one gap at a time up to the extent the whole concatenation runs at.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Entry predicates

Both predicates are the left-nested conjunctions that repeated carrying
produces, so no conversion lemma is needed at the seams between stages. -/

/-- The predicate a five-family concatenation starts from: the control pins
    together with every word some family will read.  The nesting is inside-out
    — the prefix word innermost, the output word outermost — so that repeated
    carrying adds its conjunct on the outside and no conversion is needed at
    the seams between stages. -/
def TableFrozen (M : ℕ) (pins : List (ℕ × ℕ))
    (prefBase : ℕ) (prefIdx : List ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) (outBase : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  ((((PinsHold M pins τ ∧ WordAt τ prefBase prefIdx) ∧ WordAt τ kindBase colk) ∧
      WordAt τ arg1Base col1) ∧ WordAt τ arg2Base col2) ∧ WordAt τ outBase outIdx

/-- The middle predicate between the initial and the transition stages: the
    prefix word has been consumed, the three table columns and the output word
    are still staged. -/
def TransOutFrozen (M : ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (outBase : ℕ) (outIdx : List ℕ) (τ : Store) : Prop :=
  (((PinsHold M ctlPins0 τ ∧ WordAt τ kindBase colk) ∧ WordAt τ arg1Base col1) ∧
      WordAt τ arg2Base col2) ∧ WordAt τ outBase outIdx

/-! ## Carrying words across a gap in the extent chain

A stage that reads a word runs at a larger extent than `ctlJmax`, and the words
it still carries have to cross the gap between its extent and the target one.
The lemma below takes the writer's own extent as `J1`; the word then lives in the
gap strictly between `J1` and the target extent `J2`, which is exactly why the two
placement hypotheses point in opposite directions and why `J1 = J2` would make them
contradictory. -/

/-- A writer at extent `J1` carries a word it never reads up to extent `J2`:
    the word sits above the writer's own control block, where its frame
    promise reaches, and inside the wider extent, so the entry separation
    keeps it below the pointer. -/
lemma clauseWriterIO_carry_widen (prog : Program) (M J1 J2 : ℕ)
    (Entry Exit : Store → Prop) (base : ℕ) (xs : List ℕ) (cs : List Clause)
    (hbase : M + J1 + 1 < base) (hfit : base + xs.length ≤ M + J2)
    (h : ClauseWriterIO prog M J1 wpJ Entry Exit cs) :
    ClauseWriterIO prog M J2 wpJ (fun τ => Entry τ ∧ WordAt τ base xs)
      (fun τ => Exit τ ∧ WordAt τ base xs) cs := by
  intro τ wp hF h0 hw hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h τ wp hF.1 h0 hw (by omega)
  obtain ⟨hlen, hdata⟩ := hF.2
  refine ⟨⟨a1, ?_, fun k hk => ?_⟩, a2, a3, a4, fun r hr1 hr2 => a5 r hr1 ?_⟩
  · rw [a5 (base - 1) (by omega) (Or.inr (by omega))]; exact hlen
  · rw [a5 (base + k) (by omega) (Or.inr (by omega))]; exact hdata k hk
  · unfold CtlFree at hr2 ⊢; omega

/-- Three words crossing three successive gaps, which is the shape both the
    uniqueness and the initial stages need: their carried table columns are
    consecutive on the tape, so one lemma covers the chain. -/
lemma clauseWriterIO_carry3_widen (prog : Program) (M J0 J1 J2 J3 : ℕ)
    (Entry Exit : Store → Prop) (bk : ℕ) (xsk : List ℕ) (b1 : ℕ) (xs1 : List ℕ)
    (b2 : ℕ) (xs2 : List ℕ) (cs : List Clause)
    (hk0 : M + J0 + 1 < bk) (hkfit : bk + xsk.length ≤ M + J1)
    (h10 : M + J1 + 1 < b1) (h1fit : b1 + xs1.length ≤ M + J2)
    (h20 : M + J2 + 1 < b2) (h2fit : b2 + xs2.length ≤ M + J3)
    (h : ClauseWriterIO prog M J0 wpJ Entry Exit cs) :
    ClauseWriterIO prog M J3 wpJ
      (fun τ => ((Entry τ ∧ WordAt τ bk xsk) ∧ WordAt τ b1 xs1) ∧ WordAt τ b2 xs2)
      (fun τ => ((Exit τ ∧ WordAt τ bk xsk) ∧ WordAt τ b1 xs1) ∧ WordAt τ b2 xs2) cs := by
  have hA : ClauseWriterIO prog M J1 wpJ (fun τ => Entry τ ∧ WordAt τ bk xsk)
      (fun τ => Exit τ ∧ WordAt τ bk xsk) cs :=
    clauseWriterIO_carry_widen _ M J0 J1 _ _ bk xsk _ hk0 hkfit h
  have hB : ClauseWriterIO prog M J2 wpJ
      (fun τ => (Entry τ ∧ WordAt τ bk xsk) ∧ WordAt τ b1 xs1)
      (fun τ => (Exit τ ∧ WordAt τ bk xsk) ∧ WordAt τ b1 xs1) cs :=
    clauseWriterIO_carry_widen _ M J1 J2 _ _ b1 xs1 _ h10 h1fit hA
  exact clauseWriterIO_carry_widen _ M J2 J3 _ _ b2 xs2 _ h20 h2fit hB

/-! ## The five-family program

Three of the five families, uniqueness, transition, and persist, use the named programs
from their family files.  Each name is the term its own family writer is about, unchanged. -/

/-- The five families in `descTableauCNF` order, as one program.  It depends on
    no extent: extents belong to the correctness statement, not the code. -/
def tableWriterProg (n W m T : ℕ) (d : TableauDescriptor)
    (prefBase prefLen freeLen : ℕ) (allowedIdx : List ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (outIdx : List ℕ) : Program :=
  .seq (.seq (.seq (.seq (uniquenessFamilyProg n W m T)
      (initFamilyProg n W m T d prefBase prefLen freeLen allowedIdx))
      (transFamilyProg n W m T d kindBase arg1Base arg2Base))
      (persistFamilyProg n W m T))
      (acceptFamilyProg n W m T outBase d.blankIdx outIdx.length
        (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)))

/-! ## Stride/count-separated programs -/

/-- The five-family program with layout strides separated from family counts. -/
def tableWriterProgGen (nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (prefBase prefLen freeLen : ℕ) (allowedIdx : List ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (outIdx : List ℕ) : Program :=
  .seq (.seq (.seq (.seq (uniquenessFamilyProgGen nS W mS nC mC T)
      (initFamilyProg nS W mS T d prefBase prefLen freeLen allowedIdx))
      (transFamilyProgGen nS W mS nC mC T d kindBase arg1Base arg2Base))
      (persistFamilyProgGen nS W mS mC T))
      (acceptFamilyProg nS W mS T outBase d.blankIdx outIdx.length
        (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)))

/-- Equal strides and counts recover the original five-family program. -/
lemma table_writer_prog_gen_self (n W m T : ℕ) (d : TableauDescriptor)
    (prefBase prefLen freeLen : ℕ) (allowedIdx : List ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (outIdx : List ℕ) :
    tableWriterProgGen n W m n m T d prefBase prefLen freeLen allowedIdx
      kindBase arg1Base arg2Base outBase outIdx =
    tableWriterProg n W m T d prefBase prefLen freeLen allowedIdx
      kindBase arg1Base arg2Base outBase outIdx := by
  simp only [tableWriterProgGen, tableWriterProg, uniquenessFamilyProg,
    transFamilyProg, persistFamilyProg]

/-- The five clause families with layout strides separated from family counts. -/
def tableWriterClausesGen (nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) : List Clause :=
  execUniquenessClausesAt (denseLayout nS W mS) (List.range nC) (List.range mC) W T ++
    descBoundedPrefixInitClauses (denseLayout nS W mS) d
      prefIdx freeLen allowedIdx W T ++
    transClausesTripleFamily (denseLayout nS W mS) nC W mC T
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2) ++
    execPersistClausesAt (denseLayout nS W mS) (List.range mC) W T ++
    descAcceptClauses (denseLayout nS W mS) d outIdx W T

/-- Descriptor counts turn the separated family list into the target CNF. -/
lemma table_writer_clauses_gen_eq_desc (nS W mS T : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) :
    tableWriterClausesGen nS W mS d.numStates d.numLetters T d
        prefIdx freeLen allowedIdx outIdx =
      (descTableauCNF (denseLayout nS W mS) d
        prefIdx freeLen allowedIdx outIdx W T).clauses := by
  rw [tableWriterClausesGen, trans_clauses_triple_family_eq_desc]
  rfl

/-! ## The concatenation -/

/-- The placement inequalities the concatenation needs are jointly satisfiable.  The five
    words sit in consumption order three cells apart, which leaves a gap for each stage's
    extent between one word's top and the next word's length cell.  That the entry predicate
    itself is satisfiable is shown in `ClauseTableWriterCheck.lean`. -/
lemma table_writer_placement_satisfiable :
    ∃ (M Jmax n _W _m _T prefBase _freeLen kindBase arg1Base arg2Base outBase : ℕ)
      (d : TableauDescriptor) (prefIdx _allowedIdx outIdx : List ℕ),
      d.numStates = n ∧ d.numLetters = _m ∧
      M + ctlJmax + 1 < prefBase ∧
      prefBase + prefIdx.length + 1 < kindBase ∧
      kindBase + (d.table.map transKind).length + 1 < arg1Base ∧
      arg1Base + (d.table.map transArg1).length + 1 < arg2Base ∧
      arg2Base + (d.table.map transArg2).length + 1 < outBase ∧
      outBase + outIdx.length ≤ M + Jmax := by
  refine ⟨0, 22, 1, 1, 1, 1, 9, 0, 12, 15, 18, 21, initCheckDesc, [0], [0], [0],
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ctlJmax; omega
  · norm_num
  · norm_num [initCheckDesc]
  · norm_num [initCheckDesc]
  · norm_num [initCheckDesc]
  · norm_num

/-- The five-family writer with layout strides separated from family counts. -/
lemma tableWriterProgGen_io_gen (M Jmax nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (prefBase freeLen : ℕ) (prefIdx allowedIdx : List ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (outIdx : List ℕ)
    (hPrefBase : M + ctlJmax + 1 < prefBase)
    (hPrefK : prefBase + prefIdx.length + 1 < kindBase)
    (hKA1 : kindBase + (d.table.map transKind).length + 1 < arg1Base)
    (hA1A2 : arg1Base + (d.table.map transArg1).length + 1 < arg2Base)
    (hA2Out : arg2Base + (d.table.map transArg2).length + 1 < outBase)
    (hOutFit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriterIO
      (tableWriterProgGen nS W mS nC mC T d prefBase prefIdx.length freeLen allowedIdx
        kindBase arg1Base arg2Base outBase outIdx)
      M Jmax wpJ
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (PinsHold M ctlPins0)
      (tableWriterClausesGen nS W mS nC mC T d
        prefIdx freeLen allowedIdx outIdx) := by
  have hW1 : ClauseWriterIO (uniquenessFamilyProgGen nS W mS nC mC T) M Jmax wpJ
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (execUniquenessClausesAt (denseLayout nS W mS)
        (List.range nC) (List.range mC) W T) :=
    clauseWriterIO_carry_widen _ M (arg2Base + (d.table.map transArg2).length - M)
      Jmax _ _ outBase outIdx _ (by omega) hOutFit
      (clauseWriterIO_carry3_widen _ M (prefBase + prefIdx.length - M)
        (kindBase + (d.table.map transKind).length - M)
        (arg1Base + (d.table.map transArg1).length - M)
        (arg2Base + (d.table.map transArg2).length - M) _ _
        kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) _
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (clauseWriterIO_carry_widen _ M ctlJmax (prefBase + prefIdx.length - M) _ _
          prefBase prefIdx _ hPrefBase (by omega)
          (clauseWriterIO_of_writer _ M ctlJmax wpJ _ _
            (uniquenessFamilyProgGen_writer_gen M nS W mS nC mC T))))
  have hW2 : ClauseWriterIO
      (initFamilyProg nS W mS T d prefBase prefIdx.length freeLen allowedIdx) M Jmax wpJ
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (TransOutFrozen M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (descBoundedPrefixInitClauses (denseLayout nS W mS) d
        prefIdx freeLen allowedIdx W T) :=
    clauseWriterIO_carry_widen _ M (arg2Base + (d.table.map transArg2).length - M)
      Jmax _ _ outBase outIdx _ (by omega) hOutFit
      (clauseWriterIO_carry3_widen _ M (prefBase + prefIdx.length - M)
        (kindBase + (d.table.map transKind).length - M)
        (arg1Base + (d.table.map transArg1).length - M)
        (arg2Base + (d.table.map transArg2).length - M) _ _
        kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) _
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (clauseWriterIO_weaken_exit _ M (prefBase + prefIdx.length - M) wpJ
          (PinsAndWord M ctlPins0 prefBase prefIdx) (PinsAndWord M ctlPins0 prefBase prefIdx)
          (PinsHold M ctlPins0)
          (descBoundedPrefixInitClauses (denseLayout nS W mS) d
            prefIdx freeLen allowedIdx W T)
          (fun τ h => h.1)
          (clauseWriterIO_of_writer _ M (prefBase + prefIdx.length - M) wpJ _ _
            (initFamilyProg_writer M (prefBase + prefIdx.length - M) nS W mS T prefBase
              freeLen d prefIdx allowedIdx (by omega) (by omega) (by omega)))))
  have hW3 : ClauseWriterIO
      (transFamilyProgGen nS W mS nC mC T d kindBase arg1Base arg2Base) M Jmax wpJ
      (TransOutFrozen M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (fun τ => PinsHold M ctlPins0 τ ∧ WordAt τ outBase outIdx)
      (transClausesTripleFamily (denseLayout nS W mS) nC W mC T
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) :=
    clauseWriterIO_carry_widen
      (transFamilyProgGen nS W mS nC mC T d kindBase arg1Base arg2Base) M
      (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2)) Jmax _ _ outBase outIdx _
      (by simp only [transJM, transJmax]; omega) hOutFit
      (clauseWriterIO_strengthen_entry _ M _ wpJ
        (TransFrozen M ctlPins0 kindBase (d.table.map transKind) arg1Base
          (d.table.map transArg1) arg2Base (d.table.map transArg2))
        _ (PinsHold M ctlPins0) _
        (fun τ h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
        (clauseWriterIO_weaken_exit _ M _ wpJ _ _ (PinsHold M ctlPins0) _
          (fun τ h => h.1)
          (clauseWriterIO_of_writer _ M _ wpJ _ _
            (transFamilyProgGen_writer_gen M nS W mS nC mC T kindBase arg1Base arg2Base d
              (by omega) (by omega) (by omega)))))
  have hW4 : ClauseWriterIO (persistFamilyProgGen nS W mS mC T) M Jmax wpJ
      (fun τ => PinsHold M ctlPins0 τ ∧ WordAt τ outBase outIdx)
      (fun τ => PinsHold M ctlPins0 τ ∧ WordAt τ outBase outIdx)
      (execPersistClausesAt (denseLayout nS W mS) (List.range mC) W T) :=
    clauseWriterIO_carry_widen _ M ctlJmax Jmax _ _ outBase outIdx _ (by omega) hOutFit
      (clauseWriterIO_of_writer _ M ctlJmax wpJ _ _
        (persistFamilyProgGen_writer_gen M nS W mS mC T))
  have hW5 : ClauseWriterIO
      (acceptFamilyProg nS W mS T outBase d.blankIdx outIdx.length
        (descHaltStates d (natInitSymbol d.blankIdx outIdx 0))) M Jmax wpJ
      (fun τ => PinsHold M ctlPins0 τ ∧ WordAt τ outBase outIdx) (PinsHold M ctlPins0)
      (descAcceptClauses (denseLayout nS W mS) d outIdx W T) :=
    clauseWriterIO_weaken_exit _ M Jmax wpJ _
      (PinsAndWord M ctlPins0 outBase outIdx) (PinsHold M ctlPins0)
      (descAcceptClauses (denseLayout nS W mS) d outIdx W T) (fun τ h => h.1)
      (clauseWriterIO_of_writer _ M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx) _
        (acceptFamilyProg_writer M Jmax nS W mS T outBase d outIdx
          (by omega) (by omega) hOutFit))
  have hUI := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hW1 hW2
  have hUIT := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUI hW3
  have hUITP := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUIT hW4
  simpa only [tableWriterProgGen, tableWriterClausesGen] using
    clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUITP hW5

/-- The whole generator in one contract: from the control pins and every
    staged word, the five families in `descTableauCNF` order write the
    reduction's own clause list and leave only the pins.  Each stage runs at
    its own extent — the prefix top for the initial family, `transJM` for the
    transition one — and the placement hypotheses say exactly that the five
    words are ordered as consumed, each strictly inside the gap between the
    extent of the family that reads it and that of the next one to carry it. -/
lemma tableWriterProg_io (M Jmax n W m T : ℕ) (d : TableauDescriptor)
    (prefBase freeLen : ℕ) (prefIdx allowedIdx : List ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (outIdx : List ℕ)
    (hn : d.numStates = n) (hm : d.numLetters = m)
    (hPrefBase : M + ctlJmax + 1 < prefBase)
    (hPrefK : prefBase + prefIdx.length + 1 < kindBase)
    (hKA1 : kindBase + (d.table.map transKind).length + 1 < arg1Base)
    (hA1A2 : arg1Base + (d.table.map transArg1).length + 1 < arg2Base)
    (hA2Out : arg2Base + (d.table.map transArg2).length + 1 < outBase)
    (hOutFit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriterIO (tableWriterProg n W m T d prefBase prefIdx.length freeLen allowedIdx
        kindBase arg1Base arg2Base outBase outIdx)
      M Jmax wpJ
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (PinsHold M ctlPins0)
      (descTableauCNF (denseLayout n W m) d prefIdx freeLen allowedIdx outIdx W T).clauses := by
  have h := tableWriterProgGen_io_gen M Jmax n W m d.numStates d.numLetters T d
    prefBase freeLen prefIdx allowedIdx kindBase arg1Base arg2Base outBase outIdx
    hPrefBase hPrefK hKA1 hA1A2 hA2Out hOutFit
  rw [table_writer_clauses_gen_eq_desc] at h
  simpa only [hn, hm, table_writer_prog_gen_self] using h

end NPComplete.CookLevin

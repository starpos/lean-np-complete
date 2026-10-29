module

public import NPComplete.CookLevin.ReductionProg.ParamSetup
public import NPComplete.CookLevin.ReductionProg.GeneratorRowCount
public import NPComplete.BoundedWhile.Frame

/-!
The fixed generator has two setup layers.  `setupProg` computes the scalar
parameters from the input length.  The layout layer below replaces its
constant-gap staged-word bases by gaps computed from the actual prefix and
descriptor-column lengths, and initializes the writer and emitter with one
common table base.

The clause-family programs contain only descriptor data, fixed register
addresses, and the two compile-time index lists.  Two short reload programs
separate the initial and transition stages.  They re-establish parameter cells
which the preceding writer contract does not expose in its exit predicate;
their values are computed from parameter cells that contract does preserve.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Dynamic staged-word layout -/

def generatorTableBaseReg : ℕ := 24

def generatorPrefOffset : ℕ := 30

def generatorPrefLen (N : ℕ) : ℕ := 2 * N + 1

def generatorKindOffset (N : ℕ) : ℕ :=
  generatorPrefOffset + generatorPrefLen N + 2

def generatorArg1Offset (d : TableauDescriptor) (N : ℕ) : ℕ :=
  generatorKindOffset N + d.table.length + 2

def generatorArg2Offset (d : TableauDescriptor) (N : ℕ) : ℕ :=
  generatorArg1Offset d N + d.table.length + 2

def generatorOutOffset (d : TableauDescriptor) (N : ℕ) : ℕ :=
  generatorArg2Offset d N + d.table.length + 2

def generatorJmax (d : TableauDescriptor) (outIdx : List ℕ) (N : ℕ) : ℕ :=
  generatorOutOffset d N + outIdx.length

noncomputable def generatorPrefBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorPrefOffset

noncomputable def generatorKindBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorKindOffset N

noncomputable def generatorArg1Base (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorArg1Offset d N

noncomputable def generatorArg2Base (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorArg2Offset d N

noncomputable def generatorOutBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorOutOffset d N

noncomputable def generatorTableBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (N : ℕ) : ℕ :=
  setupM p time d allowedIdx N + generatorJmax d outIdx N + 1

def generatorPrefLenE : Expr :=
  .add (.mul (.const 2) (.reg 0)) (.const 1)

noncomputable def generatorPrefBaseE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .add (setupME p time d allowedIdx) (.const generatorPrefOffset)

noncomputable def generatorKindBaseE (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  .add (.add (generatorPrefBaseE p time d allowedIdx) generatorPrefLenE) (.const 2)

noncomputable def generatorArg1BaseE (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) : Expr :=
  .add (generatorKindBaseE p time d allowedIdx) (.const (d.table.length + 2))

noncomputable def generatorArg2BaseE (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) : Expr :=
  .add (generatorArg1BaseE p time d allowedIdx) (.const (d.table.length + 2))

noncomputable def generatorOutBaseE (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) : Expr :=
  .add (generatorArg2BaseE p time d allowedIdx) (.const (d.table.length + 2))

noncomputable def generatorTableBaseE (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : Expr :=
  .add (generatorOutBaseE p time d allowedIdx) (.const (outIdx.length + 1))

noncomputable def generatorLayoutPairs (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : List (ℕ × Expr) :=
  [(initPrefBaseReg, generatorPrefBaseE p time d allowedIdx),
   (transKindBaseReg, generatorKindBaseE p time d allowedIdx),
   (transArg1BaseReg, generatorArg1BaseE p time d allowedIdx),
   (transArg2BaseReg, generatorArg2BaseE p time d allowedIdx),
   (acceptOutBaseReg, generatorOutBaseE p time d allowedIdx),
   (wpJ, generatorTableBaseE p time d allowedIdx outIdx),
   (emTblJ, generatorTableBaseE p time d allowedIdx outIdx),
   (generatorTableBaseReg, generatorTableBaseE p time d allowedIdx outIdx)]

noncomputable def generatorLayoutProg (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : Program :=
  paramSetupWrites (setupME p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx)

noncomputable def generatorSetupProg (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) : Program :=
  .seq (setupProg p time d allowedIdx) (generatorLayoutProg p time d allowedIdx outIdx)

/-! ## Parameterized five-family program -/

def loadTransParamsProg (d : TableauDescriptor) : Program :=
  .seq
    (ctlAssign transKindBaseReg
      (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2)))
    (.seq
      (ctlAssign transArg1BaseReg
        (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2))))
      (ctlAssign transArg2BaseReg
        (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2)))))

def loadAcceptParamProg (d : TableauDescriptor) : Program :=
  ctlAssign acceptOutBaseReg
    (.add (ctlCell transArg2BaseReg) (.const (d.table.length + 2)))

def loadEmitterTableProg (outIdx : List ℕ) : Program :=
  ctlAssign emTblJ
    (.add (ctlCell acceptOutBaseReg) (.const (outIdx.length + 1)))

def uniquenessStageProgParam (d : TableauDescriptor) : Program :=
  uniquenessFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
    d.numStates d.numLetters uniquenessWReg uniquenessTReg

def initStageProgParam (d : TableauDescriptor) (allowedIdx : List ℕ) : Program :=
  .seq
    (initFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d allowedIdx
      initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg)
    (loadTransParamsProg d)

def transStageProgParam (d : TableauDescriptor) : Program :=
  .seq
    (transFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
      d.numStates d.numLetters d transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg)
    (loadAcceptParamProg d)

def persistStageProgParam (d : TableauDescriptor) : Program :=
  persistFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
    d.numLetters persistWReg persistTReg

def acceptStageProgParam (d : TableauDescriptor) (outIdx : List ℕ) : Program :=
  .seq
    (acceptFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d outIdx
      acceptWReg acceptTReg acceptOutBaseReg)
    (loadEmitterTableProg outIdx)

def tableWriterProgParam (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (.seq (.seq (.seq
    (uniquenessStageProgParam d)
    (initStageProgParam d allowedIdx))
    (transStageProgParam d))
    (persistStageProgParam d))
    (acceptStageProgParam d outIdx)

noncomputable def generatorProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (generatorSetupProg p time d allowedIdx outIdx)
    (.seq (.assign 0 (setupME p time d allowedIdx))
      (.seq (clauseCountProg d.numStates d.numLetters)
        (tableWriterProgParam d allowedIdx outIdx)))

/-! ## Entry predicates and an IO transport for extra pins -/

def GeneratorTableFrozen (M W T freeLen prefLen prefBase : ℕ)
    (prefIdx : List ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (outBase : ℕ) (outIdx : List ℕ) (τ : Store) : Prop :=
  ((((InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg W T freeLen prefLen prefBase prefIdx τ ∧
      WordAt τ kindBase colk) ∧ WordAt τ arg1Base col1) ∧
      WordAt τ arg2Base col2) ∧ WordAt τ outBase outIdx)

lemma clauseWriterIO_pins_widen (prog : Program) (M J1 J2 : ℕ)
    (pins extra : List (ℕ × ℕ)) (cs : List Clause)
    (hJ : J1 ≤ J2) (habove : ∀ p ∈ extra, J1 < p.1)
    (hfit : ∀ p ∈ extra, p.1 ≤ J2)
    (h : ClauseWriterIO prog M J1 wpJ (PinsHold M pins) (PinsHold M pins) cs) :
    ClauseWriterIO prog M J2 wpJ (PinsHold M (pins ++ extra))
      (PinsHold M (pins ++ extra)) cs := by
  intro τ wp hF h0 hw hsep
  have hsmall : PinsHold M pins τ := by
    intro p hp
    exact hF p (List.mem_append_left extra hp)
  obtain ⟨a1, a2, a3, a4, a5⟩ := h τ wp hsmall h0 hw (by omega)
  refine ⟨?_, a2, a3, a4, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact a1 p hp
    · rw [a5 (M + p.1) (by have := hfit p hp; omega) (Or.inr (by
        have := habove p hp
        omega))]
      exact hF p (List.mem_append_right pins hp)
  · intro r hr hfree
    exact a5 r hr (by
      unfold CtlFree at hfree ⊢
      omega)

def InitParamsAndTransOutFrozen (M W T freeLen prefLen prefBase : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) (outBase : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  ((((PinsHold M
      (initParamPins0 initWReg initTReg initFreeLenReg initPrefLenReg
        initPrefBaseReg W T freeLen prefLen prefBase) τ ∧
      WordAt τ kindBase colk) ∧ WordAt τ arg1Base col1) ∧
      WordAt τ arg2Base col2) ∧ WordAt τ outBase outIdx)

def TransWithOutFrozen (M W T kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (outBase : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  TransParamFrozen M transWReg transTReg transKindBaseReg transArg1BaseReg
    transArg2BaseReg W T kindBase arg1Base arg2Base colk col1 col2 τ ∧
    WordAt τ outBase outIdx

def EmitterTableReady (M W T outBase tableBase : ℕ) (outIdx : List ℕ)
    (τ : Store) : Prop :=
  AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx τ ∧
  τ (M + emTblJ) = tableBase

lemma load_trans_params_io (M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (hregs : transArg2BaseReg ≤ Jmax)
    (hkind : prefBase + prefLen + 2 = kindBase)
    (harg1 : kindBase + d.table.length + 2 = arg1Base)
    (harg2 : arg1Base + d.table.length + 2 = arg2Base)
    (hbase : M + transArg2BaseReg + 1 < kindBase)
    (houtbase : M + transArg2BaseReg + 1 < outBase) :
    ClauseWriterIO (loadTransParamsProg d) M Jmax wpJ
      (InitParamsAndTransOutFrozen M W T freeLen prefLen prefBase kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx) [] := by
  intro τ wp hF h0 hwp hsep
  let p0 := initParamPins0 initWReg initTReg initFreeLenReg initPrefLenReg
    initPrefBaseReg W T freeLen prefLen prefBase
  have hpins : PinsHold M p0 τ := hF.1.1.1.1
  have hpref : τ (M + initPrefBaseReg) = prefBase := by
    exact hpins (initPrefBaseReg, prefBase) (by simp [p0, initParamPins0])
  have hplen : τ (M + initPrefLenReg) = prefLen := by
    exact hpins (initPrefLenReg, prefLen) (by simp [p0, initParamPins0])
  have hk1 : transKindBaseReg < transArg1BaseReg := by
    norm_num [transKindBaseReg, transArg1BaseReg]
  have h12 : transArg1BaseReg < transArg2BaseReg := by
    norm_num [transArg1BaseReg, transArg2BaseReg]
  have hwk : transWReg < transKindBaseReg := by
    norm_num [transWReg, transKindBaseReg]
  have htk : transTReg < transKindBaseReg := by
    norm_num [transTReg, transKindBaseReg]
  set τ1 := (ctlAssign transKindBaseReg
    (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2))).eval τ
  have hτ1f (r : ℕ) (hr : r ≠ M + transKindBaseReg) : τ1 r = τ r := by
    simpa only [τ1] using ctlAssign_eval_diff transKindBaseReg
      (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2))
      τ r (by simpa [h0] using hr)
  have hk : τ1 (M + transKindBaseReg) = kindBase := by
    have h := ctlAssign_eval_same transKindBaseReg
      (.add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2)) τ
    calc
      τ1 (M + transKindBaseReg) = prefBase + prefLen + 2 := by
        simpa [τ1, Expr.eval, ctlCell_eval, h0, hpref, hplen] using h
      _ = kindBase := hkind
  set τ2 := (ctlAssign transArg1BaseReg
    (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2)))).eval τ1
  have hτ10 : τ1 0 = M := by rw [hτ1f 0 (by omega), h0]
  have hτ2f (r : ℕ) (hr : r ≠ M + transArg1BaseReg) : τ2 r = τ1 r := by
    simpa only [τ2] using ctlAssign_eval_diff transArg1BaseReg
      (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2)))
      τ1 r (by simpa [hτ10] using hr)
  have ha1 : τ2 (M + transArg1BaseReg) = arg1Base := by
    have h := ctlAssign_eval_same transArg1BaseReg
      (.add (ctlCell transKindBaseReg) (.const (d.table.length + 2))) τ1
    calc
      τ2 (M + transArg1BaseReg) = kindBase + (d.table.length + 2) := by
        simpa [τ2, Expr.eval, ctlCell_eval, hτ10, hk] using h
      _ = arg1Base := by omega
  set τ3 := (ctlAssign transArg2BaseReg
    (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2)))).eval τ2
  have hτ20 : τ2 0 = M := by rw [hτ2f 0 (by omega), hτ10]
  have hτ3f (r : ℕ) (hr : r ≠ M + transArg2BaseReg) : τ3 r = τ2 r := by
    simpa only [τ3] using ctlAssign_eval_diff transArg2BaseReg
      (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2)))
      τ2 r (by simpa [hτ20] using hr)
  have ha2 : τ3 (M + transArg2BaseReg) = arg2Base := by
    have h := ctlAssign_eval_same transArg2BaseReg
      (.add (ctlCell transArg1BaseReg) (.const (d.table.length + 2))) τ2
    calc
      τ3 (M + transArg2BaseReg) = arg1Base + (d.table.length + 2) := by
        simpa [τ3, Expr.eval, ctlCell_eval, hτ20, ha1] using h
      _ = arg2Base := by omega
  have hframe (r : ℕ) (hrk : r ≠ M + transKindBaseReg)
      (hr1 : r ≠ M + transArg1BaseReg) (hr2 : r ≠ M + transArg2BaseReg) :
      τ3 r = τ r := by rw [hτ3f r hr2, hτ2f r hr1, hτ1f r hrk]
  have carry_word (base : ℕ) (xs : List ℕ) (hb : M + transArg2BaseReg + 1 < base)
      (hw : WordAt τ base xs) : WordAt τ3 base xs := by
    refine ⟨?_, fun k hkx => ?_⟩
    · rw [hframe (base - 1) (by omega) (by omega) (by omega)]
      exact hw.1
    · rw [hframe (base + k) (by omega) (by omega) (by omega)]
      exact hw.2 k hkx
  have htrans : TransParamFrozen M transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg W T kindBase arg1Base arg2Base
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2) τ3 := by
    refine ⟨?_, carry_word kindBase _ hbase hF.1.1.1.2,
      carry_word arg1Base _ (by omega) hF.1.1.2,
      carry_word arg2Base _ (by omega) hF.1.2⟩
    intro q hq
    simp only [transParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [hframe _ (by omega) (by omega) (by omega)]
      exact hpins (transWReg, W)
        (by simp [p0, initParamPins0, transWReg, initWReg])
    · rw [hframe _ (by omega) (by omega) (by omega)]
      exact hpins (transTReg, T)
        (by simp [p0, initParamPins0, transTReg, initTReg])
    · rw [hτ3f _ (by omega), hτ2f _ (by omega)]
      exact hk
    · rw [hτ3f _ (by omega)]; exact ha1
    · exact ha2
  have hout : WordAt τ3 outBase outIdx := carry_word outBase outIdx houtbase hF.2
  have heval : (loadTransParamsProg d).eval τ = τ3 := by
    simp only [loadTransParamsProg, eval_seq, τ1, τ2, τ3]
  rw [heval]
  refine ⟨⟨htrans, hout⟩, ?_, ?_, rowsWritten_nil τ3 wp, ?_⟩
  · rw [hframe 0 (by simp [transKindBaseReg])
      (by simp [transArg1BaseReg]) (by simp [transArg2BaseReg]), h0]
  · rw [hframe (M + wpJ) (by simp [wpJ, transKindBaseReg])
      (by simp [wpJ, transArg1BaseReg]) (by simp [wpJ, transArg2BaseReg]), hwp]
    simp [rowTableWidth_zero]
  · intro r hr hfree
    apply hframe <;> unfold CtlFree at hfree <;>
      simp [transKindBaseReg, transArg1BaseReg, transArg2BaseReg] at * <;> omega

lemma load_accept_param_io (M Jmax W T kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (outIdx : List ℕ)
    (hreg : acceptOutBaseReg ≤ Jmax)
    (hout : arg2Base + d.table.length + 2 = outBase)
    (hbase : M + acceptOutBaseReg + 1 < outBase) :
    ClauseWriterIO (loadAcceptParamProg d) M Jmax wpJ
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) [] := by
  intro τ wp hF h0 hwp hsep
  set τ1 := (loadAcceptParamProg d).eval τ
  have hframe (r : ℕ) (hr : r ≠ M + acceptOutBaseReg) : τ1 r = τ r := by
    simpa only [τ1, loadAcceptParamProg] using
      ctlAssign_eval_diff acceptOutBaseReg
        (.add (ctlCell transArg2BaseReg) (.const (d.table.length + 2)))
        τ r (by simpa [h0] using hr)
  have hob : τ1 (M + acceptOutBaseReg) = outBase := by
    have ha2 := hF.1.1 (transArg2BaseReg, arg2Base)
      (by simp [transParamPins0])
    have h := ctlAssign_eval_same acceptOutBaseReg
      (.add (ctlCell transArg2BaseReg) (.const (d.table.length + 2))) τ
    calc
      τ1 (M + acceptOutBaseReg) = arg2Base + (d.table.length + 2) := by
        simpa [τ1, loadAcceptParamProg, Expr.eval, ctlCell_eval, h0, ha2] using h
      _ = outBase := by omega
  have hword : WordAt τ1 outBase outIdx := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hframe (outBase - 1) (by omega)]; exact hF.2.1
    · rw [hframe (outBase + k) (by omega)]; exact hF.2.2 k hk
  refine ⟨⟨?_, hword⟩, ?_, ?_, rowsWritten_nil τ1 wp, ?_⟩
  · intro q hq
    simp only [acceptParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [hframe _ (by
        norm_num [acceptWReg, acceptOutBaseReg])]
      exact hF.1.1 (acceptWReg, W)
        (by simp [transParamPins0, acceptWReg, transWReg])
    · rw [hframe _ (by
        norm_num [acceptTReg, acceptOutBaseReg])]
      exact hF.1.1 (acceptTReg, T)
        (by simp [transParamPins0, acceptTReg, transTReg])
    · exact hob
  · rw [hframe 0 (by simp [acceptOutBaseReg]), h0]
  · rw [hframe _ (by
      have hw : wpJ = 1 := rfl
      have ho : acceptOutBaseReg = 23 := rfl
      omega), hwp]
    simp [rowTableWidth_zero]
  · intro r hr hfree
    apply hframe
    unfold CtlFree at hfree
    simp [acceptOutBaseReg] at hreg ⊢
    omega

lemma load_emitter_table_io (M Jmax W T outBase : ℕ) (outIdx : List ℕ)
    (hreg : emTblJ ≤ Jmax)
    (hbase : M + emTblJ + 1 < outBase) :
    ClauseWriterIO (loadEmitterTableProg outIdx) M Jmax wpJ
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg
        W T outBase outIdx)
      (EmitterTableReady M W T outBase (outBase + outIdx.length + 1) outIdx) [] := by
  intro τ wp hF h0 hwp hsep
  set τ1 := (loadEmitterTableProg outIdx).eval τ
  have hframe (r : ℕ) (hr : r ≠ M + emTblJ) : τ1 r = τ r := by
    simpa only [τ1, loadEmitterTableProg] using
      ctlAssign_eval_diff emTblJ
        (.add (ctlCell acceptOutBaseReg) (.const (outIdx.length + 1)))
        τ r (by simpa [h0] using hr)
  have hout := hF.1 (acceptOutBaseReg, outBase) (by simp [acceptParamPins0])
  have hem : τ1 (M + emTblJ) = outBase + outIdx.length + 1 := by
    have h := ctlAssign_eval_same emTblJ
      (.add (ctlCell acceptOutBaseReg) (.const (outIdx.length + 1))) τ
    simpa [τ1, loadEmitterTableProg, Expr.eval, ctlCell_eval, h0, hout,
      Nat.add_assoc] using h
  have hword : WordAt τ1 outBase outIdx := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hframe (outBase - 1) (by omega)]
      exact hF.2.1
    · rw [hframe (outBase + k) (by omega)]
      exact hF.2.2 k hk
  have hfrozen : AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg
      W T outBase outIdx τ1 := by
    refine ⟨?_, hword⟩
    intro q hq
    simp only [acceptParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [hframe _ (by norm_num [acceptWReg, emTblJ])]
      exact hF.1 _ (by simp [acceptParamPins0])
    · rw [hframe _ (by norm_num [acceptTReg, emTblJ])]
      exact hF.1 _ (by simp [acceptParamPins0])
    · rw [hframe _ (by norm_num [acceptOutBaseReg, emTblJ])]
      exact hF.1 _ (by simp [acceptParamPins0])
  refine ⟨⟨hfrozen, hem⟩, ?_, ?_, rowsWritten_nil τ1 wp, ?_⟩
  · rw [hframe 0 (by simp [emTblJ]), h0]
  · rw [hframe (M + wpJ) (by simp [wpJ, emTblJ]), hwp]
    simp [rowTableWidth_zero]
  · intro r hr hfree
    apply hframe
    unfold CtlFree at hfree
    simp [emTblJ] at hreg ⊢
    omega

/-! ## Placement and the five stage contracts -/

structure GeneratorPlacement (M Jmax prefLen prefBase kindBase arg1Base
    arg2Base outBase : ℕ) (d : TableauDescriptor)
    (prefIdx outIdx : List ℕ) : Prop where
  pref_len : prefLen = prefIdx.length
  pref_pos : 1 ≤ prefLen
  pref_base : M + initPrefBaseReg + 1 < prefBase
  kind_eq : prefBase + prefLen + 2 = kindBase
  arg1_eq : kindBase + d.table.length + 2 = arg1Base
  arg2_eq : arg1Base + d.table.length + 2 = arg2Base
  out_eq : arg2Base + d.table.length + 2 = outBase
  out_fit : outBase + outIdx.length ≤ M + Jmax

def generatorWordJ (M base len : ℕ) : ℕ := base + len - M

lemma generator_word_j_spec (M base len : ℕ) (h : M ≤ base + len) :
    M + generatorWordJ M base len = base + len := by
  unfold generatorWordJ
  omega

lemma generator_placement_of_layout (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ)
    (hlen : prefIdx.length = generatorPrefLen N) :
    GeneratorPlacement (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
      (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      (generatorKindBase p time d allowedIdx N)
      (generatorArg1Base p time d allowedIdx N)
      (generatorArg2Base p time d allowedIdx N)
      (generatorOutBase p time d allowedIdx N) d prefIdx outIdx := by
  refine ⟨hlen.symm, by simp [generatorPrefLen], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [generatorPrefLen, generatorPrefBase, generatorKindBase,
      generatorArg1Base, generatorArg2Base, generatorOutBase,
      generatorPrefOffset, generatorKindOffset, generatorArg1Offset,
      generatorArg2Offset, generatorOutOffset, generatorJmax,
      initPrefBaseReg] <;> omega

lemma generator_placement_satisfiable (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (N : ℕ) :
    ∃ prefIdx : List ℕ,
      GeneratorPlacement (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
        (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
        (generatorKindBase p time d allowedIdx N)
        (generatorArg1Base p time d allowedIdx N)
        (generatorArg2Base p time d allowedIdx N)
        (generatorOutBase p time d allowedIdx N) d prefIdx outIdx := by
  refine ⟨List.replicate (generatorPrefLen N) 0, ?_⟩
  exact generator_placement_of_layout p time d allowedIdx outIdx _ N (by simp)

/-- Carry the generated table columns from the staged word extent to the full generator extent. -/
lemma generator_placement_carry_columns
    (prog : Program) (M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hbase : ClauseWriterIO prog M (generatorWordJ M prefBase prefIdx.length) wpJ
      Entry Exit cs) :
    ClauseWriterIO prog M Jmax wpJ
      (fun τ => (((Entry τ ∧ WordAt τ kindBase (d.table.map transKind)) ∧
        WordAt τ arg1Base (d.table.map transArg1)) ∧
        WordAt τ arg2Base (d.table.map transArg2)) ∧
        WordAt τ outBase outIdx)
      (fun τ => (((Exit τ ∧ WordAt τ kindBase (d.table.map transKind)) ∧
        WordAt τ arg1Base (d.table.map transArg1)) ∧
        WordAt τ arg2Base (d.table.map transArg2)) ∧
        WordAt τ outBase outIdx) cs := by
  let Jp := generatorWordJ M prefBase prefIdx.length
  let Jk := generatorWordJ M kindBase d.table.length
  let J1 := generatorWordJ M arg1Base d.table.length
  let J2 := generatorWordJ M arg2Base d.table.length
  have hMp : M ≤ prefBase + prefIdx.length := by
    have hb := h.pref_base
    omega
  have hMk : M ≤ kindBase + d.table.length := by
    have hb := h.pref_base
    have hk := h.kind_eq
    omega
  have hM1 : M ≤ arg1Base + d.table.length := by
    have hb := h.pref_base
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    omega
  have hM2 : M ≤ arg2Base + d.table.length := by
    have hb := h.pref_base
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    omega
  have eJp : M + Jp = prefBase + prefIdx.length :=
    generator_word_j_spec M prefBase prefIdx.length hMp
  have eJk : M + Jk = kindBase + d.table.length :=
    generator_word_j_spec M kindBase d.table.length hMk
  have eJ1 : M + J1 = arg1Base + d.table.length :=
    generator_word_j_spec M arg1Base d.table.length hM1
  have eJ2 : M + J2 = arg2Base + d.table.length :=
    generator_word_j_spec M arg2Base d.table.length hM2
  have hcols := clauseWriterIO_carry3_widen _ M Jp Jk J1 J2 _ _
    kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
    arg2Base (d.table.map transArg2) _
    (by rw [eJp]; have hlen := h.pref_len; have he := h.kind_eq; omega)
    (by simpa using eJk.symm.le)
    (by rw [eJk]; have he := h.arg1_eq; omega)
    (by simpa using eJ1.symm.le)
    (by rw [eJ1]; have he := h.arg2_eq; omega)
    (by simpa using eJ2.symm.le) hbase
  exact clauseWriterIO_carry_widen _ M J2 Jmax _ _ outBase outIdx _
    (by rw [eJ2]; have he := h.out_eq; omega) h.out_fit hcols

/-- Carry the staged prefix and generated table columns to the full generator extent. -/
lemma generator_placement_carry_table
    (prog : Program) (M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hbase : ClauseWriterIO prog M initPrefBaseReg wpJ Entry Exit cs) :
    ClauseWriterIO prog M Jmax wpJ
      (fun τ => (((((Entry τ ∧ WordAt τ prefBase prefIdx) ∧
        WordAt τ kindBase (d.table.map transKind)) ∧
        WordAt τ arg1Base (d.table.map transArg1)) ∧
        WordAt τ arg2Base (d.table.map transArg2)) ∧
        WordAt τ outBase outIdx))
      (fun τ => (((((Exit τ ∧ WordAt τ prefBase prefIdx) ∧
        WordAt τ kindBase (d.table.map transKind)) ∧
        WordAt τ arg1Base (d.table.map transArg1)) ∧
        WordAt τ arg2Base (d.table.map transArg2)) ∧
        WordAt τ outBase outIdx)) cs := by
  let Jp := generatorWordJ M prefBase prefIdx.length
  have hMp : M ≤ prefBase + prefIdx.length := by
    have hb := h.pref_base
    omega
  have eJp : M + Jp = prefBase + prefIdx.length :=
    generator_word_j_spec M prefBase prefIdx.length hMp
  have hpref := clauseWriterIO_carry_widen _ M initPrefBaseReg Jp _ _
    prefBase prefIdx _ h.pref_base (by rw [eJp]) hbase
  exact generator_placement_carry_columns _ M Jmax prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx _ _ cs h hpref

/-- Carry the generated output word from the transition extent to the full extent. -/
lemma generator_placement_carry_out
    (prog : Program) (M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hbase : ClauseWriterIO prog M (generatorWordJ M arg2Base d.table.length) wpJ
      Entry Exit cs) :
    ClauseWriterIO prog M Jmax wpJ
      (fun τ => Entry τ ∧ WordAt τ outBase outIdx)
      (fun τ => Exit τ ∧ WordAt τ outBase outIdx) cs := by
  let J2 := generatorWordJ M arg2Base d.table.length
  have hM2 : M ≤ arg2Base + d.table.length := by
    have hb := h.pref_base
    have hk := h.kind_eq
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    omega
  have eJ2 : M + J2 = arg2Base + d.table.length :=
    generator_word_j_spec M arg2Base d.table.length hM2
  exact clauseWriterIO_carry_widen _ M J2 Jmax _ _ outBase outIdx _
    (by rw [eJ2]; have he := h.out_eq; omega) h.out_fit hbase

lemma uniqueness_stage_io_param (M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase : ℕ) (d : TableauDescriptor)
    (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (uniquenessStageProgParam d) M Jmax wpJ
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (execUniquenessClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numStates) (List.range d.numLetters) W T) := by
  let pins := [(uniquenessWReg, W), (uniquenessTReg, T)]
  let extra := [(initFreeLenReg, freeLen), (initPrefLenReg, prefLen),
    (initPrefBaseReg, prefBase)]
  have h0 : ClauseWriterIO (uniquenessStageProgParam d) M uniquenessParamJmax wpJ
      (PinsHold M pins) (PinsHold M pins)
      (execUniquenessClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numStates) (List.range d.numLetters) W T) := by
    exact clauseWriterIO_of_writer _ M uniquenessParamJmax wpJ _ _
      (uniquenessFamilyProgParam_writer_param M uniquenessParamJmax
        (d.numStates + 1) W (d.numLetters + 1) d.numStates d.numLetters T
        uniquenessWReg uniquenessTReg uniqueness_param_fixed_placement)
  have hp : ClauseWriterIO (uniquenessStageProgParam d) M initPrefBaseReg wpJ
      (PinsHold M (pins ++ extra)) (PinsHold M (pins ++ extra)) _ :=
    clauseWriterIO_pins_widen _ M uniquenessParamJmax initPrefBaseReg pins extra _
      (by simp [uniquenessParamJmax, initPrefBaseReg])
      (by
        intro q hq
        simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;>
          simp [uniquenessParamJmax, initFreeLenReg, initPrefLenReg,
            initPrefBaseReg])
      (by
        intro q hq
        simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;>
          simp [initFreeLenReg, initPrefLenReg, initPrefBaseReg]) h0
  have hp' : ClauseWriterIO (uniquenessStageProgParam d) M initPrefBaseReg wpJ
      (PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg
        initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase))
      (PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg
        initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase))
      (execUniquenessClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numStates) (List.range d.numLetters) W T) := by
    simpa [pins, extra, initParamPins0, uniquenessWReg, uniquenessTReg,
      initWReg, initTReg] using hp
  have hall := generator_placement_carry_table
    (uniquenessStageProgParam d) M Jmax prefLen prefBase kindBase arg1Base
    arg2Base outBase d prefIdx outIdx _ _ _ h hp'
  change ClauseWriterIO (uniquenessStageProgParam d) M Jmax wpJ
    (fun τ => ((((PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase) τ ∧
      WordAt τ prefBase prefIdx) ∧ WordAt τ kindBase (d.table.map transKind)) ∧
      WordAt τ arg1Base (d.table.map transArg1)) ∧
      WordAt τ arg2Base (d.table.map transArg2)) ∧ WordAt τ outBase outIdx)
    (fun τ => ((((PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase) τ ∧
      WordAt τ prefBase prefIdx) ∧ WordAt τ kindBase (d.table.map transKind)) ∧
      WordAt τ arg1Base (d.table.map transArg1)) ∧
      WordAt τ arg2Base (d.table.map transArg2)) ∧ WordAt τ outBase outIdx) _
  exact hall

lemma init_stage_io_param (M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (initStageProgParam d allowedIdx) M Jmax wpJ
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (descBoundedPrefixInitClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx W T) := by
  let Jp := generatorWordJ M prefBase prefIdx.length
  have hMp : M ≤ prefBase + prefIdx.length := by
    have := h.pref_base
    omega
  have eJp : M + Jp = prefBase + prefIdx.length :=
    generator_word_j_spec M prefBase prefIdx.length hMp
  have hJp19 : initPrefBaseReg ≤ Jp := by
    have hb := h.pref_base
    have hp : initPrefBaseReg = 19 := rfl
    omega
  have hplace : InitParamPlacement Jp initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg := by
    exact ⟨by have := hJp19; simp [ctlJmax, initPrefBaseReg] at *; omega,
      by simp [initWReg], by simp [initWReg, initTReg],
      by simp [initTReg, initFreeLenReg],
      by simp [initFreeLenReg, initPrefLenReg],
      by simp [initPrefLenReg, initPrefBaseReg], hJp19⟩
  have hraw := initFamilyProgParam_writer_param M Jp (d.numStates + 1) W
    (d.numLetters + 1) T prefBase prefLen freeLen d prefIdx allowedIdx
    initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg
    hplace h.pref_len h.pref_base (by rw [eJp])
  have hdrop := clauseWriterIO_weaken_exit _ M Jp wpJ
    (InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg W T freeLen prefLen prefBase prefIdx)
    (InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg W T freeLen prefLen prefBase prefIdx)
    (PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase)) _
    (fun τ hF => hF.1) (clauseWriterIO_of_writer _ M Jp wpJ _ _ hraw)
  have hinit := generator_placement_carry_columns
    (initFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d allowedIdx
      initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg)
    M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase d prefIdx outIdx
    _ _ _ h hdrop
  have hkindAbove : M + transArg2BaseReg + 1 < kindBase := by
    have hb := h.pref_base
    have hk := h.kind_eq
    have hp := h.pref_pos
    simp [transArg2BaseReg, initPrefBaseReg] at hb ⊢
    omega
  have houtAbove : M + transArg2BaseReg + 1 < outBase := by
    have hk := hkindAbove
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    have ho := h.out_eq
    omega
  have hregJ : transArg2BaseReg ≤ Jmax := by
    have hf := h.out_fit
    have ho := houtAbove
    simp [transArg2BaseReg] at *
    omega
  have hload := load_trans_params_io M Jmax W T freeLen prefLen prefBase
    kindBase arg1Base arg2Base outBase d outIdx
    hregJ h.kind_eq h.arg1_eq h.arg2_eq hkindAbove houtAbove
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hinit hload
  change ClauseWriterIO (initStageProgParam d allowedIdx) M Jmax wpJ
    (fun τ => (((InitParamFrozen M initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg W T freeLen prefLen prefBase prefIdx τ ∧
      WordAt τ kindBase (d.table.map transKind)) ∧
      WordAt τ arg1Base (d.table.map transArg1)) ∧
      WordAt τ arg2Base (d.table.map transArg2)) ∧ WordAt τ outBase outIdx)
    (TransWithOutFrozen M W T kindBase arg1Base arg2Base
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
      outBase outIdx) _
  simpa [initStageProgParam] using hseq

lemma trans_stage_io_param (M Jmax W T prefLen prefBase kindBase arg1Base
    arg2Base outBase : ℕ) (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (transStageProgParam d) M Jmax wpJ
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
      (transClausesTripleFamily
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        d.numStates W d.numLetters T (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2)) := by
  let J2 := generatorWordJ M arg2Base d.table.length
  have hM2 : M ≤ arg2Base + d.table.length := by
    have hb := h.pref_base; have hk := h.kind_eq; have h1 := h.arg1_eq
    have h2 := h.arg2_eq; omega
  have eJ2 : M + J2 = arg2Base + d.table.length :=
    generator_word_j_spec M arg2Base d.table.length hM2
  have hkindAbove : M + transArg2BaseReg + 1 < kindBase := by
    have hb := h.pref_base; have hk := h.kind_eq; have hp := h.pref_pos
    simp [transArg2BaseReg, initPrefBaseReg] at hb ⊢
    omega
  have hJ2reg : transArg2BaseReg ≤ J2 := by
    have hk := hkindAbove
    have h1 := h.arg1_eq
    have h2 := h.arg2_eq
    have he := eJ2
    simp [transArg2BaseReg] at hk ⊢
    omega
  have hp : TransParamPlacement J2 transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg := by
    exact ⟨by have := hJ2reg; simp [ctlJmax, transArg2BaseReg] at *; omega,
      by simp [transWReg], by simp [transWReg, transTReg],
      by simp [transTReg, transKindBaseReg],
      by simp [transKindBaseReg, transArg1BaseReg],
      by simp [transArg1BaseReg, transArg2BaseReg], hJ2reg⟩
  have ht : TransParamTablePlacement M J2 transArg2BaseReg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length := by
    refine ⟨hkindAbove, ?_, ?_, ?_⟩
    · simpa using Nat.lt_of_lt_of_le (by have := h.arg1_eq; omega)
        (Nat.le_refl arg1Base)
    · simpa using Nat.lt_of_lt_of_le (by have := h.arg2_eq; omega)
        (Nat.le_refl arg2Base)
    · simpa using eJ2.symm.le
  have hraw := transFamilyProgParam_writer_param M J2 (d.numStates + 1) W
    (d.numLetters + 1) d.numStates d.numLetters T d kindBase arg1Base
    arg2Base transWReg transTReg transKindBaseReg transArg1BaseReg
    transArg2BaseReg hp ht
  have htrans := generator_placement_carry_out
    (transFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
      d.numStates d.numLetters d transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg)
    M Jmax prefLen prefBase kindBase arg1Base arg2Base outBase d prefIdx outIdx
    _ _ _ h
    (clauseWriterIO_of_writer _ M J2 wpJ _ _ hraw)
  have houtAbove : M + acceptOutBaseReg + 1 < outBase := by
    have hk := hkindAbove; have h1 := h.arg1_eq; have h2 := h.arg2_eq
    have ho := h.out_eq
    simp [acceptOutBaseReg, transArg2BaseReg] at *
    omega
  have hregJ : acceptOutBaseReg ≤ Jmax := by
    have hf := h.out_fit
    have ho := houtAbove
    simp [acceptOutBaseReg] at *
    omega
  have hload := load_accept_param_io M Jmax W T kindBase arg1Base arg2Base
    outBase d outIdx hregJ h.out_eq houtAbove
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ htrans hload
  change ClauseWriterIO (transStageProgParam d) M Jmax wpJ
    (fun τ => TransParamFrozen M transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg W T kindBase arg1Base arg2Base
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2) τ ∧
      WordAt τ outBase outIdx)
    (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) _
  simpa [transStageProgParam] using hseq

lemma persist_stage_io_param (M Jmax W T prefLen prefBase kindBase arg1Base
    arg2Base outBase : ℕ) (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (persistStageProgParam d) M Jmax wpJ
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
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
      (PinsHold M (acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg
        W T outBase))
      (PinsHold M (acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg
        W T outBase))
      (execPersistClausesAt
        (denseLayout (d.numStates + 1) W (d.numLetters + 1))
        (List.range d.numLetters) W T) := by
    simpa [pins, extra, acceptParamPins0, persistWReg, persistTReg,
      acceptWReg, acceptTReg] using hp
  have houtAbove : M + acceptOutBaseReg + 1 < outBase := by
    have hb := h.pref_base; have hp := h.pref_pos; have hk := h.kind_eq
    have h1 := h.arg1_eq; have h2 := h.arg2_eq; have ho := h.out_eq
    simp [acceptOutBaseReg, initPrefBaseReg] at hb ⊢
    omega
  have hall := clauseWriterIO_carry_widen _ M acceptOutBaseReg Jmax _ _
    outBase outIdx _ houtAbove h.out_fit hp'
  change ClauseWriterIO (persistStageProgParam d) M Jmax wpJ
    (fun τ => PinsHold M (acceptParamPins0 acceptWReg acceptTReg
      acceptOutBaseReg W T outBase) τ ∧ WordAt τ outBase outIdx)
    (fun τ => PinsHold M (acceptParamPins0 acceptWReg acceptTReg
      acceptOutBaseReg W T outBase) τ ∧ WordAt τ outBase outIdx) _
  exact hall

lemma accept_stage_io_param (M Jmax W T prefLen prefBase kindBase arg1Base
    arg2Base outBase : ℕ) (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (acceptStageProgParam d outIdx) M Jmax wpJ
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
      (EmitterTableReady M W T outBase (outBase + outIdx.length + 1) outIdx)
      (descAcceptClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d outIdx W T) := by
  have houtAbove : M + acceptOutBaseReg + 1 < outBase := by
    have hb := h.pref_base; have hp := h.pref_pos; have hk := h.kind_eq
    have h1 := h.arg1_eq; have h2 := h.arg2_eq; have ho := h.out_eq
    simp [acceptOutBaseReg, initPrefBaseReg] at hb ⊢
    omega
  have hregJ : acceptOutBaseReg ≤ Jmax := by
    have hf := h.out_fit
    have ho := houtAbove
    simp [acceptOutBaseReg] at *
    omega
  have hp : AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg :=
    ⟨by have := hregJ; simp [ctlJmax, acceptOutBaseReg] at *; omega,
      by simp [acceptWReg], by simp [acceptWReg, acceptTReg],
      by simp [acceptTReg, acceptOutBaseReg], hregJ⟩
  have hA := clauseWriterIO_of_writer _ M Jmax wpJ _ _
    (acceptFamilyProgParam_writer_param M Jmax (d.numStates + 1) W
      (d.numLetters + 1) T outBase d outIdx acceptWReg acceptTReg
      acceptOutBaseReg hp houtAbove h.out_fit)
  have hE := load_emitter_table_io M Jmax W T outBase outIdx
    (by have := hregJ; simp [acceptOutBaseReg, emTblJ] at *; omega)
    (by have := houtAbove; simp [acceptOutBaseReg, emTblJ] at *; omega)
  simpa only [acceptStageProgParam, List.append_nil] using
    clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hA hE

lemma tableWriterProgParam_io_param (M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) :
    ClauseWriterIO (tableWriterProgParam d allowedIdx outIdx) M Jmax wpJ
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (EmitterTableReady M W T outBase (outBase + outIdx.length + 1) outIdx)
      (descTableauCNF
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx outIdx W T).clauses := by
  have hU := uniqueness_stage_io_param M Jmax W T freeLen prefLen prefBase
    kindBase arg1Base arg2Base outBase d prefIdx outIdx h
  have hI := init_stage_io_param M Jmax W T freeLen prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx allowedIdx outIdx h
  have hT := trans_stage_io_param M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hP := persist_stage_io_param M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hA := accept_stage_io_param M Jmax W T prefLen prefBase kindBase
    arg1Base arg2Base outBase d prefIdx outIdx h
  have hUI := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hU hI
  have hUIT := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUI hT
  have hUITP := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUIT hP
  have hall := clauseWriterIO_seq _ _ M Jmax wpJ _ _ _ _ _ hUITP hA
  have hgen : ClauseWriterIO (tableWriterProgParam d allowedIdx outIdx)
      M Jmax wpJ
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (EmitterTableReady M W T outBase (outBase + outIdx.length + 1) outIdx)
      (tableWriterClausesGen (d.numStates + 1) W (d.numLetters + 1)
        d.numStates d.numLetters T d prefIdx freeLen allowedIdx outIdx) := by
    simpa [tableWriterProgParam, tableWriterClausesGen] using hall
  rw [table_writer_clauses_gen_eq_desc] at hgen
  exact hgen

lemma table_writer_param_gives_clause_table_at
    (M Jmax W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx) (τ : Store) (tableBase : ℕ)
    (hF : GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
      (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) outBase outIdx τ)
    (h0 : τ 0 = M) (hwp : τ (M + wpJ) = tableBase)
    (hsep : M + Jmax < tableBase) :
    ClauseTableAt ((tableWriterProgParam d allowedIdx outIdx).eval τ) tableBase
      (descTableauCNF
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx outIdx W T) :=
  clauseTableAt_of_clauseWriterIO _ M Jmax _ _ _ τ tableBase
    (tableWriterProgParam_io_param M Jmax W T freeLen prefLen prefBase kindBase
      arg1Base arg2Base outBase d prefIdx allowedIdx outIdx h) hF h0 hwp hsep

/-! ## Correctness of the dynamic setup layer -/

lemma generator_pref_len_e_reg0 : Reg0Expr generatorPrefLenE :=
  reg0Expr_add _ _
    (reg0Expr_mul _ _ (reg0Expr_const _) reg0Expr_reg0) (reg0Expr_const _)

lemma generator_pref_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    Reg0Expr (generatorPrefBaseE p time d allowedIdx) :=
  reg0Expr_add _ _ (setupME_reg0 p time d allowedIdx) (reg0Expr_const _)

lemma generator_kind_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    Reg0Expr (generatorKindBaseE p time d allowedIdx) :=
  reg0Expr_add _ _
    (reg0Expr_add _ _ (generator_pref_base_e_reg0 p time d allowedIdx)
      generator_pref_len_e_reg0)
    (reg0Expr_const _)

lemma generator_arg1_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    Reg0Expr (generatorArg1BaseE p time d allowedIdx) :=
  reg0Expr_add _ _ (generator_kind_base_e_reg0 p time d allowedIdx)
    (reg0Expr_const _)

lemma generator_arg2_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    Reg0Expr (generatorArg2BaseE p time d allowedIdx) :=
  reg0Expr_add _ _ (generator_arg1_base_e_reg0 p time d allowedIdx)
    (reg0Expr_const _)

lemma generator_out_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) :
    Reg0Expr (generatorOutBaseE p time d allowedIdx) :=
  reg0Expr_add _ _ (generator_arg2_base_e_reg0 p time d allowedIdx)
    (reg0Expr_const _)

lemma generator_table_base_e_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    Reg0Expr (generatorTableBaseE p time d allowedIdx outIdx) :=
  reg0Expr_add _ _ (generator_out_base_e_reg0 p time d allowedIdx)
    (reg0Expr_const _)

lemma generator_layout_pairs_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ∀ q ∈ generatorLayoutPairs p time d allowedIdx outIdx, Reg0Expr q.2 := by
  intro q hq
  simp only [generatorLayoutPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact generator_pref_base_e_reg0 p time d allowedIdx
  · exact generator_kind_base_e_reg0 p time d allowedIdx
  · exact generator_arg1_base_e_reg0 p time d allowedIdx
  · exact generator_arg2_base_e_reg0 p time d allowedIdx
  · exact generator_out_base_e_reg0 p time d allowedIdx
  · exact generator_table_base_e_reg0 p time d allowedIdx outIdx
  · exact generator_table_base_e_reg0 p time d allowedIdx outIdx
  · exact generator_table_base_e_reg0 p time d allowedIdx outIdx

lemma generator_layout_pairs_nodup (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    (generatorLayoutPairs p time d allowedIdx outIdx).map Prod.fst |>.Nodup := by
  simp [generatorLayoutPairs, initPrefBaseReg, transKindBaseReg,
    transArg1BaseReg, transArg2BaseReg, acceptOutBaseReg, wpJ, emTblJ,
    generatorTableBaseReg]

lemma generator_layout_pairs_pos (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ∀ j ∈ (generatorLayoutPairs p time d allowedIdx outIdx).map Prod.fst, 1 ≤ j := by
  intro j hj
  simp only [generatorLayoutPairs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg,
      transArg2BaseReg, acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]

lemma generator_pref_len_e_eval (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    generatorPrefLenE.eval σ = generatorPrefLen N := by
  simp [generatorPrefLenE, generatorPrefLen, Expr.eval, h0]

lemma generator_pref_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorPrefBaseE p time d allowedIdx).eval σ
      = generatorPrefBase p time d allowedIdx N := by
  simp [generatorPrefBaseE, generatorPrefBase, Expr.eval,
    setupME_eval p time d allowedIdx σ N h0]

lemma generator_kind_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorKindBaseE p time d allowedIdx).eval σ
      = generatorKindBase p time d allowedIdx N := by
  simp [generatorKindBaseE, generatorKindBase, generatorKindOffset,
    generatorPrefBaseE, generatorPrefLenE, generatorPrefLen,
    generatorPrefOffset, Expr.eval, setupME_eval p time d allowedIdx σ N h0, h0]
  omega

lemma generator_arg1_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorArg1BaseE p time d allowedIdx).eval σ
      = generatorArg1Base p time d allowedIdx N := by
  simp [generatorArg1BaseE, generatorArg1Base, generatorArg1Offset,
    generatorKindBaseE, generatorKindOffset, generatorPrefBaseE,
    generatorPrefLenE, generatorPrefLen, generatorPrefOffset, Expr.eval,
    setupME_eval p time d allowedIdx σ N h0, h0]
  omega

lemma generator_arg2_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorArg2BaseE p time d allowedIdx).eval σ
      = generatorArg2Base p time d allowedIdx N := by
  simp [generatorArg2BaseE, generatorArg2Base, generatorArg2Offset,
    generatorArg1BaseE, generatorArg1Offset, generatorKindBaseE,
    generatorKindOffset, generatorPrefBaseE, generatorPrefLenE,
    generatorPrefLen, generatorPrefOffset, Expr.eval,
    setupME_eval p time d allowedIdx σ N h0, h0]
  omega

lemma generator_out_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorOutBaseE p time d allowedIdx).eval σ
      = generatorOutBase p time d allowedIdx N := by
  simp [generatorOutBaseE, generatorOutBase, generatorOutOffset,
    generatorArg2BaseE, generatorArg2Offset, generatorArg1BaseE,
    generatorArg1Offset, generatorKindBaseE, generatorKindOffset,
    generatorPrefBaseE, generatorPrefLenE, generatorPrefLen,
    generatorPrefOffset, Expr.eval, setupME_eval p time d allowedIdx σ N h0, h0]
  omega

lemma generator_table_base_e_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (generatorTableBaseE p time d allowedIdx outIdx).eval σ =
      generatorTableBase p time d allowedIdx outIdx N := by
  rw [generatorTableBaseE]
  simp only [Expr.eval, generator_out_base_e_eval p time d allowedIdx σ N h0]
  simp [generatorTableBase, generatorJmax, generatorOutBase,
    generatorOutOffset]
  omega

lemma paramSetupWrites_avoidsAbove_zero (mE : Expr) (pairs : List (ℕ × Expr))
    (hpos : ∀ j ∈ pairs.map Prod.fst, 1 ≤ j) :
    (paramSetupWrites mE pairs).AvoidsAbove (fun r => r = 0) 1 := by
  induction pairs with
  | nil => simp [paramSetupWrites, Program.AvoidsAbove]
  | cons q rest ih =>
      have hq : 1 ≤ q.1 := hpos q.1 (by simp)
      have hrest : ∀ j ∈ rest.map Prod.fst, 1 ≤ j := by
        intro j hj
        exact hpos j (by simp [hj])
      simp only [paramSetupWrites, Program.AvoidsAbove, paramSetupAssign]
      constructor
      · simp only [Expr.lb]
        omega
      · exact ih hrest

lemma setup_prog_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) :
    (setupProg p time d allowedIdx).eval σ 0 = σ 0 := by
  exact (paramSetupWrites_avoidsAbove_zero (setupME p time d allowedIdx)
    (setupPairs p time d allowedIdx) (setupPairs_pos p time d allowedIdx)).eval_frame
    σ rfl (by decide)

lemma generator_layout_prog_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) :
    (generatorLayoutProg p time d allowedIdx outIdx).eval σ 0 = σ 0 := by
  exact (paramSetupWrites_avoidsAbove_zero (setupME p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx)
    (generator_layout_pairs_pos p time d allowedIdx outIdx)).eval_frame σ rfl (by decide)

lemma generator_setup_prog_zero (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) :
    (generatorSetupProg p time d allowedIdx outIdx).eval σ 0 = σ 0 := by
  simp only [generatorSetupProg, eval_seq]
  rw [generator_layout_prog_zero, setup_prog_zero]

lemma generator_layout_prog_pins (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (τ σ : Store) (N : ℕ)
    (hτ0 : τ 0 = σ 0) (hσ0 : σ 0 = N) :
    ∀ q ∈ (generatorLayoutPairs p time d allowedIdx outIdx).map
        (fun q : ℕ × Expr => (q.1, q.2.eval σ)),
      (generatorLayoutProg p time d allowedIdx outIdx).eval τ
        (setupM p time d allowedIdx N + q.1) = q.2 :=
  paramSetupWrites_pins (setupME p time d allowedIdx)
    (setupME_reg0 p time d allowedIdx) (setupM p time d allowedIdx N)
    (generatorLayoutPairs p time d allowedIdx outIdx) τ σ hτ0
    (setupME_eval p time d allowedIdx σ N hσ0)
    (generator_layout_pairs_reg0 p time d allowedIdx outIdx)
    (generator_layout_pairs_nodup p time d allowedIdx outIdx)
    (generator_layout_pairs_pos p time d allowedIdx outIdx)

lemma generator_layout_prog_mid_frame (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (τ : Store) (M j : ℕ)
    (hM : (setupME p time d allowedIdx).eval τ = M) (hj1 : 15 ≤ j) (hj2 : j ≤ 18) :
    (generatorLayoutProg p time d allowedIdx outIdx).eval τ (M + j) = τ (M + j) := by
  apply paramSetupWrites_frame (setupME p time d allowedIdx)
    (setupME_reg0 p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx) τ (M + j)
    (generator_layout_pairs_pos p time d allowedIdx outIdx)
  intro k hk
  rw [hM]
  simp only [generatorLayoutPairs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg,
      transArg2BaseReg, acceptOutBaseReg, wpJ, emTblJ,
      generatorTableBaseReg] at * <;> omega

def GeneratorWordsAt (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ) (σ : Store) : Prop :=
  ((((WordAt σ (generatorPrefBase p time d allowedIdx N) prefIdx ∧
      WordAt σ (generatorKindBase p time d allowedIdx N) (d.table.map transKind)) ∧
      WordAt σ (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)) ∧
      WordAt σ (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)) ∧
      WordAt σ (generatorOutBase p time d allowedIdx N) outIdx)

noncomputable def generatorScalarPins (p time : Polynomial ℕ) (N : ℕ) :
    List (ℕ × ℕ) :=
  [(persistWReg, (cookWindowPoly p time).eval N),
   (persistTReg, (timePoly p time).eval N),
   (initFreeLenReg, p.eval N),
   (initPrefLenReg, generatorPrefLen N)]

noncomputable def generatorLayoutPins (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (N : ℕ) : List (ℕ × ℕ) :=
  [(initPrefBaseReg, generatorPrefBase p time d allowedIdx N),
   (transKindBaseReg, generatorKindBase p time d allowedIdx N),
   (transArg1BaseReg, generatorArg1Base p time d allowedIdx N),
   (transArg2BaseReg, generatorArg2Base p time d allowedIdx N),
   (acceptOutBaseReg, generatorOutBase p time d allowedIdx N),
   (wpJ, generatorTableBase p time d allowedIdx outIdx N),
   (emTblJ, generatorTableBase p time d allowedIdx outIdx N),
   (generatorTableBaseReg, generatorTableBase p time d allowedIdx outIdx N)]

lemma setup_prog_scalar_pins (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    PinsHold (setupM p time d allowedIdx N) (generatorScalarPins p time N)
      ((setupProg p time d allowedIdx).eval σ) := by
  intro q hq
  simp only [generatorScalarPins, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · have h := setupProg_pins p time d allowedIdx σ N h0
      (persistWReg,
        (hornerExpr (coeffList (cookWindowPoly p time)) (Expr.reg 0)).eval σ)
      (by simp [setupPairs])
    simpa only [hornerExpr_coeffList_eval, Expr.eval, h0] using h
  · have h := setupProg_pins p time d allowedIdx σ N h0
      (persistTReg,
        (hornerExpr (coeffList (timePoly p time)) (Expr.reg 0)).eval σ)
      (by simp [setupPairs])
    simpa only [hornerExpr_coeffList_eval, Expr.eval, h0] using h
  · have h := setupProg_pins p time d allowedIdx σ N h0
      (initFreeLenReg, (hornerExpr (coeffList p) (Expr.reg 0)).eval σ)
      (by simp [setupPairs])
    simpa only [hornerExpr_coeffList_eval, Expr.eval, h0] using h
  · have h := setupProg_pins p time d allowedIdx σ N h0
      (initPrefLenReg,
        (Expr.add (Expr.mul (Expr.const 2) (Expr.reg 0)) (Expr.const 1)).eval σ)
      (by simp [setupPairs])
    simpa [Expr.eval, h0, generatorPrefLen] using h

lemma generator_setup_prog_scalar_pins (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) :
    PinsHold (setupM p time d allowedIdx N) (generatorScalarPins p time N)
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ) := by
  let τ := (setupProg p time d allowedIdx).eval σ
  have hτ0 : τ 0 = N := by
    change (setupProg p time d allowedIdx).eval σ 0 = N
    rw [setup_prog_zero, h0]
  have hM : (setupME p time d allowedIdx).eval τ = setupM p time d allowedIdx N :=
    setupME_eval p time d allowedIdx τ N hτ0
  have hpins := setup_prog_scalar_pins p time d allowedIdx σ N h0
  intro q hq
  simp only [generatorScalarPins, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · rw [generatorSetupProg, eval_seq,
      generator_layout_prog_mid_frame p time d allowedIdx outIdx τ _ persistWReg hM
        (by simp [persistWReg]) (by simp [persistWReg])]
    exact hpins
      (persistWReg, (cookWindowPoly p time).eval N)
      (by simp [generatorScalarPins])
  · rw [generatorSetupProg, eval_seq,
      generator_layout_prog_mid_frame p time d allowedIdx outIdx τ _ persistTReg hM
        (by simp [persistTReg]) (by simp [persistTReg])]
    exact hpins
      (persistTReg, (timePoly p time).eval N)
      (by simp [generatorScalarPins])
  · rw [generatorSetupProg, eval_seq,
      generator_layout_prog_mid_frame p time d allowedIdx outIdx τ _ initFreeLenReg hM
        (by simp [initFreeLenReg]) (by simp [initFreeLenReg])]
    exact hpins (initFreeLenReg, p.eval N) (by simp [generatorScalarPins])
  · rw [generatorSetupProg, eval_seq,
      generator_layout_prog_mid_frame p time d allowedIdx outIdx τ _ initPrefLenReg hM
        (by simp [initPrefLenReg]) (by simp [initPrefLenReg])]
    exact hpins (initPrefLenReg, generatorPrefLen N)
      (by simp [generatorScalarPins])

lemma generator_setup_prog_layout_pins (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) :
    PinsHold (setupM p time d allowedIdx N)
      (generatorLayoutPins p time d allowedIdx outIdx N)
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ) := by
  let τ := (setupProg p time d allowedIdx).eval σ
  have hτ0 : τ 0 = σ 0 := by
    change (setupProg p time d allowedIdx).eval σ 0 = σ 0
    rw [setup_prog_zero]
  have hp := generator_layout_prog_pins p time d allowedIdx outIdx τ σ N hτ0 h0
  intro q hq
  simp only [generatorLayoutPins, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := hp (initPrefBaseReg, (generatorPrefBaseE p time d allowedIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_pref_base_e_eval p time d allowedIdx σ N h0] using h
  · have h := hp (transKindBaseReg, (generatorKindBaseE p time d allowedIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_kind_base_e_eval p time d allowedIdx σ N h0] using h
  · have h := hp (transArg1BaseReg, (generatorArg1BaseE p time d allowedIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_arg1_base_e_eval p time d allowedIdx σ N h0] using h
  · have h := hp (transArg2BaseReg, (generatorArg2BaseE p time d allowedIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_arg2_base_e_eval p time d allowedIdx σ N h0] using h
  · have h := hp (acceptOutBaseReg, (generatorOutBaseE p time d allowedIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_out_base_e_eval p time d allowedIdx σ N h0] using h
  · have h := hp (wpJ, (generatorTableBaseE p time d allowedIdx outIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_table_base_e_eval p time d allowedIdx outIdx σ N h0] using h
  · have h := hp (emTblJ, (generatorTableBaseE p time d allowedIdx outIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_table_base_e_eval p time d allowedIdx outIdx σ N h0] using h
  · have h := hp
      (generatorTableBaseReg,
        (generatorTableBaseE p time d allowedIdx outIdx).eval σ)
      (by simp [generatorLayoutPairs])
    simpa [generatorSetupProg, eval_seq, τ,
      generator_table_base_e_eval p time d allowedIdx outIdx σ N h0] using h

lemma setup_pairs_le_generator_table_reg (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ∀ j ∈ (setupPairs p time d allowedIdx).map Prod.fst, j ≤ generatorTableBaseReg := by
  intro j hj
  simp only [setupPairs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [persistWReg, persistTReg, initFreeLenReg, initPrefLenReg,
      initPrefBaseReg, transKindBaseReg, transArg1BaseReg,
      transArg2BaseReg, acceptOutBaseReg, generatorTableBaseReg]

lemma generator_layout_pairs_le_table_reg (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) :
    ∀ j ∈ (generatorLayoutPairs p time d allowedIdx outIdx).map Prod.fst,
      j ≤ generatorTableBaseReg := by
  intro j hj
  simp only [generatorLayoutPairs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg,
      transArg2BaseReg, acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]

lemma setup_prog_frame_above (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (N r : ℕ)
    (h0 : σ 0 = N) (hr : setupM p time d allowedIdx N + generatorTableBaseReg < r) :
    (setupProg p time d allowedIdx).eval σ r = σ r := by
  apply paramSetupWrites_frame (setupME p time d allowedIdx)
    (setupME_reg0 p time d allowedIdx)
    (setupPairs p time d allowedIdx) σ r (setupPairs_pos p time d allowedIdx)
  intro j hj
  rw [setupME_eval p time d allowedIdx σ N h0]
  have hjle := setup_pairs_le_generator_table_reg p time d allowedIdx j hj
  omega

lemma generator_layout_prog_frame_above (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (N r : ℕ)
    (h0 : σ 0 = N) (hr : setupM p time d allowedIdx N + generatorTableBaseReg < r) :
    (generatorLayoutProg p time d allowedIdx outIdx).eval σ r = σ r := by
  apply paramSetupWrites_frame (setupME p time d allowedIdx)
    (setupME_reg0 p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx) σ r
    (generator_layout_pairs_pos p time d allowedIdx outIdx)
  intro j hj
  rw [setupME_eval p time d allowedIdx σ N h0]
  have hjle := generator_layout_pairs_le_table_reg p time d allowedIdx outIdx j hj
  omega

lemma generator_setup_prog_frame_above (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (N r : ℕ)
    (h0 : σ 0 = N) (hr : setupM p time d allowedIdx N + generatorTableBaseReg < r) :
    (generatorSetupProg p time d allowedIdx outIdx).eval σ r = σ r := by
  let τ := (setupProg p time d allowedIdx).eval σ
  have hτ0 : τ 0 = N := by
    change (setupProg p time d allowedIdx).eval σ 0 = N
    rw [setup_prog_zero, h0]
  simp only [generatorSetupProg, eval_seq]
  rw [generator_layout_prog_frame_above p time d allowedIdx outIdx τ N r hτ0 hr]
  exact setup_prog_frame_above p time d allowedIdx σ N r h0 hr

lemma generator_setup_prog_preserves_word (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (N base : ℕ)
    (xs : List ℕ) (h0 : σ 0 = N)
    (hbase : setupM p time d allowedIdx N + generatorTableBaseReg < base - 1)
    (hw : WordAt σ base xs) :
    WordAt ((generatorSetupProg p time d allowedIdx outIdx).eval σ) base xs := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [generator_setup_prog_frame_above p time d allowedIdx outIdx σ N (base - 1)
      h0 hbase]
    exact hw.1
  · rw [generator_setup_prog_frame_above p time d allowedIdx outIdx σ N (base + k)
      h0 (by omega)]
    exact hw.2 k hk

lemma generator_staged_bases_above_setup (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) (N : ℕ) :
    setupM p time d allowedIdx N + generatorTableBaseReg
      < generatorPrefBase p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + generatorTableBaseReg
      < generatorKindBase p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + generatorTableBaseReg
      < generatorArg1Base p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + generatorTableBaseReg
      < generatorArg2Base p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + generatorTableBaseReg
      < generatorOutBase p time d allowedIdx N - 1 := by
  simp [generatorTableBaseReg, generatorPrefBase, generatorKindBase,
    generatorArg1Base, generatorArg2Base, generatorOutBase,
    generatorPrefOffset, generatorKindOffset, generatorArg1Offset,
    generatorArg2Offset, generatorOutOffset, generatorPrefLen]
  omega

lemma generator_setup_prog_words (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    GeneratorWordsAt p time d allowedIdx outIdx prefIdx N
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ) := by
  have hb := generator_staged_bases_above_setup p time d allowedIdx N
  unfold GeneratorWordsAt at hw ⊢
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact generator_setup_prog_preserves_word p time d allowedIdx outIdx σ N _ _ h0
      hb.1 hw.1.1.1.1
  · exact generator_setup_prog_preserves_word p time d allowedIdx outIdx σ N _ _ h0
      hb.2.1 hw.1.1.1.2
  · exact generator_setup_prog_preserves_word p time d allowedIdx outIdx σ N _ _ h0
      hb.2.2.1 hw.1.1.2
  · exact generator_setup_prog_preserves_word p time d allowedIdx outIdx σ N _ _ h0
      hb.2.2.2.1 hw.1.2
  · exact generator_setup_prog_preserves_word p time d allowedIdx outIdx σ N _ _ h0
      hb.2.2.2.2 hw.2

lemma generator_setup_prog_frozen (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N) prefIdx
      (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ) := by
  let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
  have hs := generator_setup_prog_scalar_pins p time d allowedIdx outIdx σ N h0
  have hl := generator_setup_prog_layout_pins p time d allowedIdx outIdx σ N h0
  have hwords := generator_setup_prog_words p time d allowedIdx outIdx prefIdx σ N h0 hw
  unfold GeneratorWordsAt at hwords
  unfold GeneratorTableFrozen
  refine ⟨⟨⟨⟨?_, hwords.1.1.1.2⟩, hwords.1.1.2⟩,
    hwords.1.2⟩, hwords.2⟩
  unfold InitParamFrozen PinsAndWord
  refine ⟨?_, hwords.1.1.1.1⟩
  intro q hq
  simp only [initParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hs (persistWReg, (cookWindowPoly p time).eval N)
      (by simp [generatorScalarPins, persistWReg])
  · exact hs (persistTReg, (timePoly p time).eval N)
      (by simp [generatorScalarPins, persistTReg])
  · exact hs (initFreeLenReg, p.eval N) (by simp [generatorScalarPins])
  · exact hs (initPrefLenReg, generatorPrefLen N) (by simp [generatorScalarPins])
  · exact hl (initPrefBaseReg, generatorPrefBase p time d allowedIdx N)
      (by simp [generatorLayoutPins])

lemma generator_handoff_frame (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (r : ℕ) (hr : r ≠ 0) :
    (Program.assign 0 (setupME p time d allowedIdx)).eval τ r = τ r := by
  rw [eval_assign, writeReg_diff _ _ _ _ hr]

lemma generator_handoff_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (N : ℕ) (h0 : τ 0 = N) :
    (Program.assign 0 (setupME p time d allowedIdx)).eval τ 0
      = setupM p time d allowedIdx N := by
  rw [eval_assign, writeReg_same, setupME_eval p time d allowedIdx τ N h0]

lemma generator_handoff_pins (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (M : ℕ)
    (pins : List (ℕ × ℕ)) (hM : 1 ≤ M)
    (hpos : ∀ q ∈ pins, 1 ≤ q.1) (h : PinsHold M pins τ) :
    PinsHold M pins ((Program.assign 0 (setupME p time d allowedIdx)).eval τ) := by
  intro q hq
  rw [generator_handoff_frame p time d allowedIdx τ (M + q.1) (by
    have := hpos q hq
    omega)]
  exact h q hq

lemma generator_handoff_word (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (τ : Store) (base : ℕ)
    (xs : List ℕ) (hbase : 2 ≤ base) (h : WordAt τ base xs) :
    WordAt ((Program.assign 0 (setupME p time d allowedIdx)).eval τ) base xs := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [generator_handoff_frame p time d allowedIdx τ (base - 1) (by omega)]
    exact h.1
  · rw [generator_handoff_frame p time d allowedIdx τ (base + k) (by omega)]
    exact h.2 k hk

lemma generator_handoff_frozen (p time : Polynomial ℕ) (τ : Store)
    (M W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (allowedIdx prefIdx outIdx : List ℕ)
    (hM : 1 ≤ M) (hpref : 2 ≤ prefBase) (hkind : 2 ≤ kindBase)
    (harg1 : 2 ≤ arg1Base) (harg2 : 2 ≤ arg2Base) (hout : 2 ≤ outBase)
    (hF : GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
      (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) outBase outIdx τ) :
    GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
      (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) outBase outIdx
      ((Program.assign 0 (setupME p time d allowedIdx)).eval τ) := by
  unfold GeneratorTableFrozen at hF ⊢
  refine ⟨⟨⟨⟨?_,
    generator_handoff_word p time d allowedIdx τ kindBase _ hkind hF.1.1.1.2⟩,
    generator_handoff_word p time d allowedIdx τ arg1Base _ harg1 hF.1.1.2⟩,
    generator_handoff_word p time d allowedIdx τ arg2Base _ harg2 hF.1.2⟩,
    generator_handoff_word p time d allowedIdx τ outBase _ hout hF.2⟩
  unfold InitParamFrozen PinsAndWord at hF ⊢
  refine ⟨?_,
    generator_handoff_word p time d allowedIdx τ prefBase _ hpref hF.1.1.1.1.2⟩
  exact generator_handoff_pins p time d allowedIdx τ M _ hM (by
    intro q hq
    simp only [initParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      simp [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg])
    hF.1.1.1.1.1

lemma generator_setup_handoff_entry (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
    let ρ := (Program.assign 0 (setupME p time d allowedIdx)).eval τ
    GeneratorTableFrozen (setupM p time d allowedIdx N)
        ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
        (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
        prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
        (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
        (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
        (generatorOutBase p time d allowedIdx N) outIdx ρ ∧
      ρ 0 = setupM p time d allowedIdx N ∧
      ρ (setupM p time d allowedIdx N + wpJ) =
        generatorTableBase p time d allowedIdx outIdx N ∧
      ρ (setupM p time d allowedIdx N + emTblJ) =
        generatorTableBase p time d allowedIdx outIdx N ∧
      ρ (setupM p time d allowedIdx N + generatorTableBaseReg) =
        generatorTableBase p time d allowedIdx outIdx N := by
  dsimp only
  let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
  have hτ0 : τ 0 = N := by
    change (generatorSetupProg p time d allowedIdx outIdx).eval σ 0 = N
    rw [generator_setup_prog_zero, h0]
  have hM : 1 ≤ setupM p time d allowedIdx N := by simp [setupM]; omega
  have hb := generator_staged_bases_above_setup p time d allowedIdx N
  have hF := generator_setup_prog_frozen p time d allowedIdx outIdx prefIdx σ N h0 hw
  have hLF := generator_setup_prog_layout_pins p time d allowedIdx outIdx σ N h0
  refine ⟨generator_handoff_frozen p time τ _ _ _ _ _ _ _ _ _ _ d allowedIdx
      prefIdx outIdx hM (by omega) (by omega) (by omega) (by omega) (by omega) hF,
    generator_handoff_zero p time d allowedIdx τ N hτ0, ?_, ?_, ?_⟩
  · rw [generator_handoff_frame p time d allowedIdx τ _ (by simp [wpJ])]
    exact hLF (wpJ, generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])
  · rw [generator_handoff_frame p time d allowedIdx τ _ (by simp [emTblJ])]
    exact hLF (emTblJ, generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])
  · rw [generator_handoff_frame p time d allowedIdx τ _
      (by simp [generatorTableBaseReg])]
    exact hLF (generatorTableBaseReg,
      generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])

/-! ## Frame for the clause-count stage -/

lemma clauseCountProg_zero (n m M : ℕ) (σ : Store) (h0 : σ 0 = M) :
    (clauseCountProg n m).eval σ 0 = M := by
  have hAvoids : (clauseCountProg n m).AvoidsAbove (fun r => r = 0) 1 := by
    simp_all [Program.AvoidsAbove, clauseCountProg, triAccLoop, triAccStep,
      ctlAssign, ctlAddr, Expr.lb, rowCountReg, iterReg]
  exact (hAvoids.eval_frame σ rfl (by decide)).trans h0

lemma clauseCountProg_frame (n m M addr : ℕ) (σ : Store) (h0 : σ 0 = M)
    (hM : M ≤ addr) (hrow : addr ≠ M + rowCountReg)
    (hiter : addr ≠ M + iterReg) :
    (clauseCountProg n m).eval σ addr = σ addr := by
  have hrowPos : 1 ≤ rowCountReg := by norm_num [rowCountReg]
  have hiterPos : 1 ≤ iterReg := by norm_num [iterReg]
  have hiterW : iterReg ≠ persistWReg := by norm_num [iterReg, persistWReg]
  have haddr : M + (addr - M) = addr := Nat.add_sub_of_le hM
  have hrow' : addr - M ≠ rowCountReg := by
    intro h
    apply hrow
    rw [← haddr, h]
  have hiter' : addr - M ≠ iterReg := by
    intro h
    apply hiter
    rw [← haddr, h]
  let σ1 := (ctlAssign rowCountReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero rowCountReg _ σ hrowPos).trans h0
  have hσ1addr : σ1 addr = σ addr := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff _ _ _ _ (by rw [h0]; exact hrow)]
  let σ2 := (triAccLoop rowCountReg iterReg persistWReg).eval σ1
  have hσ20 : σ2 0 = M := by
    dsimp [σ2]
    rw [triAccLoop_zero M rowCountReg iterReg persistWReg σ1 hσ10 hrowPos hiterPos]
  have hσ2addr : σ2 addr = σ1 addr := by
    dsimp [σ2]
    rw [← haddr]
    exact triAccLoop_frame M rowCountReg iterReg persistWReg (addr - M) σ1 hσ10 hrowPos
      hiterPos hrow' hiter' hiterW
  simp only [clauseCountProg, eval_seq]
  rw [show ((ctlAssign rowCountReg (.const 0)).eval σ) = σ1 by rfl]
  rw [show ((triAccLoop rowCountReg iterReg persistWReg).eval σ1) = σ2 by rfl]
  rw [ctlAssign_eval_diff _ _ _ _ (by rw [hσ20]; exact hrow)]
  exact hσ2addr.trans hσ1addr

lemma clauseCountProg_preserves_word (n m M base : ℕ) (xs : List ℕ)
    (σ : Store) (h0 : σ 0 = M)
    (hbase : M + iterReg < base - 1)
    (hw : WordAt σ base xs) :
    WordAt ((clauseCountProg n m).eval σ) base xs := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [clauseCountProg_frame n m M (base - 1) σ h0 (by omega)
      (by simp [rowCountReg, iterReg] at hbase ⊢; omega)
      (by simp [iterReg] at hbase ⊢; omega)]
    exact hw.1
  · rw [clauseCountProg_frame n m M (base + k) σ h0 (by omega)
      (by simp [rowCountReg, iterReg] at hbase ⊢; omega)
      (by simp [iterReg] at hbase ⊢; omega)]
    exact hw.2 k hk

lemma generator_staged_bases_above_count_cells (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx : List ℕ) (N : ℕ) :
    setupM p time d allowedIdx N + iterReg <
        generatorPrefBase p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + iterReg <
        generatorKindBase p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + iterReg <
        generatorArg1Base p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + iterReg <
        generatorArg2Base p time d allowedIdx N - 1 ∧
    setupM p time d allowedIdx N + iterReg <
        generatorOutBase p time d allowedIdx N - 1 := by
  simp [generatorPrefBase, generatorKindBase, generatorArg1Base, generatorArg2Base,
    generatorOutBase, generatorPrefOffset, generatorKindOffset, generatorArg1Offset,
    generatorArg2Offset, generatorOutOffset, generatorPrefLen, iterReg]
  omega

lemma clauseCountProg_preserves_generatorTableFrozen
    (n m M W T freeLen prefLen prefBase : ℕ)
    (prefIdx : List ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (outBase : ℕ) (outIdx : List ℕ) (τ : Store) (h0 : τ 0 = M)
    (hpref : M + iterReg < prefBase - 1)
    (hkind : M + iterReg < kindBase - 1)
    (harg1 : M + iterReg < arg1Base - 1)
    (harg2 : M + iterReg < arg2Base - 1)
    (hout : M + iterReg < outBase - 1)
    (hF : GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase colk
      arg1Base col1 arg2Base col2 outBase outIdx τ) :
    GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase colk
      arg1Base col1 arg2Base col2 outBase outIdx
      ((clauseCountProg n m).eval τ) := by
  unfold GeneratorTableFrozen InitParamFrozen PinsAndWord at hF ⊢
  rcases hF with ⟨hA, houtW⟩
  rcases hA with ⟨hB, harg2W⟩
  rcases hB with ⟨hC, harg1W⟩
  rcases hC with ⟨hD, hkindW⟩
  rcases hD with ⟨hpins, hprefW⟩
  have hprefW' := clauseCountProg_preserves_word n m M prefBase prefIdx τ h0 hpref hprefW
  have hkindW' := clauseCountProg_preserves_word n m M kindBase colk τ h0 hkind hkindW
  have harg1W' := clauseCountProg_preserves_word n m M arg1Base col1 τ h0 harg1 harg1W
  have harg2W' := clauseCountProg_preserves_word n m M arg2Base col2 τ h0 harg2 harg2W
  have houtW' := clauseCountProg_preserves_word n m M outBase outIdx τ h0 hout houtW
  have hpins' : PinsHold M
      (initParamPins0 initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg
        W T freeLen prefLen prefBase) ((clauseCountProg n m).eval τ) := by
    intro q hq
    simp only [initParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [clauseCountProg_frame n m M (M + initWReg) τ h0 (by omega)
        (by norm_num [initWReg, rowCountReg]) (by norm_num [initWReg, iterReg])]
      exact hpins (initWReg, W) (by simp [initParamPins0])
    · rw [clauseCountProg_frame n m M (M + initTReg) τ h0 (by omega)
        (by norm_num [initTReg, rowCountReg]) (by norm_num [initTReg, iterReg])]
      exact hpins (initTReg, T) (by simp [initParamPins0])
    · rw [clauseCountProg_frame n m M (M + initFreeLenReg) τ h0 (by omega)
        (by norm_num [initFreeLenReg, rowCountReg]) (by norm_num [initFreeLenReg, iterReg])]
      exact hpins (initFreeLenReg, freeLen) (by simp [initParamPins0])
    · rw [clauseCountProg_frame n m M (M + initPrefLenReg) τ h0 (by omega)
        (by norm_num [initPrefLenReg, rowCountReg]) (by norm_num [initPrefLenReg, iterReg])]
      exact hpins (initPrefLenReg, prefLen) (by simp [initParamPins0])
    · rw [clauseCountProg_frame n m M (M + initPrefBaseReg) τ h0 (by omega)
        (by norm_num [initPrefBaseReg, rowCountReg]) (by norm_num [initPrefBaseReg, iterReg])]
      exact hpins (initPrefBaseReg, prefBase) (by simp [initParamPins0])
  refine ⟨?_, houtW'⟩
  refine ⟨?_, harg2W'⟩
  refine ⟨?_, harg1W'⟩
  refine ⟨?_, hkindW'⟩
  exact ⟨hpins', hprefW'⟩

/-! ## Integrated generator contract -/

lemma generator_prog_writes_table (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    ClauseTableAt ((generatorProg p time d allowedIdx outIdx).eval σ)
      (generatorTableBase p time d allowedIdx outIdx N)
      (descTableauCNF
        (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval N)
          (d.numLetters + 1)) d prefIdx (p.eval N) allowedIdx outIdx
        ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)) := by
  let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
  let ρ := (Program.assign 0 (setupME p time d allowedIdx)).eval τ
  have he := generator_setup_handoff_entry p time d allowedIdx outIdx prefIdx σ N h0 hw
  change GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ ∧
    ρ 0 = setupM p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + emTblJ) =
      generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + generatorTableBaseReg) =
      generatorTableBase p time d allowedIdx outIdx N at he
  obtain ⟨hF, hρ0, hwp, _, _⟩ := he
  have hp := generator_placement_of_layout p time d allowedIdx outIdx prefIdx N hlen
  have hsep : setupM p time d allowedIdx N + generatorJmax d outIdx N <
      generatorTableBase p time d allowedIdx outIdx N := by
    simp [generatorTableBase]
  let κ := (clauseCountProg d.numStates d.numLetters).eval ρ
  have hκ0 : κ 0 = setupM p time d allowedIdx N := by
    dsimp [κ]
    exact clauseCountProg_zero d.numStates d.numLetters
      (setupM p time d allowedIdx N) ρ hρ0
  have hbases := generator_staged_bases_above_count_cells p time d allowedIdx N
  have hκF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx κ := by
    dsimp [κ]
    exact clauseCountProg_preserves_generatorTableFrozen
      d.numStates d.numLetters (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
      (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N) prefIdx
      (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ
      (by rw [hρ0]) hbases.1 hbases.2.1 hbases.2.2.1 hbases.2.2.2.1
      hbases.2.2.2.2 hF
  have hκwp : κ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N := by
    dsimp [κ]
    rw [clauseCountProg_frame d.numStates d.numLetters
      (setupM p time d allowedIdx N)
      (setupM p time d allowedIdx N + wpJ) ρ hρ0 (by omega)
      (by norm_num [wpJ, rowCountReg]) (by norm_num [wpJ, iterReg])]
    exact hwp
  have htable := table_writer_param_gives_clause_table_at
    (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
    (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
    (generatorKindBase p time d allowedIdx N)
    (generatorArg1Base p time d allowedIdx N)
    (generatorArg2Base p time d allowedIdx N)
    (generatorOutBase p time d allowedIdx N) d
    prefIdx allowedIdx outIdx hp κ (generatorTableBase p time d allowedIdx outIdx N)
    hκF hκ0 hκwp hsep
  simpa only [generatorProg, eval_seq, τ, ρ, κ] using htable

lemma generator_prog_emitter_base (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    (generatorProg p time d allowedIdx outIdx).eval σ
        (setupM p time d allowedIdx N + emTblJ)
      = generatorTableBase p time d allowedIdx outIdx N := by
  let τ := (generatorSetupProg p time d allowedIdx outIdx).eval σ
  let ρ := (Program.assign 0 (setupME p time d allowedIdx)).eval τ
  have he := generator_setup_handoff_entry p time d allowedIdx outIdx prefIdx σ N h0 hw
  change GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ ∧
    ρ 0 = setupM p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + emTblJ) =
      generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + generatorTableBaseReg) =
      generatorTableBase p time d allowedIdx outIdx N at he
  obtain ⟨hF, hρ0, hwp, _, _⟩ := he
  have hp := generator_placement_of_layout p time d allowedIdx outIdx prefIdx N hlen
  have hsep : setupM p time d allowedIdx N + generatorJmax d outIdx N <
      generatorTableBase p time d allowedIdx outIdx N := by
    simp [generatorTableBase]
  let κ := (clauseCountProg d.numStates d.numLetters).eval ρ
  have hκ0 : κ 0 = setupM p time d allowedIdx N := by
    dsimp [κ]
    exact clauseCountProg_zero d.numStates d.numLetters
      (setupM p time d allowedIdx N) ρ hρ0
  have hbases := generator_staged_bases_above_count_cells p time d allowedIdx N
  have hκF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx κ := by
    dsimp [κ]
    exact clauseCountProg_preserves_generatorTableFrozen
      d.numStates d.numLetters (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
      (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N) prefIdx
      (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ
      (by rw [hρ0]) hbases.1 hbases.2.1 hbases.2.2.1 hbases.2.2.2.1
      hbases.2.2.2.2 hF
  have hκwp : κ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N := by
    dsimp [κ]
    rw [clauseCountProg_frame d.numStates d.numLetters
      (setupM p time d allowedIdx N)
      (setupM p time d allowedIdx N + wpJ) ρ hρ0 (by omega)
      (by norm_num [wpJ, rowCountReg]) (by norm_num [wpJ, iterReg])]
    exact hwp
  have hio := tableWriterProgParam_io_param
    (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
    (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
    (generatorKindBase p time d allowedIdx N)
    (generatorArg1Base p time d allowedIdx N)
    (generatorArg2Base p time d allowedIdx N)
    (generatorOutBase p time d allowedIdx N) d
    prefIdx allowedIdx outIdx hp κ (generatorTableBase p time d allowedIdx outIdx N)
    hκF hκ0 hκwp hsep
  have hem := hio.1.2
  have hbase : generatorOutBase p time d allowedIdx N + outIdx.length + 1 =
      generatorTableBase p time d allowedIdx outIdx N := by
    simp [generatorOutBase, generatorTableBase, generatorJmax]
    omega
  rw [hbase] at hem
  simpa only [generatorProg, eval_seq, τ, ρ, κ] using hem

/-! ## Concrete input stores and input-uniformity -/

def stageWordStore (σ : Store) (base : ℕ) (xs : List ℕ) : Store :=
  fun r =>
    if r = base - 1 then xs.length
    else if base ≤ r ∧ r < base + xs.length then xs.getD (r - base) 0
    else σ r

lemma stage_word_store_word (σ : Store) (base : ℕ) (xs : List ℕ)
    (hbase : 1 ≤ base) : WordAt (stageWordStore σ base xs) base xs := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [stageWordStore]
  · have hne : base + k ≠ base - 1 := by omega
    have hrange : base ≤ base + k ∧ base + k < base + xs.length := by omega
    simp [stageWordStore, hne, hrange]

lemma stage_word_store_frame (σ : Store) (base : ℕ) (xs : List ℕ) (r : ℕ)
    (hbase : 1 ≤ base) (hr : r < base - 1 ∨ base + xs.length ≤ r) :
    stageWordStore σ base xs r = σ r := by
  unfold stageWordStore
  split
  · rename_i h
    subst r
    omega
  · split
    · rename_i h
      omega
    · rfl

lemma stage_word_store_preserves_before (σ : Store)
    (oldBase : ℕ) (oldXs : List ℕ) (base : ℕ) (xs : List ℕ)
    (holdBase : 1 ≤ oldBase)
    (hsep : oldBase + oldXs.length < base)
    (hw : WordAt σ oldBase oldXs) :
    WordAt (stageWordStore σ base xs) oldBase oldXs := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [stage_word_store_frame σ base xs (oldBase - 1) (by omega)
      (by left; omega)]
    exact hw.1
  · rw [stage_word_store_frame σ base xs (oldBase + k) (by omega)
      (by left; omega)]
    exact hw.2 k hk

def inputLengthStore (N : ℕ) : Store :=
  fun r => if r = 0 then N else 0

noncomputable def generatorInputStore (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ) : Store :=
  stageWordStore
    (stageWordStore
      (stageWordStore
        (stageWordStore
          (stageWordStore (inputLengthStore N)
            (generatorPrefBase p time d allowedIdx N) prefIdx)
          (generatorKindBase p time d allowedIdx N) (d.table.map transKind))
        (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1))
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2))
    (generatorOutBase p time d allowedIdx N) outIdx

lemma generator_input_store_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ) :
    generatorInputStore p time d allowedIdx outIdx prefIdx N 0 = N := by
  have hb := generator_staged_bases_above_setup p time d allowedIdx N
  unfold generatorInputStore
  rw [stage_word_store_frame _ _ outIdx 0 (by omega) (by left; omega)]
  rw [stage_word_store_frame _ _ (d.table.map transArg2) 0
    (by omega) (by left; omega)]
  rw [stage_word_store_frame _ _ (d.table.map transArg1) 0
    (by omega) (by left; omega)]
  rw [stage_word_store_frame _ _ (d.table.map transKind) 0
    (by omega) (by left; omega)]
  rw [stage_word_store_frame _ _ prefIdx 0 (by omega) (by left; omega)]
  simp [inputLengthStore]

/-- The five staged-word bases are positive, with each following base beyond the prior word. -/
lemma generator_input_store_words_layout_bounds (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx prefIdx : List ℕ) (N : ℕ)
    (hlen : prefIdx.length = generatorPrefLen N) :
    1 ≤ generatorPrefBase p time d allowedIdx N ∧
    1 ≤ generatorKindBase p time d allowedIdx N ∧
    1 ≤ generatorArg1Base p time d allowedIdx N ∧
    1 ≤ generatorArg2Base p time d allowedIdx N ∧
    1 ≤ generatorOutBase p time d allowedIdx N ∧
    generatorPrefBase p time d allowedIdx N + prefIdx.length <
      generatorKindBase p time d allowedIdx N ∧
    generatorKindBase p time d allowedIdx N + (d.table.map transKind).length <
      generatorArg1Base p time d allowedIdx N ∧
    generatorArg1Base p time d allowedIdx N + (d.table.map transArg1).length <
      generatorArg2Base p time d allowedIdx N ∧
    generatorArg2Base p time d allowedIdx N + (d.table.map transArg2).length <
      generatorOutBase p time d allowedIdx N := by
  have hbp : 1 ≤ generatorPrefBase p time d allowedIdx N := by
    simp [generatorPrefBase, generatorPrefOffset]
  have hbk : 1 ≤ generatorKindBase p time d allowedIdx N := by
    simp [generatorKindBase, generatorKindOffset, generatorPrefOffset]
    omega
  have hb1 : 1 ≤ generatorArg1Base p time d allowedIdx N := by
    simp [generatorArg1Base, generatorArg1Offset]
    omega
  have hb2 : 1 ≤ generatorArg2Base p time d allowedIdx N := by
    simp [generatorArg2Base, generatorArg2Offset]
    omega
  have hbo : 1 ≤ generatorOutBase p time d allowedIdx N := by
    simp [generatorOutBase, generatorOutOffset]
    omega
  have hpk : generatorPrefBase p time d allowedIdx N + prefIdx.length <
      generatorKindBase p time d allowedIdx N := by
    rw [hlen]
    simp [generatorPrefBase, generatorKindBase, generatorKindOffset, generatorPrefOffset]
    omega
  have hk1 : generatorKindBase p time d allowedIdx N + (d.table.map transKind).length <
      generatorArg1Base p time d allowedIdx N := by
    simp [generatorKindBase, generatorArg1Base, generatorArg1Offset]
    omega
  have h12 : generatorArg1Base p time d allowedIdx N + (d.table.map transArg1).length <
      generatorArg2Base p time d allowedIdx N := by
    simp [generatorArg1Base, generatorArg2Base, generatorArg2Offset]
    omega
  have h2o : generatorArg2Base p time d allowedIdx N + (d.table.map transArg2).length <
      generatorOutBase p time d allowedIdx N := by
    simp [generatorArg2Base, generatorOutBase, generatorOutOffset]
    omega
  exact ⟨hbp, hbk, hb1, hb2, hbo, hpk, hk1, h12, h2o⟩

lemma generator_input_store_words (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ)
    (hlen : prefIdx.length = generatorPrefLen N) :
    GeneratorWordsAt p time d allowedIdx outIdx prefIdx N
      (generatorInputStore p time d allowedIdx outIdx prefIdx N) := by
  let s0 := inputLengthStore N
  let s1 := stageWordStore s0 (generatorPrefBase p time d allowedIdx N) prefIdx
  let s2 := stageWordStore s1 (generatorKindBase p time d allowedIdx N)
    (d.table.map transKind)
  let s3 := stageWordStore s2 (generatorArg1Base p time d allowedIdx N)
    (d.table.map transArg1)
  let s4 := stageWordStore s3 (generatorArg2Base p time d allowedIdx N)
    (d.table.map transArg2)
  let s5 := stageWordStore s4 (generatorOutBase p time d allowedIdx N) outIdx
  obtain ⟨hbp, hbk, hb1, hb2, hbo, hpk, hk1, h12, h2o⟩ :=
    generator_input_store_words_layout_bounds p time d allowedIdx prefIdx N hlen
  have hp1 : WordAt s1 (generatorPrefBase p time d allowedIdx N) prefIdx :=
    stage_word_store_word s0 _ _ hbp
  have hp2 : WordAt s2 (generatorPrefBase p time d allowedIdx N) prefIdx :=
    stage_word_store_preserves_before s1 (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      hbp hpk hp1
  have hk2 : WordAt s2 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) :=
    stage_word_store_word s1 _ _ hbk
  have hp3 : WordAt s3 (generatorPrefBase p time d allowedIdx N) prefIdx :=
    stage_word_store_preserves_before s2 (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      hbp (by omega) hp2
  have hk3 : WordAt s3 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) :=
    stage_word_store_preserves_before s2 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) hbk hk1 hk2
  have h13 : WordAt s3 (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) :=
    stage_word_store_word s2 _ _ hb1
  have hp4 : WordAt s4 (generatorPrefBase p time d allowedIdx N) prefIdx :=
    stage_word_store_preserves_before s3 (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      hbp (by omega) hp3
  have hk4 : WordAt s4 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) :=
    stage_word_store_preserves_before s3 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) (generatorArg2Base p time d allowedIdx N)
      (d.table.map transArg2) hbk (by omega) hk3
  have h14 : WordAt s4 (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) :=
    stage_word_store_preserves_before s3 (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) (generatorArg2Base p time d allowedIdx N)
      (d.table.map transArg2) hb1 h12 h13
  have h24 : WordAt s4 (generatorArg2Base p time d allowedIdx N)
      (d.table.map transArg2) :=
    stage_word_store_word s3 _ _ hb2
  have hp5 : WordAt s5 (generatorPrefBase p time d allowedIdx N) prefIdx :=
    stage_word_store_preserves_before s4 (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorOutBase p time d allowedIdx N) outIdx hbp (by omega) hp4
  have hk5 : WordAt s5 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) :=
    stage_word_store_preserves_before s4 (generatorKindBase p time d allowedIdx N)
      (d.table.map transKind) (generatorOutBase p time d allowedIdx N) outIdx
      hbk (by omega) hk4
  have h15 : WordAt s5 (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) :=
    stage_word_store_preserves_before s4 (generatorArg1Base p time d allowedIdx N)
      (d.table.map transArg1) (generatorOutBase p time d allowedIdx N) outIdx
      hb1 (by omega) h14
  have h25 : WordAt s5 (generatorArg2Base p time d allowedIdx N)
      (d.table.map transArg2) :=
    stage_word_store_preserves_before s4 (generatorArg2Base p time d allowedIdx N)
      (d.table.map transArg2) (generatorOutBase p time d allowedIdx N) outIdx
      hb2 h2o h24
  have ho5 : WordAt s5 (generatorOutBase p time d allowedIdx N) outIdx :=
    stage_word_store_word s4 _ _ hbo
  change GeneratorWordsAt p time d allowedIdx outIdx prefIdx N s5
  exact ⟨⟨⟨⟨hp5, hk5⟩, h15⟩, h25⟩, ho5⟩

lemma generator_words_at_satisfiable (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ)
    (hlen : prefIdx.length = generatorPrefLen N) :
    ∃ σ : Store, σ 0 = N ∧ GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ := by
  refine ⟨generatorInputStore p time d allowedIdx outIdx prefIdx N,
    generator_input_store_zero p time d allowedIdx outIdx prefIdx N, ?_⟩
  exact generator_input_store_words p time d allowedIdx outIdx prefIdx N hlen

lemma generator_prog_concrete_run_exists (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ) (N : ℕ)
    (hlen : prefIdx.length = generatorPrefLen N) :
    ∃ σ : Store, σ 0 = N ∧
      ClauseTableAt ((generatorProg p time d allowedIdx outIdx).eval σ)
        (generatorTableBase p time d allowedIdx outIdx N)
        (descTableauCNF
          (denseLayout (d.numStates + 1) ((cookWindowPoly p time).eval N)
            (d.numLetters + 1)) d prefIdx (p.eval N) allowedIdx outIdx
          ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)) := by
  obtain ⟨σ, h0, hw⟩ :=
    generator_words_at_satisfiable p time d allowedIdx outIdx prefIdx N hlen
  exact ⟨σ, h0,
    generator_prog_writes_table p time d allowedIdx outIdx prefIdx σ N
      h0 hlen hw⟩

/-! ## What the emitter is owed

The emitter needs the table contents and its base register to identify the same
address; separate proofs could refer to different addresses.  Bundling both facts
at one base gives the emitter a usable precondition for the generated table. -/

/-- The generator hands the emitter both halves of its precondition, at one
address, from one run. -/
lemma generator_prog_meets_emitter_precondition (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx prefIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hlen : prefIdx.length = generatorPrefLen N)
    (hw : GeneratorWordsAt p time d allowedIdx outIdx prefIdx N σ) :
    ClauseTableAt ((generatorProg p time d allowedIdx outIdx).eval σ)
        (generatorTableBase p time d allowedIdx outIdx N)
        (descTableauCNF (denseLayout (d.numStates + 1)
            ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d
          prefIdx (p.eval N) allowedIdx outIdx
          ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)) ∧
      (generatorProg p time d allowedIdx outIdx).eval σ
          (setupM p time d allowedIdx N + emTblJ)
        = generatorTableBase p time d allowedIdx outIdx N :=
  ⟨generator_prog_writes_table p time d allowedIdx outIdx prefIdx σ N h0 hlen hw,
    generator_prog_emitter_base p time d allowedIdx outIdx prefIdx σ N h0 hlen hw⟩

end NPComplete.CookLevin

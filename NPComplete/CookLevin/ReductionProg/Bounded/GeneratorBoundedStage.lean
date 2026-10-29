module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAcceptFamily
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedUniqFamily

/-!
The family bounds are each proved against
their own natural `Frozen` — the pair of run-time parameters a family reads at
entry.  The generator's stage programs are not quite the families: each of the
initial, transition and accept stages appends a short reload step
(`loadTransParamsProg`/`loadAcceptParamProg`/`loadEmitterTableProg`) that
recomputes the *next* stage's staged-word bases from the current stage's own
exit data, matching what `GeneratorProg.lean`'s correctness side already does
for `ClauseWriterIO`.

Composing a stage's own family bound with its reload step needs nothing more
than `clauseWriterBounded_seq`, since both run under the same `Frozen`.
Composing *stages* into `tableWriterProgParam`, though, changes `Frozen` at
every seam — the uniqueness stage's exit is `GeneratorTableFrozen`, the
initial stage's exit is `TransWithOutFrozen`, and so on — which is exactly
the shape `clauseWriterBounded_seq_io` (`GeneratorBoundedTransFamily`) was
built for, mirroring `clauseWriterIO_seq` on the correctness side.

Each reload step writes only into a control cell, not the clause table, so its
width is `wid = 0`.  The bounds needed for the recomputed staged-word bases
(`kindBase`, `arg1Base`, `arg2Base`, `outBase`, and the emitter table base)
ensure they remain within `K`, allowing `TightCells` to cover each written cell.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Widening the bounded contract itself

General-purpose lemmas the write primitives did not need: accepting a
stronger `Frozen` on entry (mirroring `clauseWriterIO_strengthen_entry`).
It is used to line a stage's own bound up with the wider `Frozen`/`Jmax`
the surrounding `.seq` chain runs at. -/

/-- Accepting a stronger `Frozen` on entry. -/
lemma clauseWriterBounded_strengthen_entry (prog : Program) (M Jmax wpJ K S B wid : ℕ)
    (Frozen Frozen' : Store → Prop)
    (hs : ∀ τ, Frozen' τ → Frozen τ)
    (h : ClauseWriterBounded prog M Jmax wpJ K S B wid Frozen) :
    ClauseWriterBounded prog M Jmax wpJ K S B wid Frozen' :=
  fun τ wp hF h0 hw hsep hslack hst ht => h τ wp (hs τ hF) h0 hw hsep hslack hst ht

/-! ## Reading two control cells

`loadTransParamsProg`'s kind-base assignment is the one place in the
generator that adds two control cells before adding a constant, so a new
primitive is needed alongside `GeneratorBoundedWrite`'s single-cell ones. -/

/-- A control-cell write of the form `ctlCell a + c`. -/
lemma programBoundedIn_ctlAssign_add_const (B M j a c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj : M + j ≤ B) (ha : M + a ≤ B) (hval : σ (M + a) + c ≤ B) :
    ProgramBoundedIn B σ (ctlAssign j (.add (ctlCell a) (.const c))) := by
  unfold ctlAssign
  refine ⟨exprBoundedIn_ctlAddr B M j σ h0 hj, ?_, by rw [ctlAddr_eval_at M j σ h0]; omega⟩
  refine ⟨exprBoundedIn_ctlCell B M a σ h0 ha, by simp only [ExprBoundedIn]; omega, ?_⟩
  simp only [Expr.eval, ctlCell_eval, h0]
  omega

/-- A control-cell write of the form `ctlCell a + ctlCell b + c`. -/
lemma programBoundedIn_ctlAssign_add_add_const (B M j a b c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj : M + j ≤ B) (ha : M + a ≤ B) (hb : M + b ≤ B)
    (hval : σ (M + a) + σ (M + b) + c ≤ B) :
    ProgramBoundedIn B σ (ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))) := by
  unfold ctlAssign
  refine ⟨exprBoundedIn_ctlAddr B M j σ h0 hj, ?_, by rw [ctlAddr_eval_at M j σ h0]; omega⟩
  refine ⟨⟨exprBoundedIn_ctlCell B M a σ h0 ha, exprBoundedIn_ctlCell B M b σ h0 hb, ?_⟩,
    by simp only [ExprBoundedIn]; omega, ?_⟩
  · rw [ctlCell_eval, ctlCell_eval, h0]; omega
  · simp only [Expr.eval, ctlCell_eval, h0]
    omega

/-- Writing `ctlCell a + c` into control cell `j` keeps both envelopes,
provided the tight one covers where the written value lands. -/
lemma ctlAssign_add_const_preserves (K S M j a c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj2 : 2 ≤ j) (hj24 : j ≤ 24)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hK : σ (M + a) + c ≤ K) (hKS : K ≤ S) :
    (ctlAssign j (.add (ctlCell a) (.const c))).eval σ 0 = M ∧
      (ctlAssign j (.add (ctlCell a) (.const c))).eval σ (M + j) = σ (M + a) + c ∧
      TightCells K M ((ctlAssign j (.add (ctlCell a) (.const c))).eval σ) ∧
      StoreValuesLe S ((ctlAssign j (.add (ctlCell a) (.const c))).eval σ) := by
  have hev : (ctlAssign j (.add (ctlCell a) (.const c))).eval σ
      = writeReg σ (M + j) (σ (M + a) + c) := by
    unfold ctlAssign
    rw [eval_assignInd]
    simp only [Expr.eval, ctlAddr, ctlCell, h0]
  rw [hev]
  refine ⟨by rw [writeReg_diff σ (M + j) _ 0 (by omega), h0], writeReg_same _ _ _,
    fun j' h2 h24 => ?_, fun i => ?_⟩
  · by_cases hj' : j' = j
    · rw [hj', writeReg_same]; exact hK
    · rw [writeReg_diff σ (M + j) _ (M + j') (by omega)]; exact ht j' h2 h24
  · by_cases hi : i = M + j
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ (M + j) _ i hi]; exact hst i

/-- Writing `ctlCell a + ctlCell b + c` into control cell `j` keeps both
envelopes, provided the tight one covers where the written value lands. -/
lemma ctlAssign_add_add_const_preserves (K S M j a b c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj2 : 2 ≤ j) (hj24 : j ≤ 24)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hK : σ (M + a) + σ (M + b) + c ≤ K) (hKS : K ≤ S) :
    (ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))).eval σ 0 = M ∧
      (ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))).eval σ (M + j)
        = σ (M + a) + σ (M + b) + c ∧
      TightCells K M
        ((ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))).eval σ) ∧
      StoreValuesLe S
        ((ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))).eval σ) := by
  have hev : (ctlAssign j (.add (.add (ctlCell a) (ctlCell b)) (.const c))).eval σ
      = writeReg σ (M + j) (σ (M + a) + σ (M + b) + c) := by
    unfold ctlAssign
    rw [eval_assignInd]
    simp only [Expr.eval, ctlAddr, ctlCell, h0]
  rw [hev]
  refine ⟨by rw [writeReg_diff σ (M + j) _ 0 (by omega), h0], writeReg_same _ _ _,
    fun j' h2 h24 => ?_, fun i => ?_⟩
  · by_cases hj' : j' = j
    · rw [hj', writeReg_same]; exact hK
    · rw [writeReg_diff σ (M + j) _ (M + j') (by omega)]; exact ht j' h2 h24
  · by_cases hi : i = M + j
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ (M + j) _ i hi]; exact hst i

/-! ## The three reload steps, as `ClauseWriterBounded` at width `0`

None of these writes a clause row, so each is bounded at `wid = 0` for *any*
`Frozen` that pins the cells it reads — the caller supplies that extraction as
a hypothesis rather than the concrete `Frozen`, so the same lemma serves both
the standalone stage bound and its later use inside the wider generator
`Frozen`. -/

/-- `loadTransParamsProg`, as a `ClauseWriterBounded` at width `0`. -/
lemma clauseWriterBounded_loadTransParamsProg
    (M Jmax K S B prefLen prefBase kindBase arg1Base arg2Base : ℕ)
    (d : TableauDescriptor) (Frozen : Store → Prop)
    (hpins : ∀ τ, Frozen τ →
      τ (M + initPrefBaseReg) = prefBase ∧ τ (M + initPrefLenReg) = prefLen)
    (hkind : prefBase + prefLen + 2 = kindBase)
    (harg1 : kindBase + d.table.length + 2 = arg1Base)
    (harg2 : arg1Base + d.table.length + 2 = arg2Base)
    (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (loadTransParamsProg d) M Jmax wpJ K S B 0 Frozen := by
  have rkb : transKindBaseReg = 20 := rfl
  have ra1 : transArg1BaseReg = 21 := rfl
  have ra2 : transArg2BaseReg = 22 := rfl
  have rpb : initPrefBaseReg = 19 := rfl
  have rpl : initPrefLenReg = 18 := rfl
  intro τ wp hF h0 hwp hsep hslack hst ht
  obtain ⟨hpref, hplen⟩ := hpins τ hF
  set e1 : Expr := .add (.add (ctlCell initPrefBaseReg) (ctlCell initPrefLenReg)) (.const 2)
    with he1def
  set e2 : Expr := .add (ctlCell transKindBaseReg) (.const (d.table.length + 2)) with he2def
  set e3 : Expr := .add (ctlCell transArg1BaseReg) (.const (d.table.length + 2)) with he3def
  have hb1 : ProgramBoundedIn B τ (ctlAssign transKindBaseReg e1) := by
    rw [he1def]
    exact programBoundedIn_ctlAssign_add_add_const B M transKindBaseReg initPrefBaseReg
      initPrefLenReg 2 τ h0 (by omega) (by omega) (by omega)
      (by rw [hpref, hplen]; omega)
  obtain ⟨hτ10, hτ1kind, hτ1t, hτ1s⟩ := ctlAssign_add_add_const_preserves K S M
    transKindBaseReg initPrefBaseReg initPrefLenReg 2 τ h0 (by omega) (by omega) ht hst
    (by rw [hpref, hplen]; omega) hKS
  set τ1 := (ctlAssign transKindBaseReg e1).eval τ with hτ1def
  have hb2 : ProgramBoundedIn B τ1 (ctlAssign transArg1BaseReg e2) := by
    rw [he2def]
    exact programBoundedIn_ctlAssign_add_const B M transArg1BaseReg transKindBaseReg
      (d.table.length + 2) τ1 hτ10 (by omega) (by omega) (by rw [hτ1kind]; omega)
  obtain ⟨hτ20, hτ2arg1, hτ2t, hτ2s⟩ := ctlAssign_add_const_preserves K S M
    transArg1BaseReg transKindBaseReg (d.table.length + 2) τ1 hτ10 (by omega) (by omega)
    hτ1t hτ1s (by rw [hτ1kind]; omega) hKS
  set τ2 := (ctlAssign transArg1BaseReg e2).eval τ1 with hτ2def
  have hb3 : ProgramBoundedIn B τ2 (ctlAssign transArg2BaseReg e3) := by
    rw [he3def]
    exact programBoundedIn_ctlAssign_add_const B M transArg2BaseReg transArg1BaseReg
      (d.table.length + 2) τ2 hτ20 (by omega) (by omega) (by rw [hτ2arg1]; omega)
  obtain ⟨hτ30, hτ3arg2, hτ3t, hτ3s⟩ := ctlAssign_add_const_preserves K S M
    transArg2BaseReg transArg1BaseReg (d.table.length + 2) τ2 hτ20 (by omega) (by omega)
    hτ2t hτ2s (by rw [hτ2arg1]; omega) hKS
  have heval : (loadTransParamsProg d).eval τ
      = (ctlAssign transArg2BaseReg e3).eval τ2 := by
    unfold loadTransParamsProg
    rw [eval_seq, eval_seq]
  rw [heval]
  refine ⟨⟨hb1, hb2, hb3⟩, hτ3s, hτ3t⟩

/-- `loadAcceptParamProg`, as a `ClauseWriterBounded` at width `0`. -/
lemma clauseWriterBounded_loadAcceptParamProg
    (M Jmax K S B arg2Base outBase : ℕ) (d : TableauDescriptor) (Frozen : Store → Prop)
    (hpins : ∀ τ, Frozen τ → τ (M + transArg2BaseReg) = arg2Base)
    (hout : arg2Base + d.table.length + 2 = outBase)
    (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (houtBaseK : outBase ≤ K) :
    ClauseWriterBounded (loadAcceptParamProg d) M Jmax wpJ K S B 0 Frozen := by
  have rob : acceptOutBaseReg = 23 := rfl
  have ra2 : transArg2BaseReg = 22 := rfl
  intro τ wp hF h0 hwp hsep hslack hst ht
  have harg2 := hpins τ hF
  have hb : ProgramBoundedIn B τ (loadAcceptParamProg d) := by
    unfold loadAcceptParamProg
    refine programBoundedIn_ctlAssign_add_const B M acceptOutBaseReg transArg2BaseReg
      (d.table.length + 2) τ h0 (by omega) (by omega) (by rw [harg2]; omega)
  obtain ⟨hτ0, hτob, hτt, hτs⟩ := ctlAssign_add_const_preserves K S M
    acceptOutBaseReg transArg2BaseReg (d.table.length + 2) τ h0 (by omega)
    (by omega) ht hst (by rw [harg2]; omega) hKS
  have heval : (loadAcceptParamProg d).eval τ
      = (ctlAssign acceptOutBaseReg (.add (ctlCell transArg2BaseReg)
        (.const (d.table.length + 2)))).eval τ := by unfold loadAcceptParamProg; rfl
  rw [heval]
  exact ⟨hb, hτs, hτt⟩

/-- `loadEmitterTableProg`, as a `ClauseWriterBounded` at width `0`. -/
lemma clauseWriterBounded_loadEmitterTableProg
    (M Jmax K S B outBase : ℕ) (outIdx : List ℕ) (Frozen : Store → Prop)
    (hpins : ∀ τ, Frozen τ → τ (M + acceptOutBaseReg) = outBase)
    (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (htableBaseK : outBase + outIdx.length + 1 ≤ K) :
    ClauseWriterBounded (loadEmitterTableProg outIdx) M Jmax wpJ K S B 0 Frozen := by
  have rem : emTblJ = 14 := rfl
  have rob : acceptOutBaseReg = 23 := rfl
  intro τ wp hF h0 hwp hsep hslack hst ht
  have hob := hpins τ hF
  have hb : ProgramBoundedIn B τ (loadEmitterTableProg outIdx) := by
    unfold loadEmitterTableProg
    refine programBoundedIn_ctlAssign_add_const B M emTblJ acceptOutBaseReg
      (outIdx.length + 1) τ h0 (by omega) (by omega) (by rw [hob]; omega)
  obtain ⟨hτ0, hτem, hτt, hτs⟩ := ctlAssign_add_const_preserves K S M
    emTblJ acceptOutBaseReg (outIdx.length + 1) τ h0 (by omega)
    (by omega) ht hst (by rw [hob]; omega) hKS
  have heval : (loadEmitterTableProg outIdx).eval τ
      = (ctlAssign emTblJ (.add (ctlCell acceptOutBaseReg)
        (.const (outIdx.length + 1)))).eval τ := by unfold loadEmitterTableProg; rfl
  rw [heval]
  exact ⟨hb, hτs, hτt⟩

/-! ## Widths for the family clause lists the writer contracts already name

The five families' `ClauseWriter` correctness statements name their own
clause lists (`execUniquenessClausesAt`, `descBoundedPrefixInitClauses`,
`transClausesTripleFamily`, `execPersistClausesAt`, `descAcceptClauses`), so a
stage bound has to state a width bound for exactly those lists — not merely
some list the bounded proof happens to produce — for `clauseWriterBounded_seq`
to line up with the correctness-side `ClauseWriter` it is paired against. -/

/-- `execUniquenessClausesAt`'s width, matching `uniquenessFamilyProgParam`'s
own composition (`clauseWriterBounded_uniquenessFamilyProgParam`'s bound). -/
lemma execUniquenessClausesAt_width_le (nS W mS nC mC T : ℕ) (K : ℕ)
    (hnCK : nC ≤ K) (hmCK : mC ≤ K) (hWK : W ≤ K) :
    rowTableWidth (rowW (execUniquenessClausesAt (denseLayout nS W mS)
        (List.range nC) (List.range mC) W T))
      (execUniquenessClausesAt (denseLayout nS W mS) (List.range nC) (List.range mC)
        W T).length
      ≤ (T + 1) * (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * mC) + mC * (K * 6))) := by
  unfold execUniquenessClausesAt
  refine rowTableWidth_flatMap_range_le _ _ (T + 1) (fun t _ => ?_)
  rw [rowTableWidth_append_total, rowTableWidth_append_total]
  have hstate := exactlyOne_width_le K nC (fun q => (denseLayout nS W mS).state t q) hnCK
  have hhead := exactlyOne_width_le K W (fun p => (denseLayout nS W mS).head t p) hWK
  have hcell : rowTableWidth (rowW ((List.range W).flatMap fun p =>
      exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)))
      ((List.range W).flatMap fun p =>
        exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)).length
      ≤ W * ((2 + 2 * mC) + mC * (K * 6)) :=
    rowTableWidth_flatMap_range_le _ _ W
      (fun p _ => exactlyOne_width_le K mC (fun a => (denseLayout nS W mS).cell t p a) hmCK)
  omega

/-- `descBoundedPrefixInitClauses`'s width is under `initFamilyProgParam`'s own
bound, mirroring the append decomposition `initFamilyProgParam_writer_param` proves
correctness against. -/
lemma descBoundedPrefixInitClauses_width_le'
    (n W m T : ℕ) (d : TableauDescriptor) (prefIdx allowedIdx : List ℕ) (freeLen : ℕ) :
    rowTableWidth
      (rowW (descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T))
      (descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T).length
      ≤ 4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) := by
  have heq : descBoundedPrefixInitClauses (denseLayout n W m) d prefIdx freeLen allowedIdx W T
      = [descInitStateClause (denseLayout n W m) d] ++
        ([unitPos ((denseLayout n W m).head 0 (originIdx T))] ++
          (((List.range W).map fun p =>
              initWindowClause n W m T d.blankIdx prefIdx allowedIdx freeLen p) ++
            ((List.range freeLen).map fun i =>
              implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
                ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)))) := rfl
  rw [heq, rowTableWidth_append_total, rowTableWidth_append_total, rowTableWidth_append_total]
  have hstate : rowTableWidth (rowW [descInitStateClause (denseLayout n W m) d])
      [descInitStateClause (denseLayout n W m) d].length ≤ 4 := by
    have hcl : [descInitStateClause (denseLayout n W m) d].length = 1 := rfl
    rw [hcl, rowTableWidth_singleton]
    unfold descInitStateClause
    by_cases h : d.startState < d.numStates
    · simp [h, unitPos_len]
    · simp [h]
  have hhead : rowTableWidth (rowW [unitPos ((denseLayout n W m).head 0 (originIdx T))])
      [unitPos ((denseLayout n W m).head 0 (originIdx T))].length = 4 := by
    have hcl : [unitPos ((denseLayout n W m).head 0 (originIdx T))].length = 1 := rfl
    rw [hcl, rowTableWidth_singleton, unitPos_len]
  have hwin := init_window_map_width n W m T d.blankIdx prefIdx allowedIdx freeLen
  have htail : rowTableWidth
      (rowW ((List.range freeLen).map fun i =>
        implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)))
      ((List.range freeLen).map fun i =>
        implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)).length
      ≤ freeLen * 6 := by
    rw [List.length_map, List.length_range]
    refine (rowTableWidth_le_count_mul _ _ 2 (fun i hi => ?_)).trans (by omega)
    have heq2 : (rowW ((List.range freeLen).map fun i =>
        implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx))) i
        = (implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) d.blankIdx)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) d.blankIdx)).lits.length := by
      unfold rowW
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    rw [heq2]
    simp [implyPos]
  omega

/-- `transClausesTripleFamily`'s width, from `trans_t_width`'s per-`t` bound
composed over the outer `T` range. -/
lemma transClausesTripleFamily_width_le (nS W mS nC mC T : ℕ) (colk col1 col2 : List ℕ) :
    rowTableWidth (rowW (transClausesTripleFamily (denseLayout nS W mS) nC W mC T colk col1 col2))
      (transClausesTripleFamily (denseLayout nS W mS) nC W mC T colk col1 col2).length
      ≤ T * (W * (nC * (mC * 30))) := by
  unfold transClausesTripleFamily
  exact rowTableWidth_flatMap_range_le
    (fun t => (List.range W).flatMap fun p =>
      (List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0))
    (W * (nC * (mC * 30))) T
    (fun t _ => trans_t_width nS W mS nC mC t colk col1 col2)

/-- `execPersistClausesAt`'s width, from `persist_t_width`'s per-`t` bound
composed over the outer `T` range. -/
lemma execPersistClausesAt_width_le (n W m mC T K : ℕ) (hWK : W ≤ K) :
    rowTableWidth (rowW (execPersistClausesAt (denseLayout n W m) (List.range mC) W T))
      (execPersistClausesAt (denseLayout n W m) (List.range mC) W T).length
      ≤ T * (W * (K * (mC * 8) + K * (mC * 8))) := by
  unfold execPersistClausesAt
  exact rowTableWidth_flatMap_range_le
    (fun t => (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead) ((denseLayout n W m).cell t pCell a)
            ((denseLayout n W m).cell (t + 1) pCell a))
    (W * (K * (mC * 8) + K * (mC * 8))) T
    (fun t _ => persist_t_width n W m mC K t hWK)

/-- `descAcceptClauses`'s width, from `accept_outer_width`'s bound on the
window flatMap plus the halt row's own `atLeastOne` width. -/
lemma descAcceptClauses_width_le'
    (n W m T : ℕ) (d : TableauDescriptor) (outIdx : List ℕ) :
    rowTableWidth (rowW (descAcceptClauses (denseLayout n W m) d outIdx W T))
      (descAcceptClauses (denseLayout n W m) d outIdx W T).length
      ≤ W * (W * 6) + (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length) := by
  have heq : descAcceptClauses (denseLayout n W m) d outIdx W T
      = ((List.range W).flatMap fun pHead =>
          (List.range W).map fun p =>
            implyPos ((denseLayout n W m).head T pHead)
              ((denseLayout n W m).cell T p
                (natInitSymbol d.blankIdx outIdx ((p : ℤ) - (pHead : ℤ))))) ++
        [atLeastOne ((descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).map
          fun qi => (denseLayout n W m).state T qi)] := rfl
  rw [heq, rowTableWidth_append_total]
  have hout := accept_outer_width n W m T d.blankIdx outIdx
  have hhalt : rowTableWidth (rowW [atLeastOne ((descHaltStates d
        (natInitSymbol d.blankIdx outIdx 0)).map fun qi => (denseLayout n W m).state T qi)])
      [atLeastOne ((descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).map
        fun qi => (denseLayout n W m).state T qi)].length
      = 2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length := by
    have hcl : [atLeastOne ((descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).map
        fun qi => (denseLayout n W m).state T qi)].length = 1 := rfl
    rw [hcl, rowTableWidth_singleton, atLeastOne_lits_length, List.length_map]
  omega

/-! ## Stage 1: `uniquenessStageProgParam`

The stage *is* the family (no reload step), so its bound is the family bound
with the entry weakened from the pair of parameter pins to the whole
staged-table entry predicate `GeneratorTableFrozen`. -/

/-- `uniquenessStageProgParam`, as a `ClauseWriterBounded` under
`GeneratorTableFrozen`. -/
lemma clauseWriterBounded_uniquenessStageProgParam
    (M Jmax K S B W freeLen prefLen prefBase : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) (outBase : ℕ) (outIdx : List ℕ) (T : ℕ)
    (hplace : UniquenessParamPlacement Jmax uniquenessWReg uniquenessTReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvS : UniqEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hn : d.numStates + 1 ≤ B) (hm : d.numLetters + 1 ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hnCK : d.numStates ≤ K) (hmCK : d.numLetters ≤ K) (hWK : W ≤ K) (h2S : 2 ≤ S)
    (hTK1 : T + 1 ≤ K) :
    ClauseWriterBounded (uniquenessStageProgParam d) M Jmax wpJ K S B
      ((T + 1) * (((2 + 2 * d.numStates) + d.numStates * (K * 6))
        + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * d.numLetters) + d.numLetters * (K * 6))))
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase colk
        arg1Base col1 arg2Base col2 outBase outIdx) := by
  refine clauseWriterBounded_strengthen_entry _ M Jmax wpJ K S B _ _ _ ?_
    (clauseWriterBounded_uniquenessFamilyProgParam K S B M Jmax (d.numStates + 1) W (d.numLetters + 1)
      d.numStates d.numLetters T uniquenessWReg uniquenessTReg hplace hJ hK1
      (by norm_num [uniquenessWReg]) (by norm_num [uniquenessWReg]) (by norm_num [uniquenessTReg])
      hMB henvB henvS hn hm hSB hKB hKS hnCK hmCK hWK h2S hTK1)
  intro τ hF
  have hpins : PinsHold M (initParamPins0 initWReg initTReg initFreeLenReg initPrefLenReg
    initPrefBaseReg W T freeLen prefLen prefBase) τ := hF.1.1.1.1.1
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact hpins (initWReg, W) (by simp [initParamPins0])
  · exact hpins (initTReg, T) (by simp [initParamPins0])

/-! ## Stage 2: `initStageProgParam`

The family bound composes with `loadTransParamsProg` at width `0` via
`clauseWriterBounded_seq`, since both halves share `InitParamFrozen`.  The
result satisfies `InitParamFrozen`; the caller strengthens this entry predicate
to `GeneratorTableFrozen` when composing the full `.seq` chain. -/

/-- `initStageProgParam`, as a `ClauseWriterBounded` under `InitParamFrozen`
at the fixed init registers and descriptor-derived `n`/`m`. -/
lemma clauseWriterBounded_initStageProgParam
    (M Jmax K S B W T : ℕ) (d : TableauDescriptor)
    (allowedIdx prefIdx : List ℕ) (prefLen freeLen prefBase kindBase arg1Base arg2Base : ℕ)
    (hplace : InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg) (hJ : 24 ≤ Jmax)
    (hlen : prefLen = prefIdx.length)
    (hbase : M + initPrefBaseReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (henvB : InitEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvS : InitEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hn : d.numStates + 1 ≤ B) (hm : d.numLetters + 1 ≤ B)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (h2S : 2 ≤ S)
    (hblank : d.blankIdx ≤ K) (hallowed : ∀ v ∈ allowedIdx, v ≤ K)
    (hlenK : allowedIdx.length + 1 ≤ K) (hprefAllowed : ∀ v ∈ prefIdx, v ≤ K)
    (hWK : W ≤ K) (hfreeK : freeLen ≤ K) (hstart : d.startState ≤ K)
    (hkind : prefBase + prefLen + 2 = kindBase)
    (harg1 : kindBase + d.table.length + 2 = arg1Base)
    (harg2 : arg1Base + d.table.length + 2 = arg2Base)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (initStageProgParam d allowedIdx) M Jmax wpJ K S B
      (4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) + 0)
      (InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg
        W T freeLen prefLen prefBase prefIdx) := by
  have hfam := clauseWriterBounded_initFamilyProgParam M Jmax K S B (d.numStates + 1) W
    (d.numLetters + 1) T initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg d
    allowedIdx prefIdx prefLen freeLen prefBase hplace hJ hlen (by norm_num [initWReg])
    (by norm_num [initTReg]) (by norm_num [initFreeLenReg]) (by norm_num [initPrefLenReg])
    (by norm_num [initPrefBaseReg]) hbase hfit henvB henvS hn hm hMB hSB hKB hKS h2S hblank
    hallowed hlenK hprefAllowed hWK hfreeK hstart
  have hload := clauseWriterBounded_loadTransParamsProg M Jmax K S B prefLen prefBase kindBase
    arg1Base arg2Base d
    (InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg
      W T freeLen prefLen prefBase prefIdx)
    (fun τ hF => by
      have hpins := hF.1
      exact ⟨hpins (initPrefBaseReg, prefBase) (by simp [initParamPins0]),
        hpins (initPrefLenReg, prefLen) (by simp [initParamPins0])⟩)
    hkind harg1 harg2 hMB hKB hKS hkindBaseK harg1BaseK harg2BaseK
  have hwidfam := descBoundedPrefixInitClauses_width_le' (d.numStates + 1) W (d.numLetters + 1)
    T d prefIdx allowedIdx freeLen
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B _ 0 _ _
    (initFamilyProgParam_writer_param M Jmax (d.numStates + 1) W (d.numLetters + 1) T prefBase prefLen
      freeLen d prefIdx allowedIdx initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg hplace hlen hbase hfit)
    hwidfam hfam hload

/-! ## Stage 3: `transStageProgParam`

The family bound composes with `loadAcceptParamProg` at width `0`. -/

/-- `transStageProgParam`, as a `ClauseWriterBounded` under `TransParamFrozen`
at the fixed trans registers. -/
lemma clauseWriterBounded_transStageProgParam
    (M Jmax K S B W T outBase : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base : ℕ)
    (hplace : TransParamPlacement Jmax transWReg transTReg transKindBaseReg transArg1BaseReg
      transArg2BaseReg)
    (htable : TransParamTablePlacement M Jmax transArg2BaseReg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (henvB : TransEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvS : TransEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hnS : d.numStates + 1 ≤ B) (hmS : d.numLetters + 1 ≤ B)
    (hK1mC : K * d.numLetters + K + K ≤ B) (hmCB : d.numLetters ≤ B)
    (hmCK : d.numLetters ≤ K) (hnCK : d.numStates ≤ K)
    (hlenkB : (d.table.map transKind).length ≤ B) (hlen1B : (d.table.map transArg1).length ≤ B)
    (hlen2B : (d.table.map transArg2).length ≤ B)
    (hallowedk : ∀ v ∈ d.table.map transKind, v ≤ K)
    (hallowed1 : ∀ v ∈ d.table.map transArg1, v ≤ K)
    (hallowed2 : ∀ v ∈ d.table.map transArg2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : d.numStates ≤ B) (hWK : W ≤ K) (hTK1 : T + 1 ≤ K)
    (hout : arg2Base + d.table.length + 2 = outBase) (houtBaseK : outBase ≤ K) :
    ClauseWriterBounded (transStageProgParam d) M Jmax wpJ K S B
      (T * (W * (d.numStates * (d.numLetters * 30))) + 0)
      (TransParamFrozen M transWReg transTReg transKindBaseReg transArg1BaseReg
        transArg2BaseReg W T kindBase arg1Base arg2Base (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2)) := by
  have hfam := clauseWriterBounded_transFamilyProgParam M Jmax K S B (d.numStates + 1) W
    (d.numLetters + 1) d.numStates d.numLetters T d kindBase arg1Base arg2Base
    transWReg transTReg transKindBaseReg transArg1BaseReg transArg2BaseReg hplace htable
    hJ hK1 (by norm_num [transWReg]) (by norm_num [transWReg]) (by norm_num [transTReg])
    (by norm_num [transKindBaseReg]) (by norm_num [transArg1BaseReg])
    (by norm_num [transArg2BaseReg]) hMB hSB h4S h3S hKB hKS henvB henvS hnS hmS hK1mC hmCB
    hmCK hnCK hlenkB hlen1B hlen2B hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK
    harg2BaseK hnCB hWK hTK1
  have hload := clauseWriterBounded_loadAcceptParamProg M Jmax K S B arg2Base outBase d
    (TransParamFrozen M transWReg transTReg transKindBaseReg transArg1BaseReg
      transArg2BaseReg W T kindBase arg1Base arg2Base (d.table.map transKind)
      (d.table.map transArg1) (d.table.map transArg2))
    (fun τ hF => hF.1 (transArg2BaseReg, arg2Base) (by simp [transParamPins0]))
    hout hMB hKB hKS houtBaseK
  have hwidfam := transClausesTripleFamily_width_le (d.numStates + 1) W (d.numLetters + 1)
    d.numStates d.numLetters T (d.table.map transKind) (d.table.map transArg1)
    (d.table.map transArg2)
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B _ 0 _ _
    (transFamilyProgParam_writer_param M Jmax (d.numStates + 1) W (d.numLetters + 1) d.numStates
      d.numLetters T d kindBase arg1Base arg2Base transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg hplace htable)
    hwidfam hfam hload

/-! ## Stage 4: `persistStageProgParam`

The stage *is* the family (no reload step), matching stage 1's shape. -/

/-- `persistStageProgParam`, as a `ClauseWriterBounded` under
`AcceptParamFrozen`. -/
lemma clauseWriterBounded_persistStageProgParam
    (M Jmax K S B W T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (hplace : PersistParamPlacement Jmax persistWReg persistTReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvS : PersistEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hn : d.numStates + 1 ≤ B) (hm : d.numLetters + 1 ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : d.numLetters ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B) (hTK1 : T + 1 ≤ K) :
    ClauseWriterBounded (persistStageProgParam d) M Jmax wpJ K S B
      (T * (W * (K * (d.numLetters * 8) + K * (d.numLetters * 8))))
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) := by
  refine clauseWriterBounded_strengthen_entry _ M Jmax wpJ K S B _ _ _ ?_
    (clauseWriterBounded_persistFamilyProgParam K S B M Jmax (d.numStates + 1) (d.numLetters + 1)
      d.numLetters W T persistWReg persistTReg hplace hJ hK1
      (by norm_num [persistWReg]) (by norm_num [persistWReg]) (by norm_num [persistTReg])
      hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hWK hWB hTK1)
  intro τ hF
  have hpins : PinsHold M (acceptParamPins0 acceptWReg acceptTReg acceptOutBaseReg W T outBase) τ
    := hF.1
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact hpins (acceptWReg, W) (by simp [acceptParamPins0])
  · exact hpins (acceptTReg, T) (by simp [acceptParamPins0])

/-! ## Stage 5: `acceptStageProgParam`

The family bound composes with `loadEmitterTableProg` at width `0`. -/

/-- `acceptStageProgParam`, as a `ClauseWriterBounded` under
`AcceptParamFrozen` at the fixed accept registers. -/
lemma clauseWriterBounded_acceptStageProgParam
    (M Jmax K S B W T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (hplace : AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg) (hJ : 24 ≤ Jmax)
    (hbase : M + acceptOutBaseReg + 1 < outBase) (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hK1 : 1 ≤ K) (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hSB : S ≤ B)
    (hWK : W ≤ K)
    (henvB : AcceptEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvS : AcceptEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hn : d.numStates + 1 ≤ B) (hm : d.numLetters + 1 ≤ B)
    (hblank : d.blankIdx ≤ K)
    (houtAllowed : ∀ v ∈ outIdx, v ≤ K) (hlenB : outIdx.length ≤ B)
    (hqsK : ∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0), v ≤ K)
    (hqslenK : (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ K)
    (htableBaseK : outBase + outIdx.length + 1 ≤ K) :
    ClauseWriterBounded (acceptStageProgParam d outIdx) M Jmax wpJ K S B
      (W * (W * 6) + (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length) + 0)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) := by
  have hfam := clauseWriterBounded_acceptFamilyProgParam M Jmax K S B (d.numStates + 1) W
    (d.numLetters + 1) T outBase d outIdx acceptWReg acceptTReg acceptOutBaseReg hplace hJ
    hbase hfit hK1 (by norm_num [acceptWReg]) (by norm_num [acceptTReg])
    (by norm_num [acceptOutBaseReg]) hMB hKB hKS hSB hWK henvB henvS hn hm hblank houtAllowed
    hlenB hqsK hqslenK
  have hload := clauseWriterBounded_loadEmitterTableProg M Jmax K S B outBase outIdx
    (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
    (fun τ hF => hF.1 (acceptOutBaseReg, outBase) (by simp [acceptParamPins0]))
    hMB hKB hKS htableBaseK
  have hwidfam := descAcceptClauses_width_le' (d.numStates + 1) W (d.numLetters + 1) T d outIdx
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B _ 0 _ _
    (acceptFamilyProgParam_writer_param M Jmax (d.numStates + 1) W (d.numLetters + 1) T outBase d outIdx
      acceptWReg acceptTReg acceptOutBaseReg hplace hbase hfit)
    hwidfam hfam hload

/-! ## Generic stage composition -/

structure ClauseWriterBoundedStage
    (M Jmax wpJ K S B : ℕ) (Entry Mid : Store → Prop) where
  prog : Program
  wid : ℕ
  clauses : List Clause
  io : ClauseWriterIO prog M Jmax wpJ Entry Mid clauses
  width : rowTableWidth (rowW clauses) clauses.length ≤ wid
  bounded : ClauseWriterBounded prog M Jmax wpJ K S B wid Entry

structure ClauseWriterBoundedFinal
    (M Jmax wpJ K S B : ℕ) (Entry : Store → Prop) where
  prog : Program
  wid : ℕ
  bounded : ClauseWriterBounded prog M Jmax wpJ K S B wid Entry

def clauseWriterBoundedStage_append
    {Entry Mid Exit : Store → Prop}
    (left : ClauseWriterBoundedStage M Jmax wpJ K S B Entry Mid)
    (right : ClauseWriterBoundedStage M Jmax wpJ K S B Mid Exit) :
    ClauseWriterBoundedStage M Jmax wpJ K S B Entry Exit :=
  { prog := .seq left.prog right.prog
    wid := left.wid + right.wid
    clauses := left.clauses ++ right.clauses
    io := clauseWriterIO_seq left.prog right.prog M Jmax wpJ
      Entry Mid Exit left.clauses right.clauses left.io right.io
    width := by
      have hl := left.width
      have hr := right.width
      rw [rowTableWidth_append_total]
      omega
    bounded := clauseWriterBounded_seq_io left.prog right.prog M Jmax wpJ K S B
      left.wid right.wid Entry Mid left.clauses left.io left.width
      left.bounded right.bounded }

lemma clauseWriterBoundedStage_append_final
    {Entry Mid : Store → Prop}
    (left : ClauseWriterBoundedStage M Jmax wpJ K S B Entry Mid)
    (right : ClauseWriterBoundedFinal M Jmax wpJ K S B Mid) :
    ClauseWriterBounded (.seq left.prog right.prog) M Jmax wpJ K S B
      (left.wid + right.wid) Entry := by
  exact clauseWriterBounded_seq_io left.prog right.prog M Jmax wpJ K S B
    left.wid right.wid Entry Mid left.clauses left.io left.width
    left.bounded right.bounded

/-! ## Assembling `tableWriterProgParam`

Five stages, four `.seq` joins, and generic append/fold combinators
matching `tableWriterProgParam_io_param`'s own `.seq` chain on the correctness side
exactly (same order, same clause-list decomposition at every seam).  The
`GeneratorPlacement` argument supplies every stage's own placement structure
uniformly — its fields, not fresh hypotheses, are what discharge
`InitParamPlacement`/`TransParamTablePlacement`/etc at the fixed generator
registers. -/

/-- The fixed parameter-register placements used by all generator stages. -/
lemma fixed_generator_param_placements (Jmax : ℕ) (hJ : 24 ≤ Jmax) :
    UniquenessParamPlacement Jmax uniquenessWReg uniquenessTReg ∧
    InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg ∧
    TransParamPlacement Jmax transWReg transTReg transKindBaseReg transArg1BaseReg
      transArg2BaseReg ∧
    PersistParamPlacement Jmax persistWReg persistTReg ∧
    AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by unfold ctlJmax; omega, by norm_num [uniquenessWReg],
      by norm_num [uniquenessWReg]; omega, by norm_num [uniquenessTReg],
      by norm_num [uniquenessTReg]; omega,
      by norm_num [uniquenessWReg, uniquenessTReg]⟩
  · exact ⟨by unfold ctlJmax; omega, by norm_num [initWReg],
      by norm_num [initWReg, initTReg], by norm_num [initTReg, initFreeLenReg],
      by norm_num [initFreeLenReg, initPrefLenReg],
      by norm_num [initPrefLenReg, initPrefBaseReg], by norm_num [initPrefBaseReg]; omega⟩
  · exact ⟨by unfold ctlJmax; omega, by norm_num [transWReg],
      by norm_num [transWReg, transTReg], by norm_num [transTReg, transKindBaseReg],
      by norm_num [transKindBaseReg, transArg1BaseReg],
      by norm_num [transArg1BaseReg, transArg2BaseReg],
      by norm_num [transArg2BaseReg]; omega⟩
  · exact ⟨by unfold ctlJmax; omega, by norm_num [persistWReg],
      by norm_num [persistWReg]; omega, by norm_num [persistTReg],
      by norm_num [persistTReg]; omega, by norm_num [persistWReg, persistTReg]⟩
  · exact ⟨by unfold ctlJmax; omega, by norm_num [acceptWReg],
      by norm_num [acceptWReg, acceptTReg], by norm_num [acceptTReg, acceptOutBaseReg],
      by norm_num [acceptOutBaseReg]; omega⟩

/-- Packages the uniqueness program's boundedness, I/O, and width facts as a stage. -/
def clauseWriterBoundedStage_uniquenessStageProgParam
    (M Jmax K S B W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hnCK : d.numStates ≤ K) (hmCK : d.numLetters ≤ K) (hWK : W ≤ K)
    (hbounded : ClauseWriterBounded (uniquenessStageProgParam d) M Jmax wpJ K S B
      ((T + 1) * (((2 + 2 * d.numStates) + d.numStates * (K * 6))
        + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * d.numLetters) + d.numLetters * (K * 6))))
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)) :
    ClauseWriterBoundedStage M Jmax wpJ K S B
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx) :=
  { prog := uniquenessStageProgParam d
    wid := (T + 1) * (((2 + 2 * d.numStates) + d.numStates * (K * 6))
      + ((2 + 2 * W) + W * (K * 6))
      + W * ((2 + 2 * d.numLetters) + d.numLetters * (K * 6)))
    clauses := execUniquenessClausesAt
      (denseLayout (d.numStates + 1) W (d.numLetters + 1))
      (List.range d.numStates) (List.range d.numLetters) W T
    io := uniqueness_stage_io_param M Jmax W T freeLen prefLen prefBase kindBase
      arg1Base arg2Base outBase d prefIdx outIdx h
    width := execUniquenessClausesAt_width_le (d.numStates + 1) W
      (d.numLetters + 1) d.numStates d.numLetters T K hnCK hmCK hWK
    bounded := hbounded }

/-- Packages the initialization program's boundedness, I/O, and width facts as a stage. -/
def clauseWriterBoundedStage_initStageProgParam
    (M Jmax K S B W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hbounded : ClauseWriterBounded (initStageProgParam d allowedIdx) M Jmax wpJ K S B
      (4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) + 0)
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)) :
    ClauseWriterBoundedStage M Jmax wpJ K S B
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx)
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx) :=
  { prog := initStageProgParam d allowedIdx
    wid := 4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) + 0
    clauses := descBoundedPrefixInitClauses
      (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
      prefIdx freeLen allowedIdx W T
    io := init_stage_io_param M Jmax W T freeLen prefLen prefBase kindBase
      arg1Base arg2Base outBase d prefIdx allowedIdx outIdx h
    width := descBoundedPrefixInitClauses_width_le' (d.numStates + 1) W
      (d.numLetters + 1) T d prefIdx allowedIdx freeLen
    bounded := hbounded }

/-- Packages the transition program's boundedness, I/O, and width facts as a stage. -/
def clauseWriterBoundedStage_transStageProgParam
    (M Jmax K S B W T prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hbounded : ClauseWriterBounded (transStageProgParam d) M Jmax wpJ K S B
      (T * (W * (d.numStates * (d.numLetters * 30))) + 0)
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)) :
    ClauseWriterBoundedStage M Jmax wpJ K S B
      (TransWithOutFrozen M W T kindBase arg1Base arg2Base
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
        outBase outIdx)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) :=
  { prog := transStageProgParam d
    wid := T * (W * (d.numStates * (d.numLetters * 30))) + 0
    clauses := transClausesTripleFamily
      (denseLayout (d.numStates + 1) W (d.numLetters + 1))
      d.numStates W d.numLetters T (d.table.map transKind)
      (d.table.map transArg1) (d.table.map transArg2)
    io := trans_stage_io_param M Jmax W T prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx h
    width := transClausesTripleFamily_width_le (d.numStates + 1) W
      (d.numLetters + 1) d.numStates d.numLetters T
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
    bounded := hbounded }

/-- Packages the persistence program's boundedness, I/O, and width facts as a stage. -/
def clauseWriterBoundedStage_persistStageProgParam
    (M Jmax K S B W T prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hWK : W ≤ K)
    (hbounded : ClauseWriterBounded (persistStageProgParam d) M Jmax wpJ K S B
      (T * (W * (K * (d.numLetters * 8) + K * (d.numLetters * 8))))
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)) :
    ClauseWriterBoundedStage M Jmax wpJ K S B
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) :=
  { prog := persistStageProgParam d
    wid := T * (W * (K * (d.numLetters * 8) + K * (d.numLetters * 8)))
    clauses := execPersistClausesAt
      (denseLayout (d.numStates + 1) W (d.numLetters + 1))
      (List.range d.numLetters) W T
    io := persist_stage_io_param M Jmax W T prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx h
    width := execPersistClausesAt_width_le (d.numStates + 1) W
      (d.numLetters + 1) d.numLetters T K hWK
    bounded := hbounded }

/-- Packages the acceptance program's boundedness as the final stage. -/
def clauseWriterBoundedFinal_acceptStageProgParam
    (M Jmax K S B W T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (hbounded : ClauseWriterBounded (acceptStageProgParam d outIdx) M Jmax wpJ K S B
      (W * (W * 6) +
        (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length) + 0)
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)) :
    ClauseWriterBoundedFinal M Jmax wpJ K S B
      (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx) :=
  { prog := acceptStageProgParam d outIdx
    wid := W * (W * 6) +
      (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length) + 0
    bounded := hbounded }

/-- `tableWriterProgParam`, as a `ClauseWriterBounded` under
`GeneratorTableFrozen`. -/
lemma clauseWriterBounded_tableWriterProgParam
    (M Jmax K S B W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ)
    (h : GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
      arg2Base outBase d prefIdx outIdx)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hSB : S ≤ B) (h2S : 2 ≤ S) (h3S : 3 ≤ S) (h4S : 4 ≤ S)
    (henvUB : UniqEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvUS : UniqEnv K S (d.numStates + 1) (d.numLetters + 1))
    (henvIB : InitEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvIS : InitEnv K S (d.numStates + 1) (d.numLetters + 1))
    (henvTB : TransEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvTS : TransEnv K S (d.numStates + 1) (d.numLetters + 1))
    (henvPB : PersistEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvPS : PersistEnv K S (d.numStates + 1) (d.numLetters + 1))
    (henvAB : AcceptEnv K B (d.numStates + 1) (d.numLetters + 1))
    (henvAS : AcceptEnv K S (d.numStates + 1) (d.numLetters + 1))
    (hn : d.numStates + 1 ≤ B) (hm : d.numLetters + 1 ≤ B)
    (hnCK : d.numStates ≤ K) (hmCK : d.numLetters ≤ K) (hmCB : d.numLetters ≤ B)
    (hWK : W ≤ K) (hWB : W ≤ B)
    (hTK1 : T + 1 ≤ K)
    (hblank : d.blankIdx ≤ K) (hallowed : ∀ v ∈ allowedIdx, v ≤ K)
    (hlenK : allowedIdx.length + 1 ≤ K) (hprefAllowed : ∀ v ∈ prefIdx, v ≤ K)
    (hfreeK : freeLen ≤ K) (hstart : d.startState ≤ K)
    (hK1mC : K * d.numLetters + K + K ≤ B)
    (hlenkB : (d.table.map transKind).length ≤ B) (hlen1B : (d.table.map transArg1).length ≤ B)
    (hlen2B : (d.table.map transArg2).length ≤ B)
    (hallowedk : ∀ v ∈ d.table.map transKind, v ≤ K)
    (hallowed1 : ∀ v ∈ d.table.map transArg1, v ≤ K)
    (hallowed2 : ∀ v ∈ d.table.map transArg2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : d.numStates ≤ B)
    (houtAllowed : ∀ v ∈ outIdx, v ≤ K) (hlenB : outIdx.length ≤ B)
    (hqsK : ∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0), v ≤ K)
    (hqslenK : (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ K)
    (houtBaseK : outBase ≤ K)
    (htableBaseK : outBase + outIdx.length + 1 ≤ K) :
    ClauseWriterBounded (tableWriterProgParam d allowedIdx outIdx) M Jmax wpJ K S B
      (((((T + 1) * (((2 + 2 * d.numStates) + d.numStates * (K * 6))
          + ((2 + 2 * W) + W * (K * 6))
          + W * ((2 + 2 * d.numLetters) + d.numLetters * (K * 6)))
        + (4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) + 0))
        + (T * (W * (d.numStates * (d.numLetters * 30))) + 0))
        + (T * (W * (K * (d.numLetters * 8) + K * (d.numLetters * 8)))))
        + (W * (W * 6) + (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length)
          + 0))
      (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
        (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) outBase outIdx) := by
  obtain ⟨hplaceU, hplaceI, hplaceT, hplaceP, hplaceA⟩ :=
    fixed_generator_param_placements Jmax hJ
  have htableT : TransParamTablePlacement M Jmax transArg2BaseReg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length := by
    have hb := h.pref_base; have hp := h.pref_pos; have hk := h.kind_eq
    have h1 := h.arg1_eq; have h2 := h.arg2_eq; have ho := h.out_eq; have hf := h.out_fit
    simp only [List.length_map]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (simp only [transArg2BaseReg, initPrefBaseReg] at hb ⊢; omega)
  have hfitPref : prefBase + prefIdx.length ≤ M + Jmax := by
    have hlen := h.pref_len; have hk := h.kind_eq; have h1 := h.arg1_eq
    have h2 := h.arg2_eq; have ho := h.out_eq; have hf := h.out_fit
    omega
  have hbaseAccept : M + acceptOutBaseReg + 1 < outBase := by
    have hb := h.pref_base; have hp := h.pref_pos; have hk := h.kind_eq
    have h1 := h.arg1_eq; have h2 := h.arg2_eq; have ho := h.out_eq
    simp only [acceptOutBaseReg, initPrefBaseReg] at hb ⊢
    omega
  have hfitAccept : outBase + outIdx.length ≤ M + Jmax := h.out_fit
  have hU := clauseWriterBounded_uniquenessStageProgParam M Jmax K S B W freeLen prefLen
    prefBase d prefIdx kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
    arg2Base (d.table.map transArg2) outBase outIdx T
    hplaceU hJ hK1 hMB henvUB henvUS hn hm hSB hKB hKS hnCK hmCK hWK h2S hTK1
  have hI0 := clauseWriterBounded_initStageProgParam M Jmax K S B W T d allowedIdx prefIdx
    prefLen freeLen prefBase kindBase arg1Base arg2Base hplaceI hJ h.pref_len h.pref_base
    hfitPref henvIB henvIS hn hm hMB hSB hKB hKS h2S hblank hallowed hlenK hprefAllowed hWK
    hfreeK hstart h.kind_eq h.arg1_eq h.arg2_eq hkindBaseK harg1BaseK harg2BaseK
  have hI := clauseWriterBounded_strengthen_entry (initStageProgParam d allowedIdx)
    M Jmax wpJ K S B _
    (InitParamFrozen M initWReg initTReg initFreeLenReg initPrefLenReg initPrefBaseReg
      W T freeLen prefLen prefBase prefIdx)
    (GeneratorTableFrozen M W T freeLen prefLen prefBase prefIdx kindBase
      (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) outBase outIdx)
    (fun τ hF => hF.1.1.1.1) hI0
  have hT0 := clauseWriterBounded_transStageProgParam M Jmax K S B W T outBase d
    kindBase arg1Base arg2Base hplaceT htableT hJ hK1 hMB hSB h4S h3S hKB hKS
    henvTB henvTS hn hm hK1mC hmCB hmCK hnCK hlenkB hlen1B hlen2B hallowedk hallowed1
    hallowed2 hkindBaseK harg1BaseK harg2BaseK hnCB hWK hTK1 h.out_eq houtBaseK
  have hT := clauseWriterBounded_strengthen_entry (transStageProgParam d)
    M Jmax wpJ K S B _
    (TransParamFrozen M transWReg transTReg transKindBaseReg transArg1BaseReg
      transArg2BaseReg W T kindBase arg1Base arg2Base (d.table.map transKind)
      (d.table.map transArg1) (d.table.map transArg2))
    (TransWithOutFrozen M W T kindBase arg1Base arg2Base (d.table.map transKind)
      (d.table.map transArg1) (d.table.map transArg2) outBase outIdx)
    (fun τ hF => hF.1) hT0
  have hP := clauseWriterBounded_persistStageProgParam M Jmax K S B W T outBase d outIdx
    hplaceP hJ hK1 hMB henvPB henvPS hn hm hSB hKB hKS hmCK h3S hWK hWB hTK1
  have hP' := clauseWriterBounded_strengthen_entry (persistStageProgParam d)
    M Jmax wpJ K S B _
    (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
    (AcceptParamFrozen M acceptWReg acceptTReg acceptOutBaseReg W T outBase outIdx)
    (fun τ hF => hF) hP
  have hA := clauseWriterBounded_acceptStageProgParam M Jmax K S B W T outBase d outIdx
    hplaceA hJ hbaseAccept hfitAccept hK1 hMB hKB hKS hSB hWK henvAB henvAS hn hm hblank
    houtAllowed hlenB hqsK hqslenK htableBaseK
  let stageU := clauseWriterBoundedStage_uniquenessStageProgParam M Jmax K S B W T
    freeLen prefLen prefBase kindBase arg1Base arg2Base outBase d prefIdx outIdx h
    hnCK hmCK hWK hU
  let stageI := clauseWriterBoundedStage_initStageProgParam M Jmax K S B W T freeLen
    prefLen prefBase kindBase arg1Base arg2Base outBase d prefIdx allowedIdx outIdx h hI
  let stageT := clauseWriterBoundedStage_transStageProgParam M Jmax K S B W T prefLen
    prefBase kindBase arg1Base arg2Base outBase d prefIdx outIdx h hT
  let stageP := clauseWriterBoundedStage_persistStageProgParam M Jmax K S B W T prefLen
    prefBase kindBase arg1Base arg2Base outBase d prefIdx outIdx h hWK hP'
  let stageA := clauseWriterBoundedFinal_acceptStageProgParam M Jmax K S B W T outBase d
    outIdx hA
  let stageUI := clauseWriterBoundedStage_append stageU stageI
  let stageUIT := clauseWriterBoundedStage_append stageUI stageT
  let stageUITP := clauseWriterBoundedStage_append stageUIT stageP
  have htable := clauseWriterBoundedStage_append_final stageUITP stageA
  simpa [tableWriterProgParam, stageU, stageI, stageT, stageP, stageA,
    stageUI, stageUIT, stageUITP, clauseWriterBoundedStage_append,
    clauseWriterBoundedStage_uniquenessStageProgParam,
    clauseWriterBoundedStage_initStageProgParam,
    clauseWriterBoundedStage_transStageProgParam,
    clauseWriterBoundedStage_persistStageProgParam,
    clauseWriterBoundedFinal_acceptStageProgParam] using htable

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInit
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptExpr
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptParam
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyUniquenessCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransParam
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyPersistCheck
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableHandoff

/-!
The reduction's target lays variable numbers out for one more state and one more
letter than the descriptor enumerates, because the range certificate the
satisfiability equivalence rests on is stated at `stateList.length + 1`.  A
family writer that ties its layout stride to its own loop counts cannot reach
that target — it would need `d.numStates = d.numStates + 1`.

Two of the five families loop over the window and staged word rather than states
or letters, so their `n` and `m` stride arguments are independent of those loops.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The initial family already reaches the reduction's own stride: it loops over
the window and the free suffix, never over the state or letter sets. -/
lemma descBoundedPrefixInitClauses_writer_at_target_stride (M Jmax W T prefBase freeLen : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax) (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ∃ prog : Program, ClauseWriter prog M Jmax wpJ
      (PinsAndWord M ctlPins0 prefBase prefIdx)
      (descBoundedPrefixInitClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d prefIdx freeLen allowedIdx W T) :=
  ⟨_, initFamilyProg_writer M Jmax (d.numStates + 1) W (d.numLetters + 1) T prefBase freeLen d
    prefIdx allowedIdx hJ hbase hfit⟩

/-- The accept family likewise: its loops range over the window and the output
word, so its stride is free. -/
lemma descAcceptClauses_writer_at_target_stride (M Jmax W T outBase : ℕ)
    (d : TableauDescriptor) (outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax) (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ∃ prog : Program, ClauseWriter prog M Jmax wpJ
      (PinsAndWord M ctlPins0 outBase outIdx)
      (descAcceptClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d outIdx W T) :=
  ⟨_, acceptFamilyProg_writer M Jmax (d.numStates + 1) W (d.numLetters + 1) T outBase d outIdx
    hJ hbase hfit⟩

/-! ## The five together

Showing that each family has the target stride does not identify their
concatenation with the target clause list.  The statement below gives that
identification for all five families at once, so their writers compose for the
generator's clause list. -/

/-- The target CNF is the five families concatenated at the reduction's own
stride, so writers for the five compose into a writer for it. -/
lemma descTableauCNF_target_stride_split (W T freeLen : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) :
    (descTableauCNF (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx outIdx W T).clauses
      = descUniquenessClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T ++
        descBoundedPrefixInitClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
          prefIdx freeLen allowedIdx W T ++
        descTransClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T ++
        descPersistClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T ++
        descAcceptClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d outIdx W T :=
  rfl

/-- Every family has a writer at the reduction's own stride.  Bundling the five
existence statements records that the stride generalization is complete: no
family is left demanding that its layout stride equal its loop count. -/
lemma all_families_reach_target_stride (M Jmax W T prefBase freeLen : ℕ)
    (kindBase arg1Base arg2Base outBase : ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hpb : M + ctlJmax < prefBase) (hpf : prefBase + prefIdx.length ≤ M + Jmax)
    (hob : M + ctlJmax < outBase) (hof : outBase + outIdx.length ≤ M + Jmax)
    (hk : M + ctlJmax < kindBase) (h1 : M + ctlJmax < arg1Base)
    (h2 : M + ctlJmax < arg2Base) :
    (∃ p : Program, ClauseWriter p M ctlJmax wpJ (PinsHold M ctlPins0)
        (descUniquenessClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T)) ∧
    (∃ p : Program, ClauseWriter p M Jmax wpJ (PinsAndWord M ctlPins0 prefBase prefIdx)
        (descBoundedPrefixInitClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
          prefIdx freeLen allowedIdx W T)) ∧
    (∃ p : Program, ClauseWriter p M
        (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
          arg2Base (d.table.map transArg2)) wpJ
        (TransFrozen M ctlPins0 kindBase (d.table.map transKind) arg1Base
          (d.table.map transArg1) arg2Base (d.table.map transArg2))
        (descTransClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T)) ∧
    (∃ p : Program, ClauseWriter p M ctlJmax wpJ (PinsHold M ctlPins0)
        (descPersistClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T)) ∧
    (∃ p : Program, ClauseWriter p M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx)
        (descAcceptClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d outIdx W T)) :=
  ⟨uniqueness_writer_gen_at_target_stride M W T d,
    descBoundedPrefixInitClauses_writer_at_target_stride M Jmax W T prefBase freeLen d prefIdx allowedIdx
      hJ hpb hpf,
    trans_writer_gen_at_target_stride M W T kindBase arg1Base arg2Base d hk h1 h2,
    persist_writer_gen_at_target_stride M W T d,
    descAcceptClauses_writer_at_target_stride M Jmax W T outBase d outIdx hJ hob hof⟩

/-! ## The parameter cells the groups agree on

The five groups run in sequence over one store, so a run-time parameter staged
for the first has to be the same cell the last reads.  Each group states its own
placement predicate, which keeps the groups independent while they are built —
but nothing in those predicates forces two groups to pick the same cell, and a
disagreement would only surface when the concatenation is assembled.  These
lemmas pin the agreement down where it can be checked cheaply. -/

/-- The parameterized groups stage the window and time bound at the same two
cells, so one setup serves both. -/
lemma param_cells_agree :
    uniquenessWReg = persistWReg ∧ uniquenessTReg = persistTReg ∧
      uniquenessParamJmax = persistParamJmax :=
  ⟨rfl, rfl, rfl⟩

/-- The two placement predicates are interchangeable, so a single placement fact
discharges both groups' hypotheses. -/
lemma uniquenessParamPlacement_of_persist (Jmax wReg tReg : ℕ)
    (h : PersistParamPlacement Jmax wReg tReg) :
    UniquenessParamPlacement Jmax wReg tReg :=
  ⟨h.ctl_le, h.w_min, h.w_le, h.t_min, h.t_le, h.regs_ne⟩

lemma persistParamPlacement_of_uniqueness (Jmax wReg tReg : ℕ)
    (h : UniquenessParamPlacement Jmax wReg tReg) :
    PersistParamPlacement Jmax wReg tReg :=
  ⟨h.ctl_le, h.w_min, h.w_le, h.t_min, h.t_le, h.regs_ne⟩

/-- Every family placement is an ordered chain starting at the shared width and
time cells, so the two-cell persist/uniqueness view is the common prefix. -/
lemma persist_param_placement_of_ordered_wt (Jmax wReg tReg : ℕ)
    (hctl : ctlJmax ≤ Jmax) (hw : 15 ≤ wReg)
    (hwt : wReg < tReg) (htle : tReg ≤ Jmax) :
    PersistParamPlacement Jmax wReg tReg :=
  ⟨hctl, hw, by omega, by omega, by omega, by omega⟩

/-- The parameter cells sit above everything already allocated: the control block
the writers share, and the seven registers the emitter reads. -/
lemma param_cells_above_emitter :
    ctlJmax < emCurJ ∧ emTblJ < persistWReg ∧ persistWReg < persistTReg := by
  have h1 : ctlJmax = 7 := rfl
  have h2 : emCurJ = 8 := rfl
  have h3 : emTblJ = 14 := rfl
  have h4 : persistWReg = 15 := rfl
  have h5 : persistTReg = 16 := rfl
  omega

/-! ## Initial-family parameter placement and contracts -/

lemma init_param_cells_agree :
    initWReg = persistWReg ∧ initTReg = persistTReg ∧
      initWReg = uniquenessWReg ∧ initTReg = uniquenessTReg ∧
      initFreeLenReg = 17 ∧ initPrefLenReg = 18 ∧ initPrefBaseReg = 19 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma persist_param_placement_of_init (Jmax wReg tReg fReg plReg pbReg : ℕ)
    (h : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) :
    PersistParamPlacement Jmax wReg tReg := by
  have htf := h.t_f
  have hfp := h.f_pl
  have hpb := h.pl_pb
  have hle := h.pb_le
  exact persist_param_placement_of_ordered_wt Jmax wReg tReg h.ctl_le h.w_min h.w_t
    (by omega)

lemma uniqueness_param_placement_of_init (Jmax wReg tReg fReg plReg pbReg : ℕ)
    (h : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) :
    UniquenessParamPlacement Jmax wReg tReg :=
  uniquenessParamPlacement_of_persist Jmax wReg tReg
    (persist_param_placement_of_init Jmax wReg tReg fReg plReg pbReg h)

lemma init_param_placement_of_persist (Jmax : ℕ)
    (h : PersistParamPlacement Jmax initWReg initTReg)
    (hpb : initPrefBaseReg ≤ Jmax) :
    InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg := by
  refine ⟨h.ctl_le, h.w_min, ?_, ?_, ?_, ?_, hpb⟩ <;>
    simp [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg]

lemma init_param_placement_of_uniqueness (Jmax : ℕ)
    (h : UniquenessParamPlacement Jmax initWReg initTReg)
    (hpb : initPrefBaseReg ≤ Jmax) :
    InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg :=
  init_param_placement_of_persist Jmax
    (persistParamPlacement_of_uniqueness Jmax initWReg initTReg h) hpb

lemma init_param_cells_above_emitter :
    emTblJ < initWReg ∧ initWReg < initTReg ∧ initTReg < initFreeLenReg ∧
      initFreeLenReg < initPrefLenReg ∧ initPrefLenReg < initPrefBaseReg := by
  simp [emTblJ, initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg]

/-! ## Transition-family parameter placement and contracts -/

lemma trans_param_cells_agree :
    transWReg = persistWReg ∧ transTReg = persistTReg ∧
      transWReg = uniquenessWReg ∧ transTReg = uniquenessTReg ∧
      transWReg = initWReg ∧ transTReg = initTReg ∧
      transKindBaseReg = 20 ∧ transArg1BaseReg = 21 ∧ transArg2BaseReg = 22 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma persist_param_placement_of_trans
    (Jmax wReg tReg kbReg a1Reg a2Reg : ℕ)
    (h : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg) :
    PersistParamPlacement Jmax wReg tReg := by
  have htk := h.t_kb
  have hka := h.kb_a1
  have haa := h.a1_a2
  have hle := h.a2_le
  exact persist_param_placement_of_ordered_wt Jmax wReg tReg h.ctl_le h.w_min h.w_t
    (by omega)

lemma uniqueness_param_placement_of_trans
    (Jmax wReg tReg kbReg a1Reg a2Reg : ℕ)
    (h : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg) :
    UniquenessParamPlacement Jmax wReg tReg :=
  uniquenessParamPlacement_of_persist Jmax wReg tReg
    (persist_param_placement_of_trans Jmax wReg tReg kbReg a1Reg a2Reg h)

lemma trans_param_placement_of_persist (Jmax : ℕ)
    (h : PersistParamPlacement Jmax transWReg transTReg)
    (ha2 : transArg2BaseReg ≤ Jmax) :
    TransParamPlacement Jmax transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg := by
  refine ⟨h.ctl_le, h.w_min, ?_, ?_, ?_, ?_, ha2⟩ <;>
    simp [transWReg, transTReg, transKindBaseReg, transArg1BaseReg,
      transArg2BaseReg]

lemma trans_param_placement_of_uniqueness (Jmax : ℕ)
    (h : UniquenessParamPlacement Jmax transWReg transTReg)
    (ha2 : transArg2BaseReg ≤ Jmax) :
    TransParamPlacement Jmax transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg :=
  trans_param_placement_of_persist Jmax
    (persistParamPlacement_of_uniqueness Jmax transWReg transTReg h) ha2

lemma trans_param_placement_of_init (Jmax : ℕ)
    (h : InitParamPlacement Jmax transWReg transTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg)
    (ha2 : transArg2BaseReg ≤ Jmax) :
    TransParamPlacement Jmax transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg :=
  trans_param_placement_of_persist Jmax
    (persist_param_placement_of_init Jmax transWReg transTReg
      initFreeLenReg initPrefLenReg initPrefBaseReg h) ha2

lemma init_param_placement_of_trans (Jmax : ℕ)
    (h : TransParamPlacement Jmax initWReg initTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg) :
    InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg :=
  init_param_placement_of_persist Jmax
    (persist_param_placement_of_trans Jmax initWReg initTReg
      transKindBaseReg transArg1BaseReg transArg2BaseReg h)
    (Nat.le_trans (by simp [initPrefBaseReg, transArg2BaseReg]) h.a2_le)

/-! ## Accept-family parameter placement and contracts -/

lemma accept_param_cells_agree :
    acceptWReg = persistWReg ∧ acceptTReg = persistTReg ∧
      acceptWReg = uniquenessWReg ∧ acceptTReg = uniquenessTReg ∧
      acceptWReg = initWReg ∧ acceptTReg = initTReg ∧
      acceptWReg = transWReg ∧ acceptTReg = transTReg ∧
      acceptOutBaseReg = 23 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma persist_param_placement_of_accept
    (Jmax wReg tReg obReg : ℕ)
    (h : AcceptParamPlacement Jmax wReg tReg obReg) :
    PersistParamPlacement Jmax wReg tReg := by
  have hto := h.t_ob
  have hle := h.ob_le
  exact persist_param_placement_of_ordered_wt Jmax wReg tReg h.ctl_le h.w_min h.w_t
    (by omega)

lemma uniqueness_param_placement_of_accept
    (Jmax wReg tReg obReg : ℕ)
    (h : AcceptParamPlacement Jmax wReg tReg obReg) :
    UniquenessParamPlacement Jmax wReg tReg :=
  uniquenessParamPlacement_of_persist Jmax wReg tReg
    (persist_param_placement_of_accept Jmax wReg tReg obReg h)

lemma accept_param_placement_of_persist (Jmax : ℕ)
    (h : PersistParamPlacement Jmax acceptWReg acceptTReg)
    (hob : acceptOutBaseReg ≤ Jmax) :
    AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg := by
  refine ⟨h.ctl_le, h.w_min, ?_, ?_, hob⟩ <;>
    simp [acceptWReg, acceptTReg, acceptOutBaseReg]

lemma accept_param_placement_of_uniqueness (Jmax : ℕ)
    (h : UniquenessParamPlacement Jmax acceptWReg acceptTReg)
    (hob : acceptOutBaseReg ≤ Jmax) :
    AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg :=
  accept_param_placement_of_persist Jmax
    (persistParamPlacement_of_uniqueness Jmax acceptWReg acceptTReg h) hob

lemma accept_param_placement_of_init (Jmax : ℕ)
    (h : InitParamPlacement Jmax acceptWReg acceptTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg)
    (hob : acceptOutBaseReg ≤ Jmax) :
    AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg :=
  accept_param_placement_of_persist Jmax
    (persist_param_placement_of_init Jmax acceptWReg acceptTReg
      initFreeLenReg initPrefLenReg initPrefBaseReg h) hob

lemma accept_param_placement_of_trans (Jmax : ℕ)
    (h : TransParamPlacement Jmax acceptWReg acceptTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg)
    (hob : acceptOutBaseReg ≤ Jmax) :
    AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg :=
  accept_param_placement_of_persist Jmax
    (persist_param_placement_of_trans Jmax acceptWReg acceptTReg
      transKindBaseReg transArg1BaseReg transArg2BaseReg h) hob

lemma init_param_placement_of_accept (Jmax : ℕ)
    (h : AcceptParamPlacement Jmax initWReg initTReg acceptOutBaseReg) :
    InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg :=
  init_param_placement_of_persist Jmax
    (persist_param_placement_of_accept Jmax initWReg initTReg acceptOutBaseReg h)
    (Nat.le_trans (by simp [initPrefBaseReg, acceptOutBaseReg]) h.ob_le)

lemma trans_param_placement_of_accept (Jmax : ℕ)
    (h : AcceptParamPlacement Jmax transWReg transTReg acceptOutBaseReg) :
    TransParamPlacement Jmax transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg :=
  trans_param_placement_of_persist Jmax
    (persist_param_placement_of_accept Jmax transWReg transTReg acceptOutBaseReg h)
    (Nat.le_trans (by simp [transArg2BaseReg, acceptOutBaseReg]) h.ob_le)

lemma accept_param_cells_above_emitter :
    emTblJ < acceptWReg ∧ acceptWReg < acceptTReg ∧
      acceptTReg < acceptOutBaseReg := by
  simp [emTblJ, acceptWReg, acceptTReg, acceptOutBaseReg]

lemma init_writer_param_nonvacuous
    (M Jmax W T prefBase prefLen freeLen wReg tReg fReg plReg pbReg : ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx : List ℕ) (τ : Store) (wp : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (hF : InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase
      prefIdx τ) (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descBoundedPrefixInitClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d prefIdx freeLen
          allowedIdx W T) :=
  ⟨initFamilyProgParam (d.numStates + 1) (d.numLetters + 1) d allowedIdx
      wReg tReg fReg plReg pbReg,
    (initFamilyProgParam_writer_param M Jmax (d.numStates + 1) W (d.numLetters + 1) T
      prefBase prefLen freeLen d prefIdx allowedIdx wReg tReg fReg plReg pbReg
      hplace hlen hbase hfit τ wp hF h0 hw hsep).2.2.2.1⟩

def initParamCheckStore : Store := fun r =>
  if r = 1 then 40
  else if r = 15 then 2
  else if r = 16 then 3
  else if r = 17 then 1
  else if r = 18 then 1
  else if r = 19 then 21
  else if r = 20 then 1
  else 0

lemma init_param_check_frozen :
    InitParamFrozen 0 initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg 2 3 1 1 21 [0] initParamCheckStore := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [initParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [initParamCheckStore, initWReg, initTReg, initFreeLenReg,
        initPrefLenReg, initPrefBaseReg]
  · refine ⟨by norm_num [initParamCheckStore], fun k hk => ?_⟩
    have hk0 : k = 0 := by simpa using hk
    subst k
    norm_num [initParamCheckStore]

lemma init_writer_param_concrete_rows (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ∃ prog : Program, RowsWritten (prog.eval initParamCheckStore) 40
      (descBoundedPrefixInitClauses
        (denseLayout (d.numStates + 1) 2 (d.numLetters + 1)) d [0] 1 allowedIdx 2 3) := by
  have hplace : InitParamPlacement 30 initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg, ctlJmax]
  exact init_writer_param_nonvacuous 0 30 2 3 21 1 1 initWReg initTReg
    initFreeLenReg initPrefLenReg initPrefBaseReg d [0] allowedIdx initParamCheckStore 40
    hplace (by simp) (by simp [initPrefBaseReg]) (by simp) init_param_check_frozen
    (by norm_num [initParamCheckStore])
    (by norm_num [initParamCheckStore, wpJ]) (by norm_num)

lemma initFamilyProgParam_serves_any_parameters
    (M Jmax n m : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (wReg tReg fReg plReg pbReg : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (W₁ T₁ freeLen₁ prefLen₁ prefBase₁ W₂ T₂ freeLen₂ prefLen₂ prefBase₂ : ℕ)
    (prefIdx₁ prefIdx₂ : List ℕ)
    (hlen₁ : prefLen₁ = prefIdx₁.length) (hlen₂ : prefLen₂ = prefIdx₂.length)
    (hbase₁ : M + pbReg + 1 < prefBase₁) (hbase₂ : M + pbReg + 1 < prefBase₂)
    (hfit₁ : prefBase₁ + prefIdx₁.length ≤ M + Jmax)
    (hfit₂ : prefBase₂ + prefIdx₂.length ≤ M + Jmax) :
    ClauseWriter (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg)
        M Jmax wpJ
        (InitParamFrozen M wReg tReg fReg plReg pbReg W₁ T₁ freeLen₁ prefLen₁
          prefBase₁ prefIdx₁)
        (descBoundedPrefixInitClauses (denseLayout n W₁ m) d prefIdx₁ freeLen₁
          allowedIdx W₁ T₁) ∧
    ClauseWriter (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg)
        M Jmax wpJ
        (InitParamFrozen M wReg tReg fReg plReg pbReg W₂ T₂ freeLen₂ prefLen₂
          prefBase₂ prefIdx₂)
        (descBoundedPrefixInitClauses (denseLayout n W₂ m) d prefIdx₂ freeLen₂
          allowedIdx W₂ T₂) :=
  ⟨initFamilyProgParam_writer_param M Jmax n W₁ m T₁ prefBase₁ prefLen₁ freeLen₁ d
      prefIdx₁ allowedIdx wReg tReg fReg plReg pbReg hplace hlen₁ hbase₁ hfit₁,
    initFamilyProgParam_writer_param M Jmax n W₂ m T₂ prefBase₂ prefLen₂ freeLen₂ d
      prefIdx₂ allowedIdx wReg tReg fReg plReg pbReg hplace hlen₂ hbase₂ hfit₂⟩

lemma initFamilyProgParam_serves_distinct_parameters
    (n m : ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ClauseWriter
        (initFamilyProgParam n m d allowedIdx initWReg initTReg initFreeLenReg
          initPrefLenReg initPrefBaseReg)
        0 30 wpJ
        (InitParamFrozen 0 initWReg initTReg initFreeLenReg initPrefLenReg
          initPrefBaseReg 2 3 1 1 21 [0])
        (descBoundedPrefixInitClauses (denseLayout n 2 m) d [0] 1 allowedIdx 2 3) ∧
    ClauseWriter
        (initFamilyProgParam n m d allowedIdx initWReg initTReg initFreeLenReg
          initPrefLenReg initPrefBaseReg)
        0 30 wpJ
        (InitParamFrozen 0 initWReg initTReg initFreeLenReg initPrefLenReg
          initPrefBaseReg 4 5 2 2 25 [0, 1])
        (descBoundedPrefixInitClauses (denseLayout n 4 m) d [0, 1] 2 allowedIdx 4 5) := by
  have hplace : InitParamPlacement 30 initWReg initTReg initFreeLenReg initPrefLenReg
      initPrefBaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg, ctlJmax]
  exact initFamilyProgParam_serves_any_parameters 0 30 n m d allowedIdx initWReg initTReg
    initFreeLenReg initPrefLenReg initPrefBaseReg hplace
    2 3 1 1 21 4 5 2 2 25 [0] [0, 1]
    (by simp) (by simp) (by simp [initPrefBaseReg]) (by simp [initPrefBaseReg])
    (by simp) (by simp)

lemma trans_writer_param_nonvacuous
    (M Jmax nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base wReg tReg kbReg a1Reg a2Reg : ℕ)
    (τ : Store) (wp : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length)
    (hF : TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base (d.table.map transKind) (d.table.map transArg1)
      (d.table.map transArg2) τ)
    (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (transClausesTripleFamily (denseLayout nS W mS) nC W mC T
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) :=
  ⟨transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg,
    (transFamilyProgParam_writer_param M Jmax nS W mS nC mC T d kindBase arg1Base
      arg2Base wReg tReg kbReg a1Reg a2Reg hplace htable τ wp hF h0 hw hsep).2.2.2.1⟩

def transParamCheckStore : Store := fun r =>
  if r = 1 then 40
  else if r = 15 then 2
  else if r = 16 then 3
  else if r = 20 then 24
  else if r = 21 then 26
  else if r = 22 then 28
  else if r = 23 then 1
  else if r = 25 then 1
  else if r = 27 then 1
  else 0

lemma trans_param_check_frozen :
    TransParamFrozen 0 transWReg transTReg transKindBaseReg transArg1BaseReg
      transArg2BaseReg 2 3 24 26 28 (transCheckDesc.table.map transKind)
      (transCheckDesc.table.map transArg1) (transCheckDesc.table.map transArg2)
      transParamCheckStore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    simp only [transParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [transParamCheckStore, transWReg, transTReg, transKindBaseReg,
        transArg1BaseReg, transArg2BaseReg]
  · refine ⟨by norm_num [transParamCheckStore, transCheckDesc], fun k hk => ?_⟩
    simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [transParamCheckStore, transCheckDesc, transKind]
  · refine ⟨by norm_num [transParamCheckStore, transCheckDesc], fun k hk => ?_⟩
    simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [transParamCheckStore, transCheckDesc, transArg1]
  · refine ⟨by norm_num [transParamCheckStore, transCheckDesc], fun k hk => ?_⟩
    simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [transParamCheckStore, transCheckDesc, transArg2]

lemma trans_writer_param_concrete_rows :
    ∃ prog : Program, RowsWritten (prog.eval transParamCheckStore) 40
      (descTransClauses (denseLayout 2 2 2) transCheckDesc 2 3) := by
  have hplace : TransParamPlacement 30 transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [transWReg, transTReg, transKindBaseReg, transArg1BaseReg,
        transArg2BaseReg, ctlJmax]
  have htable : TransParamTablePlacement 0 30 transArg2BaseReg 24
      (transCheckDesc.table.map transKind).length 26
      (transCheckDesc.table.map transArg1).length 28
      (transCheckDesc.table.map transArg2).length := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      norm_num [transArg2BaseReg, transCheckDesc]
  have hw := transFamilyProgParam_writer_param_desc 0 30 2 3 transCheckDesc 24 26 28
    transWReg transTReg transKindBaseReg transArg1BaseReg transArg2BaseReg
    hplace htable
  exact ⟨_, (hw transParamCheckStore 40 trans_param_check_frozen
    (by norm_num [transParamCheckStore])
    (by norm_num [transParamCheckStore, wpJ]) (by norm_num)).2.2.2.1⟩

lemma transFamilyProgParam_serves_any_parameters
    (M Jmax nS mS nC mC : ℕ) (d : TableauDescriptor)
    (wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (W₁ T₁ kindBase₁ arg1Base₁ arg2Base₁ W₂ T₂ kindBase₂ arg1Base₂ arg2Base₂ : ℕ)
    (htable₁ : TransParamTablePlacement M Jmax a2Reg kindBase₁
      (d.table.map transKind).length arg1Base₁ (d.table.map transArg1).length
      arg2Base₁ (d.table.map transArg2).length)
    (htable₂ : TransParamTablePlacement M Jmax a2Reg kindBase₂
      (d.table.map transKind).length arg1Base₂ (d.table.map transArg1).length
      arg2Base₂ (d.table.map transArg2).length) :
    ClauseWriter (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg)
        M Jmax wpJ
        (TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W₁ T₁
          kindBase₁ arg1Base₁ arg2Base₁ (d.table.map transKind)
          (d.table.map transArg1) (d.table.map transArg2))
        (transClausesTripleFamily (denseLayout nS W₁ mS) nC W₁ mC T₁
          (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) ∧
    ClauseWriter (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg)
        M Jmax wpJ
        (TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W₂ T₂
          kindBase₂ arg1Base₂ arg2Base₂ (d.table.map transKind)
          (d.table.map transArg1) (d.table.map transArg2))
        (transClausesTripleFamily (denseLayout nS W₂ mS) nC W₂ mC T₂
          (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) :=
  ⟨transFamilyProgParam_writer_param M Jmax nS W₁ mS nC mC T₁ d kindBase₁ arg1Base₁
      arg2Base₁ wReg tReg kbReg a1Reg a2Reg hplace htable₁,
    transFamilyProgParam_writer_param M Jmax nS W₂ mS nC mC T₂ d kindBase₂ arg1Base₂
      arg2Base₂ wReg tReg kbReg a1Reg a2Reg hplace htable₂⟩

lemma transFamilyProgParam_serves_distinct_parameters (nS mS nC mC : ℕ) :
    ClauseWriter
        (transFamilyProgParam nS mS nC mC transCheckDesc transWReg transTReg
          transKindBaseReg transArg1BaseReg transArg2BaseReg)
        0 40 wpJ
        (TransParamFrozen 0 transWReg transTReg transKindBaseReg transArg1BaseReg
          transArg2BaseReg 2 3 24 26 28 (transCheckDesc.table.map transKind)
          (transCheckDesc.table.map transArg1) (transCheckDesc.table.map transArg2))
        (transClausesTripleFamily (denseLayout nS 2 mS) nC 2 mC 3
          (transCheckDesc.table.map transKind) (transCheckDesc.table.map transArg1)
          (transCheckDesc.table.map transArg2)) ∧
    ClauseWriter
        (transFamilyProgParam nS mS nC mC transCheckDesc transWReg transTReg
          transKindBaseReg transArg1BaseReg transArg2BaseReg)
        0 40 wpJ
        (TransParamFrozen 0 transWReg transTReg transKindBaseReg transArg1BaseReg
          transArg2BaseReg 4 5 31 33 35 (transCheckDesc.table.map transKind)
          (transCheckDesc.table.map transArg1) (transCheckDesc.table.map transArg2))
        (transClausesTripleFamily (denseLayout nS 4 mS) nC 4 mC 5
          (transCheckDesc.table.map transKind) (transCheckDesc.table.map transArg1)
          (transCheckDesc.table.map transArg2)) := by
  have hplace : TransParamPlacement 40 transWReg transTReg transKindBaseReg
      transArg1BaseReg transArg2BaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [transWReg, transTReg, transKindBaseReg, transArg1BaseReg,
        transArg2BaseReg, ctlJmax]
  have htable₁ : TransParamTablePlacement 0 40 transArg2BaseReg 24
      (transCheckDesc.table.map transKind).length 26
      (transCheckDesc.table.map transArg1).length 28
      (transCheckDesc.table.map transArg2).length := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      norm_num [transArg2BaseReg, transCheckDesc]
  have htable₂ : TransParamTablePlacement 0 40 transArg2BaseReg 31
      (transCheckDesc.table.map transKind).length 33
      (transCheckDesc.table.map transArg1).length 35
      (transCheckDesc.table.map transArg2).length := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      norm_num [transArg2BaseReg, transCheckDesc]
  exact transFamilyProgParam_serves_any_parameters 0 40 nS mS nC mC transCheckDesc
    transWReg transTReg transKindBaseReg transArg1BaseReg transArg2BaseReg hplace
    2 3 24 26 28 4 5 31 33 35 htable₁ htable₂

/-! ## Accept-family parameter contracts -/

lemma accept_writer_param_nonvacuous
    (M Jmax n W m T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (wReg tReg obReg : ℕ) (τ : Store) (wp : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hF : AcceptParamFrozen M wReg tReg obReg W T outBase outIdx τ)
    (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descAcceptClauses (denseLayout n W m) d outIdx W T) :=
  ⟨acceptFamilyProgParam n m d outIdx wReg tReg obReg,
    (acceptFamilyProgParam_writer_param M Jmax n W m T outBase d outIdx wReg tReg obReg
      hplace hbase hfit τ wp hF h0 hw hsep).2.2.2.1⟩

def acceptParamCheckStore : Store := fun r =>
  if r = 1 then 40
  else if r = 15 then 2
  else if r = 16 then 3
  else if r = 23 then 25
  else if r = 24 then 1
  else 0

lemma accept_param_check_frozen :
    AcceptParamFrozen 0 acceptWReg acceptTReg acceptOutBaseReg
      2 3 25 [0] acceptParamCheckStore := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [acceptParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      norm_num [acceptParamCheckStore, acceptWReg, acceptTReg, acceptOutBaseReg]
  · refine ⟨by norm_num [acceptParamCheckStore], fun k hk => ?_⟩
    have hk0 : k = 0 := by simpa using hk
    subst k
    norm_num [acceptParamCheckStore]

lemma accept_writer_param_concrete_rows :
    ∃ prog : Program, RowsWritten (prog.eval acceptParamCheckStore) 40
      (descAcceptClauses (denseLayout 2 2 2) transCheckDesc [0] 2 3) := by
  have hplace : AcceptParamPlacement 30 acceptWReg acceptTReg acceptOutBaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [acceptWReg, acceptTReg, acceptOutBaseReg, ctlJmax]
  exact accept_writer_param_nonvacuous 0 30 2 2 2 3 25 transCheckDesc [0]
    acceptWReg acceptTReg acceptOutBaseReg acceptParamCheckStore 40 hplace
    (by norm_num [acceptOutBaseReg]) (by norm_num) accept_param_check_frozen
    (by norm_num [acceptParamCheckStore])
    (by norm_num [acceptParamCheckStore, wpJ]) (by norm_num)

lemma acceptFamilyProgParam_serves_any_parameters
    (M Jmax n m : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (wReg tReg obReg : ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (W₁ T₁ outBase₁ W₂ T₂ outBase₂ : ℕ)
    (hbase₁ : M + obReg + 1 < outBase₁)
    (hbase₂ : M + obReg + 1 < outBase₂)
    (hfit₁ : outBase₁ + outIdx.length ≤ M + Jmax)
    (hfit₂ : outBase₂ + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptFamilyProgParam n m d outIdx wReg tReg obReg)
        M Jmax wpJ
        (AcceptParamFrozen M wReg tReg obReg W₁ T₁ outBase₁ outIdx)
        (descAcceptClauses (denseLayout n W₁ m) d outIdx W₁ T₁) ∧
    ClauseWriter (acceptFamilyProgParam n m d outIdx wReg tReg obReg)
        M Jmax wpJ
        (AcceptParamFrozen M wReg tReg obReg W₂ T₂ outBase₂ outIdx)
        (descAcceptClauses (denseLayout n W₂ m) d outIdx W₂ T₂) :=
  ⟨acceptFamilyProgParam_writer_param M Jmax n W₁ m T₁ outBase₁ d outIdx
      wReg tReg obReg hplace hbase₁ hfit₁,
    acceptFamilyProgParam_writer_param M Jmax n W₂ m T₂ outBase₂ d outIdx
      wReg tReg obReg hplace hbase₂ hfit₂⟩

lemma acceptFamilyProgParam_serves_distinct_parameters (n m : ℕ) :
    ClauseWriter
        (acceptFamilyProgParam n m transCheckDesc [0]
          acceptWReg acceptTReg acceptOutBaseReg)
        0 40 wpJ
        (AcceptParamFrozen 0 acceptWReg acceptTReg acceptOutBaseReg 2 3 25 [0])
        (descAcceptClauses (denseLayout n 2 m) transCheckDesc [0] 2 3) ∧
    ClauseWriter
        (acceptFamilyProgParam n m transCheckDesc [0]
          acceptWReg acceptTReg acceptOutBaseReg)
        0 40 wpJ
        (AcceptParamFrozen 0 acceptWReg acceptTReg acceptOutBaseReg 4 5 30 [0])
        (descAcceptClauses (denseLayout n 4 m) transCheckDesc [0] 4 5) := by
  have hplace : AcceptParamPlacement 40 acceptWReg acceptTReg acceptOutBaseReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [acceptWReg, acceptTReg, acceptOutBaseReg, ctlJmax]
  exact acceptFamilyProgParam_serves_any_parameters 0 40 n m transCheckDesc [0]
    acceptWReg acceptTReg acceptOutBaseReg hplace 2 3 25 4 5 30
    (by norm_num [acceptOutBaseReg]) (by norm_num [acceptOutBaseReg])
    (by norm_num) (by norm_num)

/-! ## The whole cell map

Each group states which cells it uses, and pairwise agreement is checked above.
The concatenation also needs one store with no overlap across all five groups:
two groups may agree on shared cells while assigning different values to a cell
named by only one of them.

The ordered allocation below makes the global separation explicit.  Its strict
inequalities show that the control block, emitter registers, and run-time
parameter cells occupy disjoint positions. -/

/-- The generator's control region, in order and without overlap: the writers'
control block, the emitter's registers, then one cell per run-time parameter. -/
lemma param_cell_map_is_ordered :
    ctlJmax < emCurJ ∧ emTblJ < persistWReg ∧ persistWReg < persistTReg ∧
      persistTReg < initFreeLenReg ∧ initFreeLenReg < initPrefLenReg ∧
      initPrefLenReg < initPrefBaseReg ∧ initPrefBaseReg < transKindBaseReg ∧
      transKindBaseReg < transArg1BaseReg ∧ transArg1BaseReg < transArg2BaseReg ∧
      transArg2BaseReg < acceptOutBaseReg := by
  have e1 : ctlJmax = 7 := rfl
  have e2 : emCurJ = 8 := rfl
  have e3 : emTblJ = 14 := rfl
  have e4 : persistWReg = 15 := rfl
  have e5 : persistTReg = 16 := rfl
  have e6 : initFreeLenReg = 17 := rfl
  have e7 : initPrefLenReg = 18 := rfl
  have e8 : initPrefBaseReg = 19 := rfl
  have e9 : transKindBaseReg = 20 := rfl
  have e10 : transArg1BaseReg = 21 := rfl
  have e11 : transArg2BaseReg = 22 := rfl
  have e12 : acceptOutBaseReg = 23 := rfl
  omega

/-- All five groups stage the window and the time bound at the same two cells,
so one setup serves the whole generator. -/
lemma all_groups_share_wt_cells :
    (persistWReg = uniquenessWReg ∧ persistWReg = initWReg ∧
      persistWReg = transWReg ∧ persistWReg = acceptWReg) ∧
    (persistTReg = uniquenessTReg ∧ persistTReg = initTReg ∧
      persistTReg = transTReg ∧ persistTReg = acceptTReg) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

end NPComplete.CookLevin

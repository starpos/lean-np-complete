module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitExpr
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptExpr

/-!
The initial family's first two clauses and its trailing blank-propagation loop
are independent of the three-way window test: the start-state guard is decided
when the producer is chosen, the head clause is a constant `unitPos`, and the
tail is a plain `forN` of `implyPos`.  Those three pieces therefore run as
writers under the same word-carrying `Frozen` the middle loop will use, without
an `ifNZ`.

The leaf they share, `clauseWriter_clause_word`, writes one clause whose literal
expressions may read the word, so these pieces name a clause without
re-unfolding `writeClauseProg`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A clause writer over a word-carrying `Frozen`, whose literal expressions may
    read anything below the entry write pointer. -/
lemma clauseWriter_clause_word (M Jmax base : ℕ) (xs : List ℕ)
    (lits : List (Expr × Expr)) (pins : List (ℕ × ℕ)) (c : Clause)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < base)
    (hfit : base + xs.length ≤ M + Jmax)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ)
    (hdep : ∀ q ∈ lits, ∀ (bound : ℕ) (σ σ' : Store), σ 0 = M → σ' 0 = M →
      M + ctlJmax < bound → WordBelow base xs.length bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ)
    (hlen : c.lits.length = lits.length)
    (hlit : ∀ (τ : Store) (k : ℕ), PinsAndWord M pins base xs τ → τ 0 = M →
      k < lits.length →
      (lits.getD k defLit).1.eval τ = (if litTag (c.lits.getD k default) then 1 else 0) ∧
      (lits.getD k defLit).2.eval τ = litVar (c.lits.getD k default)) :
    ClauseWriter (writeClauseProg wpJ lits) M Jmax wpJ
      (PinsAndWord M pins base xs) [c] := by
  intro τ wp hF h0 hw hsep
  have hmax : ctlJmax = 7 := rfl
  have hwp1 : wpJ = 1 := rfl
  have hpins : PinsHold M pins τ := hF.1
  have hword : WordAt τ base xs := hF.2
  have hctlwp : M + ctlJmax < wp := by omega
  have hbelow : WordBelow base xs.length wp := ⟨by omega, by omega⟩
  have hinv : ∀ q ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ :=
    fun q hq σ σ' hσ hσ' hagree => hdep q hq wp σ σ' hσ hσ' hctlwp hbelow hagree
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ lits M wp τ (by omega) h0 hw (by omega) hinv
  set σ2 := (writeClauseProg wpJ lits).eval τ
  have hwidth : rowTableWidth (rowW [c]) [c].length = 2 + 2 * lits.length := by
    rw [show [c].length = 1 from rfl, rowTableWidth_singleton, hlen]
  refine ⟨⟨?_, ?_⟩, w4, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hpin q hq
    rw [w5 (M + q.1) (by omega) (by omega)]
    exact hpins q hq
  · exact accept_word_preserved M Jmax base wp xs τ _ hbase hfit hJ hsep hword w5
  · rw [w3, hwidth]; omega
  · refine rowsWritten_singleton σ2 wp c ?_ ?_ ?_
    · rw [w1, hlen]
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).1]
      exact (hlit τ k hF h0 hk).1
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).2]
      exact (hlit τ k hF h0 hk).2
  · intro r hr1 hr2
    exact w5 r hr1 (by rcases hr2 with h | h <;> omega)

def initStateProg (n W m : ℕ) (d : TableauDescriptor) : Program :=
  if d.startState < d.numStates then
    writeClauseProg wpJ (unitPosLits (initStateE n W m d.startState))
  else writeClauseProg wpJ []

lemma init_state_writer (M Jmax n W m prefBase : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initStateProg n W m d) M Jmax wpJ
      (PinsAndWord M ctlPins0 prefBase prefIdx)
      [descInitStateClause (denseLayout n W m) d] := by
  have hpin : ∀ q ∈ ctlPins0, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ :=
    fun q hq => absurd hq (List.not_mem_nil)
  unfold initStateProg descInitStateClause
  by_cases hst : d.startState < d.numStates
  · simp only [ite_eq_left hst]
    exact clauseWriter_unitPos_word M Jmax prefBase prefIdx
      (initStateE n W m d.startState)
      ((denseLayout n W m).state 0 d.startState) ctlPins0
      hJ hbase hfit hpin
      (fun _ σ σ' _ _ _ _ _ => initStateE_frame n W m d.startState σ σ')
      (fun τ _ _ => initStateE_value n W m d.startState τ)
  · simp only [ite_eq_right hst]
    exact clauseWriter_clause_word M Jmax prefBase prefIdx [] ctlPins0 ⟨[]⟩
      hJ hbase hfit hpin
      (fun q hq => absurd hq (List.not_mem_nil)) rfl
      (fun _ k _ _ hk => by cases hk)

def initHeadProg (n W m T : ℕ) : Program :=
  writeClauseProg wpJ (unitPosLits (initHeadE n W m T))

lemma init_head_writer (M Jmax n W m T prefBase : ℕ) (prefIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initHeadProg n W m T) M Jmax wpJ
      (PinsAndWord M ctlPins0 prefBase prefIdx)
      [unitPos ((denseLayout n W m).head 0 (originIdx T))] := by
  have hpin : ∀ q ∈ ctlPins0, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ :=
    fun q hq => absurd hq (List.not_mem_nil)
  unfold initHeadProg
  exact clauseWriter_unitPos_word M Jmax prefBase prefIdx
    (initHeadE n W m T) ((denseLayout n W m).head 0 (originIdx T)) ctlPins0
    hJ hbase hfit hpin
    (fun _ σ σ' _ _ _ _ _ => initHeadE_frame n W m T σ σ')
    (fun τ _ _ => initHeadE_value n W m T τ)

/-- `cell 0 (T + prefLen + i) blank`, over the level counter. -/
def initTailCellE (n W m T prefLen blank : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.const 0)
    (.add (.const (T + prefLen)) (ctlCell lvJ0)) (.const blank)

/-- The same cell one position to the right. -/
def initTailCellNextE (n W m T prefLen blank : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.const 0)
    (.add (.add (.const (T + prefLen)) (ctlCell lvJ0)) (.const 1)) (.const blank)

lemma initTailCellE_frame (M n W m T prefLen blank : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initTailCellE n W m T prefLen blank).eval σ'
      = (initTailCellE n W m T prefLen blank).eval σ := by
  unfold initTailCellE
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree]

lemma initTailCellNextE_frame (M n W m T prefLen blank : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initTailCellNextE n W m T prefLen blank).eval σ'
      = (initTailCellNextE n W m T prefLen blank).eval σ := by
  unfold initTailCellNextE
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree]

lemma initTailCellE_value (M n W m T prefLen blank i : ℕ) (τ : Store)
    (h0 : τ 0 = M) (hi : τ (M + lvJ0) = i) :
    (initTailCellE n W m T prefLen blank).eval τ
      = (denseLayout n W m).cell 0 (T + prefLen + i) blank := by
  have e0 : (ctlCell lvJ0).eval τ = i := by rw [ctlCell_eval, h0]; exact hi
  unfold initTailCellE
  rw [denseCellE_eval]
  simp only [Expr.eval, e0]

lemma initTailCellNextE_value (M n W m T prefLen blank i : ℕ) (τ : Store)
    (h0 : τ 0 = M) (hi : τ (M + lvJ0) = i) :
    (initTailCellNextE n W m T prefLen blank).eval τ
      = (denseLayout n W m).cell 0 (T + prefLen + i + 1) blank := by
  have e0 : (ctlCell lvJ0).eval τ = i := by rw [ctlCell_eval, h0]; exact hi
  unfold initTailCellNextE
  rw [denseCellE_eval]
  simp only [Expr.eval, e0]

lemma init_tail_leaf_writer (M Jmax n W m T blank prefBase i : ℕ)
    (prefIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (writeClauseProg wpJ
        (implyPosLits (initTailCellE n W m T prefIdx.length blank)
          (initTailCellNextE n W m T prefIdx.length blank)))
      M Jmax wpJ (PinsAndWord M (ctlPins1 i) prefBase prefIdx)
      [implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
        ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)] := by
  have hpin : ∀ q ∈ ctlPins1 i, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ := by
    intro q hq
    simp only [ctlPins1, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega,
      by unfold lvJ0 wpJ; omega⟩
  refine clauseWriter_clause_word M Jmax prefBase prefIdx
    (implyPosLits (initTailCellE n W m T prefIdx.length blank)
      (initTailCellNextE n W m T prefIdx.length blank))
    (ctlPins1 i)
    (implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
      ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank))
    hJ hbase hfit hpin ?_ ?_ ?_
  · intro q hq bound σ σ' hσ hσ' hbound _hw hagree
    have hctl : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
      fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
    simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨rfl, initTailCellE_frame M n W m T prefIdx.length blank σ σ' hσ hσ' hctl⟩
    · exact ⟨rfl, initTailCellNextE_frame M n W m T prefIdx.length blank σ σ' hσ hσ' hctl⟩
  · rw [implyPos_len, implyPosLits_length]
  · intro τ k hF h0 hk
    have hpins : PinsHold M (ctlPins1 i) τ := hF.1
    have hi : τ (M + lvJ0) = i :=
      pinsHold_head M (lvJ0, i) [] τ (by simpa [ctlPins1] using hpins)
    rw [implyPosLits_length] at hk
    interval_cases k
    · rw [implyPosLits_get0]
      exact ⟨rfl, by
        rw [implyPos_var0]
        exact initTailCellE_value M n W m T prefIdx.length blank i τ h0 hi⟩
    · rw [implyPosLits_get1]
      exact ⟨rfl, by
        rw [implyPos_var1]
        exact initTailCellNextE_value M n W m T prefIdx.length blank i τ h0 hi⟩

def initTailProg (n W m T prefLen blank freeLen : ℕ) : Program :=
  loopProg lvJ0 (.const freeLen)
    (.seq (writeClauseProg wpJ
        (implyPosLits (initTailCellE n W m T prefLen blank)
          (initTailCellNextE n W m T prefLen blank)))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma init_tail_loop_writer (M Jmax n W m T blank prefBase freeLen : ℕ)
    (prefIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initTailProg n W m T prefIdx.length blank freeLen)
      M Jmax wpJ (PinsAndWord M ctlPins0 prefBase prefIdx)
      ((List.range freeLen).map fun i =>
        implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)) := by
  have hpin : ∀ q ∈ ctlPins0, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ0 ∧ q.1 ≠ wpJ :=
    fun q hq => absurd hq (List.not_mem_nil)
  rw [map_eq_flatMap_singleton]
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ0 ctlPins0 _ (.const freeLen) freeLen
    prefBase prefIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0 ctlPins0 _
    prefBase prefIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase
    (fun i => by
      have hpins : (lvJ0, i) :: ctlPins0 = ctlPins1 i := rfl
      rw [hpins]
      exact init_tail_leaf_writer M Jmax n W m T blank prefBase i prefIdx
        hJ hbase hfit)

/-! ## Run-time-parameter state, head, and suffix writers -/

lemma clause_writer_clause_word_wide (M Jmax base : ℕ) (xs : List ℕ)
    (lits : List (Expr × Expr)) (pins : List (ℕ × ℕ)) (c : Clause)
    (hJ : ctlJmax ≤ Jmax) (hbase : M + ctlJmax < base)
    (hfit : base + xs.length ≤ M + Jmax)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hdep : ∀ q ∈ lits, ∀ (bound : ℕ) (σ σ' : Store), σ 0 = M → σ' 0 = M →
      M + Jmax < bound → WordBelow base xs.length bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ)
    (hlen : c.lits.length = lits.length)
    (hlit : ∀ (τ : Store) (k : ℕ), PinsAndWord M pins base xs τ → τ 0 = M →
      k < lits.length →
      (lits.getD k defLit).1.eval τ = (if litTag (c.lits.getD k default) then 1 else 0) ∧
      (lits.getD k defLit).2.eval τ = litVar (c.lits.getD k default)) :
    ClauseWriter (writeClauseProg wpJ lits) M Jmax wpJ
      (PinsAndWord M pins base xs) [c] := by
  intro τ wp hF h0 hw hsep
  have hwpJle : wpJ ≤ Jmax := Nat.le_trans wpJ_le hJ
  have hwpsep : M + wpJ < wp := by omega
  have hlen_ne_ctl : base - 1 ≠ M + wpJ :=
    word_len_disjoint_ctl M base (M + wpJ) hbase (by unfold wpJ ctlJmax; omega)
  have hdata_ne_ctl : ∀ k, k < xs.length → base + k ≠ M + wpJ :=
    fun k _ => word_disjoint_ctl M base (M + wpJ) k hbase
      (by unfold wpJ ctlJmax; omega)
  have hctl_free_ne : ∀ r, CtlFree M Jmax r → r ≠ M + wpJ := by
    intro r hr
    unfold CtlFree at hr
    rcases hr with hr | hr
    · intro heq
      rw [heq] at hr
      have := wpJ_pos
      omega
    · intro heq
      rw [heq] at hr
      omega
  have hbelow : WordBelow base xs.length wp := ⟨by omega, by omega⟩
  have hinv : ∀ q ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ :=
    fun q hq σ σ' hσ hσ' hagree => hdep q hq wp σ σ' hσ hσ' hsep hbelow hagree
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ lits M wp τ wpJ_pos h0 hw hwpsep hinv
  set σ2 := (writeClauseProg wpJ lits).eval τ
  have hwidth : rowTableWidth (rowW [c]) [c].length = 2 + 2 * lits.length := by
    rw [show [c].length = 1 from rfl, rowTableWidth_singleton, hlen]
  refine ⟨⟨?_, ?_⟩, w4, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨_, hq2, hq3⟩ := hpin q hq
    rw [w5 (M + q.1) (by omega) (by omega)]
    exact hF.1 q hq
  · obtain ⟨hlen0, hdata⟩ := hF.2
    have hlen_lt : base - 1 < wp := by omega
    exact ⟨by rw [w5 (base - 1) hlen_lt hlen_ne_ctl]; exact hlen0,
      fun k hk => by
        have hdata_lt : base + k < wp := by omega
        rw [w5 (base + k) hdata_lt (hdata_ne_ctl k hk)]
        exact hdata k hk⟩
  · rw [w3, hwidth]
    omega
  · refine rowsWritten_singleton σ2 wp c ?_ ?_ ?_
    · rw [w1, hlen]
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).1]
      exact (hlit τ k hF h0 hk).1
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).2]
      exact (hlit τ k hF h0 hk).2
  · intro r hr1 hr2
    exact w5 r hr1 (hctl_free_ne r hr2)

def initStateProgParam (n m wReg : ℕ) (d : TableauDescriptor) : Program :=
  if d.startState < d.numStates then
    writeClauseProg wpJ (unitPosLits (initStateEParam n m wReg d.startState))
  else writeClauseProg wpJ []

lemma init_state_writer_param
    (M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg pbReg : ℕ)
    (d : TableauDescriptor) (prefIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initStateProgParam n m wReg d) M Jmax wpJ
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx)
      [descInitStateClause (denseLayout n W m) d] := by
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    have h := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase wpJ hplace wpJ_le q hq
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  unfold initStateProgParam descInitStateClause
  by_cases hst : d.startState < d.numStates
  · simp only [ite_eq_left hst]
    refine clause_writer_unit_pos_word_wide M Jmax prefBase prefIdx
      (initStateEParam n m wReg d.startState)
      ((denseLayout n W m).state 0 d.startState) _ hplace.ctl_le hctlbase hfit hpin ?_ ?_
    · intro bound σ σ' hσ hσ' hbound _ hagree
      exact init_state_e_param_frame M Jmax n m wReg tReg fReg plReg pbReg d.startState
        hplace σ σ' hσ hσ'
        (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
    · intro τ hF h0
      exact init_state_e_param_value M n W m wReg tReg fReg plReg pbReg T freeLen
        prefLen prefBase d.startState prefIdx τ hF h0
  · simp only [ite_eq_right hst]
    exact clause_writer_clause_word_wide M Jmax prefBase prefIdx [] _ ⟨[]⟩
      hplace.ctl_le hctlbase hfit hpin
      (fun q hq => absurd hq (List.not_mem_nil)) rfl
      (fun _ k _ _ hk => by cases hk)

def initHeadProgParam (n m wReg tReg : ℕ) : Program :=
  writeClauseProg wpJ (unitPosLits (initHeadEParam n m wReg tReg))

lemma init_head_writer_param
    (M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initHeadProgParam n m wReg tReg) M Jmax wpJ
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx)
      [unitPos ((denseLayout n W m).head 0 (originIdx T))] := by
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    have h := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase wpJ hplace wpJ_le q hq
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  unfold initHeadProgParam
  refine clause_writer_unit_pos_word_wide M Jmax prefBase prefIdx
    (initHeadEParam n m wReg tReg) ((denseLayout n W m).head 0 (originIdx T)) _
    hplace.ctl_le hctlbase hfit hpin ?_ ?_
  · intro bound σ σ' hσ hσ' hbound _ hagree
    exact init_head_e_param_frame M Jmax n m wReg tReg fReg plReg pbReg hplace
      σ σ' hσ hσ' (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
  · intro τ hF h0
    exact init_head_e_param_value M n W m wReg tReg fReg plReg pbReg T freeLen prefLen
      prefBase prefIdx τ hF h0

def initTailCellEParam (n m wReg tReg plReg blank : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (.const 0)
    (.add (.add (ctlCell tReg) (ctlCell plReg)) (ctlCell lvJ0)) (.const blank)

def initTailCellNextEParam (n m wReg tReg plReg blank : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (.const 0)
    (.add (.add (.add (ctlCell tReg) (ctlCell plReg)) (ctlCell lvJ0)) (.const 1))
    (.const blank)

lemma init_tail_cell_e_param_frame
    (M Jmax n m wReg tReg fReg plReg pbReg blank : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initTailCellEParam n m wReg tReg plReg blank).eval σ'
      = (initTailCellEParam n m wReg tReg plReg blank).eval σ := by
  unfold initTailCellEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree,
    init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg plReg hplace
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree]

lemma init_tail_cell_next_e_param_frame
    (M Jmax n m wReg tReg fReg plReg pbReg blank : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initTailCellNextEParam n m wReg tReg plReg blank).eval σ'
      = (initTailCellNextEParam n m wReg tReg plReg blank).eval σ := by
  unfold initTailCellNextEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree,
    init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg plReg hplace
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree]

lemma init_tail_cell_e_param_value
    (M n W m T prefLen blank wReg tReg fReg plReg pbReg freeLen prefBase i : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase i)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initTailCellEParam n m wReg tReg plReg blank).eval τ
      = (denseLayout n W m).cell 0 (T + prefLen + i) blank := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL : (ctlCell plReg).eval τ = prefLen :=
    ctlCell_eval_of_pin M _ plReg prefLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ei : (ctlCell lvJ0).eval τ = i :=
    ctlCell_eval_of_pin M _ lvJ0 i τ (by simp [initParamPins1]) hF.1 h0
  unfold initTailCellEParam
  rw [denseCellE_eval, eW]
  simp [Expr.eval, eT, eL, ei]

lemma init_tail_cell_next_e_param_value
    (M n W m T prefLen blank wReg tReg fReg plReg pbReg freeLen prefBase i : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase i)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initTailCellNextEParam n m wReg tReg plReg blank).eval τ
      = (denseLayout n W m).cell 0 (T + prefLen + i + 1) blank := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL : (ctlCell plReg).eval τ = prefLen :=
    ctlCell_eval_of_pin M _ plReg prefLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ei : (ctlCell lvJ0).eval τ = i :=
    ctlCell_eval_of_pin M _ lvJ0 i τ (by simp [initParamPins1]) hF.1 h0
  unfold initTailCellNextEParam
  rw [denseCellE_eval, eW]
  simp [Expr.eval, eT, eL, ei]

lemma init_tail_leaf_writer_param
    (M Jmax n W m T blank prefBase prefLen freeLen i wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx : List ℕ) (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (writeClauseProg wpJ
        (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
          (initTailCellNextEParam n m wReg tReg plReg blank)))
      M Jmax wpJ
      (PinsAndWord M
        (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase i)
        prefBase prefIdx)
      [implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
        ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)] := by
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase i, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    have h := init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase i wpJ hplace wpJ_le (by unfold lvJ0 wpJ; omega) q hq
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine clause_writer_clause_word_wide M Jmax prefBase prefIdx
    (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
      (initTailCellNextEParam n m wReg tReg plReg blank)) _ _
    hplace.ctl_le hctlbase hfit hpin ?_ ?_ ?_
  · intro q hq bound σ σ' hσ hσ' hbound _ hagree
    have hframe : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ →
        σ' (M + j) = σ (M + j) :=
      fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
    simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨rfl, init_tail_cell_e_param_frame M Jmax n m wReg tReg fReg plReg
        pbReg blank hplace σ σ' hσ hσ' hframe⟩
    · exact ⟨rfl, init_tail_cell_next_e_param_frame M Jmax n m wReg tReg fReg plReg
        pbReg blank hplace σ σ' hσ hσ' hframe⟩
  · rw [implyPos_len, implyPosLits_length]
  · intro τ k hF h0 hk
    rw [implyPosLits_length] at hk
    interval_cases k
    · rw [implyPosLits_get0]
      exact ⟨rfl, by
        rw [implyPos_var0]
        simpa [hlen] using init_tail_cell_e_param_value M n W m T prefLen blank wReg
          tReg fReg plReg pbReg freeLen prefBase i prefIdx τ hF h0⟩
    · rw [implyPosLits_get1]
      exact ⟨rfl, by
        rw [implyPos_var1]
        simpa [hlen] using init_tail_cell_next_e_param_value M n W m T prefLen blank
          wReg tReg fReg plReg pbReg freeLen prefBase i prefIdx τ hF h0⟩

def initTailProgParam (n m blank wReg tReg fReg plReg : ℕ) : Program :=
  loopProg lvJ0 (ctlCell fReg)
    (.seq (writeClauseProg wpJ
        (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
          (initTailCellNextEParam n m wReg tReg plReg blank)))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma init_tail_loop_writer_param
    (M Jmax n W m T blank prefBase prefLen freeLen wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx : List ℕ) (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter (initTailProgParam n m blank wReg tReg fReg plReg)
      M Jmax wpJ
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx)
      ((List.range freeLen).map fun i =>
        implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
          ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)) := by
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have hpin := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
    prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega)
  rw [map_eq_flatMap_singleton]
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ0
    (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) _
    (ctlCell fReg) freeLen prefBase prefIdx
    (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hctlbase ?_ ?_
  · exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0
      (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) _
      prefBase prefIdx (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      hpin hctlbase (fun i => by
        change ClauseWriter _ M Jmax wpJ
          (PinsAndWord M
            (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase i)
            prefBase prefIdx) _
        exact init_tail_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen i
          wReg tReg fReg plReg pbReg prefIdx hplace hlen hbase hfit)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ fReg freeLen τ (by simp [initParamPins0]) hF.1 h0

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitExpr
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptExpr

/-!
The initial family's window loop cannot be three separate `forN`s: a loop body
writes the same number of clauses at every index, so the prefix / free / blank
choice has to live inside one iteration as nested `ifNZ`.  The free-region
clause is the only run-time-width one, and its letters are a compile-time list,
so the producer indexes that list from the literal counter rather than reading
it from the store.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The clause the window loop writes at position `p`. -/
def initWindowClause (n W m T blank : ℕ) (prefIdx allowedIdx : List ℕ)
    (freeLen p : ℕ) : Clause :=
  if p < T + prefIdx.length then
    unitPos ((denseLayout n W m).cell 0 p (natInitSymbol blank prefIdx (idxToPos T p)))
  else if p < T + prefIdx.length + freeLen then
    atLeastOne ((blank :: allowedIdx).map fun a => (denseLayout n W m).cell 0 p a)
  else unitPos ((denseLayout n W m).cell 0 p blank)

/-- The variable expression for the run-time-width free-region clause: the
    window position comes from the level counter, the letter from the literal
    counter indexing a compile-time list. -/
def initFreeCellVarE (n W m blank : ℕ) (allowedIdx : List ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.const 0) (ctlCell lvJ0)
    (listGetE (blank :: allowedIdx) (ctlCell litJ))

def initWindowLeafProg (n W m T blank prefBase prefLen freeLen : ℕ)
    (allowedIdx : List ℕ) : Program :=
  .ifNZ (initInPrefixE T prefLen)
    (writeClauseProg wpJ (unitPosLits (initPrefixCellE n W m T prefBase blank prefLen)))
    (.ifNZ (initInFreeE T prefLen freeLen)
      (writeAtLeastOneProg wpJ litJ (.const (allowedIdx.length + 1))
        (initFreeCellVarE n W m blank allowedIdx))
      (writeClauseProg wpJ (unitPosLits (initBlankCellE n W m blank))))

def initWindowProg (n W m T blank prefBase prefLen freeLen W' : ℕ)
    (allowedIdx : List ℕ) : Program :=
  loopProg lvJ0 (.const W')
    (.seq (initWindowLeafProg n W m T blank prefBase prefLen freeLen allowedIdx)
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma initFreeCellVarE_frame_bound (M n W m blank : ℕ) (allowedIdx : List ℕ)
    (σ1 σ2 : Store) (h1 : σ1 0 = M) (h2 : σ2 0 = M)
    (hagree : ∀ r, r < M + ctlJmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) :
    (initFreeCellVarE n W m blank allowedIdx).eval σ1
      = (initFreeCellVarE n W m blank allowedIdx).eval σ2 := by
  unfold initFreeCellVarE
  rw [denseCellE_eval, denseCellE_eval, listGetE_eval, listGetE_eval]
  simp only [Expr.eval, ctlCell_eval, h1, h2]
  rw [hagree (M + lvJ0) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega),
    hagree (M + litJ) (by unfold litJ ctlJmax; omega) (by unfold litJ wpJ; omega)]

lemma initFreeCellVarE_value (M n W m blank p : ℕ) (allowedIdx : List ℕ)
    (τ : Store) (k : ℕ) (h0 : τ 0 = M) (hp : τ (M + lvJ0) = p)
    (hk : τ (M + litJ) = k) :
    (initFreeCellVarE n W m blank allowedIdx).eval τ
      = (denseLayout n W m).cell 0 p ((blank :: allowedIdx).getD k 0) := by
  unfold initFreeCellVarE
  rw [denseCellE_eval, listGetE_eval]
  simp only [Expr.eval, ctlCell_eval, h0, hp, hk]

lemma init_window_leaf_writer (M Jmax n W m T blank prefBase freeLen p : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter
      (initWindowLeafProg n W m T blank prefBase prefIdx.length freeLen allowedIdx)
      M Jmax wpJ (PinsAndWord M (ctlPins1 p) prefBase prefIdx)
      [initWindowClause n W m T blank prefIdx allowedIdx freeLen p] := by
  have hpin1 : ∀ q ∈ ctlPins1 p, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, _, h4⟩ := ctlPins1_ok p wpJ (by unfold lvJ0 wpJ; omega) q hq
    exact ⟨h1, h2, h4⟩
  have hpinA : ∀ q ∈ ctlPins1 p, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ ∧ q.1 ≠ litJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins1_ok p litJ (by unfold lvJ0 litJ; omega) q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h4, h3⟩
  refine clauseWriter_ifNZ_gen (initInPrefixE T prefIdx.length) _ _ M Jmax wpJ
      (PinsAndWord M (ctlPins1 p) prefBase prefIdx)
      [initWindowClause n W m T blank prefIdx allowedIdx freeLen p]
      (p < T + prefIdx.length) ?_ ?_ ?_
  · intro τ hF h0
    have hp : τ (M + lvJ0) = p := hF.1 (lvJ0, p) (by simp [ctlPins1])
    rw [initInPrefixE_eval M T prefIdx.length p τ h0 hp]
    by_cases hpT : p < T + prefIdx.length <;> simp [hpT]
  · intro hpre
    simp only [initWindowClause, ite_eq_left hpre]
    refine clauseWriter_unitPos_word M Jmax prefBase prefIdx
        (initPrefixCellE n W m T prefBase blank prefIdx.length)
        ((denseLayout n W m).cell 0 p (natInitSymbol blank prefIdx (idxToPos T p)))
        (ctlPins1 p) hJ hbase hfit hpin1 ?_ ?_
    · intro bound σ σ' hσ hσ' hbound hw hagree
      exact initPrefixCellE_frame_below M n W m T prefBase blank prefIdx.length
        bound σ σ' hσ hσ' hbound hw hbase hagree
    · intro τ hF h0
      have hp : τ (M + lvJ0) = p := hF.1 (lvJ0, p) (by simp [ctlPins1])
      exact initPrefixCellE_value M n W m T prefBase blank p τ prefIdx h0 hp hF.2
  · intro hnpre
    refine clauseWriter_ifNZ_gen (initInFreeE T prefIdx.length freeLen) _ _ M Jmax wpJ
        (PinsAndWord M (ctlPins1 p) prefBase prefIdx)
        [initWindowClause n W m T blank prefIdx allowedIdx freeLen p]
        (p < T + prefIdx.length + freeLen) ?_ ?_ ?_
    · intro τ hF h0
      have hp : τ (M + lvJ0) = p := hF.1 (lvJ0, p) (by simp [ctlPins1])
      rw [initInFreeE_eval M T prefIdx.length freeLen p τ h0 hp]
      by_cases hpT : p < T + prefIdx.length + freeLen <;> simp [hpT]
    · intro hfree
      simp only [initWindowClause, ite_eq_right hnpre, ite_eq_left hfree]
      refine clauseWriter_atLeastOne_word M Jmax litJ
          (.const (allowedIdx.length + 1))
          (initFreeCellVarE n W m blank allowedIdx) (ctlPins1 p)
          ((blank :: allowedIdx).map fun a => (denseLayout n W m).cell 0 p a)
          prefBase prefIdx
          (by unfold litJ; omega)
          (by unfold litJ wpJ; omega)
          (by unfold litJ ctlJmax; omega)
          hpinA hbase hfit
          (fun τ _ _ => by simp [Expr.eval, List.length_map, List.length_cons])
          (fun _ _ _ _ _ => rfl) ?_ ?_
      · intro σ1 σ2 h1 h2 hagree
        exact initFreeCellVarE_frame_bound M n W m blank allowedIdx σ1 σ2 h1 h2
          (fun r hr1 hr2 => hagree r (by omega) hr2)
      · intro τ k hF h0 hk hlt
        have hp : τ (M + lvJ0) = p := hF.1 (lvJ0, p) (by simp [ctlPins1])
        have hlen :
            ((blank :: allowedIdx).map fun a =>
              (denseLayout n W m).cell 0 p a).length = (blank :: allowedIdx).length :=
          by simp
        rw [initFreeCellVarE_value M n W m blank p allowedIdx τ k h0 hp hk, map_getD_of_lt]
        omega
    · intro hnfree
      simp only [initWindowClause, ite_eq_right hnpre, ite_eq_right hnfree]
      refine clauseWriter_unitPos_word M Jmax prefBase prefIdx
          (initBlankCellE n W m blank)
          ((denseLayout n W m).cell 0 p blank)
          (ctlPins1 p) hJ hbase hfit hpin1 ?_ ?_
      · intro bound σ σ' hσ hσ' hbound _ hagree
        exact initBlankCellE_frame_below M n W m blank bound σ σ' hσ hσ' hbound hagree
      · intro τ hF h0
        have hp : τ (M + lvJ0) = p := hF.1 (lvJ0, p) (by simp [ctlPins1])
        exact initBlankCellE_value M n W m blank p τ h0 hp

lemma init_window_loop_writer (M Jmax n W m T blank prefBase freeLen : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter
      (initWindowProg n W m T blank prefBase prefIdx.length freeLen W allowedIdx)
      M Jmax wpJ (PinsAndWord M ctlPins0 prefBase prefIdx)
      ((List.range W).map fun p =>
        initWindowClause n W m T blank prefIdx allowedIdx freeLen p) := by
  have hpin : ∀ q ∈ ctlPins0, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ0 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins0_ok lvJ0 q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  rw [map_eq_flatMap_singleton]
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ0 ctlPins0 _ (.const W) W
    prefBase prefIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0 ctlPins0 _
    prefBase prefIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase
    (fun p =>
      have hpins : (lvJ0, p) :: ctlPins0 = ctlPins1 p := rfl
      hpins ▸ init_window_leaf_writer M Jmax n W m T blank prefBase freeLen p
        prefIdx allowedIdx hJ hbase hfit)

/-! ## Run-time-parameter window writer -/

def initFreeCellVarEParam (n m wReg blank : ℕ) (allowedIdx : List ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (.const 0) (ctlCell lvJ0)
    (listGetE (blank :: allowedIdx) (ctlCell litJ))

lemma init_free_cell_var_e_param_frame
    (M Jmax n m wReg tReg fReg plReg pbReg blank : ℕ) (allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initFreeCellVarEParam n m wReg blank allowedIdx).eval σ'
      = (initFreeCellVarEParam n m wReg blank allowedIdx).eval σ := by
  unfold initFreeCellVarEParam
  rw [denseCellE_eval, denseCellE_eval, listGetE_eval, listGetE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax litJ hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree]

lemma init_free_cell_var_e_param_value
    (M n W m wReg tReg fReg plReg pbReg T freeLen prefLen prefBase blank p : ℕ)
    (allowedIdx prefIdx : List ℕ) (τ : Store) (k : ℕ)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) (hk : τ (M + litJ) = k) :
    (initFreeCellVarEParam n m wReg blank allowedIdx).eval τ
      = (denseLayout n W m).cell 0 p ((blank :: allowedIdx).getD k 0) := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  have ek : (ctlCell litJ).eval τ = k := by rw [ctlCell_eval, h0]; exact hk
  unfold initFreeCellVarEParam
  rw [denseCellE_eval, listGetE_eval, eW, ep, ek]
  simp [Expr.eval]

def initWindowLeafProgParam
    (n m blank wReg tReg fReg plReg pbReg : ℕ) (allowedIdx : List ℕ) : Program :=
  .ifNZ (initInPrefixEParam tReg plReg)
    (.seq (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
      (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg))))
    (.ifNZ (initInFreeEParam tReg plReg fReg)
      (writeAtLeastOneProg wpJ litJ (.const (allowedIdx.length + 1))
        (initFreeCellVarEParam n m wReg blank allowedIdx))
      (writeClauseProg wpJ (unitPosLits (initBlankCellEParam n m wReg blank))))

lemma init_prefix_leaf_writer_param
    (M Jmax n W m T blank prefBase prefLen freeLen p wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx : List ℕ) (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter
      (.seq (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
        (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg))))
      M Jmax wpJ
      (PinsAndWord M
        (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx)
      [unitPos ((denseLayout n W m).cell 0 p
        (natInitSymbol blank prefIdx (idxToPos T p)))] := by
  let pins := initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p
  let av := natInitSymbol blank prefIdx (idxToPos T p)
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have htmpbase : M + tmpJ + 1 < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold tmpJ
    omega
  have hpinstmp : ∀ q ∈ pins, q.1 ≠ tmpJ := by
    intro q hq
    have h := init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase p tmpJ hplace (by unfold tmpJ ctlJmax; omega)
      (by unfold lvJ0 tmpJ; omega) q hq
    exact h.2.2.1
  have hstage : ClauseWriterIO
      (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank)) M Jmax wpJ
      (PinsAndWord M pins prefBase prefIdx)
      (PinsAndWord M ((tmpJ, av) :: pins) prefBase prefIdx) [] := by
    refine clause_writer_io_stage_word_value M Jmax tmpJ prefBase av prefIdx pins
      (initPrefixSymbolEParam tReg plReg pbReg blank)
      (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le)
      (by unfold tmpJ wpJ; omega) hpinstmp htmpbase ?_
    intro τ hF h0
    exact init_prefix_symbol_e_param_value M wReg tReg fReg plReg pbReg W T freeLen
      prefLen prefBase blank p prefIdx τ hF h0 hlen
  have hpinwrite : ∀ q ∈ (tmpJ, av) :: pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨by unfold tmpJ; omega,
        Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le,
        by unfold tmpJ wpJ; omega⟩
    · have h := init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen
        prefLen prefBase p wpJ hplace wpJ_le (by unfold lvJ0 wpJ; omega) q hq
      exact ⟨h.1, h.2.1, h.2.2.2⟩
  have hwrite : ClauseWriter
      (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg)))
      M Jmax wpJ (PinsAndWord M ((tmpJ, av) :: pins) prefBase prefIdx)
      [unitPos ((denseLayout n W m).cell 0 p av)] := by
    refine clause_writer_unit_pos_word_wide M Jmax prefBase prefIdx
      (initPrefixCellStagedEParam n m wReg) ((denseLayout n W m).cell 0 p av)
      ((tmpJ, av) :: pins) hplace.ctl_le hctlbase hfit hpinwrite ?_ ?_
    · intro bound σ σ' hσ hσ' hbound _ hagree
      exact init_prefix_cell_staged_e_param_frame M Jmax n m wReg tReg fReg plReg pbReg
        hplace σ σ' hσ hσ'
        (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
    · intro τ hF h0
      exact init_prefix_cell_staged_e_param_value M n W m wReg tReg fReg plReg pbReg T
        freeLen prefLen prefBase av p prefIdx τ hF h0
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ
    (PinsAndWord M pins prefBase prefIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) prefBase prefIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) prefBase prefIdx) [] _ hstage
    (clauseWriterIO_of_writer _ M Jmax wpJ _ _ hwrite)
  have hdrop := clauseWriterIO_weaken_exit _ M Jmax wpJ
    (PinsAndWord M pins prefBase prefIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) prefBase prefIdx)
    (PinsAndWord M pins prefBase prefIdx) _
    (fun τ h => pinsAndWord_tail M (tmpJ, av) pins prefBase prefIdx τ h) hseq
  simpa [ClauseWriterIO, ClauseWriter, pins, av] using hdrop

lemma init_window_leaf_writer_param
    (M Jmax n W m T blank prefBase prefLen freeLen p wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter
      (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      M Jmax wpJ
      (PinsAndWord M
        (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx)
      [initWindowClause n W m T blank prefIdx allowedIdx freeLen p] := by
  let pins := initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p
  have hctlbase : M + ctlJmax < prefBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_f
    have := hplace.f_pl
    have := hplace.pl_pb
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    have h := init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase p wpJ hplace wpJ_le (by unfold lvJ0 wpJ; omega) q hq
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  have hpinA : ∀ q ∈ pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ ∧ q.1 ≠ litJ := by
    intro q hq
    have h := init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase p litJ hplace (by unfold litJ ctlJmax; omega)
      (by unfold lvJ0 litJ; omega) q hq
    exact ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩
  unfold initWindowLeafProgParam
  refine clauseWriter_ifNZ_gen (initInPrefixEParam tReg plReg) _ _ M Jmax wpJ
    (PinsAndWord M pins prefBase prefIdx)
    [initWindowClause n W m T blank prefIdx allowedIdx freeLen p]
    (p < T + prefIdx.length) ?_ ?_ ?_
  · intro τ hF h0
    rw [init_in_prefix_e_param_eval M wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase p prefIdx τ hF h0]
    by_cases hp : p < T + prefIdx.length <;> simp [hlen, hp]
  · intro hpre
    simp only [initWindowClause, ite_eq_left hpre]
    exact init_prefix_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen p
      wReg tReg fReg plReg pbReg prefIdx hplace hlen hbase hfit
  · intro hnpre
    refine clauseWriter_ifNZ_gen (initInFreeEParam tReg plReg fReg) _ _ M Jmax wpJ
      (PinsAndWord M pins prefBase prefIdx)
      [initWindowClause n W m T blank prefIdx allowedIdx freeLen p]
      (p < T + prefIdx.length + freeLen) ?_ ?_ ?_
    · intro τ hF h0
      rw [init_in_free_e_param_eval M wReg tReg fReg plReg pbReg W T freeLen prefLen
        prefBase p prefIdx τ hF h0]
      by_cases hp : p < T + prefIdx.length + freeLen <;> simp [hlen, hp]
    · intro hfree
      simp only [initWindowClause, ite_eq_right hnpre, ite_eq_left hfree]
      refine clauseWriter_atLeastOne_word M Jmax litJ (.const (allowedIdx.length + 1))
        (initFreeCellVarEParam n m wReg blank allowedIdx) pins
        ((blank :: allowedIdx).map fun a => (denseLayout n W m).cell 0 p a)
        prefBase prefIdx (by unfold litJ; omega)
        (by unfold litJ wpJ; omega) (by unfold litJ ctlJmax; omega)
        hpinA hctlbase hfit
        (fun τ _ _ => by simp [Expr.eval, List.length_map, List.length_cons])
        (fun _ _ _ _ _ => rfl) ?_ ?_
      · intro σ σ' hσ hσ' hagree
        exact init_free_cell_var_e_param_frame M Jmax n m wReg tReg fReg plReg pbReg
          blank allowedIdx hplace σ' σ hσ' hσ
          (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
      · intro τ k hF h0 hk hlt
        have hlenMap :
            ((blank :: allowedIdx).map fun a =>
              (denseLayout n W m).cell 0 p a).length = (blank :: allowedIdx).length := by
          simp
        rw [init_free_cell_var_e_param_value M n W m wReg tReg fReg plReg pbReg T
          freeLen prefLen prefBase blank p allowedIdx prefIdx τ k hF h0 hk,
          map_getD_of_lt]
        omega
    · intro hnfree
      simp only [initWindowClause, ite_eq_right hnpre, ite_eq_right hnfree]
      refine clause_writer_unit_pos_word_wide M Jmax prefBase prefIdx
        (initBlankCellEParam n m wReg blank) ((denseLayout n W m).cell 0 p blank)
        pins hplace.ctl_le hctlbase hfit hpin ?_ ?_
      · intro bound σ σ' hσ hσ' hbound _ hagree
        exact init_blank_cell_e_param_frame M Jmax n m wReg tReg fReg plReg pbReg blank
          hplace σ σ' hσ hσ'
          (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
      · intro τ hF h0
        exact init_blank_cell_e_param_value M n W m wReg tReg fReg plReg pbReg T freeLen
          prefLen prefBase blank p prefIdx τ hF h0

def initWindowProgParam
    (n m blank wReg tReg fReg plReg pbReg : ℕ) (allowedIdx : List ℕ) : Program :=
  loopProg lvJ0 (ctlCell wReg)
    (.seq (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma init_window_loop_writer_param
    (M Jmax n W m T blank prefBase prefLen freeLen wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hbase : M + pbReg + 1 < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax) :
    ClauseWriter
      (initWindowProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      M Jmax wpJ
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx)
      ((List.range W).map fun p =>
        initWindowClause n W m T blank prefIdx allowedIdx freeLen p) := by
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
    (ctlCell wReg) W prefBase prefIdx (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hctlbase ?_ ?_
  · exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0
      (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) _
      prefBase prefIdx (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      hpin hctlbase (fun p => by
        change ClauseWriter _ M Jmax wpJ
          (PinsAndWord M
            (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
            prefBase prefIdx) _
        exact init_window_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen p
          wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hbase hfit)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ (by simp [initParamPins0]) hF.1 h0

end NPComplete.CookLevin

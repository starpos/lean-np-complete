module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitTail

/-!
The accept family has three run-time inputs: the tableau width, the final time,
and the base address of the staged output word.  The word lookup is indirect,
so each inner iteration stages its selected symbol in `tmpJ` before invoking the
clause writer.  The written literal expressions consequently read only fixed
control and parameter cells.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Parameter placement and entry predicates -/

structure AcceptParamPlacement (Jmax wReg tReg obReg : ℕ) : Prop where
  ctl_le : ctlJmax ≤ Jmax
  w_min : 15 ≤ wReg
  w_t : wReg < tReg
  t_ob : tReg < obReg
  ob_le : obReg ≤ Jmax

def acceptWReg : ℕ := 15
def acceptTReg : ℕ := 16
def acceptOutBaseReg : ℕ := 23
def acceptParamJmax : ℕ := 23

lemma accept_param_fixed_placement :
    AcceptParamPlacement acceptParamJmax acceptWReg acceptTReg acceptOutBaseReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [acceptParamJmax, acceptWReg, acceptTReg, acceptOutBaseReg, ctlJmax]

lemma accept_param_placement_satisfiable :
    ∃ Jmax wReg tReg obReg, AcceptParamPlacement Jmax wReg tReg obReg :=
  ⟨acceptParamJmax, acceptWReg, acceptTReg, acceptOutBaseReg,
    accept_param_fixed_placement⟩

lemma accept_param_full_placement_satisfiable :
    ∃ M Jmax outBase, ∃ outIdx : List ℕ,
      AcceptParamPlacement Jmax acceptWReg acceptTReg acceptOutBaseReg ∧
        M + acceptOutBaseReg + 1 < outBase ∧
        outBase + outIdx.length ≤ M + Jmax := by
  refine ⟨0, 26, 25, [0], ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [acceptWReg, acceptTReg, acceptOutBaseReg, ctlJmax]
  · simp [acceptOutBaseReg]
  · simp

def acceptParamPins0 (wReg tReg obReg W T outBase : ℕ) : List (ℕ × ℕ) :=
  [(wReg, W), (tReg, T), (obReg, outBase)]

def acceptParamPins1 (wReg tReg obReg W T outBase pHead : ℕ) : List (ℕ × ℕ) :=
  (lvJ0, pHead) :: acceptParamPins0 wReg tReg obReg W T outBase

def acceptParamPins2 (wReg tReg obReg W T outBase pHead p : ℕ) : List (ℕ × ℕ) :=
  (lvJ1, p) :: acceptParamPins1 wReg tReg obReg W T outBase pHead

def AcceptParamFrozen (M wReg tReg obReg W T outBase : ℕ)
    (outIdx : List ℕ) (τ : Store) : Prop :=
  PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx τ

lemma accept_param_pins0_ok (Jmax wReg tReg obReg W T outBase iJ : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg) (hiJctl : iJ ≤ ctlJmax) :
    ∀ q ∈ acceptParamPins0 wReg tReg obReg W T outBase,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have hto := hplace.t_ob
  have hle := hplace.ob_le
  simp only [acceptParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, hle, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩

lemma accept_param_pins1_ok (Jmax wReg tReg obReg W T outBase pHead iJ : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) :
    ∀ q ∈ acceptParamPins1 wReg tReg obReg W T outBase pHead,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ0; omega,
      Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le, h0,
      by unfold lvJ0 wpJ; omega⟩
  · exact accept_param_pins0_ok Jmax wReg tReg obReg W T outBase iJ hplace
      hiJctl q hq

lemma accept_param_pins2_ok
    (Jmax wReg tReg obReg W T outBase pHead p iJ : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) :
    ∀ q ∈ acceptParamPins2 wReg tReg obReg W T outBase pHead p,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ1; omega,
      Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le, h1,
      by unfold lvJ1 wpJ; omega⟩
  · exact accept_param_pins1_ok Jmax wReg tReg obReg W T outBase pHead iJ hplace
      hiJctl h0 q hq

/-! ## Dynamic word lookup and staged literal expressions -/

def acceptWordReadEParam (baseReg blank len : ℕ) (kE : Expr) : Expr :=
  wordReadEExpr (ctlCell baseReg) (.const len) blank kE

lemma accept_word_read_e_param_eval
    (σ : Store) (base blank baseReg : ℕ) (xs : List ℕ) (kE : Expr)
    (hbase : (ctlCell baseReg).eval σ = base) (hw : WordAt σ base xs) :
    (acceptWordReadEParam baseReg blank xs.length kE).eval σ
      = xs.getD (kE.eval σ) blank := by
  exact wordReadEExpr_eval σ base blank xs (ctlCell baseReg) (.const xs.length) kE
    hbase (by simp [Expr.eval]) hw


def acceptSymbolEParam (baseReg blank len : ℕ) (pE qE : Expr) : Expr :=
  .add
    (.mul (.sub (.const 1) (.lt pE qE))
      (acceptWordReadEParam baseReg blank len (.sub pE qE)))
    (.mul (.lt pE qE) (.const blank))

lemma accept_symbol_e_param_eval
    (σ : Store) (base blank baseReg : ℕ) (xs : List ℕ) (pE qE : Expr)
    (hbase : (ctlCell baseReg).eval σ = base) (hw : WordAt σ base xs) :
    (acceptSymbolEParam baseReg blank xs.length pE qE).eval σ
      = natInitSymbol blank xs ((pE.eval σ : ℤ) - (qE.eval σ : ℤ)) := by
  rw [natInitSymbol_sub]
  unfold acceptSymbolEParam
  simp only [Expr.eval]
  by_cases h : pE.eval σ < qE.eval σ
  · rw [ite_eq_left h, ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right h, ite_eq_left (by omega)]
    have hread := accept_word_read_e_param_eval σ base blank baseReg xs (.sub pE qE)
      hbase hw
    simp only [Expr.eval] at hread
    rw [hread]
    omega

def acceptHeadEParam (n m wReg tReg : ℕ) : Expr :=
  denseHeadE (.const n) (ctlCell wReg) (.const m) (ctlCell tReg) (ctlCell lvJ0)

def acceptCellStagedEParam (n m wReg tReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (ctlCell tReg)
    (ctlCell lvJ1) (ctlCell tmpJ)

def acceptOutputSymbolEParam (obReg blank outLen : ℕ) : Expr :=
  acceptSymbolEParam obReg blank outLen (ctlCell lvJ1) (ctlCell lvJ0)

lemma accept_param_reg_frame (M Jmax wReg tReg obReg j : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hj : j = wReg ∨ j = tReg ∨ j = obReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  rcases hplace with ⟨_, _, _, _, _⟩
  exact ctlCell_frame M Jmax j (by omega) (by omega) (by unfold wpJ; omega)
    σ σ' hσ hσ' hagree

lemma accept_param_ctl_frame (M Jmax j : ℕ) (hJ : ctlJmax ≤ Jmax)
    (hj : j = lvJ0 ∨ j = lvJ1 ∨ j = litJ ∨ j = tmpJ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  rcases hj with rfl | rfl | rfl | rfl
  · exact ctlCell_frame M Jmax lvJ0 (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
      (by unfold lvJ0 wpJ; omega) σ σ' hσ hσ' hagree
  · exact ctlCell_frame M Jmax lvJ1 (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hJ)
      (by unfold lvJ1 wpJ; omega) σ σ' hσ hσ' hagree
  · exact ctlCell_frame M Jmax litJ (by unfold litJ; omega)
      (Nat.le_trans (by unfold litJ ctlJmax; omega) hJ)
      (by unfold litJ wpJ; omega) σ σ' hσ hσ' hagree
  · exact ctlCell_frame M Jmax tmpJ (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hJ)
      (by unfold tmpJ wpJ; omega) σ σ' hσ hσ' hagree

lemma accept_head_e_param_frame (M Jmax n m wReg tReg obReg : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (acceptHeadEParam n m wReg tReg).eval σ'
      = (acceptHeadEParam n m wReg tReg).eval σ := by
  unfold acceptHeadEParam
  rw [denseHeadE_eval, denseHeadE_eval]
  simp only [Expr.eval]
  rw [accept_param_reg_frame M Jmax wReg tReg obReg wReg hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    accept_param_reg_frame M Jmax wReg tReg obReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree,
    accept_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree]

lemma accept_cell_staged_e_param_frame (M Jmax n m wReg tReg obReg : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (acceptCellStagedEParam n m wReg tReg).eval σ'
      = (acceptCellStagedEParam n m wReg tReg).eval σ := by
  unfold acceptCellStagedEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [accept_param_reg_frame M Jmax wReg tReg obReg wReg hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    accept_param_reg_frame M Jmax wReg tReg obReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree,
    accept_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree,
    accept_param_ctl_frame M Jmax tmpJ hplace.ctl_le (Or.inr (Or.inr (Or.inr rfl)))
      σ σ' hσ hσ' hagree]

lemma accept_head_e_param_value
    (M n W m T outBase wReg tReg obReg pHead p : ℕ) (τ : Store)
    (hF : PinsHold M
      (acceptParamPins2 wReg tReg obReg W T outBase pHead p) τ)
    (h0 : τ 0 = M) :
    (acceptHeadEParam n m wReg tReg).eval τ
      = (denseLayout n W m).head T pHead := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF h0
  have e0 : (ctlCell lvJ0).eval τ = pHead :=
    ctlCell_eval_of_pin M _ lvJ0 pHead τ
      (by simp [acceptParamPins2, acceptParamPins1]) hF h0
  unfold acceptHeadEParam
  rw [denseHeadE_eval, eW, eT, e0]
  simp [Expr.eval]

lemma accept_cell_staged_e_param_value
    (M n W m T outBase wReg tReg obReg pHead p a : ℕ) (τ : Store)
    (hF : PinsHold M
      ((tmpJ, a) :: acceptParamPins2 wReg tReg obReg W T outBase pHead p) τ)
    (h0 : τ 0 = M) :
    (acceptCellStagedEParam n m wReg tReg).eval τ
      = (denseLayout n W m).cell T p a := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF h0
  have e1 : (ctlCell lvJ1).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [acceptParamPins2]) hF h0
  have ea : (ctlCell tmpJ).eval τ = a :=
    ctlCell_eval_of_pin M _ tmpJ a τ (by simp) hF h0
  unfold acceptCellStagedEParam
  rw [denseCellE_eval, eW, eT, e1, ea]
  simp [Expr.eval]

lemma accept_output_symbol_e_param_value
    (M wReg tReg obReg W T outBase blank pHead p : ℕ)
    (outIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx τ)
    (h0 : τ 0 = M) :
    (acceptOutputSymbolEParam obReg blank outIdx.length).eval τ
      = natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ)) := by
  have eB : (ctlCell obReg).eval τ = outBase :=
    ctlCell_eval_of_pin M _ obReg outBase τ
      (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF.1 h0
  have e0 : (ctlCell lvJ0).eval τ = pHead :=
    ctlCell_eval_of_pin M _ lvJ0 pHead τ
      (by simp [acceptParamPins2, acceptParamPins1]) hF.1 h0
  have e1 : (ctlCell lvJ1).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [acceptParamPins2]) hF.1 h0
  have hsym := accept_symbol_e_param_eval τ outBase blank obReg outIdx
    (ctlCell lvJ1) (ctlCell lvJ0) eB hF.2
  simp only [e0, e1] at hsym
  simpa [acceptOutputSymbolEParam] using hsym

/-! ## The staged fixed-width leaf -/

lemma accept_stage_output_symbol_writer_param
    (M Jmax wReg tReg obReg W T outBase blank pHead p : ℕ)
    (outIdx : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase) :
    ClauseWriterIO
      (ctlAssign tmpJ (acceptOutputSymbolEParam obReg blank outIdx.length))
      M Jmax wpJ
      (PinsAndWord M
        (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)
      (PinsAndWord M
        ((tmpJ, natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))) ::
          acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)
      [] := by
  let pins := acceptParamPins2 wReg tReg obReg W T outBase pHead p
  let av := natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))
  have htmpbase : M + tmpJ + 1 < outBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_ob
    unfold tmpJ
    omega
  have hpinstmp : ∀ q ∈ pins, q.1 ≠ tmpJ := by
    intro q hq
    have h := accept_param_pins2_ok Jmax wReg tReg obReg W T outBase pHead p
      tmpJ hplace (by unfold tmpJ ctlJmax; omega) (by unfold lvJ0 tmpJ; omega)
      (by unfold lvJ1 tmpJ; omega) q hq
    exact h.2.2.1
  refine clause_writer_io_stage_word_value M Jmax tmpJ outBase av outIdx pins
    (acceptOutputSymbolEParam obReg blank outIdx.length)
    (by unfold tmpJ; omega)
    (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le)
    (by unfold tmpJ wpJ; omega) hpinstmp htmpbase ?_
  intro τ hF h0
  exact accept_output_symbol_e_param_value M wReg tReg obReg W T outBase blank
    pHead p outIdx τ hF h0

lemma accept_staged_clause_writer_param
    (M Jmax n W m T outBase wReg tReg obReg pHead p a : ℕ)
    (outIdx : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter
      (writeClauseProg wpJ
        (implyPosLits (acceptHeadEParam n m wReg tReg)
          (acceptCellStagedEParam n m wReg tReg)))
      M Jmax wpJ
      (PinsAndWord M
        ((tmpJ, a) :: acceptParamPins2 wReg tReg obReg W T outBase pHead p)
        outBase outIdx)
      [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p a)] := by
  let pins := acceptParamPins2 wReg tReg obReg W T outBase pHead p
  have hctlbase : M + ctlJmax < outBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_ob
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ (tmpJ, a) :: pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨by unfold tmpJ; omega,
        Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le,
        by unfold tmpJ wpJ; omega⟩
    · have h := accept_param_pins2_ok Jmax wReg tReg obReg W T outBase pHead p
        tmpJ hplace (by unfold tmpJ ctlJmax; omega) (by unfold lvJ0 tmpJ; omega)
        (by unfold lvJ1 tmpJ; omega) q hq
      exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine clause_writer_clause_word_wide M Jmax outBase outIdx
    (implyPosLits (acceptHeadEParam n m wReg tReg)
      (acceptCellStagedEParam n m wReg tReg)) ((tmpJ, a) :: pins)
    (implyPos ((denseLayout n W m).head T pHead)
      ((denseLayout n W m).cell T p a))
    hplace.ctl_le hctlbase hfit hpin ?_ ?_ ?_
  · intro q hq bound σ σ' hσ hσ' _ _ hagree
    have hframe : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ →
        σ' (M + j) = σ (M + j) :=
      fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
    simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨rfl, accept_head_e_param_frame M Jmax n m wReg tReg obReg hplace
        σ σ' hσ hσ' hframe⟩
    · exact ⟨rfl, accept_cell_staged_e_param_frame M Jmax n m wReg tReg obReg
        hplace σ σ' hσ hσ' hframe⟩
  · rw [implyPos_len, implyPosLits_length]
  · intro τ k hF h0 hk
    have hpins : PinsHold M pins τ :=
      pinsHold_tail M (tmpJ, a) pins τ hF.1
    rw [implyPosLits_length] at hk
    interval_cases k
    · rw [implyPosLits_get0]
      exact ⟨rfl, by
        rw [implyPos_var0]
        exact accept_head_e_param_value M n W m T outBase wReg tReg obReg pHead p
          τ hpins h0⟩
    · rw [implyPosLits_get1]
      exact ⟨rfl, by
        rw [implyPos_var1]
        exact accept_cell_staged_e_param_value M n W m T outBase wReg tReg obReg
          pHead p a τ hF.1 h0⟩

def acceptLeafProgParam
    (n m blank outLen wReg tReg obReg : ℕ) : Program :=
  .seq (ctlAssign tmpJ (acceptOutputSymbolEParam obReg blank outLen))
    (writeClauseProg wpJ
      (implyPosLits (acceptHeadEParam n m wReg tReg)
        (acceptCellStagedEParam n m wReg tReg)))

lemma accept_leaf_writer_param
    (M Jmax n W m T outBase blank pHead p wReg tReg obReg : ℕ)
    (outIdx : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter
      (acceptLeafProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ
      (PinsAndWord M
        (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)
      [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))] := by
  let pins := acceptParamPins2 wReg tReg obReg W T outBase pHead p
  let av := natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))
  have hstage := accept_stage_output_symbol_writer_param M Jmax wReg tReg obReg W T
    outBase blank pHead p outIdx hplace hbase
  have hwrite := accept_staged_clause_writer_param M Jmax n W m T outBase wReg tReg
    obReg pHead p av outIdx hplace hbase hfit
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ
    (PinsAndWord M pins outBase outIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) outBase outIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) outBase outIdx) [] _ hstage
    (clauseWriterIO_of_writer _ M Jmax wpJ _ _ hwrite)
  have hdrop := clauseWriterIO_weaken_exit _ M Jmax wpJ
    (PinsAndWord M pins outBase outIdx)
    (PinsAndWord M ((tmpJ, av) :: pins) outBase outIdx)
    (PinsAndWord M pins outBase outIdx) _
    (fun τ h => pinsAndWord_tail M (tmpJ, av) pins outBase outIdx τ h) hseq
  simpa [acceptLeafProgParam, ClauseWriterIO, ClauseWriter, pins, av] using hdrop

/-! ## The two window loops -/

def acceptInnerProgParam
    (n m blank outLen wReg tReg obReg : ℕ) : Program :=
  loopProg lvJ1 (ctlCell wReg)
    (.seq (acceptLeafProgParam n m blank outLen wReg tReg obReg)
      (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))

lemma accept_p_loop_writer_param
    (M Jmax n W m T outBase blank pHead wReg tReg obReg : ℕ)
    (outIdx : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter
      (acceptInnerProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ
      (PinsAndWord M
        (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx)
      ((List.range W).map fun p =>
        implyPos ((denseLayout n W m).head T pHead)
          ((denseLayout n W m).cell T p
            (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))) := by
  let pins := acceptParamPins1 wReg tReg obReg W T outBase pHead
  have hctlbase : M + ctlJmax < outBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_ob
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ1 ∧ q.1 ≠ wpJ := by
    intro q hq
    exact accept_param_pins1_ok Jmax wReg tReg obReg W T outBase pHead lvJ1
      hplace (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) q hq
  rw [map_eq_flatMap_singleton]
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ1 pins _ (ctlCell wReg) W
    outBase outIdx (by unfold lvJ1; omega)
    (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega)
    hpin hctlbase ?_ ?_
  · exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ1 pins _ outBase outIdx
      (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega)
      hpin hctlbase
      (fun p =>
        have hpins : (lvJ1, p) :: pins =
            acceptParamPins2 wReg tReg obReg W T outBase pHead p := rfl
        hpins ▸ accept_leaf_writer_param M Jmax n W m T outBase blank pHead p
          wReg tReg obReg outIdx hplace hbase hfit)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [pins, acceptParamPins1, acceptParamPins0]) hF.1 h0

def acceptOuterProgParam
    (n m blank outLen wReg tReg obReg : ℕ) : Program :=
  loopProg lvJ0 (ctlCell wReg)
    (.seq (acceptInnerProgParam n m blank outLen wReg tReg obReg)
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma accept_p_head_loop_writer_param
    (M Jmax n W m T outBase blank wReg tReg obReg : ℕ)
    (outIdx : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter
      (acceptOuterProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ
      (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase)
        outBase outIdx)
      ((List.range W).flatMap fun pHead =>
        (List.range W).map fun p =>
          implyPos ((denseLayout n W m).head T pHead)
            ((denseLayout n W m).cell T p
              (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))) := by
  let pins := acceptParamPins0 wReg tReg obReg W T outBase
  have hctlbase : M + ctlJmax < outBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_ob
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ0 ∧ q.1 ≠ wpJ := by
    intro q hq
    exact accept_param_pins0_ok Jmax wReg tReg obReg W T outBase lvJ0 hplace
      (by unfold lvJ0 ctlJmax; omega) q hq
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ0 pins _ (ctlCell wReg) W
    outBase outIdx (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hctlbase ?_ ?_
  · exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0 pins _ outBase outIdx
      (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      hpin hctlbase
      (fun pHead =>
        have hpins : (lvJ0, pHead) :: pins =
            acceptParamPins1 wReg tReg obReg W T outBase pHead := rfl
        hpins ▸ accept_p_loop_writer_param M Jmax n W m T outBase blank pHead
          wReg tReg obReg outIdx hplace hbase hfit)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [pins, acceptParamPins0]) hF.1 h0

/-! ## The final halt-state clause -/

def acceptHaltVarEParam (n m wReg tReg : ℕ) (qs : List ℕ) : Expr :=
  denseStateE (.const n) (ctlCell wReg) (.const m) (ctlCell tReg)
    (listGetE qs (ctlCell litJ))

lemma accept_halt_var_e_param_frame (M Jmax n m wReg tReg obReg : ℕ)
    (qs : List ℕ) (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (acceptHaltVarEParam n m wReg tReg qs).eval σ'
      = (acceptHaltVarEParam n m wReg tReg qs).eval σ := by
  unfold acceptHaltVarEParam
  rw [denseStateE_eval, denseStateE_eval, listGetE_eval, listGetE_eval]
  simp only [Expr.eval]
  rw [accept_param_reg_frame M Jmax wReg tReg obReg wReg hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    accept_param_reg_frame M Jmax wReg tReg obReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree,
    accept_param_ctl_frame M Jmax litJ hplace.ctl_le
      (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree]

lemma accept_halt_var_e_param_value_word
    (M n W m T outBase wReg tReg obReg : ℕ) (qs outIdx : List ℕ)
    (τ : Store) (k : ℕ)
    (hF : PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase)
      outBase outIdx τ)
    (h0 : τ 0 = M) (hk : τ (M + litJ) = k) :
    (acceptHaltVarEParam n m wReg tReg qs).eval τ
      = (denseLayout n W m).state T (qs.getD k 0) := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [acceptParamPins0]) hF.1 h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [acceptParamPins0]) hF.1 h0
  have ek : (ctlCell litJ).eval τ = k := by
    rw [ctlCell_eval, h0]
    exact hk
  unfold acceptHaltVarEParam
  rw [denseStateE_eval, listGetE_eval, eW, eT, ek]
  simp [Expr.eval]

def acceptHaltProgParam (n m wReg tReg : ℕ) (qs : List ℕ) : Program :=
  writeAtLeastOneProg wpJ litJ (.const qs.length)
    (acceptHaltVarEParam n m wReg tReg qs)

lemma accept_halt_writer_param
    (M Jmax n W m T outBase wReg tReg obReg : ℕ) (outIdx qs : List ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptHaltProgParam n m wReg tReg qs)
      M Jmax wpJ
      (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase)
        outBase outIdx)
      [atLeastOne (qs.map fun qi => (denseLayout n W m).state T qi)] := by
  let pins := acceptParamPins0 wReg tReg obReg W T outBase
  have hctlbase : M + ctlJmax < outBase := by
    have := hplace.w_min
    have := hplace.w_t
    have := hplace.t_ob
    unfold ctlJmax
    omega
  have hpin : ∀ q ∈ pins,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ ∧ q.1 ≠ litJ := by
    intro q hq
    have h := accept_param_pins0_ok Jmax wReg tReg obReg W T outBase litJ hplace
      (by unfold litJ ctlJmax; omega) q hq
    exact ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩
  refine clauseWriter_atLeastOne_word M Jmax litJ (.const qs.length)
    (acceptHaltVarEParam n m wReg tReg qs) pins
    (qs.map fun qi => (denseLayout n W m).state T qi) outBase outIdx
    (by unfold litJ; omega)
    (by unfold litJ wpJ; omega) (by unfold litJ ctlJmax; omega)
    hpin hctlbase hfit
    (fun τ _ _ => by simp [Expr.eval, List.length_map])
    (fun _ _ _ _ _ => rfl) ?_ ?_
  · intro σ1 σ2 h1 h2 hagree
    exact accept_halt_var_e_param_frame M Jmax n m wReg tReg obReg qs hplace
      σ2 σ1 h2 h1
      (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
  · intro τ k hF h0 hk hlt
    rw [accept_halt_var_e_param_value_word M n W m T outBase wReg tReg obReg
      qs outIdx τ k hF h0 hk, map_getD_of_lt]
    simpa using hlt

/-! ## Complete parameterized accept family -/

def acceptFamilyProgParam (n m : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (wReg tReg obReg : ℕ) : Program :=
  .seq
    (acceptOuterProgParam n m d.blankIdx outIdx.length wReg tReg obReg)
    (acceptHaltProgParam n m wReg tReg
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)))

lemma acceptFamilyProgParam_writer_param
    (M Jmax n W m T outBase : ℕ) (d : TableauDescriptor)
    (outIdx : List ℕ) (wReg tReg obReg : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptFamilyProgParam n m d outIdx wReg tReg obReg)
      M Jmax wpJ
      (AcceptParamFrozen M wReg tReg obReg W T outBase outIdx)
      (descAcceptClauses (denseLayout n W m) d outIdx W T) := by
  unfold descAcceptClauses acceptFamilyProgParam AcceptParamFrozen
  exact clauseWriter_seq _ _ M Jmax wpJ
    (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase)
      outBase outIdx) _ _
    (accept_p_head_loop_writer_param M Jmax n W m T outBase d.blankIdx
      wReg tReg obReg outIdx hplace hbase hfit)
    (accept_halt_writer_param M Jmax n W m T outBase wReg tReg obReg outIdx
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0))
      hplace hbase hfit)

end NPComplete.CookLevin

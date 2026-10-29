module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTrans
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteFrozen

/-!
The transition family has five run-time inputs: the tableau width and time
bound, and the base addresses of its three transition-table columns.  This
file keeps all five values out of `Program` syntax.  Guards read the columns
through base-address cells.  Accepting branches stage the selected `arg1` and
`arg2` values in the otherwise unused `litJ` and `tmpJ` control cells before
writing clauses, so every expression used by `writeClauseProg` has a static
frame bound.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## Parameter and table placement -/

structure TransParamPlacement
    (Jmax wReg tReg kbReg a1Reg a2Reg : ℕ) : Prop where
  ctl_le : ctlJmax ≤ Jmax
  w_min : 15 ≤ wReg
  w_t : wReg < tReg
  t_kb : tReg < kbReg
  kb_a1 : kbReg < a1Reg
  a1_a2 : a1Reg < a2Reg
  a2_le : a2Reg ≤ Jmax

structure TransParamTablePlacement
    (M Jmax a2Reg kindBase lenk arg1Base len1 arg2Base len2 : ℕ) : Prop where
  params_kind : M + a2Reg + 1 < kindBase
  kind_arg1 : kindBase + lenk < arg1Base
  arg1_arg2 : arg1Base + len1 < arg2Base
  arg2_fit : arg2Base + len2 ≤ M + Jmax

def transWReg : ℕ := 15
def transTReg : ℕ := 16
def transKindBaseReg : ℕ := 20
def transArg1BaseReg : ℕ := 21
def transArg2BaseReg : ℕ := 22
def transParamCellJmax : ℕ := 22

lemma trans_param_fixed_placement :
    TransParamPlacement transParamCellJmax transWReg transTReg
      transKindBaseReg transArg1BaseReg transArg2BaseReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [transParamCellJmax, transWReg, transTReg, transKindBaseReg,
      transArg1BaseReg, transArg2BaseReg, ctlJmax]

lemma trans_param_placement_satisfiable :
    ∃ Jmax wReg tReg kbReg a1Reg a2Reg,
      TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg :=
  ⟨transParamCellJmax, transWReg, transTReg, transKindBaseReg,
    transArg1BaseReg, transArg2BaseReg, trans_param_fixed_placement⟩

lemma trans_param_full_placement_satisfiable (M lenk len1 len2 : ℕ) :
    ∃ Jmax kindBase arg1Base arg2Base,
      TransParamPlacement Jmax transWReg transTReg transKindBaseReg
        transArg1BaseReg transArg2BaseReg ∧
      TransParamTablePlacement M Jmax transArg2BaseReg
        kindBase lenk arg1Base len1 arg2Base len2 := by
  refine ⟨26 + lenk + len1 + len2, M + 24, M + 25 + lenk,
    M + 26 + lenk + len1, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [transWReg, transTReg, transKindBaseReg, transArg1BaseReg,
        transArg2BaseReg, ctlJmax] <;> omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [transArg2BaseReg]
    · omega
    · omega
    · omega

lemma trans_param_bases_above_ctl
    (M Jmax a2Reg kindBase arg1Base arg2Base lenk len1 len2 : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase lenk
      arg1Base len1 arg2Base len2) :
    M + ctlJmax < kindBase ∧ M + ctlJmax < arg1Base ∧
      M + ctlJmax < arg2Base := by
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have htk := hplace.t_kb
  have hka := hplace.kb_a1
  have haa := hplace.a1_a2
  have hb := htable.params_kind
  have hk := htable.kind_arg1
  have h1 := htable.arg1_arg2
  unfold ctlJmax
  omega

lemma trans_param_words_below
    (M Jmax a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    WordBelow kindBase colk.length (M + Jmax + 1) ∧
      WordBelow arg1Base col1.length (M + Jmax + 1) ∧
      WordBelow arg2Base col2.length (M + Jmax + 1) := by
  have hb := htable.params_kind
  have hk := htable.kind_arg1
  have h1 := htable.arg1_arg2
  have h2 := htable.arg2_fit
  unfold WordBelow
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-! ## Parameter pins -/

def transParamPins0
    (wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base : ℕ) :
    List (ℕ × ℕ) :=
  [(wReg, W), (tReg, T), (kbReg, kindBase), (a1Reg, arg1Base), (a2Reg, arg2Base)]

def transParamPins1
    (wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t : ℕ) :
    List (ℕ × ℕ) :=
  (lvJ0, t) :: transParamPins0 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base

def transParamPins2
    (wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p : ℕ) :
    List (ℕ × ℕ) :=
  (lvJ1, p) :: transParamPins1 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t

def transParamPins3
    (wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi : ℕ) :
    List (ℕ × ℕ) :=
  (lvJ2, qi) :: transParamPins2 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p

def transParamPins4
    (wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai : ℕ) :
    List (ℕ × ℕ) :=
  (lvJ3, ai) :: transParamPins3 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi

abbrev TransParamFrozen
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) : Store → Prop :=
  TransFrozen M
    (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
    kindBase colk arg1Base col1 arg2Base col2

lemma trans_param_pins0_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base iJ : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hiJctl : iJ ≤ ctlJmax) :
    ∀ q ∈ transParamPins0 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  simp only [transParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have htk := hplace.t_kb
  have hka := hplace.kb_a1
  have haa := hplace.a1_a2
  have hle := hplace.a2_le
  unfold ctlJmax at hiJctl
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by omega, by omega, by omega, by unfold wpJ; omega⟩

lemma trans_param_pins1_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t iJ : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hiJctl : iJ ≤ ctlJmax) (h0 : lvJ0 ≠ iJ) :
    ∀ q ∈ transParamPins1 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ0; omega,
      Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le, h0,
      by unfold lvJ0 wpJ; omega⟩
  · exact trans_param_pins0_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base iJ hplace hiJctl q hq

lemma trans_param_pins2_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p iJ : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hiJctl : iJ ≤ ctlJmax) (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) :
    ∀ q ∈ transParamPins2 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ1; omega,
      Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le, h1,
      by unfold lvJ1 wpJ; omega⟩
  · exact trans_param_pins1_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t iJ hplace hiJctl h0 q hq

lemma trans_param_pins3_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi iJ : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hiJctl : iJ ≤ ctlJmax) (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ)
    (h2 : lvJ2 ≠ iJ) :
    ∀ q ∈ transParamPins3 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ2; omega,
      Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le, h2,
      by unfold lvJ2 wpJ; omega⟩
  · exact trans_param_pins2_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p iJ hplace hiJctl h0 h1 q hq

lemma trans_param_pins4_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      t p qi ai iJ : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hiJctl : iJ ≤ ctlJmax) (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ)
    (h2 : lvJ2 ≠ iJ) (h3 : lvJ3 ≠ iJ) :
    ∀ q ∈ transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ3; omega,
      Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le, h3,
      by unfold lvJ3 wpJ; omega⟩
  · exact trans_param_pins3_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi iJ hplace hiJctl h0 h1 h2 q hq

/-! ## Dynamic column bases -/

def wordReadEBaseParam (baseReg blank len : ℕ) (kE : Expr) : Expr :=
  wordReadEExpr (ctlCell baseReg) (.const len) blank kE

lemma word_read_e_base_param_eval
    (σ : Store) (base blank baseReg : ℕ) (xs : List ℕ) (kE : Expr)
    (hbase : (ctlCell baseReg).eval σ = base) (hw : WordAt σ base xs) :
    (wordReadEBaseParam baseReg blank xs.length kE).eval σ
      = xs.getD (kE.eval σ) blank := by
  exact wordReadEExpr_eval σ base blank xs (ctlCell baseReg) (.const xs.length) kE
    hbase (by simp [Expr.eval]) hw

def transKindEParam (kbReg lenk mC : ℕ) : Expr :=
  wordReadEBaseParam kbReg 0 lenk (transIdxE mC)

def transArg1EParam (a1Reg len1 mC : ℕ) : Expr :=
  wordReadEBaseParam a1Reg 0 len1 (transIdxE mC)

def transArg2EParam (a2Reg len2 mC : ℕ) : Expr :=
  wordReadEBaseParam a2Reg 0 len2 (transIdxE mC)

lemma trans_col_e_param_value
    (M baseReg base mC t p qi ai : ℕ) (pins : List (ℕ × ℕ))
    (τ : Store) (col : List ℕ) (hmem : (baseReg, base) ∈ pins)
    (hF : PinsHold M pins τ) (hctl : PinsHold M (ctlPins3 t p qi) τ)
    (h0 : τ 0 = M)
    (hai : τ (M + lvJ3) = ai) (hw : WordAt τ base col) :
    (wordReadEBaseParam baseReg 0 col.length (transIdxE mC)).eval τ
      = col.getD (qi * mC + ai) 0 := by
  have eB : (ctlCell baseReg).eval τ = base :=
    ctlCell_eval_of_pin M pins baseReg base τ hmem hF h0
  rw [word_read_e_base_param_eval τ base 0 baseReg col (transIdxE mC) eB hw]
  rw [transIdxE_value M mC t p qi ai τ hctl h0 hai]

/-! ## Static expressions after staging -/

def transStateEParam (nS mS wReg : ℕ) : Expr :=
  denseStateE (.const nS) (ctlCell wReg) (.const mS) (ctlCell lvJ0) (ctlCell lvJ2)

def transHeadEParam (nS mS wReg : ℕ) : Expr :=
  denseHeadE (.const nS) (ctlCell wReg) (.const mS) (ctlCell lvJ0) (ctlCell lvJ1)

def transCellEParam (nS mS wReg : ℕ) : Expr :=
  denseCellE (.const nS) (ctlCell wReg) (.const mS)
    (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ3)

def transStateSameEParam (nS mS wReg : ℕ) : Expr :=
  denseStateE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ2)

def transHeadSameEParam (nS mS wReg : ℕ) : Expr :=
  denseHeadE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1)

def transCellSameEParam (nS mS wReg : ℕ) : Expr :=
  denseCellE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1) (ctlCell lvJ3)

def transStateNextEParam (nS mS wReg : ℕ) : Expr :=
  denseStateE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell litJ)

def transCellWriteEParam (nS mS wReg : ℕ) : Expr :=
  denseCellE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1) (ctlCell tmpJ)

def transHeadMoveEParam (nS mS wReg : ℕ) : Expr :=
  denseHeadE (.const nS) (ctlCell wReg) (.const mS)
    (.add (ctlCell lvJ0) (.const 1))
    (.sub (.add (ctlCell lvJ1) (ctlCell tmpJ))
      (.sub (.const 1) (ctlCell tmpJ)))

def moveOkEParam (wReg : ℕ) (pE dirE : Expr) : Expr :=
  .add
    (.mul (.sub (.const 1) dirE) (.lt (.const 0) pE))
    (.mul dirE (.lt (.add pE (.const 1)) (ctlCell wReg)))

lemma trans_param_reg_frame
    (M Jmax wReg tReg kbReg a1Reg a2Reg j : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (hj : j = wReg ∨ j = tReg ∨ j = kbReg ∨ j = a1Reg ∨ j = a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have htk := hplace.t_kb
  have hka := hplace.kb_a1
  have haa := hplace.a1_a2
  have hle := hplace.a2_le
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  have hjle : j ≤ Jmax := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  have hjwp : j ≠ wpJ := by
    unfold wpJ
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  exact ctlCell_frame M Jmax j hj1 hjle hjwp σ σ' hσ hσ' hagree

lemma trans_param_ctl_frame (M Jmax j : ℕ) (hJ : ctlJmax ≤ Jmax)
    (hj : j = lvJ0 ∨ j = lvJ1 ∨ j = lvJ2 ∨ j = lvJ3 ∨ j = litJ ∨ j = tmpJ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  have hj1 : 1 ≤ j := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [lvJ0, lvJ1, lvJ2, lvJ3, litJ, tmpJ]
  have hjctl : j ≤ ctlJmax := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [lvJ0, lvJ1, lvJ2, lvJ3, litJ, tmpJ, ctlJmax]
  have hjwp : j ≠ wpJ := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [lvJ0, lvJ1, lvJ2, lvJ3, litJ, tmpJ, wpJ]
  exact ctlCell_frame M Jmax j hj1 (Nat.le_trans hjctl hJ) hjwp
    σ σ' hσ hσ' hagree

lemma trans_state_e_param_frame (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transStateEParam nS mS wReg).eval σ' =
      (transStateEParam nS mS wReg).eval σ := by
  unfold transStateEParam
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (trans_param_ctl_frame M Jmax lvJ2 hplace.ctl_le (Or.inr (Or.inr (Or.inl rfl)))
      σ σ' hσ hσ' hagree)

lemma trans_head_e_param_frame (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transHeadEParam nS mS wReg).eval σ' =
      (transHeadEParam nS mS wReg).eval σ := by
  unfold transHeadEParam
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)

lemma trans_cell_e_param_frame (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transCellEParam nS mS wReg).eval σ' =
      (transCellEParam nS mS wReg).eval σ := by
  unfold transCellEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)
    (trans_param_ctl_frame M Jmax lvJ3 hplace.ctl_le
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) σ σ' hσ hσ' hagree)

lemma trans_state_same_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transStateSameEParam nS mS wReg).eval σ' =
      (transStateSameEParam nS mS wReg).eval σ := by
  unfold transStateSameEParam
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (expr_add_one_eval_congr _ σ σ'
      (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
        σ σ' hσ hσ' hagree))
    (trans_param_ctl_frame M Jmax lvJ2 hplace.ctl_le (Or.inr (Or.inr (Or.inl rfl)))
      σ σ' hσ hσ' hagree)

lemma trans_head_same_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transHeadSameEParam nS mS wReg).eval σ' =
      (transHeadSameEParam nS mS wReg).eval σ := by
  unfold transHeadSameEParam
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (expr_add_one_eval_congr _ σ σ'
      (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
        σ σ' hσ hσ' hagree))
    (trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)

lemma trans_cell_same_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transCellSameEParam nS mS wReg).eval σ' =
      (transCellSameEParam nS mS wReg).eval σ := by
  unfold transCellSameEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree) rfl
    (expr_add_one_eval_congr _ σ σ'
      (trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
        σ σ' hσ hσ' hagree))
    (trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)
    (trans_param_ctl_frame M Jmax lvJ3 hplace.ctl_le
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) σ σ' hσ hσ' hagree)

lemma trans_state_next_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transStateNextEParam nS mS wReg).eval σ' =
      (transStateNextEParam nS mS wReg).eval σ := by
  unfold transStateNextEParam
  rw [denseStateE_eval, denseStateE_eval]
  simp only [Expr.eval]
  rw [trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax litJ hplace.ctl_le
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) σ σ' hσ hσ' hagree]

lemma trans_cell_write_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transCellWriteEParam nS mS wReg).eval σ' =
      (transCellWriteEParam nS mS wReg).eval σ := by
  unfold transCellWriteEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax tmpJ hplace.ctl_le
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) σ σ' hσ hσ' hagree]

lemma trans_head_move_e_param_frame
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ →
      σ' (M + k) = σ (M + k)) :
    (transHeadMoveEParam nS mS wReg).eval σ' =
      (transHeadMoveEParam nS mS wReg).eval σ := by
  unfold transHeadMoveEParam
  rw [denseHeadE_eval, denseHeadE_eval]
  simp only [Expr.eval]
  rw [trans_param_reg_frame M Jmax wReg tReg kbReg a1Reg a2Reg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax lvJ1 hplace.ctl_le (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree,
    trans_param_ctl_frame M Jmax tmpJ hplace.ctl_le
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) σ σ' hσ hσ' hagree]

lemma clause_writer_io_stage_words3_value
    (M Jmax reg basek base1 base2 av : ℕ) (xsk xs1 xs2 : List ℕ)
    (pins : List (ℕ × ℕ)) (aE : Expr)
    (hreg1 : 1 ≤ reg) (hregJ : reg ≤ Jmax) (hregwp : reg ≠ wpJ)
    (hpin : ∀ q ∈ pins, q.1 ≠ reg)
    (hbasek : M + reg + 1 < basek) (hbase1 : M + reg + 1 < base1)
    (hbase2 : M + reg + 1 < base2)
    (hval : ∀ τ : Store,
      PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ →
      τ 0 = M → aE.eval τ = av) :
    ClauseWriterIO (ctlAssign reg aE) M Jmax wpJ
      (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2)
      (PinsAndWords3 M ((reg, av) :: pins) basek xsk base1 xs1 base2 xs2) [] := by
  intro τ wp hF h0 hw _
  have heval : (ctlAssign reg aE).eval τ = writeReg τ (M + reg) av := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0, hval τ hF h0]
  rw [heval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply pinsAndWords3_cons M (reg, av) pins basek xsk base1 xs1 base2 xs2
      (writeReg τ (M + reg) av)
    · rw [writeReg_same]
    · exact pinsAndWords3_writeReg M pins basek xsk base1 xs1 base2 xs2
        (M + reg) av τ hF
        (fun q hq => by have := hpin q hq; omega)
        (by omega) (fun k _ => by omega)
        (by omega) (fun k _ => by omega)
        (by omega) (fun k _ => by omega)
  · rw [writeReg_diff τ (M + reg) av 0 (by omega), h0]
  · rw [List.length_nil, rowTableWidth_zero, Nat.add_zero,
      writeReg_diff τ (M + reg) av (M + wpJ) (by omega), hw]
  · exact rowsWritten_nil _ wp
  · intro r _ hr
    rw [writeReg_diff]
    unfold CtlFree at hr
    omega

lemma trans_param_pins4_ctl
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai : ℕ)
    (τ : Store)
    (hF : PinsHold M (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai) τ) :
    PinsHold M (ctlPins3 t p qi) τ := by
  intro q hq
  apply hF q
  simp only [ctlPins3, List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [transParamPins4, transParamPins3, transParamPins2, transParamPins1,
    List.mem_cons]
  rcases hq with rfl | rfl | rfl <;> simp

lemma trans_kind_e_param_value
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      mC t p qi ai : ℕ) (τ : Store) (colk col1 col2 : List ℕ)
    (hF : PinsAndWords3 M
      (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
        t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ)
    (h0 : τ 0 = M) :
    (transKindEParam kbReg colk.length mC).eval τ =
      colk.getD (qi * mC + ai) 0 := by
  exact trans_col_e_param_value M kbReg kindBase mC t p qi ai _ τ colk
    (by simp [transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hF.1
    (trans_param_pins4_ctl M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base
      arg2Base t p qi ai τ hF.1) h0
    (pinsHold_head M (lvJ3, ai) _ τ hF.1) hF.2.1

lemma trans_arg1_e_param_value
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      mC t p qi ai : ℕ) (τ : Store) (colk col1 col2 : List ℕ)
    (hF : PinsAndWords3 M
      (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
        t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ)
    (h0 : τ 0 = M) :
    (transArg1EParam a1Reg col1.length mC).eval τ =
      col1.getD (qi * mC + ai) 0 := by
  exact trans_col_e_param_value M a1Reg arg1Base mC t p qi ai _ τ col1
    (by simp [transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hF.1
    (trans_param_pins4_ctl M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base
      arg2Base t p qi ai τ hF.1) h0
    (pinsHold_head M (lvJ3, ai) _ τ hF.1) hF.2.2.1

lemma trans_arg2_e_param_value
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      mC t p qi ai : ℕ) (τ : Store) (colk col1 col2 : List ℕ)
    (hF : PinsAndWords3 M
      (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
        t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ)
    (h0 : τ 0 = M) :
    (transArg2EParam a2Reg col2.length mC).eval τ =
      col2.getD (qi * mC + ai) 0 := by
  exact trans_col_e_param_value M a2Reg arg2Base mC t p qi ai _ τ col2
    (by simp [transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hF.1
    (trans_param_pins4_ctl M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base
      arg2Base t p qi ai τ hF.1) h0
    (pinsHold_head M (lvJ3, ai) _ τ hF.1) hF.2.2.2

lemma trans_state_e_param_value
    (M nS W mS wReg t qi : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ)
    (hw : (wReg, W) ∈ pins) (ht : (lvJ0, t) ∈ pins) (hq : (lvJ2, qi) ∈ pins)
    (h0 : τ 0 = M) :
    (transStateEParam nS mS wReg).eval τ = (denseLayout nS W mS).state t qi := by
  unfold transStateEParam
  exact denseStateE_eval_eq _ _ _ _ _ τ nS W mS t qi rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0)
    (ctlCell_eval_of_pin M pins lvJ2 qi τ hq hF h0)

lemma trans_head_e_param_value
    (M nS W mS wReg t p : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ)
    (hw : (wReg, W) ∈ pins) (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins)
    (h0 : τ 0 = M) :
    (transHeadEParam nS mS wReg).eval τ = (denseLayout nS W mS).head t p := by
  unfold transHeadEParam
  exact denseHeadE_eval_eq _ _ _ _ _ τ nS W mS t p rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0)
    (ctlCell_eval_of_pin M pins lvJ1 p τ hp hF h0)

lemma trans_cell_e_param_value
    (M nS W mS wReg t p ai : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ) (hw : (wReg, W) ∈ pins)
    (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins) (ha : (lvJ3, ai) ∈ pins)
    (h0 : τ 0 = M) :
    (transCellEParam nS mS wReg).eval τ = (denseLayout nS W mS).cell t p ai := by
  unfold transCellEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ nS W mS t p ai rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0)
    (ctlCell_eval_of_pin M pins lvJ1 p τ hp hF h0)
    (ctlCell_eval_of_pin M pins lvJ3 ai τ ha hF h0)

lemma trans_state_same_e_param_value
    (M nS W mS wReg t qi : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ) (hw : (wReg, W) ∈ pins)
    (ht : (lvJ0, t) ∈ pins) (hq : (lvJ2, qi) ∈ pins) (h0 : τ 0 = M) :
    (transStateSameEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).state (t + 1) qi := by
  unfold transStateSameEParam
  exact denseStateE_eval_eq _ _ _ _ _ τ nS W mS (t + 1) qi rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0))
    (ctlCell_eval_of_pin M pins lvJ2 qi τ hq hF h0)

lemma trans_head_same_e_param_value
    (M nS W mS wReg t p : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ) (hw : (wReg, W) ∈ pins)
    (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins) (h0 : τ 0 = M) :
    (transHeadSameEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).head (t + 1) p := by
  unfold transHeadSameEParam
  exact denseHeadE_eval_eq _ _ _ _ _ τ nS W mS (t + 1) p rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0))
    (ctlCell_eval_of_pin M pins lvJ1 p τ hp hF h0)

lemma trans_cell_same_e_param_value
    (M nS W mS wReg t p ai : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M pins τ) (hw : (wReg, W) ∈ pins)
    (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins) (ha : (lvJ3, ai) ∈ pins)
    (h0 : τ 0 = M) :
    (transCellSameEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).cell (t + 1) p ai := by
  unfold transCellSameEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ nS W mS (t + 1) p ai rfl
    (ctlCell_eval_of_pin M pins wReg W τ hw hF h0) rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M pins lvJ0 t τ ht hF h0))
    (ctlCell_eval_of_pin M pins lvJ1 p τ hp hF h0)
    (ctlCell_eval_of_pin M pins lvJ3 ai τ ha hF h0)

lemma trans_state_next_e_param_value
    (M nS W mS wReg t a1 a2 : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M ((tmpJ, a2) :: (litJ, a1) :: pins) τ)
    (hw : (wReg, W) ∈ pins) (ht : (lvJ0, t) ∈ pins) (h0 : τ 0 = M) :
    (transStateNextEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).state (t + 1) a1 := by
  have eW := ctlCell_eval_of_pin M _ wReg W τ (by simp [hw]) hF h0
  have e0 := ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ht]) hF h0
  have ea := ctlCell_eval_of_pin M _ litJ a1 τ (by simp) hF h0
  unfold transStateNextEParam
  rw [denseStateE_eval]
  simp only [Expr.eval, eW, e0, ea]

lemma trans_cell_write_e_param_value
    (M nS W mS wReg t p a1 a2 : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M ((tmpJ, a2) :: (litJ, a1) :: pins) τ)
    (hw : (wReg, W) ∈ pins) (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins)
    (h0 : τ 0 = M) :
    (transCellWriteEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).cell (t + 1) p a2 := by
  have eW := ctlCell_eval_of_pin M _ wReg W τ (by simp [hw]) hF h0
  have e0 := ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ht]) hF h0
  have e1 := ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [hp]) hF h0
  have ea := ctlCell_eval_of_pin M _ tmpJ a2 τ (by simp) hF h0
  unfold transCellWriteEParam
  rw [denseCellE_eval]
  simp only [Expr.eval, eW, e0, e1, ea]

lemma trans_head_move_e_param_value
    (M nS W mS wReg t p a1 a2 p' : ℕ) (τ : Store) (pins : List (ℕ × ℕ))
    (hF : PinsHold M ((tmpJ, a2) :: (litJ, a1) :: pins) τ)
    (hw : (wReg, W) ∈ pins) (ht : (lvJ0, t) ∈ pins) (hp : (lvJ1, p) ∈ pins)
    (h0 : τ 0 = M) (hp' : p' = p + a2 - (1 - a2)) :
    (transHeadMoveEParam nS mS wReg).eval τ =
      (denseLayout nS W mS).head (t + 1) p' := by
  have eW := ctlCell_eval_of_pin M _ wReg W τ (by simp [hw]) hF h0
  have e0 := ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ht]) hF h0
  have e1 := ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [hp]) hF h0
  have ea := ctlCell_eval_of_pin M _ tmpJ a2 τ (by simp) hF h0
  unfold transHeadMoveEParam
  rw [denseHeadE_eval]
  simp only [Expr.eval, eW, e0, e1, ea]
  rw [hp']

lemma move_ok_e_param_value
    (M wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      mC t p qi ai : ℕ) (τ : Store) (colk col1 col2 : List ℕ)
    (hF : PinsAndWords3 M
      (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
        t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ)
    (h0 : τ 0 = M) :
    (moveOkEParam wReg (ctlCell lvJ1)
      (transArg2EParam a2Reg col2.length mC)).eval τ =
      moveOk W p (col2.getD (qi * mC + ai) 0) := by
  have eW := ctlCell_eval_of_pin M _ wReg W τ
    (by simp [transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hF.1 h0
  have ep := ctlCell_eval_of_pin M _ lvJ1 p τ
    (by simp [transParamPins4, transParamPins3, transParamPins2]) hF.1 h0
  have ea := trans_arg2_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
  unfold moveOkEParam moveOk
  simp only [Expr.eval, eW, ep, ea]

/-! ## Wide single-clause and block writers -/

def ParamExprFrame (M Jmax wpJV : ℕ) (e : Expr) : Prop :=
  ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
    (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJV → σ' (M + j) = σ (M + j)) →
    e.eval σ' = e.eval σ

def FrozenExprValue (Frozen : Store → Prop) (M : ℕ) (e : Expr) (v : ℕ) : Prop :=
  ∀ τ : Store, Frozen τ → τ 0 = M → e.eval τ = v

lemma imply3_writer_words3_param
    (M Jmax wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (pins : List (ℕ × ℕ))
    (aE bE cE dE : Expr) (av bv cv dv : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hfa : ParamExprFrame M Jmax wpJ aE) (hfb : ParamExprFrame M Jmax wpJ bE)
    (hfc : ParamExprFrame M Jmax wpJ cE) (hfd : ParamExprFrame M Jmax wpJ dE)
    (hva : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M aE av)
    (hvb : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M bE bv)
    (hvc : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M cE cv)
    (hvd : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M dE dv) :
    ClauseWriter (writeClauseProg wpJ (imply3Lits aE bE cE dE)) M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [imply3 av bv cv dv] := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  obtain ⟨hwk, hw1, hw2⟩ := trans_param_words_below M Jmax a2Reg
    kindBase arg1Base arg2Base colk col1 col2 htable
  refine clauseWriter_clause_below_words3 M Jmax _ pins _ kindBase colk
    arg1Base col1 arg2Base col2 (Nat.le_trans wpJ_le hplace.ctl_le)
    hpin hbk hb1 hb2 hwk hw1 hw2 ?_ rfl ?_
  · intro l hl bound σ σ' hσ hσ' hbound hagree
    simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ aE hfa bound σ σ' hσ hσ'
        hbound hagree⟩
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ bE hfb bound σ σ' hσ hσ'
        hbound hagree⟩
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ cE hfc bound σ σ' hσ hσ'
        hbound hagree⟩
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ dE hfd bound σ σ' hσ hσ'
        hbound hagree⟩
  · intro τ k hF h0 hk
    rw [imply3Lits_length] at hk
    interval_cases k
    · rw [imply3Lits_get0, imply3_var0]
      exact ⟨rfl, hva τ hF h0⟩
    · rw [imply3Lits_get1, imply3_var1]
      exact ⟨rfl, hvb τ hF h0⟩
    · rw [imply3Lits_get2, imply3_var2]
      exact ⟨rfl, hvc τ hF h0⟩
    · rw [imply3Lits_get3, imply3_var3]
      exact ⟨rfl, hvd τ hF h0⟩

lemma forbid3_writer_words3_param
    (M Jmax wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (pins : List (ℕ × ℕ))
    (aE bE cE : Expr) (av bv cv : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hfa : ParamExprFrame M Jmax wpJ aE) (hfb : ParamExprFrame M Jmax wpJ bE)
    (hfc : ParamExprFrame M Jmax wpJ cE)
    (hva : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M aE av)
    (hvb : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M bE bv)
    (hvc : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M cE cv) :
    ClauseWriter (writeClauseProg wpJ (forbid3Lits aE bE cE)) M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 av bv cv] := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  obtain ⟨hwk, hw1, hw2⟩ := trans_param_words_below M Jmax a2Reg
    kindBase arg1Base arg2Base colk col1 col2 htable
  refine clauseWriter_clause_below_words3 M Jmax _ pins _ kindBase colk
    arg1Base col1 arg2Base col2 (Nat.le_trans wpJ_le hplace.ctl_le)
    hpin hbk hb1 hb2 hwk hw1 hw2 ?_ rfl ?_
  · intro l hl bound σ σ' hσ hσ' hbound hagree
    simp only [forbid3Lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ aE hfa bound σ σ' hσ hσ'
        hbound hagree⟩
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ bE hfb bound σ σ' hσ hσ'
        hbound hagree⟩
    · exact ⟨rfl, ctl_frame_below M Jmax wpJ cE hfc bound σ σ' hσ hσ'
        hbound hagree⟩
  · intro τ k hF h0 hk
    rw [forbid3Lits_length] at hk
    interval_cases k
    · rw [forbid3Lits_get0, forbid3_var0]
      exact ⟨rfl, hva τ hF h0⟩
    · rw [forbid3Lits_get1, forbid3_var1]
      exact ⟨rfl, hvb τ hF h0⟩
    · rw [forbid3Lits_get2, forbid3_var2]
      exact ⟨rfl, hvc τ hF h0⟩

lemma imply3_block_words3_param
    (M Jmax wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (pins : List (ℕ × ℕ))
    (aE bE cE dE1 dE2 dE3 : Expr) (av bv cv dv1 dv2 dv3 : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hfa : ParamExprFrame M Jmax wpJ aE) (hfb : ParamExprFrame M Jmax wpJ bE)
    (hfc : ParamExprFrame M Jmax wpJ cE)
    (hfd1 : ParamExprFrame M Jmax wpJ dE1)
    (hfd2 : ParamExprFrame M Jmax wpJ dE2)
    (hfd3 : ParamExprFrame M Jmax wpJ dE3)
    (hva : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M aE av)
    (hvb : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M bE bv)
    (hvc : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M cE cv)
    (hvd1 : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M dE1 dv1)
    (hvd2 : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M dE2 dv2)
    (hvd3 : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M dE3 dv3) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits aE bE cE dE1))
        (writeClauseProg wpJ (imply3Lits aE bE cE dE2)))
        (writeClauseProg wpJ (imply3Lits aE bE cE dE3)))
      M Jmax wpJ (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [imply3 av bv cv dv1, imply3 av bv cv dv2, imply3 av bv cv dv3] :=
  clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (clauseWriter_seq _ _ M Jmax wpJ _ _ _
      (imply3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
        kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE dE1 av bv cv dv1
        hplace htable hpin hfa hfb hfc hfd1 hva hvb hvc hvd1)
      (imply3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
        kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE dE2 av bv cv dv2
        hplace htable hpin hfa hfb hfc hfd2 hva hvb hvc hvd2))
    (imply3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
      kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE dE3 av bv cv dv3
      hplace htable hpin hfa hfb hfc hfd3 hva hvb hvc hvd3)

lemma forbid3_block_words3_param
    (M Jmax wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (pins : List (ℕ × ℕ))
    (aE bE cE : Expr) (av bv cv : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hfa : ParamExprFrame M Jmax wpJ aE) (hfb : ParamExprFrame M Jmax wpJ bE)
    (hfc : ParamExprFrame M Jmax wpJ cE)
    (hva : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M aE av)
    (hvb : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M bE bv)
    (hvc : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M cE cv) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (forbid3Lits aE bE cE))
        (writeClauseProg wpJ (forbid3Lits aE bE cE)))
        (writeClauseProg wpJ (forbid3Lits aE bE cE)))
      M Jmax wpJ (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 av bv cv, forbid3 av bv cv, forbid3 av bv cv] :=
  clauseWriter_seq _ _ M Jmax wpJ _ _ _
    (clauseWriter_seq _ _ M Jmax wpJ _ _ _
      (forbid3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
        kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE av bv cv
        hplace htable hpin hfa hfb hfc hva hvb hvc)
      (forbid3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
        kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE av bv cv
        hplace htable hpin hfa hfb hfc hva hvb hvc))
    (forbid3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
      kindBase arg1Base arg2Base colk col1 col2 pins aE bE cE av bv cv
      hplace htable hpin hfa hfb hfc hva hvb hvc)

lemma trans_param_leaf_pins_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      t p qi ai : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg) :
    ∀ q ∈ transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
  intro q hq
  have h := trans_param_pins4_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai wpJ hplace wpJ_le
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ1 wpJ; omega)
    (by unfold lvJ2 wpJ; omega) (by unfold lvJ3 wpJ; omega) q hq
  exact ⟨h.1, h.2.1, h.2.2.2⟩

lemma trans_param_staged_pins_ok
    (Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      t p qi ai av1 av2 : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg) :
    ∀ q ∈ (tmpJ, av2) :: (litJ, av1) ::
      transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base t p qi ai,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold tmpJ; omega,
      Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le,
      by unfold tmpJ wpJ; omega⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold litJ; omega,
      Nat.le_trans (by unfold litJ ctlJmax; omega) hplace.ctl_le,
      by unfold litJ wpJ; omega⟩
  exact trans_param_leaf_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai hplace q hq

lemma trans_param_bases_above_scratch
    (M Jmax wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base
      lenk len1 len2 reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase lenk
      arg1Base len1 arg2Base len2) (hreg : reg ≤ ctlJmax) :
    M + reg + 1 < kindBase ∧ M + reg + 1 < arg1Base ∧
      M + reg + 1 < arg2Base := by
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have htk := hplace.t_kb
  have hka := hplace.kb_a1
  have haa := hplace.a1_a2
  have hb := htable.params_kind
  have hk := htable.kind_arg1
  have h1 := htable.arg1_arg2
  unfold ctlJmax at hreg
  omega

lemma trans_forbid3_block_writer_param
    (M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)))
        (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))))
        (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai),
       forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai),
       forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)] := by
  let pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  apply forbid3_block_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 pins
    (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
    (transCellEParam nS mS wReg) _ _ _ hplace htable
  · exact trans_param_leaf_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai hplace
  · exact trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · intro τ hF h0
    exact trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3]) h0
  · intro τ hF h0
    exact trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, transParamPins4]) h0

lemma trans_accept_halt_writer_param
    (M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transStateSameEParam nS mS wReg)))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transHeadSameEParam nS mS wReg))))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transCellSameEParam nS mS wReg))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).state (t + 1) qi),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).cell (t + 1) p ai)] := by
  let pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  apply imply3_block_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 pins
    (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
    (transCellEParam nS mS wReg) (transStateSameEParam nS mS wReg)
    (transHeadSameEParam nS mS wReg) (transCellSameEParam nS mS wReg)
    _ _ _ _ _ _ hplace htable
  · exact trans_param_leaf_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai hplace
  · exact trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_state_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · intro τ hF h0
    exact trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3]) h0
  · intro τ hF h0
    exact trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, transParamPins4]) h0
  · intro τ hF h0
    exact trans_state_same_e_param_value M nS W mS wReg t qi τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3]) h0
  · intro τ hF h0
    exact trans_head_same_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_same_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, transParamPins4]) h0

def transStageArgsProgParam (a1Reg a2Reg len1 len2 mC : ℕ) : Program :=
  .seq (ctlAssign litJ (transArg1EParam a1Reg len1 mC))
    (ctlAssign tmpJ (transArg2EParam a2Reg len2 mC))

lemma trans_stage_args_io_param
    (M Jmax wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
      mC t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriterIO
      (transStageArgsProgParam a1Reg a2Reg col1.length col2.length mC)
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (TransFrozen M
        ((tmpJ, col2.getD (qi * mC + ai) 0) ::
          (litJ, col1.getD (qi * mC + ai) 0) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
            kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) [] := by
  let pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  let av1 := col1.getD (qi * mC + ai) 0
  let av2 := col2.getD (qi * mC + ai) 0
  obtain ⟨hlk, hl1, hl2⟩ := trans_param_bases_above_scratch M Jmax wReg tReg
    kbReg a1Reg a2Reg kindBase arg1Base arg2Base colk.length col1.length
    col2.length litJ hplace htable (by unfold litJ ctlJmax; omega)
  obtain ⟨htk, ht1, ht2⟩ := trans_param_bases_above_scratch M Jmax wReg tReg
    kbReg a1Reg a2Reg kindBase arg1Base arg2Base colk.length col1.length
    col2.length tmpJ hplace htable (by unfold tmpJ ctlJmax; omega)
  have hstage1 : ClauseWriterIO
      (ctlAssign litJ (transArg1EParam a1Reg col1.length mC)) M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2) [] := by
    refine clause_writer_io_stage_words3_value M Jmax litJ kindBase arg1Base
      arg2Base av1 colk col1 col2 pins (transArg1EParam a1Reg col1.length mC)
      (by unfold litJ; omega)
      (Nat.le_trans (by unfold litJ ctlJmax; omega) hplace.ctl_le)
      (by unfold litJ wpJ; omega) ?_ hlk hl1 hl2 ?_
    · intro q hq
      have h := trans_param_pins4_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base t p qi ai litJ hplace
        (by unfold litJ ctlJmax; omega) (by unfold lvJ0 litJ; omega)
        (by unfold lvJ1 litJ; omega) (by unfold lvJ2 litJ; omega)
        (by unfold lvJ3 litJ; omega) q hq
      exact h.2.2.1
    · intro τ hF h0
      exact trans_arg1_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
  have hstage2 : ClauseWriterIO
      (ctlAssign tmpJ (transArg2EParam a2Reg col2.length mC)) M Jmax wpJ
      (PinsAndWords3 M ((litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((tmpJ, av2) :: (litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2) [] := by
    refine clause_writer_io_stage_words3_value M Jmax tmpJ kindBase arg1Base
      arg2Base av2 colk col1 col2 ((litJ, av1) :: pins)
      (transArg2EParam a2Reg col2.length mC) (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le)
      (by unfold tmpJ wpJ; omega) ?_ htk ht1 ht2 ?_
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · unfold litJ tmpJ
        omega
      · have h := trans_param_pins4_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
          kindBase arg1Base arg2Base t p qi ai tmpJ hplace
          (by unfold tmpJ ctlJmax; omega) (by unfold lvJ0 tmpJ; omega)
          (by unfold lvJ1 tmpJ; omega) (by unfold lvJ2 tmpJ; omega)
          (by unfold lvJ3 tmpJ; omega) q hq
        exact h.2.2.1
    · intro τ hF h0
      have htail := pinsAndWords3_tail M (litJ, av1) pins kindBase colk
        arg1Base col1 arg2Base col2 τ hF
      exact trans_arg2_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 htail h0
  simpa [transStageArgsProgParam, pins, av1, av2] using
    clauseWriterIO_seq _ _ M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((tmpJ, av2) :: (litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2) [] [] hstage1 hstage2

lemma trans_accept_write_block_writer_param
    (M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transStateNextEParam nS mS wReg)))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transHeadSameEParam nS mS wReg))))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transCellWriteEParam nS mS wReg))))
      M Jmax wpJ
      (TransFrozen M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
            kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).state (t + 1) av1),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).cell (t + 1) p av2)] := by
  let basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  let pins := (tmpJ, av2) :: (litJ, av1) :: basePins
  apply imply3_block_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 pins
    (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
    (transCellEParam nS mS wReg) (transStateNextEParam nS mS wReg)
    (transHeadSameEParam nS mS wReg) (transCellWriteEParam nS mS wReg)
    _ _ _ _ _ _ hplace htable
  · exact trans_param_staged_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai av1 av2 hplace
  · exact trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_state_next_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_write_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · intro τ hF h0
    exact trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3]) h0
  · intro τ hF h0
    exact trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, basePins, transParamPins4]) h0
  · intro τ hF h0
    exact trans_state_next_e_param_value M nS W mS wReg t av1 av2 τ basePins hF.1
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1]) h0
  · intro τ hF h0
    exact trans_head_same_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_write_e_param_value M nS W mS wReg t p av1 av2 τ basePins hF.1
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2]) h0

lemma trans_accept_write_writer_param
    (M Jmax nS W mS mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq
        (transStageArgsProgParam a1Reg a2Reg col1.length col2.length mC)
        (.seq (.seq
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transStateNextEParam nS mS wReg)))
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transHeadSameEParam nS mS wReg))))
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transCellWriteEParam nS mS wReg)))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0))] := by
  let basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  let av1 := col1.getD (qi * mC + ai) 0
  let av2 := col2.getD (qi * mC + ai) 0
  let stagedPins := (tmpJ, av2) :: (litJ, av1) :: basePins
  have hs := trans_stage_args_io_param M Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base mC t p qi ai colk col1 col2 hplace htable
  have hb := trans_accept_write_block_writer_param M Jmax nS W mS wReg tReg
    kbReg a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai av1 av2
    colk col1 col2 hplace htable
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    [] _ hs (clauseWriterIO_of_writer _ M Jmax wpJ _ _ hb)
  have hdrop := clauseWriterIO_weaken_exit _ M Jmax wpJ
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2) _
    (fun τ h => pinsAndWords3_tail M (litJ, av1) basePins kindBase colk
      arg1Base col1 arg2Base col2 τ
      (pinsAndWords3_tail M (tmpJ, av2) ((litJ, av1) :: basePins)
        kindBase colk arg1Base col1 arg2Base col2 τ h)) hseq
  simpa [ClauseWriterIO, ClauseWriter, basePins, stagedPins, av1, av2] using hdrop

lemma trans_accept_move_block_writer_param
    (M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transStateNextEParam nS mS wReg)))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transHeadMoveEParam nS mS wReg))))
        (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
          (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
          (transCellSameEParam nS mS wReg))))
      M Jmax wpJ
      (TransFrozen M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
            kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).state (t + 1) av1),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).head (t + 1) (p + av2 - (1 - av2))),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).cell (t + 1) p ai)] := by
  let basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  let pins := (tmpJ, av2) :: (litJ, av1) :: basePins
  apply imply3_block_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 pins
    (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
    (transCellEParam nS mS wReg) (transStateNextEParam nS mS wReg)
    (transHeadMoveEParam nS mS wReg) (transCellSameEParam nS mS wReg)
    _ _ _ _ _ _ hplace htable
  · exact trans_param_staged_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base t p qi ai av1 av2 hplace
  · exact trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_state_next_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_head_move_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · exact trans_cell_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
  · intro τ hF h0
    exact trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3]) h0
  · intro τ hF h0
    exact trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2]) h0
  · intro τ hF h0
    exact trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, basePins, transParamPins4]) h0
  · intro τ hF h0
    exact trans_state_next_e_param_value M nS W mS wReg t av1 av2 τ basePins hF.1
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1]) h0
  · intro τ hF h0
    exact trans_head_move_e_param_value M nS W mS wReg t p av1 av2
      (p + av2 - (1 - av2)) τ basePins hF.1
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [basePins, transParamPins4, transParamPins3, transParamPins2]) h0 rfl
  · intro τ hF h0
    exact trans_cell_same_e_param_value M nS W mS wReg t p ai τ pins hF.1
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1, transParamPins0])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2,
        transParamPins1])
      (by simp [pins, basePins, transParamPins4, transParamPins3, transParamPins2])
      (by simp [pins, basePins, transParamPins4]) h0

lemma trans_accept_move_writer_param
    (M Jmax nS W mS mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (.seq
        (transStageArgsProgParam a1Reg a2Reg col1.length col2.length mC)
        (.seq (.seq
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transStateNextEParam nS mS wReg)))
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transHeadMoveEParam nS mS wReg))))
          (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
            (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
            (transCellSameEParam nS mS wReg)))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).head (t + 1)
          (p + col2.getD (qi * mC + ai) 0 - (1 - col2.getD (qi * mC + ai) 0))),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).cell (t + 1) p ai)] := by
  let basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai
  let av1 := col1.getD (qi * mC + ai) 0
  let av2 := col2.getD (qi * mC + ai) 0
  let stagedPins := (tmpJ, av2) :: (litJ, av1) :: basePins
  have hs := trans_stage_args_io_param M Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base mC t p qi ai colk col1 col2 hplace htable
  have hb := trans_accept_move_block_writer_param M Jmax nS W mS wReg tReg
    kbReg a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai av1 av2
    colk col1 col2 hplace htable
  have hseq := clauseWriterIO_seq _ _ M Jmax wpJ
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    [] _ hs (clauseWriterIO_of_writer _ M Jmax wpJ _ _ hb)
  have hdrop := clauseWriterIO_weaken_exit _ M Jmax wpJ
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M stagedPins kindBase colk arg1Base col1 arg2Base col2)
    (PinsAndWords3 M basePins kindBase colk arg1Base col1 arg2Base col2) _
    (fun τ h => pinsAndWords3_tail M (litJ, av1) basePins kindBase colk
      arg1Base col1 arg2Base col2 τ
      (pinsAndWords3_tail M (tmpJ, av2) ((litJ, av1) :: basePins)
        kindBase colk arg1Base col1 arg2Base col2 τ h)) hseq
  simpa [ClauseWriterIO, ClauseWriter, basePins, stagedPins, av1, av2] using hdrop

def transForbidBlockProgParam (nS mS wReg : ℕ) : Program :=
  .seq (.seq
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)))
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))))
    (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)))

def transHaltBlockProgParam (nS mS wReg : ℕ) : Program :=
  .seq (.seq
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateSameEParam nS mS wReg)))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadSameEParam nS mS wReg))))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellSameEParam nS mS wReg)))

def transWriteBlockProgParam (nS mS wReg : ℕ) : Program :=
  .seq (.seq
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateNextEParam nS mS wReg)))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadSameEParam nS mS wReg))))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellWriteEParam nS mS wReg)))

def transMoveBlockProgParam (nS mS wReg : ℕ) : Program :=
  .seq (.seq
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateNextEParam nS mS wReg)))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadMoveEParam nS mS wReg))))
    (writeClauseProg wpJ (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellSameEParam nS mS wReg)))

def transAcceptWriteProgParam
    (nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) : Program :=
  .seq (transStageArgsProgParam a1Reg a2Reg len1 len2 mC)
    (transWriteBlockProgParam nS mS wReg)

def transAcceptMoveProgParam
    (nS mS mC wReg a1Reg a2Reg len1 len2 : ℕ) : Program :=
  .seq (transStageArgsProgParam a1Reg a2Reg len1 len2 mC)
    (transMoveBlockProgParam nS mS wReg)

lemma trans_leaf_write_branch_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter
      (.ifNZ (.lt (transArg1EParam a1Reg col1.length mC) (.const nC))
        (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg
          col1.length col2.length)
        (transForbidBlockProgParam nS mS wReg))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
        (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)) := by
  have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
      (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)
      = if col1.getD (qi * mC + ai) 0 < nC then
          [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)
            ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)
            ((denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0))]
        else
          [forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai),
           forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai),
           forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)] := by
    unfold natTransClausesTriple
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  rw [heq]
  refine clauseWriter_ifNZ _ _ _ M Jmax wpJ _ _
    (col1.getD (qi * mC + ai) 0 < nC) ?_ ?_ ?_
  · intro τ hF h0
    have hval := trans_arg1_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
    simp only [Expr.eval, hval]
    by_cases hlt : col1.getD (qi * mC + ai) 0 < nC <;> simp
  · intro hlt
    rw [ite_eq_left hlt]
    simpa [transAcceptWriteProgParam, transWriteBlockProgParam] using
      trans_accept_write_writer_param M Jmax nS W mS mC wReg tReg kbReg a1Reg
        a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
  · intro hnlt
    rw [ite_eq_right hnlt]
    simpa [transForbidBlockProgParam] using
      trans_forbid3_block_writer_param M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg
        T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable

lemma trans_leaf_move_branch_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter
      (.ifNZ (.lt (transArg1EParam a1Reg col1.length mC) (.const nC))
        (.ifNZ (moveOkEParam wReg (ctlCell lvJ1)
            (transArg2EParam a2Reg col2.length mC))
          (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg
            col1.length col2.length)
          (transForbidBlockProgParam nS mS wReg))
        (transForbidBlockProgParam nS mS wReg))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 2
        (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)) := by
  unfold natTransClausesTriple
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine clauseWriter_ifNZ _ _ _ M Jmax wpJ _ _
    (col1.getD (qi * mC + ai) 0 < nC) ?_ ?_ ?_
  · intro τ hF h0
    have hval := trans_arg1_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
    simp only [Expr.eval, hval]
    by_cases hlt : col1.getD (qi * mC + ai) 0 < nC <;> simp
  · intro hlt
    rw [ite_eq_left hlt]
    refine clauseWriter_ifNZ _ _ _ M Jmax wpJ _ _
      (moveOk W p (col2.getD (qi * mC + ai) 0) ≠ 0) ?_ ?_ ?_
    · intro τ hF h0
      rw [move_ok_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0]
    · intro hok
      rw [ite_eq_left hok]
      simpa [transAcceptMoveProgParam, transMoveBlockProgParam] using
        trans_accept_move_writer_param M Jmax nS W mS mC wReg tReg kbReg a1Reg
          a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
    · intro hnok
      rw [ite_eq_right hnok]
      simpa [transForbidBlockProgParam] using
        trans_forbid3_block_writer_param M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg
          T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
  · intro hnlt
    rw [ite_eq_right hnlt]
    simpa [transForbidBlockProgParam] using
      trans_forbid3_block_writer_param M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg
        T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable

def transLeafProgParam
    (nS mS nC mC wReg kbReg a1Reg a2Reg lenk len1 len2 : ℕ) : Program :=
  .ifNZ (.eq (transKindEParam kbReg lenk mC) (.const 0))
    (transHaltBlockProgParam nS mS wReg)
    (.ifNZ (.eq (transKindEParam kbReg lenk mC) (.const 1))
      (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
        (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
        (transForbidBlockProgParam nS mS wReg))
      (.ifNZ (.lt (transArg1EParam a1Reg len1 mC) (.const nC))
        (.ifNZ (moveOkEParam wReg (ctlCell lvJ1) (transArg2EParam a2Reg len2 mC))
          (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg len1 len2)
          (transForbidBlockProgParam nS mS wReg))
        (transForbidBlockProgParam nS mS wReg)))

lemma trans_leaf_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter
      (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
        colk.length col1.length col2.length)
      M Jmax wpJ
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
        (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
        (col2.getD (qi * mC + ai) 0)) := by
  unfold transLeafProgParam
  refine clauseWriter_ifNZ _ _ _ M Jmax wpJ _ _
    (colk.getD (qi * mC + ai) 0 = 0) ?_ ?_ ?_
  · intro τ hF h0
    have hval := trans_kind_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
      kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
    simp only [Expr.eval, hval]
    by_cases h : colk.getD (qi * mC + ai) 0 = 0 <;> simp
  · intro hk0
    have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
        (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
        (col2.getD (qi * mC + ai) 0)
        = [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).state (t + 1) qi),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)
            ((denseLayout nS W mS).cell (t + 1) p ai)] := by
      unfold natTransClausesTriple
      rw [ite_eq_left hk0]
    rw [heq]
    simpa [transHaltBlockProgParam] using
      trans_accept_halt_writer_param M Jmax nS W mS wReg tReg kbReg a1Reg a2Reg T
        kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
  · intro hkn0
    refine clauseWriter_ifNZ _ _ _ M Jmax wpJ _ _
      (colk.getD (qi * mC + ai) 0 = 1) ?_ ?_ ?_
    · intro τ hF h0
      have hval := trans_kind_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
      simp only [Expr.eval, hval]
      by_cases h : colk.getD (qi * mC + ai) 0 = 1 <;> simp
    · intro hk1
      have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)
          = natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
              (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) := by
        rw [hk1]
      rw [heq]
      exact trans_leaf_write_branch_writer_param M Jmax nS W mS nC mC wReg tReg
        kbReg a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2
        hplace htable
    · intro hkn1
      have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)
          = natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 2
              (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) :=
        natTransClausesTriple_of_ge2 (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0) hkn0 hkn1
      rw [heq]
      exact trans_leaf_move_branch_writer_param M Jmax nS W mS nC mC wReg tReg
        kbReg a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2
        hplace htable

lemma trans_ai_loop_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p qi : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
            colk.length col1.length col2.length)
          (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins3 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi) kindBase colk arg1Base col1 arg2Base col2)
      ((List.range mC).flatMap fun ai =>
        natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins3_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi lvJ3 hplace
    (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
    (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega)
  refine clauseWriter_forN_words3 _ M Jmax wpJ lvJ3 _ _ (.const mC) mC
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega) (le_refl lvJ3) hpin hbk hb1 hb2 ?_
    (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ3 _ _
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega) (le_refl lvJ3) hpin hbk hb1 hb2
    (fun ai => trans_leaf_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
      a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2
      hplace htable)

lemma trans_qi_loop_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (loopProg lvJ2 (.const nC)
        (.seq (loopProg lvJ3 (.const mC)
            (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
                colk.length col1.length col2.length)
              (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins2 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p) kindBase colk arg1Base col1 arg2Base col2)
      ((List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins2_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p lvJ2 hplace
    (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
    (by unfold lvJ1 lvJ2; omega)
  refine clauseWriter_forN_words3 _ M Jmax wpJ lvJ2 _ _ (.const nC) nC
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ2; omega)
    (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 wpJ; omega) (by unfold lvJ2 lvJ3; omega) hpin
    hbk hb1 hb2 ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ2 _ _
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ2; omega)
    (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 wpJ; omega) (by unfold lvJ2 lvJ3; omega) hpin
    hbk hb1 hb2
    (fun qi => trans_ai_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
      a1Reg a2Reg T kindBase arg1Base arg2Base t p qi colk col1 col2 hplace htable)

lemma trans_p_loop_writer_param
    (M Jmax nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length) :
    ClauseWriter (loopProg lvJ1 (ctlCell wReg)
        (.seq (loopProg lvJ2 (.const nC)
            (.seq (loopProg lvJ3 (.const mC)
                (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
                    colk.length col1.length col2.length)
                  (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ
      (TransFrozen M
        (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
        kindBase colk arg1Base col1 arg2Base col2)
      ((List.range W).flatMap fun p =>
        (List.range nC).flatMap fun qi =>
          (List.range mC).flatMap fun ai =>
            natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0)) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins1_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t lvJ1 hplace
    (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega)
  refine clauseWriter_forN_words3 _ M Jmax wpJ lvJ1 _ _ (ctlCell wReg) W
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ1; omega)
    (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega) hpin
    hbk hb1 hb2 ?_ ?_
  · exact clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ1 _ _
      kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega) hpin
      hbk hb1 hb2
      (fun p => trans_qi_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p colk col1 col2 hplace htable)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [transParamPins1, transParamPins0]) hF.1 h0

def transFamilyProgParam (nS mS nC mC : ℕ) (d : TableauDescriptor)
    (wReg tReg kbReg a1Reg a2Reg : ℕ) : Program :=
  loopProg lvJ0 (ctlCell tReg)
    (.seq (loopProg lvJ1 (ctlCell wReg)
      (.seq (loopProg lvJ2 (.const nC)
        (.seq (loopProg lvJ3 (.const mC)
          (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
              (d.table.map transKind).length (d.table.map transArg1).length
              (d.table.map transArg2).length)
            (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma transFamilyProgParam_writer_param
    (M Jmax nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length) :
    ClauseWriter
      (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg)
      M Jmax wpJ
      (TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base (d.table.map transKind) (d.table.map transArg1)
        (d.table.map transArg2))
      (transClausesTripleFamily (denseLayout nS W mS) nC W mC T
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) := by
  unfold transFamilyProgParam transClausesTripleFamily
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base (d.table.map transKind).length
    (d.table.map transArg1).length (d.table.map transArg2).length hplace htable
  have hpin := trans_param_pins0_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base lvJ0 hplace (by unfold lvJ0 ctlJmax; omega)
  refine clauseWriter_forN_words3 _ M Jmax wpJ lvJ0 _ _ (ctlCell tReg) T
    kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
    arg2Base (d.table.map transArg2) (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega) hpin
    hbk hb1 hb2 ?_ ?_
  · exact clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ0 _ _
      kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega) hpin
      hbk hb1 hb2
      (fun t => trans_p_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2) hplace htable)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ tReg T τ
      (by simp [transParamPins0]) hF.1 h0

lemma transFamilyProgParam_writer_param_desc
    (M Jmax W T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length) :
    ClauseWriter
      (transFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
        d.numStates d.numLetters d wReg tReg kbReg a1Reg a2Reg)
      M Jmax wpJ
      (TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base (d.table.map transKind) (d.table.map transArg1)
        (d.table.map transArg2))
      (descTransClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T) := by
  simpa only [trans_clauses_triple_family_eq_desc] using
    transFamilyProgParam_writer_param M Jmax (d.numStates + 1) W (d.numLetters + 1)
      d.numStates d.numLetters T d kindBase arg1Base arg2Base wReg tReg kbReg
      a1Reg a2Reg hplace htable

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq
public import NPComplete.CookLevin.Tableau.TableauRamLoops

/-!
The persistence family is the reduction's deepest nest that reads nothing but
arithmetic — no symbol table, no run-time clause width — so it is where the
combinators are first driven all the way from a family definition down to a
`ClauseWriter`.  Its one obstacle is the guard `if pHead = pCell then [] else ...`:
a `forN` writes the same number of clauses at every index, so an iteration that
sometimes emits nothing cannot be a loop body.  `persist_range_split` removes the
excluded index from the iteration space instead, leaving two unguarded loops.

The variable numbering is where the split shows up in the program: the second
loop's cell index is `pHead + 1 + j`, so the expression for it adds the pinned
head counter to the level's own counter rather than reading one cell.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## Map to `flatMap`

Families state their innermost level as a `map`; a loop writes a `flatMap` of
singletons.  The two agree, which is what lets a family definition be matched
against a loop's clause list without restating the family. -/

/-! ## Variable expressions

The three numbers a persistence clause needs, as expressions over the control
block.  The letter index is the innermost counter; the cell index is either a
counter (first loop) or the head counter plus one plus a counter (second loop),
which is exactly the shift `persist_range_split` introduces. -/

/-- `head t pHead`, over the time and head counters. -/
def persistHeadE (n W m : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- `cell t pCell a` in the first loop, where `pCell` is the level-2 counter and
`a` the level-3 counter. -/
def persistCellE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ2) (ctlCell lvJ3)

/-- `cell (t+1) pCell a`, the same cell one row down. -/
def persistCellNextE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ2) (ctlCell lvJ3)

/-- `cell t pCell a` in the second loop, where `pCell` is `pHead + 1 + j`. -/
def persistCellShiftE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2)) (ctlCell lvJ3)

/-- `cell (t+1) pCell a` in the second loop. -/
def persistCellShiftNextE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.add (ctlCell lvJ0) (.const 1))
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2)) (ctlCell lvJ3)

/-! ## Discharging the two obligations

Each expression owes a frame condition and a value.  Both follow from the two
`ctlCell` lemmas: rewrite the dense-expression evaluation, replace each
`ctlCell` read, and close by `simp`. -/

lemma persistHeadE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistHeadE n W m).eval σ' = (persistHeadE n W m).eval σ := by
  unfold persistHeadE
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)

lemma persistCellE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellE n W m).eval σ' = (persistCellE n W m).eval σ := by
  unfold persistCellE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

lemma persistCellNextE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellNextE n W m).eval σ' = (persistCellNextE n W m).eval σ := by
  unfold persistCellNextE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (expr_add_one_eval_congr _ σ σ'
      (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

lemma persistCellShiftE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellShiftE n W m).eval σ' = (persistCellShiftE n W m).eval σ := by
  unfold persistCellShiftE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
      (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

lemma persistCellShiftNextE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellShiftNextE n W m).eval σ' = (persistCellShiftNextE n W m).eval σ := by
  unfold persistCellShiftNextE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (expr_add_one_eval_congr _ σ σ'
      (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree))
    (expr_add_one_add_eval_congr _ _ σ σ'
      (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
      (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

/-! ### Values at the innermost level

At depth 3 the outer three counters are pinned and the level's own counter holds
the letter index, so each expression is the dense layout's own number. -/

lemma persistHeadE_value (M n W m t pHead pCell : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t pHead pCell) τ) (h0 : τ 0 = M) :
    (persistHeadE n W m).eval τ = (denseLayout n W m).head t pHead := by
  unfold persistHeadE
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t pHead rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [ctlPins3]) hF h0)

lemma persistCellE_value (M n W m t pHead pCell : ℕ) (τ : Store) (a : ℕ)
    (hF : PinsHold M (ctlPins3 t pHead pCell) τ) (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellE n W m).eval τ = (denseLayout n W m).cell t pCell a := by
  unfold persistCellE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t pCell a rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ2 pCell τ (by simp [ctlPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persistCellNextE_value (M n W m t pHead pCell : ℕ) (τ : Store) (a : ℕ)
    (hF : PinsHold M (ctlPins3 t pHead pCell) τ) (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellNextE n W m).eval τ = (denseLayout n W m).cell (t + 1) pCell a := by
  unfold persistCellNextE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m (t + 1) pCell a rfl rfl rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0))
    (ctlCell_eval_of_pin M _ lvJ2 pCell τ (by simp [ctlPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persistCellShiftE_value (M n W m t pHead j : ℕ) (τ : Store) (a : ℕ)
    (hF : PinsHold M (ctlPins3 t pHead j) τ) (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellShiftE n W m).eval τ
      = (denseLayout n W m).cell t (pHead + 1 + j) a := by
  unfold persistCellShiftE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t (pHead + 1 + j) a rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (expr_add_one_add_eval _ _ τ pHead j
      (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [ctlPins3]) hF h0)
      (ctlCell_eval_of_pin M _ lvJ2 j τ (by simp [ctlPins3]) hF h0))
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persistCellShiftNextE_value (M n W m t pHead j : ℕ) (τ : Store) (a : ℕ)
    (hF : PinsHold M (ctlPins3 t pHead j) τ) (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellShiftNextE n W m).eval τ
      = (denseLayout n W m).cell (t + 1) (pHead + 1 + j) a := by
  unfold persistCellShiftNextE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m (t + 1) (pHead + 1 + j) a rfl rfl rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0))
    (expr_add_one_add_eval _ _ τ pHead j
      (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [ctlPins3]) hF h0)
      (ctlCell_eval_of_pin M _ lvJ2 j τ (by simp [ctlPins3]) hF h0))
    (by rw [ctlCell_eval, h0]; exact ha)

/-! ## The innermost two levels

Assembling the letter level and closing it into a writer is the pattern every
remaining level of every family repeats, so these two are stated in full: the
leaf, then the loop that ends it.  The outer levels differ only in which counter
they own and which clause list their iteration produces. -/

/-- The letter level of the first persistence loop: one `imply2` per letter. -/
lemma persist_leaf_body (M n W m t pHead pCell : ℕ) :
    ClauseLoopBody (leafProg wpJ lvJ3
        (imply2Lits (persistHeadE n W m) (persistCellE n W m) (persistCellNextE n W m)))
      M ctlJmax wpJ lvJ3 (PinsHold M (ctlPins3 t pHead pCell))
      (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)]) := by
  refine clauseLoopBody_imply2 M ctlJmax wpJ lvJ3
    (persistHeadE n W m) (persistCellE n W m) (persistCellNextE n W m)
    (ctlPins3 t pHead pCell) _ _ _
    (by unfold wpJ; omega) (by unfold wpJ ctlJmax; omega)
    (by unfold lvJ3; omega) (by unfold lvJ3 ctlJmax; omega)
    (by unfold lvJ3 wpJ; omega)
    (ctlPins3_ok t pHead pCell lvJ3 (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (fun σ σ' hσ hσ' h => persistHeadE_frame M n W m σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persistCellE_frame M n W m σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persistCellNextE_frame M n W m σ σ' hσ hσ' h)
    (fun τ _ hF h0 _ => persistHeadE_value M n W m t pHead pCell τ hF h0)
    (fun τ a hF h0 ha => persistCellE_value M n W m t pHead pCell τ a hF h0 ha)
    (fun τ a hF h0 ha => persistCellNextE_value M n W m t pHead pCell τ a hF h0 ha)

/-! ## The second loop's letter level

`persist_range_split` shifts the second half of the `pCell` range by
`pHead + 1`, so this level is the mirror of `persist_leaf_body`,
reading the shifted variable expressions instead. -/

/-- The letter level of the second persistence loop: one `imply2` per letter,
at cell `pHead + 1 + j`. -/
lemma persist_leaf_body_shift (M n W m t pHead j : ℕ) :
    ClauseLoopBody (leafProg wpJ lvJ3
        (imply2Lits (persistHeadE n W m) (persistCellShiftE n W m) (persistCellShiftNextE n W m)))
      M ctlJmax wpJ lvJ3 (PinsHold M (ctlPins3 t pHead j))
      (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t (pHead + 1 + j) a)
        ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseLoopBody_imply2 M ctlJmax wpJ lvJ3
    (persistHeadE n W m) (persistCellShiftE n W m) (persistCellShiftNextE n W m)
    (ctlPins3 t pHead j) _ _ _
    (by unfold wpJ; omega) (by unfold wpJ ctlJmax; omega)
    (by unfold lvJ3; omega) (by unfold lvJ3 ctlJmax; omega)
    (by unfold lvJ3 wpJ; omega)
    (ctlPins3_ok t pHead j lvJ3 (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (fun σ σ' hσ hσ' h => persistHeadE_frame M n W m σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persistCellShiftE_frame M n W m σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persistCellShiftNextE_frame M n W m σ σ' hσ hσ' h)
    (fun τ _ hF h0 _ => persistHeadE_value M n W m t pHead j τ hF h0)
    (fun τ a hF h0 ha => persistCellShiftE_value M n W m t pHead j τ a hF h0 ha)
    (fun τ a hF h0 ha => persistCellShiftNextE_value M n W m t pHead j τ a hF h0 ha)

/-! ## Layout-stride/count-separated writers -/

/-- The first letter loop with a count independent of the dense-layout stride. -/
lemma persist_letter_writer_gen (M nS W mS mC t pHead pCell : ℕ) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
            (persistCellNextE nS W mS))))
      M ctlJmax wpJ (PinsHold M (ctlPins3 t pHead pCell))
      ((List.range mC).flatMap fun a =>
        [imply2 ((denseLayout nS W mS).head t pHead)
          ((denseLayout nS W mS).cell t pCell a)
          ((denseLayout nS W mS).cell (t + 1) pCell a)]) :=
  clauseWriter_forN _ M ctlJmax wpJ lvJ3 (ctlPins3 t pHead pCell) _ (.const mC) mC
    (by unfold lvJ3; omega) (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ3 wpJ; omega)
    (ctlPins3_ok t pHead pCell lvJ3 (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (persist_leaf_body M nS W mS t pHead pCell) (fun _ _ _ _ => rfl)

/-- The shifted letter loop with a count independent of the dense-layout stride. -/
lemma persist_letter_writer_shift_gen (M nS W mS mC t pHead j : ℕ) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
            (persistCellShiftNextE nS W mS))))
      M ctlJmax wpJ (PinsHold M (ctlPins3 t pHead j))
      ((List.range mC).flatMap fun a =>
        [imply2 ((denseLayout nS W mS).head t pHead)
          ((denseLayout nS W mS).cell t (pHead + 1 + j) a)
          ((denseLayout nS W mS).cell (t + 1) (pHead + 1 + j) a)]) :=
  clauseWriter_forN _ M ctlJmax wpJ lvJ3 (ctlPins3 t pHead j) _ (.const mC) mC
    (by unfold lvJ3; omega) (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ3 wpJ; omega)
    (ctlPins3_ok t pHead j lvJ3 (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (persist_leaf_body_shift M nS W mS t pHead j) (fun _ _ _ _ => rfl)

/-- The first cell-position loop with an independent letter count. -/
lemma persist_pCell_writer_gen (M nS W mS mC t pHead : ℕ) :
    ClauseWriter (loopProg lvJ2 (ctlCell lvJ1)
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                (persistCellNextE nS W mS))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M ctlJmax wpJ (PinsHold M (ctlPins2 t pHead))
      ((List.range pHead).flatMap fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout nS W mS).head t pHead)
            ((denseLayout nS W mS).cell t pCell a)
            ((denseLayout nS W mS).cell (t + 1) pCell a)]) := by
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ2 (ctlPins2 t pHead) _ (ctlCell lvJ1) pHead
    (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ2 wpJ; omega)
    (ctlPins2_ok t pHead lvJ2 (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
    ?_ ?_
  · exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ2 (ctlPins2 t pHead) _
      (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ2 wpJ; omega)
      (ctlPins2_ok t pHead lvJ2 (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
      (fun i => persist_letter_writer_gen M nS W mS mC t pHead i)
  · intro τ h0 hF hz
    rw [ctlCell_eval, h0]
    exact hF (lvJ1, pHead) (by simp [ctlPins2])

/-- The shifted cell-position loop with an independent letter count. -/
lemma persist_pCell_writer_shift_gen (M nS W mS mC t pHead : ℕ) :
    ClauseWriter (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                (persistCellShiftNextE nS W mS))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M ctlJmax wpJ (PinsHold M (ctlPins2 t pHead))
      ((List.range (W - pHead - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout nS W mS).head t pHead)
            ((denseLayout nS W mS).cell t (pHead + 1 + j) a)
            ((denseLayout nS W mS).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ2 (ctlPins2 t pHead) _
    (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1)) (W - pHead - 1)
    (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ2 wpJ; omega)
    (ctlPins2_ok t pHead lvJ2 (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
    ?_ ?_
  · exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ2 (ctlPins2 t pHead) _
      (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ2 wpJ; omega)
      (ctlPins2_ok t pHead lvJ2 (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
      (fun j => persist_letter_writer_shift_gen M nS W mS mC t pHead j)
  · intro τ h0 hF hz
    simp only [Expr.eval]
    rw [ctlCell_eval, h0]
    rw [hF (lvJ1, pHead) (by simp [ctlPins2])]

/-- The two cell-position loops with an independent letter count. -/
lemma persist_pHead_fixed_writer_raw_gen (M nS W mS mC t pHead : ℕ) :
    ClauseWriter (.seq
        (loopProg lvJ2 (ctlCell lvJ1)
          (.seq (loopProg lvJ3 (.const mC)
              (leafProg wpJ lvJ3
                (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                  (persistCellNextE nS W mS))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
          (.seq (loopProg lvJ3 (.const mC)
              (leafProg wpJ lvJ3
                (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                  (persistCellShiftNextE nS W mS))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
      M ctlJmax wpJ (PinsHold M (ctlPins2 t pHead))
      ((List.range pHead).flatMap (fun pCell =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout nS W mS).head t pHead)
              ((denseLayout nS W mS).cell t pCell a)
              ((denseLayout nS W mS).cell (t + 1) pCell a)])
        ++ (List.range (W - pHead - 1)).flatMap fun j =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout nS W mS).head t pHead)
              ((denseLayout nS W mS).cell t (pHead + 1 + j) a)
              ((denseLayout nS W mS).cell (t + 1) (pHead + 1 + j) a)]) :=
  clauseWriter_seq _ _ M ctlJmax wpJ (PinsHold M (ctlPins2 t pHead)) _ _
    (persist_pCell_writer_gen M nS W mS mC t pHead)
    (persist_pCell_writer_shift_gen M nS W mS mC t pHead)

/-- The head-position loop with an independent letter count. -/
lemma persist_pHead_loop_writer_raw_gen (M nS W mS mC t : ℕ) :
    ClauseWriter (loopProg lvJ1 (.const W)
        (.seq (.seq
          (loopProg lvJ2 (ctlCell lvJ1)
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                    (persistCellNextE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                    (persistCellShiftNextE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      ((List.range W).flatMap fun pHead =>
        (List.range pHead).flatMap (fun pCell =>
            (List.range mC).flatMap fun a =>
              [imply2 ((denseLayout nS W mS).head t pHead)
                ((denseLayout nS W mS).cell t pCell a)
                ((denseLayout nS W mS).cell (t + 1) pCell a)])
          ++ (List.range (W - pHead - 1)).flatMap fun j =>
            (List.range mC).flatMap fun a =>
              [imply2 ((denseLayout nS W mS).head t pHead)
                ((denseLayout nS W mS).cell t (pHead + 1 + j) a)
                ((denseLayout nS W mS).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ1 (ctlPins1 t) _ (.const W) W
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ1 wpJ; omega)
    (ctlPins1_ok t lvJ1 (by unfold lvJ0 lvJ1; omega))
    ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ1 (ctlPins1 t) _
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ1 wpJ; omega)
    (ctlPins1_ok t lvJ1 (by unfold lvJ0 lvJ1; omega))
    (fun pHead => persist_pHead_fixed_writer_raw_gen M nS W mS mC t pHead)

/-- The range split with an independent dense-layout stride and letter count. -/
lemma persist_family_eq_split_gen (nS W mS mC t : ℕ) :
    (List.range W).flatMap (fun pHead =>
      (List.range pHead).flatMap (fun pCell =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout nS W mS).head t pHead)
              ((denseLayout nS W mS).cell t pCell a)
              ((denseLayout nS W mS).cell (t + 1) pCell a)])
        ++ (List.range (W - pHead - 1)).flatMap fun j =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout nS W mS).head t pHead)
              ((denseLayout nS W mS).cell t (pHead + 1 + j) a)
              ((denseLayout nS W mS).cell (t + 1) (pHead + 1 + j) a)])
      = (List.range W).flatMap fun pHead =>
          (List.range W).flatMap fun pCell =>
            if pHead = pCell then []
            else (List.range mC).map fun a =>
              imply2 ((denseLayout nS W mS).head t pHead)
                ((denseLayout nS W mS).cell t pCell a)
                ((denseLayout nS W mS).cell (t + 1) pCell a) := by
  apply List.flatMap_congr
  intro pHead hpHead
  have hp : pHead < W := List.mem_range.mp hpHead
  rw [persist_range_split W pHead hp]
  congr 1
  · apply List.flatMap_congr
    intro pCell _
    exact (map_eq_flatMap_singleton _ _).symm
  · apply List.flatMap_congr
    intro j _
    exact (map_eq_flatMap_singleton _ _).symm

/-- One persistence row with an independent letter count. -/
lemma persist_t_fixed_writer_gen (M nS W mS mC t : ℕ) :
    ClauseWriter (loopProg lvJ1 (.const W)
        (.seq (.seq
          (loopProg lvJ2 (ctlCell lvJ1)
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                    (persistCellNextE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                    (persistCellShiftNextE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      ((List.range W).flatMap fun pHead =>
          (List.range W).flatMap fun pCell =>
            if pHead = pCell then []
            else (List.range mC).map fun a =>
              imply2 ((denseLayout nS W mS).head t pHead)
                ((denseLayout nS W mS).cell t pCell a)
                ((denseLayout nS W mS).cell (t + 1) pCell a)) := by
  rw [← persist_family_eq_split_gen]
  exact persist_pHead_loop_writer_raw_gen M nS W mS mC t

/-- The persistence program with an independent layout stride and letter count. -/
def persistFamilyProgGen (nS W mS mC T : ℕ) : Program :=
  loopProg lvJ0 (.const T)
    (.seq (loopProg lvJ1 (.const W)
      (.seq (.seq
        (loopProg lvJ2 (ctlCell lvJ1)
          (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                (persistCellNextE nS W mS))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
          (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                (persistCellShiftNextE nS W mS))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

/-- The persist family's program, as in `persistFamilyProg_writer`. -/
def persistFamilyProg (n W m T : ℕ) : Program :=
  persistFamilyProgGen n W m m T

/-- The full persistence family with independent layout strides and letter count. -/
lemma persistFamilyProgGen_writer_gen (M nS W mS mC T : ℕ) :
    ClauseWriter (loopProg lvJ0 (.const T)
        (.seq (loopProg lvJ1 (.const W)
          (.seq (.seq
            (loopProg lvJ2 (ctlCell lvJ1)
              (.seq (loopProg lvJ3 (.const mC)
                  (leafProg wpJ lvJ3
                    (imply2Lits (persistHeadE nS W mS) (persistCellE nS W mS)
                      (persistCellNextE nS W mS))))
                (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
            (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
              (.seq (loopProg lvJ3 (.const mC)
                  (leafProg wpJ lvJ3
                    (imply2Lits (persistHeadE nS W mS) (persistCellShiftE nS W mS)
                      (persistCellShiftNextE nS W mS))))
                (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M ctlJmax wpJ (PinsHold M ctlPins0)
      (execPersistClausesAt (denseLayout nS W mS) (List.range mC) W T) := by
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ0 ctlPins0 _ (.const T) T
    (by unfold lvJ0; omega) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega)
    (ctlPins0_ok lvJ0)
    ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ0 ctlPins0 _
    (by unfold lvJ0; omega) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega)
    (ctlPins0_ok lvJ0)
    (fun t => persist_t_fixed_writer_gen M nS W mS mC t)

/-! ## The `t` loop, closing the whole family -/

/-- The full persist family, as a `ClauseWriter`.  Its clause list is
`execPersistClausesAt (denseLayout n W m) (List.range m) W T` by `rfl`, so the
right-hand side is exactly the family's own definition, with `A` specialized
to `List.range m` as `descPersistClauses` does. -/
lemma persistFamilyProg_writer (M n W m T : ℕ) :
    ClauseWriter (loopProg lvJ0 (.const T)
        (.seq (loopProg lvJ1 (.const W)
          (.seq (.seq
            (loopProg lvJ2 (ctlCell lvJ1)
              (.seq (loopProg lvJ3 (.const m)
                  (leafProg wpJ lvJ3
                    (imply2Lits (persistHeadE n W m) (persistCellE n W m)
                      (persistCellNextE n W m))))
                (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
            (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
              (.seq (loopProg lvJ3 (.const m)
                  (leafProg wpJ lvJ3
                    (imply2Lits (persistHeadE n W m) (persistCellShiftE n W m)
                      (persistCellShiftNextE n W m))))
                (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M ctlJmax wpJ (PinsHold M ctlPins0)
      (execPersistClausesAt (denseLayout n W m) (List.range m) W T) :=
  persistFamilyProgGen_writer_gen M n W m m T

/-! ## Run-time width and time parameters -/

/-- Placement requirements for the run-time width and time cells. -/
structure PersistParamPlacement (Jmax wReg tReg : ℕ) : Prop where
  ctl_le : ctlJmax ≤ Jmax
  w_min : 15 ≤ wReg
  w_le : wReg ≤ Jmax
  t_min : 15 ≤ tReg
  t_le : tReg ≤ Jmax
  regs_ne : wReg ≠ tReg

/-- Cell storing the persist family's run-time width parameter. -/
def persistWReg : ℕ := 15

/-- Cell storing the persist family's time parameter. -/
def persistTReg : ℕ := 16

/-- The control extent covering the persist family's two parameter cells. -/
def persistParamJmax : ℕ := 16

lemma persist_param_fixed_placement :
    PersistParamPlacement persistParamJmax persistWReg persistTReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [persistParamJmax, persistWReg, persistTReg, ctlJmax]

lemma persist_param_placement_satisfiable :
    ∃ Jmax wReg tReg, PersistParamPlacement Jmax wReg tReg :=
  ⟨persistParamJmax, persistWReg, persistTReg, persist_param_fixed_placement⟩

/-- Run-time parameters at the outermost persistence level. -/
def persistParamPins0 (wReg tReg W T : ℕ) : List (ℕ × ℕ) :=
  [(wReg, W), (tReg, T)]

/-- Run-time parameters together with the time counter. -/
def persistParamPins1 (wReg tReg W T t : ℕ) : List (ℕ × ℕ) :=
  (lvJ0, t) :: persistParamPins0 wReg tReg W T

/-- Run-time parameters together with the time and head counters. -/
def persistParamPins2 (wReg tReg W T t pHead : ℕ) : List (ℕ × ℕ) :=
  (lvJ1, pHead) :: persistParamPins1 wReg tReg W T t

/-- Run-time parameters together with the three enclosing counters. -/
def persistParamPins3 (wReg tReg W T t pHead pCell : ℕ) : List (ℕ × ℕ) :=
  (lvJ2, pCell) :: persistParamPins2 wReg tReg W T t pHead

lemma persist_param_pins0_ok (Jmax wReg tReg W T iJ : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax) :
    ∀ p ∈ persistParamPins0 wReg tReg W T,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  simp only [persistParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by have := hplace.w_min; omega, hplace.w_le,
      by have hw := hplace.w_min; unfold ctlJmax at hiJctl; omega,
      by have := hplace.w_min; unfold wpJ; omega⟩
  · exact ⟨by have := hplace.t_min; omega, hplace.t_le,
      by have ht := hplace.t_min; unfold ctlJmax at hiJctl; omega,
      by have := hplace.t_min; unfold wpJ; omega⟩

lemma persist_param_pins1_ok (Jmax wReg tReg W T t iJ : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) :
    ∀ p ∈ persistParamPins1 wReg tReg W T t,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by unfold lvJ0; omega,
      Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le, h0,
      by unfold lvJ0 wpJ; omega⟩
  · exact persist_param_pins0_ok Jmax wReg tReg W T iJ hplace hiJctl p hp

lemma persist_param_pins2_ok (Jmax wReg tReg W T t pHead iJ : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) :
    ∀ p ∈ persistParamPins2 wReg tReg W T t pHead,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by unfold lvJ1; omega,
      Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le, h1,
      by unfold lvJ1 wpJ; omega⟩
  · exact persist_param_pins1_ok Jmax wReg tReg W T t iJ hplace hiJctl h0 p hp

lemma persist_param_pins3_ok (Jmax wReg tReg W T t pHead pCell iJ : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) (h2 : lvJ2 ≠ iJ) :
    ∀ p ∈ persistParamPins3 wReg tReg W T t pHead pCell,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by unfold lvJ2; omega,
      Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le, h2,
      by unfold lvJ2 wpJ; omega⟩
  · exact persist_param_pins2_ok Jmax wReg tReg W T t pHead iJ hplace hiJctl h0 h1 p hp

/-- `head t pHead` with the dense-layout width read from a parameter cell. -/
def persistHeadEParam (n m wReg : ℕ) : Expr :=
  denseHeadE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- `cell t pCell a` with the dense-layout width read from a parameter cell. -/
def persistCellEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m)
    (ctlCell lvJ0) (ctlCell lvJ2) (ctlCell lvJ3)

/-- `cell (t+1) pCell a` with a run-time dense-layout width. -/
def persistCellNextEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ2) (ctlCell lvJ3)

/-- The shifted current-row cell expression with a run-time dense-layout width. -/
def persistCellShiftEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2)) (ctlCell lvJ3)

/-- The shifted next-row cell expression with a run-time dense-layout width. -/
def persistCellShiftNextEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (.add (ctlCell lvJ0) (.const 1))
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2)) (ctlCell lvJ3)

lemma persist_param_ctl_frame (M Jmax wReg tReg j : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (hj : j = lvJ0 ∨ j = lvJ1 ∨ j = lvJ2 ∨ j = lvJ3)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  exact ctlCell_frame_lv M j hj σ σ' hσ hσ'
    (fun k hk1 hk2 hkw => hagree k hk1 (Nat.le_trans hk2 hplace.ctl_le) hkw)

lemma persist_param_width_frame (M Jmax wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell wReg).eval σ' = (ctlCell wReg).eval σ := by
  exact ctlCell_frame M Jmax wReg (by have := hplace.w_min; omega) hplace.w_le
    (by have := hplace.w_min; unfold wpJ; omega)
    σ σ' hσ hσ' hagree

lemma persist_head_e_param_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistHeadEParam n m wReg).eval σ' = (persistHeadEParam n m wReg).eval σ := by
  unfold persistHeadEParam
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl
    (persist_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (persist_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (persist_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)

lemma persist_cell_e_param_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellEParam n m wReg).eval σ' = (persistCellEParam n m wReg).eval σ := by
  unfold persistCellEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (persist_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (persist_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (persist_param_ctl_frame M Jmax wReg tReg lvJ2 hplace (Or.inr (Or.inr (Or.inl rfl)))
      σ σ' hσ hσ' hagree)
    (persist_param_ctl_frame M Jmax wReg tReg lvJ3 hplace (Or.inr (Or.inr (Or.inr rfl)))
      σ σ' hσ hσ' hagree)

lemma persist_cell_next_e_param_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellNextEParam n m wReg).eval σ' = (persistCellNextEParam n m wReg).eval σ := by
  unfold persistCellNextEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (persist_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (expr_add_one_eval_congr _ σ σ'
      (persist_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
        σ σ' hσ hσ' hagree))
    (persist_param_ctl_frame M Jmax wReg tReg lvJ2 hplace (Or.inr (Or.inr (Or.inl rfl)))
      σ σ' hσ hσ' hagree)
    (persist_param_ctl_frame M Jmax wReg tReg lvJ3 hplace (Or.inr (Or.inr (Or.inr rfl)))
      σ σ' hσ hσ' hagree)

lemma persist_cell_shift_e_param_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellShiftEParam n m wReg).eval σ' = (persistCellShiftEParam n m wReg).eval σ := by
  unfold persistCellShiftEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (persist_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (persist_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (persist_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
        σ σ' hσ hσ' hagree)
      (persist_param_ctl_frame M Jmax wReg tReg lvJ2 hplace (Or.inr (Or.inr (Or.inl rfl)))
        σ σ' hσ hσ' hagree))
    (persist_param_ctl_frame M Jmax wReg tReg lvJ3 hplace (Or.inr (Or.inr (Or.inr rfl)))
      σ σ' hσ hσ' hagree)

lemma persist_cell_shift_next_e_param_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (persistCellShiftNextEParam n m wReg).eval σ'
      = (persistCellShiftNextEParam n m wReg).eval σ := by
  unfold persistCellShiftNextEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (persist_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (expr_add_one_eval_congr _ σ σ'
      (persist_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
        σ σ' hσ hσ' hagree))
    (expr_add_one_add_eval_congr _ _ σ σ'
      (persist_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
        σ σ' hσ hσ' hagree)
      (persist_param_ctl_frame M Jmax wReg tReg lvJ2 hplace (Or.inr (Or.inr (Or.inl rfl)))
        σ σ' hσ hσ' hagree))
    (persist_param_ctl_frame M Jmax wReg tReg lvJ3 hplace (Or.inr (Or.inr (Or.inr rfl)))
      σ σ' hσ hσ' hagree)

lemma persist_head_e_param_value (M n W m T wReg tReg t pHead pCell : ℕ) (τ : Store)
    (hF : PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell) τ)
    (h0 : τ 0 = M) :
    (persistHeadEParam n m wReg).eval τ = (denseLayout n W m).head t pHead := by
  unfold persistHeadEParam
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t pHead rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1, persistParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [persistParamPins3, persistParamPins2]) hF h0)

lemma persist_cell_e_param_value (M n W m T wReg tReg t pHead pCell : ℕ) (τ : Store)
    (a : ℕ) (hF : PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell) τ)
    (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellEParam n m wReg).eval τ = (denseLayout n W m).cell t pCell a := by
  unfold persistCellEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t pCell a rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1, persistParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ2 pCell τ (by simp [persistParamPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persist_cell_next_e_param_value (M n W m T wReg tReg t pHead pCell : ℕ)
    (τ : Store) (a : ℕ)
    (hF : PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell) τ)
    (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellNextEParam n m wReg).eval τ = (denseLayout n W m).cell (t + 1) pCell a := by
  unfold persistCellNextEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m (t + 1) pCell a rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1, persistParamPins0]) hF h0) rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [persistParamPins3, persistParamPins2,
        persistParamPins1]) hF h0))
    (ctlCell_eval_of_pin M _ lvJ2 pCell τ (by simp [persistParamPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persist_cell_shift_e_param_value (M n W m T wReg tReg t pHead j : ℕ)
    (τ : Store) (a : ℕ)
    (hF : PinsHold M (persistParamPins3 wReg tReg W T t pHead j) τ)
    (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellShiftEParam n m wReg).eval τ
      = (denseLayout n W m).cell t (pHead + 1 + j) a := by
  unfold persistCellShiftEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t (pHead + 1 + j) a rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1, persistParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1]) hF h0)
    (expr_add_one_add_eval _ _ τ pHead j
      (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [persistParamPins3, persistParamPins2]) hF h0)
      (ctlCell_eval_of_pin M _ lvJ2 j τ (by simp [persistParamPins3]) hF h0))
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persist_cell_shift_next_e_param_value (M n W m T wReg tReg t pHead j : ℕ)
    (τ : Store) (a : ℕ)
    (hF : PinsHold M (persistParamPins3 wReg tReg W T t pHead j) τ)
    (h0 : τ 0 = M) (ha : τ (M + lvJ3) = a) :
    (persistCellShiftNextEParam n m wReg).eval τ
      = (denseLayout n W m).cell (t + 1) (pHead + 1 + j) a := by
  unfold persistCellShiftNextEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m (t + 1) (pHead + 1 + j) a rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins3, persistParamPins2,
      persistParamPins1, persistParamPins0]) hF h0) rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [persistParamPins3, persistParamPins2,
        persistParamPins1]) hF h0))
    (expr_add_one_add_eval _ _ τ pHead j
      (ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [persistParamPins3, persistParamPins2]) hF h0)
      (ctlCell_eval_of_pin M _ lvJ2 j τ (by simp [persistParamPins3]) hF h0))
    (by rw [ctlCell_eval, h0]; exact ha)

lemma persist_leaf_body_param (M Jmax n W m T wReg tReg t pHead pCell : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseLoopBody (leafProg wpJ lvJ3
        (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
          (persistCellNextEParam n m wReg)))
      M Jmax wpJ lvJ3
      (PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell))
      (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t pCell a)
        ((denseLayout n W m).cell (t + 1) pCell a)]) := by
  refine clauseLoopBody_imply2 M Jmax wpJ lvJ3
    (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
    (persistCellNextEParam n m wReg)
    (persistParamPins3 wReg tReg W T t pHead pCell) _ _ _ wpJ_pos
    (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega)
    (persist_param_pins3_ok Jmax wReg tReg W T t pHead pCell lvJ3 hplace
      (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (fun σ σ' hσ hσ' h => persist_head_e_param_frame M Jmax n m wReg tReg hplace
      σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persist_cell_e_param_frame M Jmax n m wReg tReg hplace
      σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persist_cell_next_e_param_frame M Jmax n m wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ _ hF h0 _ => persist_head_e_param_value M n W m T wReg tReg t pHead pCell
      τ hF h0)
    (fun τ a hF h0 ha => persist_cell_e_param_value M n W m T wReg tReg t pHead pCell
      τ a hF h0 ha)
    (fun τ a hF h0 ha => persist_cell_next_e_param_value M n W m T wReg tReg t pHead
      pCell τ a hF h0 ha)

lemma persist_letter_writer_param (M Jmax n W m mC T wReg tReg t pHead pCell : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
            (persistCellNextEParam n m wReg))))
      M Jmax wpJ (PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell))
      ((List.range mC).flatMap fun a =>
        [imply2 ((denseLayout n W m).head t pHead)
          ((denseLayout n W m).cell t pCell a)
          ((denseLayout n W m).cell (t + 1) pCell a)]) :=
  clauseWriter_forN _ M Jmax wpJ lvJ3
    (persistParamPins3 wReg tReg W T t pHead pCell) _ (.const mC) mC
    (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega)
    (persist_param_pins3_ok Jmax wReg tReg W T t pHead pCell lvJ3 hplace
      (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (persist_leaf_body_param M Jmax n W m T wReg tReg t pHead pCell hplace)
    (fun _ _ _ _ => rfl)

lemma persist_leaf_body_shift_param (M Jmax n W m T wReg tReg t pHead j : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseLoopBody (leafProg wpJ lvJ3
        (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
          (persistCellShiftNextEParam n m wReg)))
      M Jmax wpJ lvJ3 (PinsHold M (persistParamPins3 wReg tReg W T t pHead j))
      (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t (pHead + 1 + j) a)
        ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseLoopBody_imply2 M Jmax wpJ lvJ3
    (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
    (persistCellShiftNextEParam n m wReg)
    (persistParamPins3 wReg tReg W T t pHead j) _ _ _ wpJ_pos
    (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega)
    (persist_param_pins3_ok Jmax wReg tReg W T t pHead j lvJ3 hplace
      (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (fun σ σ' hσ hσ' h => persist_head_e_param_frame M Jmax n m wReg tReg hplace
      σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persist_cell_shift_e_param_frame M Jmax n m wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => persist_cell_shift_next_e_param_frame M Jmax n m wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ _ hF h0 _ => persist_head_e_param_value M n W m T wReg tReg t pHead j τ hF h0)
    (fun τ a hF h0 ha => persist_cell_shift_e_param_value M n W m T wReg tReg t pHead j
      τ a hF h0 ha)
    (fun τ a hF h0 ha => persist_cell_shift_next_e_param_value M n W m T wReg tReg t
      pHead j τ a hF h0 ha)

lemma persist_letter_writer_shift_param
    (M Jmax n W m mC T wReg tReg t pHead j : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
            (persistCellShiftNextEParam n m wReg))))
      M Jmax wpJ (PinsHold M (persistParamPins3 wReg tReg W T t pHead j))
      ((List.range mC).flatMap fun a =>
        [imply2 ((denseLayout n W m).head t pHead)
          ((denseLayout n W m).cell t (pHead + 1 + j) a)
          ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) :=
  clauseWriter_forN _ M Jmax wpJ lvJ3 (persistParamPins3 wReg tReg W T t pHead j) _
    (.const mC) mC (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3 wpJ; omega)
    (persist_param_pins3_ok Jmax wReg tReg W T t pHead j lvJ3 hplace
      (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega))
    (persist_leaf_body_shift_param M Jmax n W m T wReg tReg t pHead j hplace)
    (fun _ _ _ _ => rfl)

lemma persist_p_cell_writer_param (M Jmax n W m mC T wReg tReg t pHead : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ2 (ctlCell lvJ1)
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                (persistCellNextEParam n m wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ (PinsHold M (persistParamPins2 wReg tReg W T t pHead))
      ((List.range pHead).flatMap fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a)
            ((denseLayout n W m).cell (t + 1) pCell a)]) := by
  refine clauseWriter_forN _ M Jmax wpJ lvJ2
    (persistParamPins2 wReg tReg W T t pHead) _ (ctlCell lvJ1) pHead
    (by unfold lvJ2; omega)
    (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 wpJ; omega)
    (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
      (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
      (by unfold lvJ1 lvJ2; omega)) ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ2
      (persistParamPins2 wReg tReg W T t pHead) _ (by unfold lvJ2; omega)
      (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ2 wpJ; omega)
      (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
        (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
        (by unfold lvJ1 lvJ2; omega))
      (fun i => persist_letter_writer_param M Jmax n W m mC T wReg tReg t pHead i hplace)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ lvJ1 pHead τ
      (by simp [persistParamPins2]) hF h0

lemma persist_p_cell_writer_shift_param
    (M Jmax n W m mC T wReg tReg t pHead : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
                (persistCellShiftNextEParam n m wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ (PinsHold M (persistParamPins2 wReg tReg W T t pHead))
      ((List.range (W - pHead - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t (pHead + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseWriter_forN _ M Jmax wpJ lvJ2
    (persistParamPins2 wReg tReg W T t pHead) _
    (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1)) (W - pHead - 1)
    (by unfold lvJ2; omega)
    (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 wpJ; omega)
    (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
      (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
      (by unfold lvJ1 lvJ2; omega)) ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ2
      (persistParamPins2 wReg tReg W T t pHead) _ (by unfold lvJ2; omega)
      (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ2 wpJ; omega)
      (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
        (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
        (by unfold lvJ1 lvJ2; omega))
      (fun j => persist_letter_writer_shift_param M Jmax n W m mC T wReg tReg t pHead j
        hplace)
  · intro τ h0 hF _
    have eW : (ctlCell wReg).eval τ = W :=
      ctlCell_eval_of_pin M _ wReg W τ (by simp [persistParamPins2, persistParamPins1,
        persistParamPins0]) hF h0
    have e1 : (ctlCell lvJ1).eval τ = pHead :=
      ctlCell_eval_of_pin M _ lvJ1 pHead τ (by simp [persistParamPins2]) hF h0
    simp only [Expr.eval, eW, e1]

lemma persist_p_head_fixed_writer_raw_param
    (M Jmax n W m mC T wReg tReg t pHead : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (.seq
        (loopProg lvJ2 (ctlCell lvJ1)
          (.seq (loopProg lvJ3 (.const mC)
              (leafProg wpJ lvJ3
                (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                  (persistCellNextEParam n m wReg))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
          (.seq (loopProg lvJ3 (.const mC)
              (leafProg wpJ lvJ3
                (imply2Lits (persistHeadEParam n m wReg)
                  (persistCellShiftEParam n m wReg)
                  (persistCellShiftNextEParam n m wReg))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
      M Jmax wpJ (PinsHold M (persistParamPins2 wReg tReg W T t pHead))
      ((List.range pHead).flatMap (fun pCell =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout n W m).head t pHead)
              ((denseLayout n W m).cell t pCell a)
              ((denseLayout n W m).cell (t + 1) pCell a)])
        ++ (List.range (W - pHead - 1)).flatMap fun j =>
          (List.range mC).flatMap fun a =>
            [imply2 ((denseLayout n W m).head t pHead)
              ((denseLayout n W m).cell t (pHead + 1 + j) a)
              ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) :=
  clauseWriter_seq _ _ M Jmax wpJ
    (PinsHold M (persistParamPins2 wReg tReg W T t pHead)) _ _
    (persist_p_cell_writer_param M Jmax n W m mC T wReg tReg t pHead hplace)
    (persist_p_cell_writer_shift_param M Jmax n W m mC T wReg tReg t pHead hplace)

lemma persist_p_head_loop_writer_raw_param (M Jmax n W m mC T wReg tReg t : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
          (loopProg lvJ2 (ctlCell lvJ1)
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                    (persistCellNextEParam n m wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadEParam n m wReg)
                    (persistCellShiftEParam n m wReg)
                    (persistCellShiftNextEParam n m wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ (PinsHold M (persistParamPins1 wReg tReg W T t))
      ((List.range W).flatMap fun pHead =>
        (List.range pHead).flatMap (fun pCell =>
            (List.range mC).flatMap fun a =>
              [imply2 ((denseLayout n W m).head t pHead)
                ((denseLayout n W m).cell t pCell a)
                ((denseLayout n W m).cell (t + 1) pCell a)])
          ++ (List.range (W - pHead - 1)).flatMap fun j =>
            (List.range mC).flatMap fun a =>
              [imply2 ((denseLayout n W m).head t pHead)
                ((denseLayout n W m).cell t (pHead + 1 + j) a)
                ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) := by
  refine clauseWriter_forN _ M Jmax wpJ lvJ1 (persistParamPins1 wReg tReg W T t) _
    (ctlCell wReg) W (by unfold lvJ1; omega)
    (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega)
    (persist_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
      (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega)) ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ1
      (persistParamPins1 wReg tReg W T t) _ (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega)
      (persist_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
        (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega))
      (fun pHead => persist_p_head_fixed_writer_raw_param M Jmax n W m mC T wReg tReg t
        pHead hplace)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [persistParamPins1, persistParamPins0]) hF h0

lemma persist_t_fixed_writer_param (M Jmax n W m mC T wReg tReg t : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
          (loopProg lvJ2 (ctlCell lvJ1)
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                    (persistCellNextEParam n m wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
            (.seq (loopProg lvJ3 (.const mC)
                (leafProg wpJ lvJ3
                  (imply2Lits (persistHeadEParam n m wReg)
                    (persistCellShiftEParam n m wReg)
                    (persistCellShiftNextEParam n m wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ (PinsHold M (persistParamPins1 wReg tReg W T t))
      ((List.range W).flatMap fun pHead =>
        (List.range W).flatMap fun pCell =>
          if pHead = pCell then []
          else (List.range mC).map fun a =>
            imply2 ((denseLayout n W m).head t pHead)
              ((denseLayout n W m).cell t pCell a)
              ((denseLayout n W m).cell (t + 1) pCell a)) := by
  rw [← persist_family_eq_split_gen]
  exact persist_p_head_loop_writer_raw_param M Jmax n W m mC T wReg tReg t hplace

/-- The persistence program whose syntax contains parameter addresses but not their values. -/
def persistFamilyProgParam (n m mC wReg tReg : ℕ) : Program :=
  loopProg lvJ0 (ctlCell tReg)
    (.seq (loopProg lvJ1 (ctlCell wReg)
      (.seq (.seq
        (loopProg lvJ2 (ctlCell lvJ1)
          (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                (persistCellNextEParam n m wReg))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
          (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
                (persistCellShiftNextEParam n m wReg))))
            (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma persistFamilyProgParam_writer_param (M Jmax n W m mC T wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) :
    ClauseWriter (persistFamilyProgParam n m mC wReg tReg) M Jmax wpJ
      (PinsHold M [(wReg, W), (tReg, T)])
      (execPersistClausesAt (denseLayout n W m) (List.range mC) W T) := by
  unfold persistFamilyProgParam
  refine clauseWriter_forN _ M Jmax wpJ lvJ0 (persistParamPins0 wReg tReg W T) _
    (ctlCell tReg) T (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega)
    (persist_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace
      (by unfold lvJ0 ctlJmax; omega)) ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ0
      (persistParamPins0 wReg tReg W T) _ (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega)
      (persist_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace
        (by unfold lvJ0 ctlJmax; omega))
      (fun t => persist_t_fixed_writer_param M Jmax n W m mC T wReg tReg t hplace)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ tReg T τ (by simp [persistParamPins0]) hF h0

end NPComplete.CookLevin

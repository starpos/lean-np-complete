module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedValue
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedKit
public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelope

/-!
The persist family is the simplest of the five and settles the shape the other
four follow.  Its clauses say a cell away from the head keeps its symbol, so each
leaf writes one `imply2` row whose three expressions are dense variable numbers,
and the family is four nested loops around them.

Every obligation the leaves raise is dominated by one inequality, `PersistEnv`,
rather than by a separate hypothesis per expression.  The expression bounds were
proved with per-shape majorants, which is right for them — each is as tight as
its own shape allows — but a family citing five different shapes would push that
bookkeeping up into the envelope aggregation, where it would have to be redone
against the polynomial.  One inequality per family keeps the aggregation to five
obligations instead of twenty.

`PersistEnv` is stated over an arbitrary bound rather than over `B`, because the
two envelopes need the same shape: `B` covers the expressions' intermediates and
`S` covers what the variable numbers reach once written into the table.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- One inequality dominating every majorant the persist expressions use.  The
    largest is the shifted next-cell number, and the rest are below it. -/
def PersistEnv (K X n m : ℕ) : Prop :=
  K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) + K ≤ X

lemma persistEnv_of_le {K X X' n m : ℕ} (h : PersistEnv K X n m) (hX : X ≤ X') :
    PersistEnv K X' n m := le_trans h hX

/-! ## The two leaves

The family writes `imply2` rows of two shapes: one for cells before the head,
one for cells after it, the latter reading its position as a shifted sum.  Both
are literal lists of three, so both discharge `LitsBounded` the same way — an
expression bound and a value bound per literal, at any store with the right
control cells. -/

/-- The leaf for cells before the head. -/
lemma litsBounded_persist_before (K S B M n m wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (imply2Lits (persistHeadEParam n m wReg)
      (persistCellEParam n m wReg) (persistCellNextEParam n m wReg)) := by
  unfold PersistEnv at henvB henvS
  have hexp : (2 * K + 1) * m = 2 * (K * m) + m := by ring
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply2Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_persistHeadEParam M K B n m wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (persistHeadEParam_eval_le M K n m wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_persistCellEParam M K B n m wReg τ hK1 h0 g2 g4 g5 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (persistCellEParam_eval_le M K n m wReg τ h0 g2 g4 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_persistCellNextEParam M K B n m wReg τ hK1 h0 g2 g4 g5 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (persistCellNextEParam_eval_le M K n m wReg τ h0 g2 g4 g5 gw) (by omega)

/-- The leaf for cells after the head, whose position is a shifted sum. -/
lemma litsBounded_persist_after (K S B M n m wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m)
    (hn : n ≤ B) (hm : m ≤ B) :
    LitsBounded K S B M (imply2Lits (persistHeadEParam n m wReg)
      (persistCellShiftEParam n m wReg) (persistCellShiftNextEParam n m wReg)) := by
  unfold PersistEnv at henvB henvS
  have hexp : (2 * K + 1) * m = 2 * (K * m) + m := by ring
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply2Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_persistHeadEParam M K B n m wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hn hm
    · exact le_trans (persistHeadEParam_eval_le M K n m wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_persistCellShiftEParam M K B n m wReg τ hK1 h0 g2 g3 g4 g5 gw
        hwR2 (by omega) (by omega) hn hm
    · exact le_trans (persistCellShiftEParam_eval_le M K n m wReg τ h0 g2 g3 g4 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_persistCellShiftNextEParam M K B n m wReg τ h0 g2 g3 g4 g5 gw
        hwR2 (by omega) (by omega) hn hm
    · exact le_trans (persistCellShiftNextEParam_eval_le M K n m wReg τ h0 g2 g3 g4 g5 gw)
        (by omega)

/-! ## Level 3: the two letter loops -/

/-- The first letter loop's `ClauseWriterBounded`.  Each of the `mC` iterations
    writes one `imply2` row (width `8`), so the loop's own width is `mC * 8`. -/
lemma clauseWriterBounded_persist_letter (M Jmax K S B n W m mC T wReg tReg t pHead pCell : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) (h3S : 3 ≤ S) :
    ClauseWriterBounded (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
            (persistCellNextEParam n m wReg))))
      M Jmax wpJ K S B (mC * 8)
      (PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell)) := by
  have hne3 : ∀ p ∈ persistParamPins3 wReg tReg W T t pHead pCell, p.1 ≠ lvJ3 := by
    intro p hp
    simp only [persistParamPins3, persistParamPins2, persistParamPins1, persistParamPins0,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · unfold lvJ2 lvJ3; omega
    · unfold lvJ1 lvJ3; omega
    · unfold lvJ0 lvJ3; omega
    · have := hplace.w_min; unfold lvJ3; omega
    · have := hplace.t_min; unfold lvJ3; omega
  have hlvJ3le : lvJ3 ≤ 24 := by unfold lvJ3; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ3 mC 8 (.const mC) _
    (PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell))
    (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
    (by unfold lvJ3; omega) hlvJ3le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ3 _ τ h0 hne3 hF)
    (fun a _ => by
      simp only [List.length_cons, List.length_nil]
      rw [rowTableWidth_singleton]; simp [imply2])
    (persist_leaf_body_param M Jmax n W m T wReg tReg t pHead pCell hplace)
    (clauseLoopBodyBoundedUpTo_leafProg K S B M Jmax lvJ3 mC _
      (PinsHold M (persistParamPins3 wReg tReg W T t pHead pCell))
      (by unfold lvJ3; omega) hlvJ3le hJ hMB hSB hKB hKS
      hmCK (by simp [imply2Lits]; omega)
      (litsBounded_persist_before K S B M n m wReg hK1 hwR hwR2 hMB henvB henvS hn hm))
    (fun τ _ h0 => by simp [ExprBoundedIn]; omega)
    (fun τ _ _ => by simp [Expr.eval])

/-- The second letter loop's `ClauseWriterBounded`, at the shifted cell. -/
lemma clauseWriterBounded_persist_letter_shift
    (M Jmax K S B n W m mC T wReg tReg t pHead j : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) (h3S : 3 ≤ S) :
    ClauseWriterBounded (loopProg lvJ3 (.const mC)
        (leafProg wpJ lvJ3
          (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
            (persistCellShiftNextEParam n m wReg))))
      M Jmax wpJ K S B (mC * 8)
      (PinsHold M (persistParamPins3 wReg tReg W T t pHead j)) := by
  have hne3 : ∀ p ∈ persistParamPins3 wReg tReg W T t pHead j, p.1 ≠ lvJ3 := by
    intro p hp
    simp only [persistParamPins3, persistParamPins2, persistParamPins1, persistParamPins0,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · unfold lvJ2 lvJ3; omega
    · unfold lvJ1 lvJ3; omega
    · unfold lvJ0 lvJ3; omega
    · have := hplace.w_min; unfold lvJ3; omega
    · have := hplace.t_min; unfold lvJ3; omega
  have hlvJ3le : lvJ3 ≤ 24 := by unfold lvJ3; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ3 mC 8 (.const mC) _
    (PinsHold M (persistParamPins3 wReg tReg W T t pHead j))
    (fun a => [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t (pHead + 1 + j) a)
        ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)])
    (by unfold lvJ3; omega) hlvJ3le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ3 _ τ h0 hne3 hF)
    (fun a _ => by
      simp only [List.length_cons, List.length_nil]
      rw [rowTableWidth_singleton]; simp [imply2])
    (persist_leaf_body_shift_param M Jmax n W m T wReg tReg t pHead j hplace)
    (clauseLoopBodyBoundedUpTo_leafProg K S B M Jmax lvJ3 mC _
      (PinsHold M (persistParamPins3 wReg tReg W T t pHead j))
      (by unfold lvJ3; omega) hlvJ3le hJ hMB hSB hKB hKS
      hmCK (by simp [imply2Lits]; omega)
      (litsBounded_persist_after K S B M n m wReg hK1 hwR hwR2 hMB henvB henvS hn hm))
    (fun τ _ h0 => by simp [ExprBoundedIn]; omega)
    (fun τ _ _ => by simp [Expr.eval])

/-! ## Level 2: the two cell-position loops -/

/-- The first `pCell` loop, `[0, pHead)`.  `hpHK` (`pHead ≤ K`) is what the
enclosing `pHead` loop supplies from its own trip count.  Each of the `pHead`
iterations is itself the `mC`-row letter loop (width `mC * 8`), so the whole
loop's width is `pHead * (mC * 8)`. -/
lemma clauseWriterBounded_persist_pCell_before
    (M Jmax K S B n W m mC T wReg tReg t pHead : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hpHK : pHead ≤ K) :
    ClauseWriterBounded (loopProg lvJ2 (ctlCell lvJ1)
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellEParam n m wReg)
                (persistCellNextEParam n m wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ K S B (pHead * (mC * 8))
      (PinsHold M (persistParamPins2 wReg tReg W T t pHead)) := by
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlvJ2ctl : lvJ2 ≤ ctlJmax := by unfold lvJ2 ctlJmax; omega
  have hlvJ2Jmax : lvJ2 ≤ Jmax := le_trans hlvJ2ctl hplace.ctl_le
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hne2 : ∀ p ∈ persistParamPins2 wReg tReg W T t pHead, p.1 ≠ lvJ2 := by
    intro p hp
    simp only [persistParamPins2, persistParamPins1, persistParamPins0,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · unfold lvJ1 lvJ2; omega
    · unfold lvJ0 lvJ2; omega
    · have := hplace.w_min; unfold lvJ2; omega
    · have := hplace.t_min; unfold lvJ2; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ2 pHead (mC * 8) (ctlCell lvJ1) _
    (PinsHold M (persistParamPins2 wReg tReg W T t pHead))
    (fun pCell => (List.range mC).flatMap fun a =>
      [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
    hlvJ2 hlvJ2le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ2 _ τ h0 hne2 hF)
    (fun pCell _ => by
      set cs := (List.range mC).flatMap (fun a =>
        [imply2 ((denseLayout n W m).head t pHead)
          ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
        with hcs
      have hlen : cs.length = mC := by simp [hcs]
      rw [hlen]
      have hbound := rowTableWidth_le_count_mul (rowW cs) mC 3 (fun i hi => by
        have hmem : cs.getD i default ∈ cs := by
          rw [List.getD_eq_getElem _ _ (by omega : i < cs.length)]
          exact List.getElem_mem (by omega)
        simp only [hcs, List.mem_flatMap, List.mem_singleton, List.mem_range] at hmem
        obtain ⟨a, _, ha⟩ := hmem
        rw [rowW, ha]; simp [imply2])
      omega)
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ2 (persistParamPins2 wReg tReg W T t pHead) _
      (by omega) hlvJ2Jmax (by unfold lvJ2 wpJ; omega)
      (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
        hlvJ2ctl (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
      (fun i => persist_letter_writer_param M Jmax n W m mC T wReg tReg t pHead i hplace))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ2 K S B pHead (mC * 8)
      (persistParamPins2 wReg tReg W T t pHead) _
      hlvJ2 hlvJ2le hMB hKS (by omega) hpHK
      (fun pCell => persist_letter_writer_param M Jmax n W m mC T wReg tReg t pHead pCell hplace)
      (fun pCell => clauseWriterBounded_persist_letter M Jmax K S B n W m mC T wReg tReg t
        pHead pCell hplace hJ hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ2 _ τ h0 hne2 hF
      have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
      exact exprBoundedIn_ctlCell B M lvJ1 _ h1 (by omega))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ2 _ τ h0 hne2 hF
      have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
      exact ctlCell_eval_of_pin M _ lvJ1 pHead _ (by simp [persistParamPins2]) hev h1)

/-- The second `pCell` loop, `[0, W - pHead - 1)`.  Its count expression's
`ExprBoundedIn`/value obligations need `W`'s own value bounded by `B`
(`hWB`), since the count reads `wReg`'s content rather than a control
cell.  As in the `before` loop, each of the `W - pHead - 1` iterations is
the `mC`-row letter loop, so the whole loop's width is
`(W - pHead - 1) * (mC * 8)`. -/
lemma clauseWriterBounded_persist_pCell_shift
    (M Jmax K S B n W m mC T wReg tReg t pHead : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B) :
    ClauseWriterBounded (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
        (.seq (loopProg lvJ3 (.const mC)
            (leafProg wpJ lvJ3
              (imply2Lits (persistHeadEParam n m wReg) (persistCellShiftEParam n m wReg)
                (persistCellShiftNextEParam n m wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ K S B ((W - pHead - 1) * (mC * 8))
      (PinsHold M (persistParamPins2 wReg tReg W T t pHead)) := by
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlvJ2ctl : lvJ2 ≤ ctlJmax := by unfold lvJ2 ctlJmax; omega
  have hlvJ2Jmax : lvJ2 ≤ Jmax := le_trans hlvJ2ctl hplace.ctl_le
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hne2 : ∀ p ∈ persistParamPins2 wReg tReg W T t pHead, p.1 ≠ lvJ2 := by
    intro p hp
    simp only [persistParamPins2, persistParamPins1, persistParamPins0,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · unfold lvJ1 lvJ2; omega
    · unfold lvJ0 lvJ2; omega
    · have := hplace.w_min; unfold lvJ2; omega
    · have := hplace.t_min; unfold lvJ2; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ2 (W - pHead - 1) (mC * 8)
    (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1)) _
    (PinsHold M (persistParamPins2 wReg tReg W T t pHead))
    (fun j => (List.range mC).flatMap fun a =>
      [imply2 ((denseLayout n W m).head t pHead)
        ((denseLayout n W m).cell t (pHead + 1 + j) a)
        ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)])
    hlvJ2 hlvJ2le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ2 _ τ h0 hne2 hF)
    (fun j _ => by
      set cs := (List.range mC).flatMap (fun a =>
        [imply2 ((denseLayout n W m).head t pHead)
          ((denseLayout n W m).cell t (pHead + 1 + j) a)
          ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]) with hcs
      have hlen : cs.length = mC := by simp [hcs]
      rw [hlen]
      have hbound := rowTableWidth_le_count_mul (rowW cs) mC 3 (fun i hi => by
        have hmem : cs.getD i default ∈ cs := by
          rw [List.getD_eq_getElem _ _ (by omega : i < cs.length)]
          exact List.getElem_mem (by omega)
        simp only [hcs, List.mem_flatMap, List.mem_singleton, List.mem_range] at hmem
        obtain ⟨a, _, ha⟩ := hmem
        rw [rowW, ha]; simp [imply2])
      omega)
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ2 (persistParamPins2 wReg tReg W T t pHead) _
      (by omega) hlvJ2Jmax (by unfold lvJ2 wpJ; omega)
      (persist_param_pins2_ok Jmax wReg tReg W T t pHead lvJ2 hplace
        hlvJ2ctl (by unfold lvJ0 lvJ2; omega) (by unfold lvJ1 lvJ2; omega))
      (fun j => persist_letter_writer_shift_param M Jmax n W m mC T wReg tReg t pHead j hplace))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ2 K S B (W - pHead - 1) (mC * 8)
      (persistParamPins2 wReg tReg W T t pHead) _
      hlvJ2 hlvJ2le hMB hKS (by omega) (by omega)
      (fun j => persist_letter_writer_shift_param M Jmax n W m mC T wReg tReg t pHead j hplace)
      (fun j => clauseWriterBounded_persist_letter_shift M Jmax K S B n W m mC T wReg tReg t
        pHead j hplace hJ hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ2 _ τ h0 hne2 hF
      have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
      have h1v : ExprBoundedIn B _ (ctlCell wReg) :=
        exprBoundedIn_ctlCell B M wReg _ h1 (by omega)
      have h2v : ExprBoundedIn B _ (ctlCell lvJ1) :=
        exprBoundedIn_ctlCell B M lvJ1 _ h1 (by omega)
      have hWeval : (ctlCell wReg).eval ((ctlAssign lvJ2 (.const 0)).eval τ) = W :=
        ctlCell_eval_of_pin M _ wReg W _ (by simp [persistParamPins2, persistParamPins1,
          persistParamPins0]) hev h1
      have hwregB : (ctlCell wReg).eval ((ctlAssign lvJ2 (.const 0)).eval τ) ≤ B := by
        rw [hWeval]; omega
      refine ⟨⟨h1v, h2v, hwregB⟩, ?_, ?_⟩
      · show (1:ℕ) ≤ B
        omega
      · show (ctlCell wReg).eval ((ctlAssign lvJ2 (.const 0)).eval τ) -
          (ctlCell lvJ1).eval ((ctlAssign lvJ2 (.const 0)).eval τ) ≤ B
        omega)
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ2 _ τ h0 hne2 hF
      have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
      have eW : (ctlCell wReg).eval ((ctlAssign lvJ2 (.const 0)).eval τ) = W :=
        ctlCell_eval_of_pin M _ wReg W _ (by simp [persistParamPins2, persistParamPins1,
          persistParamPins0]) hev h1
      have e1 : (ctlCell lvJ1).eval ((ctlAssign lvJ2 (.const 0)).eval τ) = pHead :=
        ctlCell_eval_of_pin M _ lvJ1 pHead _ (by simp [persistParamPins2]) hev h1
      simp only [Expr.eval, eW, e1])

/-! ## Level 1: the `pHead` level -/

/-- Width of the `[0, pHead)` `pCell` clause list, uniformly by `K` since
`pHead ≤ K` — the bound level 1's own trip count (`W ≤ K`) supplies. -/
lemma persist_pCell_before_width (n W m t pHead mC K : ℕ) (hpHK : pHead ≤ K) :
    rowTableWidth (rowW ((List.range pHead).flatMap fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)]))
      ((List.range pHead).flatMap fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)]).length
      ≤ K * (mC * 8) := by
  set cs := (List.range pHead).flatMap (fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
    with hcs
  have hlen : cs.length = pHead * mC := by simp [hcs, List.length_flatMap]
  rw [hlen]
  have hbound := rowTableWidth_le_count_mul (rowW cs) (pHead * mC) 3 (fun i hi => by
    have hmem : cs.getD i default ∈ cs := by
      rw [List.getD_eq_getElem _ _ (by omega : i < cs.length)]
      exact List.getElem_mem (by omega)
    simp only [hcs, List.mem_flatMap, List.mem_range, List.mem_singleton] at hmem
    obtain ⟨pCell, _, a, _, ha⟩ := hmem
    rw [rowW, hcs, ha]; simp [imply2])
  have hpm : pHead * mC ≤ K * mC := Nat.mul_le_mul_right _ hpHK
  nlinarith [hbound, hpm]

/-- Width of the `[0, W - pHead - 1)` `pCell` clause list, uniformly by `K`
since `W ≤ K`. -/
lemma persist_pCell_shift_width (n W m t pHead mC K : ℕ) (hWK : W ≤ K) :
    rowTableWidth (rowW ((List.range (W - pHead - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t (pHead + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]))
      ((List.range (W - pHead - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t (pHead + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)]).length
      ≤ K * (mC * 8) := by
  set cs := (List.range (W - pHead - 1)).flatMap (fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t (pHead + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead + 1 + j) a)])
    with hcs
  have hlen : cs.length = (W - pHead - 1) * mC := by simp [hcs, List.length_flatMap]
  rw [hlen]
  have hbound := rowTableWidth_le_count_mul (rowW cs) ((W - pHead - 1) * mC) 3 (fun i hi => by
    have hmem : cs.getD i default ∈ cs := by
      rw [List.getD_eq_getElem _ _ (by omega : i < cs.length)]
      exact List.getElem_mem (by omega)
    simp only [hcs, List.mem_flatMap, List.mem_range, List.mem_singleton] at hmem
    obtain ⟨j, _, a, _, ha⟩ := hmem
    rw [rowW, hcs, ha]; simp [imply2])
  have hpm : (W - pHead - 1) * mC ≤ K * mC := Nat.mul_le_mul_right _ (by omega)
  nlinarith [hbound, hpm]

/-- The two `pCell` loops joined by `.seq`, then the `lvJ1` bump: level 1's
own body as an UpTo-bounded loop body over the outer pins.  The two loops
compose through `clauseWriterBounded_seq` before either combinator's own
`Frozen` (which pins `lvJ1 = pHead`) is available — feeding the resulting
`.seq loopA loopB` to `clauseLoopBodyBoundedUpTo_of_clauseWriterBounded` as one
`prog` is what avoids a bespoke "two loops then bump" combinator.  Each `pCell`
loop's own width is at most `K * (mC * 8)` (Levels 2/3's widths, widened
uniformly by `pHead, W - pHead - 1 ≤ K`), so their sum bounds level 1's own
per-iteration width. -/
lemma clauseLoopBodyBoundedUpTo_persist_pHead
    (M Jmax K S B n W m mC T wReg tReg t : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B) :
    ClauseLoopBodyBoundedUpTo (.seq
        (.seq
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
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))
      M Jmax wpJ lvJ1 K S B W (K * (mC * 8) + K * (mC * 8))
      (PinsHold M (persistParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  refine clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ1 K S B W
    (K * (mC * 8) + K * (mC * 8)) (persistParamPins1 wReg tReg W T t)
    (fun pHead' => (List.range pHead').flatMap (fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead')
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
      ++ (List.range (W - pHead' - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead')
            ((denseLayout n W m).cell t (pHead' + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead' + 1 + j) a)])
    hlvJ1 hlvJ1le hMB hKS (by omega) hWK
    (fun i => persist_p_head_fixed_writer_raw_param M Jmax n W m mC T wReg tReg t i hplace)
    (fun i => clauseWriterBounded_of_le_or_vacuous _ M Jmax wpJ K S B (K * (mC * 8) + K * (mC * 8))
      lvJ1 i (persistParamPins1 wReg tReg W T t) hlvJ1 hlvJ1le (fun hiK =>
        clauseWriterBounded_seq _ _ M Jmax wpJ K S B (K * (mC * 8)) (K * (mC * 8))
          (PinsHold M ((lvJ1, i) :: persistParamPins1 wReg tReg W T t))
          ((List.range i).flatMap fun pCell =>
            (List.range mC).flatMap fun a =>
              [imply2 ((denseLayout n W m).head t i)
                ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
          (persist_p_cell_writer_param M Jmax n W m mC T wReg tReg t i hplace)
          (persist_pCell_before_width n W m t i mC K hiK)
          (clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B (i * (mC * 8)) (K * (mC * 8))
            (PinsHold M ((lvJ1, i) :: persistParamPins1 wReg tReg W T t))
            (Nat.mul_le_mul_right _ hiK)
            (clauseWriterBounded_persist_pCell_before M Jmax K S B n W m mC T wReg tReg
              t i hplace hJ hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hiK))
          (clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B ((W - i - 1) * (mC * 8)) (K * (mC * 8))
            (PinsHold M ((lvJ1, i) :: persistParamPins1 wReg tReg W T t))
            (Nat.mul_le_mul_right _ (by omega))
            (clauseWriterBounded_persist_pCell_shift M Jmax K S B n W m mC T wReg tReg t i hplace
              hJ hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hWK hWB))))

/-- Level 1 as a whole: `loopProg lvJ1 (ctlCell wReg) ...`, closing
`clauseLoopBodyBoundedUpTo_persist_pHead` into a `ClauseWriterBounded`.
`W` iterations of width `K * (mC * 8) + K * (mC * 8)` each. -/
lemma clauseWriterBounded_persist_t
    (M Jmax K S B n W m mC T wReg tReg t : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B) :
    ClauseWriterBounded (loopProg lvJ1 (ctlCell wReg)
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
      M Jmax wpJ K S B (W * (K * (mC * 8) + K * (mC * 8)))
      (PinsHold M (persistParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ1ctl : lvJ1 ≤ ctlJmax := by unfold lvJ1 ctlJmax; omega
  have hlvJ1Jmax : lvJ1 ≤ Jmax := le_trans hlvJ1ctl hplace.ctl_le
  have hne1 : ∀ p ∈ persistParamPins1 wReg tReg W T t, p.1 ≠ lvJ1 := by
    intro p hp
    simp only [persistParamPins1, persistParamPins0,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · unfold lvJ0 lvJ1; omega
    · have := hplace.w_min; unfold lvJ1; omega
    · have := hplace.t_min; unfold lvJ1; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ1 W (K * (mC * 8) + K * (mC * 8))
    (ctlCell wReg) _
    (PinsHold M (persistParamPins1 wReg tReg W T t))
    (fun pHead' => (List.range pHead').flatMap (fun pCell =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead')
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)])
      ++ (List.range (W - pHead' - 1)).flatMap fun j =>
        (List.range mC).flatMap fun a =>
          [imply2 ((denseLayout n W m).head t pHead')
            ((denseLayout n W m).cell t (pHead' + 1 + j) a)
            ((denseLayout n W m).cell (t + 1) (pHead' + 1 + j) a)])
    hlvJ1 hlvJ1le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ1 _ τ h0 hne1 hF)
    (fun pHead' hlt => by
      rw [rowTableWidth_append_total]
      gcongr
      · exact persist_pCell_before_width n W m t pHead' mC K (by omega)
      · exact persist_pCell_shift_width n W m t pHead' mC K hWK)
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ1 (persistParamPins1 wReg tReg W T t) _
      (by omega) hlvJ1Jmax (by unfold lvJ1 wpJ; omega)
      (persist_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace hlvJ1ctl
        (by unfold lvJ0 lvJ1; omega))
      (fun pHead' => persist_p_head_fixed_writer_raw_param M Jmax n W m mC T wReg tReg t pHead'
        hplace))
    (clauseLoopBodyBoundedUpTo_persist_pHead M Jmax K S B n W m mC T wReg tReg t hplace hJ
      hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hWK hWB)
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ1 _ τ h0 hne1 hF
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ1 _ τ h0 hne1 hF
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [persistParamPins1, persistParamPins0])
        hev h1)

/-! ## Level 0: the `t` level and the whole family -/

/-- Level 0's body: `loopProg lvJ1 ...` (level 1's whole), then the `lvJ0`
bump — the same "run a bounded writer, then bump" shape as level 1's own
body, one level up.  `W * (K * (mC * 8) + K * (mC * 8))` is level 1's own
width, from `clauseWriterBounded_persist_t`, and does not depend on `t`. -/
lemma clauseLoopBodyBoundedUpTo_persist_t
    (M Jmax K S B n W m mC T wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B)
    (hTK : T ≤ K) :
    ClauseLoopBodyBoundedUpTo (.seq
        (loopProg lvJ1 (ctlCell wReg)
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
        (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))
      M Jmax wpJ lvJ0 K S B T (W * (K * (mC * 8) + K * (mC * 8)))
      (PinsHold M [(wReg, W), (tReg, T)]) := by
  have hlvJ0 : 2 ≤ lvJ0 := by unfold lvJ0; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  refine clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ0 K S B T
    (W * (K * (mC * 8) + K * (mC * 8))) [(wReg, W), (tReg, T)]
    (fun t => (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a))
    hlvJ0 hlvJ0le hMB hKS (by omega) hTK
    (fun t => persist_t_fixed_writer_param M Jmax n W m mC T wReg tReg t hplace)
    (fun t => clauseWriterBounded_persist_t M Jmax K S B n W m mC T wReg tReg t hplace hJ
      hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hWK hWB)

/-- A uniform bound on each generated row gives a count bound for a range flattening;
this is the clause-count contract used at both levels of the persist family. -/
lemma persist_t_width_range_flat_map_length_le {α : Type} (n m : ℕ)
    (f : ℕ → List α) (hf : ∀ i ∈ List.range n, (f i).length ≤ m) :
    ((List.range n).flatMap f).length ≤ n * m := by
  rw [List.length_flatMap]
  calc
    _ ≤ ((List.range n).map fun _ => m).sum := by
      apply List.sum_le_sum
      intro i hi
      exact hf i hi
    _ = n * m := by simp

/-- Width of one `t`-level clause list: at most `W * W` `(pHead, pCell)` pairs,
`mC` rows each, each of width `8` — widened uniformly by `W ≤ K`. -/
lemma persist_t_width (n W m mC K : ℕ) (t : ℕ) (hWK : W ≤ K) :
    rowTableWidth (rowW ((List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)))
      ((List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a)).length
      ≤ W * (K * (mC * 8) + K * (mC * 8)) := by
  set cs := (List.range W).flatMap (fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a))
    with hcs
  have hlen : cs.length ≤ W * (W * mC) := by
    rw [hcs]
    apply persist_t_width_range_flat_map_length_le
    intro pHead _
    apply persist_t_width_range_flat_map_length_le
    intro pCell _
    by_cases heq : pHead = pCell <;> simp [heq]
  have hwid := rowTableWidth_le_count_mul (rowW cs) cs.length 3 (fun i hi => by
    have hmem : cs.getD i default ∈ cs := by
      rw [List.getD_eq_getElem _ _ (by omega : i < cs.length)]
      exact List.getElem_mem (by omega)
    simp only [hcs, List.mem_flatMap, List.mem_range] at hmem
    obtain ⟨pHead, _, pCell, _, hmem2⟩ := hmem
    by_cases heq : pHead = pCell
    · simp [heq] at hmem2
    · simp only [heq, ite_false, List.mem_map, List.mem_range] at hmem2
      obtain ⟨a, _, ha⟩ := hmem2
      rw [rowW, hcs, ← ha]; simp [imply2])
  have h1 : W * mC ≤ K * mC := Nat.mul_le_mul_right _ hWK
  have heq1 : K * (mC * 8) = K * mC * 8 := by ring
  have h4 : W * (W * mC * 8) ≤ W * (K * mC * 8 + K * mC * 8) := by
    apply Nat.mul_le_mul_left; omega
  have hfinal : W * (W * mC) * 8 ≤ W * (K * (mC * 8) + K * (mC * 8)) := by
    calc W * (W * mC) * 8 = W * (W * mC * 8) := by ring
      _ ≤ W * (K * mC * 8 + K * mC * 8) := h4
      _ = W * (K * (mC * 8) + K * (mC * 8)) := by rw [heq1]
  nlinarith [hwid, hlen, hfinal]

/-- The full persist family, as a `ClauseWriterBounded`. The outermost loop's
counter reaches `T`, so its loop-body bound needs `T ≤ K`; `hTK1`
(`T + 1 ≤ K`) supplies that inequality. -/
lemma clauseWriterBounded_persistFamilyProgParam (K S B M Jmax n m mC W T wReg tReg : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : PersistEnv K B n m) (henvS : PersistEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K)
    (h3S : 3 ≤ S) (hWK : W ≤ K) (hWB : W ≤ B)
    (hTK1 : T + 1 ≤ K) :
    ClauseWriterBounded (persistFamilyProgParam n m mC wReg tReg) M Jmax wpJ K S B
      (T * (W * (K * (mC * 8) + K * (mC * 8)))) (PinsHold M [(wReg, W), (tReg, T)]) := by
  unfold persistFamilyProgParam
  have hlvJ0 : 2 ≤ lvJ0 := by unfold lvJ0; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  have hne0 : ∀ p ∈ ([(wReg, W), (tReg, T)] : List (ℕ × ℕ)), p.1 ≠ lvJ0 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have := hplace.w_min; unfold lvJ0; omega
    · have := hplace.t_min; unfold lvJ0; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 T (W * (K * (mC * 8) + K * (mC * 8)))
    (ctlCell tReg) _
    (PinsHold M [(wReg, W), (tReg, T)])
    (fun t => (List.range W).flatMap fun pHead =>
      (List.range W).flatMap fun pCell =>
        if pHead = pCell then []
        else (List.range mC).map fun a =>
          imply2 ((denseLayout n W m).head t pHead)
            ((denseLayout n W m).cell t pCell a) ((denseLayout n W m).cell (t + 1) pCell a))
    hlvJ0 hlvJ0le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ0 _ τ h0 hne0 hF)
    (fun t _ => persist_t_width n W m mC K t hWK)
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ0 [(wReg, W), (tReg, T)] _
      (by omega) (le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega)
      (persist_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace (by unfold lvJ0 ctlJmax; omega))
      (fun t => persist_t_fixed_writer_param M Jmax n W m mC T wReg tReg t hplace))
    (clauseLoopBodyBoundedUpTo_persist_t M Jmax K S B n W m mC T wReg tReg hplace hJ hK1 hwR
      hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h3S hWK hWB (by omega))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ0 _ τ h0 hne0 hF
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by omega), h0]
      exact exprBoundedIn_ctlCell B M tReg _ h1 (by omega))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ0 _ τ h0 hne0 hF
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by omega), h0]
      exact ctlCell_eval_of_pin M _ tReg T _ (by simp) hev h1)

end NPComplete.CookLevin

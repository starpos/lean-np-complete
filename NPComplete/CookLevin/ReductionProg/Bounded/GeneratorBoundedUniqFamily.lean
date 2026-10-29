module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedUniq
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedKit
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAtLeastOne
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyUniqueness

/-!
The uniqueness family follows the assembly kit `GeneratorBoundedKit` used by
the persist family, with one addition: two of its three blocks are
`clauseWriter_exactlyOne_range` — a `writeAtLeastOneProg` row of run-time width
followed by the `atMostOneRange` double loop — rather than a fixed-width leaf
nest.  `GeneratorBoundedAtLeastOne`'s bound for `writeAtLeastOneProg` slots into
the kit's `clauseWriterBounded_seq` the same way a loop's bound would.

Counting the `clauseWriter_exactlyOne_range` block (including its double loop) as
one packaged component, the assembly kit is three levels deep; persist's kit has
four. Once that block is packaged, the rest follows the same pattern.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The table width one `exactlyOne` block consumes, uniformly bounded by
`K` once its own length `len` is under `K`.  Reused for all three uniqueness
blocks (state/head/cell), whose lengths are `nC`/`W`/`mC` respectively. -/
lemma exactlyOne_width_le (K len : ℕ) (vals : ℕ → ℕ) (hlenK : len ≤ K) :
    rowTableWidth (rowW (exactlyOne ((List.range len).map vals)))
      (exactlyOne ((List.range len).map vals)).length
      ≤ (2 + 2 * len) + len * (K * 6) := by
  rw [exactlyOne_eq_atLeastOne_append, rowTableWidth_append_total]
  gcongr
  · rw [show ([atLeastOne ((List.range len).map vals)] : List Clause).length = 1 from rfl,
      rowTableWidth_singleton, atLeastOne_length, range_map_length]
  · rw [atMostOneRange_range_map_flatMap]
    set cs := (List.range len).flatMap (fun i =>
      (List.range (len - i - 1)).flatMap fun j =>
        ([negPair (vals i) (vals (i + 1 + j))] : List Clause)) with hcs
    have hlen : cs.length ≤ len * len := by
      rw [hcs, List.length_flatMap]
      calc ((List.range len).map fun i =>
          ((List.range (len - i - 1)).flatMap fun j =>
            ([negPair (vals i) (vals (i + 1 + j))] : List Clause)).length).sum
        ≤ ((List.range len).map fun _ => len).sum :=
          List.sum_le_sum (fun i _ => by simp; omega)
      _ = len * len := by simp
    have hbound := rowTableWidth_le_count_mul (rowW cs) cs.length 2 (fun k hk => by
      have hmem : cs.getD k default ∈ cs := by
        rw [List.getD_eq_getElem _ _ (by omega : k < cs.length)]
        exact List.getElem_mem (by omega)
      simp only [hcs, List.mem_flatMap, List.mem_range, List.mem_singleton] at hmem
      obtain ⟨i, _, j, _, hj⟩ := hmem
      rw [rowW, hj]; simp [negPair])
    have h1 : len * len ≤ len * K := Nat.mul_le_mul_left _ hlenK
    nlinarith [hbound, hlen, h1]

/-! ## The `atMostOneRange` double loop, bounded -/

/-- The inner `negPair` loop (`atMostOneRange`'s inner range), bounded.  `len -
i - 1` iterations, each a 6-wide `negPair` row (widened uniformly to `K * 6`
since `len ≤ K`).  `cntE` is a general count expression (not necessarily a
compile-time constant), matching `clauseWriterBounded_uniq_outer`; `hcntEB`/
`hcntEV` are its bound/value at the reset store, which is what `hsubB` below
needs to bound the `sub`'s own two operands. -/
lemma clauseWriterBounded_uniq_inner
    (K S B M Jmax iOuter iInner len i : ℕ) (cntE indexE shiftE : Expr)
    (pins : List (ℕ × ℕ)) (av bv : ℕ → ℕ)
    (hiOuterle : iOuter ≤ 24)
    (hiInner : 2 ≤ iInner) (hiInnerle : iInner ≤ 24)
    (hJ : 24 ≤ Jmax) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hlenK : len ≤ K) (h2S : 2 ≤ S)
    (hne : ∀ p ∈ ((iOuter, i) :: pins : List (ℕ × ℕ)), p.1 ≠ iInner)
    (hcntEB : ∀ τ : Store, PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      ExprBoundedIn B ((ctlAssign iInner (.const 0)).eval τ) cntE)
    (hcntEV : ∀ τ : Store, PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      cntE.eval ((ctlAssign iInner (.const 0)).eval τ) = len)
    (hbody : ClauseLoopBody (leafProg wpJ iInner (negPairLits indexE shiftE))
      M Jmax wpJ iInner (PinsHold M ((iOuter, i) :: pins)) (fun j => [negPair (av i) (bv j)]))
    (hlits : LitsBounded K S B M (negPairLits indexE shiftE)) :
    ClauseWriterBounded (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
        (leafProg wpJ iInner (negPairLits indexE shiftE)))
      M Jmax wpJ K S B (K * 6) (PinsHold M ((iOuter, i) :: pins)) := by
  refine clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B ((len - i - 1) * 6) (K * 6)
    (PinsHold M ((iOuter, i) :: pins)) (Nat.mul_le_mul_right _ (by omega)) ?_
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax iInner (len - i - 1) 6
    (.sub (.sub cntE (ctlCell iOuter)) (.const 1)) _
    (PinsHold M ((iOuter, i) :: pins))
    (fun j => [negPair (av i) (bv j)])
    (by omega) hiInnerle hMB
    (fun τ hF h0 => pinsHold_reset M iInner _ τ h0 hne hF)
    (fun j _ => by
      rw [show ([negPair (av i) (bv j)] : List Clause).length = 1 from rfl,
        rowTableWidth_singleton]
      simp [negPair])
    hbody
    (clauseLoopBodyBoundedUpTo_leafProg K S B M Jmax iInner (len - i - 1) _
      (PinsHold M ((iOuter, i) :: pins)) (by omega) hiInnerle hJ hMB hSB hKB hKS
      (by omega) (by simp [negPairLits]; omega) hlits)
    (fun τ hF h0 => by
      have hev := pinsHold_reset M iInner _ τ h0 hne hF
      have h1 : ((ctlAssign iInner (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + iInner) 0 0 (by omega), h0]
      have hi' : ((ctlAssign iInner (.const 0)).eval τ) (M + iOuter) = i :=
        pinsHold_head M (iOuter, i) pins _ hev
      have hocB : ExprBoundedIn B ((ctlAssign iInner (.const 0)).eval τ) (ctlCell iOuter) :=
        exprBoundedIn_ctlCell B M iOuter _ h1 (by omega)
      have hcB := hcntEB τ hF h0
      have hcV := hcntEV τ hF h0
      have hsubB : ExprBoundedIn B ((ctlAssign iInner (.const 0)).eval τ)
          (.sub cntE (ctlCell iOuter)) := by
        refine ⟨hcB, hocB, ?_⟩
        rw [hcV]; omega
      exact ⟨hsubB, by simp [ExprBoundedIn]; omega, by
        simp only [Expr.eval, ctlCell_eval, h1, hi', hcV]; omega⟩)
    (fun τ hF h0 => by
      have hev := pinsHold_reset M iInner _ τ h0 hne hF
      have h1 : ((ctlAssign iInner (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + iInner) 0 0 (by omega), h0]
      have hi' : ((ctlAssign iInner (.const 0)).eval τ) (M + iOuter) = i :=
        pinsHold_head M (iOuter, i) pins _ hev
      simp only [Expr.eval, ctlCell_eval, h1, hi', hcntEV τ hF h0])

/-- The outer `atMostOneRange` loop, bounded: `len` iterations, each an inner
loop widened to `K * 6`.  `cntE` is a general count expression (not necessarily
a compile-time constant) so both the state/cell blocks (`.const nC`) and the
head block (`ctlCell wReg`) can share one lemma. -/
lemma clauseWriterBounded_uniq_outer
    (K S B M Jmax iOuter iInner len : ℕ) (cntE indexE shiftE : Expr) (av bv : ℕ → ℕ → ℕ)
    (pins : List (ℕ × ℕ))
    (hiOuter : 2 ≤ iOuter) (hiOuterle : iOuter ≤ 24) (hiOuterJ : iOuter ≤ Jmax)
    (hMB : M + 24 ≤ B)
    (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hlenK : len ≤ K)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ wpJ)
    (hcntE : ∀ τ : Store, PinsHold M pins τ → τ 0 = M →
      ExprBoundedIn B ((ctlAssign iOuter (.const 0)).eval τ) cntE)
    (hcntN : ∀ τ : Store, PinsHold M pins τ → τ 0 = M →
      cntE.eval ((ctlAssign iOuter (.const 0)).eval τ) = len)
    (hw : ∀ i, ClauseWriter (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
        (leafProg wpJ iInner (negPairLits indexE shiftE)))
      M Jmax wpJ (PinsHold M ((iOuter, i) :: pins)) ((List.range (len - i - 1)).flatMap
        fun j => [negPair (av i i) (bv i j)]))
    (hb : ∀ i, ClauseWriterBounded (loopProg iInner
        (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
        (leafProg wpJ iInner (negPairLits indexE shiftE)))
      M Jmax wpJ K S B (K * 6) (PinsHold M ((iOuter, i) :: pins))) :
    ClauseWriterBounded (loopProg iOuter cntE
        (.seq (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits indexE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1)))))
      M Jmax wpJ K S B (len * (K * 6)) (PinsHold M pins) := by
  have hne : ∀ p ∈ pins, p.1 ≠ iOuter := fun p hp => (hpin p hp).2.2.1
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax iOuter len (K * 6) cntE _
    (PinsHold M pins)
    (fun i => (List.range (len - i - 1)).flatMap fun j => [negPair (av i i) (bv i j)])
    (by omega) hiOuterle hMB
    (fun τ hF h0 => pinsHold_reset M iOuter _ τ h0 hne hF)
    (fun i _ => by
      set cs := (List.range (len - i - 1)).flatMap
        (fun j => ([negPair (av i i) (bv i j)] : List Clause)) with hcs
      have hlen : cs.length = len - i - 1 := by simp [hcs]
      rw [hlen]
      have hbound := rowTableWidth_le_count_mul (rowW cs) (len - i - 1) 2 (fun k hk => by
        have hmem : cs.getD k default ∈ cs := by
          rw [List.getD_eq_getElem _ _ (by omega : k < cs.length)]
          exact List.getElem_mem (by omega)
        simp only [hcs, List.mem_flatMap, List.mem_range, List.mem_singleton] at hmem
        obtain ⟨j, _, hj⟩ := hmem
        rw [rowW, hj]; simp [negPair])
      have h1 : len - i - 1 ≤ K := by omega
      nlinarith [hbound, h1])
    (clauseLoopBody_of_writer _ M Jmax wpJ iOuter pins _
      (by omega) hiOuterJ (by unfold wpJ; omega) hpin hw)
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ iOuter K S B len (K * 6) pins _
      hiOuter hiOuterle hMB hKS (by omega) hlenK hw hb)
    hcntE hcntN

/-! ## `writeAtLeastOneProg` then the `atMostOneRange` nest -/

/-- `clauseWriter_exactlyOne_range`'s program, packaged as `ClauseWriterBounded`:
`writeAtLeastOneProg` (width `2 + 2*len`), then the outer/inner `negPair` nest
(width `len * (K * 6)`).  General in `cntE` for the same reason as
`clauseWriterBounded_uniq_outer`. -/
lemma clauseWriterBounded_exactly_one_range
    (K S B M Jmax iOuter iInner len : ℕ) (cntE indexE shiftE : Expr) (vs : List ℕ)
    (pins : List (ℕ × ℕ)) (hlen : vs.length = len)
    (hw1 : ClauseWriter (writeAtLeastOneProg wpJ iOuter cntE indexE)
      M Jmax wpJ (PinsHold M pins) [atLeastOne vs])
    (hb1 : ClauseWriterBounded (writeAtLeastOneProg wpJ iOuter cntE indexE)
      M Jmax wpJ K S B (2 + 2 * len) (PinsHold M pins))
    (hb2 : ClauseWriterBounded (loopProg iOuter cntE
        (.seq (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits indexE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1)))))
      M Jmax wpJ K S B (len * (K * 6)) (PinsHold M pins)) :
    ClauseWriterBounded (.seq (writeAtLeastOneProg wpJ iOuter cntE indexE)
        (loopProg iOuter cntE
        (.seq (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits indexE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1))))))
      M Jmax wpJ K S B ((2 + 2 * len) + len * (K * 6)) (PinsHold M pins) :=
  clauseWriterBounded_seq _ _ M Jmax wpJ K S B (2 + 2 * len) (len * (K * 6))
    (PinsHold M pins) [atLeastOne vs] hw1
    (by rw [show ([atLeastOne vs] : List Clause).length = 1 from rfl,
      rowTableWidth_singleton, atLeastOne_length, hlen])
    hb1 hb2

/-! ## The state block (`lvJ1`/`lvJ2`, `.const nC`) -/

/-- Shared pin facts for the state/head blocks, at depth 1 (`lvJ1`/`lvJ2`). -/
lemma uniqueness_param_pins1_two (Jmax wReg tReg W T t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ∀ p ∈ uniquenessParamPins1 wReg tReg W T t,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ lvJ2 ∧ p.1 ≠ wpJ := by
  intro p hp
  have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
    (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
  have h2 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ2 hplace
    (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega) p hp
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h2.2.2.1, h1.2.2.2⟩

/-- `writeAtLeastOneProg`'s `ClauseWriterBounded`, for the state block's
run-time-width `atLeastOne` row. -/
lemma uniq_state_atLeastOne_bounded
    (M Jmax K S B nS W mS nC T wReg tReg t : ℕ) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hnCK : nC ≤ K) :
    ClauseWriterBounded (writeAtLeastOneProg wpJ lvJ1 (.const nC)
        (uniqStateBaseEParam nS mS wReg))
      M Jmax wpJ K S B (2 + 2 * nC) (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  exact clauseWriterBounded_writeAtLeastOneProg K S B M Jmax lvJ1 nC (.const nC)
    (uniqStateBaseEParam nS mS wReg) (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
    hlvJ1 hlvJ1le hJ hMB hKB hKS hSB hnCK
    (fun τ _ _ => by simp [ExprBoundedIn]; omega) (fun τ _ _ => by simp [Expr.eval])
    (fun τ wp _ _ _ _ => by simp [ExprBoundedIn]; omega)
    (fun τ wp _ _ _ _ => by simp [Expr.eval])
    (fun τ h0 ht hst => by
      have g2 := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
      have g3 := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
      have gw := ht wReg hwR (by omega)
      exact ⟨exprBoundedIn_uniqStateBaseEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by unfold UniqEnv at henvB; omega) hn hm,
        le_trans (uniqStateBaseEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw)
          (by unfold UniqEnv at henvS; omega)⟩)

/-- The state block's `writeAtLeastOneProg` correctness fact, needed alongside
its bound (`clauseWriterBounded_exactly_one_range`'s `hw1`). -/
lemma uniq_state_atLeastOne_writer
    (M Jmax nS W mS nC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      [atLeastOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)] :=
  clauseWriter_atLeastOne M Jmax wpJ lvJ1 (.const nC)
    (uniqStateBaseEParam nS mS wReg) (uniquenessParamPins1 wReg tReg W T t)
    ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega)
    (fun p hp => by
      have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
        (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
      exact ⟨h1.1, h1.2.1, h1.2.2.2, h1.2.2.1⟩)
    (fun τ _ _ => by rw [range_map_length]; simp [Expr.eval])
    (fun σ1 σ2 _ _ _ => rfl)
    (hdep_pins_to_bound M Jmax wpJ (uniqStateBaseEParam nS mS wReg)
      (fun σ σ' hσ hσ' h => uniqueness_param_state_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h))
    (fun τ k hF h0 hk hklt => by
      rw [range_map_length] at hklt
      rw [range_map_getD nC (fun q => (denseLayout nS W mS).state t q) k hklt]
      exact uniqueness_param_state_base_value M nS W mS T wReg tReg t k τ
        (pinsHold_cons M (lvJ1, k) (uniquenessParamPins1 wReg tReg W T t) τ hk hF) h0)

/-- The state block's inner-loop correctness fact for a fixed outer index `i`. -/
lemma uniq_state_inner_writer
    (M Jmax nS W mS nC T wReg tReg t i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
        (leafProg wpJ lvJ2 (negPairLits (uniqStateBaseEParam nS mS wReg)
          (uniqStateShiftEParam nS mS wReg))))
      M Jmax wpJ (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t))
      ((List.range (nC - i - 1)).flatMap fun j =>
        [negPair ((denseLayout nS W mS).state t i)
          ((denseLayout nS W mS).state t (i + 1 + j))]) :=
  clauseWriter_atMostOneRange_inner M Jmax wpJ lvJ1 lvJ2
    (uniquenessParamPins1 wReg tReg W T t) (uniqStateBaseEParam nS mS wReg)
    (uniqStateShiftEParam nS mS wReg) nC i
    (fun _ => (denseLayout nS W mS).state t i) (fun j => (denseLayout nS W mS).state t (i + 1 + j))
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega) (by unfold lvJ2 wpJ; omega)
    (uniqueness_param_pins1_two Jmax wReg tReg W T t hplace)
    (fun σ σ' hσ hσ' h => uniqueness_param_state_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_state_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ hF h0 => uniqueness_param_state_base_value M nS W mS T wReg tReg t i τ hF h0)
    (fun τ j hF h0 hj =>
      uniqueness_param_state_shift_value M nS W mS T wReg tReg t i j τ hF h0 hj)

/-- The state block's inner-loop `ClauseWriterBounded`, for a fixed outer
index `i`. -/
lemma uniq_state_inner_bounded
    (M Jmax K S B nS W mS nC T wReg tReg t i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hnCK : nC ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
        (leafProg wpJ lvJ2 (negPairLits (uniqStateBaseEParam nS mS wReg)
          (uniqStateShiftEParam nS mS wReg))))
      M Jmax wpJ K S B (K * 6)
      (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlits2 : LitsBounded K S B M (negPairLits (uniqStateBaseEParam nS mS wReg)
      (uniqStateShiftEParam nS mS wReg)) := litsBounded_uniq_state K S B M nS mS wReg
    hK1 hwR hwR2 hMB henvB henvS hn hm
  have hbody2 : ClauseLoopBody (leafProg wpJ lvJ2 (negPairLits
      (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg)))
      M Jmax wpJ lvJ2 (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t))
      (fun j => [negPair ((denseLayout nS W mS).state t i)
        ((denseLayout nS W mS).state t (i + 1 + j))]) :=
    clauseLoopBody_negPair M Jmax wpJ lvJ2
      (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg)
      ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t)
      (fun _ => (denseLayout nS W mS).state t i)
      (fun j => (denseLayout nS W mS).state t (i + 1 + j))
      (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
      (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ2 wpJ; omega)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨by unfold lvJ1; omega, Nat.le_trans (by unfold lvJ1 ctlJmax; omega)
            hplace.ctl_le, by unfold lvJ1 lvJ2; omega, by unfold lvJ1 wpJ; omega⟩
        · have h := uniqueness_param_pins1_two Jmax wReg tReg W T t hplace p hp'
          exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      (fun σ σ' hσ hσ' h => uniqueness_param_state_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun σ σ' hσ hσ' h => uniqueness_param_state_shift_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun τ _ hF h0 _ => uniqueness_param_state_base_value M nS W mS T wReg tReg t i τ hF h0)
      (fun τ j hF h0 hj =>
        uniqueness_param_state_shift_value M nS W mS T wReg tReg t i j τ hF h0 hj)
  exact clauseWriterBounded_uniq_inner K S B M Jmax lvJ1 lvJ2 nC i (.const nC)
    (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg)
    (uniquenessParamPins1 wReg tReg W T t)
    (fun _ => (denseLayout nS W mS).state t i)
    (fun j => (denseLayout nS W mS).state t (i + 1 + j))
    hlvJ1le hlvJ2 hlvJ2le hJ hMB hSB hKB hKS hnCK h2S
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · unfold lvJ1 lvJ2; omega
      · exact (uniqueness_param_pins1_two Jmax wReg tReg W T t hplace p hp').2.2.2.1)
    (fun τ _ _ => by simp [ExprBoundedIn]; omega) (fun τ _ _ => by simp [Expr.eval])
    hbody2 hlits2

/-- The state-uniqueness `ClauseWriterBounded`, at depth 1 (`lvJ1`/`lvJ2`). -/
lemma clauseWriterBounded_uniq_state
    (M Jmax K S B nS W mS nC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hnCK : nC ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (.seq
        (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
        (loopProg lvJ1 (.const nC)
        (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqStateBaseEParam nS mS wReg)
                (uniqStateShiftEParam nS mS wReg))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ K S B ((2 + 2 * nC) + nC * (K * 6))
      (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ1Jmax : lvJ1 ≤ Jmax :=
    le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le
  have hb2 : ClauseWriterBounded (loopProg lvJ1 (.const nC)
      (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
          (leafProg wpJ lvJ2 (negPairLits (uniqStateBaseEParam nS mS wReg)
            (uniqStateShiftEParam nS mS wReg))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ K S B (nC * (K * 6)) (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) :=
    clauseWriterBounded_uniq_outer K S B M Jmax lvJ1 lvJ2 nC (.const nC)
      (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg)
      (fun i _ => (denseLayout nS W mS).state t i)
      (fun i j => (denseLayout nS W mS).state t (i + 1 + j))
      (uniquenessParamPins1 wReg tReg W T t) hlvJ1 hlvJ1le hlvJ1Jmax hMB hKB hKS hnCK
      (fun p hp => by
        have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
          (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
        exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩)
      (fun τ _ h0 => by simp [ExprBoundedIn]; omega) (fun τ _ h0 => by simp [Expr.eval])
      (fun i => uniq_state_inner_writer M Jmax nS W mS nC T wReg tReg t i hplace)
      (fun i => uniq_state_inner_bounded M Jmax K S B nS W mS nC T wReg tReg t i hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hnCK h2S)
  exact clauseWriterBounded_exactly_one_range K S B M Jmax lvJ1 lvJ2 nC (.const nC)
    (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg)
    ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
    (uniquenessParamPins1 wReg tReg W T t) (range_map_length nC _)
    (uniq_state_atLeastOne_writer M Jmax nS W mS nC T wReg tReg t hplace)
    (uniq_state_atLeastOne_bounded M Jmax K S B nS W mS nC T wReg tReg t hJ hK1 hwR hwR2 hMB
      henvB henvS hn hm hSB hKB hKS hnCK)
    hb2

/-! ## The head block (`lvJ1`/`lvJ2`, `ctlCell wReg`) -/

/-- `writeAtLeastOneProg`'s `ClauseWriterBounded`, for the head block's
run-time-width `atLeastOne` row (the count is `ctlCell wReg`, evaluating to `W`
by the pin). -/
lemma uniq_head_atLeastOne_bounded
    (M Jmax K S B nS W mS T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hWK : W ≤ K) :
    ClauseWriterBounded (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg)
        (uniqHeadBaseEParam nS mS wReg))
      M Jmax wpJ K S B (2 + 2 * W) (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  refine clauseWriterBounded_writeAtLeastOneProg K S B M Jmax lvJ1 W (ctlCell wReg)
    (uniqHeadBaseEParam nS mS wReg) (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
    hlvJ1 hlvJ1le hJ hMB hKB hKS hSB hWK ?_ ?_ ?_ ?_ ?_
  · intro τ hF h0
    exact exprBoundedIn_ctlCell B M wReg τ h0 (by omega)
  · intro τ hF h0
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [uniquenessParamPins1, uniquenessParamPins0]) hF h0
  · intro τ wp hF h0 hwp hsep
    have h1 : (writeReg (writeReg (writeReg τ (wp + 1) W) (M + wpJ) (wp + 2))
        (M + lvJ1) 0) 0 = M := by
      rw [writeReg_diff _ (M + lvJ1) 0 0 (by omega),
        writeReg_diff _ (M + wpJ) (wp + 2) 0 (by simp only [wpJ]; omega),
        writeReg_diff _ (wp + 1) W 0 (by omega), h0]
    exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega)
  · intro τ wp hF h0 hwp hsep
    have heval : (ctlCell wReg).eval τ = W :=
      ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins1,
        uniquenessParamPins0]) hF h0
    have h1 : (writeReg (writeReg (writeReg τ (wp + 1) W) (M + wpJ) (wp + 2))
        (M + lvJ1) 0) 0 = M := by
      rw [writeReg_diff _ (M + lvJ1) 0 0 (by omega),
        writeReg_diff _ (M + wpJ) (wp + 2) 0 (by simp only [wpJ]; omega),
        writeReg_diff _ (wp + 1) W 0 (by omega), h0]
    rw [ctlCell_eval, h1]
    rw [writeReg_diff _ (M + lvJ1) 0 (M + wReg) (by have := hplace.w_min; unfold lvJ1; omega),
      writeReg_diff _ (M + wpJ) (wp + 2) (M + wReg) (by unfold wpJ; omega),
      writeReg_diff _ (wp + 1) W (M + wReg) (by omega)]
    rw [ctlCell_eval, h0] at heval
    exact heval
  · intro τ h0 ht hst
    have g2 := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
    have g3 := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
    have gw := ht wReg hwR (by omega)
    exact ⟨exprBoundedIn_uniqHeadBaseEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
      (by omega) (by unfold UniqEnv at henvB; omega) hn hm,
      le_trans (uniqHeadBaseEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw)
        (by unfold UniqEnv at henvS; omega)⟩

/-- The head block's `writeAtLeastOneProg` correctness fact. -/
lemma uniq_head_atLeastOne_writer
    (M Jmax nS W mS T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      [atLeastOne ((List.range W).map fun p => (denseLayout nS W mS).head t p)] :=
  clauseWriter_atLeastOne M Jmax wpJ lvJ1 (ctlCell wReg)
    (uniqHeadBaseEParam nS mS wReg) (uniquenessParamPins1 wReg tReg W T t)
    ((List.range W).map fun p => (denseLayout nS W mS).head t p)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega)
    (fun p hp => by
      have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
        (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
      exact ⟨h1.1, h1.2.1, h1.2.2.2, h1.2.2.1⟩)
    (fun τ hF h0 => by
      rw [range_map_length]
      exact ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins1,
        uniquenessParamPins0]) hF h0)
    (fun σ1 σ2 h1 h2 hagree => by
      rw [ctlCell_eval, h1, ctlCell_eval, h2]
      exact hagree (M + wReg) (by have := hplace.w_le; omega)
        (by have := hplace.w_min; unfold wpJ; omega)
        (by have := hplace.w_min; unfold lvJ1; omega))
    (hdep_pins_to_bound M Jmax wpJ (uniqHeadBaseEParam nS mS wReg)
      (fun σ σ' hσ hσ' h => uniqueness_param_head_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h))
    (fun τ k hF h0 hk hklt => by
      rw [range_map_length] at hklt
      rw [range_map_getD W (fun p => (denseLayout nS W mS).head t p) k hklt]
      exact uniqueness_param_head_base_value M nS W mS T wReg tReg t k τ
        (pinsHold_cons M (lvJ1, k) (uniquenessParamPins1 wReg tReg W T t) τ hk hF) h0)

/-- The head block's inner-loop correctness fact for a fixed outer index `i`. -/
lemma uniq_head_inner_writer
    (M Jmax nS W mS T wReg tReg t i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
        (leafProg wpJ lvJ2 (negPairLits (uniqHeadBaseEParam nS mS wReg)
          (uniqHeadShiftEParam nS mS wReg))))
      M Jmax wpJ (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t))
      ((List.range (W - i - 1)).flatMap fun j =>
        [negPair ((denseLayout nS W mS).head t i)
          ((denseLayout nS W mS).head t (i + 1 + j))]) :=
  clause_writer_at_most_one_range_inner_count M Jmax wpJ lvJ1 lvJ2
    (uniquenessParamPins1 wReg tReg W T t) (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg)
    (uniqHeadShiftEParam nS mS wReg) W i ((denseLayout nS W mS).head t i)
    (fun j => (denseLayout nS W mS).head t (i + 1 + j))
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega) (by unfold lvJ2 wpJ; omega)
    (uniqueness_param_pins1_two Jmax wReg tReg W T t hplace)
    (fun τ hF h0 => ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins1,
      uniquenessParamPins0]) hF h0)
    (fun σ σ' hσ hσ' h => uniqueness_param_head_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_head_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ hF h0 => uniqueness_param_head_base_value M nS W mS T wReg tReg t i τ hF h0)
    (fun τ j hF h0 hj =>
      uniqueness_param_head_shift_value M nS W mS T wReg tReg t i j τ hF h0 hj)

/-- The head block's inner-loop `ClauseWriterBounded`, for a fixed outer
index `i`. -/
lemma uniq_head_inner_bounded
    (M Jmax K S B nS W mS T wReg tReg t i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hWK : W ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
        (leafProg wpJ lvJ2 (negPairLits (uniqHeadBaseEParam nS mS wReg)
          (uniqHeadShiftEParam nS mS wReg))))
      M Jmax wpJ K S B (K * 6)
      (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlits2 : LitsBounded K S B M (negPairLits (uniqHeadBaseEParam nS mS wReg)
      (uniqHeadShiftEParam nS mS wReg)) := litsBounded_uniq_head K S B M nS mS wReg
    hK1 hwR hwR2 hMB henvB henvS hn hm
  have hbody2 : ClauseLoopBody (leafProg wpJ lvJ2 (negPairLits
      (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg)))
      M Jmax wpJ lvJ2 (PinsHold M ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t))
      (fun j => [negPair ((denseLayout nS W mS).head t i)
        ((denseLayout nS W mS).head t (i + 1 + j))]) :=
    clauseLoopBody_negPair M Jmax wpJ lvJ2
      (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg)
      ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t)
      (fun _ => (denseLayout nS W mS).head t i)
      (fun j => (denseLayout nS W mS).head t (i + 1 + j))
      (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
      (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ2 wpJ; omega)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨by unfold lvJ1; omega, Nat.le_trans (by unfold lvJ1 ctlJmax; omega)
            hplace.ctl_le, by unfold lvJ1 lvJ2; omega, by unfold lvJ1 wpJ; omega⟩
        · have h := uniqueness_param_pins1_two Jmax wReg tReg W T t hplace p hp'
          exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      (fun σ σ' hσ hσ' h => uniqueness_param_head_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun σ σ' hσ hσ' h => uniqueness_param_head_shift_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun τ _ hF h0 _ => uniqueness_param_head_base_value M nS W mS T wReg tReg t i τ hF h0)
      (fun τ j hF h0 hj =>
        uniqueness_param_head_shift_value M nS W mS T wReg tReg t i j τ hF h0 hj)
  refine clauseWriterBounded_uniq_inner K S B M Jmax lvJ1 lvJ2 W i (ctlCell wReg)
    (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg)
    (uniquenessParamPins1 wReg tReg W T t)
    (fun _ => (denseLayout nS W mS).head t i)
    (fun j => (denseLayout nS W mS).head t (i + 1 + j))
    hlvJ1le hlvJ2 hlvJ2le hJ hMB hSB hKB hKS hWK h2S
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · unfold lvJ1 lvJ2; omega
      · exact (uniqueness_param_pins1_two Jmax wReg tReg W T t hplace p hp').2.2.2.1)
    ?_ ?_ hbody2 hlits2
  · intro τ hF h0
    have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
      unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
      rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
    exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega)
  · intro τ hF h0
    have h1 : ((ctlAssign lvJ2 (.const 0)).eval τ) 0 = M := by
      unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
      rw [writeReg_diff τ (M + lvJ2) 0 0 (by omega), h0]
    have hne2 : ∀ p ∈ ((lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t : List (ℕ × ℕ)),
        p.1 ≠ lvJ2 := fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · unfold lvJ1 lvJ2; omega
      · exact (uniqueness_param_pins1_two Jmax wReg tReg W T t hplace p hp').2.2.2.1
    have hev := pinsHold_reset M lvJ2 _ τ h0 hne2 hF
    exact ctlCell_eval_of_pin M _ wReg W _ (by simp [uniquenessParamPins1,
      uniquenessParamPins0]) hev h1

/-- The head-uniqueness `ClauseWriterBounded`, at depth 1 (`lvJ1`/`lvJ2`). -/
lemma clauseWriterBounded_uniq_head
    (M Jmax K S B nS W mS T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hWK : W ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (.seq
        (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
        (loopProg lvJ1 (ctlCell wReg)
        (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqHeadBaseEParam nS mS wReg)
                (uniqHeadShiftEParam nS mS wReg))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ K S B ((2 + 2 * W) + W * (K * 6))
      (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ1Jmax : lvJ1 ≤ Jmax :=
    le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le
  have hb2 : ClauseWriterBounded (loopProg lvJ1 (ctlCell wReg)
      (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
          (leafProg wpJ lvJ2 (negPairLits (uniqHeadBaseEParam nS mS wReg)
            (uniqHeadShiftEParam nS mS wReg))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ K S B (W * (K * 6)) (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
    refine clauseWriterBounded_uniq_outer K S B M Jmax lvJ1 lvJ2 W (ctlCell wReg)
      (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg)
      (fun i _ => (denseLayout nS W mS).head t i)
      (fun i j => (denseLayout nS W mS).head t (i + 1 + j))
      (uniquenessParamPins1 wReg tReg W T t) hlvJ1 hlvJ1le hlvJ1Jmax hMB hKB hKS hWK
      (fun p hp => by
        have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
          (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
        exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩)
      ?_ ?_
      (fun i => uniq_head_inner_writer M Jmax nS W mS T wReg tReg t i hplace)
      (fun i => uniq_head_inner_bounded M Jmax K S B nS W mS T wReg tReg t i hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hWK h2S)
    · intro τ hF h0
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega)
    · intro τ hF h0
      have hne1 : ∀ p ∈ uniquenessParamPins1 wReg tReg W T t, p.1 ≠ lvJ1 := fun p hp =>
        (uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
          (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp).2.2.1
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      have hev := pinsHold_reset M lvJ1 _ τ h0 hne1 hF
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [uniquenessParamPins1,
        uniquenessParamPins0]) hev h1
  exact clauseWriterBounded_exactly_one_range K S B M Jmax lvJ1 lvJ2 W (ctlCell wReg)
    (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg)
    ((List.range W).map fun p => (denseLayout nS W mS).head t p)
    (uniquenessParamPins1 wReg tReg W T t) (range_map_length W _)
    (uniq_head_atLeastOne_writer M Jmax nS W mS T wReg tReg t hplace)
    (uniq_head_atLeastOne_bounded M Jmax K S B nS W mS T wReg tReg t hplace hJ hK1 hwR hwR2 hMB
      henvB henvS hn hm hSB hKB hKS hWK)
    hb2

/-! ## The cell block (`lvJ2`/`lvJ3`, `.const mC`, pinned on `p`) -/

/-- Shared pin facts for the cell block, at depth 2 (`lvJ2`/`lvJ3`, pinned on
`p` at `lvJ1`). -/
lemma uniqueness_param_pins2_two (Jmax wReg tReg W T t p : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ∀ q ∈ uniquenessParamPins2 wReg tReg W T t p,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ2 ∧ q.1 ≠ lvJ3 ∧ q.1 ≠ wpJ := by
  intro q hq
  have h2 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ2 hplace
    (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
    (by unfold lvJ1 lvJ2; omega) q hq
  have h3 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ3 hplace
    (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
    (by unfold lvJ1 lvJ3; omega) q hq
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h3.2.2.1, h2.2.2.2⟩

/-- `writeAtLeastOneProg`'s `ClauseWriterBounded`, for the cell block's
run-time-width `atLeastOne` row. -/
lemma uniq_cell_atLeastOne_bounded
    (M Jmax K S B nS W mS mC T wReg tReg t p : ℕ) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) :
    ClauseWriterBounded (writeAtLeastOneProg wpJ lvJ2 (.const mC)
        (uniqCellBaseEParam nS mS wReg))
      M Jmax wpJ K S B (2 + 2 * mC)
      (PinsHold M (uniquenessParamPins2 wReg tReg W T t p)) := by
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  refine clauseWriterBounded_writeAtLeastOneProg K S B M Jmax lvJ2 mC (.const mC)
    (uniqCellBaseEParam nS mS wReg) (PinsHold M (uniquenessParamPins2 wReg tReg W T t p))
    hlvJ2 hlvJ2le hJ hMB hKB hKS hSB hmCK ?_ ?_ ?_ ?_ ?_
  · intro τ _ _; simp [ExprBoundedIn]; omega
  · intro τ _ _; simp [Expr.eval]
  · intro τ wp _ _ _ _; simp [ExprBoundedIn]; omega
  · intro τ wp _ _ _ _; simp [Expr.eval]
  · intro τ h0 ht hst
    have g2 := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
    have g3 := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
    have g4 := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
    have gw := ht wReg hwR (by omega)
    exact ⟨exprBoundedIn_uniqCellBaseEParam M K B nS mS wReg τ hK1 h0 g2 g3 g4 gw hwR2
      (by omega) (by unfold UniqEnv at henvB; omega) hn hm,
      le_trans (uniqCellBaseEParam_eval_le M K nS mS wReg τ h0 g2 g3 g4 gw)
        (by unfold UniqEnv at henvS; omega)⟩

/-- The cell block's `writeAtLeastOneProg` correctness fact. -/
lemma uniq_cell_atLeastOne_writer
    (M Jmax nS W mS mC T wReg tReg t p : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
      M Jmax wpJ (PinsHold M (uniquenessParamPins2 wReg tReg W T t p))
      [atLeastOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)] :=
  clauseWriter_atLeastOne M Jmax wpJ lvJ2 (.const mC)
    (uniqCellBaseEParam nS mS wReg) (uniquenessParamPins2 wReg tReg W T t p)
    ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 wpJ; omega)
    (fun q hq => by
      have h2 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ2 hplace
        (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
        (by unfold lvJ1 lvJ2; omega) q hq
      exact ⟨h2.1, h2.2.1, h2.2.2.2, h2.2.2.1⟩)
    (fun τ _ _ => by rw [range_map_length]; simp [Expr.eval])
    (fun σ1 σ2 _ _ _ => rfl)
    (hdep_pins_to_bound M Jmax wpJ (uniqCellBaseEParam nS mS wReg)
      (fun σ σ' hσ hσ' h => uniqueness_param_cell_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h))
    (fun τ k hF h0 hk hklt => by
      rw [range_map_length] at hklt
      rw [range_map_getD mC (fun a => (denseLayout nS W mS).cell t p a) k hklt]
      exact uniqueness_param_cell_base_value M nS W mS T wReg tReg t p k τ
        (pinsHold_cons M (lvJ2, k) (uniquenessParamPins2 wReg tReg W T t p) τ hk hF) h0)

/-- The cell block's inner-loop correctness fact for a fixed outer index `i`. -/
lemma uniq_cell_inner_writer
    (M Jmax nS W mS mC T wReg tReg t p i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
        (leafProg wpJ lvJ3 (negPairLits (uniqCellBaseEParam nS mS wReg)
          (uniqCellShiftEParam nS mS wReg))))
      M Jmax wpJ (PinsHold M ((lvJ2, i) :: uniquenessParamPins2 wReg tReg W T t p))
      ((List.range (mC - i - 1)).flatMap fun j =>
        [negPair ((denseLayout nS W mS).cell t p i)
          ((denseLayout nS W mS).cell t p (i + 1 + j))]) :=
  clause_writer_at_most_one_range_inner_count M Jmax wpJ lvJ2 lvJ3
    (uniquenessParamPins2 wReg tReg W T t p) (.const mC) (uniqCellBaseEParam nS mS wReg)
    (uniqCellShiftEParam nS mS wReg) mC i ((denseLayout nS W mS).cell t p i)
    (fun j => (denseLayout nS W mS).cell t p (i + 1 + j))
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3; omega) (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 lvJ3; omega) (by unfold lvJ2 wpJ; omega) (by unfold lvJ3 wpJ; omega)
    (uniqueness_param_pins2_two Jmax wReg tReg W T t p hplace)
    (fun τ hF h0 => by simp [Expr.eval])
    (fun σ σ' hσ hσ' h => uniqueness_param_cell_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_cell_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ hF h0 => uniqueness_param_cell_base_value M nS W mS T wReg tReg t p i τ hF h0)
    (fun τ j hF h0 hj =>
      uniqueness_param_cell_shift_value M nS W mS T wReg tReg t p i j τ hF h0 hj)

/-- The cell block's inner-loop `ClauseWriterBounded`, for a fixed outer
index `i`. -/
lemma uniq_cell_inner_bounded
    (M Jmax K S B nS W mS mC T wReg tReg t p i : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
        (leafProg wpJ lvJ3 (negPairLits (uniqCellBaseEParam nS mS wReg)
          (uniqCellShiftEParam nS mS wReg))))
      M Jmax wpJ K S B (K * 6)
      (PinsHold M ((lvJ2, i) :: uniquenessParamPins2 wReg tReg W T t p)) := by
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlvJ3 : 2 ≤ lvJ3 := by unfold lvJ3; omega
  have hlvJ3le : lvJ3 ≤ 24 := by unfold lvJ3; omega
  have hlits2 : LitsBounded K S B M (negPairLits (uniqCellBaseEParam nS mS wReg)
      (uniqCellShiftEParam nS mS wReg)) := litsBounded_uniq_cell K S B M nS mS wReg
    hK1 hwR hwR2 hMB henvB henvS hn hm
  have hbody2 : ClauseLoopBody (leafProg wpJ lvJ3 (negPairLits
      (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg)))
      M Jmax wpJ lvJ3 (PinsHold M ((lvJ2, i) :: uniquenessParamPins2 wReg tReg W T t p))
      (fun j => [negPair ((denseLayout nS W mS).cell t p i)
        ((denseLayout nS W mS).cell t p (i + 1 + j))]) :=
    clauseLoopBody_negPair M Jmax wpJ lvJ3
      (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg)
      ((lvJ2, i) :: uniquenessParamPins2 wReg tReg W T t p)
      (fun _ => (denseLayout nS W mS).cell t p i)
      (fun j => (denseLayout nS W mS).cell t p (i + 1 + j))
      (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
      (by unfold lvJ3; omega) (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ3 wpJ; omega)
      (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ⟨by unfold lvJ2; omega, Nat.le_trans (by unfold lvJ2 ctlJmax; omega)
            hplace.ctl_le, by unfold lvJ2 lvJ3; omega, by unfold lvJ2 wpJ; omega⟩
        · have h := uniqueness_param_pins2_two Jmax wReg tReg W T t p hplace q hq'
          exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      (fun σ σ' hσ hσ' h => uniqueness_param_cell_base_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun σ σ' hσ hσ' h => uniqueness_param_cell_shift_frame M Jmax nS mS wReg tReg
        hplace σ σ' hσ hσ' h)
      (fun τ _ hF h0 _ => uniqueness_param_cell_base_value M nS W mS T wReg tReg t p i τ hF h0)
      (fun τ j hF h0 hj =>
        uniqueness_param_cell_shift_value M nS W mS T wReg tReg t p i j τ hF h0 hj)
  exact clauseWriterBounded_uniq_inner K S B M Jmax lvJ2 lvJ3 mC i (.const mC)
    (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg)
    (uniquenessParamPins2 wReg tReg W T t p)
    (fun _ => (denseLayout nS W mS).cell t p i)
    (fun j => (denseLayout nS W mS).cell t p (i + 1 + j))
    hlvJ2le hlvJ3 hlvJ3le hJ hMB hSB hKB hKS hmCK h2S
    (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq'
      · unfold lvJ2 lvJ3; omega
      · exact (uniqueness_param_pins2_two Jmax wReg tReg W T t p hplace q hq').2.2.2.1)
    (fun τ _ _ => by simp [ExprBoundedIn]; omega) (fun τ _ _ => by simp [Expr.eval])
    hbody2 hlits2

/-- The cell-uniqueness `ClauseWriterBounded`, at depth 2 (`lvJ2`/`lvJ3`),
for one fixed cell position `p`. -/
lemma clauseWriterBounded_uniq_cell
    (M Jmax K S B nS W mS mC T wReg tReg t p : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (.seq
        (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
        (loopProg lvJ2 (.const mC)
        (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
            (leafProg wpJ lvJ3
              (negPairLits (uniqCellBaseEParam nS mS wReg)
                (uniqCellShiftEParam nS mS wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
      M Jmax wpJ K S B ((2 + 2 * mC) + mC * (K * 6))
      (PinsHold M (uniquenessParamPins2 wReg tReg W T t p)) := by
  have hlvJ2 : 2 ≤ lvJ2 := by unfold lvJ2; omega
  have hlvJ2le : lvJ2 ≤ 24 := by unfold lvJ2; omega
  have hlvJ2Jmax : lvJ2 ≤ Jmax :=
    le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le
  have hb2 : ClauseWriterBounded (loopProg lvJ2 (.const mC)
      (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
          (leafProg wpJ lvJ3 (negPairLits (uniqCellBaseEParam nS mS wReg)
            (uniqCellShiftEParam nS mS wReg))))
        (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ K S B (mC * (K * 6)) (PinsHold M (uniquenessParamPins2 wReg tReg W T t p)) :=
    clauseWriterBounded_uniq_outer K S B M Jmax lvJ2 lvJ3 mC (.const mC)
      (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg)
      (fun i _ => (denseLayout nS W mS).cell t p i)
      (fun i j => (denseLayout nS W mS).cell t p (i + 1 + j))
      (uniquenessParamPins2 wReg tReg W T t p) hlvJ2 hlvJ2le hlvJ2Jmax hMB hKB hKS hmCK
      (fun q hq => by
        have h2 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ2 hplace
          (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
          (by unfold lvJ1 lvJ2; omega) q hq
        exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩)
      (fun τ _ h0 => by simp [ExprBoundedIn]; omega) (fun τ _ h0 => by simp [Expr.eval])
      (fun i => uniq_cell_inner_writer M Jmax nS W mS mC T wReg tReg t p i hplace)
      (fun i => uniq_cell_inner_bounded M Jmax K S B nS W mS mC T wReg tReg t p i hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h2S)
  exact clauseWriterBounded_exactly_one_range K S B M Jmax lvJ2 lvJ3 mC (.const mC)
    (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg)
    ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)
    (uniquenessParamPins2 wReg tReg W T t p) (range_map_length mC _)
    (uniq_cell_atLeastOne_writer M Jmax nS W mS mC T wReg tReg t p hplace)
    (uniq_cell_atLeastOne_bounded M Jmax K S B nS W mS mC T wReg tReg t p hJ hK1 hwR hwR2 hMB
      henvB henvS hn hm hSB hKB hKS hmCK)
    hb2

/-- The `p`-loop wrapping the cell block: `loopProg lvJ1 (ctlCell wReg) (.seq
cellBlock bump)`, packaged as `ClauseWriterBounded`.  `W` iterations of the
cell block's own width `(2 + 2*mC) + mC*(K*6)`. -/
lemma clauseWriterBounded_uniq_cell_p_loop
    (M Jmax K S B nS W mS mC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hmCK : mC ≤ K) (hWK : W ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
            (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseEParam nS mS wReg)
                    (uniqCellShiftEParam nS mS wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ K S B (W * ((2 + 2 * mC) + mC * (K * 6)))
      (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) := by
  have hlvJ1 : 2 ≤ lvJ1 := by unfold lvJ1; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  have hlvJ1Jmax : lvJ1 ≤ Jmax :=
    le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le
  have hpin1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
    (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega)
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ1 W ((2 + 2 * mC) + mC * (K * 6))
    (ctlCell wReg) _ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
    (fun p => exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a))
    hlvJ1 hlvJ1le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ1 _ τ h0 (fun q hq => (hpin1 q hq).2.2.1) hF)
    (fun p _ => exactlyOne_width_le K mC (fun a => (denseLayout nS W mS).cell t p a) hmCK)
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ1
      (uniquenessParamPins1 wReg tReg W T t) _ (by unfold lvJ1; omega) hlvJ1Jmax
      (by unfold lvJ1 wpJ; omega) hpin1
      (fun p => uniq_cell_writer_param M Jmax nS W mS mC T wReg tReg t p hplace))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ1 K S B W
      ((2 + 2 * mC) + mC * (K * 6)) (uniquenessParamPins1 wReg tReg W T t) _
      hlvJ1 hlvJ1le hMB hKS (by omega) hWK
      (fun p => uniq_cell_writer_param M Jmax nS W mS mC T wReg tReg t p hplace)
      (fun p => clauseWriterBounded_uniq_cell M Jmax K S B nS W mS mC T wReg tReg t p hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK h2S))
    (fun τ hF h0 => by
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ1 _ τ h0 (fun q hq => (hpin1 q hq).2.2.1) hF
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [uniquenessParamPins1,
        uniquenessParamPins0]) hev h1)

/-! ## Level 0: the `t` level and the whole family -/

/-- Level 0's body (before the `lvJ0` bump): state block, head block, cell
`p`-loop, joined by `.seq`, as a `ClauseWriterBounded`. -/
lemma clauseWriterBounded_uniq_t
    (M Jmax K S B nS W mS nC mC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hnCK : nC ≤ K) (hmCK : mC ≤ K) (hWK : W ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (.seq (.seq
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
          (loopProg lvJ1 (.const nC)
          (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqStateBaseEParam nS mS wReg)
                  (uniqStateShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
          (loopProg lvJ1 (ctlCell wReg)
          (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqHeadBaseEParam nS mS wReg)
                  (uniqHeadShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
        (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
            (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseEParam nS mS wReg)
                    (uniqCellShiftEParam nS mS wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ K S B
      (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * mC) + mC * (K * 6)))
      (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) :=
  clauseWriterBounded_seq _ _ M Jmax wpJ K S B
    (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6)))
    (W * ((2 + 2 * mC) + mC * (K * 6)))
    (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
    (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
      ++ exactlyOne ((List.range W).map fun p => (denseLayout nS W mS).head t p))
    (clauseWriter_seq _ _ M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) _ _
      (uniq_state_writer_param M Jmax nS W mS nC T wReg tReg t hplace)
      (uniq_head_writer_param M Jmax nS W mS T wReg tReg t hplace))
    (by
      rw [rowTableWidth_append_total]
      gcongr
      · exact exactlyOne_width_le K nC (fun q => (denseLayout nS W mS).state t q) hnCK
      · exact exactlyOne_width_le K W (fun p => (denseLayout nS W mS).head t p) hWK)
    (clauseWriterBounded_seq _ _ M Jmax wpJ K S B ((2 + 2 * nC) + nC * (K * 6))
      ((2 + 2 * W) + W * (K * 6)) (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q))
      (uniq_state_writer_param M Jmax nS W mS nC T wReg tReg t hplace)
      (exactlyOne_width_le K nC (fun q => (denseLayout nS W mS).state t q) hnCK)
      (clauseWriterBounded_uniq_state M Jmax K S B nS W mS nC T wReg tReg t hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hnCK h2S)
      (clauseWriterBounded_uniq_head M Jmax K S B nS W mS T wReg tReg t hplace hJ
        hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hWK h2S))
    (clauseWriterBounded_uniq_cell_p_loop M Jmax K S B nS W mS mC T wReg tReg t hplace hJ
      hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hmCK hWK h2S)

/-- The full uniqueness family, as a `ClauseWriterBounded`.  `hTK1` (`T + 1 ≤
K`) mirrors persist's: the outermost trip count is `T + 1`, so the last
iteration's counter bump must clear `K`. -/
lemma clauseWriterBounded_uniquenessFamilyProgParam
    (K S B M Jmax nS W mS nC mC T wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hJ : 24 ≤ Jmax)
    (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : UniqEnv K B nS mS) (henvS : UniqEnv K S nS mS) (hn : nS ≤ B) (hm : mS ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hnCK : nC ≤ K) (hmCK : mC ≤ K) (hWK : W ≤ K) (h2S : 2 ≤ S)
    (hTK1 : T + 1 ≤ K) :
    ClauseWriterBounded (uniquenessFamilyProgParam nS mS nC mC wReg tReg) M Jmax wpJ K S B
      ((T + 1) * (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * mC) + mC * (K * 6))))
      (PinsHold M [(wReg, W), (tReg, T)]) := by
  unfold uniquenessFamilyProgParam
  have hlvJ0 : 2 ≤ lvJ0 := by unfold lvJ0; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  have hne0 : ∀ p ∈ ([(wReg, W), (tReg, T)] : List (ℕ × ℕ)), p.1 ≠ lvJ0 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have := hplace.w_min; unfold lvJ0; omega
    · have := hplace.t_min; unfold lvJ0; omega
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 (T + 1)
    (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
      + W * ((2 + 2 * mC) + mC * (K * 6)))
    (.add (ctlCell tReg) (.const 1)) _
    (PinsHold M [(wReg, W), (tReg, T)])
    (fun t => exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
      ++ exactlyOne ((List.range W).map fun p => (denseLayout nS W mS).head t p)
      ++ (List.range W).flatMap fun p =>
        exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a))
    hlvJ0 hlvJ0le hMB
    (fun τ hF h0 => pinsHold_reset M lvJ0 _ τ h0 hne0 hF)
    (fun t _ => by
      rw [rowTableWidth_append_total, rowTableWidth_append_total]
      gcongr
      · exact exactlyOne_width_le K nC (fun q => (denseLayout nS W mS).state t q) hnCK
      · exact exactlyOne_width_le K W (fun p => (denseLayout nS W mS).head t p) hWK
      · exact rowTableWidth_flatMap_range_le
          (fun p => exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a))
          ((2 + 2 * mC) + mC * (K * 6)) W
          (fun p _ => exactlyOne_width_le K mC (fun a => (denseLayout nS W mS).cell t p a) hmCK))
    (clauseLoopBody_of_writer _ M Jmax wpJ lvJ0 [(wReg, W), (tReg, T)] _
      (by omega) (le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega)
      (uniqueness_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace
        (by unfold lvJ0 ctlJmax; omega))
      (fun t => uniq_t_fixed_writer_param M Jmax nS W mS nC mC T wReg tReg t hplace))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded _ M Jmax wpJ lvJ0 K S B (T + 1)
      (((2 + 2 * nC) + nC * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * mC) + mC * (K * 6))) [(wReg, W), (tReg, T)] _
      hlvJ0 hlvJ0le hMB hKS (by omega) (by omega)
      (fun t => uniq_t_fixed_writer_param M Jmax nS W mS nC mC T wReg tReg t hplace)
      (fun t => clauseWriterBounded_uniq_t M Jmax K S B nS W mS nC mC T wReg tReg t
        hplace hJ hK1 hwR hwR2 hMB henvB henvS hn hm hSB hKB hKS hnCK hmCK hWK h2S))
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ0 _ τ h0 hne0 hF
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by omega), h0]
      have hT : (ctlCell tReg).eval ((ctlAssign lvJ0 (.const 0)).eval τ) = T :=
        ctlCell_eval_of_pin M _ tReg T _ (by simp) hev h1
      refine ⟨exprBoundedIn_ctlCell B M tReg _ h1 (by omega), by simp [ExprBoundedIn]; omega, ?_⟩
      simp only [Expr.eval, hT]; omega)
    (fun τ hF h0 => by
      have hev := pinsHold_reset M lvJ0 _ τ h0 hne0 hF
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by omega), h0]
      have hT : (ctlCell tReg).eval ((ctlAssign lvJ0 (.const 0)).eval τ) = T :=
        ctlCell_eval_of_pin M _ tReg T _ (by simp) hev h1
      simp only [Expr.eval, hT])

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Verifier.ThreeCNFEval
public import NPComplete.CookLevin.Verifier.ClauseEvalWLoop
public import NPComplete.CookLevin.Verifier.ClauseEvalBounded
public import NPComplete.BoundedWhile.Frame

/-!
`ProgramBoundedIn`/frame facts for `decodeThreeClauseEvalStepAt` and its AND-fold wrapper
`decodeThreeCNFEvalClauseStepAt`, at the single-clause-step level.  The fixed-arity literal loop
(`.forN (.const 3) …`) makes these a `k := 3` special case of `ClauseEvalWLoop.lean`'s
generic-in-`k` facts about `decodeClauseEvalStepAt`, so no length-prefix decode bound machinery
(`decodeClauseWithLengthPrefixAt_remaining_le` and friends, needed by `CNFEvalOuterBounded.lean`
for the unbounded-width `Clause` case) is needed here.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)

/-- Growth bound for one `decodeThreeClauseEvalStepAt` step: the fixed-arity literal loop runs
    exactly `3` times (`remainingReg` is unconditionally seeded to `3`), so the cursor advances
    by at most `3 * (boundReg + 1)`. -/
lemma decodeThreeClauseEvalStepAt_one_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) :
    (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg).eval σ cursorReg ≤ σ cursorReg + 3 * (σ boundReg + 1) := by
  unfold decodeThreeClauseEvalStepAt
  rw [eval_seq, eval_seq, eval_forN]
  set σ0 := (Program.assign remainingReg (.const 3)).eval σ with hσ0def
  have h0cur : σ0 cursorReg = σ cursorReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ remainingReg 3 cursorReg hrc.symm
  have h0bnd : σ0 boundReg = σ boundReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ remainingReg 3 boundReg hbr
  set σ1 := (Program.assign satReg (.const 0)).eval σ0 with hσ1def
  have h1cur : σ1 cursorReg = σ0 cursorReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 cursorReg hcsat
  have h1bnd : σ1 boundReg = σ0 boundReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 boundReg hbs
  simp only [Expr.eval]
  have hloop := decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg boundReg 3 σ1
    hcp hcv hcd hrc hcbit hcval hcsat hbc hbp hbv hbd hbr hbb hbval hbs
  rw [h1cur, h0cur, h1bnd, h0bnd] at hloop
  exact hloop

/-- `ProgramBoundedIn` for `decodeThreeClauseEvalStepAt` from just `StoreValuesLe B σ` and a
    cursor/`wBaseReg` budget large enough for the `3`-step fixed-arity literal loop. Mirrors
    `programBoundedIn_decodeCNFEvalClauseStepAt_of_store_bounds`, at the `n := 3` special case
    of `ClauseEvalWLoop.lean`'s generic-in-`k` facts. -/
lemma programBoundedIn_decodeThreeClauseEvalStepAt_of_store_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store) (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbitw : bitReg ≠ wBaseReg)
    (hvw2 : valReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ boundReg ∧ satReg ≠ wBaseReg)
    (h3 : (3:ℕ) ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (hinner : σ cursorReg + 3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  rcases hsatFrame with ⟨hsc, hsd, hsr, hsb, hsw⟩
  have hB1 : 1 ≤ B := by omega
  unfold decodeThreeClauseEvalStepAt
  refine ⟨⟨hri, h3⟩, ?_⟩
  set σ0 := (Program.assign remainingReg (.const 3)).eval σ with hσ0def
  have hσ0cur : σ0 cursorReg = σ cursorReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ remainingReg 3 cursorReg hrc.symm
  have hσ0bnd : σ0 boundReg = σ boundReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ remainingReg 3 boundReg hbr
  have hσ0w : σ0 wBaseReg = σ wBaseReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ remainingReg 3 wBaseReg hrw.symm
  have hσ0Le : StoreValuesLe B σ0 := by
    apply storeValuesLe_assign hσ; simp only [Expr.eval]; omega
  refine ⟨⟨hsi, by simp [ExprBoundedIn]⟩, ?_⟩
  set σ1 := (Program.assign satReg (.const 0)).eval σ0 with hσ1def
  have hσ1cur : σ1 cursorReg = σ0 cursorReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 cursorReg hsc.symm
  have hσ1bnd : σ1 boundReg = σ0 boundReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 boundReg hsb.symm
  have hσ1w : σ1 wBaseReg = σ0 wBaseReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 wBaseReg hsw.symm
  have hσ1Le : StoreValuesLe B σ1 := by
    apply storeValuesLe_assign hσ0Le; simp only [Expr.eval]; omega
  show ExprBoundedIn B σ1 (.const 3) ∧
    ∀ m' < (3:ℕ), ProgramBoundedIn B
      (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg) m' σ1)
      (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg boundReg)
  refine ⟨h3, ?_⟩
  intro m hm
  have hBndEq : σ1 boundReg = σ boundReg := by rw [hσ1bnd, hσ0bnd]
  have hσ1wbase : σ1 wBaseReg = σ wBaseReg := by rw [hσ1w, hσ0w]
  have hσ1curEq : σ1 cursorReg = σ cursorReg := by rw [hσ1cur, hσ0cur]
  have hσm := storeValuesLe_decodeClauseEvalStepAt_loop_of_bounds B cursorReg polReg varReg
    doneReg remainingReg satReg bitReg valReg wBaseReg boundReg m 3 σ1 hB1
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
    hrc hcbit hcval hsc.symm hbr hbb hbval hsb.symm
    hcw hpw hvw hdw hrw hbitw hvw2 hsw hrv hσ1Le
    (by rw [hσ1curEq, hBndEq]; omega)
    (by rw [hσ1wbase, hBndEq]; exact hwbudget) (le_of_lt hm)
  have hcurm := decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg boundReg m σ1
    hcp hcv hcd hrc hcbit hcval hsc.symm hbc hbp hbv hbd hbr hbb hbval hsb.symm
  have hbndm : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg boundReg) m σ1) boundReg = σ1 boundReg :=
    decodeClauseEvalStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg boundReg m σ1 hbc hbp hbv hbd hbr hsb.symm hbb hbval
  have hwbaseM : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg boundReg) m σ1) wBaseReg = σ1 wBaseReg :=
    decodeClauseEvalStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg boundReg m σ1 hcw hpw hvw hdw hrw hbitw hvw2 hsw
  have hmle3 : m ≤ 3 := by omega
  have hmprod : m * (σ1 boundReg + 1) ≤ 3 * (σ1 boundReg + 1) := Nat.mul_le_mul_right _ hmle3
  apply programBoundedIn_decodeClauseEvalStepAt_of_store_bounds B cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg boundReg _ hσm
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
    hcw hpw hvw hdw hrw hrv
  · rw [hbndm]
    have := hcurm
    omega
  · rw [hwbaseM, hbndm, hσ1wbase, hBndEq]; exact hwbudget

/-- `decodeThreeCNFEvalClauseStepAt`'s cursor growth from one clause step, chaining
    `decodeThreeClauseEvalStepAt_one_cursor_le` through the (frame-only) AND-fold. -/
lemma decodeThreeCNFEvalClauseStepAt_one_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hck : cursorReg ≠ cnfReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) :
    (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg cnfReg boundReg).eval σ cursorReg ≤ σ cursorReg + 3 * (σ boundReg + 1) := by
  unfold decodeThreeCNFEvalClauseStepAt
  rw [eval_seq]
  have hstep := decodeThreeClauseEvalStepAt_one_cursor_le cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg boundReg σ hcp hcv hcd hrc hcbit hcval hcsat
    hbc hbp hbv hbd hbr hbb hbval hbs
  rw [andIntoProg_frame satReg cnfReg cursorReg _ hck]
  exact hstep

lemma decodeThreeCNFEvalClauseStepAt_avoids_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) :
    (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg cnfReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ satReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧ r ≠ cnfReg) := by
  simp [Program.Avoids, decodeThreeCNFEvalClauseStepAt, decodeThreeClauseEvalStepAt,
    andIntoProg, decodeClauseEvalStepAt, decodeLiteralValueProgramAt,
    decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg, readAssignBitProg,
    literalValueProg, orIntoProg]

/-- `ProgramBoundedIn` for `decodeThreeCNFEvalClauseStepAt`: the single-clause eval
    (`programBoundedIn_decodeThreeClauseEvalStepAt_of_store_bounds`) followed by the
    trivially-bounded AND-accumulator step. -/
lemma programBoundedIn_decodeThreeCNFEvalClauseStepAt_of_store_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) (σ : Store) (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbitw : bitReg ≠ wBaseReg)
    (hvw2 : valReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ boundReg ∧ satReg ≠ wBaseReg)
    (h3 : (3:ℕ) ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (hinner : σ cursorReg + 3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) := by
  have hclause := programBoundedIn_decodeThreeClauseEvalStepAt_of_store_bounds B cursorReg
    polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg σ hσ
    ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2.1, hidx.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.2.2.2⟩
    hdist hrc hcbit hcval hbr hbb hbval hcw hpw hvw hdw hrw hbitw hvw2 hrv
    hsatFrame h3 hwbudget hinner
  unfold decodeThreeCNFEvalClauseStepAt
  refine ⟨hclause, programBoundedIn_andIntoProg B satReg cnfReg _ hidx.2.2.2.2.2.1
    hidx.2.2.2.2.2.2.2.2.2.1⟩

end NPComplete.CookLevin

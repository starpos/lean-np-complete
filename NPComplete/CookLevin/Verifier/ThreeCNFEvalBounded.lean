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
end NPComplete.CookLevin

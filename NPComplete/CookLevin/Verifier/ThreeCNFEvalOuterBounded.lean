module

public import NPComplete.CookLevin.Verifier.ThreeCNFEvalBounded
public import NPComplete.CookLevin.Verifier.CNFEvalOuterBounded
public import NPComplete.BoundedWhile.Frame

/-!
Frame and growth facts for iterating `decodeThreeCNFEvalClauseStepAt` across a clause list,
one abstraction level up from `ThreeCNFEvalBounded.lean`'s single-clause-step facts. The
per-step cursor growth is the fixed `3 * (boundReg + 1)` (from `ThreeCNFEvalBounded.lean`'s
constant-arity bound) rather than `1 + boundReg + boundReg * (boundReg + 1)` (length-prefix
decode plus a register-bound literal loop), so the coarse-budget arithmetic is
correspondingly simpler.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ loopEval_succ_snoc eval_assignInd eval_skip)

lemma scanFree_decodeThreeCNFEvalClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) :
    ScanFree (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg) := by
  unfold decodeThreeCNFEvalClauseStepAt
  refine ⟨?_, scanFree_andIntoProg satReg cnfReg⟩
  unfold decodeThreeClauseEvalStepAt
  exact ⟨trivial, trivial, scanFree_decodeClauseEvalStepAt cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg boundReg⟩

/-- `decodeThreeCNFEvalClauseStepAt` never disturbs `boundReg`, iterated any number of times. -/
lemma decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg k : ℕ) (σ : Store)
    (hbr : boundReg ≠ remainingReg) (hbs : boundReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) (hbk : boundReg ≠ cnfReg) :
    loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg) k σ boundReg = σ boundReg := by
  exact (decodeThreeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg).loopEval_frame
    ⟨hbc, hbp, hbv, hbd, hbr, hbs, hbb, hbval, hbk⟩ k σ

/-- `decodeThreeCNFEvalClauseStepAt` never disturbs `wBaseReg`, iterated any number of times. -/
lemma decodeThreeCNFEvalClauseStepAt_loopEval_wBase_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg k : ℕ) (σ : Store)
    (hrw : remainingReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hbitw : bitReg ≠ wBaseReg) (hvw2 : valReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) :
    loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg) k σ wBaseReg = σ wBaseReg := by
  exact (decodeThreeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg).loopEval_frame
    ⟨hcw.symm, hpw.symm, hvw.symm, hdw.symm, hrw.symm, hsw.symm, hbitw.symm,
      hvw2.symm, hkw.symm⟩ k σ

/-- Growth bound for iterating `decodeThreeCNFEvalClauseStepAt`: after `k` steps the cursor
    has advanced by at most `k * (3 * (σ boundReg + 1))`. -/
lemma decodeThreeCNFEvalClauseStepAt_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg k : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hck : cursorReg ≠ cnfReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg) :
    (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg) k σ) cursorReg ≤
      σ cursorReg + k * (3 * (σ boundReg + 1)) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ_snoc]
      set τ := loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) k σ with hτdef
      have hstep := decodeThreeCNFEvalClauseStepAt_one_cursor_le cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg τ
        hcp hcv hcd hrc hcbit hcval hcsat hck hbc hbp hbv hbd hbr hbb hbval hbs
      have hbnd : τ boundReg = σ boundReg := by
        rw [hτdef]
        exact decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg
          doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg k σ
          hbr hbs hbc hbp hbv hbd hbb hbval hbk
      have hik := ih σ
      rw [← hτdef] at hik
      rw [hbnd] at hstep
      have hmul : (k + 1) * (3 * (σ boundReg + 1)) =
          k * (3 * (σ boundReg + 1)) + 3 * (σ boundReg + 1) := by ring
      omega
end NPComplete.CookLevin

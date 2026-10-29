module

public import NPComplete.CookLevin.Verifier.ClauseEvalBounded
public import NPComplete.BoundedWhile.Frame

/-!
# Clause-evaluator loop bounds

Clause evaluation scans a sequence of literals, so its cursor and frame
invariants must hold across repeated iterations rather than one literal at a
time. This module lifts bounded one-step evaluation facts to the loop contracts
used by outer CNF evaluation.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ loopEval_succ_snoc eval_assignInd eval_skip)

lemma scanFree_orIntoProg (valReg satReg : ℕ) :
    ScanFree (orIntoProg valReg satReg) := by
  simp [ScanFree, orIntoProg]

/-- `decodeClauseEvalStepAt` is `ScanFree`: every sub-program it sequences
    (`decodeLiteralValueProgramAt`, `readAssignBitProg`, `literalValueProg`,
    `orIntoProg`) is itself `.scanList`/`.lookup`-free. -/
lemma scanFree_decodeClauseEvalStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ) :
    ScanFree (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg) := by
  unfold decodeClauseEvalStepAt
  refine ⟨⟨scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg,
    trivial, scanFree_readAssignBitProg wBaseReg varReg bitReg,
    scanFree_literalValueProg polReg bitReg valReg, scanFree_orIntoProg valReg satReg⟩, trivial⟩

/-- Growth: one `decodeClauseEvalStepAt` step advances `cursorReg` by at most
    `1 + σ boundReg`. -/
lemma decodeClauseEvalStepAt_one_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) :
    (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg boundReg).eval σ cursorReg ≤ σ cursorReg + 1 + σ boundReg := by
  unfold decodeClauseEvalStepAt
  rw [eval_ifNZ]
  by_cases hz : σ remainingReg = 0
  · rw [ite_eq_right (by simpa [Expr.eval] using hz)]
    simp only [eval_skip]
    omega
  · rw [ite_eq_left (by simpa [Expr.eval] using hz)]
    rw [eval_seq, eval_seq, eval_seq, eval_seq]
    set τ := (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
      with hτdef
    have hτ := decodeLiteralValueProgramAt_cursor_le cursorReg polReg varReg doneReg boundReg σ
      hcp hcv hcd hbc hbp hbv hbd
    have hbτ : τ boundReg = σ boundReg :=
      decodeLiteralValueProgramAt_bound_frame cursorReg polReg varReg doneReg boundReg σ
        hbc hbp hbv hbd
    have h1cur : (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ
        cursorReg = τ cursorReg := by
      rw [eval_assign, Expr.eval]; exact writeReg_diff τ remainingReg _ cursorReg hrc.symm
    set σ1 := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ
      with hσ1def
    have h2cur : (readAssignBitProg wBaseReg varReg bitReg).eval σ1 cursorReg = σ1 cursorReg :=
      readAssignBitProg_frame wBaseReg varReg bitReg cursorReg σ1 hcbit
    set σ2 := (readAssignBitProg wBaseReg varReg bitReg).eval σ1 with hσ2def
    have h3cur : (literalValueProg polReg bitReg valReg).eval σ2 cursorReg = σ2 cursorReg :=
      literalValueProg_frame polReg bitReg valReg cursorReg σ2 hcval
    set σ3 := (literalValueProg polReg bitReg valReg).eval σ2 with hσ3def
    have h4cur : (orIntoProg valReg satReg).eval σ3 cursorReg = σ3 cursorReg :=
      orIntoProg_frame valReg satReg cursorReg σ3 hcsat
    rw [h4cur, h3cur, h2cur, h1cur]
    omega

/-- Growth bound for iterating `decodeClauseEvalStepAt`: after `k` steps the cursor
    has advanced by at most `k * (σ boundReg + 1)`, mirroring
    `decodeClauseStepAt_cursor_le`'s per-step bound `1 + σ boundReg` per iteration. -/
lemma decodeClauseEvalStepAt_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg k : ℕ)
    (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) :
    (loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg)
        k σ) cursorReg ≤ σ cursorReg + k * (σ boundReg + 1) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ_snoc]
      set τ := loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
            wBaseReg boundReg) k σ with hτdef
      have hstep := decodeClauseEvalStepAt_one_cursor_le cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg boundReg τ
        hcp hcv hcd hrc hcbit hcval hcsat hbc hbp hbv hbd
      have hbnd : τ boundReg = σ boundReg :=
        decodeClauseEvalStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg k σ hbc hbp hbv hbd hbr hbs hbb hbval
      have hik := ih σ
      rw [← hτdef] at hik
      rw [hbnd] at hstep
      have hmul : (k + 1) * (σ boundReg + 1) = k * (σ boundReg + 1) + (σ boundReg + 1) := by
        ring
      omega

/-- `decodeClauseEvalStepAt` never disturbs `wBaseReg`, iterated any number of times. -/
lemma decodeClauseEvalStepAt_loopEval_wBase_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg k : ℕ)
    (σ : Store)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) :
    loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg)
        k σ wBaseReg = σ wBaseReg := by
  exact (decodeClauseEvalStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg boundReg).loopEval_frame
    ⟨hcw.symm, hpw.symm, hvw.symm, hdw.symm, hrw.symm, hbw.symm, hvalw.symm, hsw.symm⟩ k σ

/-- `StoreValuesLe` is preserved by iterating `decodeClauseEvalStepAt`, given a coarse
    bound `hcoarse` covering the entire run (`n` iterations' worth of cursor growth,
    the `+ 1 + boundReg` per-step read/write budget) and `hwcoarse` covering the
    certificate array's base address. Mirrors
    `storeValuesLe_decodeClauseStepAt_loop_of_bounds`, with the extra distinctness
    hypotheses `decodeClauseEvalStepAt_cursor_le` needs beyond the plain
    `programBoundedIn_decodeClauseEvalStepAt_of_store_bounds` tuple. -/
lemma storeValuesLe_decodeClauseEvalStepAt_loop_of_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
      k n : ℕ) (σ : Store)
    (hB1 : 1 ≤ B)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hσ : StoreValuesLe B σ)
    (hcoarse : σ cursorReg + n * (σ boundReg + 1) + 1 + σ boundReg ≤ B)
    (hwcoarse : σ wBaseReg + σ boundReg ≤ B)
    (hk : k ≤ n) :
    StoreValuesLe B
      (loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg) k σ) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hprev := ih hk'
      have hcur := decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg boundReg k σ
        hcp hcv hcd hrc hcbit hcval hcsat hbc hbp hbv hbd hbr hbb hbval hbs
      have hbnd : loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg) k σ boundReg = σ boundReg :=
        decodeClauseEvalStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg k σ hbc hbp hbv hbd hbr hbs hbb hbval
      have hwbnd : loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg) k σ wBaseReg = σ wBaseReg :=
        decodeClauseEvalStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg k σ hcw hpw hvw hdw hrw hbw hvalw hsw
      have hprod : k * (σ boundReg + 1) ≤ n * (σ boundReg + 1) :=
        Nat.mul_le_mul_right _ hk'
      have hbudget :
          (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
            bitReg valReg wBaseReg boundReg) k σ) cursorReg + 1 +
            (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
              bitReg valReg wBaseReg boundReg) k σ) boundReg ≤ B := by
        rw [hbnd]
        have hcur' :
            (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
              bitReg valReg wBaseReg boundReg) k σ) cursorReg ≤
              σ cursorReg + k * (σ boundReg + 1) := hcur
        omega
      have hwbudget : loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg) k σ wBaseReg +
          loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg) k σ boundReg ≤ B := by
        rw [hbnd, hwbnd]; omega
      have hstep := programBoundedIn_decodeClauseEvalStepAt_of_store_bounds B cursorReg polReg
        varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
        (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
          bitReg valReg wBaseReg boundReg) k σ) hprev
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩ hcw hpw hvw hdw hrw hrv hbudget hwbudget
      rw [loopEval_succ_snoc]
      exact program_eval_storeValuesLe _ _ hB1 hprev hstep
        (scanFree_decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
          bitReg valReg wBaseReg boundReg)

end NPComplete.CookLevin

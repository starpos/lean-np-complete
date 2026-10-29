module

public import NPComplete.CookLevin.Verifier.ThreeCNFEvalBounded
public import NPComplete.CookLevin.Verifier.CNFEvalOuterBounded
public import NPComplete.BoundedWhile.Frame

/-!
Loop-level `ProgramBoundedIn`/`StoreValuesLe` facts for `decodeThreeCNFEvalClauseStepAt`,
iterated across a clause list: mirrors `CNFEvalOuterBounded.lean`'s
`storeValuesLe_decodeCNFEvalClauseStepAt_loop_of_bounds`, one abstraction level up from
`ThreeCNFEvalBounded.lean`'s single-clause-step facts. The per-step cursor growth is the fixed
`3 * (boundReg + 1)` (from `ThreeCNFEvalBounded.lean`'s constant-arity bound) rather than
`CNFEvalOuterBounded.lean`'s `1 + boundReg + boundReg * (boundReg + 1)` (length-prefix decode
plus a register-bound literal loop), so the coarse-budget arithmetic is correspondingly simpler.
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

/-- `StoreValuesLe` is preserved by iterating `decodeThreeCNFEvalClauseStepAt`, given a
    coarse bound `hcoarse` covering the entire run and `hwcoarse` covering the certificate
    array's base address. Mirrors `storeValuesLe_decodeCNFEvalClauseStepAt_loop_of_bounds`,
    one abstraction level up. -/
lemma storeValuesLe_decodeThreeCNFEvalClauseStepAt_loop_of_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg k n : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hB1 : 1 ≤ B)
    (hσ : StoreValuesLe B σ)
    (hcoarse : σ cursorReg + n * (3 * (σ boundReg + 1)) + 1 + σ boundReg ≤ B)
    (hwcoarse : σ wBaseReg + σ boundReg ≤ B)
    (hk : k ≤ n) :
    StoreValuesLe B
      (loopEval
        (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg cnfReg boundReg) k σ) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hprev := ih hk'
      have hcur := decodeThreeCNFEvalClauseStepAt_cursor_le cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg k σ
        hcp hcv hcd hrc hcbit hcval hcsat hck hbc hbp hbv hbd hbr hbb hbval hbs hbk
      have hbnd : loopEval
          (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
            bitReg valReg wBaseReg cnfReg boundReg) k σ boundReg = σ boundReg :=
        decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg k σ
          hbr hbs hbc hbp hbv hbd hbb hbval hbk
      have hwbnd : loopEval
          (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
            bitReg valReg wBaseReg cnfReg boundReg) k σ wBaseReg = σ wBaseReg :=
        decodeThreeCNFEvalClauseStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg k σ
          hrw hsw hcw hpw hvw hdw hbw hvalw hkw
      have hprod : k * (3 * (σ boundReg + 1)) ≤ n * (3 * (σ boundReg + 1)) :=
        Nat.mul_le_mul_right _ hk'
      have hprod' : (k + 1) * (3 * (σ boundReg + 1)) ≤ n * (3 * (σ boundReg + 1)) :=
        Nat.mul_le_mul_right _ hk
      have hbudget :
          (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
            satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) cursorReg + 1 +
            (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
              remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) boundReg ≤ B := by
        rw [hbnd]
        have hcur' :
            (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
              remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) cursorReg ≤
              σ cursorReg + k * (3 * (σ boundReg + 1)) := hcur
        omega
      have hwbudget2 : loopEval
          (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
            bitReg valReg wBaseReg cnfReg boundReg) k σ wBaseReg +
          loopEval
          (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
            bitReg valReg wBaseReg cnfReg boundReg) k σ boundReg ≤ B := by
        rw [hbnd, hwbnd]; omega
      have hinnerK :
          (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
            satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) cursorReg +
            3 * ((loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
              remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) boundReg + 1) + 1 +
            (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
              remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) boundReg ≤ B := by
        rw [hbnd]
        have hexpand : (k + 1) * (3 * (σ boundReg + 1)) =
            k * (3 * (σ boundReg + 1)) + 3 * (σ boundReg + 1) := by ring
        omega
      have hstep := programBoundedIn_decodeThreeCNFEvalClauseStepAt_of_store_bounds B cursorReg
        polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg
        (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg cnfReg boundReg) k σ) hprev
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
        hrc hcbit hcval hbr hbb hbval hcw hpw hvw hdw hrw hbw hvalw hrv
        ⟨hcsat.symm, hsd, hrs.symm, hbs.symm, hsw⟩
        (by omega) hwbudget2 hinnerK
      rw [loopEval_succ_snoc]
      exact program_eval_storeValuesLe _ _ hB1 hprev hstep
        (scanFree_decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg cnfReg boundReg)

/-- `ProgramBoundedIn` for `decodeThreeCNFEvalClauseStepAt` at the `m`-th visit of the outer
    `.forN outerReg` loop, given only a coarse cursor/bound/`wBaseReg` budget carried from
    the loop's entry store `σ` (via `σ2`, the store right after the clause-count prefix).
    Mirrors `programBoundedIn_decodeCNFEvalClauseStepAt_at_loop_of_outer_bounds`
    (`CNFEvalTop.lean`), one abstraction level up. -/
lemma programBoundedIn_decodeThreeCNFEvalClauseStepAt_at_loop_of_outer_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg m : ℕ) (σ σ2 : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hB1 : 1 ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg + σ boundReg * (3 * (σ boundReg + 1)) +
        3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B)
    (hσ2Le : StoreValuesLe B σ2)
    (hb2' : σ2 boundReg = σ boundReg) (hw2 : σ2 wBaseReg = σ wBaseReg)
    (hσ2cur : σ2 cursorReg ≤ σ cursorReg + σ boundReg) (houterLe : m ≤ σ boundReg) :
    ProgramBoundedIn B
      (loopEval
        (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg cnfReg boundReg) m σ2)
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  have hcoarse : σ2 cursorReg + σ boundReg * (3 * (σ2 boundReg + 1)) + 1 + σ2 boundReg ≤ B := by
    rw [hb2']; omega
  have hwcoarse : σ2 wBaseReg + σ2 boundReg ≤ B := by rw [hw2, hb2']; exact hwbudget
  have hσiterLe : StoreValuesLe B
      (loopEval
        (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg cnfReg boundReg) m σ2) :=
    storeValuesLe_decodeThreeCNFEvalClauseStepAt_loop_of_bounds B cursorReg polReg varReg
      doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg m (σ boundReg) σ2
      ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
      ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
      hrc hcbit hcval hcsat hbb hbval hbs hbk hck hrs hsd
      hcw hpw hvw hdw hrw hbw hvalw hsw hkw hrv hB1 hσ2Le hcoarse hwcoarse houterLe
  have hCurIter : (loopEval
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) m σ2) cursorReg ≤
      σ2 cursorReg + m * (3 * (σ2 boundReg + 1)) :=
    decodeThreeCNFEvalClauseStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg m σ2
      hcp hcv hcd hrc hcbit hcval hcsat hck hbc hbp hbv hbd hbr hbb hbval hbs hbk
  have hBndIterFinal : (loopEval
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) m σ2) boundReg = σ boundReg := by
    rw [decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg m σ2
      hbr hbs hbc hbp hbv hbd hbb hbval hbk, hb2']
  have hWBaseIterFinal : (loopEval
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) m σ2) wBaseReg = σ wBaseReg := by
    rw [decodeThreeCNFEvalClauseStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg m σ2
      hrw hsw hcw hpw hvw hdw hbw hvalw hkw, hw2]
  have hCurIterFinal : (loopEval
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg) m σ2) cursorReg ≤
      σ cursorReg + σ boundReg + σ boundReg * (3 * (σ boundReg + 1)) := by
    rw [hb2'] at hCurIter
    have hmb : m * (3 * (σ boundReg + 1)) ≤ σ boundReg * (3 * (σ boundReg + 1)) :=
      Nat.mul_le_mul_right _ houterLe
    have := hσ2cur
    omega
  refine programBoundedIn_decodeThreeCNFEvalClauseStepAt_of_store_bounds B cursorReg polReg
    varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg _ hσiterLe
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
    hrc hcbit hcval hbr hbb hbval hcw hpw hvw hdw hrw hbw hvalw hrv
    ⟨hcsat.symm, hsd, hrs.symm, hbs.symm, hsw⟩ (by omega) ?_ ?_
  · rw [hBndIterFinal, hWBaseIterFinal]; omega
  · rw [hBndIterFinal]
    have := hCurIterFinal
    omega

end NPComplete.CookLevin

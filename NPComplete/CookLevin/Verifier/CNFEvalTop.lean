module

public import NPComplete.CookLevin.Verifier.CNFEvalOuterBounded

/-!
# Top-level evaluator storage bounds

Bounding each clause step is not enough to bound the complete evaluator's outer
loop from its entry store. This module combines those loop bounds with store
constraints to establish the top-level memory contract.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

/-- `ProgramBoundedIn` for `decodeCNFEvalClauseStepAt` at the `m`-th visit of the outer
    `.forN outerReg` loop, given only a coarse cursor/bound/`wBaseReg` budget carried from
    the loop's entry store `σ` (via `σ2`, the store right after the clause-count prefix).
    Supplies the per-iteration bound used by
    `programBoundedIn_decodeCNFEvalProgramAt_of_store_bounds`. -/
lemma programBoundedIn_decodeCNFEvalClauseStepAt_at_loop_of_outer_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg m : ℕ) (σ σ2 : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbl : boundReg ≠ lengthReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg)
    (hsd : satReg ≠ doneReg) (hsl : satReg ≠ lengthReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hB1 : 1 ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg +
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) +
        2 + 2 * σ boundReg + σ boundReg * (σ boundReg + 1) ≤ B)
    (hσ2Le : StoreValuesLe B σ2)
    (hb2' : σ2 boundReg = σ boundReg) (hw2 : σ2 wBaseReg = σ wBaseReg)
    (hσ2cur : σ2 cursorReg ≤ σ cursorReg + σ boundReg) (houterLe : m ≤ σ boundReg) :
    ProgramBoundedIn B
      (loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg) m σ2)
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  have hcoarse : σ2 cursorReg + σ boundReg *
      (1 + σ2 boundReg + σ2 boundReg * (σ2 boundReg + 1)) + 1 + σ2 boundReg ≤ B := by
    rw [hb2']; omega
  have hwcoarse : σ2 wBaseReg + σ2 boundReg ≤ B := by rw [hw2, hb2']; exact hwbudget
  have hσiterLe : StoreValuesLe B
      (loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg) m σ2) :=
    storeValuesLe_decodeCNFEvalClauseStepAt_loop_of_bounds B cursorReg polReg varReg
      doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg m
      (σ boundReg) σ2
      ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
      ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
      hcl hld hrc hcbit hcval hcsat hbl hbb hbval hbs hbk hck hrs hsd hsl
      hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw hrv hB1 hσ2Le hcoarse hwcoarse houterLe
  have hCurIter : (loopEval
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) m σ2) cursorReg ≤
      σ2 cursorReg + m * (1 + σ2 boundReg + σ2 boundReg * (σ2 boundReg + 1)) :=
    decodeCNFEvalClauseStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg cnfReg boundReg m σ2
      hcp hcv hcd hcl hld hrc hcbit hcval hcsat hbc hbp hbv hbd hbl hbr hbb hbval hbs hbk hck hrs
  have hBndIterFinal : (loopEval
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) m σ2) boundReg = σ boundReg := by
    rw [decodeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg m σ2
      hbc hbp hbv hbd hbl hbr hbs hbb hbval hbk, hb2']
  have hWBaseIterFinal : (loopEval
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) m σ2) wBaseReg = σ wBaseReg := by
    rw [decodeCNFEvalClauseStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg m σ2
      hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw, hw2]
  have hCurIterFinal : (loopEval
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) m σ2) cursorReg ≤
      σ cursorReg + σ boundReg +
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) := by
    rw [hb2'] at hCurIter
    have hmb : m * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) ≤
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) :=
      Nat.mul_le_mul_right _ houterLe
    omega
  refine programBoundedIn_decodeCNFEvalClauseStepAt_of_store_bounds B cursorReg polReg varReg
    doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg _ hσiterLe
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
    hcl hld hrc hrv hbl hcw hpw hvw hdw hrw hlw hcbit hcval hbb hbval hbw hvalw
    ⟨hcsat.symm, hsd, hrs.symm, hsl, hbs.symm, hsw⟩ ?_ ?_ ?_
  · rw [hBndIterFinal]; omega
  · rw [hWBaseIterFinal, hBndIterFinal]; exact hwbudget
  · rw [hBndIterFinal]; omega

/-- `ProgramBoundedIn` for `decodeCNFEvalProgramAt`: decode the clause-count prefix, then
    bound the per-clause `.forN` loop via `storeValuesLe_decodeCNFEvalClauseStepAt_loop_of_bounds`
    at every prefix count. Given a single coarse polynomial bound `B` in the encoded length
    (via `σ boundReg`), covering the whole run. -/
lemma programBoundedIn_decodeCNFEvalProgramAt_of_store_bounds
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store) (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbl : boundReg ≠ lengthReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg)
    (hsd : satReg ≠ doneReg) (hsl : satReg ≠ lengthReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hco : cursorReg ≠ outerReg) (hdo : doneReg ≠ outerReg) (hoBnd : outerReg ≠ boundReg)
    (how : outerReg ≠ wBaseReg)
    (hB1 : 1 ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg +
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) +
        2 + 2 * σ boundReg + σ boundReg * (σ boundReg + 1) ≤ B) :
    ProgramBoundedIn B σ
      (decodeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  unfold decodeCNFEvalProgramAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨⟨hdi, Nat.zero_le B⟩, ⟨hoi, Nat.zero_le B⟩, ?_, hoi, ?_⟩
  · set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
    have hσ0b : σ0 boundReg = σ boundReg := by
      rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 boundReg hbd
    have hσ0cur : σ0 cursorReg = σ cursorReg := by
      rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 cursorReg hcd
    set σ1 := (Program.assign outerReg (.const 0)).eval σ0 with hσ1def
    have hσ1b : σ1 boundReg = σ0 boundReg := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 outerReg 0 boundReg hoBnd.symm
    have hσ1cur : σ1 cursorReg = σ0 cursorReg := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 outerReg 0 cursorReg hco
    have hσ1Le : StoreValuesLe B σ1 := by
      apply storeValuesLe_assign
      · apply storeValuesLe_assign hσ
        simp only [Expr.eval]; omega
      · simp only [Expr.eval]; omega
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg outerReg doneReg boundReg B σ1
      hco hcd (fun h => hdo h.symm) ⟨hci, hoi, hdi, hbi⟩
    · rw [hσ1cur, hσ0cur]
      omega
    · have h0 : σ1 outerReg = 0 := by
        rw [hσ1def, eval_assign, Expr.eval, writeReg_same]
      rw [h0, hσ1b, hσ0b]
      omega
  · set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
    have hσ0b : σ0 boundReg = σ boundReg := by
      rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 boundReg hbd
    have hσ0cur : σ0 cursorReg = σ cursorReg := by
      rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 cursorReg hcd
    have hσ0w : σ0 wBaseReg = σ wBaseReg := by
      rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 wBaseReg hdw.symm
    set σ1 := (Program.assign outerReg (.const 0)).eval σ0 with hσ1def
    have hσ1b : σ1 boundReg = σ0 boundReg := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 outerReg 0 boundReg hoBnd.symm
    have hσ1cur : σ1 cursorReg = σ0 cursorReg := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 outerReg 0 cursorReg hco
    have hσ1w : σ1 wBaseReg = σ0 wBaseReg := by
      rw [hσ1def, eval_assign, Expr.eval]
      exact writeReg_diff σ0 outerReg 0 wBaseReg how.symm
    have hσ1Le : StoreValuesLe B σ1 := by
      apply storeValuesLe_assign
      · apply storeValuesLe_assign hσ
        simp only [Expr.eval]; omega
      · simp only [Expr.eval]; omega
    have hprefix : ProgramBoundedIn B σ1
        (decodeNatProgramAt cursorReg outerReg doneReg boundReg) := by
      apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg outerReg doneReg boundReg B σ1
        hco hcd (fun h => hdo h.symm) ⟨hci, hoi, hdi, hbi⟩
      · rw [hσ1cur, hσ0cur]
        omega
      · have h0 : σ1 outerReg = 0 := by
          rw [hσ1def, eval_assign, Expr.eval, writeReg_same]
        rw [h0, hσ1b, hσ0b]
        omega
    have hπStore : StoreValuesLe B
        ((decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1) :=
      program_eval_storeValuesLe σ1 _ hB1 hσ1Le hprefix
        (scanFree_decodeNatProgramAt cursorReg outerReg doneReg boundReg)
    intro m hm
    have hb1 : (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1 boundReg =
        σ1 boundReg :=
      decodeNatProgramAt_bound_frame cursorReg outerReg doneReg boundReg σ1 hbc hoBnd.symm hbd
    have hw1 : (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1 wBaseReg =
        σ1 wBaseReg :=
      decodeNatProgramAt_frame cursorReg outerReg doneReg boundReg wBaseReg σ1
        hcw.symm how.symm hdw.symm
    have houterLe : m ≤ σ boundReg := by
      change m < (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1 outerReg at hm
      have hcount := decodeNatProgramAt_count_le cursorReg outerReg doneReg boundReg σ1
        hco hdo.symm
      have h0 : σ1 outerReg = 0 := by
        rw [hσ1def, eval_assign, Expr.eval, writeReg_same]
      rw [h0] at hcount
      have hb1' : σ1 boundReg = σ boundReg := by rw [hσ1b, hσ0b]
      omega
    set σ2 := (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1 with hσ2def
    have hcur2 : σ2 cursorReg ≤ σ1 cursorReg + σ1 boundReg := by
      unfold decodeNatProgramAt decodeUnaryProgAt at hσ2def
      rw [hσ2def, eval_forN]
      simp only [Expr.eval]
      exact loopEval_decodeUnaryStep_cursor_le cursorReg outerReg doneReg hco hcd (σ1 boundReg) σ1
    have hb2 : σ2 boundReg = σ1 boundReg := hb1
    have hw2 : σ2 wBaseReg = σ1 wBaseReg := hw1
    have hσ2Le : StoreValuesLe B σ2 := hπStore
    have hb2' : σ2 boundReg = σ boundReg := by rw [hb2, hσ1b, hσ0b]
    have hw2' : σ2 wBaseReg = σ wBaseReg := by rw [hw2, hσ1w, hσ0w]
    have hσ2cur : σ2 cursorReg ≤ σ cursorReg + σ boundReg := by
      rw [hσ1cur, hσ0cur, hσ1b, hσ0b] at hcur2
      exact hcur2
    exact programBoundedIn_decodeCNFEvalClauseStepAt_at_loop_of_outer_bounds B cursorReg polReg
      varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg m σ σ2
      ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
      ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
      hcl hld hrc hcbit hcval hcsat hbl hbb hbval hbs hbk hck hrs hsd hsl
      hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw hrv hB1 hwbudget houterCoarse
      hσ2Le hb2' hw2' hσ2cur houterLe

end NPComplete.CookLevin

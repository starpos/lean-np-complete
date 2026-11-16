module

public import NPComplete.CookLevin.Verifier.ClauseEvalWLoop
public import NPComplete.CookLevin.Verifier.CNFEvalAt
public import NPComplete.CookLevin.UniformPackaging.ProducerProgram
public import NPComplete.BoundedWhile.Frame

/-!
# Outer CNF-evaluator bounds

The CNF evaluator repeatedly decodes length-prefixed clauses, so local bounds
must survive the outer loop together with its base and cursor invariants. This
module establishes the frame and storage bounds for an outer clause step, which
the top-level theorem packages for the complete program.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ loopEval_succ_snoc eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

lemma scanFree_andIntoProg (clauseSatReg cnfReg : ℕ) :
    ScanFree (andIntoProg clauseSatReg cnfReg) := by
  simp [ScanFree, andIntoProg]

/-- `decodeClauseEvalWithLengthProgramAt` is `ScanFree`: the length prefix decoder and
    the per-literal AND/OR loop body (`decodeClauseEvalStepAt`) are both scan-free. -/
lemma scanFree_decodeClauseEvalWithLengthProgramAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg boundReg : ℕ) :
    ScanFree (decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg lengthReg boundReg) := by
  unfold decodeClauseEvalWithLengthProgramAt
  exact ⟨scanFree_decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
    boundReg, trivial, scanFree_decodeClauseEvalStepAt cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg boundReg⟩

/-- `decodeCNFEvalClauseStepAt` is `ScanFree`: the length-prefixed clause evaluator and
    the AND-accumulator step are both scan-free. -/
lemma scanFree_decodeCNFEvalClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) :
    ScanFree (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg cnfReg boundReg) := by
  unfold decodeCNFEvalClauseStepAt
  exact ⟨scanFree_decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg lengthReg boundReg, scanFree_andIntoProg satReg cnfReg⟩

/-- General frame for `decodeClauseWithLengthPrefixAt`: any register distinct from
    `cursorReg`/`doneReg`/`remainingReg`/`lengthReg` (its only writes) is unchanged. -/
lemma decodeClauseWithLengthPrefixAt_frame
    (cursorReg doneReg remainingReg lengthReg boundReg r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ doneReg) (h3 : r ≠ remainingReg) (h4 : r ≠ lengthReg) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ r =
      σ r := by
  exact (decodeClauseWithLengthPrefixAt_avoids_frame cursorReg doneReg remainingReg lengthReg
    boundReg).eval_frame σ ⟨h1, h2, h3, h4⟩

/-- `decodeClauseWithLengthPrefixAt` leaves `remainingReg` at most `σ boundReg`: the
    length prefix it decodes is bounded by `boundReg` (`decodeNatProgramAt_count_le`),
    and `remainingReg` is seeded from exactly that count. -/
lemma decodeClauseWithLengthPrefixAt_remaining_le
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) (σ : Store)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg)
    (hbd : boundReg ≠ doneReg) (hbl : boundReg ≠ lengthReg) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
      remainingReg ≤ σ boundReg := by
  unfold decodeClauseWithLengthPrefixAt
  rw [eval_seq, eval_seq, eval_seq, eval_seq]
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
  have hb0 : σ0 boundReg = σ boundReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 boundReg hbd
  set σ1 := (Program.assign lengthReg (.const 0)).eval σ0 with hσ1def
  have hσ1len : σ1 lengthReg = 0 := by
    rw [hσ1def, eval_assign, Expr.eval, writeReg_same]
  have hb1 : σ1 boundReg = σ0 boundReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 lengthReg 0 boundReg hbl
  have hle : (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1 lengthReg ≤
      σ1 lengthReg + σ1 boundReg :=
    decodeNatProgramAt_count_le cursorReg lengthReg doneReg boundReg σ1 hcl hld
  set σ2 := (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1 with hσ2def
  rw [hσ1len] at hle
  simp only [eval_assign, Expr.eval, writeReg_same]
  have hd2 : writeReg σ2 doneReg 0 lengthReg = σ2 lengthReg :=
    writeReg_diff σ2 doneReg 0 lengthReg hld
  rw [hd2]
  omega

/-- Growth bound for one `decodeCNFEvalClauseStepAt` step: the cursor advances by at
    most `1 + boundReg` (the length prefix) plus `boundReg * (1 + boundReg)` (the
    per-literal loop, run at most `boundReg` times since `remainingReg ≤ boundReg`
    after the prefix). -/
lemma decodeCNFEvalClauseStepAt_one_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg) :
    (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg lengthReg cnfReg boundReg).eval σ cursorReg ≤
      σ cursorReg + 1 + σ boundReg + σ boundReg * (σ boundReg + 1) := by
  change ((decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg lengthReg boundReg).seq
      (andIntoProg satReg cnfReg)).eval σ cursorReg ≤ _
  rw [eval_seq]
  unfold decodeClauseEvalWithLengthProgramAt
  rw [eval_seq, eval_seq]
  have hpre := decodeClauseWithLengthPrefixAt_cursor_le cursorReg doneReg remainingReg lengthReg
    boundReg σ hcd hcl hrc hbl hbd
  have hpreRem := decodeClauseWithLengthPrefixAt_remaining_le cursorReg doneReg remainingReg
    lengthReg boundReg σ hcl hld hbd hbl
  have hpreB : (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
      boundReg).eval σ boundReg = σ boundReg :=
    decodeClauseWithLengthPrefixAt_bound_frame cursorReg doneReg remainingReg lengthReg
      boundReg σ hbc hbd hbl hbr
  set σ0 := (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
    boundReg).eval σ with hσ0def
  set σ1 := (Program.assign satReg (.const 0)).eval σ0 with hσ1def
  have hσ1cur : σ1 cursorReg = σ0 cursorReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 cursorReg hcsat
  have hσ1rem : σ1 remainingReg = σ0 remainingReg := by
    rw [hσ1def, eval_assign, Expr.eval]
    exact writeReg_diff σ0 satReg 0 remainingReg hrs
  have hσ1b : σ1 boundReg = σ0 boundReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 boundReg hbs
  rw [eval_forN]
  simp only [Expr.eval]
  set K := σ1 remainingReg with hKdef
  have hloopCur := decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg boundReg K σ1
    hcp hcv hcd hrc hcbit hcval hcsat hbc hbp hbv hbd hbr hbb hbval hbs
  have hKle : K ≤ σ boundReg := by
    rw [hKdef]
    calc σ1 remainingReg = σ0 remainingReg := hσ1rem
      _ ≤ σ boundReg := hpreRem
  have hσ1bEq : σ1 boundReg = σ boundReg := by rw [hσ1b, hpreB]
  have hprodK : K * (σ1 boundReg + 1) ≤ σ boundReg * (σ boundReg + 1) := by
    rw [hσ1bEq]; exact Nat.mul_le_mul_right _ hKle
  have hpreCur : σ0 cursorReg ≤ σ cursorReg + 1 + σ boundReg := hpre
  have hAndFrame : (andIntoProg satReg cnfReg).eval
      (loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg) K σ1) cursorReg =
      (loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg) K σ1) cursorReg :=
    andIntoProg_frame satReg cnfReg cursorReg _ hck
  rw [hAndFrame]
  calc
    (loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
          wBaseReg boundReg) K σ1) cursorReg
        ≤ σ1 cursorReg + K * (σ1 boundReg + 1) := hloopCur
    _ = σ0 cursorReg + K * (σ1 boundReg + 1) := by rw [hσ1cur]
    _ ≤ σ cursorReg + 1 + σ boundReg + σ boundReg * (σ boundReg + 1) := by
        have := hprodK; omega

/-- `decodeCNFEvalClauseStepAt` never disturbs `boundReg`, iterated any number of times. -/
lemma decodeCNFEvalClauseStepAt_loopEval_bound_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg k : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbs : boundReg ≠ satReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbk : boundReg ≠ cnfReg) :
    loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg)
        k σ boundReg = σ boundReg := by
  exact (decodeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg).loopEval_frame
    ⟨hbc, hbp, hbv, hbd, hbr, hbs, hbb, hbval, hbl, hbk⟩ k σ

/-- `decodeCNFEvalClauseStepAt` never disturbs `wBaseReg`, iterated any number of times. -/
lemma decodeCNFEvalClauseStepAt_loopEval_wBase_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg k : ℕ) (σ : Store)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) :
    loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg)
        k σ wBaseReg = σ wBaseReg := by
  exact (decodeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg).loopEval_frame
    ⟨hcw.symm, hpw.symm, hvw.symm, hdw.symm, hrw.symm, hsw.symm, hbw.symm,
      hvalw.symm, hlw.symm, hkw.symm⟩ k σ

/-- Growth bound for iterating `decodeCNFEvalClauseStepAt`: after `k` steps the cursor
    has advanced by at most `k * (1 + σ boundReg + σ boundReg * (σ boundReg + 1))`. -/
lemma decodeCNFEvalClauseStepAt_cursor_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg k : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg)
    (hbk : boundReg ≠ cnfReg) (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg) :
    (loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg)
        k σ) cursorReg ≤
      σ cursorReg + k * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ_snoc]
      set τ := loopEval
          (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg lengthReg cnfReg boundReg) k σ with hτdef
      have hstep := decodeCNFEvalClauseStepAt_one_cursor_le cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg τ
        hcp hcv hcd hcl hld hrc hcbit hcval hcsat hbc hbp hbv hbd hbl hbr hbb hbval hbs hck hrs
      have hbnd : τ boundReg = σ boundReg :=
        decodeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg k σ
          hbc hbp hbv hbd hbl hbr hbs hbb hbval hbk
      have hik := ih σ
      rw [← hτdef] at hik
      rw [hbnd] at hstep
      have hmul : (k + 1) * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) =
          k * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) +
            (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) := by ring
      omega
end NPComplete.CookLevin

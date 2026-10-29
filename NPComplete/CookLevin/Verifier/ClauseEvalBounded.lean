module

public import NPComplete.CookLevin.Verifier.CNFEvalAt
public import NPComplete.CookLevin.UniformPackaging.DecoderBounds
public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailBounds
public import NPComplete.CookLevin.UniformPackaging.EmitStateBounds
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
# Clause-evaluator storage bounds

Literal evaluation reads variable indices derived from encoded input, so its
RAM program needs a store-bound proof before it can be composed with compiled
execution. This module derives bounds for clause parsing and Boolean operations
from the decoder and memory-layout invariants.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)

lemma scanFree_readAssignBitProg (wBaseReg varReg bitReg : ℕ) :
    ScanFree (readAssignBitProg wBaseReg varReg bitReg) := by
  simp [ScanFree, readAssignBitProg]

lemma scanFree_literalValueProg (polReg bitReg valReg : ℕ) :
    ScanFree (literalValueProg polReg bitReg valReg) := by
  simp [ScanFree, literalValueProg]

lemma programBoundedIn_decodeClauseEvalStepAt_of_store_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store) (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg boundReg) := by
  have hB1 : 1 ≤ B := by omega
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  have hlit := programBoundedIn_decodeLiteralValueProgramAt_of_bounds B cursorReg polReg
    varReg doneReg boundReg σ ⟨hci, hpi, hvi, hdi, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩ hB1 hσ hbudget
  have hσlit : StoreValuesLe B
      ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ) :=
    program_eval_storeValuesLe σ _ hB1 hσ hlit
      (scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
  set σ1 := (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
    with hσ1def
  unfold decodeClauseEvalStepAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hri, ⟨hlit, ⟨hri, hri, hB1, hσlit remainingReg⟩, ?_⟩, trivial⟩
  set σr := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval σ1
    with hσrdef
  have hσrLe : StoreValuesLe B σr := storeValuesLe_assign hσlit (by
    have := hσlit remainingReg
    simp only [Expr.eval]
    omega)
  have hσrvar : σr varReg = σ1 varReg := by
    simp only [hσrdef, eval_assign, Expr.eval]
    exact writeReg_diff σ1 remainingReg _ varReg hrv.symm
  have hσrw : σr wBaseReg = σ1 wBaseReg := by
    simp only [hσrdef, eval_assign, Expr.eval]
    exact writeReg_diff σ1 remainingReg _ wBaseReg hrw.symm
  have hσ1w : σ1 wBaseReg = σ wBaseReg :=
    decodeLiteralValueProgramAt_frame cursorReg polReg varReg doneReg boundReg wBaseReg σ
      hcw.symm hpw.symm hvw.symm hdw.symm
  have hpread : ProgramBoundedIn B σr (readAssignBitProg wBaseReg varReg bitReg) := by
    unfold readAssignBitProg
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    have hvar : σ1 varReg ≤ σ boundReg :=
      decodeLiteralValueProgramAt_var_le cursorReg polReg varReg doneReg boundReg σ
        hbc hbp hbv hbd hcv hvd
    have hsum : σr wBaseReg + σr varReg ≤ B := by
      rw [hσrvar, hσrw, hσ1w]
      omega
    exact ⟨hbiti, ⟨hwi, hvi, hsum⟩, hsum⟩
  refine ⟨hpread, ?_⟩
  have hσreadLe : StoreValuesLe B
      ((readAssignBitProg wBaseReg varReg bitReg).eval σr) :=
    program_eval_storeValuesLe σr _ hB1 hσrLe hpread (scanFree_readAssignBitProg _ _ _)
  set σ2 := (readAssignBitProg wBaseReg varReg bitReg).eval σr with hσ2def
  have hpval : ProgramBoundedIn B σ2 (literalValueProg polReg bitReg valReg) := by
    unfold literalValueProg
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    exact ⟨hpi, ⟨hvali, hB1, hbiti, hB1⟩, hvali, hbiti⟩
  refine ⟨hpval, ?_⟩
  have hσvalLe : StoreValuesLe B
      ((literalValueProg polReg bitReg valReg).eval σ2) :=
    program_eval_storeValuesLe σ2 _ hB1 hσreadLe hpval (scanFree_literalValueProg _ _ _)
  set σ3 := (literalValueProg polReg bitReg valReg).eval σ2 with hσ3def
  unfold orIntoProg
  simp only [ProgramBoundedIn, ExprBoundedIn]
  exact ⟨hvali, ⟨hsi, hB1⟩, trivial⟩

/-- `decodeClauseEvalWithLengthProgramAt` keeps every address/value `≤ B`: decode the
    length prefix, then bound the per-literal AND/OR loop at every prefix count via
    `programBoundedIn_decodeClauseEvalStepAt_of_store_bounds`. Mirrors
    `programBoundedIn_decodeClauseWithLengthProgramAt_of_invariants`, swapping the
    max-tracking step for the OR-accumulator/certificate-read step. -/
lemma programBoundedIn_decodeClauseEvalWithLengthProgramAt_of_invariants
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hprefix : ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg))
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ lengthReg ∧ satReg ≠ boundReg)
    (hwbudget : ∀ m ≤
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) wBaseReg +
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) boundReg ≤ B)
    (hbudget : ∀ m <
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) cursorReg + 1 +
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) boundReg ≤ B)
    (hstoreLoop : ∀ m ≤
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      StoreValuesLe B
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ)))) :
    ProgramBoundedIn B σ
      (decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg boundReg) := by
  rcases hsatFrame with ⟨hsc, hsd, hsr, hsl, hsb⟩
  unfold decodeClauseEvalWithLengthProgramAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hprefix, ⟨hidx.2.2.2.2.2.1, Nat.zero_le B⟩, hidx.2.2.2.2.1, ?_⟩
  set σ0 :=
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
    with hσ0def
  set σ1 := (Program.assign satReg (.const 0)).eval σ0 with hσ1def
  have hσ1rem : σ1 remainingReg = σ0 remainingReg := by
    rw [hσ1def, eval_assign, Expr.eval]
    exact writeReg_diff σ0 satReg 0 remainingReg (Ne.symm hsr)
  simp only [Expr.eval, hσ1rem]
  intro m hm
  exact programBoundedIn_decodeClauseEvalStepAt_of_store_bounds B cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg wBaseReg boundReg _ (hstoreLoop m (by omega))
    ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2.1, hidx.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2.2.2.2.2⟩
    ⟨hdist.1, hdist.2.1, hdist.2.2.1, hdist.2.2.2.1, hdist.2.2.2.2.1, hdist.2.2.2.2.2.1,
      hdist.2.2.2.2.2.2.1, hdist.2.2.2.2.2.2.2.1⟩
    hcw hpw hvw hdw hrw hrv (hbudget m hm) (hwbudget m (by omega))

/-- `andIntoProg` is trivially `ProgramBoundedIn` at every store: its only write is
    `cnfReg := 0`, checked unconditionally by `ProgramBoundedIn` regardless of the
    guard (`ProgramBoundedIn` checks unselected branches). -/
lemma programBoundedIn_andIntoProg (B clauseSatReg cnfReg : ℕ) (σ : Store)
    (hsi : clauseSatReg ≤ B) (hci : cnfReg ≤ B) :
    ProgramBoundedIn B σ (andIntoProg clauseSatReg cnfReg) := by
  unfold andIntoProg
  simp only [ProgramBoundedIn, ExprBoundedIn]
  exact ⟨hsi, trivial, hci, Nat.zero_le B⟩


/-- `decodeCNFEvalClauseStepAt` keeps every address/value `≤ B`: the length-prefixed
    clause decode/eval (`programBoundedIn_decodeClauseEvalWithLengthProgramAt_of_invariants`)
    followed by the trivially-bounded AND-accumulator step. -/
lemma programBoundedIn_decodeCNFEvalClauseStepAt_of_invariants
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hprefix : ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg))
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ lengthReg ∧ satReg ≠ boundReg)
    (hwbudget : ∀ m ≤
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) wBaseReg +
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) boundReg ≤ B)
    (hbudget : ∀ m <
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) cursorReg + 1 +
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ))) boundReg ≤ B)
    (hstoreLoop : ∀ m ≤
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      StoreValuesLe B
        (loopEval
          (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg boundReg)
          m
          ((Program.assign satReg (.const 0)).eval
            ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
              boundReg).eval σ)))) :
    ProgramBoundedIn B σ
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) := by
  have hclause := programBoundedIn_decodeClauseEvalWithLengthProgramAt_of_invariants B cursorReg
    polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg boundReg σ
    ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2.1, hidx.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.2.1,
      hidx.2.2.2.2.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2.2.2.2.2⟩
    hdist hcw hpw hvw hdw hrw hrv hprefix hsatFrame hwbudget hbudget hstoreLoop
  unfold decodeCNFEvalClauseStepAt
  simp only [ProgramBoundedIn]
  exact ⟨hclause, programBoundedIn_andIntoProg B satReg cnfReg _ hidx.2.2.2.2.2.1
    hidx.2.2.2.2.2.2.2.2.2.2.1⟩

end NPComplete.CookLevin

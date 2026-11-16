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

/-- **Local-bounds body.** The clause-step leaf with a local premise: bounds on the two cells
whose values enter operands, the `regInd` address cell `cursorReg` at the entry store, and
`remainingReg` at the store the literal decoder leaves (the `sub` operand of the guarded
step).  The intermediate global preservation (`StoreValuesLe` of the literal decoder's
output) is dead weight. -/
lemma programBoundedIn_decodeClauseEvalStepAt_of_local_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hcur : σ cursorReg ≤ B)
    (hrem : ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ)
      remainingReg ≤ B)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg boundReg) := by
  have hB1 : 1 ≤ B := by omega
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  have hlit := programBoundedIn_decodeLiteralValueProgramAt_of_local_bounds B cursorReg polReg
    varReg doneReg boundReg σ ⟨hci, hpi, hvi, hdi, hbi⟩
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩ hB1 hcur hbudget
  set σ1 := (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
    with hσ1def
  unfold decodeClauseEvalStepAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hri, ⟨hlit, ⟨hri, hri, hB1, hrem⟩, ?_⟩, trivial⟩
  set σr := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval σ1
    with hσrdef
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
  set σ2 := (readAssignBitProg wBaseReg varReg bitReg).eval σr with hσ2def
  have hpval : ProgramBoundedIn B σ2 (literalValueProg polReg bitReg valReg) := by
    unfold literalValueProg
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    exact ⟨hpi, ⟨hvali, hB1, hbiti, hB1⟩, hvali, hbiti⟩
  refine ⟨hpval, ?_⟩
  set σ3 := (literalValueProg polReg bitReg valReg).eval σ2 with hσ3def
  unfold orIntoProg
  simp only [ProgramBoundedIn, ExprBoundedIn]
  exact ⟨hvali, ⟨hsi, hB1⟩, trivial⟩
/-- `andIntoProg` is trivially `ProgramBoundedIn` at every store: its only write is
    `cnfReg := 0`, checked unconditionally by `ProgramBoundedIn` regardless of the
    guard (`ProgramBoundedIn` checks unselected branches). -/
lemma programBoundedIn_andIntoProg (B clauseSatReg cnfReg : ℕ) (σ : Store)
    (hsi : clauseSatReg ≤ B) (hci : cnfReg ≤ B) :
    ProgramBoundedIn B σ (andIntoProg clauseSatReg cnfReg) := by
  unfold andIntoProg
  simp only [ProgramBoundedIn, ExprBoundedIn]
  exact ⟨hsi, trivial, hci, Nat.zero_le B⟩

end NPComplete.CookLevin

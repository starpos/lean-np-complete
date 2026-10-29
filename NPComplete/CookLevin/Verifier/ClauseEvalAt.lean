module

public import NPComplete.CookLevin.Verifier.ClauseEval
public import NPComplete.CookLevin.NatParser.UniformDecode
public import NPComplete.BoundedWhile.Frame

/-!
`decodeClauseEvalStep`'s literal-decode sub-call bakes its unary-scan bound in as a
compile-time `.const`. A single `Program` implementing the SAT verifier's machine-side
check must work for every CNF, so the bound is sampled from a register at loop entry.
This module specialises `decodeClauseEvalStep` as `decodeClauseEvalStepAt`, mirroring
`decodeClauseStepAt` (`UniformDecode.lean`) in the max-tracking scanner.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length)
open NPComplete.SAT (Literal)

/-- Register-driven-bound counterpart of `decodeClauseEvalStep`: the literal decoder's
    unary-scan bound is read from `boundReg` instead of baked in, so the same `Program`
    term works for every literal, not just those whose variable index is below a fixed
    compile-time bound. -/
def decodeClauseEvalStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ) :
    Program :=
  .ifNZ (.reg remainingReg)
    (.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
      <| .seq (.assign remainingReg (.sub (.reg remainingReg) (.const 1)))
          <| .seq (readAssignBitProg wBaseReg varReg bitReg)
            <| .seq (literalValueProg polReg bitReg valReg)
                (orIntoProg valReg satReg))
    .skip

/-- `decodeClauseEvalStepAt` agrees with `decodeClauseEvalStep` whenever `boundReg` holds
    the bound value `decodeClauseEvalStep` was given as a constant. -/
lemma decodeClauseEvalStepAt_eq
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
      bound : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg boundReg).eval σ =
      (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg bound).eval σ := by
  unfold decodeClauseEvalStepAt decodeClauseEvalStep
  rw [eval_ifNZ, eval_ifNZ]
  split_ifs
  · have h := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
      hb hbc hbp hbv hbd
    simp [eval_seq, h]
  · rfl

lemma decodeClauseEvalStepAt_avoids_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ) :
    (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧ r ≠ satReg) := by
  simp [Program.Avoids, decodeClauseEvalStepAt, decodeLiteralValueProgramAt,
    decodeNatProgramAt, decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg,
    readAssignBitProg, literalValueProg, orIntoProg]

/-- `decodeClauseEvalStepAt` preserves `boundReg` if it differs from every register
    the step writes. -/
lemma decodeClauseEvalStepAt_bound_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbs : boundReg ≠ satReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) :
    (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg boundReg).eval σ boundReg = σ boundReg := by
  exact (decodeClauseEvalStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg boundReg).eval_frame σ
    ⟨hbc, hbp, hbv, hbd, hbr, hbb, hbval, hbs⟩

/-- Iterating `decodeClauseEvalStepAt` agrees with iterating `decodeClauseEvalStep` at the
    matching constant bound, for any iteration count. -/
lemma decodeClauseEvalStepAt_loopEval_eq
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
      bound k : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbs : boundReg ≠ satReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) :
    loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg boundReg)
        k σ =
      loopEval
        (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg bound)
        k σ := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      have hstep := decodeClauseEvalStepAt_eq cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg boundReg bound σ hb hbc hbp hbv hbd
      have hb' := decodeClauseEvalStepAt_bound_frame cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg boundReg σ hbc hbp hbv hbd hbr hbs hbb hbval
      rw [loopEval_succ, loopEval_succ, hstep]
      apply ih
      exact hstep ▸ hb'.trans hb

end NPComplete.CookLevin

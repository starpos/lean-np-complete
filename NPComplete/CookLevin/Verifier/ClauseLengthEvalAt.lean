module

public import NPComplete.CookLevin.Verifier.ClauseEvalAt
public import NPComplete.CookLevin.Verifier.ClauseLengthEval
public import NPComplete.BoundedWhile.Frame

/-!
`decodeClauseEvalWithLengthProgram`'s length-prefix decode and per-literal scan both
bake their unary bound in as a compile-time `.const`.  This module is the
register-driven-bound counterpart, `decodeClauseEvalWithLengthProgramAt`, built from
`decodeClauseWithLengthPrefixAt` (`UniformDecode.lean`) and `decodeClauseEvalStepAt`
(`ClauseEvalAt.lean`) exactly as `decodeClauseWithLengthProgramAt` combines
`decodeClauseWithLengthPrefixAt` with `decodeClauseStepAt` for the reduction pipeline.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

/-- `decodeClauseEvalStepAt` never disturbs `boundReg`, iterated any number of times. -/
lemma decodeClauseEvalStepAt_loopEval_bound_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg k : ℕ)
    (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbs : boundReg ≠ satReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) :
    loopEval
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg boundReg)
        k σ boundReg = σ boundReg := by
  exact (decodeClauseEvalStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg boundReg).loopEval_frame
    ⟨hbc, hbp, hbv, hbd, hbr, hbb, hbval, hbs⟩ k σ

/-- Register-driven-bound counterpart of `decodeClauseEvalWithLengthProgram`. -/
def decodeClauseEvalWithLengthProgramAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg boundReg : ℕ) : Program :=
  .seq (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg)
    <| .seq (.assign satReg (.const 0))
      (.forN (.reg remainingReg)
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg boundReg))

/-- `decodeClauseEvalWithLengthProgramAt` agrees with `decodeClauseEvalWithLengthProgram`
    whenever `boundReg` holds the constant bound. -/
lemma decodeClauseEvalWithLengthProgramAt_eq
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg boundReg bound : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbs : boundReg ≠ satReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) :
    (decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg boundReg).eval σ =
      (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg bound).eval σ := by
  unfold decodeClauseEvalWithLengthProgramAt decodeClauseEvalWithLengthProgram
  rw [eval_seq, eval_seq, eval_seq, eval_seq, eval_forN, eval_forN]
  rw [decodeClauseWithLengthPrefixAt_eq cursorReg doneReg remainingReg lengthReg boundReg
    bound σ hb hbd hbl]
  set τ0 := (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
  have hbτ0 : τ0 boundReg = bound := by
    have hfr := decodeClauseWithLengthPrefixAt_bound_frame cursorReg doneReg remainingReg
      lengthReg boundReg σ hbc hbd hbl hbr
    have heq := decodeClauseWithLengthPrefixAt_eq cursorReg doneReg remainingReg lengthReg
      boundReg bound σ hb hbd hbl
    exact (heq ▸ hfr).trans hb
  set τ1 := (Program.assign satReg (.const 0)).eval τ0
  have hbτ1 : τ1 boundReg = bound := by
    simp only [τ1, eval_assign, Expr.eval]
    exact (writeReg_diff τ0 satReg 0 boundReg hbs).trans hbτ0
  simp only [Expr.eval]
  exact decodeClauseEvalStepAt_loopEval_eq cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg boundReg bound (τ1 remainingReg) τ1 hbτ1
    hbc hbp hbv hbd hbr hbs hbb hbval

end NPComplete.CookLevin

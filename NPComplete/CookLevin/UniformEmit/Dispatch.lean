module

public import NPComplete.CookLevin.UniformEmit.SplitTailTransport

/-!
# Clause dispatch programs

Emission chooses among short-clause cases and the split-tail path at runtime. This module assembles
those branches into reusable programs so their behavior can be proved separately from the
relational transport lemmas.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF)


/-! ## Second-pass rewind / startup with a bound register and a runtime start -/

def secondPassRewindProgramAt
    (cursorReg inputBaseReg outerReg doneReg boundReg : ℕ) : Program :=
  .seq (.assign cursorReg (.reg inputBaseReg))
    (.seq (.assign doneReg (.const 0))
      (.seq (.assign outerReg (.const 0))
        (decodeNatProgramAt cursorReg outerReg doneReg boundReg)))

lemma secondPassRewindProgramAt_eq
    (cursorReg inputBaseReg outerReg doneReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbo : boundReg ≠ outerReg) :
    (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ =
      (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ := by
  unfold secondPassRewindProgramAt secondPassRewindProgram
  rw [eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_seq]
  set σ0 := (Program.assign cursorReg (.reg inputBaseReg)).eval σ
  have hσ0 : σ0 boundReg = bound := by
    simp only [σ0, eval_assign, Expr.eval]
    exact (writeReg_diff σ cursorReg _ boundReg hbc).trans hb
  set σ1 := (Program.assign doneReg (.const 0)).eval σ0
  have hσ1 : σ1 boundReg = bound := by
    simp only [σ1, eval_assign, Expr.eval]
    exact (writeReg_diff σ0 doneReg 0 boundReg hbd).trans hσ0
  set σ2 := (Program.assign outerReg (.const 0)).eval σ1
  have hσ2 : σ2 boundReg = bound := by
    simp only [σ2, eval_assign, Expr.eval]
    exact (writeReg_diff σ1 outerReg 0 boundReg hbo).trans hσ1
  exact decodeNatProgramAt_eq cursorReg outerReg doneReg boundReg bound σ2 hσ2

def secondPassStartupProgramAt
    (cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ : ℕ)
    (startE : Expr) (numVarsReg clauseCountReg : ℕ) : Program :=
  .seq (secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg)
    (.seq (ctlAssign curJ startE)
      (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg))

lemma secondPassStartupProgramAt_eq
    (cursorReg inputBaseReg outerReg doneReg boundReg bound curJ tmpJ start : ℕ)
    (startE : Expr) (numVarsReg clauseCountReg : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbo : boundReg ≠ outerReg)
    (hstart : startE.eval
        ((secondPassRewindProgramAt cursorReg inputBaseReg outerReg doneReg boundReg).eval σ) =
      start) :
    (secondPassStartupProgramAt cursorReg inputBaseReg outerReg doneReg boundReg curJ tmpJ
      startE numVarsReg clauseCountReg).eval σ =
      (secondPassStartupProgram cursorReg inputBaseReg outerReg doneReg bound curJ tmpJ start
        numVarsReg clauseCountReg).eval σ := by
  unfold secondPassStartupProgramAt secondPassStartupProgram
  rw [eval_seq, eval_seq, eval_seq, eval_seq,
    secondPassRewindProgramAt_eq cursorReg inputBaseReg outerReg doneReg boundReg bound σ
      hb hbc hbd hbo]
  set τ := (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ
  have hτ : startE.eval τ = start := by
    have heq := secondPassRewindProgramAt_eq cursorReg inputBaseReg outerReg doneReg boundReg
      bound σ hb hbc hbd hbo
    simpa [heq] using hstart
  have hctl : (ctlAssign curJ startE).eval τ = (ctlAssign curJ (.const start)).eval τ := by
    simp [ctlAssign, eval_assignInd, hτ, Expr.eval]
  rw [hctl]

/-! ## Dispatch / iteration with a bound register; tail loop is dynamic -/

def splitTailEmitLongClauseSetupAt
    (curJ tmpJ cursorReg _polReg _varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg : ℕ) : Program :=
  .seq
    (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
    (.seq
      (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
      (.seq
        (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
          posPolReg freshReg)
        (.seq
          (.assign carryPolReg (.const 1))
          (.seq
            (.assign carryValReg (.reg freshReg))
            (.seq
              (.assign freshReg (.add (.reg freshReg) (.const 1)))
              (.seq
                (.assign remainingReg (.sub (.reg remainingReg) (.const 2)))
                (.skip)))))))

def splitTailEmitLongClauseProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg : ℕ) : Program :=
  .seq
    (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
    (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
       pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)

def emitClauseDispatchProgAtWithLong (longProg : Program)
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) : Program :=
  .ifNZ (.eq (.reg lengthReg) (.const 0))
    (.seq
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
      (.seq (emitClauseEmptyFreshProg freshReg)
        (emitClauseCommitProg outerReg)))
    (.ifNZ (.eq (.reg lengthReg) (.const 1))
      (.seq
        (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (.seq
          (writerAppendClauseOneProg curJ tmpJ polReg varReg)
          (emitClauseCommitProg outerReg)))
      (.ifNZ (.eq (.reg lengthReg) (.const 2))
        (.seq
          (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
          (.seq
            (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
            (.seq
              (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
              (emitClauseCommitProg outerReg))))
        (.ifNZ (.eq (.reg lengthReg) (.const 3))
          (.seq
            (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
            (.seq
              (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
              (.seq
                (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
                (.seq
                  (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
                    pol3Reg var3Reg posPolReg negPolReg freshReg)
                  (.seq (emitClauseEmptyFreshProg freshReg)
                    (emitClauseCommitProg outerReg))))))
          (.seq
            (.assign remainingReg (.reg lengthReg))
            (.seq
              (.assign carryPolReg (.const 1))
              (.seq
                (.assign carryValReg (.reg freshReg))
                (.seq
                  (.assign posPolReg (.const 0))
                  (.seq
                    longProg
                     (emitClauseCommitProg outerReg)))))))))

def emitClauseDispatchProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) : Program :=
  emitClauseDispatchProgAtWithLong
    (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
    curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg boundReg

def emitClauseProgramAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) : Program :=
  .seq (decodeNatProgramAt cursorReg lengthReg doneReg boundReg)
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg)

def emitClauseIterProgramAt
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) : Program :=
  .seq (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg)
    (emitClauseResetProg lengthReg doneReg)

end NPComplete.CookLevin

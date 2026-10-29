module

public import NPComplete.CookLevin.UniformEmit.SplitTailScratch

/-!
# Runtime Split-Tail Loop Programs

`splitTailEmitProgAt` is the register-driven split-tail loop: it samples the remaining count from
its register once at entry, so the loop bound needs no separate parameter. This module proves that
its step, terminal, and intermediate programs agree with their fixed-bound counterparts
(`splitTailEmitStepProg`, `splitTailEmitTerminalOneProg`, `splitTailEmitTerminalTwoProg`,
`splitTailEmitIntermediateProg`) whenever the bound register holds the bound, and gives the
loop's evaluation as iterates of the step program. This lets the invariants on the cursor,
carry, and writer state be proved once for the fixed-bound form; the agreement of the whole loop
(`splitTailEmitProgAt_eval_of_rel`) is in `SplitTailTransport.lean`.
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


/-- Register-driven split-tail loop: sample `remainingReg + 1` once at entry. -/
def splitTailEmitProgAt
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) : Program :=
  .ifNZ (.eq (.reg remainingReg) (.const 0))
    (splitTailEmitTerminalZeroProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg boundReg)
    (.forN (.add (.reg remainingReg) (.const 1))
       (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
         pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg))

lemma splitTailEmitProgAt_pos_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg k : ℕ) (σ : Store)
    (hrem : σ remainingReg = k) (hk : 0 < k) :
    (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        (k + 1) σ := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [splitTailEmitProgAt, eval_ifNZ, Expr.eval, hrem, hk0, eval_forN]

lemma splitTailEmitProg_pos_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound k : ℕ) (σ : Store)
    (hrem : σ remainingReg = k) (hk : 0 < k) :
    (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound).eval σ =
      loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        (tailBound + 1) σ := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [splitTailEmitProg, eval_ifNZ, Expr.eval, hrem, hk0, eval_forN]

lemma splitTailEmitTerminalOneProgAt_eq
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg carryPolReg
      carryValReg posPolReg freshReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ pol2Reg)
    (hbv : boundReg ≠ var2Reg) (hbd : boundReg ≠ doneReg) :
    (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  unfold splitTailEmitTerminalOneProgAt splitTailEmitTerminalOneProg
  have h := decodeLiteralValueProgramAt_eq cursorReg pol2Reg var2Reg doneReg boundReg bound σ
    hb hbc hbp hbv hbd
  simp [eval_seq, h]

lemma splitTailEmitIntermediateProgAt_eq
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  unfold splitTailEmitIntermediateProgAt splitTailEmitIntermediateProg
  have h := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
    hb hbc hbp hbv hbd
  simp [eval_seq, h]

lemma splitTailEmitTerminalTwoProgAt_eq
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp2 : boundReg ≠ pol2Reg)
    (hbv2 : boundReg ≠ var2Reg) (hbd : boundReg ≠ doneReg)
    (hbp3 : boundReg ≠ pol3Reg) (hbv3 : boundReg ≠ var3Reg) :
    (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  unfold splitTailEmitTerminalTwoProgAt splitTailEmitTerminalTwoProg
  rw [eval_seq, eval_seq]
  have h1 := decodeLiteralValueProgramAt_eq cursorReg pol2Reg var2Reg doneReg boundReg bound σ
    hb hbc hbp2 hbv2 hbd
  rw [h1]
  set τ := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ
  have hbτ : τ boundReg = bound := by
    have hfr := decodeLiteralValueProgramAt_bound_frame cursorReg pol2Reg var2Reg doneReg
      boundReg σ hbc hbp2 hbv2 hbd
    exact (h1 ▸ hfr).trans hb
  have h2 := decodeLiteralValueProgramAt_eq cursorReg pol3Reg var3Reg doneReg boundReg bound τ
    hbτ hbc hbp3 hbv3 hbd
  simp [eval_seq, h2, τ]

lemma splitTailEmitStepProgAt_eq
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbp2 : boundReg ≠ pol2Reg) (hbv2 : boundReg ≠ var2Reg)
    (hbp3 : boundReg ≠ pol3Reg) (hbv3 : boundReg ≠ var3Reg) :
    (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  simp only [splitTailEmitStepProgAt, splitTailEmitStepProg, eval_ifNZ]
  split_ifs
  · rfl
  · exact splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg bound σ
      hb hbc hbp2 hbv2 hbd
  · exact splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound σ hb hbc hbp2 hbv2 hbd hbp3 hbv3
  · exact splitTailEmitIntermediateProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg boundReg bound σ
      hb hbc hbp hbv hbd

lemma splitTailEmitStepProgAt_zero_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) (σ : Store)
    (hrem : σ remainingReg = 0) :
    (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      σ := by
  simp [splitTailEmitStepProgAt, hrem, Expr.eval]

lemma splitTailEmitStepProgAt_zero_loop
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) (σ : Store) (n : ℕ)
    (hrem : σ remainingReg = 0) :
    loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      n σ = σ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [loopEval_succ, splitTailEmitStepProgAt_zero_eval curJ tmpJ cursorReg polReg varReg
        doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg σ hrem, ih]

lemma splitTailEmitStepProgAt_loopEval_of_zero
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound n : ℕ) (σ : Store)
    (hrem : σ remainingReg = 0) :
    loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        n σ =
      loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        n σ := by
  rw [splitTailEmitStepProgAt_zero_loop curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg σ n hrem,
    splitTailEmitStepProg_zero_loop curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound σ n hrem]

end NPComplete.CookLevin

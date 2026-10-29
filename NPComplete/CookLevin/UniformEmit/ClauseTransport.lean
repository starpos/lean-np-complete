module

public import NPComplete.CookLevin.UniformEmit.TopLevel

/-!
# Clause program transport

Short clauses and split-tail long clauses follow different programs but must expose one semantic
interface to the outer loop. This module proves their normalized evaluation and frame behavior
under that shared relation so the producer can compose all cases uniformly.
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


/-! ## Long-clause / dispatch / iteration transport -/

structure EmitClauseBoundRegOk
    (boundReg start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg : ℕ) : Prop where
  split : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
  ne_length : boundReg ≠ lengthReg
  ne_outer : boundReg ≠ outerReg
  ne_neg_pol : boundReg ≠ negPolReg

lemma splitTailEmitLongClauseSetupAt_eq
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbp2 : boundReg ≠ pol2Reg) (hbv2 : boundReg ≠ var2Reg)
    (hbp3 : boundReg ≠ pol3Reg) (hbv3 : boundReg ≠ var3Reg) :
    (splitTailEmitLongClauseSetupAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  unfold splitTailEmitLongClauseSetupAt splitTailEmitLongClauseSetup
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

lemma splitTailEmitLongClauseProgAt_eval_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ []) (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
      M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hbsetup :
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
        boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        bound tailBound).eval σ := by
  have hsetup := splitTailEmitLongClauseSetupAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound σ hb hok.ne_cursor hok.ne_done hok.ne_pol2 hok.ne_var2 hok.ne_pol3 hok.ne_var3
  unfold splitTailEmitLongClauseProgAt splitTailEmitLongClauseProg
  rw [eval_seq, eval_seq, hsetup]
  exact splitTailEmitProgAt_eval_of_rel M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound tailBound base carry ls pref tail addr
    ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    hbound hne hls hrel hbsetup hok

lemma emitClauseDispatchProgAt_zero_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) (σ : Store)
    (hlen : σ lengthReg = 0) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (Program.seq (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
        (Program.seq (emitClauseEmptyFreshProg freshReg)
          (emitClauseCommitProg outerReg))).eval σ := by
  simp [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, hlen, Expr.eval]

lemma emitClauseDispatchProgAt_one_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) (σ : Store)
    (hlen : σ lengthReg = 1) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (writerAppendClauseOneProg curJ tmpJ polReg varReg)
          (emitClauseCommitProg outerReg))).eval σ := by
  simp [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, hlen, Expr.eval]

lemma emitClauseDispatchProgAt_two_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) (σ : Store)
    (hlen : σ lengthReg = 2) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
          (Program.seq (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
            (emitClauseCommitProg outerReg)))).eval σ := by
  simp [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, hlen, Expr.eval]

lemma emitClauseDispatchProgAt_three_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) (σ : Store)
    (hlen : σ lengthReg = 3) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
        (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
          (Program.seq (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
            (Program.seq (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
              pol3Reg var3Reg posPolReg negPolReg freshReg)
              (Program.seq (emitClauseEmptyFreshProg freshReg)
                (emitClauseCommitProg outerReg)))))).eval σ := by
  simp [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, hlen, Expr.eval]

lemma emitClauseDispatchProgAt_long_eval
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg : ℕ) (σ : Store)
    (hlen : 4 ≤ σ lengthReg) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (Program.seq (.assign remainingReg (.reg lengthReg))
        (Program.seq (.assign carryPolReg (.const 1))
          (Program.seq (.assign carryValReg (.reg freshReg))
            (Program.seq (.assign posPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg
                  remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                  posPolReg freshReg boundReg)
                (emitClauseCommitProg outerReg)))))).eval σ := by
  have h0 : σ lengthReg ≠ 0 := by omega
  have h1 : σ lengthReg ≠ 1 := by omega
  have h2 : σ lengthReg ≠ 2 := by omega
  have h3 : σ lengthReg ≠ 3 := by omega
  simp [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, h0, h1, h2, h3, Expr.eval]

lemma emitClauseDispatchProgAt_zero_eq
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 0) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  rw [emitClauseDispatchProgAt_zero_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg σ hlen,
    emitClauseDispatchProg_zero_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ hlen]

lemma emitClauseDispatchProgAt_one_eq
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 1) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  rw [emitClauseDispatchProgAt_one_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg σ hlen,
    emitClauseDispatchProg_one_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ hlen]
  have h := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
    hb hbc hbp hbv hbd
  simp [eval_seq, h]

lemma emitClauseDispatchProgAt_two_eq
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 2) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbp2 : boundReg ≠ pol2Reg) (hbv2 : boundReg ≠ var2Reg) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  rw [emitClauseDispatchProgAt_two_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg σ hlen,
    emitClauseDispatchProg_two_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ hlen]
  rw [eval_seq, eval_seq]
  have h1 := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
    hb hbc hbp hbv hbd
  rw [h1]
  set τ := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ
  have hbτ : τ boundReg = bound := by
    have hfr := decodeLiteralValueProgramAt_bound_frame cursorReg polReg varReg doneReg
      boundReg σ hbc hbp hbv hbd
    exact (h1 ▸ hfr).trans hb
  have h2 := decodeLiteralValueProgramAt_eq cursorReg pol2Reg var2Reg doneReg boundReg bound τ
    hbτ hbc hbp2 hbv2 hbd
  simp [eval_seq, h2, τ]

lemma emitClauseDispatchProgAt_three_eq
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hlen : σ lengthReg = 3) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbp2 : boundReg ≠ pol2Reg) (hbv2 : boundReg ≠ var2Reg)
    (hbp3 : boundReg ≠ pol3Reg) (hbv3 : boundReg ≠ var3Reg) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  rw [emitClauseDispatchProgAt_three_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg σ hlen,
    emitClauseDispatchProg_three_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ hlen]
  rw [eval_seq, eval_seq]
  have h1 := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
    hb hbc hbp hbv hbd
  rw [h1]
  set τ := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ
  have hbτ : τ boundReg = bound := by
    have hfr := decodeLiteralValueProgramAt_bound_frame cursorReg polReg varReg doneReg
      boundReg σ hbc hbp hbv hbd
    exact (h1 ▸ hfr).trans hb
  rw [eval_seq, eval_seq]
  have h2 := decodeLiteralValueProgramAt_eq cursorReg pol2Reg var2Reg doneReg boundReg bound τ
    hbτ hbc hbp2 hbv2 hbd
  rw [h2]
  set υ := (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval τ
  have hbυ : υ boundReg = bound := by
    have hfr := decodeLiteralValueProgramAt_bound_frame cursorReg pol2Reg var2Reg doneReg
      boundReg τ hbc hbp2 hbv2 hbd
    exact (h2 ▸ hfr).trans hbτ
  have h3 := decodeLiteralValueProgramAt_eq cursorReg pol3Reg var3Reg doneReg boundReg bound υ
    hbυ hbc hbp3 hbv3 hbd
  simp [eval_seq, h3, υ, τ]

lemma emitClauseDispatchProgAt_long_eq
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hlen : 4 ≤ σ lengthReg)
    (hlong :
      (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval
        ((Program.seq (.assign remainingReg (.reg lengthReg))
          (Program.seq (.assign carryPolReg (.const 1))
            (Program.seq (.assign carryValReg (.reg freshReg))
              (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ) =
        (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          bound tailBound).eval
          ((Program.seq (.assign remainingReg (.reg lengthReg))
            (Program.seq (.assign carryPolReg (.const 1))
              (Program.seq (.assign carryValReg (.reg freshReg))
                (Program.seq (.assign posPolReg (.const 0)) (.skip))))).eval σ)) :
    (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  rw [emitClauseDispatchProgAt_long_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg boundReg σ hlen,
    emitClauseDispatchProg_long_eval curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound σ hlen]
  simp only [eval_seq, eval_skip] at hlong ⊢
  exact congrArg (emitClauseCommitProg outerReg).eval hlong

lemma emitClauseIterProgramAt_eq_of
    (curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg bound tailBound : ℕ) (σ : Store)
    (hprog :
      (emitClauseProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg boundReg).eval σ =
        (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
          freshReg outerReg bound tailBound).eval σ) :
    (emitClauseIterProgramAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg boundReg).eval σ =
      (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ := by
  unfold emitClauseIterProgramAt emitClauseIterProgram
  simp [eval_seq, hprog]

end NPComplete.CookLevin

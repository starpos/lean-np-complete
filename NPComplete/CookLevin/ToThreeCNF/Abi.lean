module

public import NPComplete.CookLevin.ToThreeCNF.CNFEmitCons

/-!
# Parser-emitter interface

The bounded input decoder and second-pass writer exchange clause counts, cursor
positions, and output state, so their boundary must be explicit before the
compiled programs can be composed. This module packages that interface and
proves the decoder and startup states satisfy the clause-emission relation.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
  (BitsFrom bitsFrom_append bitsFrom_writeReg bitsFrom_of_eq_on BitsAt bitsAt_of_frame finalizeOutputProg FinalizeRegsOk ctlCell ctlCell_eval)
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same cost_seq
    cost_ifNZ cost_forN eval_ifNZ eval_forN loopEval loopEval_succ
    loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

/-! ## Output ABI adapter

The writer invariant gives bitness of the emitted range, while the generic ABI finalizer publishes
the range in cells `outAddrCell`/`outLenCell`.  This theorem is intentionally independent of the
top-level scanner: it is the reusable boundary theorem needed once a caller has arranged the two
metadata registers.  In particular, it does not assert that the current bounded parser computes a
runtime output length.
-/

open NPComplete.RAMToTM.Generic (ReductionOutput outAddrCell outLenCell)

lemma reductionOutput_of_writerState
    (outBaseReg outLenReg M curJ start : ℕ) (bits : Bits) (σ : Store)
    (hs : WriterState σ M curJ start bits)
    (hbase : σ outBaseReg = start) (hlen : σ outLenReg = bits.length)
    (hok : FinalizeRegsOk outBaseReg outLenReg) (hstart : 2 ≤ start) :
    ReductionOutput
      ((finalizeOutputProg outBaseReg outLenReg).eval σ) start bits.length := by
  have hbits : ∀ i < σ outLenReg, σ (σ outBaseReg + i) = 0 ∨ σ (σ outBaseReg + i) = 1 := by
    rw [hbase, hlen]
    intro i hi
    have hb := hs.bits i hi
    cases hbit : bits[i] with
    | false => exact Or.inl (by simpa [hbit] using hb)
    | true => exact Or.inr (by simpa [hbit] using hb)
  have hstart' : 2 ≤ σ outBaseReg := by rw [hbase]; exact hstart
  simpa [hbase, hlen] using
    (NPComplete.RAMToTM.reductionOutput_of_finalize outBaseReg outLenReg σ hok hbits
      hstart')

lemma reductionOutput_of_writerState_abiSuffix
    (outBaseReg outLenReg M curJ start : ℕ) (bits : Bits) (σ : Store)
    (hs : WriterState σ M curJ start bits)
    (hbaseLow : outBaseReg < start) (hlenLow : outLenReg < start)
    (houtNe : outBaseReg ≠ outLenReg)
    (hok : FinalizeRegsOk outBaseReg outLenReg) (hstart : 2 ≤ start) :
    ReductionOutput
      ((Program.seq (Program.assign outBaseReg (.const start))
        (Program.seq (Program.assign outLenReg (.sub (ctlCell curJ) (.const start)))
          (finalizeOutputProg outBaseReg outLenReg))).eval σ)
      start bits.length := by
  have hbase0 : outBaseReg ≠ 0 := by
    simpa [outAddrCell] using hok.1
  have hlen0 : outLenReg ≠ 0 := by
    simpa [outAddrCell] using hok.2.2.1
  have hbaseL : outBaseReg ≠ outLenReg := houtNe
  have hlenBase : outLenReg ≠ outBaseReg := Ne.symm hbaseL
  have hMcurJ : start + bits.length < M + curJ := hs.safe
  let σb := (Program.assign outBaseReg (.const start)).eval σ
  have hbaseFrame (r : ℕ) (hr : r ≠ outBaseReg) : σb r = σ r := by
    simp only [σb, eval_assign, Expr.eval]
    exact writeReg_diff σ outBaseReg start r hr
  have hbaseWrite : σb outBaseReg = start := by
    simp [σb, eval_assign, Expr.eval]
  have hlenEval : (Expr.sub (ctlCell curJ) (.const start)).eval σb = bits.length := by
    simp only [Expr.eval, ctlCell_eval]
    rw [hbaseFrame 0 (Ne.symm hbase0), hs.root, hbaseFrame (M + curJ) (by omega), hs.cursor]
    omega
  let σl := (Program.assign outLenReg (.sub (ctlCell curJ) (.const start))).eval σb
  have hlenFrame (r : ℕ) (hr : r ≠ outLenReg) : σl r = σb r := by
    simp only [σl, eval_assign, Expr.eval]
    exact writeReg_diff σb outLenReg _ r hr
  have hbaseLval : σl outBaseReg = start := by
    rw [hlenFrame outBaseReg hbaseL]
    exact hbaseWrite
  have hlenLval : σl outLenReg = bits.length := by
    rw [show σl outLenReg =
      (Expr.sub (ctlCell curJ) (.const start)).eval σb by
        simp [σl, eval_assign, Expr.eval]]
    exact hlenEval
  have hrootL : σl 0 = M := by
    rw [hlenFrame 0 (Ne.symm hlen0), hbaseFrame 0 (Ne.symm hbase0)]
    exact hs.root
  have hcursorL : σl (M + curJ) = start + bits.length := by
    rw [hlenFrame (M + curJ) (by omega), hbaseFrame (M + curJ) (by omega)]
    exact hs.cursor
  have hbitsL : BitsAt σl start bits := by
    intro i hi
    rw [hlenFrame (start + i) (by omega), hbaseFrame (start + i) (by omega)]
    exact hs.bits i hi
  have hsL : WriterState σl M curJ start bits :=
    { root := hrootL, cursor := hcursorL, bits := hbitsL
      start_pos := hs.start_pos, safe := hs.safe }
  have hfinal := reductionOutput_of_writerState outBaseReg outLenReg M curJ start bits σl hsL
    hbaseLval hlenLval hok hstart
  simpa [σl, σb, eval_seq] using hfinal

/-! Construct the outer relation from the state produced by the startup/header
    program.  Keeping this bridge independent of the concrete register layout
    lets the scanner and the startup machine be instantiated separately. -/
lemma cnfEmitRel_of_startup_state
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (clauses : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hstate : CNFEmissionState σ M curJ start pref cursorReg outerReg freshReg
      addr clauses.length base)
    (hinput : BitsFrom σ addr ((clauses.map encodeClause).flatten ++ tail))
    (hlength : σ lengthReg = 0) (hdone : σ doneReg = 0)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (hlongSafety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg
      doneReg outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hcapacity : start + pref.length +
      (encodeThreeClausesPayload (clausesToThree base clauses).1).length + 2 < M + curJ)
    (hclauseBound : ∀ c ∈ clauses, c.lits.length + 1 ≤ bound)
    (hliteralBound : ∀ c ∈ clauses, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (htailBound : ∀ c ∈ clauses, c.lits.length ≤ tailBound) :
    CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base clauses tail pref addr σ := by
  exact {
    input := hinput
    cursor := hstate.input_cursor
    outer := hstate.clauses_remaining
    fresh := hstate.fresh_counter
    length_zero := hlength
    done_zero := hdone
    pos := hpos
    neg := hneg
    writer := hstate.writer
    capacity := hcapacity
    input_above := hinputAbove
    start_at_input := hstartAtInput
    safety := hsafety
    long_safety := hlongSafety
    clause_bound := hclauseBound
    literal_bound := hliteralBound
    tail_bound_ok := htailBound }

/-! The decoder leaves `doneReg = 1` as its successful-stop marker.  The
    clause emitter boundary uses zero instead, so this wrapper performs the
    small reset before exposing the relation. -/
lemma cnfEmitRel_after_startup_reset
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (clauses : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hstate : CNFEmissionState σ M curJ start pref cursorReg outerReg freshReg
      addr clauses.length base)
    (hinput : BitsFrom σ addr ((clauses.map encodeClause).flatten ++ tail))
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hresetAbove : lengthReg < addr ∧ doneReg < addr)
    (hsafety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
      outerReg freshReg posPolReg negPolReg)
    (hlongSafety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg
      doneReg outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hcapacity : start + pref.length +
      (encodeThreeClausesPayload (clausesToThree base clauses).1).length + 2 < M + curJ)
    (hclauseBound : ∀ c ∈ clauses, c.lits.length + 1 ≤ bound)
    (hliteralBound : ∀ c ∈ clauses, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (htailBound : ∀ c ∈ clauses, c.lits.length ≤ tailBound) :
    CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base clauses tail pref addr
      ((emitClauseResetProg lengthReg doneReg).eval σ) := by
  have hwriter := emitClauseResetProg_writer M curJ start lengthReg doneReg pref σ
    hstate.writer hsafety.length_below hsafety.done_below
    hsafety.length_nonzero hsafety.done_nonzero
    (ClauseEmitSafety.ne_of_pair hsafety (by simp [clauseEmitPairs]))
  have hframe {r : ℕ} (hrl : r ≠ lengthReg) (hrd : r ≠ doneReg) :
      (emitClauseResetProg lengthReg doneReg).eval σ r = σ r :=
    emitClauseResetProg_frame lengthReg doneReg σ hrl hrd
  have hinput' : BitsFrom ((emitClauseResetProg lengthReg doneReg).eval σ) addr
      ((clauses.map encodeClause).flatten ++ tail) := by
    intro i hi
    rw [hframe (by omega) (by omega)]
    exact hinput i hi
  have hcursor' :
      (emitClauseResetProg lengthReg doneReg).eval σ cursorReg = addr := by
    rw [hframe (Ne.symm (ClauseEmitSafety.ne_of_pair hsafety (by simp [clauseEmitPairs])))
      (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))]
    exact hstate.input_cursor
  have houter' :
      (emitClauseResetProg lengthReg doneReg).eval σ outerReg = clauses.length := by
    rw [hframe (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))
      (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))]
    exact hstate.clauses_remaining
  have hfresh' :
      (emitClauseResetProg lengthReg doneReg).eval σ freshReg = base := by
    rw [hframe (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))
      (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))]
    exact hstate.fresh_counter
  have hpos' :
      (emitClauseResetProg lengthReg doneReg).eval σ posPolReg = 0 := by
    rw [hframe (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))
      (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))]
    exact hpos
  have hneg' :
      (emitClauseResetProg lengthReg doneReg).eval σ negPolReg = 1 := by
    rw [hframe (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))
      (by exact hsafety.ne_of_pair (by simp [clauseEmitPairs]))]
    exact hneg
  have hlen' :
      (emitClauseResetProg lengthReg doneReg).eval σ lengthReg = 0 := by
    have hneLD : lengthReg ≠ doneReg := hsafety.ne_of_pair (by simp [clauseEmitPairs])
    rw [emitClauseResetProg_eval, writeReg_diff _ doneReg 0 lengthReg hneLD, writeReg_same]
  have hdone' :
      (emitClauseResetProg lengthReg doneReg).eval σ doneReg = 0 := by
    rw [emitClauseResetProg_eval, writeReg_same]
  refine cnfEmitRel_of_startup_state M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base clauses tail pref addr
    ((emitClauseResetProg lengthReg doneReg).eval σ)
    { writer := hwriter, input_cursor := hcursor', clauses_remaining := houter',
      fresh_counter := hfresh' } hinput' hlen' hdone' hpos' hneg' hinputAbove
    hstartAtInput hsafety hlongSafety hcapacity hclauseBound hliteralBound htailBound

lemma splitTailEmitStepProg_zero_loop
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) (σ : Store) (k : ℕ)
    (hrem : σ remainingReg = 0) :
    loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      k σ = σ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ]
      rw [splitTailEmitStepProg_zero_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound σ hrem]
      exact ih

lemma splitTail_loopEval_add_right (body : Program) (n k : ℕ) (σ : Store) :
    loopEval body (n + k) σ = loopEval body k (loopEval body n σ) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [show n + k.succ = (n + k) + 1 by omega, loopEval_succ_right_local,
        ih, ← loopEval_succ_right_local]

lemma splitTailEmitProg_pad_after_zero
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (σ : Store) (n k : ℕ)
    (hrem : (loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      n σ) remainingReg = 0) :
    loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      (n + k) σ =
      loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
          pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        n σ := by
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  rw [splitTail_loopEval_add_right body n k σ]
  exact splitTailEmitStepProg_zero_loop curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    (loopEval body n σ) k hrem


end NPComplete.CookLevin

module

public import NPComplete.CookLevin.NatParser.Stats
public import NPComplete.BoundedWhile.Frame

/-!
An outer CNF scanner must decode each clause's length prefix before scanning its
literals, so it can initialize the scan and update clause statistics. This module
provides that prefix stage, the fixed-bound clause and CNF steps, the register-driven
CNF scanner, and their evaluation and cost lemmas.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr cost_forN loopCost loopCost_le_of_body_le
    eval_seq eval_assign eval_ifNZ eval_forN loopEval loopEval_succ cost_seq cost_assign
    writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_length)
open NPComplete.SAT (Literal encodeLiteral)

def decodeClauseWithLengthPrefix
    (cursorReg doneReg remainingReg lengthReg bound : ℕ) : Program :=
  .seq (.assign doneReg (.const 0))
      <| .seq (.assign lengthReg (.const 0))
        <| .seq (decodeNatProgram cursorReg lengthReg doneReg bound)
        <| .seq (.assign doneReg (.const 0))
          (.assign remainingReg (.reg lengthReg))

def decodeClauseWithLengthProgram
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound clauseBound : ℕ) :
    Program :=
  .seq (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound)
    (.forN (.const clauseBound)
      (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound))

/-- Dynamic counterpart of `decodeClauseWithLengthProgram`.  The register-driven `forN` reads
    `remainingReg` once at loop entry, after the length prefix has been decoded; the body retains
    the same decrement and zero guard as the fixed-bound scanner. -/
def decodeClauseWithLengthProgramDynamic
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound : ℕ) : Program :=
  .seq (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound)
    (.forN (.reg remainingReg)
      (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound))

lemma decodeClauseWithLengthProgramDynamic_eq_fixed_of_prefix
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg bound n : ℕ) (σ : Store)
    (hprefix : (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval
      σ remainingReg = n) :
    (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound).eval σ =
      (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg bound n).eval σ := by
  unfold decodeClauseWithLengthProgramDynamic decodeClauseWithLengthProgram
  rw [eval_seq, eval_seq, eval_forN, eval_forN]
  simp only [Expr.eval]
  rw [hprefix]

lemma decodeClauseWithLengthPrefix_remaining_eval
    (cursorReg doneReg remainingReg lengthReg bound addr : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hlc : lengthReg ≠ cursorReg)
    (hld : lengthReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ doneReg < addr ∧ lengthReg < addr)
    (hc : σ cursorReg = addr)
    (hbound : xs.length + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest)) :
    (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
      remainingReg = xs.length := by
  have hshape : encodeList encodeLiteral xs ++ rest =
      encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  have hbitsOrig := hbits
  rw [hshape] at hbits
  let σ0 := (Program.assign doneReg (.const 0)).eval σ
  have hσ0done : σ0 doneReg = 0 := by
    simp [σ0, eval_assign, Expr.eval, writeReg_same]
  have hσ0frame : ∀ r, r ≠ doneReg → σ0 r = σ r := by
    intro r hr
    simp [σ0, eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  have hbits0 : BitsFrom σ0 addr
      (encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest)) := by
    intro i hi
    rw [hσ0frame _ (by omega)]
    exact hbits i hi
  let σlen := (Program.assign lengthReg (.const 0)).eval σ0
  have hlen0 : σlen lengthReg = 0 := by
    simp [σlen, eval_assign, Expr.eval, writeReg_same]
  have hσlenFrame : ∀ r, r ≠ lengthReg → σlen r = σ0 r := by
    intro r hr
    simp [σlen, eval_assign, Expr.eval, writeReg_diff _ lengthReg _ r hr]
  have hσlendone : σlen doneReg = 0 :=
    (hσlenFrame doneReg (Ne.symm hld)).trans hσ0done
  have hbitsLen : BitsFrom σlen addr
      (encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest)) := by
    intro i hi
    rw [hσlenFrame _ (by omega)]
    exact hbits0 i hi
  have hbitsLenOrig : BitsFrom σlen addr (encodeList encodeLiteral xs ++ rest) := by
    intro i hi
    rw [hσlenFrame _ (by omega), hσ0frame _ (by omega)]
    exact hbitsOrig i hi
  have hclen : σlen cursorReg = addr :=
    (hσlenFrame cursorReg (Ne.symm hlc)).trans
      ((hσ0frame cursorReg hcd).trans hc)
  obtain ⟨_, hlen, _, _⟩ :=
    decodeNatProgram_encodeList_length_append encodeLiteral cursorReg lengthReg doneReg bound
      addr 0 xs rest σlen (Ne.symm hlc) hcd hld hbound hbelow.1 hbelow.2.2 hbelow.2.1
      hclen hlen0 hσlendone hbitsLenOrig
  let σ1 := (decodeNatProgram cursorReg lengthReg doneReg bound).eval σlen
  have hlen1 : σ1 lengthReg = xs.length := by simpa using hlen
  let σ2 := (Program.assign doneReg (.const 0)).eval σ1
  have hlen2 : σ2 lengthReg = xs.length := by
    simp [σ2, eval_assign, Expr.eval, writeReg_diff _ doneReg _ lengthReg hld, hlen1]
  let σ3 := (Program.assign remainingReg (.reg lengthReg)).eval σ2
  have hrem3 : σ3 remainingReg = xs.length := by
    simp [σ3, eval_assign, Expr.eval, writeReg_same, hlen2]
  simpa [decodeClauseWithLengthPrefix, eval_seq, σ0, σlen, σ1, σ2, σ3] using hrem3

def clauseStatsProgram
    (clauseLenReg freshReg countReg _tmpReg : ℕ) : Program :=
  .ifNZ (.eq (.reg clauseLenReg) (.const 0))
    (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
      (.assign countReg (.add (.reg countReg) (.const 2))))
    (.ifNZ (.eq (.reg clauseLenReg) (.const 1))
      (.assign countReg (.add (.reg countReg) (.const 1)))
      (.ifNZ (.eq (.reg clauseLenReg) (.const 2))
        (.assign countReg (.add (.reg countReg) (.const 1)))
        (.ifNZ (.eq (.reg clauseLenReg) (.const 3))
          (.seq (.assign freshReg (.add (.reg freshReg) (.const 1)))
            (.assign countReg (.add (.reg countReg) (.const 2))))
          (.seq (.assign freshReg
                    (.add (.reg freshReg) (.sub (.reg clauseLenReg) (.const 3))))
            (.assign countReg
              (.add (.reg countReg) (.sub (.reg clauseLenReg) (.const 2))))))))

def decodeCNFClauseStepWithStats
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound clauseBound : ℕ) : Program :=
  .seq (decodeClauseWithLengthProgram cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound clauseBound)
    (clauseStatsProgram lengthReg freshReg countReg tmpReg)

def decodeCNFStep
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg bound clauseBound : ℕ) : Program :=
  .seq (decodeCNFClauseStepWithStats cursorReg polReg varReg doneReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg bound clauseBound)
    (.assign outerReg (.sub (.reg outerReg) (.const 1)))

/-! Dynamic CNF scanner.  The clause counter is decoded into `outerReg`; `forN` samples that
counter once and each step decrements it, so the loop terminates exactly after the encoded number
of clauses.  The per-clause literal counter is likewise register-driven by the dynamic clause
scanner above. -/

def decodeCNFClauseStepWithStatsDynamic
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      bound : ℕ) : Program :=
  .seq (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg bound)
    (clauseStatsProgram lengthReg freshReg countReg tmpReg)

def decodeCNFStepDynamic
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg bound : ℕ) : Program :=
  .seq (decodeCNFClauseStepWithStatsDynamic cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg bound)
    (.assign outerReg (.sub (.reg outerReg) (.const 1)))

lemma clauseStatsProgram_outputs
    (clauseLenReg freshReg countReg tmpReg n base c : ℕ) (σ : Store)
    (hcf : clauseLenReg ≠ freshReg) (hcc : clauseLenReg ≠ countReg)
    (hct : clauseLenReg ≠ tmpReg) (hfc : freshReg ≠ countReg)
    (hft : freshReg ≠ tmpReg) (hct' : countReg ≠ tmpReg)
    (hlen : σ clauseLenReg = n) (hbase : σ freshReg = base)
    (hcount : σ countReg = c) :
    (clauseStatsProgram clauseLenReg freshReg countReg tmpReg).eval σ freshReg =
        base + clauseFreshIncByLength n ∧
    (clauseStatsProgram clauseLenReg freshReg countReg tmpReg).eval σ countReg =
        c + clauseThreeCountByLength n := by
  have hcfR := Ne.symm hcf
  have hccR := Ne.symm hcc
  have hctR := Ne.symm hct
  have hfcR := Ne.symm hfc
  have hftR := Ne.symm hft
  have hctR' := Ne.symm hct'
  cases n with
  | zero =>
      simp_all [clauseStatsProgram, eval_ifNZ, eval_assign, Expr.eval,
        writeReg, clauseFreshIncByLength, clauseThreeCountByLength]
  | succ n =>
      cases n with
      | zero =>
          simp_all [clauseStatsProgram, eval_ifNZ, eval_assign, Expr.eval,
            writeReg, clauseFreshIncByLength, clauseThreeCountByLength]
      | succ n =>
          cases n with
          | zero =>
              simp_all [clauseStatsProgram, eval_ifNZ, eval_assign, Expr.eval,
                writeReg, clauseFreshIncByLength, clauseThreeCountByLength]
          | succ n =>
              cases n with
              | zero =>
                  simp_all [clauseStatsProgram, eval_ifNZ, eval_assign, Expr.eval,
                    writeReg, clauseFreshIncByLength, clauseThreeCountByLength]
              | succ n =>
                  simp_all [clauseStatsProgram, eval_ifNZ, eval_assign, Expr.eval,
                    writeReg, clauseFreshIncByLength, clauseThreeCountByLength]

lemma clauseStatsProgram_frame
    (clauseLenReg freshReg countReg tmpReg : ℕ) (σ : Store) (r : ℕ)
    (hrf : r ≠ freshReg) (hrn : r ≠ countReg) :
    (clauseStatsProgram clauseLenReg freshReg countReg tmpReg).eval σ r = σ r := by
  have hAvoids : (clauseStatsProgram clauseLenReg freshReg countReg tmpReg).Avoids
      (fun r => r ≠ freshReg ∧ r ≠ countReg) := by
    simp [Program.Avoids, clauseStatsProgram]
  exact hAvoids.eval_frame σ ⟨hrf, hrn⟩

lemma loopEval_succ_right_local (body : Program) (k : ℕ) (σ : Store) :
    loopEval body (k + 1) σ = body.eval (loopEval body k σ) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ, ih (body.eval σ), loopEval_succ]

lemma loopEval_add_right_local (body : Program) (a b : ℕ) (σ : Store) :
    loopEval body (a + b) σ = loopEval body b (loopEval body a σ) := by
  induction b generalizing σ with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        loopEval_succ_right_local, ih, loopEval_succ_right_local]

lemma decodeClauseStep_loop_zero_local
    (cursorReg polReg varReg doneReg remainingReg maxReg bound k : ℕ) (σ : Store)
    (hrem : σ remainingReg = 0) :
    loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound) k σ = σ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ, decodeClauseStep_zero cursorReg polReg varReg doneReg remainingReg maxReg
        bound σ hrem]
      exact ih

end NPComplete.CookLevin

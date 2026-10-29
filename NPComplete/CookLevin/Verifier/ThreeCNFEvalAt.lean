module

public import NPComplete.CookLevin.Verifier.ClauseEvalAt
public import NPComplete.CookLevin.Verifier.CNFEval
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatDecodePhase

/-!
`threeSAT_inNP`'s machine half needs a RAM evaluator for `ThreeCNF` satisfiability against a
certificate, mirroring `CNFEvalAt.lean`'s `decodeCNFEvalProgramAt` for the unbounded-width
`CNF` type.  A `ThreeClause` fixes its arity at `3` (`l1`/`l2`/`l3`), unlike `Clause`'s
`List Literal`, so no length-prefixed clause decode (`decodeClauseWithLengthPrefixAt`) or
per-clause `.forN` loop is needed: `decodeThreeClauseEvalStepAt` runs the register-bound
literal-eval step `decodeClauseEvalStepAt` (`ClauseEvalAt.lean`) exactly three times, reusing
`ClauseEval.lean`'s already-proven `decode_clause_eval_loop_eval` at the concrete list
`c.literals` (definitionally length `3`) instead of re-deriving the literal loop.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length)
open NPComplete.SAT (Literal ThreeClause encodeLiteral encodeThreeClause)

/-- Decode-and-evaluate a fixed-arity `ThreeClause`: seed the OR-accumulator `satReg` at
    `0`, drive `remainingReg` to `3`, and run the register-bound literal-eval loop
    `decodeClauseEvalStepAt` three times. -/
def decodeThreeClauseEvalStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      boundReg : ℕ) : Program :=
  .seq (.assign remainingReg (.const 3))
    <| .seq (.assign satReg (.const 0))
      (.forN (.const 3)
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg boundReg))

/-- Runs the two register seeds at the front of `decodeThreeClauseEvalStepAt`
    (`remainingReg := 3`, `satReg := 0`) and transports every fact the loop bridge needs
    (`cursorReg`/`boundReg`/`wBaseReg` values, the clause's bit window, and the certificate
    bits at each of `c`'s three variables) across that prelude, together with frame
    preservation for every other register. -/
lemma decodeThreeClauseEvalStepAt_prelude
    (cursorReg remainingReg satReg boundReg wBaseReg addr bound wBase : ℕ)
    (c : ThreeClause) (rest : Bits) (σ : Store)
    (hsr : satReg ≠ remainingReg) (hrc : remainingReg ≠ cursorReg) (hsc : satReg ≠ cursorReg)
    (hbr0 : boundReg ≠ remainingReg) (hbs0 : boundReg ≠ satReg)
    (hwr : wBaseReg ≠ remainingReg) (hsw : satReg ≠ wBaseReg)
    (hrA : remainingReg < addr) (hsA : satReg < addr)
    (hrW : remainingReg < wBase) (hsW : satReg < wBase)
    (hc : σ cursorReg = addr) (hb : σ boundReg = bound) (hwbase : σ wBaseReg = wBase)
    (hbits : BitsFrom σ addr (encodeThreeClause c ++ rest))
    (w : List Bool)
    (hwbits : (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) remainingReg = 3) ∧
    ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) satReg = 0) ∧
    ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) cursorReg = addr) ∧
    ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) boundReg = bound) ∧
    ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) wBaseReg = wBase) ∧
    BitsFrom ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ)) addr (encodeThreeClause c ++ rest) ∧
    (((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) (wBase + c.l1.var) =
      if w.getD c.l1.var false then 1 else 0) ∧
     ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) (wBase + c.l2.var) =
      if w.getD c.l2.var false then 1 else 0) ∧
     ((Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) (wBase + c.l3.var) =
      if w.getD c.l3.var false then 1 else 0)) ∧
    (∀ r, r ≠ remainingReg → r ≠ satReg →
      (Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) r = σ r) := by
  have hframe1 : ∀ r, r ≠ remainingReg → r ≠ satReg →
      (Program.assign satReg (.const 0)).eval
        ((Program.assign remainingReg (.const 3)).eval σ) r = σ r := by
    intro r h1 h2
    simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ r h2, writeReg_diff _ remainingReg _ r h1]
  refine ⟨?_, ?_, (hframe1 cursorReg hrc.symm hsc.symm).trans hc,
    (hframe1 boundReg hbr0 hbs0).trans hb, (hframe1 wBaseReg hwr hsw.symm).trans hwbase,
    fun i hi => (hframe1 (addr + i) (by omega) (by omega)).trans (hbits i hi),
    ⟨(hframe1 _ (by omega) (by omega)).trans hwbits.1,
      (hframe1 _ (by omega) (by omega)).trans hwbits.2.1,
      (hframe1 _ (by omega) (by omega)).trans hwbits.2.2⟩,
    hframe1⟩
  · simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ remainingReg hsr.symm, writeReg_same]
  · simp [eval_assign, Expr.eval, writeReg_same]

/-- Correctness of `decodeThreeClauseEvalStepAt`: decoding a `ThreeClause`'s three literals
    off the cursor and folding their evaluated Boolean values against certificate `w` leaves
    `satReg` holding `c.is_satisfied (decodeAssignment w)`'s Boolean value, `cursorReg` past
    the clause's whole encoding, and `wBaseReg`/every other register frame-preserved.
    Delegates to `decode_clause_eval_loop_eval` (`ClauseEval.lean`) at the concrete literal list
    `c.literals`, bridged from the register-driven `decodeClauseEvalStepAt` to the
    constant-bound `decodeClauseEvalStep` via `decodeClauseEvalStepAt_loopEval_eq`
    (`ClauseEvalAt.lean`). -/
lemma decodeThreeClauseEvalStepAt_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
      addr bound wBase : ℕ) (c : ThreeClause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg) (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hbc0 : boundReg ≠ cursorReg) (hbp0 : boundReg ≠ polReg) (hbv0 : boundReg ≠ varReg)
    (hbd0 : boundReg ≠ doneReg) (hbr0 : boundReg ≠ remainingReg) (hbs0 : boundReg ≠ satReg)
    (hbbit0 : boundReg ≠ bitReg) (hbval0 : boundReg ≠ valReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hb : σ boundReg = bound)
    (hbound : c.l1.var + 1 ≤ bound ∧ c.l2.var + 1 ≤ bound ∧ c.l3.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeClause c ++ rest))
    (w : List Bool)
    (hwbits : (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg).eval σ cursorReg = addr + (encodeThreeClause c).length ∧
    (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg).eval σ satReg =
      (if c.is_satisfied (decodeAssignment w) then 1 else 0) ∧
    (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg).eval σ wBaseReg = wBase ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → r ≠ remainingReg →
      r ≠ satReg → r ≠ bitReg → r ≠ valReg →
      (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg).eval σ r = σ r) := by
  unfold decodeThreeClauseEvalStepAt
  rw [eval_seq, eval_seq, eval_forN]
  obtain ⟨h1rem, h1sat, h1cur, h1bound, h1wbase, h1bits, ⟨h1wbits1, h1wbits2, h1wbits3⟩, hframe1⟩ :=
    decodeThreeClauseEvalStepAt_prelude cursorReg remainingReg satReg boundReg wBaseReg addr
      bound wBase c rest σ hsr hrc hsc hbr0 hbs0 hwr hsw hbelow.2.2.2.2.1
      hbelow.2.2.2.2.2.1 hbelowW.2.2.2.2.1 hbelowW.2.2.2.2.2.1 hc hb hwbase hbits w hwbits
  set σ1 := (Program.assign satReg (.const 0)).eval
    ((Program.assign remainingReg (.const 3)).eval σ) with hσ1
  simp only [Expr.eval]
  rw [decodeClauseEvalStepAt_loopEval_eq cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg boundReg bound 3 σ1 h1bound hbc0 hbp0 hbv0 hbd0 hbr0 hbs0 hbbit0 hbval0]
  have hbitsL : BitsFrom σ1 addr ((c.literals.map encodeLiteral).flatten ++ rest) := by
    simpa [ThreeClause.literals, encodeThreeClause] using h1bits
  have hboundL : ∀ l ∈ c.literals, l.var + 1 ≤ bound := by
    intro l hl
    simp only [ThreeClause.literals, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact hbound.1
    · exact hbound.2.1
    · exact hbound.2.2
  have hwbitsL : ∀ l ∈ c.literals, σ1 (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro l hl
    simp only [ThreeClause.literals, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact h1wbits1
    · exact h1wbits2
    · exact h1wbits3
  have hlen3 : c.literals.length = 3 := rfl
  have hloop := decode_clause_eval_loop_eval cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg bound addr 0 wBase c.literals rest σ1
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl
    hsc hsp hsv hsd hsr hsb hsl hsw
    hbelowW ⟨hbelow.1, hbelow.2.1, hbelow.2.2.1, hbelow.2.2.2.1, hbelow.2.2.2.2.1,
      hbelow.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.2.2⟩
    hWA (by rw [hlen3]; exact h1rem) h1sat (Or.inl rfl) h1wbase hboundL h1cur hbitsL w hwbitsL
  rw [hlen3] at hloop
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hloop.1]; simp [ThreeClause.literals, encodeThreeClause]
  · rw [hloop.2.2.1]
    congr 1
    simp only [eq_iff_iff, ThreeClause.is_satisfied, ThreeClause.literals, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    cases c.l1.eval (decodeAssignment w) <;> cases c.l2.eval (decodeAssignment w) <;>
      cases c.l3.eval (decodeAssignment w) <;> simp
  · rw [hloop.2.2.2 wBaseReg hwc hwp hwv hwd hwr hsw.symm hwb hwl, h1wbase]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [hloop.2.2.2 r h1 h2 h3 h4 h5 h6 h7 h8, hframe1 r h5 h6]

end NPComplete.CookLevin

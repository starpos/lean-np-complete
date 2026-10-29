module

public import NPComplete.CookLevin.Verifier.ClauseLengthEvalAt
public import NPComplete.CookLevin.Verifier.CNFEval
public import NPComplete.BoundedWhile.Frame

/-!
`decodeCNFEvalClauseStep` folds `decodeClauseEvalWithLengthProgram`'s per-clause result
into an AND-accumulator, but that clause evaluator bakes its unary bound in as a
compile-time `.const`.  This module is the register-driven-bound counterpart,
`decodeCNFEvalClauseStepAt`, built from `decodeClauseEvalWithLengthProgramAt`
(`ClauseLengthEvalAt.lean`).  The new content is the AND-accumulator step with its loop
bridge to `decodeCNFEvalClauseStep`, and the top-level evaluator `decodeCNFEvalProgramAt`
(clause-count decode, then a `forN` over that step) with its evaluation lemma
`decodeCNFEvalProgramAt_eval`; the length-prefix/literal-loop machinery is fully reused.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

/-- Register-driven-bound counterpart of `decodeCNFEvalClauseStep`: decode one
    length-prefixed clause via `decodeClauseEvalWithLengthProgramAt` and AND its Boolean
    value into `cnfReg`. -/
def decodeCNFEvalClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) : Program :=
  .seq (decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg boundReg)
    (andIntoProg satReg cnfReg)

/-- `decodeCNFEvalClauseStepAt` agrees with `decodeCNFEvalClauseStep` at the matching
    constant bound. -/
lemma decodeCNFEvalClauseStepAt_eq
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg bound : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbs : boundReg ≠ satReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg) :
    (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg lengthReg cnfReg boundReg).eval σ =
      (decodeCNFEvalClauseStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg bound).eval σ := by
  unfold decodeCNFEvalClauseStepAt decodeCNFEvalClauseStep
  rw [eval_seq, eval_seq]
  rw [decodeClauseEvalWithLengthProgramAt_eq cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg lengthReg boundReg bound σ hb hbc hbp hbv hbd hbl hbr hbs hbb hbval]

lemma decodeCNFEvalClauseStepAt_avoids_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) :
    (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg lengthReg cnfReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ satReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧
        r ≠ lengthReg ∧ r ≠ cnfReg) := by
  simp [Program.Avoids, decodeCNFEvalClauseStepAt, decodeClauseEvalWithLengthProgramAt,
    decodeClauseWithLengthPrefixAt, decodeClauseEvalStepAt, decodeNatProgramAt,
    decodeLiteralValueProgramAt, decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg,
    readAssignBitProg, andIntoProg, literalValueProg, orIntoProg]

/-- `decodeCNFEvalClauseStepAt` never disturbs `boundReg`. -/
lemma decodeCNFEvalClauseStepAt_bound_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbs : boundReg ≠ satReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbk : boundReg ≠ cnfReg) :
    (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg lengthReg cnfReg boundReg).eval σ boundReg = σ boundReg := by
  exact (decodeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg).eval_frame σ
    ⟨hbc, hbp, hbv, hbd, hbr, hbs, hbb, hbval, hbl, hbk⟩

/-- Iterating `decodeCNFEvalClauseStepAt` agrees with iterating `decodeCNFEvalClauseStep`
    at the matching constant bound, for any iteration count. -/
lemma decodeCNFEvalClauseStepAt_loopEval_eq
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg bound k : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg)
    (hbs : boundReg ≠ satReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbk : boundReg ≠ cnfReg) :
    loopEval
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg)
        k σ =
      loopEval
        (decodeCNFEvalClauseStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg bound)
        k σ := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      have hstep := decodeCNFEvalClauseStepAt_eq cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg bound σ hb
        hbc hbp hbv hbd hbl hbr hbs hbb hbval
      have hb' := decodeCNFEvalClauseStepAt_bound_frame cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg σ
        hbc hbp hbv hbd hbl hbr hbs hbb hbval hbk
      rw [loopEval_succ, loopEval_succ, hstep]
      apply ih
      exact hstep ▸ hb'.trans hb

/-- Register-driven-bound counterpart of `decodeNatProgram_encodeList_length_append`
    (`NatParser/Foundation.lean`), mirroring `decodeNatProgramAt_encodeNat_append`
    (`UniformDecode.lean`) at an `encodeList`-shaped prefix. -/
lemma decodeNatProgramAt_encodeList_length_append
    {α : Type} (enc : α → Bits)
    (cursorReg countReg doneReg boundReg bound addr c0 : ℕ) (xs : List α) (rest : Bits)
    (σ : Store) (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hkd : countReg ≠ doneReg)
    (hbound : xs.length + 1 ≤ bound) (hb : σ boundReg = bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeList enc xs ++ rest)) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ cursorReg =
        addr + xs.length + 1 ∧
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ countReg = c0 + xs.length ∧
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ r = σ r) := by
  have hshape : encodeList enc xs ++ rest =
      encodeNat xs.length ++ ((xs.map enc).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  rw [hshape] at hbits
  exact decodeNatProgramAt_encodeNat_append cursorReg countReg doneReg boundReg xs.length bound
    addr c0 ((xs.map enc).flatten ++ rest) σ hcc hcd hkd hbound hb hca hka hda hc hk hd hbits

/-- Register-driven-bound top-level CNF evaluator: decode the clause-count prefix
    (bound sampled from `boundReg`), then loop `decodeCNFEvalClauseStepAt` over the
    decoded count, folding the AND-accumulator `cnfReg` (seeded at `1`) across every
    clause. The outer shape is the clause-count decode followed by a `forN` over the decoded
    count, with `decodeCNFEvalClauseStepAt` as the body. -/
def decodeCNFEvalProgramAt
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) : Program :=
  .seq (.assign doneReg (.const 0))
    <| .seq (.assign outerReg (.const 0))
      <| .seq (decodeNatProgramAt cursorReg outerReg doneReg boundReg)
        (.forN (.reg outerReg)
          (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
            valReg wBaseReg lengthReg cnfReg boundReg))

/-- Correctness of `decodeCNFEvalProgramAt`: decoding the clause-count prefix off
    `encodeList encodeClause cs ++ rest` and then folding `decodeCNFEvalClauseStepAt`
    over the decoded clauses leaves `cnfReg` holding `cnfSatBool w ⟨cs⟩`'s Boolean value.
    `outerReg` is below `wBase` (`houterW`); the cursor, literal, loop-state, length,
    and CNF registers have separate bounds there. This keeps those control registers
    outside the witness-bit area during clause-count decoding and clause iteration. -/
lemma decodeCNFEvalProgramAt_eval
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg addr wBase bound : ℕ) (cs : List Clause) (rest : Bits)
    (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg) (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg) (hwlen : wBaseReg ≠ lengthReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
    (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hkl : cnfReg ≠ lengthReg)
    (hbboc : boundReg ≠ cursorReg) (hbbop : boundReg ≠ polReg) (hbbov : boundReg ≠ varReg)
    (hbbod : boundReg ≠ doneReg) (hbbor : boundReg ≠ remainingReg) (hbbos : boundReg ≠ satReg)
    (hbbob : boundReg ≠ bitReg) (hbboval : boundReg ≠ valReg) (hbbol : boundReg ≠ lengthReg)
    (hbbok : boundReg ≠ cnfReg) (hbboo : boundReg ≠ outerReg)
    (houtc : outerReg ≠ cursorReg) (houtd : outerReg ≠ doneReg)
    (houtk : outerReg ≠ cnfReg) (houtw : outerReg ≠ wBaseReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hlenW : lengthReg < wBase) (hcnfregW : cnfReg < wBase)
    (houterW : outerReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      lengthReg < addr ∧ cnfReg < addr ∧ boundReg < addr ∧ outerReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hcnf0 : σ cnfReg = 1) (hb : σ boundReg = bound)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeList encodeClause cs ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ cs, ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (decodeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg
      valReg wBaseReg lengthReg cnfReg boundReg).eval σ cnfReg =
      (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) := by
  unfold decodeCNFEvalProgramAt
  rw [eval_seq, eval_seq, eval_seq, eval_forN]
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
  have hσ0done : σ0 doneReg = 0 := by rw [hσ0def]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ0frame : ∀ r, r ≠ doneReg → σ0 r = σ r := by
    intro r hr; rw [hσ0def]; simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  set σ1 := (Program.assign outerReg (.const 0)).eval σ0 with hσ1def
  have hσ1out : σ1 outerReg = 0 := by rw [hσ1def]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ1frame : ∀ r, r ≠ outerReg → σ1 r = σ0 r := by
    intro r hr; rw [hσ1def]; simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ r hr]
  have hσ1cur : σ1 cursorReg = addr :=
    (hσ1frame cursorReg houtc.symm).trans ((hσ0frame cursorReg hcd).trans hc)
  have hσ1done : σ1 doneReg = 0 := (hσ1frame doneReg houtd.symm).trans hσ0done
  have hσ1bound : σ1 boundReg = bound :=
    (hσ1frame boundReg hbboo).trans ((hσ0frame boundReg hbbod).trans hb)
  have hσ1sat0 : σ1 cnfReg = 1 :=
    (hσ1frame cnfReg houtk.symm).trans ((hσ0frame cnfReg hkd).trans hcnf0)
  have hσ1wbase : σ1 wBaseReg = wBase :=
    (hσ1frame wBaseReg houtw.symm).trans ((hσ0frame wBaseReg hwd).trans hwbase)
  have hbits1 : BitsFrom σ1 addr (encodeList encodeClause cs ++ rest) := by
    intro i hi
    rw [hσ1frame _ (by omega), hσ0frame _ (by omega)]
    exact hbits i hi
  obtain ⟨hcur2, hout2, hdone2, hframe2⟩ := decodeNatProgramAt_encodeList_length_append
    encodeClause cursorReg outerReg doneReg boundReg bound addr 0 cs rest σ1
    houtc.symm hcd houtd hbound hσ1bound hbelow.1
    hbelow.2.2.2.2.2.2.2.2.2.2.2.2 hbelow.2.2.2.1 hσ1cur hσ1out hσ1done hbits1
  set σ2 := (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval σ1 with hσ2def
  have hout2' : σ2 outerReg = cs.length := by simpa using hout2
  simp only [Expr.eval, hout2']
  have hσ2cur : σ2 cursorReg = addr + cs.length + 1 := hcur2
  have hσ2bound : σ2 boundReg = bound := (hframe2 boundReg hbboc hbboo hbbod).trans hσ1bound
  have hσ2sat0 : σ2 cnfReg = 1 := (hframe2 cnfReg hkc houtk.symm hkd).trans hσ1sat0
  have hσ2wbase : σ2 wBaseReg = wBase := (hframe2 wBaseReg hwc houtw.symm hwd).trans hσ1wbase
  have hbits2 : BitsFrom σ2 (addr + cs.length + 1) ((cs.map encodeClause).flatten ++ rest) := by
    intro i hi
    have hfr := hframe2 (addr + cs.length + 1 + i) (by omega) (by omega) (by omega)
    rw [hfr]
    obtain ⟨_, htail⟩ := bitsFrom_append σ1 addr (encodeNat cs.length)
      ((cs.map encodeClause).flatten ++ rest) (by
        have hshape : encodeList encodeClause cs ++ rest =
            encodeNat cs.length ++ ((cs.map encodeClause).flatten ++ rest) := by
          simp [encodeList, List.append_assoc]
        rw [← hshape]; exact hbits1)
    have heq : addr + cs.length + 1 + i = addr + (encodeNat cs.length).length + i := by
      rw [encodeNat_length]; omega
    rw [heq]
    exact htail i hi
  have hwbits2 : ∀ c ∈ cs, ∀ l ∈ c.lits,
      σ2 (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro c hc' l hl
    have hne1 : wBase + l.var ≠ cursorReg := by have := hbelowW.1; omega
    have hne2 : wBase + l.var ≠ outerReg := by have := houterW; omega
    have hne3 : wBase + l.var ≠ doneReg := by have := hbelowW.2.2.2.1; omega
    rw [hframe2 (wBase + l.var) hne1 hne2 hne3]
    have hσ0wl : σ0 (wBase + l.var) = σ (wBase + l.var) := hσ0frame _ hne3
    have hσ1wl : σ1 (wBase + l.var) = σ0 (wBase + l.var) := hσ1frame _ hne2
    rw [hσ1wl, hσ0wl]
    exact hwbits c hc' l hl
  rw [decodeCNFEvalClauseStepAt_loopEval_eq cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg lengthReg cnfReg boundReg bound cs.length σ2 hσ2bound
    hbboc hbbop hbbov hbbod hbbol hbbor hbbos hbbob hbboval hbbok]
  have hbelow' : cursorReg < addr + cs.length + 1 ∧ polReg < addr + cs.length + 1 ∧
      varReg < addr + cs.length + 1 ∧ doneReg < addr + cs.length + 1 ∧
      remainingReg < addr + cs.length + 1 ∧ satReg < addr + cs.length + 1 ∧
      bitReg < addr + cs.length + 1 ∧ valReg < addr + cs.length + 1 ∧
      wBaseReg < addr + cs.length + 1 ∧ lengthReg < addr + cs.length + 1 ∧
      cnfReg < addr + cs.length + 1 :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  have hWA' : wBase < addr + cs.length + 1 := by omega
  have hloop := decode_cnf_eval_clause_loop_eval cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg cnfReg bound (addr + cs.length + 1) 1 wBase cs rest σ2
      hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr hvc hvr
      hwc hwp hwv hwd hwr hwb hwl hwlen hsc hsp hsv hsd hsr hsb hsl hsw
      hlc hld hkc hkp hkv hkd hkr hks hkb hkval hkw hkl
      hbelowW hlenW hcnfregW hbelow'
      hWA' hσ2wbase hσ2sat0 (Or.inr rfl) hbound2 hvarbound hσ2cur hbits2 w hwbits2
  simpa using hloop.2

end NPComplete.CookLevin

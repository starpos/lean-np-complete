module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck
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

The At-variant programs are written once against the role-indexed register assignment of
`CNFEval.lean` (the `...L` definitions); the numbered programs are the same trees at plain
numbers.  The stage contracts of the clause step, the clause loop and the whole evaluator
are stated over the layout (`LayoutStage`), and the numbered correctness lemmas follow.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip ReadsOnly)
open NPComplete.BoundedWhile (RegLayout LayoutFact)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

stage_default boundary

/-- Register-driven-bound counterpart of `decodeCNFEvalClauseStep`: decode one
    length-prefixed clause via `decodeClauseEvalWithLengthProgramAt` and AND its Boolean
    value into `cnfReg` — the one place the At clause step's syntax tree is written. -/
def decodeCNFEvalClauseStepAtL (reg : CNFEvalRole → ℕ) : Program :=
  .seq (decodeClauseEvalWithLengthProgramAtL reg .cursor .pol .var .done .remaining .sat .bit
      .val .wBase .length .bound)
    (andIntoProgL reg)

/-- Numbered form of `decodeCNFEvalClauseStepAtL` (the same tree at plain numbers). -/
def decodeCNFEvalClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) : Program :=
  decodeCNFEvalClauseStepAtL
    (fun
      | .cursor => cursorReg
      | .pol => polReg
      | .var => varReg
      | .done => doneReg
      | .remaining => remainingReg
      | .sat => satReg
      | .bit => bitReg
      | .val => valReg
      | .wBase => wBaseReg
      | .length => lengthReg
      | .cnf => cnfReg
      | .bound => boundReg
      | _ => 0)

/-- `decodeCNFEvalClauseStepAt` agrees with `decodeCNFEvalClauseStep` at the matching
    constant bound. -/
@[stage_impl] lemma decodeCNFEvalClauseStepAt_eq
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
  change ((decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg lengthReg boundReg).seq
      (andIntoProg satReg cnfReg)).eval σ =
    ((decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound).seq (andIntoProg satReg cnfReg)).eval σ
  rw [eval_seq, eval_seq]
  rw [decodeClauseEvalWithLengthProgramAt_eq cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg lengthReg boundReg bound σ hb hbc hbp hbv hbd hbl hbr hbs hbb hbval]

@[stage_impl] lemma decodeCNFEvalClauseStepAt_avoids_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) :
    (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg lengthReg cnfReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ satReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧
        r ≠ lengthReg ∧ r ≠ cnfReg) := by
  change ((decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg lengthReg boundReg).seq
      (andIntoProg satReg cnfReg)).Avoids _
  simp [Program.Avoids, decodeClauseEvalWithLengthProgramAt,
    decodeClauseWithLengthPrefixAt, decodeClauseEvalStepAt, decodeNatProgramAt,
    decodeLiteralValueProgramAt, decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg,
    readAssignBitProg, andIntoProg, literalValueProg, orIntoProg]

/-- `decodeCNFEvalClauseStepAt` never disturbs `boundReg`. -/
@[stage_impl] lemma decodeCNFEvalClauseStepAt_bound_frame
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
@[stage_impl] lemma decodeCNFEvalClauseStepAt_loopEval_eq
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
@[stage_impl] lemma decodeNatProgramAt_encodeList_length_append
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
    (bound sampled from the `bound` role), then loop `decodeCNFEvalClauseStepAtL` over the
    decoded count, folding the AND-accumulator `cnf` (seeded at `1`) across every
    clause — the one place the evaluator's syntax tree is written. -/
def decodeCNFEvalProgramAtL (reg : CNFEvalRole → ℕ) : Program :=
  .seq (.assign (reg .done) (.const 0))
    <| .seq (.assign (reg .outer) (.const 0))
      <| .seq (decodeNatProgramAtL reg .cursor .outer .done .bound)
        (.forN (.reg (reg .outer)) (decodeCNFEvalClauseStepAtL reg))

/-- Numbered form of `decodeCNFEvalProgramAtL` (the same tree at plain numbers). -/
def decodeCNFEvalProgramAt
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) : Program :=
  decodeCNFEvalProgramAtL
    (fun
      | .cursor => cursorReg
      | .pol => polReg
      | .var => varReg
      | .done => doneReg
      | .outer => outerReg
      | .remaining => remainingReg
      | .sat => satReg
      | .bit => bitReg
      | .val => valReg
      | .wBase => wBaseReg
      | .length => lengthReg
      | .cnf => cnfReg
      | .bound => boundReg
      | _ => 0)

/-- Correctness of `decodeCNFEvalProgramAt`: decoding the clause-count prefix off
    `encodeList encodeClause cs ++ rest` and then folding `decodeCNFEvalClauseStepAt`
    over the decoded clauses leaves `cnfReg` holding `cnfSatBool w ⟨cs⟩`'s Boolean value.
    `outerReg` is below `wBase` (`houterW`); the cursor, literal, loop-state, length,
    and CNF registers have separate bounds there. This keeps those control registers
    outside the witness-bit area during clause-count decoding and clause iteration. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_eval
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
  change ((Program.assign doneReg (.const 0)).seq
      ((Program.assign outerReg (.const 0)).seq
        ((decodeNatProgramAt cursorReg outerReg doneReg boundReg).seq
          (Program.forN (.reg outerReg)
            (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
              bitReg valReg wBaseReg lengthReg cnfReg boundReg))))).eval σ cnfReg =
    (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0)
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
    apply bitsFrom_of_eq_on _ hbits
    intro i hi
    rw [hσ1frame _ (by omega), hσ0frame _ (by omega)]
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
    apply bitsFrom_of_eq_on _ (by
      simpa [encodeList, List.append_assoc, encodeNat_length, Nat.add_assoc] using
        (bitsFrom_append σ1 addr (encodeNat cs.length) ((cs.map encodeClause).flatten ++ rest)
          (by simpa [encodeList, List.append_assoc] using hbits1)).2)
    intro i hi
    exact hframe2 _ (by omega) (by omega) (by omega)
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

/-! ## Stage contracts

The clause step, the clause loop and the whole evaluator are published as bundled stages over
the layout: their boundaries name facts and footprints, never a raw store.  The resource
component (`ProgramBoundedIn`) is an explicit obligation of each contract, because the
verifier's resource lemmas live downstream of this module. -/

/-- The register roles the clause step reserves: the registers it writes plus the reserved
scratch role. -/
@[stage_boundary] def stepRegs : Finset CNFEvalRole :=
  {.cursor, .pol, .var, .done, .remaining, .sat, .bit, .val, .length, .cnf, .scratch}

/-- The register roles the whole evaluator reserves: the clause step's plus the count role. -/
@[stage_boundary] def progRegs : Finset CNFEvalRole :=
  {.cursor, .pol, .var, .done, .outer, .remaining, .sat, .bit, .val, .length, .cnf, .scratch}

/-- The registers the clause step writes. -/
@[stage_boundary] def stepFoot (R : RegLayout CNFEvalRole) : RegLayout.Foot R :=
  RegLayout.Foot.regsOnly stepRegs

/-- The registers the whole evaluator writes. -/
@[stage_boundary] def progFoot (R : RegLayout CNFEvalRole) : RegLayout.Foot R :=
  RegLayout.Foot.regsOnly progRegs

@[stage_impl] lemma ne_reg_of_not_mem_denote {R : RegLayout CNFEvalRole}
    {S : Finset CNFEvalRole} {r : ℕ} {role : CNFEvalRole}
    (hr : r ∉ ((RegLayout.Foot.regsOnly S : RegLayout.Foot R)).denote) (h : role ∈ S) :
    r ≠ R.reg role :=
  fun he => hr (he ▸ RegLayout.Foot.reg_mem_denote h)

@[stage_impl] lemma not_mem_denote_reg {R : RegLayout CNFEvalRole} {S : Finset CNFEvalRole}
    {role : CNFEvalRole} (h : role ∉ S) :
    (R.reg role) ∉ ((RegLayout.Foot.regsOnly S : RegLayout.Foot R)).denote := by
  intro hx
  rcases RegLayout.Foot.mem_denote.1 hx with ⟨r, hr, he⟩ | hm
  · exact h (R.reg_injective he ▸ hr)
  · simp at hm

/-- The clause step avoids everything outside its footprint. -/
@[stage_contract] lemma decodeCNFEvalClauseStepAtL_avoids (R : RegLayout CNFEvalRole) :
    (decodeCNFEvalClauseStepAtL R.reg).Avoids (· ∉ (stepFoot R).denote) := by
  have h := decodeCNFEvalClauseStepAt_avoids_frame (R.reg .cursor) (R.reg .pol) (R.reg .var)
    (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
    (R.reg .length) (R.reg .cnf) (R.reg .bound)
  refine Program.Avoids.mono h fun r hr => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ne_reg_of_not_mem_denote hr (by decide)

/-- The clause step as a bundled stage: one length-prefixed clause moves the loop invariant
one clause forward. -/
@[stage_contract] lemma decodeCNFEvalClauseStepAt_stage (R : RegLayout CNFEvalRole)
    (B addr v wBase bound : ℕ) (c : Clause) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound_c : c.lits.length + 1 ≤ bound)
    (hvarbound_c : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hbnd : ∀ σ,
      (clauseInvFact R addr v wBase bound (((c :: cs).map encodeClause).flatten ++ rest)
        (c :: cs) w haddr hb).holds σ →
        ProgramBoundedIn B σ (decodeCNFEvalClauseStepAtL R.reg)) :
    LayoutStage R B (decodeCNFEvalClauseStepAtL R.reg)
      (clauseInvFact R addr v wBase bound (((c :: cs).map encodeClause).flatten ++ rest)
        (c :: cs) w haddr hb)
      (clauseInvFact R (addr + (encodeClause c).length) (if clauseSatBool w c then v else 0)
        wBase bound ((cs.map encodeClause).flatten ++ rest) cs w (by omega) hb)
      (stepFoot R) := by
  refine LayoutStage.ofSpec ?_
  refine LayoutSpec.of_direct (decodeCNFEvalClauseStepAtL_avoids R) (fun σ hσ => ?_)
    (fun σ hσ => hbnd σ hσ)
  obtain ⟨hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
  have hσbound : σ (R.reg .bound) = bound := hbd
  change (clauseInvFact R (addr + (encodeClause c).length)
      (if clauseSatBool w c then v else 0) wBase bound ((cs.map encodeClause).flatten ++ rest)
      cs w (by omega) hb).holds
      ((decodeCNFEvalClauseStepAt (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
        (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
        (R.reg .length) (R.reg .cnf) (R.reg .bound)).eval σ)
  rw [decodeCNFEvalClauseStepAt_eq (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
    (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase) (R.reg .length)
    (R.reg .cnf) (R.reg .bound) bound σ hσbound
    (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
    (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
    (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))]
  obtain ⟨σ2, hσ2, hcur2, hwb2, hcnf2, hbits2, hwbits2⟩ :=
    decode_cnf_eval_clause_loop_eval_step (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) bound addr v wBase c cs
      ((cs.map encodeClause).flatten ++ rest) σ
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide))
      ⟨R.reg_lt_of_top_le .cursor hb, R.reg_lt_of_top_le .pol hb,
        R.reg_lt_of_top_le .var hb, R.reg_lt_of_top_le .done hb,
        R.reg_lt_of_top_le .remaining hb, R.reg_lt_of_top_le .sat hb,
        R.reg_lt_of_top_le .bit hb, R.reg_lt_of_top_le .val hb⟩
      (R.reg_lt_of_top_le .length hb) (R.reg_lt_of_top_le .cnf hb)
      ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr,
        R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr,
        R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr,
        R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr,
        R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .length haddr,
        R.reg_lt_of_top_le .cnf haddr⟩
      hWA hwb hcnf hbound_c hvarbound_c hcur
      (show BitsFrom σ addr (encodeClause c ++ ((cs.map encodeClause).flatten ++ rest)) from by
        rw [← List.append_assoc]; exact hbits) w
      (hwit c (by simp)) (fun cc hcc => hwit cc (by simp [hcc]))
  have hbound2 : σ2 (R.reg .bound) = bound := by
    rw [hσ2, ← decodeCNFEvalClauseStepAt_eq (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) (R.reg .bound) bound σ hσbound
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide)),
      decodeCNFEvalClauseStepAt_bound_frame (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) (R.reg .bound) σ
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide))]
    exact hσbound
  rw [← hσ2]
  exact ⟨hcur2, hcnf2, hwb2, hbound2, hbits2, hwbits2⟩

/-- The clause loop as a bundled stage: one iteration per clause folds every clause's
satisfaction value into the accumulator and leaves the input tail at `rest`. -/
@[stage_contract] lemma decodeCNFEvalClauseLoop_stage (R : RegLayout CNFEvalRole)
    (B addr v wBase bound : ℕ) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hs0 : v = 0 ∨ v = 1)
    (hbound : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hbnd : ∀ σ,
      (LayoutFact.bigAnd [LayoutFact.reg .outer cs.length,
        clauseInvFact R addr v wBase bound ((cs.map encodeClause).flatten ++ rest) cs w haddr
          hb]).holds σ →
        ProgramBoundedIn B σ
          (Program.forN (.reg (R.reg .outer)) (decodeCNFEvalClauseStepAtL R.reg))) :
    LayoutStage R B
      (Program.forN (.reg (R.reg .outer)) (decodeCNFEvalClauseStepAtL R.reg))
      (LayoutFact.bigAnd [LayoutFact.reg .outer cs.length,
        clauseInvFact R addr v wBase bound ((cs.map encodeClause).flatten ++ rest) cs w haddr
          hb])
      (LayoutFact.bigAnd [LayoutFact.reg .outer cs.length,
        clauseInvFact R (addr + (cs.map encodeClause).flatten.length)
          (if v = 1 ∧ ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) wBase bound rest [] w
          (by omega) hb])
      (stepFoot R) := by
  refine LayoutStage.ofSpec ?_
  refine LayoutSpec.of_direct (decodeCNFEvalClauseStepAtL_avoids R) (fun σ hσ => ?_)
    (fun σ hσ => hbnd σ hσ)
  obtain ⟨hcount, hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
  have hσbound : σ (R.reg .bound) = bound := hbd
  have hbridge : loopEval (decodeCNFEvalClauseStepAtL R.reg) cs.length σ =
      loopEval (decodeCNFEvalClauseStep (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
        (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
        (R.reg .length) (R.reg .cnf) bound) cs.length σ :=
    decodeCNFEvalClauseStepAt_loopEval_eq (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) (R.reg .bound) bound cs.length σ hσbound
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide))
  have hloop := decode_cnf_eval_clause_loop_eval_full (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) bound addr v wBase cs rest σ
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide))
      ⟨R.reg_lt_of_top_le .cursor hb, R.reg_lt_of_top_le .pol hb,
        R.reg_lt_of_top_le .var hb, R.reg_lt_of_top_le .done hb,
        R.reg_lt_of_top_le .remaining hb, R.reg_lt_of_top_le .sat hb,
        R.reg_lt_of_top_le .bit hb, R.reg_lt_of_top_le .val hb⟩
      (R.reg_lt_of_top_le .length hb) (R.reg_lt_of_top_le .cnf hb)
      ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr,
        R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr,
        R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr,
        R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr,
        R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .length haddr,
        R.reg_lt_of_top_le .cnf haddr⟩
      hWA hwb hcnf hs0 hbound hvarbound hcur hbits w hwit
  obtain ⟨hcur2, hcnf2, hwb2, hbits2⟩ := hloop
  have houterAt : (loopEval (decodeCNFEvalClauseStepAtL R.reg) cs.length σ) (R.reg .outer) =
      σ (R.reg .outer) :=
    Program.Avoids.loopEval_frame (decodeCNFEvalClauseStepAtL_avoids R)
      (not_mem_denote_reg (show (CNFEvalRole.outer : CNFEvalRole) ∉ stepRegs from by decide))
      cs.length σ
  have hboundAt : (loopEval (decodeCNFEvalClauseStepAtL R.reg) cs.length σ) (R.reg .bound) =
      σ (R.reg .bound) :=
    Program.Avoids.loopEval_frame (decodeCNFEvalClauseStepAtL_avoids R)
      (not_mem_denote_reg (show (CNFEvalRole.bound : CNFEvalRole) ∉ stepRegs from by decide))
      cs.length σ
  have houter : (loopEval (decodeCNFEvalClauseStep (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) bound) cs.length σ) (R.reg .outer) = cs.length := by
    rw [← hbridge, houterAt]
    exact hcount
  have hbound2 : (loopEval (decodeCNFEvalClauseStep (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
      (R.reg .length) (R.reg .cnf) bound) cs.length σ) (R.reg .bound) = bound := by
    rw [← hbridge, hboundAt]
    exact hσbound
  rw [eval_forN]
  simp only [Expr.eval]
  rw [hcount, hbridge]
  refine ⟨houter, hcur2, hcnf2, hwb2, hbound2, hbits2, ?_⟩
  intro cc hcc
  nomatch hcc

/-- The whole evaluator as a bundled stage: decode the clause-count prefix and fold every
clause into the accumulator, which holds the CNF's Boolean value at the end. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_stage (R : RegLayout CNFEvalRole)
    (B addr wBase bound : ℕ) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hbnd : ∀ σ,
      (clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr
        hb).holds σ →
        ProgramBoundedIn B σ (decodeCNFEvalProgramAtL R.reg)) :
    LayoutStage R B (decodeCNFEvalProgramAtL R.reg)
      (clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr hb)
      (LayoutFact.reg .cnf (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0))
      (progFoot R) := by
  refine LayoutStage.ofSpec ?_
  refine LayoutSpec.of_direct ?_ (fun σ hσ => ?_) (fun σ hσ => hbnd σ hσ)
  · have h : (decodeCNFEvalProgramAtL R.reg).Avoids
        (fun r => r ≠ R.reg .done ∧ r ≠ R.reg .outer ∧ r ≠ R.reg .cursor ∧ r ≠ R.reg .pol ∧
          r ≠ R.reg .var ∧ r ≠ R.reg .remaining ∧ r ≠ R.reg .sat ∧ r ≠ R.reg .bit ∧
          r ≠ R.reg .val ∧ r ≠ R.reg .length ∧ r ≠ R.reg .cnf) := by
      simp [Program.Avoids, decodeCNFEvalProgramAtL, decodeCNFEvalClauseStepAtL,
        decodeNatProgramAtL, decodeClauseEvalWithLengthProgramAtL, andIntoProgL,
        decodeClauseEvalWithLengthProgramAt, decodeClauseWithLengthPrefixAt,
        decodeClauseEvalStepAt, decodeNatProgramAt, decodeLiteralValueProgramAt,
        decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg, readAssignBitProg, andIntoProg,
        literalValueProg, orIntoProg]
    refine Program.Avoids.mono h fun r hr => ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact ne_reg_of_not_mem_denote hr (by decide)
  · obtain ⟨hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
    have h := decodeCNFEvalProgramAt_eval (R.reg .cursor) (R.reg .pol) (R.reg .var)
      (R.reg .done) (R.reg .outer) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val)
      (R.reg .wBase) (R.reg .length) (R.reg .cnf) (R.reg .bound) addr wBase bound cs rest σ
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide)) (R.reg_ne (by decide)) (R.reg_ne (by decide))
      (R.reg_ne (by decide))
      ⟨R.reg_lt_of_top_le .cursor hb, R.reg_lt_of_top_le .pol hb,
        R.reg_lt_of_top_le .var hb, R.reg_lt_of_top_le .done hb,
        R.reg_lt_of_top_le .remaining hb, R.reg_lt_of_top_le .sat hb,
        R.reg_lt_of_top_le .bit hb, R.reg_lt_of_top_le .val hb⟩
      (R.reg_lt_of_top_le .length hb) (R.reg_lt_of_top_le .cnf hb)
      (R.reg_lt_of_top_le .outer hb)
      ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr,
        R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr,
        R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr,
        R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr,
        R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .length haddr,
        R.reg_lt_of_top_le .cnf haddr, R.reg_lt_of_top_le .bound haddr,
        R.reg_lt_of_top_le .outer haddr⟩
      hWA hwb hcnf hbd hbound hbound2 hvarbound hcur hbits w hwit
    exact h

end NPComplete.CookLevin

#check_stage_discipline all

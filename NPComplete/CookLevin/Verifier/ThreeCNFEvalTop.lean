module

public import NPComplete.CookLevin.Verifier.ThreeCNFEval
public import NPComplete.CookLevin.Verifier.CNFEvalAt
public import NPComplete.SAT.ThreeCNFEncoding

/-!
The register-driven-bound top-level `ThreeCNF` evaluator, `decodeThreeCNFEvalProgramAt`, closing
`ThreeCNFEval.lean`'s per-clause fold against the whole formula: skip the `numVars` header (its
value is not needed for satisfaction, unlike `f.Bounded`'s var-bound argument, which the wiring
layer supplies separately), decode the clause-count prefix, then fold
`decodeThreeCNFEvalClauseStepAt` over the decoded clauses. Mirrors `CNFEvalAt.lean`'s
`decodeCNFEvalProgramAt`, with the extra leading `numVars`-skip stage `encodeThreeCNF`'s header
needs that `encodeCNF` does not.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip RegLayout)
open NPComplete.BitEncoding
  (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeThreeCNF encodeThreeClause)

/-- Register-driven-bound top-level `ThreeCNF` evaluator: skip the `numVars` header, decode
    the clause-count prefix (bound sampled from `boundReg`), then loop
    `decodeThreeCNFEvalClauseStepAt` over the decoded count, folding the AND-accumulator
    `cnfReg` (seeded at `1`) across every clause. -/
def decodeThreeCNFEvalProgramAt
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      cnfReg boundReg numVarsSkipReg : ℕ) : Program :=
  .seq (.assign doneReg (.const 0))
    <| .seq (.assign numVarsSkipReg (.const 0))
      <| .seq (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg)
        <| .seq (.assign doneReg (.const 0))
          <| .seq (.assign outerReg (.const 0))
            <| .seq (decodeNatProgramAt cursorReg outerReg doneReg boundReg)
              (.forN (.reg outerReg)
                (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
                  satReg bitReg valReg wBaseReg cnfReg boundReg))

/-- The `numVars`-skip stage of `decodeThreeCNFEvalProgramAt`: seeding `doneReg`/
    `numVarsSkipReg` and running `decodeNatProgramAt` over `encodeThreeCNF f`'s `numVars`
    header advances the cursor past it, leaves `boundReg`/`wBaseReg`/`cnfReg` frame-preserved,
    and exposes the clause-list bits and certificate-bit readings starting at the new
    cursor. -/
lemma skip_numVars
    (cursorReg doneReg wBaseReg cnfReg boundReg numVarsSkipReg addr wBase bound : ℕ)
    (f : ThreeCNF) (rest : Bits) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hkd : cnfReg ≠ doneReg) (hwd : wBaseReg ≠ doneReg)
    (hkc : cnfReg ≠ cursorReg) (hwc : wBaseReg ≠ cursorReg) (hbboc : boundReg ≠ cursorReg)
    (hnc : numVarsSkipReg ≠ cursorReg) (hnd : numVarsSkipReg ≠ doneReg)
    (hnk : numVarsSkipReg ≠ cnfReg) (hnw : numVarsSkipReg ≠ wBaseReg)
    (hbbod : boundReg ≠ doneReg) (hbbon : boundReg ≠ numVarsSkipReg)
    (hbelow' : cursorReg < addr ∧ doneReg < addr ∧ numVarsSkipReg < addr)
    (hcursorW : cursorReg < wBase) (hdoneW : doneReg < wBase)
    (hnumvarsskipW : numVarsSkipReg < wBase)
    (hwbase : σ wBaseReg = wBase) (hcnf0 : σ cnfReg = 1) (hb : σ boundReg = bound)
    (hboundNV : f.numVars + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeCNF f ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ f.clauses,
      (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    ∃ σ2 : Store,
    (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg).eval
        ((Program.assign numVarsSkipReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ)) = σ2 ∧
    σ2 cursorReg = addr + f.numVars + 1 ∧ σ2 boundReg = bound ∧ σ2 wBaseReg = wBase ∧
    σ2 cnfReg = 1 ∧
    BitsFrom σ2 (addr + f.numVars + 1) (encodeList encodeThreeClause f.clauses ++ rest) ∧
    (∀ c ∈ f.clauses,
      (σ2 (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ2 (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ2 (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) := by
  have hbits' : BitsFrom σ addr
      (encodeNat f.numVars ++ (encodeList encodeThreeClause f.clauses ++ rest)) := by
    simpa [encodeThreeCNF, List.append_assoc] using hbits
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
  have hσ0done : σ0 doneReg = 0 := by rw [hσ0def]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ0frame : ∀ r, r ≠ doneReg → σ0 r = σ r := by
    intro r hr; rw [hσ0def]; simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  set σ1 := (Program.assign numVarsSkipReg (.const 0)).eval σ0 with hσ1def
  have hσ1n : σ1 numVarsSkipReg = 0 := by
    rw [hσ1def]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ1frame : ∀ r, r ≠ numVarsSkipReg → σ1 r = σ0 r := by
    intro r hr; rw [hσ1def]; simp [eval_assign, Expr.eval, writeReg_diff _ numVarsSkipReg _ r hr]
  have hσ1cur : σ1 cursorReg = addr :=
    (hσ1frame cursorReg hnc.symm).trans ((hσ0frame cursorReg hcd).trans hc)
  have hσ1done : σ1 doneReg = 0 := (hσ1frame doneReg hnd.symm).trans hσ0done
  have hσ1bound : σ1 boundReg = bound :=
    (hσ1frame boundReg hbbon).trans ((hσ0frame boundReg hbbod).trans hb)
  have hbits1 : BitsFrom σ1 addr
      (encodeNat f.numVars ++ (encodeList encodeThreeClause f.clauses ++ rest)) := by
    intro i hi
    rw [hσ1frame _ (by omega), hσ0frame _ (by omega)]
    exact hbits' i hi
  obtain ⟨hcurNV, hcntNV, hdoneNV, hframeNV⟩ := decodeNatProgramAt_encodeNat_append
    cursorReg numVarsSkipReg doneReg boundReg f.numVars bound addr 0
    (encodeList encodeThreeClause f.clauses ++ rest) σ1
    hnc.symm hcd hnd hboundNV hσ1bound hbelow'.1 hbelow'.2.2 hbelow'.2.1 hσ1cur hσ1n hσ1done hbits1
  refine ⟨_, rfl, hcurNV, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hframeNV boundReg hbboc hbbon hbbod).trans hσ1bound
  · rw [hframeNV wBaseReg hwc hnw.symm hwd, hσ1frame wBaseReg hnw.symm, hσ0frame wBaseReg hwd,
      hwbase]
  · rw [hframeNV cnfReg hkc hnk.symm hkd, hσ1frame cnfReg hnk.symm, hσ0frame cnfReg hkd, hcnf0]
  · intro i hi
    have hfr := hframeNV (addr + f.numVars + 1 + i) (by omega) (by omega) (by omega)
    rw [hfr]
    obtain ⟨_, htail⟩ := bitsFrom_append σ1 addr (encodeNat f.numVars)
      (encodeList encodeThreeClause f.clauses ++ rest) hbits1
    have heq : addr + f.numVars + 1 + i = addr + (encodeNat f.numVars).length + i := by
      rw [encodeNat_length]; omega
    rw [heq]; exact htail i hi
  · intro c hc'
    have hb1 := hwbits c hc'
    refine ⟨?_, ?_, ?_⟩
    · rw [hframeNV _ (by have := hcursorW; omega) (by have := hnumvarsskipW; omega)
        (by have := hdoneW; omega), hσ1frame _ (by have := hnumvarsskipW; omega),
        hσ0frame _ (by have := hdoneW; omega)]
      exact hb1.1
    · rw [hframeNV _ (by have := hcursorW; omega) (by have := hnumvarsskipW; omega)
        (by have := hdoneW; omega), hσ1frame _ (by have := hnumvarsskipW; omega),
        hσ0frame _ (by have := hdoneW; omega)]
      exact hb1.2.1
    · rw [hframeNV _ (by have := hcursorW; omega) (by have := hnumvarsskipW; omega)
        (by have := hdoneW; omega), hσ1frame _ (by have := hnumvarsskipW; omega),
        hσ0frame _ (by have := hdoneW; omega)]
      exact hb1.2.2

/-- Running two sequential zero-assignments (`doneReg` then `outerReg`) leaves every other
    register frame-preserved. -/
lemma two_assign_frame (doneReg outerReg : ℕ) (σ : Store) :
    ∀ r, r ≠ doneReg → r ≠ outerReg →
      (Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ) r = σ r := by
  intro r h1 h2
  simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ r h2, writeReg_diff _ doneReg _ r h1]

/-- The clause-count-decode stage of `decodeThreeCNFEvalProgramAt`, running right after
    `skip_numVars`: seeding `doneReg`/`outerReg` and running `decodeNatProgramAt` over the
    clause-count prefix advances the cursor past it, sets `outerReg` to the clause count,
    leaves `boundReg`/`wBaseReg`/`cnfReg` frame-preserved, and exposes the clause-list bits
    and certificate-bit readings starting at the new cursor. -/
lemma decode_clause_count
    (cursorReg outerReg doneReg wBaseReg cnfReg boundReg addr1 wBase bound : ℕ)
    (cs : List ThreeClause) (rest : Bits) (σ2 : Store)
    (hcd : cursorReg ≠ doneReg) (houtc : outerReg ≠ cursorReg) (houtd : outerReg ≠ doneReg)
    (houtk : outerReg ≠ cnfReg) (houtw : outerReg ≠ wBaseReg)
    (hkd : cnfReg ≠ doneReg) (hwd : wBaseReg ≠ doneReg)
    (hkc : cnfReg ≠ cursorReg) (hwc : wBaseReg ≠ cursorReg)
    (hbboc : boundReg ≠ cursorReg) (hbboo : boundReg ≠ outerReg) (hbbod : boundReg ≠ doneReg)
    (hboundCC : cs.length + 1 ≤ bound)
    (hbelow' : cursorReg < addr1 ∧ outerReg < addr1 ∧ doneReg < addr1)
    (hcursorW : cursorReg < wBase) (houterW : outerReg < wBase) (hdoneW : doneReg < wBase)
    (hσ2cur : σ2 cursorReg = addr1) (hσ2bound : σ2 boundReg = bound)
    (hσ2wbase : σ2 wBaseReg = wBase) (hσ2cnf : σ2 cnfReg = 1)
    (hbits2 : BitsFrom σ2 addr1 (encodeList encodeThreeClause cs ++ rest))
    (w : List Bool)
    (hwbits2 : ∀ c ∈ cs,
      (σ2 (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ2 (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ2 (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    ∃ σ5 : Store,
    (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval
        ((Program.assign outerReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ2)) = σ5 ∧
    σ5 outerReg = cs.length ∧ σ5 cursorReg = addr1 + cs.length + 1 ∧ σ5 boundReg = bound ∧
    σ5 wBaseReg = wBase ∧ σ5 cnfReg = 1 ∧
    BitsFrom σ5 (addr1 + cs.length + 1) ((cs.map encodeThreeClause).flatten ++ rest) ∧
    (∀ c ∈ cs,
      (σ5 (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ5 (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ5 (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) := by
  have hframe4 := two_assign_frame doneReg outerReg σ2
  set σ4 := (Program.assign outerReg (.const 0)).eval
    ((Program.assign doneReg (.const 0)).eval σ2) with hσ4def
  have hσ4out : σ4 outerReg = 0 := by rw [hσ4def]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ4done : σ4 doneReg = 0 := by
    rw [hσ4def]
    simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ doneReg houtd.symm, writeReg_same]
  have hσ4cur : σ4 cursorReg = addr1 := (hframe4 cursorReg hcd houtc.symm).trans hσ2cur
  have hσ4bound : σ4 boundReg = bound := (hframe4 boundReg hbbod hbboo).trans hσ2bound
  have hσ4wbase : σ4 wBaseReg = wBase := (hframe4 wBaseReg hwd houtw.symm).trans hσ2wbase
  have hσ4cnf : σ4 cnfReg = 1 := (hframe4 cnfReg hkd houtk.symm).trans hσ2cnf
  have hbits4 : BitsFrom σ4 addr1 (encodeList encodeThreeClause cs ++ rest) := by
    intro i hi; rw [hframe4 _ (by omega) (by omega)]; exact hbits2 i hi
  have hwbits4 : ∀ c ∈ cs,
      (σ4 (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ4 (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ4 (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0) := by
    intro c hc'
    have hb1 := hwbits2 c hc'
    refine ⟨?_, ?_, ?_⟩
    · rw [hframe4 _ (by have := hdoneW; omega) (by have := houterW; omega)]; exact hb1.1
    · rw [hframe4 _ (by have := hdoneW; omega) (by have := houterW; omega)]; exact hb1.2.1
    · rw [hframe4 _ (by have := hdoneW; omega) (by have := houterW; omega)]; exact hb1.2.2
  obtain ⟨hcurCC, hcntCC, hdoneCC, hframeCC⟩ := decodeNatProgramAt_encodeList_length_append
    encodeThreeClause cursorReg outerReg doneReg boundReg bound addr1 0 cs rest σ4
    houtc.symm hcd houtd hboundCC hσ4bound hbelow'.1 hbelow'.2.1 hbelow'.2.2
    hσ4cur hσ4out hσ4done hbits4
  refine ⟨_, rfl, by simpa using hcntCC, hcurCC,
    (hframeCC boundReg hbboc hbboo hbbod).trans hσ4bound,
    (hframeCC wBaseReg hwc houtw.symm hwd).trans hσ4wbase,
    (hframeCC cnfReg hkc houtk.symm hkd).trans hσ4cnf, ?_, ?_⟩
  · intro i hi
    have hfr := hframeCC (addr1 + cs.length + 1 + i) (by omega) (by omega) (by omega)
    rw [hfr]
    obtain ⟨_, htail⟩ := bitsFrom_append σ4 addr1 (encodeNat cs.length)
      ((cs.map encodeThreeClause).flatten ++ rest) (by
        have hshape : encodeList encodeThreeClause cs ++ rest =
            encodeNat cs.length ++ ((cs.map encodeThreeClause).flatten ++ rest) := by
          simp [encodeList, List.append_assoc]
        rw [← hshape]; exact hbits4)
    have heq : addr1 + cs.length + 1 + i = addr1 + (encodeNat cs.length).length + i := by
      rw [encodeNat_length]; omega
    rw [heq]; exact htail i hi
  · intro c hc'
    have hb1 := hwbits4 c hc'
    refine ⟨?_, ?_, ?_⟩
    · rw [hframeCC _ (by have := hcursorW; omega) (by have := houterW; omega)
        (by have := hdoneW; omega)]; exact hb1.1
    · rw [hframeCC _ (by have := hcursorW; omega) (by have := houterW; omega)
        (by have := hdoneW; omega)]; exact hb1.2.1
    · rw [hframeCC _ (by have := hcursorW; omega) (by have := houterW; omega)
        (by have := hdoneW; omega)]; exact hb1.2.2

/-- Correctness of `decodeThreeCNFEvalProgramAt`: decoding `encodeThreeCNF f ++ rest`'s
    `numVars` header and clause-count prefix, then folding `decodeThreeCNFEvalClauseStepAt`
    over the decoded clauses, leaves `cnfReg` holding `threeCnfSatBool w f`'s Boolean value. -/
lemma decodeThreeCNFEvalProgramAt_eval
    (R : RegLayout ThreeCNFEvalRole) (addr wBase bound : ℕ) (f : ThreeCNF) (rest : Bits)
    (σ : Store)
    (haddr : R.top ≤ addr) (hwtop : R.top ≤ wBase) (hWA : wBase < addr)
    (hwbase : σ (R.reg .wBase) = wBase) (hcnf0 : σ (R.reg .cnf) = 1)
    (hb : σ (R.reg .bound) = bound)
    (hboundNV : f.numVars + 1 ≤ bound) (hboundCC : f.clauses.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ f.clauses,
      c.l1.var + 1 ≤ bound ∧ c.l2.var + 1 ≤ bound ∧ c.l3.var + 1 ≤ bound)
    (hc : σ (R.reg .cursor) = addr)
    (hbits : BitsFrom σ addr (encodeThreeCNF f ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ f.clauses,
      (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    (decodeThreeCNFEvalProgramAt (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
      (R.reg .outer) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val)
      (R.reg .wBase) (R.reg .cnf) (R.reg .bound) (R.reg .numVarsSkip)).eval σ (R.reg .cnf) =
      (if threeCnfSatBool w f then 1 else 0) := by
  set cursorReg := R.reg .cursor
  set polReg := R.reg .pol
  set varReg := R.reg .var
  set doneReg := R.reg .done
  set outerReg := R.reg .outer
  set remainingReg := R.reg .remaining
  set satReg := R.reg .sat
  set bitReg := R.reg .bit
  set valReg := R.reg .val
  set wBaseReg := R.reg .wBase
  set cnfReg := R.reg .cnf
  set boundReg := R.reg .bound
  set numVarsSkipReg := R.reg .numVarsSkip
  have hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧ polReg ≠ varReg ∧ polReg ≠ doneReg ∧ varReg ≠ doneReg ∧ remainingReg ≠ cursorReg ∧ remainingReg ≠ polReg ∧ remainingReg ≠ varReg ∧ remainingReg ≠ doneReg ∧ bitReg ≠ cursorReg ∧ bitReg ≠ polReg ∧ bitReg ≠ remainingReg ∧ valReg ≠ cursorReg ∧ valReg ≠ remainingReg ∧ wBaseReg ≠ cursorReg ∧ wBaseReg ≠ polReg ∧ wBaseReg ≠ varReg ∧ wBaseReg ≠ doneReg ∧ wBaseReg ≠ remainingReg ∧ wBaseReg ≠ bitReg ∧ wBaseReg ≠ valReg ∧ satReg ≠ cursorReg ∧ satReg ≠ polReg ∧ satReg ≠ varReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧ satReg ≠ bitReg ∧ satReg ≠ valReg ∧ satReg ≠ wBaseReg ∧ cnfReg ≠ cursorReg ∧ cnfReg ≠ polReg ∧ cnfReg ≠ varReg ∧ cnfReg ≠ doneReg ∧ cnfReg ≠ remainingReg ∧ cnfReg ≠ satReg ∧ cnfReg ≠ bitReg ∧ cnfReg ≠ valReg ∧ cnfReg ≠ wBaseReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧ boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg ∧ boundReg ≠ satReg ∧ boundReg ≠ bitReg ∧ boundReg ≠ valReg ∧ boundReg ≠ cnfReg ∧ boundReg ≠ outerReg ∧ boundReg ≠ numVarsSkipReg ∧ outerReg ≠ cursorReg ∧ outerReg ≠ doneReg ∧ outerReg ≠ cnfReg ∧ outerReg ≠ wBaseReg ∧ numVarsSkipReg ≠ cursorReg ∧ numVarsSkipReg ≠ doneReg ∧ numVarsSkipReg ≠ cnfReg ∧ numVarsSkipReg ≠ wBaseReg :=
  ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide)⟩
  obtain ⟨hcp, hcv, hcd, hpv, hpd, hvd, hrc, hrp, hrv, hrd, hbc, hbp, hbr, hvc, hvr, hwc, hwp, hwv, hwd, hwr, hwb, hwl, hsc, hsp, hsv, hsd, hsr, hsb, hsl, hsw, hkc, hkp, hkv, hkd, hkr, hks, hkb, hkval, hkw, hbboc, hbbop, hbbov, hbbod, hbbor, hbbos, hbbob, hbboval, hbbok, hbboo, hbbon, houtc, houtd, houtk, houtw, hnc, hnd, hnk, hnw⟩ := hdist
  have hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧ remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase :=
    ⟨R.reg_lt_of_top_le .cursor hwtop, R.reg_lt_of_top_le .pol hwtop, R.reg_lt_of_top_le .var hwtop, R.reg_lt_of_top_le .done hwtop, R.reg_lt_of_top_le .remaining hwtop, R.reg_lt_of_top_le .sat hwtop, R.reg_lt_of_top_le .bit hwtop, R.reg_lt_of_top_le .val hwtop⟩
  have hcnfregW : cnfReg < wBase := R.reg_lt_of_top_le .cnf hwtop
  have houterW : outerReg < wBase := R.reg_lt_of_top_le .outer hwtop
  have hnumvarsskipW : numVarsSkipReg < wBase := R.reg_lt_of_top_le .numVarsSkip hwtop
  have hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧ remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧ cnfReg < addr ∧ boundReg < addr ∧ outerReg < addr ∧ numVarsSkipReg < addr :=
    ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr, R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr, R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr, R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr, R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .cnf haddr, R.reg_lt_of_top_le .bound haddr, R.reg_lt_of_top_le .outer haddr, R.reg_lt_of_top_le .numVarsSkip haddr⟩
  unfold decodeThreeCNFEvalProgramAt
  simp only [eval_seq]
  obtain ⟨σ2, hσ2def, hσ2cur, hσ2bound, hσ2wbase, hσ2cnf, hbits2, hwbits2⟩ := skip_numVars
    cursorReg doneReg wBaseReg cnfReg boundReg numVarsSkipReg addr wBase bound f rest σ
    hcd hkd hwd hkc hwc hbboc hnc hnd hnk hnw hbbod hbbon
    ⟨hbelow.1, hbelow.2.2.2.1, hbelow.2.2.2.2.2.2.2.2.2.2.2.2⟩
    hbelowW.1 hbelowW.2.2.2.1 hnumvarsskipW hwbase hcnf0 hb hboundNV hc hbits w hwbits
  rw [hσ2def]
  set addr1 := addr + f.numVars + 1 with haddr1
  obtain ⟨σ5, hσ5def, hcnt5, hσ5cur, hσ5bound, hσ5wbase, hσ5cnf, hbits5, hwbits5⟩ :=
    decode_clause_count cursorReg outerReg doneReg wBaseReg cnfReg boundReg addr1 wBase bound
      f.clauses rest σ2 hcd houtc houtd houtk houtw hkd hwd hkc hwc hbboc hbboo hbbod
      hboundCC ⟨by have := hbelow.1; omega, by have := hbelow.2.2.2.2.2.2.2.2.2.2.2.2; omega,
        by have := hbelow.2.2.2.1; omega⟩
      hbelowW.1 houterW hbelowW.2.2.2.1 hσ2cur hσ2bound hσ2wbase hσ2cnf hbits2 w hwbits2
  rw [eval_forN, hσ5def]
  show loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg
      satReg bitReg valReg wBaseReg cnfReg boundReg) ((Expr.reg outerReg).eval σ5) σ5 cnfReg = _
  simp only [Expr.eval, hcnt5]
  have hWA' : wBase < addr1 + f.clauses.length + 1 := by omega
  have hloop := decode_three_cnf_eval_clause_loop_eval R bound
    (addr1 + f.clauses.length + 1) 1 wBase f.clauses rest σ5
    (by rw [haddr1]; omega) hwtop hWA' hσ5wbase hσ5bound hσ5cnf (Or.inr rfl)
    hvarbound hσ5cur hbits5 w hwbits5
  rw [hloop.2]
  unfold threeCnfSatBool
  simp [List.all_eq_true]

end NPComplete.CookLevin

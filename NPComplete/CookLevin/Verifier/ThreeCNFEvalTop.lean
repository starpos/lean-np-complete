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
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
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
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      cnfReg boundReg numVarsSkipReg addr wBase bound : ℕ) (f : ThreeCNF) (rest : Bits)
    (σ : Store)
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
    (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hbboc : boundReg ≠ cursorReg) (hbbop : boundReg ≠ polReg) (hbbov : boundReg ≠ varReg)
    (hbbod : boundReg ≠ doneReg) (hbbor : boundReg ≠ remainingReg) (hbbos : boundReg ≠ satReg)
    (hbbob : boundReg ≠ bitReg) (hbboval : boundReg ≠ valReg) (hbbok : boundReg ≠ cnfReg)
    (hbboo : boundReg ≠ outerReg)
    (hbbon : boundReg ≠ numVarsSkipReg)
    (houtc : outerReg ≠ cursorReg) (houtd : outerReg ≠ doneReg) (houtk : outerReg ≠ cnfReg)
    (houtw : outerReg ≠ wBaseReg)
    (hnc : numVarsSkipReg ≠ cursorReg) (hnd : numVarsSkipReg ≠ doneReg)
    (hnk : numVarsSkipReg ≠ cnfReg) (hnw : numVarsSkipReg ≠ wBaseReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hcnfregW : cnfReg < wBase) (houterW : outerReg < wBase)
    (hnumvarsskipW : numVarsSkipReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      cnfReg < addr ∧ boundReg < addr ∧ outerReg < addr ∧ numVarsSkipReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hcnf0 : σ cnfReg = 1) (hb : σ boundReg = bound)
    (hboundNV : f.numVars + 1 ≤ bound) (hboundCC : f.clauses.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ f.clauses,
      c.l1.var + 1 ≤ bound ∧ c.l2.var + 1 ≤ bound ∧ c.l3.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeCNF f ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ f.clauses,
      (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    (decodeThreeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg numVarsSkipReg).eval σ cnfReg =
      (if threeCnfSatBool w f then 1 else 0) := by
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
  have hbelow' : cursorReg < addr1 + f.clauses.length + 1 ∧
      polReg < addr1 + f.clauses.length + 1 ∧ varReg < addr1 + f.clauses.length + 1 ∧
      doneReg < addr1 + f.clauses.length + 1 ∧
      remainingReg < addr1 + f.clauses.length + 1 ∧ satReg < addr1 + f.clauses.length + 1 ∧
      bitReg < addr1 + f.clauses.length + 1 ∧ valReg < addr1 + f.clauses.length + 1 ∧
      wBaseReg < addr1 + f.clauses.length + 1 ∧ cnfReg < addr1 + f.clauses.length + 1 :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hWA' : wBase < addr1 + f.clauses.length + 1 := by omega
  have hloop := decode_three_cnf_eval_clause_loop_eval cursorReg polReg varReg doneReg remainingReg
    satReg bitReg valReg wBaseReg cnfReg boundReg (addr1 + f.clauses.length + 1) 1 wBase
    f.clauses rest σ5
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl
    hsc hsp hsv hsd hsr hsb hsl hsw hbboc hbbop hbbov hbbod hbbor hbbos hbbob hbboval
    hkc hkp hkv hkd hkr hks hkb hkval hkw hbbok.symm
    hbelowW hcnfregW hbelow'
    hWA' hσ5wbase hσ5bound hσ5cnf (Or.inr rfl) hvarbound hσ5cur hbits5 w hwbits5
  rw [hloop.2]
  unfold threeCnfSatBool
  simp [List.all_eq_true]

end NPComplete.CookLevin

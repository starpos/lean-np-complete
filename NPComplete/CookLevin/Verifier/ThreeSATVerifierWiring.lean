module

public import NPComplete.CookLevin.Verifier.SATVerifierWiring
public import NPComplete.CookLevin.Verifier.ThreeCNFEvalProgramBounded
public import NPComplete.SAT.ThreeSAT
public import NPComplete.RAMToTM.Generic.Api.ProgramCostBounds

/-!
The machine half of `threeSAT_inNP`: a single `Program`, `threeSatVerifierProg`, that uses the
paired-input contract before evaluating the decoded `ThreeCNF` against the certificate. The
contract supplies the encoded instance, witness base, and a bounded store for the evaluator. The
only 3SAT-specific wiring is `decodeThreeCNFEvalProgramAt`'s `numVarsSkipReg = 16` and the
`f.Bounded` argument (`ValidThreeCNF`'s subtype proof) supplying per-literal variable bounds via
`encodeThreeCNF_numVars_succ_le`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  writeReg_diff writeReg_same)
open NPComplete.BitEncoding (Bits encodeList)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)
open Turing
open Computability (encodeBool)
open Polynomial
open NPComplete.SAT

/-! ## The composed program

Registers 1 and 5 use the instance and witness bases from the paired-input contract. Register 15
is the output accumulator, while register 16 skips `ThreeCNF`'s `numVars` header. -/

/-- The whole verifier: apply the paired-input prelude, seed the accumulator, then evaluate. -/
def threeSatVerifierProg : Program :=
  pairPreludeProg.seq
    ((Program.assign 15 (.const 1)).seq
      (decodeThreeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 15 0 16))

/-! ## `ScanFree` -/

lemma scanFree_decodeThreeCNFEvalProgramAt
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      cnfReg boundReg numVarsSkipReg : ℕ) :
    ScanFree (decodeThreeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg
      satReg bitReg valReg wBaseReg cnfReg boundReg numVarsSkipReg) := by
  unfold decodeThreeCNFEvalProgramAt
  exact ⟨trivial, trivial, scanFree_decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg,
    trivial, trivial, scanFree_decodeNatProgramAt cursorReg outerReg doneReg boundReg,
    scanFree_decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg cnfReg boundReg⟩

lemma scanFree_threeSatVerifierProg : ScanFree threeSatVerifierProg := by
  unfold threeSatVerifierProg
  exact ⟨ScanFree_pairPreludeProg, trivial,
    scanFree_decodeThreeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 15 0 16⟩

/-! ## Correctness -/

/-- The paired-input contract facts feeding the 3SAT evaluator. -/
lemma threeSatVerifierProg_phase1 (f : ThreeCNF) (w : List Bool) :
    PairPreludeSpec (encodeThreeCNF f) w (bitInputStore (pairBits (encodeThreeCNF f) w))
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w))) ∧
    ProgramBoundedIn (pairPreludeBound (pairBits (encodeThreeCNF f) w).length)
      (bitInputStore (pairBits (encodeThreeCNF f) w)) pairPreludeProg := by
  exact pairPreludeProg_runs (encodeThreeCNF f) w

/-- The paired-input contract gives the post-prelude facts needed by the evaluator. -/
lemma threeSatVerifierProg_phase2 (f : ThreeCNF) (w : List Bool) :
    let τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w))
    let σ3 := (Program.assign 15 (Expr.const 1)).eval τ
    PairPreludeSpec (encodeThreeCNF f) w (bitInputStore (pairBits (encodeThreeCNF f) w)) τ ∧
      σ3 0 = (pairBits (encodeThreeCNF f) w).length ∧ σ3 1 = τ 1 ∧
      σ3 3 = (encodeThreeCNF f).length ∧ σ3 5 = τ 5 ∧ σ3 15 = 1 ∧
      BitsFrom σ3 (τ 1) (encodeThreeCNF f) ∧
      (∀ v, v < (encodeThreeCNF f).length →
        σ3 (τ 5 + v) = if w.getD v false then 1 else 0) := by
  dsimp only
  obtain ⟨hSpec, _⟩ := threeSatVerifierProg_phase1 f w
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  change PairPreludeSpec (encodeThreeCNF f) w (bitInputStore (pairBits (encodeThreeCNF f) w)) τ ∧
    σ3 0 = (pairBits (encodeThreeCNF f) w).length ∧ σ3 1 = τ 1 ∧
    σ3 3 = (encodeThreeCNF f).length ∧ σ3 5 = τ 5 ∧ σ3 15 = 1 ∧
    BitsFrom σ3 (τ 1) (encodeThreeCNF f) ∧
    (∀ v, v < (encodeThreeCNF f).length →
      σ3 (τ 5 + v) = if w.getD v false then 1 else 0)
  have h0 : σ3 0 = (pairBits (encodeThreeCNF f) w).length := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 0 (by omega)]
    exact hSpec.input_length
  have h1 : σ3 1 = τ 1 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 1 (by omega)]
  have h3 : σ3 3 = (encodeThreeCNF f).length := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 3 (by omega)]
    exact hSpec.x_length
  have h5 : σ3 5 = τ 5 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 5 (by omega)]
  have h15 : σ3 15 = 1 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_same]
  have hbits : BitsFrom σ3 (τ 1) (encodeThreeCNF f) := by
    intro i hi
    have hne : τ 1 + i ≠ 15 := by
      have := hSpec.bases.1
      have := hSpec.bases.2
      omega
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 _ hne]
    exact hSpec.x_bits i hi
  have hwbits : ∀ v, v < (encodeThreeCNF f).length →
      σ3 (τ 5 + v) = if w.getD v false then 1 else 0 := by
    intro v hv
    have hvmax : v < max (encodeThreeCNF f).length w.length :=
      lt_of_lt_of_le hv (le_max_left _ _)
    have hne : τ 5 + v ≠ 15 := by
      have := hSpec.bases.1
      omega
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 _ hne]
    exact hSpec.w_bits v hvmax
  exact ⟨hSpec, h0, h1, h3, h5, h15, hbits, hwbits⟩


/-- Running on the canonical paired input leaves the output register holding the Boolean
    evaluation. The evaluator's variable and clause bounds come from `f.Bounded` and its encoding. -/
lemma threeSatVerifierProg_correct (f : ValidThreeCNF) (w : List Bool) :
    threeSatVerifierProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w)) 15 =
      if threeCnfSatBool w f.1 then 1 else 0 := by
  have hLeq : (pairBits (encodeThreeCNF f.1) w).length =
      2 * (encodeThreeCNF f.1).length + 1 + w.length :=
    pairBits_length (encodeThreeCNF f.1) w
  set L := (pairBits (encodeThreeCNF f.1) w).length with hLdef
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  have hphase2 := threeSatVerifierProg_phase2 f.1 w
  dsimp only at hphase2
  rw [← hσ3def, ← hτdef] at hphase2
  rcases hphase2 with ⟨hSpec, hσ30, hσ31, _, hσ35, hσ315, hσ3bits, hσ3wbits⟩
  rw [← hLdef] at hσ30
  have hboundNV : f.1.numVars + 1 ≤ L := by
    have h := encodeThreeCNF_numVars_succ_le f.1; omega
  have hboundCC : f.1.clauses.length + 1 ≤ L := by
    have h := encodeThreeCNF_clauseCount_succ_le f.1; omega
  have hvarbound : ∀ c ∈ f.1.clauses,
      c.l1.var + 1 ≤ L ∧ c.l2.var + 1 ≤ L ∧ c.l3.var + 1 ≤ L := by
    intro c hc
    have h1 := f.2 c hc c.l1 (by simp [ThreeClause.literals])
    have h2 := f.2 c hc c.l2 (by simp [ThreeClause.literals])
    have h3 := f.2 c hc c.l3 (by simp [ThreeClause.literals])
    have hnv := encodeThreeCNF_numVars_succ_le f.1
    omega
  have hnumvarsskipW : 16 < τ 5 := by have := hSpec.bases.1; omega
  have hWA : τ 5 < τ 1 := hSpec.bases.2
  have hfinal := decodeThreeCNFEvalProgramAt_eval 1 6 7 9 8 10 11 12 13 5 15 0 16
    (τ 1) (τ 5) L f.1 ([] : Bits) σ3
    (hcp := by omega) (hcv := by omega) (hcd := by omega) (hpv := by omega) (hpd := by omega)
    (hvd := by omega) (hrc := by omega) (hrp := by omega) (hrv := by omega) (hrd := by omega)
    (hbc := by omega) (hbp := by omega) (hbr := by omega)
    (hvc := by omega) (hvr := by omega)
    (hwc := by omega) (hwp := by omega) (hwv := by omega) (hwd := by omega)
    (hwr := by omega) (hwb := by omega) (hwl := by omega)
    (hsc := by omega) (hsp := by omega) (hsv := by omega) (hsd := by omega) (hsr := by omega)
    (hsb := by omega) (hsl := by omega) (hsw := by omega)
    (hkc := by omega) (hkp := by omega) (hkv := by omega) (hkd := by omega) (hkr := by omega)
    (hks := by omega) (hkb := by omega) (hkval := by omega) (hkw := by omega)
    (hbboc := by omega) (hbbop := by omega) (hbbov := by omega) (hbbod := by omega)
    (hbbor := by omega) (hbbos := by omega) (hbbob := by omega) (hbboval := by omega)
    (hbbok := by omega) (hbboo := by omega) (hbbon := by omega)
    (houtc := by omega) (houtd := by omega) (houtk := by omega) (houtw := by omega)
    (hnc := by omega) (hnd := by omega) (hnk := by omega) (hnw := by omega)
    (hbelowW := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    (hcnfregW := by omega) (houterW := by omega)
    (hnumvarsskipW := hnumvarsskipW)
    (hbelow := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩)
    (hWA := hWA)
    (hwbase := hσ35) (hcnf0 := hσ315) (hb := hσ30) (hboundNV := hboundNV)
    (hboundCC := hboundCC) (hvarbound := hvarbound) (hc := hσ31)
    (hbits := by simpa using hσ3bits)
    (w := w) (hwbits := by
      intro c hc
      refine ⟨?_, ?_, ?_⟩
      · exact hσ3wbits c.l1.var (lt_of_lt_of_le (f.2 c hc c.l1 (by simp [ThreeClause.literals]))
          (by have := encodeThreeCNF_numVars_succ_le f.1; omega))
      · exact hσ3wbits c.l2.var (lt_of_lt_of_le (f.2 c hc c.l2 (by simp [ThreeClause.literals]))
          (by have := encodeThreeCNF_numVars_succ_le f.1; omega))
      · exact hσ3wbits c.l3.var (lt_of_lt_of_le (f.2 c hc c.l3 (by simp [ThreeClause.literals]))
          (by have := encodeThreeCNF_numVars_succ_le f.1; omega)))
  show threeSatVerifierProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w)) 15 = _
  rw [threeSatVerifierProg, eval_seq, eval_seq, hfinal]

/-! ## `ProgramBoundedIn`

The prelude's linear access budget is enlarged to `B := 200 * (L+1)^4` (`L` the paired-input
length). The decoder's store-bound theorem then shows that the encoded instance, witness region,
and clause-iteration budget all fit beneath the same coarse polynomial bound. -/

/-- The prelude's contract and the polynomially enlarged access bound. -/
lemma threeSatVerifierProg_bounded_in_phase1 (f : ThreeCNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeThreeCNF f) w).length+1)^4)
      (bitInputStore (pairBits (encodeThreeCNF f) w)) pairPreludeProg ∧
    StoreValuesLe (200 * ((pairBits (encodeThreeCNF f) w).length+1)^4)
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w))) ∧
    PairPreludeSpec (encodeThreeCNF f) w (bitInputStore (pairBits (encodeThreeCNF f) w))
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w))) := by
  obtain ⟨hSpec, hprelude⟩ := threeSatVerifierProg_phase1 f w
  set L := (pairBits (encodeThreeCNF f) w).length with hLdef
  set B := 200 * (L+1)^4 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith [pow_pos (show 0 < L+1 by omega) 4]
  have hσ0_le : StoreValuesLe B (bitInputStore (pairBits (encodeThreeCNF f) w)) := by
    intro i
    cases i with
    | zero => show (pairBits (encodeThreeCNF f) w).length ≤ B; rw [← hLdef, hBdef]
              nlinarith [sq_nonneg L]
    | succ i => simp [bitInputStore]; split <;> omega
  have hprelude_le : pairPreludeBound (pairBits (encodeThreeCNF f) w).length ≤ B := by
    rw [← hLdef, hBdef]
    simp [pairPreludeBound]
    nlinarith [sq_nonneg L, sq_nonneg (L * L)]
  have hp : ProgramBoundedIn B (bitInputStore (pairBits (encodeThreeCNF f) w)) pairPreludeProg :=
    programBoundedIn_mono pairPreludeProg hprelude_le hprelude
  have hτ_le : StoreValuesLe B (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f) w))) :=
    program_eval_storeValuesLe (bitInputStore (pairBits (encodeThreeCNF f) w)) pairPreludeProg
      hB1 hσ0_le hp ScanFree_pairPreludeProg
  exact ⟨hp, hτ_le, hSpec⟩

/-- The prelude, accumulator seed, and evaluator fit the same coarse polynomial budget. -/
lemma threeSatVerifierProg_bounded_in_phase2 (f : ValidThreeCNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeThreeCNF f.1) w).length+1)^4)
      (bitInputStore (pairBits (encodeThreeCNF f.1) w)) pairPreludeProg ∧
    ProgramBoundedIn (200 * ((pairBits (encodeThreeCNF f.1) w).length+1)^4)
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w)))
      (Program.assign 15 (Expr.const 1)) ∧
    ProgramBoundedIn (200 * ((pairBits (encodeThreeCNF f.1) w).length+1)^4)
      ((Program.assign 15 (Expr.const 1)).eval
        (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w))))
      (decodeThreeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 15 0 16) := by
  have hLeq : (pairBits (encodeThreeCNF f.1) w).length =
      2 * (encodeThreeCNF f.1).length + 1 + w.length :=
    pairBits_length (encodeThreeCNF f.1) w
  obtain ⟨hp1, hτ_le, _⟩ := threeSatVerifierProg_bounded_in_phase1 f.1 w
  set L := (pairBits (encodeThreeCNF f.1) w).length with hLdef
  set B := 200 * (L+1)^4 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith [pow_pos (show 0 < L+1 by omega) 4]
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  have hphase2 := threeSatVerifierProg_phase2 f.1 w
  dsimp only at hphase2
  rw [← hσ3def, ← hτdef] at hphase2
  rcases hphase2 with ⟨hSpec, hσ30, hσ31, _, hσ35, _, _, _⟩
  rw [← hLdef] at hσ30
  have hp3 : ProgramBoundedIn B τ (Program.assign 15 (Expr.const 1)) := by
    refine ⟨by have := hB1; omega, ?_⟩
    simp only [ExprBoundedIn]
    omega
  have hσ3_le : StoreValuesLe B σ3 :=
    program_eval_storeValuesLe τ (Program.assign 15 (Expr.const 1)) hB1 hτ_le hp3 trivial
  have hXend : τ 1 + (encodeThreeCNF f.1).length ≤ pairPreludeBound L := by
    have h := hSpec.x_end_le
    rw [← hLdef] at h
    exact h
  have haddr : τ 1 ≤ pairPreludeBound L := by omega
  have hPplus : pairPreludeBound L + L ≤ B := by
    rw [hBdef]
    simp [pairPreludeBound]
    nlinarith [sq_nonneg L, sq_nonneg (L * L)]
  have hbase : τ 5 ≤ pairPreludeBound L := by
    have hlt := hSpec.bases.2
    omega
  have hσ3wbudget : σ3 5 + σ3 0 ≤ B := by
    rw [hσ35, hσ30]
    have hbound := hPplus
    have hbase' := hbase
    rw [hBdef]
    simp only [pairPreludeBound] at hbound hbase'
    omega
  have hσ3houter : σ3 1 + σ3 0 + σ3 0 + σ3 0 * (3 * (σ3 0 + 1)) +
      3 * (σ3 0 + 1) + 1 + σ3 0 ≤ B := by
    rw [hσ31, hσ30, hBdef]
    have haddr' : τ 1 ≤ 5 * L + 101 := by simpa [pairPreludeBound] using haddr
    nlinarith [haddr', sq_nonneg L, sq_nonneg (L * L)]
  have hp4 : ProgramBoundedIn B σ3
      (decodeThreeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 15 0 16) :=
    programBoundedIn_decodeThreeCNFEvalProgramAt_of_store_bounds B 1 6 7 9 8 10 11 12 13 5 15 0 16
      σ3 hσ3_le
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      (hrc := by omega) (hcbit := by omega) (hcval := by omega) (hcsat := by omega)
      (hbb := by omega) (hbval := by omega) (hbs := by omega) (hbk := by omega)
      (hck := by omega) (hrs := by omega) (hsd := by omega)
      (hcw := by omega) (hpw := by omega) (hvw := by omega) (hdw := by omega) (hrw := by omega)
      (hbw := by omega) (hvalw := by omega) (hsw := by omega) (hkw := by omega) (hrv := by omega)
      (hco := by omega) (hdo := by omega) (hoBnd := by omega) (how := by omega)
      (hnc := by omega) (hnd := by omega) (hnBnd := by omega) (hnw := by omega)
      (hB1 := hB1) (hwbudget := hσ3wbudget) (houterCoarse := hσ3houter)
  exact ⟨hp1, hp3, hp4⟩

/-- `threeSatVerifierProg` stays within the coarse polynomial access budget. -/
lemma threeSatVerifierProg_bounded_in (f : ValidThreeCNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeThreeCNF f.1) w).length+1)^4)
      (bitInputStore (pairBits (encodeThreeCNF f.1) w)) threeSatVerifierProg := by
  obtain ⟨hp1, _, _⟩ := threeSatVerifierProg_bounded_in_phase1 f.1 w
  obtain ⟨_, hp2, hp3⟩ := threeSatVerifierProg_bounded_in_phase2 f w
  unfold threeSatVerifierProg
  exact programBoundedIn_seq pairPreludeProg _ _
    (bitInputStore (pairBits (encodeThreeCNF f.1) w)) hp1
    (programBoundedIn_seq (Program.assign 15 (.const 1)) _ _
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeThreeCNF f.1) w))) hp2 hp3)

/-! ## `cost_le` / `compiled_operands_le`

`CostEnvelope threeSatVerifierProg` is a structural, register-independent expression in the
store's values, so composing it with `B := 200 * (X+1)^4` gives a genuine `Polynomial ℕ`
(`threeSatVerifierCostPoly`) via `uniformCostEnvelopePoly`. `polynomial_nat_eval_le_power` turns
that into a `c * (N+1)^c` bound (`threeSatVerifierCostC`), the shape
`BoundedWhileDecider.cost_le` needs; `compiledOperandBound_of_programBoundedIn` reuses the same
`ProgramBoundedIn`/`ScanFree` facts for the bit-cost side. Mirrors `SATVerifierWiring.lean`'s
`satVerifierCostPoly`/`satVerifierCostC` section. -/

noncomputable def threeSatVerifierCostPoly : Polynomial ℕ :=
  (uniformCostEnvelopePoly threeSatVerifierProg).comp (C 200 * (X + 1)^4)

lemma three_sat_verifier_costEnvelope_le_poly (N : ℕ) :
    CostEnvelope threeSatVerifierProg (200 * (N+1)^4) ≤ threeSatVerifierCostPoly.eval N := by
  rw [threeSatVerifierCostPoly, Polynomial.eval_comp, uniformCostEnvelopePoly_eval]
  simp

noncomputable def threeSatVerifierCostC : ℕ :=
  1000 + (threeSatVerifierCostPoly.support.card + 1) *
    (threeSatVerifierCostPoly.support.sup (fun n => threeSatVerifierCostPoly.coeff n) + 1) *
    (threeSatVerifierCostPoly.support.sup id + 1)

lemma threeSatVerifierCostPoly_le_power (N : ℕ) :
    threeSatVerifierCostPoly.eval N ≤ threeSatVerifierCostC * (N + 1) ^ threeSatVerifierCostC := by
  have h := polynomial_nat_eval_le_power threeSatVerifierCostPoly N
  set c := (threeSatVerifierCostPoly.support.card + 1) *
    (threeSatVerifierCostPoly.support.sup (fun n => threeSatVerifierCostPoly.coeff n) + 1) *
    (threeSatVerifierCostPoly.support.sup id + 1) with hcdef
  have hcle : c ≤ threeSatVerifierCostC := by unfold threeSatVerifierCostC; omega
  calc threeSatVerifierCostPoly.eval N ≤ c * (N+1)^c := h
    _ ≤ threeSatVerifierCostC * (N+1)^threeSatVerifierCostC := by
        apply Nat.mul_le_mul hcle
        exact Nat.pow_le_pow_right (by omega) hcle

lemma threeSatVerifierCostC_ge300 : (300:ℕ) ≤ threeSatVerifierCostC := by
  unfold threeSatVerifierCostC; omega

/-! ## The decider -/

/-- The `BoundedWhileDecider` packaging `threeSatVerifierProg` against the promise-everywhere
    domain `D := fun _ => True`, deciding `threeCnfSatBool xw.2 xw.1.1 = true` at the shared
    polynomial exponent `threeSatVerifierCostC`. Mirrors `satVerifierDecider`. -/
noncomputable def threeSatVerifierDecider :
    BoundedWhileDecider (fun xw : ValidThreeCNF × List Bool => pairBits (encodeThreeCNF xw.1.1) xw.2)
      (fun _ => True) (fun xw => threeCnfSatBool xw.2 xw.1.1) where
  p := threeSatVerifierProg
  outReg := 15
  c := threeSatVerifierCostC
  correct := by
    intro x _
    rw [threeSatVerifierProg_correct x.1 x.2]
    split_ifs with hc <;> simp_all
  cost_le := by
    intro x _
    have hp := threeSatVerifierProg_bounded_in x.1 x.2
    set N := (pairBits (encodeThreeCNF x.1.1) x.2).length with hNdef
    have hσle : StoreValuesLe (200 * (N+1)^4)
        (bitInputStore (pairBits (encodeThreeCNF x.1.1) x.2)) := by
      intro i
      cases i with
      | zero => show (pairBits (encodeThreeCNF x.1.1) x.2).length ≤ _
                rw [← hNdef]; nlinarith [sq_nonneg N]
      | succ i =>
          simp only [bitInputStore]
          split <;> nlinarith [pow_pos (show 0 < N+1 by omega) 4]
    have hB1 : (1:ℕ) ≤ 200*(N+1)^4 := by nlinarith [pow_pos (show 0 < N+1 by omega) 4]
    have hcost := program_cost_le_CostEnvelope_of_bounded threeSatVerifierProg (200*(N+1)^4)
      (bitInputStore (pairBits (encodeThreeCNF x.1.1) x.2)) hB1 hσle hp
      scanFree_threeSatVerifierProg
    have hcostpoly := three_sat_verifier_costEnvelope_le_poly N
    have hcostpow := threeSatVerifierCostPoly_le_power N
    show threeSatVerifierProg.cost (bitInputStore (pairBits (encodeThreeCNF x.1.1) x.2)) ≤
      threeSatVerifierCostC * (N + 1) ^ threeSatVerifierCostC
    omega
  bit_c := threeSatVerifierCostC
  compiled_operands_le := by
    intro x _
    set N := (pairBits (encodeThreeCNF x.1.1) x.2).length with hNdef
    refine ⟨bitLen (200*(N+1)^4), ?_, ?_⟩
    · have hbl := bitLen_le_succ (200*(N+1)^4)
      have hpos : (1:ℕ) ≤ (N+1)^4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpow4 : (N+1)^4 ≤ (N+1)^threeSatVerifierCostC :=
        Nat.pow_le_pow_right (by omega) (by have := threeSatVerifierCostC_ge300; omega)
      have h1 : threeSatVerifierCostC * (N+1)^4 ≤
          threeSatVerifierCostC * (N+1)^threeSatVerifierCostC :=
        Nat.mul_le_mul_left threeSatVerifierCostC hpow4
      have h2 : 300 * (N+1)^4 ≤ threeSatVerifierCostC * (N+1)^4 :=
        Nat.mul_le_mul_right _ threeSatVerifierCostC_ge300
      nlinarith [hbl, hpos, h1, h2]
    · have hp := threeSatVerifierProg_bounded_in x.1 x.2
      have hσle : StoreValuesLe (200 * (N+1)^4)
          (bitInputStore (pairBits (encodeThreeCNF x.1.1) x.2)) := by
        intro i
        cases i with
        | zero => show (pairBits (encodeThreeCNF x.1.1) x.2).length ≤ _
                  rw [← hNdef]; nlinarith [sq_nonneg N]
        | succ i =>
            simp only [bitInputStore]
            split <;> nlinarith [pow_pos (show 0 < N+1 by omega) 4]
      have hB1 : (1:ℕ) ≤ 200*(N+1)^4 := by nlinarith [pow_pos (show 0 < N+1 by omega) 4]
      exact compiledOperandBound_of_programBoundedIn threeSatVerifierProg
        (pairBits (encodeThreeCNF x.1.1) x.2) (200*(N+1)^4) hB1 hσle hp
        scanFree_threeSatVerifierProg

end NPComplete.CookLevin

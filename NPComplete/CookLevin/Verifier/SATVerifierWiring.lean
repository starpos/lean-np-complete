module

public import NPComplete.CookLevin.Verifier.PairPrelude
public import NPComplete.CookLevin.Verifier.CNFEvalTop
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatLoaderRelocate
public import NPComplete.CookLevin.UniformPackaging.OutputBounds
public import NPComplete.CookLevin.UniformPackaging.CostAndOperands
public import NPComplete.RAMToTM.Generic.Api.TransducerMachine
public import NPComplete.RAMToTM.Generic.Api.BoundedInMono
public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.CookLevin.Verifier.SATBool

/-!
The machine half of `sat_inNP`: a single `Program`, `satVerifierProg`, that uses the paired-input
prelude contract to expose the encoded CNF and certificate before decoding and evaluating the CNF.
Packaging this as a `BoundedWhileDecider` (`satVerifierDecider`) is the machine half of `sat_inNP`;
the generic entry `InNP.of_bounded_while_verifier` (`Entry.lean`) closes it.

This file cannot be merged into `SATVerifier.lean` itself: `CNFEvalTop.lean` sits downstream of
`SATBool.lean` (via `ClauseEval.lean`, which needs `cnfSatBool`/`decodeAssignment` for its own
literal/clause evaluator), and `SATVerifier.lean` needs `CNFEvalTop.lean`'s `decodeCNFEvalProgramAt`
for its machine half — putting both halves in one file would make `SATVerifier.lean` import
itself transitively. `SATBool.lean` breaks that cycle by holding `cnfSatBool` at the lowest
layer; this file holds the RAM-to-TM half at the layer just below `SATVerifier.lean`.
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

The cursor and witness-base registers published by the paired-input contract are shared with
`decodeCNFEvalProgramAt`; register 15 doubles as `BoundedWhileDecider.outReg`. -/

/-- The whole verifier: apply the paired-input prelude, seed the accumulator, then evaluate. -/
def satVerifierProg : Program :=
  pairPreludeProg.seq
    ((Program.assign 15 (.const 1)).seq
      (decodeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 14 15 0))

/-! ## `ScanFree` -/

lemma scanFree_decodeCNFEvalProgramAt
    (cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) :
    ScanFree (decodeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg cnfReg boundReg) := by
  unfold decodeCNFEvalProgramAt
  exact ⟨trivial, trivial, scanFree_decodeNatProgramAt cursorReg outerReg doneReg boundReg,
    scanFree_decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg cnfReg boundReg⟩

lemma scanFree_satVerifierProg : ScanFree satVerifierProg := by
  unfold satVerifierProg
  exact ⟨ScanFree_pairPreludeProg, trivial,
    scanFree_decodeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 14 15 0⟩

/-! ## Correctness -/

lemma satVerifierProg_phase1 (φ : CNF) (w : List Bool) :
    PairPreludeSpec (encodeCNF φ) w (bitInputStore (pairBits (encodeCNF φ) w))
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) ∧
    ProgramBoundedIn (pairPreludeBound (pairBits (encodeCNF φ) w).length)
      (bitInputStore (pairBits (encodeCNF φ) w)) pairPreludeProg := by
  exact pairPreludeProg_runs (encodeCNF φ) w

lemma satVerifierProg_phase2 (φ : CNF) (w : List Bool) :
    PairPreludeSpec (encodeCNF φ) w (bitInputStore (pairBits (encodeCNF φ) w))
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) ∧
    ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))) 0 =
        (pairBits (encodeCNF φ) w).length ∧
    ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))) 1 =
        (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) 1 ∧
    ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))) 3 =
        (encodeCNF φ).length ∧
    ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))) 5 =
        (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) 5 ∧
    ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))) 15 = 1 ∧
    BitsFrom ((Program.assign 15 (Expr.const 1)).eval
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))))
      ((pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) 1) (encodeCNF φ) ∧
    ∀ v, v < (encodeCNF φ).length →
      ((Program.assign 15 (Expr.const 1)).eval
        (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))))
        ((pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) 5 + v) =
          if w.getD v false then 1 else 0 := by
  obtain ⟨hSpec, _⟩ := satVerifierProg_phase1 φ w
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  change PairPreludeSpec (encodeCNF φ) w (bitInputStore (pairBits (encodeCNF φ) w)) τ ∧
    σ3 0 = (pairBits (encodeCNF φ) w).length ∧ σ3 1 = τ 1 ∧
    σ3 3 = (encodeCNF φ).length ∧ σ3 5 = τ 5 ∧ σ3 15 = 1 ∧
    BitsFrom σ3 (τ 1) (encodeCNF φ) ∧
    (∀ v, v < (encodeCNF φ).length →
      σ3 (τ 5 + v) = if w.getD v false then 1 else 0)
  have h0 : σ3 0 = (pairBits (encodeCNF φ) w).length := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 0 (by omega)]
    exact hSpec.input_length
  have h1 : σ3 1 = τ 1 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 1 (by omega)]
  have h3 : σ3 3 = (encodeCNF φ).length := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 3 (by omega)]
    exact hSpec.x_length
  have h5 : σ3 5 = τ 5 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 5 (by omega)]
  have h15 : σ3 15 = 1 := by
    rw [hσ3def, eval_assign, Expr.eval, writeReg_same]
  have hbits : BitsFrom σ3 (τ 1) (encodeCNF φ) := by
    intro i hi
    have hne : τ 1 + i ≠ 15 := by
      have := hSpec.bases.1
      have := hSpec.bases.2
      omega
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 _ hne]
    exact hSpec.x_bits i hi
  have hwbits : ∀ v, v < (encodeCNF φ).length →
      σ3 (τ 5 + v) = if w.getD v false then 1 else 0 := by
    intro v hv
    have hvmax : v < max (encodeCNF φ).length w.length := lt_of_lt_of_le hv (le_max_left _ _)
    have hne : τ 5 + v ≠ 15 := by have := hSpec.bases.1; omega
    rw [hσ3def, eval_assign, Expr.eval, writeReg_diff _ 15 1 _ hne]
    exact hSpec.w_bits v hvmax
  exact ⟨hSpec, h0, h1, h3, h5, h15, hbits, hwbits⟩

lemma satVerifierProg_correct (φ : CNF) (w : List Bool) :
    satVerifierProg.eval (bitInputStore (pairBits (encodeCNF φ) w)) 15 =
      if cnfSatBool w φ = true then 1 else 0 := by
  have hLeq : (pairBits (encodeCNF φ) w).length = 2 * (encodeCNF φ).length + 1 + w.length :=
    pairBits_length (encodeCNF φ) w
  set L := (pairBits (encodeCNF φ) w).length with hLdef
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  have hphase2 := satVerifierProg_phase2 φ w
  rw [← hσ3def, ← hτdef] at hphase2
  rcases hphase2 with ⟨hSpec, hσ30, hσ31, _, hσ35, hσ315, hσ3bits, hσ3wbits⟩
  rw [← hLdef] at hσ30
  have hsum := encodeCNF_sum_lits_succ_le φ
  have hboundc : φ.clauses.length + 1 ≤ L := by omega
  have hboundc2 : ∀ c ∈ φ.clauses, c.lits.length + 1 ≤ L := by
    intro c hc
    have hmem : (c.lits.length + 1) ∈ φ.clauses.map (fun c => c.lits.length + 1) :=
      List.mem_map_of_mem hc
    have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    omega
  have hvarbound : ∀ c ∈ φ.clauses, ∀ l ∈ c.lits, l.var + 1 ≤ L := by
    intro c hc l hl
    have h1 := cnfVarBound_gt φ c hc l hl
    have h2 := cnfVarBound_le_encodeCNF φ
    omega
  have hbelowW : 16 ≤ τ 5 := by have := hSpec.bases.1; omega
  have hWA : τ 5 < τ 1 := hSpec.bases.2
  have hfinal := decodeCNFEvalProgramAt_eval 1 6 7 9 8 10 11 12 13 5 14 15 0
    (τ 1) (τ 5) L φ.clauses ([] : Bits) σ3
    (hcp := by omega) (hcv := by omega) (hcd := by omega) (hpv := by omega) (hpd := by omega)
    (hvd := by omega) (hrc := by omega) (hrp := by omega) (hrv := by omega) (hrd := by omega)
    (hbc := by omega) (hbp := by omega) (hbr := by omega)
    (hvc := by omega) (hvr := by omega)
    (hwc := by omega) (hwp := by omega) (hwv := by omega) (hwd := by omega)
    (hwr := by omega) (hwb := by omega) (hwl := by omega) (hwlen := by omega)
    (hsc := by omega) (hsp := by omega) (hsv := by omega) (hsd := by omega) (hsr := by omega)
    (hsb := by omega) (hsl := by omega) (hsw := by omega) (hlc := by omega) (hld := by omega)
    (hkc := by omega) (hkp := by omega) (hkv := by omega) (hkd := by omega) (hkr := by omega)
    (hks := by omega) (hkb := by omega) (hkval := by omega) (hkw := by omega) (hkl := by omega)
    (hbboc := by omega) (hbbop := by omega) (hbbov := by omega) (hbbod := by omega)
    (hbbor := by omega) (hbbos := by omega) (hbbob := by omega) (hbboval := by omega)
    (hbbol := by omega) (hbbok := by omega) (hbboo := by omega)
    (houtc := by omega) (houtd := by omega) (houtk := by omega) (houtw := by omega)
    (hbelowW := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    (hlenW := by omega) (hcnfregW := by omega)
    (houterW := by omega)
    (hbelow := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩)
    (hWA := hWA) (hwbase := hσ35) (hcnf0 := hσ315) (hb := hσ30)
    (hbound := hboundc) (hbound2 := hboundc2) (hvarbound := hvarbound) (hc := hσ31)
    (hbits := by simpa [encodeCNF] using hσ3bits) (w := w)
    (hwbits := by
      intro c hc l hl
      exact hσ3wbits l.var (lt_of_lt_of_le (cnfVarBound_gt φ c hc l hl)
        (cnfVarBound_le_encodeCNF φ)))
  rw [satVerifierProg, eval_seq, eval_seq, hfinal]
  simp [cnfSatBool, List.all_eq_true]

/-! ## `ProgramBoundedIn`

The contract's linear access budget is enlarged to the verifier's coarse polynomial budget, then
composed with the accumulator initialization and the decoder. -/

lemma satVerifierProg_bounded_in_phase1 (φ : CNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      (bitInputStore (pairBits (encodeCNF φ) w)) pairPreludeProg ∧
    StoreValuesLe (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) ∧
    PairPreludeSpec (encodeCNF φ) w (bitInputStore (pairBits (encodeCNF φ) w))
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) := by
  obtain ⟨hSpec, hprelude⟩ := satVerifierProg_phase1 φ w
  set L := (pairBits (encodeCNF φ) w).length with hLdef
  set B := 200 * (L+1)^4 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith [pow_pos (show 0 < L+1 by omega) 4]
  have hσ0_le : StoreValuesLe B (bitInputStore (pairBits (encodeCNF φ) w)) := by
    intro i
    cases i with
    | zero => show (pairBits (encodeCNF φ) w).length ≤ B; rw [← hLdef, hBdef]; nlinarith [sq_nonneg L]
    | succ i => simp [bitInputStore]; split <;> omega
  have hprelude_le : pairPreludeBound (pairBits (encodeCNF φ) w).length ≤ B := by
    rw [← hLdef, hBdef]
    simp [pairPreludeBound]
    nlinarith [sq_nonneg L, sq_nonneg (L * L)]
  have hp : ProgramBoundedIn B (bitInputStore (pairBits (encodeCNF φ) w)) pairPreludeProg :=
    programBoundedIn_mono pairPreludeProg hprelude_le hprelude
  have hτ_le : StoreValuesLe B (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) :=
    program_eval_storeValuesLe (bitInputStore (pairBits (encodeCNF φ) w)) pairPreludeProg
      hB1 hσ0_le hp ScanFree_pairPreludeProg
  exact ⟨hp, hτ_le, hSpec⟩

lemma satVerifierProg_bounded_in_phase2 (φ : CNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      (bitInputStore (pairBits (encodeCNF φ) w)) pairPreludeProg ∧
    ProgramBoundedIn (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)))
      (Program.assign 15 (Expr.const 1)) ∧
    ProgramBoundedIn (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      ((Program.assign 15 (Expr.const 1)).eval
        (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))))
      (decodeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 14 15 0) := by
  have hLeq : (pairBits (encodeCNF φ) w).length = 2 * (encodeCNF φ).length + 1 + w.length :=
    pairBits_length (encodeCNF φ) w
  obtain ⟨hp1, hτ_le, _⟩ := satVerifierProg_bounded_in_phase1 φ w
  set L := (pairBits (encodeCNF φ) w).length with hLdef
  set B := 200 * (L+1)^4 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith [pow_pos (show 0 < L+1 by omega) 4]
  set τ := pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w)) with hτdef
  set σ3 := (Program.assign 15 (Expr.const 1)).eval τ with hσ3def
  have hphase2 := satVerifierProg_phase2 φ w
  rw [← hσ3def, ← hτdef] at hphase2
  rcases hphase2 with ⟨hSpec, hσ30, hσ31, _, hσ35, _, _, _⟩
  rw [← hLdef] at hσ30
  have hp3 : ProgramBoundedIn B τ (Program.assign 15 (Expr.const 1)) := by
    refine ⟨by have := hB1; omega, ?_⟩
    simp only [ExprBoundedIn]
    omega
  have hσ3_le : StoreValuesLe B σ3 :=
    program_eval_storeValuesLe τ (Program.assign 15 (Expr.const 1)) hB1 hτ_le hp3 trivial
  have hXend : τ 1 + (encodeCNF φ).length ≤ pairPreludeBound L := by
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
  have hσ3houter : σ3 1 + σ3 0 + σ3 0 * (1 + σ3 0 + σ3 0 * (σ3 0 + 1)) +
      2 + 2 * σ3 0 + σ3 0 * (σ3 0 + 1) ≤ B := by
    rw [hσ31, hσ30, hBdef]
    have haddr' : τ 1 ≤ 5 * L + 101 := by simpa [pairPreludeBound] using haddr
    nlinarith [haddr', sq_nonneg L, sq_nonneg (L * L)]
  have hp4 : ProgramBoundedIn B σ3
      (decodeCNFEvalProgramAt 1 6 7 9 8 10 11 12 13 5 14 15 0) :=
    programBoundedIn_decodeCNFEvalProgramAt_of_store_bounds B 1 6 7 9 8 10 11 12 13 5 14 15 0 σ3
      hσ3_le
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      (hcl := by omega) (hld := by omega) (hrc := by omega) (hcbit := by omega)
      (hcval := by omega) (hcsat := by omega) (hbl := by omega) (hbb := by omega)
      (hbval := by omega) (hbs := by omega) (hbk := by omega) (hck := by omega)
      (hrs := by omega) (hsd := by omega) (hsl := by omega) (hcw := by omega)
      (hpw := by omega) (hvw := by omega) (hdw := by omega) (hrw := by omega)
      (hbw := by omega) (hvalw := by omega) (hsw := by omega) (hlw := by omega)
      (hkw := by omega) (hrv := by omega) (hco := by omega) (hdo := by omega)
      (hoBnd := by omega) (how := by omega) (hB1 := hB1) (hwbudget := hσ3wbudget)
      (houterCoarse := hσ3houter)
  exact ⟨hp1, hp3, hp4⟩

lemma satVerifierProg_bounded_in (φ : CNF) (w : List Bool) :
    ProgramBoundedIn (200 * ((pairBits (encodeCNF φ) w).length+1)^4)
      (bitInputStore (pairBits (encodeCNF φ) w)) satVerifierProg := by
  obtain ⟨hp1, _, _⟩ := satVerifierProg_bounded_in_phase1 φ w
  obtain ⟨_, hp2, hp3⟩ := satVerifierProg_bounded_in_phase2 φ w
  unfold satVerifierProg
  exact programBoundedIn_seq pairPreludeProg _ _ (bitInputStore (pairBits (encodeCNF φ) w)) hp1
    (programBoundedIn_seq (Program.assign 15 (.const 1)) _ _
      (pairPreludeProg.eval (bitInputStore (pairBits (encodeCNF φ) w))) hp2 hp3)

/-! ## `cost_le` / `compiled_operands_le`

`CostEnvelope satVerifierProg` is a structural, register-independent expression in the store's
values, so composing it with `B := 200 * (X+1)^4` gives a genuine `Polynomial ℕ`
(`satVerifierCostPoly`) via `uniformCostEnvelopePoly`. `polynomial_nat_eval_le_power` turns that
into a `c * (N+1)^c` bound (`satVerifierCostC`), the shape `BoundedWhileDecider.cost_le` needs;
`compiledOperandBound_of_programBoundedIn` reuses the same `ProgramBoundedIn`/`ScanFree` facts for
the bit-cost side, at `bitLen B ≤ c * (N+1)^c` (via `bitLen_le_succ`). -/

noncomputable def satVerifierCostPoly : Polynomial ℕ :=
  (uniformCostEnvelopePoly satVerifierProg).comp (C 200 * (X + 1)^4)

lemma sat_verifier_costEnvelope_le_poly (N : ℕ) :
    CostEnvelope satVerifierProg (200 * (N+1)^4) ≤ satVerifierCostPoly.eval N := by
  rw [satVerifierCostPoly, Polynomial.eval_comp, uniformCostEnvelopePoly_eval]
  simp

noncomputable def satVerifierCostC : ℕ :=
  1000 + (satVerifierCostPoly.support.card + 1) *
    (satVerifierCostPoly.support.sup (fun n => satVerifierCostPoly.coeff n) + 1) *
    (satVerifierCostPoly.support.sup id + 1)

lemma satVerifierCostPoly_le_power (N : ℕ) :
    satVerifierCostPoly.eval N ≤ satVerifierCostC * (N + 1) ^ satVerifierCostC := by
  have h := polynomial_nat_eval_le_power satVerifierCostPoly N
  set c := (satVerifierCostPoly.support.card + 1) *
    (satVerifierCostPoly.support.sup (fun n => satVerifierCostPoly.coeff n) + 1) *
    (satVerifierCostPoly.support.sup id + 1) with hcdef
  have hcle : c ≤ satVerifierCostC := by unfold satVerifierCostC; omega
  calc satVerifierCostPoly.eval N ≤ c * (N+1)^c := h
    _ ≤ satVerifierCostC * (N+1)^satVerifierCostC := by
        apply Nat.mul_le_mul hcle
        exact Nat.pow_le_pow_right (by omega) hcle

lemma satVerifierCostC_ge300 : (300:ℕ) ≤ satVerifierCostC := by
  unfold satVerifierCostC; omega

/-! ## The decider -/

/-- The `BoundedWhileDecider` packaging `satVerifierProg` against the promise-everywhere domain
    `D := fun _ => True`, deciding `cnfSatBool xw.2 xw.1 = true` at the shared polynomial exponent
    `satVerifierCostC`. -/
noncomputable def satVerifierDecider :
    BoundedWhileDecider (fun xw : CNF × List Bool => pairBits (encodeCNF xw.1) xw.2)
      (fun _ => True) (fun xw => cnfSatBool xw.2 xw.1 = true) where
  p := satVerifierProg
  outReg := 15
  c := satVerifierCostC
  correct := by
    intro x _
    rw [satVerifierProg_correct x.1 x.2]
    split_ifs with hc <;> simp_all
  cost_le := by
    intro x _
    have hp := satVerifierProg_bounded_in x.1 x.2
    set N := (pairBits (encodeCNF x.1) x.2).length with hNdef
    have hσle : StoreValuesLe (200 * (N+1)^4) (bitInputStore (pairBits (encodeCNF x.1) x.2)) := by
      intro i
      cases i with
      | zero => show (pairBits (encodeCNF x.1) x.2).length ≤ _
                rw [← hNdef]; nlinarith [sq_nonneg N]
      | succ i =>
          simp only [bitInputStore]
          split <;> nlinarith [pow_pos (show 0 < N+1 by omega) 4]
    have hB1 : (1:ℕ) ≤ 200*(N+1)^4 := by nlinarith [pow_pos (show 0 < N+1 by omega) 4]
    have hcost := program_cost_le_CostEnvelope_of_bounded satVerifierProg (200*(N+1)^4)
      (bitInputStore (pairBits (encodeCNF x.1) x.2)) hB1 hσle hp scanFree_satVerifierProg
    have hcostpoly := sat_verifier_costEnvelope_le_poly N
    have hcostpow := satVerifierCostPoly_le_power N
    show satVerifierProg.cost (bitInputStore (pairBits (encodeCNF x.1) x.2)) ≤
      satVerifierCostC * (N + 1) ^ satVerifierCostC
    omega
  bit_c := satVerifierCostC
  compiled_operands_le := by
    intro x _
    set N := (pairBits (encodeCNF x.1) x.2).length with hNdef
    refine ⟨bitLen (200*(N+1)^4), ?_, ?_⟩
    · have hbl := bitLen_le_succ (200*(N+1)^4)
      have hpos : (1:ℕ) ≤ (N+1)^4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpow4 : (N+1)^4 ≤ (N+1)^satVerifierCostC :=
        Nat.pow_le_pow_right (by omega) (by have := satVerifierCostC_ge300; omega)
      have h1 : satVerifierCostC * (N+1)^4 ≤ satVerifierCostC * (N+1)^satVerifierCostC :=
        Nat.mul_le_mul_left satVerifierCostC hpow4
      have h2 : 300 * (N+1)^4 ≤ satVerifierCostC * (N+1)^4 :=
        Nat.mul_le_mul_right _ satVerifierCostC_ge300
      nlinarith [hbl, hpos, h1, h2]
    · have hp := satVerifierProg_bounded_in x.1 x.2
      have hσle : StoreValuesLe (200 * (N+1)^4) (bitInputStore (pairBits (encodeCNF x.1) x.2)) := by
        intro i
        cases i with
        | zero => show (pairBits (encodeCNF x.1) x.2).length ≤ _
                  rw [← hNdef]; nlinarith [sq_nonneg N]
        | succ i =>
            simp only [bitInputStore]
            split <;> nlinarith [pow_pos (show 0 < N+1 by omega) 4]
      have hB1 : (1:ℕ) ≤ 200*(N+1)^4 := by nlinarith [pow_pos (show 0 < N+1 by omega) 4]
      exact compiledOperandBound_of_programBoundedIn satVerifierProg
        (pairBits (encodeCNF x.1) x.2) (200*(N+1)^4) hB1 hσle hp scanFree_satVerifierProg

end NPComplete.CookLevin

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Verifier.DepairProg
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatLoaderRelocate
public import NPComplete.RAMToTM.Generic.Api.ProgramCostBounds

/-!
# Public contract of the pair-splitting prelude

`InNP.of_bounded_while_verifier` gives every verifier the paired input `pairBits (enc x) w` on the
canonical `bitInputStore` loader, and each verifier begins by splitting that pair. The composition
here exposes the resulting read-back regions and a conservative bound without making callers depend
on the intermediate relocation layout.

The register arguments of the two stages are fixed (`depairProg 1 2 3 4 5`): `BoundedWhileDecider`
requires one shared `Program`, and fixing the registers lets the contract name the published output
registers directly. Registers 1 and 5 publish the two bases, register 3 records `x.length`, and
registers 2 and 4 remain scratch. The low registers are excluded from the input frame because the
relocation stage writes its controls at offsets from the input length.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM (ProgramBoundedIn ScanFree LoadRelocInput BitsFrom bitInputStore
  bitInputStore_eq_zero_of_ge_inputEnd loadRelocProg loadRelocControlGap)
open NPComplete.BoundedWhile (Program Store Expr writeReg eval_seq eval_forN loopEval
  loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits)

/-- The whole prelude: relocate the paired input to the runtime-computed wide-gap base, then
split it into the instance half and the certificate half. -/
@[construction_api] def pairPreludeProg : Program :=
  loadRelocProg.seq (depairProg 1 2 3 4 5)

/-- The single cell/register budget the prelude promises: every cell or register the run writes
stays below it, and both published output regions fit under it. Linear in `L`, so a downstream
stage can add its own budget and stay linear. -/
@[construction_api] def pairPreludeBound (L : ℕ) : ℕ := 5 * L + 101

/-- The public post-state of one `pairPreludeProg` run from an initial store `σ` to `τ`.
Registers 0 and 3 publish the paired-input and instance lengths, registers 1 and 5 publish the
bases of `x` and `w`, and the bit equations make both regions directly readable. The contract
ensures `100 ≤ τ 5 < τ 1`: the witness base is at least 100 and below the instance base. Callers may
use registers 0 through 99 as their own control band without colliding with either published
region. These are workspace and ordering guarantees, not a placement formula. The frame keeps input
cells above the scratch registers and cells beyond the shared budget unchanged. -/
@[construction_api] structure PairPreludeSpec (x w : Bits) (σ τ : Store) : Prop where
  input_length : τ 0 = (pairBits x w).length
  x_length : τ 3 = x.length
  bases : 100 ≤ τ 5 ∧ τ 5 < τ 1
  x_bits : ∀ i, (h : i < x.length) →
    τ (τ 1 + i) = if x[i] then 1 else 0
  w_bits : ∀ i, i < max x.length w.length →
    τ (τ 5 + i) = if w.getD i false then 1 else 0
  x_end_le : τ 1 + x.length ≤ pairPreludeBound (pairBits x w).length
  w_read_end_le :
    τ 5 + max x.length w.length ≤ pairPreludeBound (pairBits x w).length
  input_frame : ∀ r, 5 < r → r ≤ (pairBits x w).length → τ r = σ r
  tail_frame : ∀ r, pairPreludeBound (pairBits x w).length < r → τ r = σ r

lemma pair_prelude_loader_facts (x w : Bits) (L : ℕ) (σ0 σ1 : Store)
    (hLdef : L = (pairBits x w).length)
    (hσ0 : σ0 = bitInputStore (pairBits x w))
    (hσ1 : σ1 = loadRelocProg.eval σ0) :
    σ1 0 = L ∧
    NPComplete.RAMToTM.BitsFrom σ1 (depairRelocBase L) (pairBits x w) ∧
    ∀ r, depairRelocBase L + L ≤ r → r < depairCnfDst L → σ1 r = 0 := by
  have hin : LoadRelocInput σ0 (pairBits x w) := by
    rw [hσ0]
    exact NPComplete.RAMToTM.loadRelocInput_bitInputStore (pairBits x w)
  have hfinal := NPComplete.RAMToTM.loadRelocProg_final_state σ0 (pairBits x w) hin
  have h0 : σ1 0 = L := by
    rw [hσ1, hfinal.1, hLdef]
  have haddr : (pairBits x w).length + ((pairBits x w).length + loadRelocControlGap) =
      depairRelocBase L := by
    rw [← hLdef]
    simp only [depairRelocBase, loadRelocControlGap]
    omega
  have hbitsRaw := NPComplete.RAMToTM.loadRelocProg_output_bits σ0 (pairBits x w) hin
  have hbits : NPComplete.RAMToTM.BitsFrom σ1 (depairRelocBase L) (pairBits x w) := by
    simpa [hσ1, haddr] using hbitsRaw
  refine ⟨h0, hbits, ?_⟩
  intro r hr1 hr2
  have hframeBound : (pairBits x w).length + ((pairBits x w).length + loadRelocControlGap) +
      (pairBits x w).length ≤ r := by
    simp only [depairRelocBase, loadRelocControlGap] at hr1 ⊢
    rw [hLdef] at hr1
    omega
  have hframe := NPComplete.RAMToTM.loadRelocProg_frame_two_sided σ0 (pairBits x w) hin r
    (Or.inr hframeBound)
  have hrInput : (pairBits x w).length + 1 ≤ r := by
    rw [← hLdef]
    simp only [depairRelocBase] at hr1
    omega
  rw [hσ1, hframe, hσ0]
  exact bitInputStore_eq_zero_of_ge_inputEnd (pairBits x w) r hrInput

lemma pair_prelude_depair_frame (x w : Bits) (L r : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hbits : NPComplete.RAMToTM.BitsFrom σ (depairRelocBase L) (pairBits x w))
    (hr1 : r ≠ 1) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hr4 : r ≠ 4) (hr5 : r ≠ 5)
    (hdst : ∀ i, i < x.length → r ≠ depairCnfDst L + i) :
    (depairProg 1 2 3 4 5).eval σ r = σ r := by
  have hloop := depairProg_loop_correct 1 2 3 4
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    x w L σ h0 hL
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) (by simp [depairRelocBase]) hbits
  obtain ⟨hloop0, _, _, _, _, hframe⟩ := hloop
  have hpost := depairProg_postproc_eval 1 5 _ L hloop0 (by omega) (by omega)
  rw [depairProg_eval_eq, hpost.2.2 r hr5 hr1]
  exact hframe r hr1 hr2 hr3 hr4 hdst

lemma pair_prelude_depair_count (x w : Bits) (L : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hbits : NPComplete.RAMToTM.BitsFrom σ (depairRelocBase L) (pairBits x w)) :
    (depairProg 1 2 3 4 5).eval σ 3 = x.length := by
  set τ0 := (depairSetup 1 2 3 4).eval σ with hτ0
  have hτ0eq : τ0 =
      writeReg (writeReg (writeReg (writeReg σ 1 (depairRelocBase L))
        2 (depairCnfDst L)) 3 0) 4 0 := by
    rw [hτ0]
    exact depairSetup_eval 1 2 3 4 σ L h0 (by omega)
  have hτ00 : τ0 0 = L := by
    rw [hτ0eq, writeReg_diff _ 4 _ 0 (by omega), writeReg_diff _ 3 _ 0 (by omega),
      writeReg_diff _ 2 _ 0 (by omega), writeReg_diff _ 1 _ 0 (by omega), h0]
  have hτ01 : τ0 1 = depairRelocBase L := by
    rw [hτ0eq, writeReg_diff _ 4 _ 1 (by omega), writeReg_diff _ 3 _ 1 (by omega),
      writeReg_diff _ 2 _ 1 (by omega), writeReg_same]
  have hτ02 : τ0 2 = depairCnfDst L := by
    rw [hτ0eq, writeReg_diff _ 4 _ 2 (by omega), writeReg_diff _ 3 _ 2 (by omega),
      writeReg_same]
  have hτ03 : τ0 3 = 0 := by
    rw [hτ0eq, writeReg_diff _ 4 _ 3 (by omega), writeReg_same]
  have hτ04 : τ0 4 = 0 := by
    rw [hτ0eq, writeReg_same]
  have hbits' : NPComplete.RAMToTM.BitsFrom σ (depairRelocBase L)
      (doubleBits x ++ (false :: w)) := by
    rw [pairBits_eq_doubleBits] at hbits
    exact hbits
  have hbits0 : NPComplete.RAMToTM.BitsFrom τ0 (depairRelocBase L)
      (doubleBits x ++ (false :: w)) := by
    rw [hτ0eq]
    exact NPComplete.RAMToTM.bitsFrom_writeReg
      (NPComplete.RAMToTM.bitsFrom_writeReg
        (NPComplete.RAMToTM.bitsFrom_writeReg
          (NPComplete.RAMToTM.bitsFrom_writeReg hbits' 1 (depairRelocBase L)
            (by simp [depairRelocBase]))
          2 (depairCnfDst L) (by simp [depairRelocBase]))
        3 0 (by simp [depairRelocBase]))
      4 0 (by simp [depairRelocBase])
  have hlen : (doubleBits x ++ (false :: w)).length = L := by
    simp [doubleBits_length, hL]
    omega
  have hexact := depair_exact_correct 1 2 3 4
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    x w (depairRelocBase L) (depairCnfDst L) 0 τ0
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by rw [hlen]; simp only [depairCnfDst]; omega)
    hτ01 hτ02 hτ03 hτ04 hbits0
  have hsplit : L = (x.length + 1) + (L - (x.length + 1)) := by omega
  have hdone : (loopEval (depairStep 1 2 3 4) (x.length + 1) τ0) 4 ≠ 0 := by
    have hh := hexact.2.2.2.1
    omega
  have hfreeze := loopEval_depairStep_done 1 2 3 4
    (loopEval (depairStep 1 2 3 4) (x.length + 1) τ0) (L - (x.length + 1)) hdone
  have hcountLoop : (loopEval (depairStep 1 2 3 4) L τ0) 3 = x.length := by
    rw [hsplit, NPComplete.RAMToTM.loopEval_add, hfreeze]
    simpa using hexact.2.2.1
  have hloop := depairProg_loop_correct 1 2 3 4
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    x w L σ h0 hL
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) (by simp [depairRelocBase]) hbits
  have hcountFor :
      (((depairSetup 1 2 3 4).seq (Program.forN (Expr.reg 0) (depairStep 1 2 3 4))).eval σ) 3 =
        x.length := by
    rw [eval_seq, ← hτ0, eval_forN, Expr.eval, hτ00]
    exact hcountLoop
  have hpost := depairProg_postproc_eval 1 5 _ L hloop.1 (by omega) (by omega)
  rw [depairProg_eval_eq, hpost.2.2 3 (by omega) (by omega)]
  exact hcountFor

lemma pair_prelude_relocated_witness_bits (x w : Bits) (L : ℕ) (σ : Store)
    (hbits : NPComplete.RAMToTM.BitsFrom σ (depairRelocBase L) (pairBits x w)) :
    NPComplete.RAMToTM.BitsFrom σ (depairWitnessBase L x.length) w := by
  have hbits' : NPComplete.RAMToTM.BitsFrom σ (depairRelocBase L)
      (doubleBits x ++ (false :: w)) := by
    rw [pairBits_eq_doubleBits] at hbits
    exact hbits
  obtain ⟨_, htail⟩ := NPComplete.RAMToTM.bitsFrom_append σ (depairRelocBase L)
    (doubleBits x) (false :: w) hbits'
  obtain ⟨_, hw⟩ := NPComplete.RAMToTM.bitsFrom_cons σ
    (depairRelocBase L + (doubleBits x).length) false w htail
  have heq : depairRelocBase L + (doubleBits x).length + 1 = depairWitnessBase L x.length := by
    simp [depairWitnessBase, doubleBits_length]
  rw [heq] at hw
  exact hw

lemma pair_prelude_spec (x w : Bits) :
    PairPreludeSpec x w (bitInputStore (pairBits x w))
      (pairPreludeProg.eval (bitInputStore (pairBits x w))) := by
  set L := (pairBits x w).length with hLdef
  have hL : L = 2 * x.length + 1 + w.length := by
    rw [hLdef]
    exact pairBits_length x w
  let σ0 := bitInputStore (pairBits x w)
  let σ1 := loadRelocProg.eval σ0
  have hloader := pair_prelude_loader_facts x w L σ0 σ1 hLdef rfl rfl
  have h0 := hloader.1
  have hbits := hloader.2.1
  have hzero := hloader.2.2
  have hin : LoadRelocInput σ0 (pairBits x w) := by
    simpa [σ0] using NPComplete.RAMToTM.loadRelocInput_bitInputStore (pairBits x w)
  have hcor := depairProg_correct 1 2 3 4 5
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    x w L σ1 h0 hL
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) hbits
  have hwit := depairProg_witness_correct 1 2 3 4 5
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    x w L σ1 h0 hL
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) (by simp [depairRelocBase])
    (by simp [depairRelocBase]) hbits hzero
  have hWbits := pair_prelude_relocated_witness_bits x w L σ1 hbits
  have hcount := pair_prelude_depair_count x w L σ1 h0 hL hbits
  have hfinal0 : (depairProg 1 2 3 4 5).eval σ1 0 = L := by
    have hf := pair_prelude_depair_frame x w L 0 σ1 h0 hL hbits
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro i hi; simp [depairCnfDst, depairRelocBase]; omega)
    rw [hf]
    exact h0
  have hDend : depairCnfDst L + x.length ≤ pairPreludeBound L := by
    simp [pairPreludeBound, depairCnfDst, depairRelocBase]
    omega
  have hmax : max x.length w.length ≤ L := max_le (by omega) (by omega)
  have hRun : pairPreludeProg.eval (bitInputStore (pairBits x w)) =
      (depairProg 1 2 3 4 5).eval σ1 := by
    simp [pairPreludeProg, σ0, σ1, eval_seq]
  rw [hRun]
  change PairPreludeSpec x w σ0 ((depairProg 1 2 3 4 5).eval σ1)
  refine ⟨hfinal0, hcount, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcor.1, hcor.2.1]
    simp [depairWitnessBase, depairCnfDst, depairRelocBase]
    omega
  · intro i hi
    rw [hcor.2.1]
    exact hcor.2.2.1 i hi
  · intro i hi
    rw [hcor.1]
    by_cases hiw : i < w.length
    · rw [hwit.1 i hiw, hWbits i hiw, List.getD_eq_getElem _ false hiw]
    · have hix : i < x.length := by
        by_contra hn
        have hxle : x.length ≤ i := Nat.le_of_not_gt hn
        have hwle : w.length ≤ i := Nat.le_of_not_gt hiw
        have hm : max x.length w.length ≤ i := max_le hxle hwle
        omega
      have hread := hwit.2 i (Nat.le_of_not_gt hiw) hix
      have hfalse : w.getD i false = false := by
        simp [List.getD_eq_getElem?_getD, hiw]
      rw [hread, hfalse]
      rfl
  · rw [hcor.2.1, ← hLdef]
    simp [pairPreludeBound, depairCnfDst, depairRelocBase]
    omega
  · rw [hcor.1, ← hLdef]
    simp [pairPreludeBound, depairWitnessBase, depairRelocBase]
    omega
  · intro r hr5 hrL
    have hdepair := pair_prelude_depair_frame x w L r σ1 h0 hL hbits
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro i hi; simp [depairCnfDst, depairRelocBase]; omega)
    have hloader := NPComplete.RAMToTM.loadRelocProg_frame_two_sided σ0 (pairBits x w) hin r
      (Or.inl (by omega))
    rw [hdepair]
    change loadRelocProg.eval σ0 r = σ0 r
    exact hloader
  · intro r hr
    have hrB : pairPreludeBound L < r := by simpa [hLdef] using hr
    have hrgt5 : 5 < r := by
      have hfive : 5 < pairPreludeBound L := by simp [pairPreludeBound]
      omega
    have hdepair := pair_prelude_depair_frame x w L r σ1 h0 hL hbits
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro i hi; have := hDend; omega)
    have hloaderBound : (pairBits x w).length + ((pairBits x w).length + loadRelocControlGap) +
        (pairBits x w).length ≤ r := by
      have hbound : pairPreludeBound (pairBits x w).length < r := by
        simpa [hLdef] using hrB
      simp only [loadRelocControlGap, pairPreludeBound] at hbound ⊢
      omega
    have hloader := NPComplete.RAMToTM.loadRelocProg_frame_two_sided σ0 (pairBits x w) hin r
      (Or.inr hloaderBound)
    rw [hdepair]
    change loadRelocProg.eval σ0 r = σ0 r
    exact hloader

lemma pair_prelude_programBoundedIn (x w : Bits) :
    ProgramBoundedIn (pairPreludeBound (pairBits x w).length)
      (bitInputStore (pairBits x w)) pairPreludeProg := by
  set L := (pairBits x w).length with hLdef
  have hL : L = 2 * x.length + 1 + w.length := by
    rw [hLdef]
    exact pairBits_length x w
  let σ0 := bitInputStore (pairBits x w)
  let σ1 := loadRelocProg.eval σ0
  have h0 : σ0 0 = L := by
    change (pairBits x w).length = L
    exact hLdef.symm
  have hloader := pair_prelude_loader_facts x w L σ0 σ1 hLdef rfl rfl
  have hbits := hloader.2.1
  have hloadBound : ProgramBoundedIn (pairPreludeBound L) σ0 loadRelocProg :=
    NPComplete.RAMToTM.loadRelocProg_programBoundedIn σ0 L (pairPreludeBound L) h0
      (by simp [pairPreludeBound, loadRelocControlGap]; omega)
  have hdepairBound : ProgramBoundedIn (pairPreludeBound L) σ1 (depairProg 1 2 3 4 5) :=
    depairProg_programBoundedIn 1 2 3 4 5
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by change 1 ≤ 5 * L + 101; omega)
      (by change 2 ≤ 5 * L + 101; omega)
      (by change 3 ≤ 5 * L + 101; omega)
      (by change 4 ≤ 5 * L + 101; omega)
      (by change 5 ≤ 5 * L + 101; omega)
      (by change 1 ≤ 5 * L + 101; omega)
      x w L σ1 hloader.1 hL
      (by simp [depairRelocBase]) (by simp [depairRelocBase])
      (by simp [depairRelocBase]) (by simp [depairRelocBase]) hbits
      (by simp only [pairPreludeBound, depairCnfDst, depairRelocBase]; omega)
  have hseq := NPComplete.RAMToTM.programBoundedIn_seq loadRelocProg
    (depairProg 1 2 3 4 5) (pairPreludeBound L) σ0 hloadBound hdepairBound
  simpa [pairPreludeProg, hLdef] using hseq

/-- The two stages both avoid `scanList` and `lookup`, so their composition has the same property. -/
@[construction_api] lemma ScanFree_pairPreludeProg : ScanFree pairPreludeProg := by
  simp [pairPreludeProg, ScanFree, NPComplete.RAMToTM.scanFree_loadRelocProg, scanFree_depairProg]

/-- The contract and the prelude's access bound hold on the canonical paired-input store. -/
@[construction_api] lemma pairPreludeProg_runs (x w : Bits) :
    PairPreludeSpec x w (bitInputStore (pairBits x w))
      (pairPreludeProg.eval (bitInputStore (pairBits x w))) ∧
    ProgramBoundedIn (pairPreludeBound (pairBits x w).length)
      (bitInputStore (pairBits x w)) pairPreludeProg := by
  exact ⟨pair_prelude_spec x w, pair_prelude_programBoundedIn x w⟩

end NPComplete.CookLevin

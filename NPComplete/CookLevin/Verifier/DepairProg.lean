module

public import NPComplete.CookLevin.Verifier.DepairBounded
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
`depairStep` (`Depair.lean`) and its loop correctness/boundedness facts (`DepairBounded.lean`)
assume a caller-supplied, statically fixed copy destination. That assumption breaks for
`sat_inNP`'s machine half: `BoundedWhileDecider.p : Program` must be a single `Program` shared by
every `CNF`, but the destination a real de-pair run needs depends on `(encodeCNF φ).length`, which
varies with `φ`. This module closes that gap: `depairProg` computes its own destination and cursor
addresses at run time from `register 0` (which the surrounding pipeline, following the
`bitInputStore`/`loadRelocProg` convention, always holds the relocated input's total bit length),
mirroring `ThreeSatLoaderRelocate.lean`'s `loadRelocProg` design for the same problem (dynamic
placement driven by a runtime-computed `Expr`, not a caller-supplied constant).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits)

/-! ## Layout

`register 0` holds `L := (pairBits x w).length = 2 * x.length + 1 + w.length` for the `x`/`w` a
run actually decodes — the same convention `loadRelocProg` uses for its own input length. Every
other address below is computed from `L` alone, so a single `depairProg` value works uniformly
across every `CNF`. -/

/-- The relocated pairing region's base address, matching `loadRelocProg`'s own wide-gap
    destination (`2 * N + 100`) for `N := L`: the caller is expected to have already copied
    `pairBits x w` to this address (via `loadRelocProg` itself) before running `depairProg`. -/
def depairRelocBase (L : ℕ) : ℕ := 2 * L + 100

/-- The de-pair scan's CNF destination. This is `depairRelocBase L + 2 * L`, not
    `depairRelocBase L + L` (which would just clear the source): the extra `L` cells of headroom
    give the witness-offset zero-padding gap (`depairWitnessBase_add_mem_gap`) room to sit between
    the relocated region's end and this destination, entirely disjoint from it. -/
def depairCnfDst (L : ℕ) : ℕ := depairRelocBase L + 2 * L

/-- The certificate's base address once the de-pair loop reaches the separator — `depairRelocBase
    L + 2 * n + 1`, i.e. right after `pairBits`'s doubled `n`-bit prefix and its separator, at the
    relocated position where `loadRelocProg` already placed it. -/
def depairWitnessBase (L n : ℕ) : ℕ := depairRelocBase L + 2 * n + 1

lemma depairCnfDst_eq (L : ℕ) : depairCnfDst L = depairRelocBase L + 2 * L := rfl

lemma depairRelocBase_le_depairCnfDst (L : ℕ) : depairRelocBase L ≤ depairCnfDst L := by
  simp only [depairCnfDst]; omega

lemma depairWitnessBase_ge (L n : ℕ) : depairRelocBase L ≤ depairWitnessBase L n := by
  simp only [depairWitnessBase]; omega

/-- The CNF destination's write range `[depairCnfDst L, depairCnfDst L + n)` never overlaps a
    witness-offset cell `depairWitnessBase L n + v` as long as `v` stays under the full budget
    `L = 2 * n + 1 + m` — the frame condition `depairProg_correct` needs at every witness offset,
    not just the in-range ones. -/
lemma depairWitnessBase_add_lt_disjoint (L n m v i : ℕ) (hL : L = 2 * n + 1 + m) (hv : v < L)
    : depairWitnessBase L n + v ≠ depairCnfDst L + i := by
  simp only [depairWitnessBase, depairCnfDst]; omega

/-- If `L = 2 * n + 1 + m`, every witness offset `depairWitnessBase L n + v` with `m ≤ v < n` lies in
    the zero-padding gap `[depairRelocBase L + L, depairCnfDst L)` between the relocated pairing
    region's end and the CNF destination. These are the out-of-range reads the witness lookup must
    see as zero once `v` runs past the real certificate. -/
lemma depairWitnessBase_add_mem_gap (L n m v : ℕ) (hL : L = 2 * n + 1 + m)
    (hv1 : m ≤ v) (hv2 : v < n) :
    depairRelocBase L + L ≤ depairWitnessBase L n + v ∧
    depairWitnessBase L n + v < depairCnfDst L := by
  simp only [depairWitnessBase, depairCnfDst, depairRelocBase]; omega

/-! ## Setup: computing `depairRelocBase L`/`depairCnfDst L` from `register 0` -/

/-- `cursorReg`'s initial value, `register 0` added to itself plus the `loadRelocProg`-style gap
    constant `100` — the `Expr` form of `depairRelocBase`. -/
def depairCursorInitExpr : Expr := .add (.reg 0) (.add (.reg 0) (.const 100))

/-- `dstReg`'s initial value, `depairCursorInitExpr` plus `register 0` doubled again — the `Expr`
    form of `depairCnfDst`. -/
def depairDstInitExpr : Expr := .add depairCursorInitExpr (.add (.reg 0) (.reg 0))

lemma depairCursorInitExpr_eval (σ : Store) (L : ℕ) (h0 : σ 0 = L) :
    depairCursorInitExpr.eval σ = depairRelocBase L := by
  simp only [depairCursorInitExpr, depairRelocBase, Expr.eval, h0]; omega

lemma depairDstInitExpr_eval (σ : Store) (L : ℕ) (h0 : σ 0 = L) :
    depairDstInitExpr.eval σ = depairCnfDst L := by
  simp only [depairDstInitExpr, depairCnfDst, Expr.eval, depairCursorInitExpr_eval σ L h0, h0]
  omega

lemma depairCursorInitExpr_bounded_in (σ : Store) (L B : ℕ) (h0 : σ 0 = L)
    (hB : depairCnfDst L ≤ B) : ExprBoundedIn B σ depairCursorInitExpr := by
  simp only [depairCursorInitExpr, ExprBoundedIn, Expr.eval, h0, depairCnfDst,
    depairRelocBase] at hB ⊢
  omega

lemma depairDstInitExpr_bounded_in (σ : Store) (L B : ℕ) (h0 : σ 0 = L)
    (hB : depairCnfDst L ≤ B) : ExprBoundedIn B σ depairDstInitExpr := by
  simp only [depairDstInitExpr, depairCursorInitExpr, ExprBoundedIn, Expr.eval, h0, depairCnfDst,
    depairRelocBase] at hB ⊢
  omega

/-- Initialize the four `depairStep` control registers: `cursorReg` at `depairRelocBase L`,
    `dstReg` at `depairCnfDst L`, and `countReg`/`doneReg` at `0`. -/
def depairSetup (cursorReg dstReg countReg doneReg : ℕ) : Program :=
  .seq (.assign cursorReg depairCursorInitExpr)
    (.seq (.assign dstReg depairDstInitExpr)
      (.seq (.assign countReg (.const 0))
        (.assign doneReg (.const 0))))

lemma depairSetup_eval (cursorReg dstReg countReg doneReg : ℕ) (σ : Store) (L : ℕ)
    (h0 : σ 0 = L) (hc0 : cursorReg ≠ 0) :
    (depairSetup cursorReg dstReg countReg doneReg).eval σ =
      writeReg (writeReg (writeReg (writeReg σ cursorReg (depairRelocBase L))
        dstReg (depairCnfDst L)) countReg 0) doneReg 0 := by
  have hσ0 : (writeReg σ cursorReg (depairRelocBase L)) 0 = L := by
    rw [writeReg_diff σ cursorReg (depairRelocBase L) 0 (Ne.symm hc0), h0]
  unfold depairSetup
  simp only [eval_seq, eval_assign, Expr.eval, depairCursorInitExpr_eval σ L h0,
    depairDstInitExpr_eval _ L hσ0]

lemma depairSetup_programBoundedIn (cursorReg dstReg countReg doneReg : ℕ) (σ : Store) (L B : ℕ)
    (h0 : σ 0 = L) (hc0 : cursorReg ≠ 0)
    (hci : cursorReg ≤ B) (hdi : dstReg ≤ B) (hki : countReg ≤ B) (hni : doneReg ≤ B)
    (hB1 : 1 ≤ B) (hB : depairCnfDst L ≤ B) :
    ProgramBoundedIn B σ (depairSetup cursorReg dstReg countReg doneReg) := by
  have hp1 : ProgramBoundedIn B σ (.assign cursorReg depairCursorInitExpr) :=
    ⟨hci, depairCursorInitExpr_bounded_in σ L B h0 hB⟩
  set σ1 := (Program.assign cursorReg depairCursorInitExpr).eval σ with hσ1
  have h01 : σ1 0 = L := by
    rw [hσ1]; simp only [eval_assign]
    rw [writeReg_diff σ cursorReg _ 0 (Ne.symm hc0), h0]
  have hp2 : ProgramBoundedIn B σ1 (.assign dstReg depairDstInitExpr) :=
    ⟨hdi, depairDstInitExpr_bounded_in σ1 L B h01 hB⟩
  set σ2 := (Program.assign dstReg depairDstInitExpr).eval σ1 with hσ2
  have hp3 : ProgramBoundedIn B σ2 (.assign countReg (.const 0)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]; omega
  set σ3 := (Program.assign countReg (Expr.const 0)).eval σ2 with hσ3
  have hp4 : ProgramBoundedIn B σ3 (.assign doneReg (.const 0)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]; omega
  unfold depairSetup
  exact ⟨hp1, ⟨hp2, ⟨hp3, hp4⟩⟩⟩

/-- Running `depairStep` for `b ≥ a` iterations after it already reached the terminator (`doneReg
    ≠ 0`) at step `a` gives the same store as stopping at `a`: the extra `b - a` iterations are
    no-ops (`loopEval_depairStep_done`). Lets a `forN` loop's fixed bound (`register 0`'s full
    value `L`) be safely replaced by the exact terminating count `x.length + 1` once that count is
    known to be `≤ L`. -/
lemma loopEval_depairStep_eq_of_ge (cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (a b : ℕ) (hab : a ≤ b)
    (hd : (loopEval (depairStep cursorReg dstReg countReg doneReg) a σ) doneReg ≠ 0) :
    loopEval (depairStep cursorReg dstReg countReg doneReg) b σ =
      loopEval (depairStep cursorReg dstReg countReg doneReg) a σ := by
  have hsplit : b = a + (b - a) := by omega
  rw [hsplit, NPComplete.RAMToTM.loopEval_add]
  exact loopEval_depairStep_done cursorReg dstReg countReg doneReg _ (b - a) hd

/-! ## `depairProg`: setup, dynamic-count loop, and cursor/witness-base commit -/

/-- The full de-pair `Program`: `depairSetup` computes the dynamic addresses, `.forN (.reg 0)`
    runs `depairStep` for `L` iterations (safe: `L ≥ x.length + 1`, the exact terminating count,
    per `depair_exact_correct`; the rest are no-ops), then the trailing pair of assigns commits
    the loop's final cursor position into `wBaseReg` before resetting `cursorReg` to
    `depairCnfDst L` for the caller's subsequent CNF decode. -/
def depairProg (cursorReg dstReg countReg doneReg wBaseReg : ℕ) : Program :=
  .seq (depairSetup cursorReg dstReg countReg doneReg)
    (.seq (.forN (.reg 0) (depairStep cursorReg dstReg countReg doneReg))
      (.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)))

lemma depairProg_eval_eq (cursorReg dstReg countReg doneReg wBaseReg : ℕ) (σ : Store) :
    (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ =
      (Program.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)).eval
        (((depairSetup cursorReg dstReg countReg doneReg).seq
          (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ) := by
  unfold depairProg
  simp [eval_seq]

/-- The setup+loop stage's full transcript: `register 0` unchanged, the final control-register
    values (cursor at the witness base, `doneReg = 1`), the copied CNF/witness bits, and the frame
    condition over every cell outside the four control registers and the CNF write range. Reduces
    the `forN` loop's runtime bound `L` to the exact terminating count `x.length + 1`
    (`loopEval_depairStep_eq_of_ge`) and reuses `depair_exact_correct` for the rest. -/
lemma depairProg_loop_correct (cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hc0 : cursorReg ≠ 0) (hd0 : dstReg ≠ 0) (hk0 : countReg ≠ 0) (hn0 : doneReg ≠ 0)
    (x w : List Bool) (L : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hbits : BitsFrom σ (depairRelocBase L) (pairBits x w)) :
    ((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ
        0 = L ∧
    ((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ
        cursorReg = depairWitnessBase L x.length ∧
    ((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ
        doneReg = 1 ∧
    BitsFrom (((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ)
      (depairCnfDst L) x ∧
    BitsFrom (((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ)
      (depairWitnessBase L x.length) w ∧
    (∀ r, r ≠ cursorReg → r ≠ dstReg → r ≠ countReg → r ≠ doneReg →
      (∀ i, i < x.length → r ≠ depairCnfDst L + i) →
      ((depairSetup cursorReg dstReg countReg doneReg).seq
        (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg))).eval σ r
        = σ r) := by
  rw [eval_seq]
  set τ0 := (depairSetup cursorReg dstReg countReg doneReg).eval σ with hτ0
  have hτ0eq := depairSetup_eval cursorReg dstReg countReg doneReg σ L h0 hc0
  rw [← hτ0] at hτ0eq
  have hτ00 : τ0 0 = L := by
    rw [hτ0eq]
    rw [writeReg_diff _ doneReg _ 0 (Ne.symm hn0), writeReg_diff _ countReg _ 0 (Ne.symm hk0),
      writeReg_diff _ dstReg _ 0 (Ne.symm hd0), writeReg_diff _ cursorReg _ 0 (Ne.symm hc0), h0]
  have hbitsτ0 : BitsFrom τ0 (depairRelocBase L) (pairBits x w) := by
    rw [hτ0eq]
    exact bitsFrom_writeReg (bitsFrom_writeReg (bitsFrom_writeReg
      (bitsFrom_writeReg hbits cursorReg (depairRelocBase L) hca) dstReg (depairCnfDst L) hda)
      countReg 0 hka) doneReg 0 hna
  have hτ0c : τ0 cursorReg = depairRelocBase L := by
    rw [hτ0eq, writeReg_diff _ doneReg _ cursorReg hcDone,
      writeReg_diff _ countReg _ cursorReg hck0,
      writeReg_diff _ dstReg _ cursorReg hcd0, writeReg_same]
  have hτ0d : τ0 dstReg = depairCnfDst L := by
    rw [hτ0eq, writeReg_diff _ doneReg _ dstReg hdDone,
      writeReg_diff _ countReg _ dstReg hdk0, writeReg_same]
  have hτ0k : τ0 countReg = 0 := by
    rw [hτ0eq, writeReg_diff _ doneReg _ countReg hkDone, writeReg_same]
  have hτ0n : τ0 doneReg = 0 := by
    rw [hτ0eq, writeReg_same]
  have hτ0frame : ∀ r, r ≠ cursorReg → r ≠ dstReg → r ≠ countReg → r ≠ doneReg → τ0 r = σ r := by
    intro r h1 h2 h3 h4
    rw [hτ0eq, writeReg_diff _ doneReg _ r h4, writeReg_diff _ countReg _ r h3,
      writeReg_diff _ dstReg _ r h2, writeReg_diff _ cursorReg _ r h1]
  have hgap : depairRelocBase L + (doubleBits x ++ (false :: w)).length ≤ depairCnfDst L := by
    have hlen : (doubleBits x ++ (false :: w)).length = 2 * x.length + (w.length + 1) := by
      rw [List.length_append, doubleBits_length]; simp
    simp only [depairCnfDst]; omega
  rw [pairBits_eq_doubleBits] at hbitsτ0
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := depair_exact_correct cursorReg dstReg countReg doneReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone x w (depairRelocBase L) (depairCnfDst L) 0 τ0
    hca hda hka hna hgap hτ0c hτ0d hτ0k hτ0n hbitsτ0
  have hLeval : (Expr.reg 0).eval τ0 = L := by simpa [Expr.eval] using hτ00
  rw [eval_forN, hLeval]
  have hstepEq : loopEval (depairStep cursorReg dstReg countReg doneReg) L τ0 =
      loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) τ0 :=
    loopEval_depairStep_eq_of_ge cursorReg dstReg countReg doneReg τ0 (x.length + 1) L
      (by omega) (by rw [g4]; decide)
  rw [hstepEq]
  have h0keep : loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) τ0 0
      = τ0 0 := by
    apply g7 0 (Ne.symm hc0) (Ne.symm hd0) (Ne.symm hk0) (Ne.symm hn0)
    intro i _
    simp only [depairCnfDst]; omega
  refine ⟨?_, ?_, g4, g5, ?_, ?_⟩
  · rw [h0keep, hτ00]
  · rw [g1]; simp [depairWitnessBase]
  · rw [show depairWitnessBase L x.length = depairRelocBase L + 2 * x.length + 1 by
      simp [depairWitnessBase]]
    exact g6
  · intro r h1 h2 h3 h4 h5
    rw [g7 r h1 h2 h3 h4 h5]
    exact hτ0frame r h1 h2 h3 h4

/-- The trailing commit pair (`wBaseReg := cursorReg`, `cursorReg := depairCnfDst L`), evaluated
    against a store `σ1` known only to have `σ1 0 = L`: writes exactly `wBaseReg` and `cursorReg`
    (reading register `0` to compute the destination), leaving every other cell fixed. -/
lemma depairProg_postproc_eval (cursorReg wBaseReg : ℕ) (σ1 : Store)
    (L : ℕ) (h01 : σ1 0 = L) (hwc : wBaseReg ≠ cursorReg) (hw0 : wBaseReg ≠ 0) :
    (Program.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)).eval
        σ1 wBaseReg = σ1 cursorReg ∧
    (Program.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)).eval
        σ1 cursorReg = depairCnfDst L ∧
    ∀ r, r ≠ wBaseReg → r ≠ cursorReg →
      (Program.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)).eval
        σ1 r = σ1 r := by
  simp only [eval_seq, eval_assign, Expr.eval]
  have h0mid : (writeReg σ1 wBaseReg (σ1 cursorReg)) 0 = L := by
    rw [writeReg_diff σ1 wBaseReg (σ1 cursorReg) 0 (Ne.symm hw0), h01]
  refine ⟨?_, ?_, ?_⟩
  · rw [writeReg_diff _ cursorReg _ wBaseReg hwc, writeReg_same]
  · rw [depairDstInitExpr_eval _ L h0mid]; exact writeReg_same _ _ _
  · intro r h1 h2
    rw [writeReg_diff _ cursorReg _ r h2, writeReg_diff _ wBaseReg _ r h1]

/-- `depairProg`'s full-run correctness: `wBaseReg` lands on the witness base, `cursorReg` on the
    CNF destination, the CNF bits `x` are copied to `depairCnfDst L`, and every cell at a
    witness-offset `depairWitnessBase L x.length + v` for `v < L` is left exactly as `σ` had it —
    covering both the in-range certificate cells and the zero-padding gap
    (`depairProg_witness_correct` below splits this into the two cases). -/
lemma depairProg_correct (cursorReg dstReg countReg doneReg wBaseReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hc0 : cursorReg ≠ 0) (hd0 : dstReg ≠ 0) (hk0 : countReg ≠ 0) (hn0 : doneReg ≠ 0)
    (hw0 : wBaseReg ≠ 0) (hwc : wBaseReg ≠ cursorReg)
    (x w : List Bool) (L : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hwa : wBaseReg < depairRelocBase L)
    (hbits : BitsFrom σ (depairRelocBase L) (pairBits x w)) :
    (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ wBaseReg =
      depairWitnessBase L x.length ∧
    (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ cursorReg = depairCnfDst L ∧
    BitsFrom ((depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ) (depairCnfDst L) x ∧
    (∀ v, v < L →
      (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ
        (depairWitnessBase L x.length + v) = σ (depairWitnessBase L x.length + v)) := by
  rw [depairProg_eval_eq]
  obtain ⟨h00, e1, _, hbitsCnf, _, hframe⟩ := depairProg_loop_correct cursorReg dstReg countReg
    doneReg hcd0 hck0 hdk0 hcDone hdDone hkDone hc0 hd0 hk0 hn0 x w L σ h0 hL hca hda hka hna hbits
  obtain ⟨ew, ec, epframe⟩ := depairProg_postproc_eval cursorReg wBaseReg _ L h00 hwc hw0
  rw [e1] at ew
  have hge := depairWitnessBase_ge L x.length
  have hgeD := depairRelocBase_le_depairCnfDst L
  refine ⟨ew, ec, ?_, ?_⟩
  · intro i hi
    have hr : depairCnfDst L + i ≠ cursorReg := by omega
    rw [epframe (depairCnfDst L + i) (by omega) hr]
    exact hbitsCnf i hi
  · intro v hv
    have hr1 : depairWitnessBase L x.length + v ≠ cursorReg := by omega
    have hr2 : depairWitnessBase L x.length + v ≠ dstReg := by omega
    have hr3 : depairWitnessBase L x.length + v ≠ countReg := by omega
    have hr4 : depairWitnessBase L x.length + v ≠ doneReg := by omega
    have hr5 : ∀ i, i < x.length → depairWitnessBase L x.length + v ≠ depairCnfDst L + i :=
      fun i hi => depairWitnessBase_add_lt_disjoint L x.length w.length v i hL hv
    have hrw : depairWitnessBase L x.length + v ≠ wBaseReg := by omega
    rw [epframe (depairWitnessBase L x.length + v) hrw hr1]
    exact hframe (depairWitnessBase L x.length + v) hr1 hr2 hr3 hr4 hr5

/-- Given the zero-padding premise on the gap between the relocated pairing
    region and the CNF destination, witness offsets inside the witness are
    preserved, while offsets from the witness length up to the input length
    are returned as zero. Connecting this premise to a concrete store remains
    the caller's responsibility. -/
lemma depairProg_witness_correct (cursorReg dstReg countReg doneReg wBaseReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hc0 : cursorReg ≠ 0) (hd0 : dstReg ≠ 0) (hk0 : countReg ≠ 0) (hn0 : doneReg ≠ 0)
    (hw0 : wBaseReg ≠ 0) (hwc : wBaseReg ≠ cursorReg)
    (x w : List Bool) (L : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hwa : wBaseReg < depairRelocBase L)
    (hbits : BitsFrom σ (depairRelocBase L) (pairBits x w))
    (hzero : ∀ r, depairRelocBase L + L ≤ r → r < depairCnfDst L → σ r = 0) :
    (∀ v, v < w.length →
      (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ
        (depairWitnessBase L x.length + v) = σ (depairWitnessBase L x.length + v)) ∧
    (∀ v, w.length ≤ v → v < x.length →
      (depairProg cursorReg dstReg countReg doneReg wBaseReg).eval σ
        (depairWitnessBase L x.length + v) = 0) := by
  obtain ⟨_, _, _, hpreserve⟩ := depairProg_correct cursorReg dstReg countReg doneReg wBaseReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone hc0 hd0 hk0 hn0 hw0 hwc x w L σ h0 hL hca hda hka hna hwa
    hbits
  refine ⟨fun v hv => hpreserve v (by omega), fun v hv1 hv2 => ?_⟩
  obtain ⟨hlo, hhi⟩ := depairWitnessBase_add_mem_gap L x.length w.length v hL hv1 hv2
  rw [hpreserve v (by omega)]
  exact hzero _ hlo hhi

/-! ## `ProgramBoundedIn depairProg`: register/cell bound for a `.forN (.reg 0)` uniform loop -/

/-- `ProgramBoundedIn` for `depairStep` across the full `L`-iteration `forN` loop: splits on
    whether the iteration `m'` lands inside the real `x.length + 1`-step scan (`depair_loop_prefix`
    gives the store's register values at that prefix) or past it, where
    `loopEval_depairStep_eq_of_ge` freezes the store at its terminal value. Both cases reduce to
    `depairStep_programBoundedIn` (`DepairBounded.lean`). -/
lemma depairProg_loop_programBoundedIn (B cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hci : cursorReg ≤ B) (hdi : dstReg ≤ B) (hki : countReg ≤ B) (hni : doneReg ≤ B) (hB1 : 1 ≤ B)
    (x w : List Bool) (L : ℕ) (τ0 : Store)
    (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hc : τ0 cursorReg = depairRelocBase L) (hd : τ0 dstReg = depairCnfDst L)
    (hk : τ0 countReg = 0) (hn : τ0 doneReg = 0)
    (hbits : BitsFrom τ0 (depairRelocBase L) (pairBits x w))
    (hB : depairCnfDst L + L + 1 ≤ B) :
    ∀ m' < L, ProgramBoundedIn B (loopEval (depairStep cursorReg dstReg countReg doneReg) m' τ0)
      (depairStep cursorReg dstReg countReg doneReg) := by
  have hgap : depairRelocBase L + (doubleBits x ++ (false :: w)).length ≤ depairCnfDst L := by
    have hlen : (doubleBits x ++ (false :: w)).length = 2 * x.length + (w.length + 1) := by
      rw [List.length_append, doubleBits_length]; simp
    simp only [depairCnfDst]; omega
  have hDeq := depairCnfDst_eq L
  rw [pairBits_eq_doubleBits] at hbits
  intro m' hm'
  by_cases hmle : m' ≤ x.length
  · obtain ⟨g1, g2, g3, g4⟩ := depair_loop_prefix cursorReg dstReg countReg doneReg
      hcd0 hck0 hdk0 hcDone hdDone hkDone x (depairRelocBase L) (depairCnfDst L) 0 (false :: w) τ0
      hca hda hka hna hgap hc hd hk hn hbits m' hmle
    apply depairStep_programBoundedIn B cursorReg dstReg countReg doneReg _
      hcd0 hck0 hdk0 hcDone hci hdi hki hni hB1
    · rw [g2]; omega
    · rw [g2]; omega
    · rw [g2]; omega
    · rw [g1]; omega
    · rw [g2]; omega
    · rw [g3]; omega
  · obtain ⟨g1, g2, g3, g4, _, _, _⟩ := depair_exact_correct cursorReg dstReg countReg doneReg
      hcd0 hck0 hdk0 hcDone hdDone hkDone x w (depairRelocBase L) (depairCnfDst L) 0 τ0
      hca hda hka hna hgap hc hd hk hn hbits
    have hfreeze := loopEval_depairStep_eq_of_ge cursorReg dstReg countReg doneReg τ0
      (x.length + 1) m' (by omega) (by rw [g4]; decide)
    rw [hfreeze]
    apply depairStep_programBoundedIn B cursorReg dstReg countReg doneReg _
      hcd0 hck0 hdk0 hcDone hci hdi hki hni hB1
    · rw [g2]; omega
    · rw [g2]; omega
    · rw [g2]; omega
    · rw [g1]; omega
    · rw [g2]; omega
    · rw [g3]; omega

/-- `depairProg`'s loop-stage store keeps `register 0` (`= L`) unchanged: `depair_exact_correct`'s
    frame condition at `r = 0` (distinct from all four control registers and from the CNF
    destination cells, since `depairRelocBase L = 2 * L + 100 > 0`), transported from the exact
    `x.length + 1`-step store to the full `L`-step `forN` store via `loopEval_depairStep_eq_of_ge`.
    Needed so the postprocessing step can still read `L` off `register 0` after the loop runs. -/
lemma depairProg_loop_zero_unchanged (cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hc0 : cursorReg ≠ 0) (hd0 : dstReg ≠ 0) (hk0 : countReg ≠ 0) (hn0 : doneReg ≠ 0)
    (x w : List Bool) (L : ℕ) (τ0 : Store)
    (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hc : τ0 cursorReg = depairRelocBase L) (hd : τ0 dstReg = depairCnfDst L)
    (hk : τ0 countReg = 0) (hn : τ0 doneReg = 0)
    (hbits : BitsFrom τ0 (depairRelocBase L) (pairBits x w)) :
    loopEval (depairStep cursorReg dstReg countReg doneReg) L τ0 0 = τ0 0 := by
  have hgap : depairRelocBase L + (doubleBits x ++ (false :: w)).length ≤ depairCnfDst L := by
    have hlen : (doubleBits x ++ (false :: w)).length = 2 * x.length + (w.length + 1) := by
      rw [List.length_append, doubleBits_length]; simp
    simp only [depairCnfDst]; omega
  rw [pairBits_eq_doubleBits] at hbits
  obtain ⟨g1, g2, g3, g4, _, _, g7⟩ := depair_exact_correct cursorReg dstReg countReg doneReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone x w (depairRelocBase L) (depairCnfDst L) 0 τ0
    hca hda hka hna hgap hc hd hk hn hbits
  have hfreeze := loopEval_depairStep_eq_of_ge cursorReg dstReg countReg doneReg τ0
    (x.length + 1) L (by omega) (by rw [g4]; decide)
  rw [hfreeze]
  exact g7 0 (Ne.symm hc0) (Ne.symm hd0) (Ne.symm hk0) (Ne.symm hn0)
    (fun i _ => by simp only [depairCnfDst]; omega)

lemma depairProg_postproc_programBoundedIn (cursorReg wBaseReg B L : ℕ) (σ1 : Store)
    (h01 : σ1 0 = L) (hw0 : wBaseReg ≠ 0)
    (hwi : wBaseReg ≤ B) (hci : cursorReg ≤ B) (hB : depairCnfDst L ≤ B) :
    ProgramBoundedIn B σ1
      (Program.seq (.assign wBaseReg (.reg cursorReg)) (.assign cursorReg depairDstInitExpr)) := by
  have hp1 : ProgramBoundedIn B σ1 (.assign wBaseReg (.reg cursorReg)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]; exact ⟨hwi, hci⟩
  set σ1' := (Program.assign wBaseReg (Expr.reg cursorReg)).eval σ1 with hσ1'
  have h0' : σ1' 0 = L := by
    rw [hσ1']
    simp only [eval_assign]
    rw [writeReg_diff σ1 wBaseReg _ 0 (Ne.symm hw0), h01]
  have hp2 : ProgramBoundedIn B σ1' (.assign cursorReg depairDstInitExpr) :=
    ⟨hci, depairDstInitExpr_bounded_in σ1' L B h0' hB⟩
  exact ⟨hp1, hp2⟩

/-- `depairProg` keeps its touched cells `≤ B` when the four control registers are pairwise
    distinct, nonzero, and `≤ B`; `wBaseReg` is nonzero and `≤ B`; `1 ≤ B`; `L` has its
    stated relation to `x` and `w`; the pairing bits are preloaded; and
    `depairCnfDst L + L + 1 ≤ B` provides headroom for the destination and loop. -/
lemma depairProg_programBoundedIn (cursorReg dstReg countReg doneReg wBaseReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (hc0 : cursorReg ≠ 0) (hd0 : dstReg ≠ 0) (hk0 : countReg ≠ 0) (hn0 : doneReg ≠ 0)
    (hw0 : wBaseReg ≠ 0)
    (hci : cursorReg ≤ B) (hdi : dstReg ≤ B) (hki : countReg ≤ B) (hni : doneReg ≤ B)
    (hwi : wBaseReg ≤ B) (hB1 : 1 ≤ B)
    (x w : List Bool) (L : ℕ) (σ : Store)
    (h0 : σ 0 = L) (hL : L = 2 * x.length + 1 + w.length)
    (hca : cursorReg < depairRelocBase L) (hda : dstReg < depairRelocBase L)
    (hka : countReg < depairRelocBase L) (hna : doneReg < depairRelocBase L)
    (hbits : BitsFrom σ (depairRelocBase L) (pairBits x w))
    (hB : depairCnfDst L + L + 1 ≤ B) :
    ProgramBoundedIn B σ (depairProg cursorReg dstReg countReg doneReg wBaseReg) := by
  have hsetup := depairSetup_programBoundedIn cursorReg dstReg countReg doneReg σ L B h0 hc0
    hci hdi hki hni hB1 (by omega)
  set τ0 := (depairSetup cursorReg dstReg countReg doneReg).eval σ with hτ0
  have hτ0eq := depairSetup_eval cursorReg dstReg countReg doneReg σ L h0 hc0
  rw [← hτ0] at hτ0eq
  have hτ00 : τ0 0 = L := by
    rw [hτ0eq]
    rw [writeReg_diff _ doneReg _ 0 (Ne.symm hn0), writeReg_diff _ countReg _ 0 (Ne.symm hk0),
      writeReg_diff _ dstReg _ 0 (Ne.symm hd0), writeReg_diff _ cursorReg _ 0 (Ne.symm hc0), h0]
  have hτ0bits : BitsFrom τ0 (depairRelocBase L) (pairBits x w) := by
    rw [hτ0eq]
    exact bitsFrom_writeReg (bitsFrom_writeReg (bitsFrom_writeReg
      (bitsFrom_writeReg hbits cursorReg (depairRelocBase L) hca) dstReg (depairCnfDst L) hda)
      countReg 0 hka) doneReg 0 hna
  have hτ0c : τ0 cursorReg = depairRelocBase L := by
    rw [hτ0eq, writeReg_diff _ doneReg _ cursorReg hcDone,
      writeReg_diff _ countReg _ cursorReg hck0,
      writeReg_diff _ dstReg _ cursorReg hcd0, writeReg_same]
  have hτ0d : τ0 dstReg = depairCnfDst L := by
    rw [hτ0eq, writeReg_diff _ doneReg _ dstReg hdDone,
      writeReg_diff _ countReg _ dstReg hdk0, writeReg_same]
  have hτ0k : τ0 countReg = 0 := by
    rw [hτ0eq, writeReg_diff _ doneReg _ countReg hkDone, writeReg_same]
  have hτ0n : τ0 doneReg = 0 := by
    rw [hτ0eq, writeReg_same]
  have hloop := depairProg_loop_programBoundedIn B cursorReg dstReg countReg doneReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone hci hdi hki hni hB1 x w L τ0 hL hca hda hka hna
    hτ0c hτ0d hτ0k hτ0n hτ0bits hB
  have hLeval : (Expr.reg 0).eval τ0 = L := by simpa [Expr.eval] using hτ00
  have hforNBounded : ProgramBoundedIn B τ0
      (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg)) := by
    simp only [ProgramBoundedIn, ExprBoundedIn]
    exact ⟨by omega, hLeval ▸ hloop⟩
  have hσ10 : (Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg)).eval τ0
      0 = L := by
    rw [eval_forN, hLeval]
    rw [depairProg_loop_zero_unchanged cursorReg dstReg countReg doneReg
      hcd0 hck0 hdk0 hcDone hdDone hkDone hc0 hd0 hk0 hn0 x w L τ0 hL hca hda hka hna
      hτ0c hτ0d hτ0k hτ0n hτ0bits, hτ00]
  have hpostproc := depairProg_postproc_programBoundedIn cursorReg wBaseReg B L
    ((Program.forN (Expr.reg 0) (depairStep cursorReg dstReg countReg doneReg)).eval τ0)
    hσ10 hw0 hwi hci (by omega)
  unfold depairProg
  simp only [ProgramBoundedIn]
  rw [← hτ0]
  exact ⟨hsetup, hforNBounded, hpostproc⟩

/-! ## `ScanFree depairProg`: no `scanList`/`lookup` node anywhere -/

lemma scanFree_depairStep (cursorReg dstReg countReg doneReg : ℕ) :
    ScanFree (depairStep cursorReg dstReg countReg doneReg) := by
  simp [ScanFree, depairStep]

lemma scanFree_depairSetup (cursorReg dstReg countReg doneReg : ℕ) :
    ScanFree (depairSetup cursorReg dstReg countReg doneReg) := by
  simp [ScanFree, depairSetup]

lemma scanFree_depairProg (cursorReg dstReg countReg doneReg wBaseReg : ℕ) :
    ScanFree (depairProg cursorReg dstReg countReg doneReg wBaseReg) := by
  simp [ScanFree, depairProg, scanFree_depairSetup, scanFree_depairStep]

end NPComplete.CookLevin

module

public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatRuntimeCore
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.CookLevin.Classes

/-!
The machine half of `sat_inNP` reads its input off `bitInputStore (pairBits
(encodeCNF φ) w)`: instance bits doubled (`true, b`), a `false` separator, then
the raw certificate.  Nothing in `NatParser/`/`UniformDecode.lean` reads this
shape — their decoders assume a plain (relocated) bit run, not a doubled one.
This module isolates the one new RAM primitive the bridge needs: a scan that
un-doubles the prefix into a fresh region and stops at the separator, so the
existing CNF decoder can run against its output unchanged.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits)

/-- One iteration of the de-pair scan against a `bitInputStore`-shaped input: while
    `doneReg = 0`, read the tag bit at `cursorReg`.  A `1` (true) tag means the
    doubled instance prefix continues: copy the following data bit (at
    `cursorReg + 1`) to `dstReg`, advance `cursorReg` by 2 and `dstReg`/`countReg`
    by 1.  A `0` tag is the separator: mark `doneReg` and advance `cursorReg` past
    it, landing on the raw certificate. -/
def depairStep (cursorReg dstReg countReg doneReg : ℕ) : Program :=
  .ifNZ (.reg doneReg) .skip
    (.ifNZ (.regInd (.reg cursorReg))
      (.seq (.assignInd (.reg dstReg) (.regInd (.add (.reg cursorReg) (.const 1))))
        (.seq (.assign cursorReg (.add (.reg cursorReg) (.const 2)))
          (.seq (.assign dstReg (.add (.reg dstReg) (.const 1)))
            (.assign countReg (.add (.reg countReg) (.const 1))))))
      (.seq (.assign doneReg (.const 1))
        (.assign cursorReg (.add (.reg cursorReg) (.const 1)))))

/-- The data-bit branch of `depairStep`, as a chain of `writeReg` updates: given
    `cursorReg`/`dstReg`/`countReg` pairwise distinct and each distinct from the
    write address `σ dstReg`, the branch performs one indirect write and three
    scalar increments. -/
lemma depairStep_data_bit' (cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hCurDst : cursorReg ≠ σ dstReg) (hDstDst : dstReg ≠ σ dstReg)
    (hCountDst : countReg ≠ σ dstReg)
    (hd : σ doneReg = 0) (hb : σ (σ cursorReg) ≠ 0) :
    (depairStep cursorReg dstReg countReg doneReg).eval σ =
      writeReg (writeReg (writeReg (writeReg σ (σ dstReg) (σ (σ cursorReg + 1)))
        cursorReg (σ cursorReg + 2)) dstReg (σ dstReg + 1)) countReg (σ countReg + 1) := by
  unfold depairStep
  simp only [eval_ifNZ, eval_seq, eval_assign, eval_assignInd, Expr.eval]
  rw [ite_eq_right (by simpa using hd), ite_eq_left hb]
  set σ1 := writeReg σ (σ dstReg) (σ (σ cursorReg + 1)) with hσ1
  have h1cur : σ1 cursorReg = σ cursorReg := writeReg_diff σ (σ dstReg) _ cursorReg hCurDst
  have h1dst : σ1 dstReg = σ dstReg := writeReg_diff σ (σ dstReg) _ dstReg hDstDst
  have h1cnt : σ1 countReg = σ countReg := writeReg_diff σ (σ dstReg) _ countReg hCountDst
  rw [h1cur]
  set σ2 := writeReg σ1 cursorReg (σ cursorReg + 2) with hσ2
  have h2dst : σ2 dstReg = σ1 dstReg := writeReg_diff σ1 cursorReg _ dstReg (Ne.symm hcd0)
  have h2cnt : σ2 countReg = σ1 countReg := writeReg_diff σ1 cursorReg _ countReg (Ne.symm hck0)
  rw [h2dst, h1dst]
  set σ3 := writeReg σ2 dstReg (σ dstReg + 1) with hσ3
  have h3cnt : σ3 countReg = σ2 countReg := writeReg_diff σ2 dstReg _ countReg (Ne.symm hdk0)
  rw [h3cnt, h2cnt, h1cnt]

/-- Value-level corollary of `depairStep_data_bit'`: the new cursor/dst/count
    values, the new `doneReg` (unchanged at `0`), the newly written data cell,
    and the frame condition on every other cell. -/
lemma depairStep_data_bit_at (cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hCurDst : cursorReg ≠ σ dstReg) (hDstDst : dstReg ≠ σ dstReg)
    (hCountDst : countReg ≠ σ dstReg) (hDoneDst : doneReg ≠ σ dstReg)
    (hDoneCur : doneReg ≠ cursorReg) (hDoneDst2 : doneReg ≠ dstReg) (hDoneCount : doneReg ≠ countReg)
    (hd : σ doneReg = 0) (hb : σ (σ cursorReg) ≠ 0) :
    (depairStep cursorReg dstReg countReg doneReg).eval σ cursorReg = σ cursorReg + 2 ∧
    (depairStep cursorReg dstReg countReg doneReg).eval σ dstReg = σ dstReg + 1 ∧
    (depairStep cursorReg dstReg countReg doneReg).eval σ countReg = σ countReg + 1 ∧
    (depairStep cursorReg dstReg countReg doneReg).eval σ doneReg = 0 ∧
    (depairStep cursorReg dstReg countReg doneReg).eval σ (σ dstReg) = σ (σ cursorReg + 1) ∧
    (∀ r, r ≠ cursorReg → r ≠ dstReg → r ≠ countReg → r ≠ doneReg → r ≠ σ dstReg →
      (depairStep cursorReg dstReg countReg doneReg).eval σ r = σ r) := by
  rw [depairStep_data_bit' cursorReg dstReg countReg doneReg σ hcd0 hck0 hdk0
    hCurDst hDstDst hCountDst hd hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeReg_diff _ countReg _ cursorReg hck0,
      writeReg_diff _ dstReg _ cursorReg hcd0, writeReg_same]
  · rw [writeReg_diff _ countReg _ dstReg hdk0, writeReg_same]
  · rw [writeReg_same]
  · rw [writeReg_diff _ countReg _ doneReg hDoneCount,
      writeReg_diff _ dstReg _ doneReg hDoneDst2,
      writeReg_diff _ cursorReg _ doneReg hDoneCur,
      writeReg_diff _ (σ dstReg) _ doneReg hDoneDst, hd]
  · rw [writeReg_diff _ countReg _ (σ dstReg) (Ne.symm hCountDst),
      writeReg_diff _ dstReg _ (σ dstReg) (Ne.symm hDstDst),
      writeReg_diff _ cursorReg _ (σ dstReg) (Ne.symm hCurDst), writeReg_same]
  · intro r h1 h2 h3 h4 h5
    rw [writeReg_diff _ countReg _ r h3,
      writeReg_diff _ dstReg _ r h2,
      writeReg_diff _ cursorReg _ r h1,
      writeReg_diff _ (σ dstReg) _ r h5]

/-- The separator branch of `depairStep`: the tag bit is `0`, so only `doneReg`
    and `cursorReg` move. -/
lemma depairStep_separator (cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hd : σ doneReg = 0) (hb : σ (σ cursorReg) = 0) :
    (depairStep cursorReg dstReg countReg doneReg).eval σ =
      writeReg (writeReg σ doneReg 1) cursorReg (σ cursorReg + 1) := by
  unfold depairStep
  simp only [eval_ifNZ, eval_seq, eval_assign, eval_assignInd, Expr.eval]
  rw [ite_eq_right (by simpa using hd), ite_eq_right (by simpa using hb)]
  congr 1
  simp [writeReg_diff σ doneReg 1 cursorReg hcd]

/-- Once `doneReg ≠ 0` the step is a no-op. -/
lemma depairStep_done (cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (hd : σ doneReg ≠ 0) :
    (depairStep cursorReg dstReg countReg doneReg).eval σ = σ := by
  unfold depairStep
  simp only [eval_ifNZ, Expr.eval, ite_eq_left hd, eval_skip]

lemma loopEval_depairStep_done (cursorReg dstReg countReg doneReg : ℕ) (σ : Store) (k : ℕ)
    (hd : σ doneReg ≠ 0) :
    loopEval (depairStep cursorReg dstReg countReg doneReg) k σ = σ := by
  induction k with
  | zero => simp
  | succ k ih => rw [loopEval_succ, depairStep_done cursorReg dstReg countReg doneReg σ hd, ih]

/-- The doubled instance prefix `pairBits` writes ahead of its separator:
    each source bit `b` becomes `[true, b]`. -/
def doubleBits (x : List Bool) : List Bool := x.flatMap fun b => [true, b]

lemma doubleBits_length (x : List Bool) : (doubleBits x).length = 2 * x.length := by
  simp [doubleBits, List.length_flatMap]; ring

lemma doubleBits_cons (b : Bool) (bs : List Bool) :
    doubleBits (b :: bs) = true :: b :: doubleBits bs := by
  simp [doubleBits]

lemma pairBits_eq_doubleBits (x w : List Bool) : pairBits x w = doubleBits x ++ (false :: w) := by
  simp [pairBits, doubleBits]

/-- Loop correctness for the de-pairing scan: run exactly `x.length` data-bit
    iterations against a store whose bit region `BitsFrom σ addr (doubleBits x
    ++ rest)` holds, and whose destination region `[dst0, dst0 + x.length)`
    lies entirely past the source region (so no self-clobbering during the
    copy).  Ends with the cursor at the separator, `x`'s bits copied out to
    `dst0`, and every other cell — in particular `rest`, past the source
    region entirely — untouched. -/
lemma depair_loop_correct (cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg) :
    ∀ (x : List Bool) (addr dst0 c0 : ℕ) (rest : Bits) (σ : Store),
      cursorReg < addr → dstReg < addr → countReg < addr → doneReg < addr →
      addr + (doubleBits x ++ rest).length ≤ dst0 →
      σ cursorReg = addr → σ dstReg = dst0 → σ countReg = c0 → σ doneReg = 0 →
      BitsFrom σ addr (doubleBits x ++ rest) →
      (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) cursorReg =
        addr + 2 * x.length ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) dstReg =
        dst0 + x.length ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) countReg =
        c0 + x.length ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) doneReg = 0 ∧
      BitsFrom (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) dst0 x ∧
      BitsFrom (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ)
        (addr + 2 * x.length) rest ∧
      (∀ r, r ≠ cursorReg → r ≠ dstReg → r ≠ countReg → r ≠ doneReg →
        (∀ i, i < x.length → r ≠ dst0 + i) →
        (loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ) r = σ r) := by
  intro x
  induction x with
  | nil =>
      intro addr dst0 c0 rest σ _ _ _ _ hgap hc hd hk hn hbits
      simp only [doubleBits, List.flatMap_nil, List.nil_append] at hgap hbits
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, loopEval]
      exact ⟨hc, hd, hk, hn, fun i hi => by simp at hi, hbits, fun r _ _ _ _ _ => trivial⟩
  | cons b bs ih =>
      intro addr dst0 c0 rest σ hca hda hka hna hgap hc hd hk hn hbits
      rw [doubleBits_cons] at hgap hbits
      have hgapnum : addr + 2 + (doubleBits bs ++ rest).length ≤ dst0 + 1 := by
        simp only [List.cons_append, List.length_cons] at hgap
        omega
      have hgapstrict : addr + 2 + (doubleBits bs ++ rest).length ≤ dst0 := by
        simp only [List.cons_append, List.length_cons] at hgap
        omega
      have hshape : true :: b :: doubleBits bs ++ rest =
          true :: (b :: (doubleBits bs ++ rest)) := by simp
      rw [hshape] at hbits
      obtain ⟨htag, hrest0⟩ := bitsFrom_cons σ addr true (b :: (doubleBits bs ++ rest)) hbits
      obtain ⟨hbit, hrest1⟩ := bitsFrom_cons σ (addr + 1) b (doubleBits bs ++ rest) hrest0
      have htagv : σ addr = 1 := by simpa using htag
      have hcb : σ (σ cursorReg) ≠ 0 := by rw [hc, htagv]; decide
      have hbv : σ (addr + 1) = (if b then 1 else 0) := hbit
      have hCurDst : cursorReg ≠ σ dstReg := by rw [hd]; omega
      have hDstDst : dstReg ≠ σ dstReg := by rw [hd]; omega
      have hCountDst : countReg ≠ σ dstReg := by rw [hd]; omega
      have hDoneDst : doneReg ≠ σ dstReg := by rw [hd]; omega
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := depairStep_data_bit_at cursorReg dstReg countReg doneReg σ
        hcd0 hck0 hdk0 hCurDst hDstDst hCountDst hDoneDst
        (Ne.symm hcDone) (Ne.symm hdDone) (Ne.symm hkDone) hn hcb
      set σ1 := (depairStep cursorReg dstReg countReg doneReg).eval σ with hσ1def
      have h1cur : σ1 cursorReg = addr + 2 := by rw [e1, hc]
      have h1dst : σ1 dstReg = dst0 + 1 := by rw [e2, hd]
      have h1cnt : σ1 countReg = c0 + 1 := by rw [e3, hk]
      have h1done : σ1 doneReg = 0 := e4
      have h1writev : σ1 dst0 = (if b then 1 else 0) := by
        rw [← hd, e5, hc]; exact hbv
      have hbits' : BitsFrom σ1 (addr + 2) (doubleBits bs ++ rest) := by
        intro i hi
        have hne : addr + 2 + i ≠ σ dstReg := by rw [hd]; omega
        have hfr := e6 (addr + 2 + i) (by omega) (by omega) (by omega) (by omega) hne
        rw [hfr]
        exact hrest1 i hi
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := ih (addr + 2) (dst0 + 1) (c0 + 1) rest σ1
        (by omega) (by omega) (by omega) (by omega) hgapnum h1cur h1dst h1cnt h1done hbits'
      rw [show (b :: bs).length = bs.length + 1 by simp, loopEval_succ]
      rw [← hσ1def]
      refine ⟨?_, ?_, ?_, f4, ?_, ?_, ?_⟩
      · rw [f1]; ring
      · rw [f2]; ring
      · rw [f3]; ring
      · intro i hi
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · subst hi0
          have hne : ∀ j, j < bs.length → dst0 ≠ dst0 + 1 + j := fun j _ => by omega
          have hfr := f7 dst0 (by omega) (by omega) (by omega) (by omega) hne
          rw [show dst0 + 0 = dst0 by omega, hfr, h1writev]
          simp
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          have hi' : i' < bs.length := by simp at hi; omega
          have hfi := f5 i' hi'
          rw [show dst0 + 1 + i' = dst0 + (i' + 1) by omega] at hfi
          rw [hfi]
          simp
      · rw [show addr + 2 * (bs.length + 1) = addr + 2 + 2 * bs.length by ring]
        exact f6
      · intro r h1 h2 h3 h4 h5
        have h5' : ∀ i, i < bs.length → r ≠ dst0 + 1 + i := by
          intro i hi
          have := h5 (i + 1) (by simp; omega)
          rwa [show dst0 + (i + 1) = dst0 + 1 + i by omega] at this
        have hrne : r ≠ dst0 := by have := h5 0 (by simp); simpa using this
        rw [f7 r h1 h2 h3 h4 h5']
        exact e6 r h1 h2 h3 h4 (by rw [hd]; exact hrne)

/-- Running `depairStep` for exactly `x.length + 1` iterations (the data-bit
    scan followed by one separator step) reaches the post-separator store:
    `cursorReg` at the certificate's first bit, `dstReg`/`countReg` advanced
    by `x.length`, `doneReg` marked, `x` copied to `dst0`, and the certificate
    region (starting right after the separator) undisturbed. -/
lemma depair_exact_correct (cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (x w : List Bool) (addr dst0 c0 : ℕ) (σ : Store)
    (hca : cursorReg < addr) (hda : dstReg < addr) (hka : countReg < addr) (hna : doneReg < addr)
    (hgap : addr + (doubleBits x ++ (false :: w)).length ≤ dst0)
    (hc : σ cursorReg = addr) (hd : σ dstReg = dst0) (hk : σ countReg = c0) (hn : σ doneReg = 0)
    (hbits : BitsFrom σ addr (doubleBits x ++ (false :: w))) :
    (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) cursorReg =
      addr + 2 * x.length + 1 ∧
    (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) dstReg =
      dst0 + x.length ∧
    (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) countReg =
      c0 + x.length ∧
    (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) doneReg = 1 ∧
    BitsFrom (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) dst0 x ∧
    BitsFrom (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ)
      (addr + 2 * x.length + 1) w ∧
    (∀ r, r ≠ cursorReg → r ≠ dstReg → r ≠ countReg → r ≠ doneReg →
      (∀ i, i < x.length → r ≠ dst0 + i) →
      (loopEval (depairStep cursorReg dstReg countReg doneReg) (x.length + 1) σ) r = σ r) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := depair_loop_correct cursorReg dstReg countReg doneReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone x addr dst0 c0 (false :: w) σ
    hca hda hka hna hgap hc hd hk hn hbits
  obtain ⟨hsep0, hsep1⟩ := bitsFrom_cons _ _ false w g6
  set σ' := loopEval (depairStep cursorReg dstReg countReg doneReg) x.length σ with hσ'
  have hsepv : σ' (addr + 2 * x.length) = 0 := by simpa using hsep0
  have hb0 : σ' (σ' cursorReg) = 0 := by rw [g1]; exact hsepv
  rw [NPComplete.RAMToTM.loopEval_add, NPComplete.RAMToTM.loopEval_one, ← hσ']
  rw [depairStep_separator cursorReg dstReg countReg doneReg σ' hcDone g4 hb0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeReg_same, g1]
  · rw [writeReg_diff _ cursorReg _ dstReg hcd0.symm,
      writeReg_diff _ doneReg _ dstReg hdDone, g2]
  · rw [writeReg_diff _ cursorReg _ countReg hck0.symm,
      writeReg_diff _ doneReg _ countReg hkDone, g3]
  · rw [writeReg_diff _ cursorReg _ doneReg hcDone.symm, writeReg_same]
  · intro i hi
    have hneC : dst0 + i ≠ cursorReg := by omega
    have hneD : dst0 + i ≠ doneReg := by omega
    rw [writeReg_diff _ cursorReg _ (dst0 + i) hneC,
      writeReg_diff _ doneReg _ (dst0 + i) hneD]
    exact g5 i hi
  · intro i hi
    have hneC : addr + 2 * x.length + 1 + i ≠ cursorReg := by omega
    have hneD : addr + 2 * x.length + 1 + i ≠ doneReg := by omega
    rw [writeReg_diff _ cursorReg _ (addr + 2 * x.length + 1 + i) hneC,
      writeReg_diff _ doneReg _ (addr + 2 * x.length + 1 + i) hneD]
    exact hsep1 i hi
  · intro r h1 h2 h3 h4 h5
    rw [writeReg_diff _ cursorReg _ r h1, writeReg_diff _ doneReg _ r h4]
    exact g7 r h1 h2 h3 h4 h5

end NPComplete.CookLevin

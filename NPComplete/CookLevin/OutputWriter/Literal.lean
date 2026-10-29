module

public import NPComplete.CookLevin.OutputWriter.SecondPass

/-!
# Literal encoding writes

Clause serialization requires polarity followed by a unary variable code in the
shared output buffer. This module gives that encoded fragment and proves its
append, framing, and cost contracts, allowing clause writers to treat one literal
as a composable unit.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd writeReg writeReg_same writeReg_diff
    loopEval loopCost loopCost_le_of_body_le cost_seq cost_forN cost_assignInd eval_forN)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

/-! ## Encoded literal append -/

def natBit (n : ℕ) : Bool := decide (n ≠ 0)

def writerAppendLiteralProg (curJ tmpJ : ℕ) (polReg varReg : ℕ) : Program :=
  .seq (emitBitProg curJ (.reg polReg))
    (emitNatProg curJ tmpJ (.reg varReg))

def encodedLiteralBits (polarity varVal : ℕ) : Bits :=
  [natBit polarity] ++ encodeNat varVal

lemma writerAppendLiteralProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits) (polReg varReg : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = polarity) (hvar : σ varReg = varVal)
    (hpol01 : polarity = 0 ∨ polarity = 1)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + varVal + 2 < M + curJ)
    (hvarLow : varReg < start) :
    WriterState ((writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ)
      M curJ start (pref ++ encodedLiteralBits polarity varVal) := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hcur1 : 1 ≤ cur := by dsimp [cur]; omega
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  have hbit := emitBitProg_eval_eq curJ M cur (.reg polReg) σ hroot hcur
    (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1cur : σ1 (M + curJ) = cur + 1 := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_cursor curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1root : σ1 0 = M := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_ctl curJ M cur (.reg polReg) σ hcurJ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1var : σ1 varReg = varVal := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    rw [emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega) varReg
      (by omega) (by omega)]
    exact hvar
  have hσ1bits : BitsAt σ1 cur [natBit polarity] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    have hc := emitBitProg_eval_cell curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
    have hbitval : σ polReg = (if natBit polarity then 1 else 0) := by
      rw [hpol]
      rcases hpol01 with rfl | rfl <;> simp [natBit]
    have hc' : (emitBitProg curJ (.reg polReg)).eval σ cur = σ polReg := by
      simpa [Expr.eval] using hc
    rw [hbitval] at hc'
    simpa [cur, natBit] using hc'
  have hvarEval : (.reg varReg : Expr).eval σ1 = varVal := by
    simp [Expr.eval, hσ1var]
  have hsep1 : (cur + 1) + (.reg varReg : Expr).eval σ1 < M + curJ := by
    rw [hvarEval]
    dsimp [cur]
    omega
  have hnat := emitNatProg_eval_state curJ tmpJ M (cur + 1) (.reg varReg) σ1
    hcurJ (by omega) (by omega : curJ ≠ tmpJ) hσ1root hσ1cur (by omega) hsep1
  rw [hvarEval] at hnat
  unfold writerAppendLiteralProg
  rw [eval_seq]
  change WriterState ((emitNatProg curJ tmpJ (.reg varReg)).eval σ1) M curJ start
      (pref ++ encodedLiteralBits polarity varVal)
  refine ⟨hnat.2.2.2, ?_, ?_, hstart, ?_⟩
  · have hc := hnat.2.1
    convert hc using 1
    all_goals simp [cur, List.length_append, encodedLiteralBits, encodeNat_length]
    all_goals ring
  · rw [bitsAt_append]
    have hwhole : BitsAt ((emitNatProg curJ tmpJ (.reg varReg)).eval σ1) cur
        (encodedLiteralBits polarity varVal) := by
      change BitsAt ((emitNatProg curJ tmpJ (.reg varReg)).eval σ1) cur
        ([natBit polarity] ++ encodeNat varVal)
      rw [bitsAt_append]
      refine ⟨?_, hnat.1⟩
      have hkeep := hnat.2.2.1 cur (by omega : cur ≠ M + curJ)
        (by omega : cur ≠ M + tmpJ) (Or.inl (by omega))
      intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      have hf := hσ1bits 0 (by simp)
      simpa [Nat.add_zero] using hkeep.trans hf
    refine ⟨?_, hwhole⟩
    intro i hi
    have hframe := hnat.2.2.1 (start + i)
      (by omega : start + i ≠ M + curJ)
      (by omega : start + i ≠ M + tmpJ)
      (Or.inl (by dsimp [cur]; omega))
    have hσ1old : σ1 (start + i) = σ (start + i) := by
      rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
      exact emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
        (by dsimp [cur]; omega) (by dsimp [cur]; omega) (start + i)
          (by dsimp [cur]; omega) (by dsimp [cur]; omega)
    rw [hframe, hσ1old]
    exact hbits i hi
  · have hlen : (pref ++ encodedLiteralBits polarity varVal).length =
        pref.length + varVal + 2 := by
      simp [List.length_append, encodedLiteralBits, encodeNat_length]
      ring
    rw [hlen]
    omega

lemma writerAppendLiteralProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits) (polReg varReg : ℕ)
    (varVal : ℕ) (σ : Store) (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hvar : σ varReg = varVal) (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + varVal + 2 < M + curJ)
    (hvarLow : varReg < start) {r : ℕ} (hr : r < start) :
    (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hσ1root : σ1 0 = M := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_ctl curJ M cur (.reg polReg) σ hcurJ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1cur : σ1 (M + curJ) = cur + 1 := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_cursor curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1var : σ1 varReg = varVal := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    rw [emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega) varReg
      (by omega) (by omega)]
    exact hvar
  have hsep1 : (cur + 1) + (.reg varReg : Expr).eval σ1 < M + curJ := by
    simp [Expr.eval, hσ1var]
    dsimp [cur]
    omega
  have hnat := emitNatProg_eval_state curJ tmpJ M (cur + 1)
    (.reg varReg) σ1 hcurJ (by omega) (by omega : curJ ≠ tmpJ)
    hσ1root hσ1cur (by omega) hsep1
  have hnatframe := hnat.2.2.1 r (by omega) (by omega) (Or.inl (by dsimp [cur]; omega))
  have hbitframe := emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
    (by dsimp [cur]; omega) (by dsimp [cur]; omega) r (by omega) (by omega)
  unfold writerAppendLiteralProg
  rw [eval_seq]
  exact hnatframe.trans hbitframe

lemma writerAppendLiteralProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits) (polReg varReg : ℕ)
    (varVal : ℕ) (σ : Store) (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hvar : σ varReg = varVal) (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + varVal + 2 < M + curJ)
    (hvarLow : varReg < start) {r : ℕ}
    (hr : M + tmpJ < r) :
    (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  let σ1 := (emitBitProg curJ (.reg polReg)).eval σ
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hσ1root : σ1 0 = M := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_ctl curJ M cur (.reg polReg) σ hcurJ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1cur : σ1 (M + curJ) = cur + 1 := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    exact emitBitProg_cursor curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  have hσ1var : σ1 varReg = varVal := by
    rw [show σ1 = (emitBitProg curJ (.reg polReg)).eval σ from rfl]
    rw [emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
      (by dsimp [cur]; omega) (by dsimp [cur]; omega) varReg
      (by omega) (by omega)]
    exact hvar
  have hsep1 : (cur + 1) + (.reg varReg : Expr).eval σ1 < M + curJ := by
    simp [Expr.eval, hσ1var]
    dsimp [cur]
    omega
  have hnat := emitNatProg_eval_state curJ tmpJ M (cur + 1)
    (.reg varReg) σ1 hcurJ (by omega) (by omega : curJ ≠ tmpJ)
    hσ1root hσ1cur (by omega) hsep1
  have hnatframe := hnat.2.2.1 r (by omega) (by omega)
    (Or.inr (by simp [Expr.eval, hσ1var]; dsimp [cur]; omega))
  have hbitframe := emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur
    (by dsimp [cur]; omega) (by dsimp [cur]; omega) r (by omega) (by omega)
  unfold writerAppendLiteralProg
  rw [eval_seq]
  exact hnatframe.trans hbitframe

lemma writerAppendLiteralProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits) (polReg varReg : ℕ)
    (varVal : ℕ) (σ : Store) (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hvar : σ varReg = varVal) (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + varVal + 2 < M + curJ)
    (hvarLow : varReg < start) {r : ℕ}
    (hr : start + pref.length + varVal + 2 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendLiteralProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hcur0 : cur ≠ 0 := by dsimp [cur]; omega
  have hcurCtl : cur ≠ M + curJ := by dsimp [cur]; omega
  have hσ1root : (emitBitProg curJ (.reg polReg)).eval σ 0 = M :=
    emitBitProg_ctl curJ M cur (.reg polReg) σ hcurJ hroot hcur hcur0 hcurCtl
  have hσ1cur : (emitBitProg curJ (.reg polReg)).eval σ (M + curJ) = cur + 1 :=
    emitBitProg_cursor curJ M cur (.reg polReg) σ hroot hcur hcur0 hcurCtl
  have hσ1var : (emitBitProg curJ (.reg polReg)).eval σ varReg = varVal := by
    rw [emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur hcur0 hcurCtl varReg
      (by omega) (by omega)]
    exact hvar
  have hsep1 : (cur + 1) + (.reg varReg : Expr).eval
      ((emitBitProg curJ (.reg polReg)).eval σ) < M + curJ := by
    simp [Expr.eval, hσ1var]
    dsimp [cur]
    omega
  have hnat := emitNatProg_eval_state curJ tmpJ M (cur + 1) (.reg varReg)
    ((emitBitProg curJ (.reg polReg)).eval σ) hcurJ (by omega) (by omega)
    hσ1root hσ1cur (by omega) hsep1
  have hright : (cur + 1) + varVal + 1 ≤ r := by dsimp [cur]; omega
  have hnatframe := hnat.2.2.1 r hrc hrt
    (Or.inr (by simpa [Expr.eval, hσ1var] using hright))
  have hbitframe := emitBitProg_frame curJ M cur (.reg polReg) σ hroot hcur hcur0 hcurCtl r
    (by omega) (by omega)
  unfold writerAppendLiteralProg
  rw [eval_seq]
  exact hnatframe.trans hbitframe

def writerAppendThreeRegsProg
    (curJ tmpJ p1 v1 p2 v2 p3 v3 : ℕ) : Program :=
  .seq (writerAppendLiteralProg curJ tmpJ p1 v1)
    (.seq (writerAppendLiteralProg curJ tmpJ p2 v2)
      (writerAppendLiteralProg curJ tmpJ p3 v3))

lemma writerAppendThreeRegsProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
     (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ) :
    WriterState ((writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ)
      M curJ start
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2 ++
        encodedLiteralBits pol3 val3) := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ
    hcurJ htmpJ hp1 hv1 hpol1 hs hroom1 hlow1
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  have hσ1p2 : σ1 p2 = pol2 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ hcurJ htmpJ
      hv1 hs hroom1 hlow1 hlow2.1).trans hp2
  have hσ1v2 : σ1 v2 = val2 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ hcurJ htmpJ
      hv1 hs hroom1 hlow1 hlow2.2).trans hv2
  have hσ1p3 : σ1 p3 = pol3 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ hcurJ htmpJ
      hv1 hs hroom1 hlow1 hlow3.1).trans hp3
  have hσ1v3 : σ1 v3 = val3 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ hcurJ htmpJ
      hv1 hs hroom1 hlow1 hlow3.2).trans hv3
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 σ1 hcurJ htmpJ
    hσ1p2 hσ1v2 hpol2 (by simpa [σ1] using hs1) hroom2 hlow2.2
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hσ2p3 : σ2 p3 = pol3 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start
      (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
      hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.1).trans hσ1p3
  have hσ2v3 : σ2 v3 = val3 := by
    exact (writerAppendLiteralProg_frame M curJ tmpJ start
      (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
      hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.2).trans hσ1v3
  have hroom3 : start +
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2).length +
      val3 + 2 < M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs3 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 σ2 hcurJ htmpJ hσ2p3 hσ2v3 hpol3
    (by simpa [σ2, σ1] using hs2) hroom3 hlow3.2
  simpa [writerAppendThreeRegsProg, eval_seq, List.append_assoc] using hs3

lemma writerAppendThreeRegsProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ
    hcurJ htmpJ hp1 hv1 hpol1 hs hroom1 hlow1
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  have hσ1p2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.1).trans hp2
  have hσ1v2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.2).trans hv2
  have hσ1p3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.1).trans hp3
  have hσ1v3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.2).trans hv3
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 σ1 hcurJ htmpJ
    hσ1p2 hσ1v2 hpol2 (by simpa [σ1] using hs1) hroom2 hlow2.2
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hσ2p3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
    hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.1).trans hσ1p3
  have hσ2v3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
    hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.2).trans hσ1v3
  have hroom3 : start +
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2).length +
      val3 + 2 < M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs3 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 σ2 hcurJ htmpJ hσ2p3 hσ2v3 hpol3
    (by simpa [σ2, σ1] using hs2) hroom3 hlow3.2
  have hf3 := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 val3 σ2 hcurJ htmpJ hσ2v3
    (by simpa [σ2, σ1] using hs2) hroom3 hlow3.2 hr
  have hf2 := writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
    hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hr
  have hf1 := writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hr
  rw [writerAppendThreeRegsProg, eval_seq, eval_seq]
  exact hf3.trans (hf2.trans hf1)

lemma writerAppendThreeRegsProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ
    hcurJ htmpJ hp1 hv1 hpol1 hs hroom1 hlow1
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  have hσ1p2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.1).trans hp2
  have hσ1v2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.2).trans hv2
  have hσ1p3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.1).trans hp3
  have hσ1v3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.2).trans hv3
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 σ1 hcurJ htmpJ
    hσ1p2 hσ1v2 hpol2 (by simpa [σ1] using hs1) hroom2 hlow2.2
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hσ2p3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
      hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.1).trans hσ1p3
  have hσ2v3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
      hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hlow3.2).trans hσ1v3
  have hroom3 : start +
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2).length +
      val3 + 2 < M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs3 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 σ2 hcurJ htmpJ hσ2p3 hσ2v3 hpol3
      (by simpa [σ2, σ1] using hs2) hroom3 hlow3.2
  have hf3 := writerAppendLiteralProg_frame_high M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 val3 σ2 hcurJ htmpJ hσ2v3
      (by simpa [σ2, σ1] using hs2) hroom3 hlow3.2 hr
  have hf2 := writerAppendLiteralProg_frame_high M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
      hσ1v2 (by simpa [σ1] using hs1) hroom2 hlow2.2 hr
  have hf1 := writerAppendLiteralProg_frame_high M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hr
  rw [writerAppendThreeRegsProg, eval_seq, eval_seq]
  exact hf3.trans (hf2.trans hf1)

lemma writerAppendThreeRegsProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
     (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ)
    {r : ℕ} (hr : start + pref.length + val1 + val2 + val3 + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + 2 < M + curJ := by omega
  have hs1 := writerAppendLiteralProg_eval M curJ tmpJ start pref p1 v1 σ
    hcurJ htmpJ hp1 hv1 hpol1 hs hroom1 hlow1
  let σ1 := (writerAppendLiteralProg curJ tmpJ p1 v1).eval σ
  have hσ1p2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.1).trans hp2
  have hσ1v2 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow2.2).trans hv2
  have hσ1p3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.1).trans hp3
  have hσ1v3 := (writerAppendLiteralProg_frame M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hlow3.2).trans hv3
  have hs1' : WriterState σ1 M curJ start
      (pref ++ encodedLiteralBits pol1 val1) := by simpa [σ1] using hs1
  have hroom2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hs2 := writerAppendLiteralProg_eval M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 σ1 hcurJ htmpJ
    hσ1p2 hσ1v2 hpol2 hs1' hroom2 hlow2.2
  let σ2 := (writerAppendLiteralProg curJ tmpJ p2 v2).eval σ1
  have hσ2p3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
    hσ1v2 hs1' hroom2 hlow2.2 hlow3.1).trans hσ1p3
  have hσ2v3 := (writerAppendLiteralProg_frame M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ
    hσ1v2 hs1' hroom2 hlow2.2 hlow3.2).trans hσ1v3
  have hs2' : WriterState σ2 M curJ start
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2) := by
    simpa [σ2, σ1, List.append_assoc] using hs2
  have hroom3 : start +
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2).length + val3 + 2 <
      M + curJ := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hr3 : start +
      (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2).length + val3 + 2 ≤ r := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length] at hr ⊢
    omega
  have hr2 : start + (pref ++ encodedLiteralBits pol1 val1).length + val2 + 2 ≤ r := by
    simp [encodedLiteralBits, List.length_append, encodeNat_length] at hr ⊢
    omega
  have hr1 : start + pref.length + val1 + 2 ≤ r := by
    omega
  have hf3 := writerAppendLiteralProg_frame_after M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2)
    p3 v3 val3 σ2 hcurJ htmpJ hσ2v3 hs2' hroom3 hlow3.2 hr3 hrc hrt
  have hf2 := writerAppendLiteralProg_frame_after M curJ tmpJ start
    (pref ++ encodedLiteralBits pol1 val1) p2 v2 val2 σ1 hcurJ htmpJ hσ1v2 hs1'
    hroom2 hlow2.2 hr2 hrc hrt
  have hf1 := writerAppendLiteralProg_frame_after M curJ tmpJ start pref p1 v1 val1 σ
    hcurJ htmpJ hv1 hs hroom1 hlow1 hr1 hrc hrt
  rw [writerAppendThreeRegsProg, eval_seq, eval_seq]
  exact hf3.trans (hf2.trans hf1)

lemma writerAppendThreeRegsProg_bitsFrom_frame
    (M curJ tmpJ start : ℕ) (pref bits : Bits) (addr : ℕ)
    (p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + val3 + 6 < M + curJ)
    (hinputHigh : M + tmpJ < addr) (hbits : BitsFrom σ addr bits) :
    BitsFrom
      ((writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 p3 v3).eval σ) addr bits := by
  intro i hi
  have hf := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    p1 v1 p2 v2 p3 v3 pol1 val1 pol2 val2 pol3 val3 σ hcurJ htmpJ
    hp1 hv1 hp2 hv2 hp3 hv3 hpol1 hpol2 hpol3 hlow1 hlow2 hlow3 hs hroom
    (r := addr + i) (by omega)
  rw [hf]
  exact hbits i hi

def encodedThreeLiteralBits (pol1 val1 pol2 val2 pol3 val3 : ℕ) : Bits :=
  encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2 ++
    encodedLiteralBits pol3 val3

def literalOfPolarity (polarity val : ℕ) : Literal :=
  if polarity = 0 then Literal.pos val else Literal.neg val

lemma encodedLiteralBits_eq_encodeLiteral_of_polarity
    (polarity val : ℕ) (hpol : polarity = 0 ∨ polarity = 1) :
    encodedLiteralBits polarity val = encodeLiteral (literalOfPolarity polarity val) := by
  rcases hpol with h | h
  · simp [encodedLiteralBits, literalOfPolarity, h, encodeLiteral, natBit]
  · simp [encodedLiteralBits, literalOfPolarity, h, encodeLiteral, natBit]

lemma encodedThreeLiteralBits_eq_encodeThreeClause
    (pol1 val1 pol2 val2 pol3 val3 : ℕ)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1) :
    encodedThreeLiteralBits pol1 val1 pol2 val2 pol3 val3 =
      encodeThreeClause
        ⟨literalOfPolarity pol1 val1, literalOfPolarity pol2 val2,
          literalOfPolarity pol3 val3⟩ := by
  simp only [encodedThreeLiteralBits, encodeThreeClause]
  rw [encodedLiteralBits_eq_encodeLiteral_of_polarity pol1 val1 hpol1,
    encodedLiteralBits_eq_encodeLiteral_of_polarity pol2 val2 hpol2,
    encodedLiteralBits_eq_encodeLiteral_of_polarity pol3 val3 hpol3]

end NPComplete.CookLevin

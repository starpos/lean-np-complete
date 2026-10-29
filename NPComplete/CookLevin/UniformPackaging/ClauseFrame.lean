module

public import NPComplete.CookLevin.UniformPackaging.OuterAccounting

/-!
# Writer clause frames

Appending a clause changes the output region and scratch slots, so frame facts
are needed to preserve unrelated store cells across each writer branch. This
module proves those frame properties for one-, two-, three-literal, and
empty-clause emitters.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma writerAppendClauseOneProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg pol val : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = pol) (hval : σ varReg = val)
    (hpol01 : pol = 0 ∨ pol = 1)
    (hlow : polReg < start ∧ varReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (val + 2) < M + curJ)
    {r : ℕ} (hr : start + pref.length + 3 * (val + 2) ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  have hroom' : start + pref.length + val + val + val + 6 < M + curJ := by omega
  have hr' : start + pref.length + val + val + val + 6 ≤ r := by omega
  simpa [writerAppendClauseOneProg] using
    (writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
      polReg varReg polReg varReg polReg varReg pol val pol val pol val σ
      hcurJ htmpJ hpol hval hpol hval hpol hval hpol01 hpol01
      hlow.2 ⟨hlow.1, hlow.2⟩ ⟨hlow.1, hlow.2⟩ hs hroom'
      hr' hrc hrt)

lemma writerAppendClauseTwoProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 pol1 val1 pol2 val2 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + 2 * val2 + 6 < M + curJ)
    {r : ℕ} (hr : start + pref.length + val1 + 2 * val2 + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2).eval σ r = σ r := by
  have hroom' : start + pref.length + val1 + val2 + val2 + 6 < M + curJ := by omega
  have hr' : start + pref.length + val1 + val2 + val2 + 6 ≤ r := by omega
  simpa [writerAppendClauseTwoProg] using
    (writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
      p1 v1 p2 v2 p2 v2 pol1 val1 pol2 val2 pol2 val2 σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hp2 hv2 hpol1 hpol2
      hlow1 hlow2 hlow2 hs hroom' hr' hrc hrt)

lemma writerAppendClauseThreeProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ)
    (pol1 val1 pol2 val2 pol3 val3 base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hp3 : σ p3 = pol3) (hv3 : σ v3 = val3)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + 2 * base + 2 * val3 + 12 < M + curJ)
    {r : ℕ} (hr : start + pref.length + val1 + val2 + 2 * base + 2 * val3 + 12 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3
      posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + val2 + base + 6 < M + curJ := by omega
  have hr1 : start + pref.length + val1 + val2 + base + 6 ≤ r := by omega
  have hfirst := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hr1 hrc hrt
  have hfirstState := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg).eval σ
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowFresh).trans hfresh
  have hσ1p3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs (by omega) hlow3.1).trans hp3
  have hσ1v3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs (by omega) hlow3.2).trans hv3
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base).length +
      base + val3 + val3 + 6 < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hr2 : start +
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base).length +
      base + val3 + val3 + 6 ≤ r := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length] at hr ⊢
    omega
  have hsecond := writerAppendThreeRegsProg_frame_after M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base)
    negPolReg freshReg p3 v3 p3 v3 1 base pol3 val3 pol3 val3 σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1p3 hσ1v3 hσ1p3 hσ1v3
    (by simp) hpol3 hlowFresh hlow3 hlow3
    (by simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirstState) hroom2 hr2 hrc hrt
  rw [writerAppendClauseThreeProg, eval_seq]
  simpa [σ1] using hsecond.trans hfirst

lemma writerAppendClauseEmptyProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (posPolReg negPolReg freshReg base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    {r : ℕ} (hr : start + pref.length + 6 * (base + 2) ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + 3 * (base + 2) < M + curJ := by omega
  have hroom1' : start + pref.length + base + base + base + 6 < M + curJ := by omega
  have hr1 : start + pref.length + 3 * (base + 2) ≤ r := by omega
  have hr1' : start + pref.length + base + base + base + 6 ≤ r := by omega
  have hfirst := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (by simp) (by simp)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs hroom1' hr1' hrc hrt
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg
    posPolReg freshReg posPolReg freshReg).eval σ
  have hfirstState := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (by simp) (by simp) (by simp)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs hroom1'
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (by simp) (by simp) (by simp)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (by simp) (by simp) (by simp)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowFresh).trans hfresh
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length + 3 * (base + 2) < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length]
    omega
  have hroom2' : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length + base + base + base + 6 <
      M + curJ := by omega
  have hr2 : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length + 3 * (base + 2) ≤ r := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length] at hr ⊢
    omega
  have hr2' : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length + base + base + base + 6 ≤ r := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length] at hr ⊢
    omega
  have hsecond := writerAppendThreeRegsProg_frame_after M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base)
    negPolReg freshReg negPolReg freshReg negPolReg freshReg 1 base 1 base 1 base σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1neg hσ1fresh hσ1neg hσ1fresh
    (by simp) (by simp) hlowFresh
    ⟨hlowNeg, hlowFresh⟩ ⟨hlowNeg, hlowFresh⟩
    (by simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirstState)
    hroom2' hr2' hrc hrt
  rw [writerAppendClauseEmptyProg, eval_seq]
  simpa [σ1] using hsecond.trans hfirst

lemma emitClauseProgram_nil_frame_after_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [] rest pref σ σ0)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ) :
    ∀ r, start + pref.length + 6 * (base + 2) ≤ r →
      r ≠ M + curJ → r ≠ M + tmpJ →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr hrc hrt
  have hframe0 : σ0 r = σ r := hprep.frame r (by
    have hs := hprep.safety.cursor_below
    omega) (by
    have hs := hprep.safety.length_below
    omega) (by
    have hs := hprep.safety.done_below
    omega)
  have hwframe :
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0 r = σ0 r :=
    writerAppendClauseEmptyProg_frame_after M curJ tmpJ start pref posPolReg negPolReg
      freshReg base σ0 hprep.cur_j_pos hprep.tmp_j_pos hprep.pos_value hprep.neg_value
      hprep.fresh_value hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below
      hprep.writer hroom hr hrc hrt
  let σ1 := (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ0
  have hσ1 : σ1 r = σ0 r := by simpa [σ1] using hwframe
  let σfresh := (emitClauseEmptyFreshProg freshReg).eval σ1
  have hfreshFrame : σfresh r = σ1 r := by
    dsimp [σfresh, emitClauseEmptyFreshProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ freshReg _ r (by
      have hs := hprep.safety.fresh_below
      omega)
  let σ2 := (emitClauseCommitProg outerReg).eval σfresh
  have hcommitFrame : σ2 r = σfresh r := by
    dsimp [σ2, emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ outerReg _ r (by
      have hs := hprep.safety.outer_below
      omega)
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 r = σ2 r := by
    rw [emitClauseDispatchProg_zero_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprep.length]
    simp [σ1, σfresh, σ2, emitClauseEmptyFreshProg, emitClauseCommitProg, Expr.eval]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hcommitFrame.trans (hfreshFrame.trans (hσ1.trans hframe0))

lemma emitClauseProgram_one_frame_after_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l : NPComplete.SAT.Literal) (rest pref : Bits)
    (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr [l] rest pref σ σ0)
    (hbound : l.var + 1 ≤ bound)
    (hroom : start + pref.length + 3 * (l.var + 2) < M + curJ) :
    ∀ r, start + pref.length + 3 * (l.var + 2) ≤ r →
      r ≠ M + curJ → r ≠ M + tmpJ →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr hrc hrt
  have hσ0r : σ0 r = σ r := hprep.frame r (by
    have hs := hprep.safety.cursor_below
    omega) (by
    have hs := hprep.safety.length_below
    omega) (by
    have hs := hprep.safety.done_below
    omega)
  have hneq : ∀ {a b : ℕ},
      (a, b) ∈ clauseEmitPairs cursorReg lengthReg polReg varReg doneReg outerReg
        freshReg posPolReg negPolReg → True → a ≠ b := by
    intro a b hp _
    exact hprep.safety.ne_of_pair hp
  have hstart2 : start ≤ addr + 2 := by simpa using hprep.start_at_input
  obtain ⟨hcur1, hpol1, hvar1, hdone1, hframe1⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound
      (addr + 2) l rest σ0
      (hneq (a := cursorReg) (b := polReg) (by simp) (by simp))
      (hneq (a := cursorReg) (b := varReg) (by simp) (by simp))
      (hneq (a := cursorReg) (b := doneReg) (by simp) (by simp))
      (hneq (a := polReg) (b := varReg) (by simp) (by simp))
      (hneq (a := polReg) (b := doneReg) (by simp) (by simp))
      (hneq (a := varReg) (b := doneReg) (by simp) (by simp))
      (lt_of_lt_of_le hprep.safety.cursor_below hstart2)
      (lt_of_lt_of_le hprep.safety.pol_below hstart2)
      (lt_of_lt_of_le hprep.safety.var_below hstart2)
      (lt_of_lt_of_le hprep.safety.done_below hstart2) hbound hprep.cursor
      (by simpa using hprep.input)
  let σ1 := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ0
  have hσ1pol : σ1 polReg = literalPolarity l := by
    cases l <;> simpa [σ1, literalPolarity] using hpol1
  have hσ1var : σ1 varReg = l.var := by simpa [σ1] using hvar1
  have hwriter1 : WriterState σ1 M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ0 σ1
      cursorReg polReg varReg doneReg hprep.writer hframe1
      hprep.safety.cursor_nonzero hprep.safety.pol_nonzero hprep.safety.var_nonzero
      hprep.safety.done_nonzero hprep.safety.cursor_below hprep.safety.pol_below
      hprep.safety.var_below hprep.safety.done_below
  have hstartR : start ≤ r := by omega
  have hσ1r : σ1 r = σ0 r := by
    simpa [σ1] using hframe1 r
      (by have := hprep.safety.cursor_below; omega)
      (by have := hprep.safety.pol_below; omega)
      (by have := hprep.safety.var_below; omega)
      (by have := hprep.safety.done_below; omega)
  have hwframe :
      (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1 r = σ1 r :=
    writerAppendClauseOneProg_frame_after M curJ tmpJ start pref polReg varReg
      (literalPolarity l) l.var σ1 hprep.cur_j_pos hprep.tmp_j_pos hσ1pol hσ1var
      (by cases l <;> simp [literalPolarity])
      ⟨hprep.safety.pol_below, hprep.safety.var_below⟩ hwriter1 hroom hr
      hrc hrt
  let σ2 := (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ1
  have hσ2r : σ2 r = σ1 r := by simpa [σ2] using hwframe
  have hcommit : (emitClauseCommitProg outerReg).eval σ2 r = σ2 r := by
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ outerReg _ r (by
      have hs := hprep.safety.outer_below
      omega)
  let σ3 := (emitClauseCommitProg outerReg).eval σ2
  have hσ3r : σ3 r = σ2 r := by simpa [σ3] using hcommit
  have hdispatch :
      (emitClauseDispatchProg curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ0 r = σ3 r := by
    rw [emitClauseDispatchProg_one_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprep.length]
    simp [σ1, σ2, σ3, emitClauseCommitProg, Expr.eval]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hσ3r.trans (hσ2r.trans (hσ1r.trans hσ0r))

lemma emitClauseProgram_two_frame_after_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hpairBelow : pol2Reg < start ∧ var2Reg < start)
    (hpairNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0)
    (hpairSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + 2 * l2.var + 6 < M + curJ) :
    ∀ r, start + pref.length + l1.var + 2 * l2.var + 6 ≤ r →
      r ≠ M + curJ → r ≠ M + tmpJ →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr hrc hrt
  have hσ0r : σ0 r = σ r := hprep.frame r (by
    have hs := hprep.safety.cursor_below
    omega) (by
    have hs := hprep.safety.length_below
    omega) (by
    have hs := hprep.safety.done_below
    omega)
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r
      (by have := hprep.safety.cursor_below; omega)
      (by have := hprep.safety.pol_below; omega)
      (by have := hprep.safety.var_below; omega)
      (by have := hprep.safety.done_below; omega)
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r
      (by have := hprep.safety.cursor_below; omega)
      (by have := hpairBelow.1; omega)
      (by have := hpairBelow.2; omega)
      (by have := hprep.safety.done_below; omega)
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      WriterState τ M curJ start pref →
      (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hstate
    exact writerAppendClauseTwoProg_frame_after M curJ tmpJ start pref polReg varReg pol2Reg var2Reg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var τ hprep.cur_j_pos hprep.tmp_j_pos
      hpol1 hvar1 hpol2 hvar2
      (by cases l1 <;> simp [literalPolarity]) (by cases l2 <;> simp [literalPolarity])
      hprep.safety.var_below hpairBelow hstate hroom hr hrc hrt
  exact emitClauseProgram_two_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 rest pref
    σ σ0 r hprep hbound1 hbound2 hpairBelow hpairNonzero hpairSafe hσ0r hframeR1 hframeR2
    hwriterFrame (by have hs := hprep.safety.outer_below; omega)

lemma emitClauseProgram_three_frame_after_of_prep
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound : ℕ)
    (base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σ σ0 : Store)
    (hprep : EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg outerReg freshReg posPolReg negPolReg bound base outer addr
      [l1, l2, l3] rest pref σ σ0)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hbound3 : l3.var + 1 ≤ bound)
    (htripleBelow : pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start)
    (htripleNonzero : pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0)
    (htripleSafe : RegisterPairwise
      [cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
        posPolReg, negPolReg, freshReg, outerReg])
    (hroom : start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 < M + curJ) :
    ∀ r, start + pref.length + l1.var + l2.var + 2 * base + 2 * l3.var + 12 ≤ r →
      r ≠ M + curJ → r ≠ M + tmpJ →
      (emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
        freshReg outerReg bound tailBound).eval σ r = σ r := by
  intro r hr hrc hrt
  have hσ0r : σ0 r = σ r := hprep.frame r (by
    have hs := hprep.safety.cursor_below
    omega) (by
    have hs := hprep.safety.length_below
    omega) (by
    have hs := hprep.safety.done_below
    omega)
  have hframeR1 : ∀ τ : Store,
      (∀ q, q ≠ cursorReg → q ≠ polReg → q ≠ varReg → q ≠ doneReg → τ q = σ0 q) →
      τ r = σ0 r := by
    intro τ hframe
    exact hframe r
      (by have := hprep.safety.cursor_below; omega)
      (by have := hprep.safety.pol_below; omega)
      (by have := hprep.safety.var_below; omega)
      (by have := hprep.safety.done_below; omega)
  have hframeR2 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol2Reg → q ≠ var2Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r
      (by have := hprep.safety.cursor_below; omega)
      (by have := htripleBelow.1; omega)
      (by have := htripleBelow.2.1; omega)
      (by have := hprep.safety.done_below; omega)
  have hframeR3 : ∀ τ υ : Store,
      (∀ q, q ≠ cursorReg → q ≠ pol3Reg → q ≠ var3Reg → q ≠ doneReg → υ q = τ q) →
      υ r = τ r := by
    intro τ υ hframe
    exact hframe r
      (by have := hprep.safety.cursor_below; omega)
      (by have := htripleBelow.2.2.1; omega)
      (by have := htripleBelow.2.2.2; omega)
      (by have := hprep.safety.done_below; omega)
  have hwriterFrame : ∀ τ : Store,
      τ polReg = literalPolarity l1 → τ varReg = l1.var →
      τ pol2Reg = literalPolarity l2 → τ var2Reg = l2.var →
      τ pol3Reg = literalPolarity l3 → τ var3Reg = l3.var →
      τ posPolReg = 0 → τ negPolReg = 1 → τ freshReg = base →
      WriterState τ M curJ start pref →
      (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
        pol3Reg var3Reg posPolReg negPolReg freshReg).eval τ r = τ r := by
    intro τ hpol1 hvar1 hpol2 hvar2 hpol3 hvar3 hpos hneg hfresh hstate
    exact writerAppendClauseThreeProg_frame_after M curJ tmpJ start pref
      polReg varReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var
      (literalPolarity l3) l3.var base τ hprep.cur_j_pos hprep.tmp_j_pos
      hpol1 hvar1 hpol2 hvar2 hpol3 hvar3
      (by cases l1 <;> simp [literalPolarity])
      (by cases l2 <;> simp [literalPolarity])
      (by cases l3 <;> simp [literalPolarity]) hpos hneg hfresh
      hprep.safety.var_below
      ⟨htripleBelow.1, htripleBelow.2.1⟩
      ⟨htripleBelow.2.2.1, htripleBelow.2.2.2⟩
      hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below
      hstate hroom hr hrc hrt
  exact emitClauseProgram_three_frame_of_prep_dispatch M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base outer addr l1 l2 l3 rest pref
    σ σ0 r hprep hbound1 hbound2 hbound3 htripleBelow htripleNonzero htripleSafe hσ0r
    hframeR1 hframeR2 hframeR3 hwriterFrame
    (by have hs := hprep.safety.fresh_below; omega)
    (by have hs := hprep.safety.outer_below; omega)

end NPComplete.CookLevin

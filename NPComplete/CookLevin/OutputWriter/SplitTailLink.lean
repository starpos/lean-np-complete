module

public import NPComplete.CookLevin.OutputWriter.Literal

/-! Keeping a one-link contract lets recursive split-tail output be assembled
link by link. `writerAppendSplitTailLinkDynamicProg` appends the
`(carry, current, pos base)` triple and, when `carryValReg ≠ freshReg`, leaves
`carryValReg` at the previous `freshReg` value and `freshReg` one past it.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd writeReg writeReg_same writeReg_diff
    loopEval loopCost loopCost_le_of_body_le cost_seq cost_forN cost_assignInd eval_forN)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

def writerAppendSplitTailLinkDynamicProg
    (curJ tmpJ carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ) : Program :=
  .seq
    (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg polReg valReg
      posPolReg freshReg)
    (.seq (.assign carryValReg (.reg freshReg))
      (.assign freshReg (.add (.reg freshReg) (.const 1))))

lemma writerAppendSplitTailLinkDynamicProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ)
    (carryPol carryVal val base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcarryPol : σ carryPolReg = carryPol)
    (hcarryVal : σ carryValReg = carryVal)
    (hpol : σ polReg = 0 ∨ σ polReg = 1)
    (hval : σ valReg = val) (hpos : σ posPolReg = 0)
    (hfresh : σ freshReg = base)
    (hcarryPol01 : carryPol = 0 ∨ carryPol = 1)
    (hlowCarryVal : carryValReg < start)
    (hlowPol : polReg < start) (hlowVal : valReg < start)
    (hlowPos : posPolReg < start) (hlowFresh : freshReg < start)
    (hcarryVal0 : carryValReg ≠ 0) (hfresh0 : freshReg ≠ 0)
    (hcarryFresh : carryValReg ≠ freshReg)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + carryVal + val + base + 6 < M + curJ) :
    WriterState
      ((writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
        posPolReg freshReg).eval σ)
      M curJ start
      (pref ++ encodedThreeLiteralBits carryPol carryVal (σ polReg) val 0 base) ∧
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
      posPolReg freshReg).eval σ carryValReg = base ∧
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
      posPolReg freshReg).eval σ freshReg = base + 1 := by
  have hpol' : σ polReg = 0 ∨ σ polReg = 1 := hpol
  have hbody := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    carryPolReg carryValReg polReg valReg posPolReg freshReg
    carryPol carryVal (σ polReg) val 0 base σ
    hcurJ htmpJ hcarryPol hcarryVal rfl hval hpos hfresh
    hcarryPol01 hpol' (Or.inl rfl)
    hlowCarryVal ⟨hlowPol, hlowVal⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
  let σw := (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg polReg valReg
    posPolReg freshReg).eval σ
  have hbody' : WriterState σw M curJ start
      (pref ++ encodedThreeLiteralBits carryPol carryVal (σ polReg) val 0 base) := by
    simpa [σw, encodedThreeLiteralBits, List.append_assoc] using hbody
  have hσwFresh : σw freshReg = base := by
    exact (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      carryPolReg carryValReg polReg valReg posPolReg freshReg
      carryPol carryVal (σ polReg) val 0 base σ hcurJ htmpJ hcarryPol hcarryVal
      rfl hval hpos hfresh hcarryPol01 hpol' (Or.inl rfl)
      hlowCarryVal ⟨hlowPol, hlowVal⟩ ⟨hlowPos, hlowFresh⟩ hs
      (by omega) hlowFresh).trans hfresh
  have hcarryFresh' : freshReg ≠ carryValReg := Ne.symm hcarryFresh
  have hqCarry : M + curJ ≠ carryValReg := by
    intro heq
    have hlt : carryValReg < M + curJ := by omega
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hqFresh : M + curJ ≠ freshReg := by
    intro heq
    have hlt : freshReg < M + curJ := by omega
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hstate : WriterState
      (writeReg (writeReg σw carryValReg (σw freshReg)) freshReg (σw freshReg + 1))
      M curJ start (pref ++ encodedThreeLiteralBits carryPol carryVal (σ polReg) val 0 base) := by
    rcases hbody' with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
    refine ⟨?_, ?_, ?_, hstart, hsafe⟩
    · rw [writeReg_diff _ freshReg _ 0 (Ne.symm hfresh0),
        writeReg_diff _ carryValReg _ 0 (Ne.symm hcarryVal0)]
      exact hroot
    · rw [writeReg_diff _ freshReg _ (M + curJ) hqFresh,
        writeReg_diff _ carryValReg _ (M + curJ) hqCarry]
      exact hcursor
    · apply bitsAt_of_frame σw
        (writeReg (writeReg σw carryValReg (σw freshReg)) freshReg (σw freshReg + 1))
        start _ hbits
      intro r hlo hhi
      rw [writeReg_diff _ freshReg _ r (by omega),
        writeReg_diff _ carryValReg _ r (by omega)]
  have hprog :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
        posPolReg freshReg).eval σ =
        writeReg (writeReg σw carryValReg (σw freshReg)) freshReg (σw freshReg + 1) := by
    simp only [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_assign, Expr.eval]
    rw [writeReg_diff _ carryValReg _ freshReg hcarryFresh']
  have hprog' :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
        posPolReg freshReg).eval σ =
        writeReg (writeReg σw carryValReg base) freshReg (base + 1) := by
    rw [hprog, hσwFresh]
  have hstate' : WriterState
      (writeReg (writeReg σw carryValReg base) freshReg (base + 1))
      M curJ start (pref ++ encodedThreeLiteralBits carryPol carryVal (σ polReg) val 0 base) := by
    simpa only [hσwFresh] using hstate
  refine ⟨?_, ?_, ?_⟩
  · rw [hprog']
    exact hstate'
  · rw [hprog]
    rw [hσwFresh, writeReg_diff _ freshReg _ carryValReg hcarryFresh]
    simp only [writeReg_same]
  · rw [hprog]
    rw [hσwFresh, writeReg_same]

lemma writerAppendSplitTailLinkDynamicProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ)
    (carryPol carryVal val base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcarryPol : σ carryPolReg = carryPol)
    (hcarryVal : σ carryValReg = carryVal)
    (hpol : σ polReg = 0 ∨ σ polReg = 1)
    (hval : σ valReg = val) (hpos : σ posPolReg = 0)
    (hfresh : σ freshReg = base)
    (hcarryPol01 : carryPol = 0 ∨ carryPol = 1)
    (hlowCarryVal : carryValReg < start)
    (hlowPol : polReg < start) (hlowVal : valReg < start)
    (hlowPos : posPolReg < start) (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + carryVal + val + base + 6 < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
      posPolReg freshReg).eval σ r = σ r := by
  have hbody := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    carryPolReg carryValReg polReg valReg posPolReg freshReg
    carryPol carryVal (σ polReg) val 0 base σ hcurJ htmpJ hcarryPol hcarryVal
    rfl hval hpos hfresh hcarryPol01 hpol (Or.inl rfl)
    hlowCarryVal ⟨hlowPol, hlowVal⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega) hr
  let σw := (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg polReg valReg
    posPolReg freshReg).eval σ
  have hlowStart : start < M + tmpJ := by
    rcases hs with ⟨_, _, _, _, hsafe⟩
    omega
  have hcarry : carryValReg ≠ r := by omega
  have hfresh' : freshReg ≠ r := by omega
  have hbody' : σw r = σ r := by simpa [σw] using hbody
  have hfinal :
      (writeReg (writeReg σw carryValReg (σw freshReg)) freshReg
        ((writeReg σw carryValReg (σw freshReg)) freshReg + 1)) r = σ r := by
    rw [writeReg_diff _ freshReg _ r hfresh'.symm,
      writeReg_diff _ carryValReg _ r hcarry.symm]
    exact hbody'
  rw [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_seq]
  simp only [eval_assign, Expr.eval]
  simpa [σw] using hfinal

lemma writerAppendSplitTailLinkDynamicProg_frame_after
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ)
    (carryPol carryVal val base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcarryPol : σ carryPolReg = carryPol)
    (hcarryVal : σ carryValReg = carryVal)
    (hpol : σ polReg = 0 ∨ σ polReg = 1)
    (hval : σ valReg = val) (hpos : σ posPolReg = 0)
    (hfresh : σ freshReg = base)
    (hcarryPol01 : carryPol = 0 ∨ carryPol = 1)
    (hlowCarryVal : carryValReg < start)
    (hlowPol : polReg < start) (hlowVal : valReg < start)
    (hlowPos : posPolReg < start) (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + carryVal + val + base + 6 < M + curJ)
    {r : ℕ} (hr : start + pref.length + carryVal + val + base + 6 ≤ r)
    (hrc : r ≠ M + curJ) (hrt : r ≠ M + tmpJ) :
    (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
      posPolReg freshReg).eval σ r = σ r := by
  have hw := writerAppendThreeRegsProg_frame_after M curJ tmpJ start pref
    carryPolReg carryValReg polReg valReg posPolReg freshReg
    carryPol carryVal (σ polReg) val 0 base σ hcurJ htmpJ hcarryPol hcarryVal
    rfl hval hpos hfresh hcarryPol01 hpol
    hlowCarryVal ⟨hlowPol, hlowVal⟩
    ⟨hlowPos, hlowFresh⟩ hs hroom hr hrc hrt
  rw [writerAppendSplitTailLinkDynamicProg, eval_seq, eval_seq]
  simp only [eval_assign, Expr.eval]
  rw [writeReg_diff _ freshReg _ r (by omega),
    writeReg_diff _ carryValReg _ r (by omega)]
  exact hw

lemma writerAppendSplitTailLinkDynamicProg_bitsFrom_frame
    (M curJ tmpJ start : ℕ) (pref bits : Bits) (addr : ℕ)
    (carryPolReg carryValReg polReg valReg posPolReg freshReg : ℕ)
    (carryPol carryVal val base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hcarryPol : σ carryPolReg = carryPol)
    (hcarryVal : σ carryValReg = carryVal)
    (hpol : σ polReg = 0 ∨ σ polReg = 1)
    (hval : σ valReg = val) (hpos : σ posPolReg = 0)
    (hfresh : σ freshReg = base)
    (hcarryPol01 : carryPol = 0 ∨ carryPol = 1)
    (hlowCarryVal : carryValReg < start)
    (hlowPol : polReg < start) (hlowVal : valReg < start)
    (hlowPos : posPolReg < start) (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + carryVal + val + base + 6 < M + curJ)
    (hinputHigh : M + tmpJ < addr)
    (hbits : BitsFrom σ addr bits) :
    BitsFrom
      ((writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg valReg
        posPolReg freshReg).eval σ) addr bits := by
  intro i hi
  have hf := writerAppendSplitTailLinkDynamicProg_frame_high M curJ tmpJ start pref
    carryPolReg carryValReg polReg valReg posPolReg freshReg
    carryPol carryVal val base σ hcurJ htmpJ hcarryPol hcarryVal hpol hval hpos hfresh
    hcarryPol01 hlowCarryVal hlowPol hlowVal hlowPos hlowFresh hs hroom
    (r := addr + i) (by omega)
  rw [hf]
  exact hbits i hi

end NPComplete.CookLevin

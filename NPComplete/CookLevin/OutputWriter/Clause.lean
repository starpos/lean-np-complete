module

public import NPComplete.CookLevin.OutputWriter.SplitTailLink

/-!
# Clause-Level Output Writers

The lower-level writer appends encoded literals, while clause-table construction needs each clause
handled as one operation. This module packages fixed-arity clause encodings with state, frame, and cost
contracts, so higher-level emission can reason at clause boundaries.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd writeReg writeReg_same writeReg_diff
    loopEval loopCost loopCost_le_of_body_le cost_seq cost_forN cost_assignInd eval_forN)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

def writerAppendClauseOneProg (curJ tmpJ polReg varReg : ℕ) : Program :=
  writerAppendThreeRegsProg curJ tmpJ polReg varReg polReg varReg polReg varReg

def writerAppendClauseTwoProg
    (curJ tmpJ pol1Reg var1Reg pol2Reg var2Reg : ℕ) : Program :=
  writerAppendThreeRegsProg curJ tmpJ pol1Reg var1Reg pol2Reg var2Reg pol2Reg var2Reg

def writerAppendClauseEmptyProg
    (curJ tmpJ posPolReg negPolReg freshReg : ℕ) : Program :=
  .seq
    (writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg posPolReg freshReg
      posPolReg freshReg)
    (writerAppendThreeRegsProg curJ tmpJ negPolReg freshReg negPolReg freshReg
      negPolReg freshReg)

/-! The length-three case is the first nontrivial split-tail case.  The first
clause uses the two decoded literals and a fresh positive literal; the second
clause carries the corresponding negative literal and duplicates the remaining
input literal. -/

def writerAppendClauseThreeProg
    (curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ) : Program :=
  .seq
    (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg)
    (writerAppendThreeRegsProg curJ tmpJ negPolReg freshReg p3 v3 p3 v3)

lemma writerAppendClauseOneProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg pol val : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = pol) (hval : σ varReg = val)
    (hpol01 : pol = 0 ∨ pol = 1)
    (hlow : polReg < start ∧ varReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (val + 2) < M + curJ) :
    WriterState ((writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ)
      M curJ start
      (pref ++ encodedThreeLiteralBits pol val pol val pol val) := by
  simpa [writerAppendClauseOneProg, encodedThreeLiteralBits,
    List.append_assoc, Nat.mul_add, Nat.add_mul] using
    (writerAppendThreeRegsProg_eval M curJ tmpJ start pref
      polReg varReg polReg varReg polReg varReg pol val pol val pol val σ
      hcurJ htmpJ hpol hval hpol hval hpol hval hpol01 hpol01 hpol01
      hlow.2 ⟨hlow.1, hlow.2⟩ ⟨hlow.1, hlow.2⟩ hs (by omega))

lemma writerAppendClauseOneProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg pol val : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = pol) (hval : σ varReg = val)
    (hpol01 : pol = 0 ∨ pol = 1)
    (hlow : polReg < start ∧ varReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (val + 2) < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  simpa [writerAppendClauseOneProg] using
    (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      polReg varReg polReg varReg polReg varReg pol val pol val pol val σ
      hcurJ htmpJ hpol hval hpol hval hpol hval hpol01 hpol01 hpol01
      hlow.2 ⟨hlow.1, hlow.2⟩ ⟨hlow.1, hlow.2⟩ hs (by omega) hr)

lemma writerAppendClauseOneProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (polReg varReg pol val : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpol : σ polReg = pol) (hval : σ varReg = val)
    (hpol01 : pol = 0 ∨ pol = 1)
    (hlow : polReg < start ∧ varReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 3 * (val + 2) < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendClauseOneProg curJ tmpJ polReg varReg).eval σ r = σ r := by
  simpa [writerAppendClauseOneProg] using
    (writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
      polReg varReg polReg varReg polReg varReg pol val pol val pol val σ
      hcurJ htmpJ hpol hval hpol hval hpol hval hpol01 hpol01 hpol01
      hlow.2 ⟨hlow.1, hlow.2⟩ ⟨hlow.1, hlow.2⟩ hs (by omega) hr)

lemma writerAppendClauseTwoProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 pol1 val1 pol2 val2 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + 2 * val2 + 6 < M + curJ) :
    WriterState ((writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2).eval σ)
      M curJ start
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 pol2 val2) := by
  simpa [writerAppendClauseTwoProg, encodedThreeLiteralBits,
    List.append_assoc, Nat.mul_add, Nat.add_mul] using
    (writerAppendThreeRegsProg_eval M curJ tmpJ start pref
      p1 v1 p2 v2 p2 v2 pol1 val1 pol2 val2 pol2 val2 σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hp2 hv2 hpol1 hpol2 hpol2
      hlow1 hlow2 hlow2 hs (by omega))

lemma writerAppendClauseTwoProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 pol1 val1 pol2 val2 : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hlow1 : v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + 2 * val2 + 6 < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendClauseTwoProg curJ tmpJ p1 v1 p2 v2).eval σ r = σ r := by
  simpa [writerAppendClauseTwoProg] using
    (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 p2 v2 pol1 val1 pol2 val2 pol2 val2 σ
      hcurJ htmpJ hp1 hv1 hp2 hv2 hp2 hv2 hpol1 hpol2 hpol2
      hlow1 hlow2 hlow2 hs (by omega) hr)

lemma writerAppendClauseEmptyProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (posPolReg negPolReg freshReg base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ) :
    WriterState ((writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ)
      M curJ start
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base ++
        encodedThreeLiteralBits 1 base 1 base 1 base) := by
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) hlowFresh ⟨hlowPos, hlowFresh⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg
    posPolReg freshReg posPolReg freshReg).eval σ
  have hfirst' : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) hlowFresh ⟨hlowPos, hlowFresh⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) hlowFresh ⟨hlowPos, hlowFresh⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowFresh).trans hfresh
  have hsecond := writerAppendThreeRegsProg_eval M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base)
    negPolReg freshReg negPolReg freshReg negPolReg freshReg 1 base 1 base 1 base σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1neg hσ1fresh hσ1neg hσ1fresh
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    hlowFresh ⟨hlowNeg, hlowFresh⟩ ⟨hlowNeg, hlowFresh⟩
    hfirst' (by
      simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
        encodeNat_length]
      omega)
  rw [writerAppendClauseEmptyProg, eval_seq]
  simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hsecond

lemma writerAppendClauseEmptyProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (posPolReg negPolReg freshReg base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + 3 * (base + 2) < M + curJ := by omega
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega)
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg
    posPolReg freshReg posPolReg freshReg).eval σ
  have hfirst' : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowFresh).trans hfresh
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length +
      3 * (base + 2) < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
      encodeNat_length]
    omega
  have hsecond := writerAppendThreeRegsProg_frame M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base)
    negPolReg freshReg negPolReg freshReg negPolReg freshReg 1 base 1 base 1 base σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1neg hσ1fresh hσ1neg hσ1fresh
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    hlowFresh ⟨hlowNeg, hlowFresh⟩ ⟨hlowNeg, hlowFresh⟩ hfirst' (by omega) hr
  have hfirstFrame := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hr
  rw [writerAppendClauseEmptyProg, eval_seq]
  simpa [σ1] using hsecond.trans hfirstFrame

lemma writerAppendClauseEmptyProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (posPolReg negPolReg freshReg base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1)
    (hfresh : σ freshReg = base)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + 6 * (base + 2) < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + 3 * (base + 2) < M + curJ := by omega
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega)
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ posPolReg freshReg
    posPolReg freshReg posPolReg freshReg).eval σ
  have hfirst' : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hlowFresh).trans hfresh
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length +
        3 * (base + 2) < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
      encodeNat_length]
    omega
  have hroom2' : start +
      (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base).length +
        base + base + base + 6 < M + curJ := by omega
  have hsecond := writerAppendThreeRegsProg_frame_high M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits 0 base 0 base 0 base)
    negPolReg freshReg negPolReg freshReg negPolReg freshReg 1 base 1 base 1 base σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1neg hσ1fresh hσ1neg hσ1fresh
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    hlowFresh ⟨hlowNeg, hlowFresh⟩ ⟨hlowNeg, hlowFresh⟩ hfirst' hroom2' hr
  have hfirstFrame := writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
    posPolReg freshReg posPolReg freshReg posPolReg freshReg 0 base 0 base 0 base σ
    hcurJ htmpJ hpos hfresh hpos hfresh hpos hfresh
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    hlowFresh ⟨hlowPos, hlowFresh⟩ ⟨hlowPos, hlowFresh⟩ hs (by omega) hr
  rw [writerAppendClauseEmptyProg, eval_seq]
  simpa [σ1] using hsecond.trans hfirstFrame

lemma writerAppendClauseThreeProg_eval
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
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + 2 * base + 2 * val3 + 12 < M + curJ) :
    WriterState ((writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3
      posPolReg negPolReg freshReg).eval σ)
      M curJ start
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base ++
        encodedThreeLiteralBits 1 base pol3 val3 pol3 val3) := by
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg
    pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh
    hpol1 hpol2 (Or.inl rfl) hlow1 ⟨hlow2.1, hlow2.2⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg).eval σ
  have hfirst' : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg
    pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh
    hpol1 hpol2 (Or.inl rfl) hlow1 ⟨hlow2.1, hlow2.2⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
    hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg
    pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh
    hpol1 hpol2 (Or.inl rfl) hlow1 ⟨hlow2.1, hlow2.2⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
    hlowFresh).trans hfresh
  have hσ1p3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg
    pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh
    hpol1 hpol2 (Or.inl rfl) hlow1 ⟨hlow2.1, hlow2.2⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
    hlow3.1).trans hp3
  have hσ1v3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg
    pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh
    hpol1 hpol2 (Or.inl rfl) hlow1 ⟨hlow2.1, hlow2.2⟩
    ⟨hlowPos, hlowFresh⟩ hs (by omega)
    hlow3.2).trans hv3
  have hsecond := writerAppendThreeRegsProg_eval M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base)
    negPolReg freshReg p3 v3 p3 v3 1 base
      pol3 val3 pol3 val3 σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1p3 hσ1v3 hσ1p3 hσ1v3
    (Or.inr rfl) hpol3 hpol3 hlowFresh
    ⟨hlow3.1, hlow3.2⟩ ⟨hlow3.1, hlow3.2⟩ hfirst' (by
      simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
        encodeNat_length]
      omega)
  rw [writerAppendClauseThreeProg, eval_seq]
  simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hsecond

lemma writerAppendClauseThreeProg_frame
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
    (hlow1 : v1 < start)
    (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + val1 + val2 + 2 * base + 2 * val3 + 12 < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3
      posPolReg negPolReg freshReg).eval σ r = σ r := by
  have hroom1 : start + pref.length + val1 + val2 + base + 6 < M + curJ := by omega
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2
    posPolReg freshReg).eval σ
  have hfirst' : WriterState σ1 M curJ start
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base) := by
    simpa [σ1, encodedThreeLiteralBits, List.append_assoc] using hfirst
  have hσ1neg := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlowNeg).trans hneg
  have hσ1fresh := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlowFresh).trans hfresh
  have hσ1p3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlow3.1).trans hp3
  have hσ1v3 := (writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hlow3.2).trans hv3
  have hroom2 : start +
      (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base).length +
      base + 2 * val3 + 6 < M + curJ := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append,
      encodeNat_length]
    omega
  have hsecond := writerAppendThreeRegsProg_frame M curJ tmpJ start
    (pref ++ encodedThreeLiteralBits pol1 val1 pol2 val2 0 base)
    negPolReg freshReg p3 v3 p3 v3 1 base pol3 val3 pol3 val3 σ1
    hcurJ htmpJ hσ1neg hσ1fresh hσ1p3 hσ1v3 hσ1p3 hσ1v3
    (Or.inr rfl) hpol3 hpol3 hlowFresh hlow3 hlow3 hfirst'
    (by omega) hr
  have hfirstFrame := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ
    hcurJ htmpJ hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (Or.inl rfl)
    hlow1 hlow2 ⟨hlowPos, hlowFresh⟩ hs hroom1 hr
  rw [writerAppendClauseThreeProg, eval_seq]
  simpa [σ1] using hsecond.trans hfirstFrame

end NPComplete.CookLevin

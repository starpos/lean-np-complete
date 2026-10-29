module

public import NPComplete.CookLevin.UniformPackaging.DecoderBounds

/-!
# Reachability of split-tail states

Raw bounds are needed at every intermediate state, although the semantic relation
only describes the current parser and writer state. This module proves
reachable-or-done facts across the clause transitions and uses them to establish
program bounds.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma programBoundedIn_splitTailEmitStepProgAt_raw_of_bounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
      carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hdist1 : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
      var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
      boundReg ≠ var2Reg ∧ boundReg ≠ doneReg)
    (hdist2 : cursorReg ≠ pol3Reg ∧ cursorReg ≠ var3Reg ∧ cursorReg ≠ doneReg ∧
      var3Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol3Reg ∧
      boundReg ≠ var3Reg ∧ boundReg ≠ doneReg)
    (hzero1 : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0)
    (hzero2 : cursorReg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol1 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
      M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg)
    (hcontrol2 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol3Reg ∧
      M + curJ ≠ var3Reg ∧ M + curJ ≠ doneReg)
    (hzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol : M + curJ ≠ cursorReg ∧ M + curJ ≠ polReg ∧
      M + curJ ≠ varReg ∧ M + curJ ≠ doneReg)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hcursor1 : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      cursorReg + 1 + (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
        boundReg ≤ K)
    (hcarryVal0 : carryValReg ≠ 0) (hfresh0 : freshReg ≠ 0)
    (hcarryValCursor : carryValReg ≠ M + curJ) (hfreshCursor : freshReg ≠ M + curJ)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg) := by
  rcases hidx with ⟨hcursorK, hpolK, hvarK, hdoneK, hremK, hpol2K, hvar2K,
    hpol3K, hvar3K, hcpK, hcvK, hposK, hfreshK, hboundK⟩
  have hKB : K ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hremB : remainingReg ≤ B := hremK.trans hKB
  have hB2 : 2 ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget
    omega
  have hone := programBoundedIn_splitTailEmitTerminalOneProgAt_raw_bounds K B M curJ tmpJ
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg carryPolReg carryValReg
    posPolReg freshReg boundReg σ hcurJ1 htmpJlt hstatic
    ⟨hcursorK, hpolK, hvarK, hdoneK, hremK, hpol2K, hvar2K, hcpK, hcvK, hposK, hfreshK,
      hboundK⟩ hdist1 hzero1 hcontrol1 hσ hM hq0 hcursor1
    (by simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢; omega)
  have htwo := programBoundedIn_splitTailEmitTerminalTwoProgAt_raw_bounds K B M curJ tmpJ
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg boundReg σ hcurJ1 htmpJlt hstatic
    ⟨hcursorK, hpolK, hvarK, hdoneK, hremK, hpol2K, hvar2K, hpol3K, hvar3K, hcpK,
      hcvK, hposK, hfreshK, hboundK⟩ hdist1 hdist2 hzero1 hzero2 hcontrol1 hcontrol2 hσ hM hq0
    hcursor1 hcursor2
    (by simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢; omega)
  have hinter := programBoundedIn_splitTailEmitIntermediateProgAt_raw_bounds K B M curJ tmpJ
    cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg posPolReg freshReg boundReg
    σ hcurJ1 htmpJlt hstatic
    ⟨hcursorK, hpolK, hvarK, hdoneK, hremK, hcpK, hcvK, hposK, hfreshK, hboundK⟩
    hdist hzero hcontrol hσ hM hq0 hcursor1
    hcarryVal0 hfresh0 hcarryValCursor hfreshCursor hbudget
  exact programBoundedIn_splitTailEmitStepProgAt_raw_of_branches B curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg boundReg σ hB2 hremB hone htwo hinter

structure SplitTailEmitStepRawBounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) : Prop where
  cur_j1 : 1 ≤ curJ
  tmp_jlt : curJ < tmpJ
  static : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K
  idx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
    remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
    carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K
  dist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
    varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
    boundReg ≠ varReg ∧ boundReg ≠ doneReg
  dist1 : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
    var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
    boundReg ≠ var2Reg ∧ boundReg ≠ doneReg
  dist2 : cursorReg ≠ pol3Reg ∧ cursorReg ≠ var3Reg ∧ cursorReg ≠ doneReg ∧
    var3Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol3Reg ∧
    boundReg ≠ var3Reg ∧ boundReg ≠ doneReg
  zero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0
  zero1 : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0
  zero2 : cursorReg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0
  control : M + curJ ≠ cursorReg ∧ M + curJ ≠ polReg ∧
    M + curJ ≠ varReg ∧ M + curJ ≠ doneReg
  control1 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
    M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg
  control2 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol3Reg ∧
    M + curJ ≠ var3Reg ∧ M + curJ ≠ doneReg
  store : StoreValuesLe K σ
  root : σ 0 = M
  cursor_nonzero : σ (M + curJ) ≠ 0
  cursor1 : σ cursorReg + 1 + σ boundReg ≤ K
  cursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ boundReg ≤ K
  carry_val0 : carryValReg ≠ 0
  fresh0 : freshReg ≠ 0
  carry_val_cursor : carryValReg ≠ M + curJ
  fresh_cursor : freshReg ≠ M + curJ
  budget : writerAppendRawThreeBound K + 1 ≤ B

structure SplitTailEmitDoneRawBounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) : Prop where
  done : SplitTailEmitDone σ M curJ start base carry ls pref tail addr cursorReg remainingReg freshReg
  bound_eq : σ boundReg = bound
  raw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg σ

/-! A terminal frame transports the source-store bound through the writer window.
    Parser cursor budgets remain explicit rather than following from a terminal state alone. -/
lemma SplitTailEmitDoneFrame.writer_cursor_le_of_raw
    (K M curJ : ℕ) (σ τ : Store)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hdone : SplitTailEmitDoneFrame τ σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg remainingReg freshReg posPolReg) :
    τ (M + curJ) ≤ K := by
  rw [hdone.done.writer.cursor]
  have hs := hdone.done.writer.safe
  have hM := hraw.static.1
  omega

/-- The raw bounds at a terminal store follow from the source store's raw bounds and the
    terminal frame, given `StoreValuesLe K` at the terminal store and the two parser cursor
    budgets. -/
lemma SplitTailEmitDoneFrame.to_raw_bounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hdone : SplitTailEmitDoneFrame τ σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg remainingReg freshReg posPolReg)
    (hbound : τ boundReg = bound)
    (hstore : StoreValuesLe K τ)
    (hcursor1 : τ cursorReg + 1 + τ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ
      cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ boundReg ≤ K) :
    SplitTailEmitDoneRawBounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound base carry ls pref tail addr τ := by
  have hroot : τ 0 = M := hdone.done.writer.root
  have hq0 : τ (M + curJ) ≠ 0 := by
    have hstart := hdone.done.writer.start_pos
    rw [hdone.done.writer.cursor]
    omega
  have hpostRaw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg τ := by
    refine
      { cur_j1 := hraw.cur_j1
        tmp_jlt := hraw.tmp_jlt
        static := hraw.static
        idx := hraw.idx
        dist := hraw.dist
        dist1 := hraw.dist1
        dist2 := hraw.dist2
        zero := hraw.zero
        zero1 := hraw.zero1
        zero2 := hraw.zero2
        control := hraw.control
        control1 := hraw.control1
        control2 := hraw.control2
        store := hstore
        root := hroot
        cursor_nonzero := hq0
        cursor1 := hcursor1
        cursor2 := hcursor2
        carry_val0 := hraw.carry_val0
        fresh0 := hraw.fresh0
        carry_val_cursor := hraw.carry_val_cursor
        fresh_cursor := hraw.fresh_cursor
        budget := hraw.budget }
  exact ⟨hdone.done, hbound, hpostRaw⟩

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.UniformPackaging.SplitTailTerminalBounds

/-!
# Certificates for split-tail emission

Semantic reachability of the parameterized emitter does not directly provide the
raw syntax bounds required by program-bound proofs. This module packages those
facts as certificates and converts reachability evidence into per-step bounds.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

structure SplitTailEmitRelRawLayout
    (M curJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) : Prop where
  root : σ 0 = M
  cursor_nonzero : σ (M + curJ) ≠ 0
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
  carry_val0 : carryValReg ≠ 0
  fresh0 : freshReg ≠ 0
  carry_val_cursor : carryValReg ≠ M + curJ
  fresh_cursor : freshReg ≠ M + curJ

structure SplitTailEmitStepSyntaxBounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) : Prop where
  cur_j1 : 1 ≤ curJ
  tmp_jlt : curJ < tmpJ
  static : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K
  idx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
    remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
    carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K
  layout : SplitTailEmitRelRawLayout M curJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg σ
  store : StoreValuesLe K σ
  cursor1 : σ cursorReg + 1 + σ boundReg ≤ B
  cursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ boundReg ≤ B
  budget : writerAppendRawThreeBound K + 1 ≤ B

lemma SplitTailEmitRel.raw_layout
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    SplitTailEmitRelRawLayout M curJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg σ := by
  have hsafe := hrel.writer.safe
  have hq : start < M + curJ := by omega
  rcases hrel.safety.main.distinct with ⟨hcp, hcv, hcd, hpv, hpd, hvd⟩
  rcases hrel.safety.second.distinct with ⟨hcp2, hcv2, hcd2, hp2v2, hp2d, hv2d⟩
  rcases hrel.safety.third.distinct with ⟨hcp3, hcv3, hcd3, hp3v3, hp3d, hv3d⟩
  rcases hok.ne_write_set with ⟨hbc, hbp, hbv, hbd, hbr, hbp2, hbv2, hbp3, hbv3,
    hbcp, hbcv, hbpos, hbfresh⟩
  have hbelow :
      cursorReg < start ∧ polReg < start ∧ varReg < start ∧ doneReg < start ∧
      pol2Reg < start ∧ var2Reg < start ∧ pol3Reg < start ∧ var3Reg < start ∧
      carryValReg < start ∧ freshReg < start := by
    exact ⟨hrel.safety.main.below.1, hrel.safety.main.below.2.1,
      hrel.safety.main.below.2.2.1, hrel.safety.main.below.2.2.2,
      hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1,
      hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1,
      hrel.safety.writer_below.2.1, hrel.safety.writer_below.2.2.2.1⟩
  refine
    { root := hrel.writer.root
      cursor_nonzero := by rw [hrel.writer.cursor]; omega
      dist := ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
      dist1 := ⟨hcp2, hcv2, hcd2, hv2d, hbc, hbp2, hbv2, hbd⟩
      dist2 := ⟨hcp3, hcv3, hcd3, hv3d, hbc, hbp3, hbv3, hbd⟩
      zero := hrel.safety.main.nonzero
      zero1 := hrel.safety.second.nonzero
      zero2 := hrel.safety.third.nonzero
      control := by omega
      control1 := by omega
      control2 := by omega
      carry_val0 := hrel.safety.writer_nonzero.1
      fresh0 := hrel.safety.writer_nonzero.2
      carry_val_cursor := by omega
      fresh_cursor := by omega }

lemma SplitTailEmitRel.to_raw_bounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
      carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hσ : StoreValuesLe K σ) (hcursor1 : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      cursorReg + 1 + (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
        boundReg ≤ K)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg σ := by
  have hl := SplitTailEmitRel.raw_layout M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg base carry ls pref tail addr σ hrel hok
  refine
    { cur_j1 := hrel.cur_j_pos
      tmp_jlt := hrel.tmp_j_pos
      static := hstatic
      idx := hidx
      dist := hl.dist
      dist1 := hl.dist1
      dist2 := hl.dist2
      zero := hl.zero
      zero1 := hl.zero1
      zero2 := hl.zero2
      control := hl.control
      control1 := hl.control1
      control2 := hl.control2
      store := hσ
      root := hl.root
      cursor_nonzero := hl.cursor_nonzero
      cursor1 := hcursor1
      cursor2 := hcursor2
      carry_val0 := hl.carry_val0
      fresh0 := hl.fresh0
      carry_val_cursor := hl.carry_val_cursor
      fresh_cursor := hl.fresh_cursor
      budget := hbudget }

end NPComplete.CookLevin

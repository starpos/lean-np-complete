module

public import NPComplete.CookLevin.ToThreeCNF.SplitTailIntermediate

/-!
# Long-clause register safety

The split-tail branch reuses temporary registers inside a loop, so overlap with
outer controls would invalidate its frame argument. This module records the
required register separation and derives the safety facts used by the branch and
outer emission proofs.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
  (BitsFrom bitsFrom_append bitsFrom_writeReg bitsFrom_of_eq_on BitsAt bitsAt_of_frame finalizeOutputProg FinalizeRegsOk ctlCell ctlCell_eval)
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same cost_seq
    cost_ifNZ cost_forN eval_ifNZ eval_forN loopEval loopEval_succ
    loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
/-! The long-clause branch uses `outerReg`, which the clause dispatcher updates,
and `negPolReg`, which is reset after the branch, in addition to the registers
written by the split-tail program.  `LongClauseRegisterSafety` records the
registers needed for the branch and its surrounding control in one duplicate-
free list, with the bounds required by the frame arguments. -/

def longClauseRegisterList
    (cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ) : List ℕ :=
  [cursorReg, lengthReg, polReg, varReg, doneReg, outerReg, negPolReg,
    remainingReg, pol2Reg, var2Reg, pol3Reg, var3Reg, carryPolReg,
    carryValReg, posPolReg, freshReg]

structure LongClauseRegisterSafety
    (start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ) : Prop where
  register_nodup :
    (longClauseRegisterList cursorReg lengthReg polReg varReg doneReg outerReg negPolReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg).Nodup
  below : ∀ r ∈ longClauseRegisterList cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg, r < start
  nonzero : ∀ r ∈ longClauseRegisterList cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg, r ≠ 0

lemma long_clause_fixed_register_safety :
    LongClauseRegisterSafety 32 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 := by
  refine { register_nodup := ?_, below := ?_, nonzero := ?_ }
  · decide
  · intro r hr
    simp [longClauseRegisterList] at hr
    omega
  · intro r hr
    simp [longClauseRegisterList] at hr
    omega

lemma LongClauseRegisterSafety.outer_not_mem_splitTailEmitStepWriteSet
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    outerReg ∉ splitTailEmitStepWriteSet cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg := by
  intro hmem
  simp [splitTailEmitStepWriteSet] at hmem
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn
  aesop

lemma LongClauseRegisterSafety.neg_pol_not_mem_splitTailEmitStepWriteSet
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    negPolReg ∉ splitTailEmitStepWriteSet cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg := by
  intro hmem
  simp [splitTailEmitStepWriteSet] at hmem
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn
  aesop

lemma LongClauseRegisterSafety.to_split_tail_safety
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn
  obtain ⟨⟨-, h0_2, h0_3, h0_4, -, -, h0_7, h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14,
    h0_15⟩, hnR1⟩ := hn
  obtain ⟨-, hnR2⟩ := hnR1
  obtain ⟨⟨h2_3, h2_4, -, -, h2_7, -, -, -, -, h2_12, h2_13, h2_14, h2_15⟩, hnR3⟩ := hnR2
  obtain ⟨⟨h3_4, -, -, h3_7, -, -, -, -, h3_12, h3_13, h3_14, h3_15⟩, hnR4⟩ := hnR3
  obtain ⟨⟨-, -, h4_7, h4_8, h4_9, h4_10, h4_11, h4_12, h4_13, h4_14, h4_15⟩, hnR5⟩ := hnR4
  obtain ⟨-, hnR6⟩ := hnR5
  obtain ⟨-, hnR7⟩ := hnR6
  obtain ⟨⟨h7_8, h7_9, h7_10, h7_11, h7_12, h7_13, h7_14, h7_15⟩, hnR8⟩ := hnR7
  obtain ⟨⟨h8_9, h8_10, h8_11, h8_12, h8_13, h8_14, h8_15⟩, hnR9⟩ := hnR8
  obtain ⟨⟨h9_10, h9_11, h9_12, h9_13, h9_14, h9_15⟩, hnR10⟩ := hnR9
  obtain ⟨⟨h10_11, h10_12, h10_13, h10_14, h10_15⟩, hnR11⟩ := hnR10
  obtain ⟨⟨h11_12, h11_13, h11_14, h11_15⟩, hnR12⟩ := hnR11
  obtain ⟨⟨h12_13, h12_14, h12_15⟩, hnR13⟩ := hnR12
  obtain ⟨⟨h13_14, h13_15⟩, h14_15⟩ := hnR13
  have hcur : cursorReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hpol : polReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hvar : varReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hdone : doneReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hrem : remainingReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hpol2 : pol2Reg < start := hs.below _ (by simp [longClauseRegisterList])
  have hvar2 : var2Reg < start := hs.below _ (by simp [longClauseRegisterList])
  have hpol3 : pol3Reg < start := hs.below _ (by simp [longClauseRegisterList])
  have hvar3 : var3Reg < start := hs.below _ (by simp [longClauseRegisterList])
  have hcarryPol : carryPolReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hcarryVal : carryValReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hpos : posPolReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hfresh : freshReg < start := hs.below _ (by simp [longClauseRegisterList])
  have hcur0 : cursorReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hpol0 : polReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hvar0 : varReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hdone0 : doneReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hrem0 : remainingReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hpol20 : pol2Reg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hvar20 : var2Reg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hpol30 : pol3Reg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hvar30 : var3Reg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hcarryPol0 : carryPolReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hcarryVal0 : carryValReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hpos0 : posPolReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  have hfresh0 : freshReg ≠ 0 := hs.nonzero _ (by simp [longClauseRegisterList])
  refine { main := { below := ⟨hcur, hpol, hvar, hdone⟩
                     nonzero := ⟨hcur0, hpol0, hvar0, hdone0⟩
                     distinct := ⟨h0_2, h0_3, h0_4, h2_3, h2_4, h3_4⟩ }
           second := { below := ⟨hcur, hpol2, hvar2, hdone⟩
                       nonzero := ⟨hcur0, hpol20, hvar20, hdone0⟩
                       distinct := ⟨h0_8, h0_9, h0_4, h8_9, (Ne.symm h4_8), (Ne.symm h4_9)⟩ }
           third := { below := ⟨hcur, hpol3, hvar3, hdone⟩
                      nonzero := ⟨hcur0, hpol30, hvar30, hdone0⟩
                      distinct := ⟨h0_10, h0_11, h0_4, h10_11, (Ne.symm h4_10), (Ne.symm h4_11)⟩ }
           cross := ⟨h8_10, h8_11, h9_10, h9_11⟩
           writer_below := ⟨hcarryPol, hcarryVal, hpos, hfresh, hrem⟩
           carry_pol_nonzero := hcarryPol0
           writer_nonzero := ⟨hcarryVal0, hfresh0⟩
           remaining_nonzero := hrem0
           writer_distinct := ⟨h12_13, h12_14, h12_15, (Ne.symm h7_12), h13_14, h13_15,
             (Ne.symm h7_13), h14_15, (Ne.symm h7_14), (Ne.symm h7_15)⟩
           writer_parser := by
             intro r hr
             rcases hr with rfl | rfl | rfl | rfl | rfl
             · exact ⟨(Ne.symm h0_12), (Ne.symm h2_12), (Ne.symm h3_12), (Ne.symm h4_12),
                 (Ne.symm h8_12), (Ne.symm h9_12), (Ne.symm h10_12), (Ne.symm h11_12)⟩
             · exact ⟨(Ne.symm h0_13), (Ne.symm h2_13), (Ne.symm h3_13), (Ne.symm h4_13),
                 (Ne.symm h8_13), (Ne.symm h9_13), (Ne.symm h10_13), (Ne.symm h11_13)⟩
             · exact ⟨(Ne.symm h0_14), (Ne.symm h2_14), (Ne.symm h3_14), (Ne.symm h4_14),
                 (Ne.symm h8_14), (Ne.symm h9_14), (Ne.symm h10_14), (Ne.symm h11_14)⟩
             · exact ⟨(Ne.symm h0_15), (Ne.symm h2_15), (Ne.symm h3_15), (Ne.symm h4_15),
                 (Ne.symm h8_15), (Ne.symm h9_15), (Ne.symm h10_15), (Ne.symm h11_15)⟩
             · exact ⟨(Ne.symm h0_7), (Ne.symm h2_7), (Ne.symm h3_7), (Ne.symm h4_7),
                 h7_8, h7_9, h7_10, h7_11⟩ }

lemma LongClauseRegisterSafety.pair_register_nodup
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    ([cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg, outerReg]).Nodup := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn ⊢
  aesop

lemma LongClauseRegisterSafety.triple_register_nodup
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    ([cursorReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
      posPolReg, negPolReg, freshReg, outerReg]).Nodup := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn ⊢
  obtain ⟨⟨h0_1, h0_2, h0_3, h0_4, h0_5, h0_6, h0_7, h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14, h0_15⟩, ⟨h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15⟩, ⟨h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15⟩, ⟨h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15⟩, ⟨h4_5, h4_6, h4_7, h4_8, h4_9, h4_10, h4_11, h4_12, h4_13, h4_14, h4_15⟩, ⟨h5_6, h5_7, h5_8, h5_9, h5_10, h5_11, h5_12, h5_13, h5_14, h5_15⟩, ⟨h6_7, h6_8, h6_9, h6_10, h6_11, h6_12, h6_13, h6_14, h6_15⟩, ⟨h7_8, h7_9, h7_10, h7_11, h7_12, h7_13, h7_14, h7_15⟩, ⟨h8_9, h8_10, h8_11, h8_12, h8_13, h8_14, h8_15⟩, ⟨h9_10, h9_11, h9_12, h9_13, h9_14, h9_15⟩, ⟨h10_11, h10_12, h10_13, h10_14, h10_15⟩, ⟨h11_12, h11_13, h11_14, h11_15⟩, ⟨h12_13, h12_14, h12_15⟩, ⟨h13_14, h13_15⟩, h14_15⟩ := hn
  exact ⟨⟨h0_2, h0_3, h0_4, h0_8, h0_9, h0_10, h0_11, h0_14, h0_6, h0_15, h0_5⟩, ⟨⟨h2_3, h2_4, h2_8, h2_9, h2_10, h2_11, h2_14, h2_6, h2_15, h2_5⟩, ⟨⟨h3_4, h3_8, h3_9, h3_10, h3_11, h3_14, h3_6, h3_15, h3_5⟩, ⟨⟨h4_8, h4_9, h4_10, h4_11, h4_14, h4_6, h4_15, h4_5⟩, ⟨⟨h8_9, h8_10, h8_11, h8_14, (Ne.symm h6_8), h8_15, (Ne.symm h5_8)⟩, ⟨⟨h9_10, h9_11, h9_14, (Ne.symm h6_9), h9_15, (Ne.symm h5_9)⟩, ⟨⟨h10_11, h10_14, (Ne.symm h6_10), h10_15, (Ne.symm h5_10)⟩, ⟨⟨h11_14, (Ne.symm h6_11), h11_15, (Ne.symm h5_11)⟩, ⟨⟨(Ne.symm h6_14), h14_15, (Ne.symm h5_14)⟩, ⟨⟨h6_15, (Ne.symm h5_6)⟩, (Ne.symm h5_15)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma LongClauseRegisterSafety.triple_pos_neg_nodup
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    ([cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, pol3Reg, var3Reg,
      freshReg, outerReg, posPolReg, negPolReg]).Nodup := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn ⊢
  obtain ⟨⟨h0_1, h0_2, h0_3, h0_4, h0_5, h0_6, h0_7, h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14, h0_15⟩, ⟨h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15⟩, ⟨h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15⟩, ⟨h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15⟩, ⟨h4_5, h4_6, h4_7, h4_8, h4_9, h4_10, h4_11, h4_12, h4_13, h4_14, h4_15⟩, ⟨h5_6, h5_7, h5_8, h5_9, h5_10, h5_11, h5_12, h5_13, h5_14, h5_15⟩, ⟨h6_7, h6_8, h6_9, h6_10, h6_11, h6_12, h6_13, h6_14, h6_15⟩, ⟨h7_8, h7_9, h7_10, h7_11, h7_12, h7_13, h7_14, h7_15⟩, ⟨h8_9, h8_10, h8_11, h8_12, h8_13, h8_14, h8_15⟩, ⟨h9_10, h9_11, h9_12, h9_13, h9_14, h9_15⟩, ⟨h10_11, h10_12, h10_13, h10_14, h10_15⟩, ⟨h11_12, h11_13, h11_14, h11_15⟩, ⟨h12_13, h12_14, h12_15⟩, ⟨h13_14, h13_15⟩, h14_15⟩ := hn
  exact ⟨⟨h0_1, h0_2, h0_3, h0_4, h0_8, h0_9, h0_10, h0_11, h0_15, h0_5, h0_14, h0_6⟩, ⟨⟨h1_2, h1_3, h1_4, h1_8, h1_9, h1_10, h1_11, h1_15, h1_5, h1_14, h1_6⟩, ⟨⟨h2_3, h2_4, h2_8, h2_9, h2_10, h2_11, h2_15, h2_5, h2_14, h2_6⟩, ⟨⟨h3_4, h3_8, h3_9, h3_10, h3_11, h3_15, h3_5, h3_14, h3_6⟩, ⟨⟨h4_8, h4_9, h4_10, h4_11, h4_15, h4_5, h4_14, h4_6⟩, ⟨⟨h8_9, h8_10, h8_11, h8_15, (Ne.symm h5_8), h8_14, (Ne.symm h6_8)⟩, ⟨⟨h9_10, h9_11, h9_15, (Ne.symm h5_9), h9_14, (Ne.symm h6_9)⟩, ⟨⟨h10_11, h10_15, (Ne.symm h5_10), h10_14, (Ne.symm h6_10)⟩, ⟨⟨h11_15, (Ne.symm h5_11), h11_14, (Ne.symm h6_11)⟩, ⟨⟨(Ne.symm h5_15), (Ne.symm h14_15), (Ne.symm h6_15)⟩, ⟨⟨h5_14, h5_6⟩, (Ne.symm h6_14)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma LongClauseRegisterSafety.pair_pos_neg_nodup
    {start cursorReg lengthReg polReg varReg doneReg outerReg negPolReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hs : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg outerReg
      negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg) :
    ([cursorReg, lengthReg, polReg, varReg, doneReg, pol2Reg, var2Reg, freshReg,
      outerReg, posPolReg, negPolReg]).Nodup := by
  have hn := hs.register_nodup
  simp [longClauseRegisterList, List.nodup_cons] at hn ⊢
  aesop

def splitTailEmitStepProg
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) : Program :=
  .ifNZ (.eq (.reg remainingReg) (.const 0))
    Program.skip
    (.ifNZ (.eq (.reg remainingReg) (.const 1))
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound)
      (.ifNZ (.eq (.reg remainingReg) (.const 2))
        (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          carryPolReg carryValReg posPolReg freshReg bound)))

lemma splitTailEmitStepProg_zero_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) (σ : Store)
    (hrem : σ remainingReg = 0) :
    (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ = σ := by
  simp [splitTailEmitStepProg, hrem, Expr.eval]

lemma splitTailEmitStepProg_one_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) (σ : Store)
    (hrem : σ remainingReg = 1) :
    (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ =
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  simp [splitTailEmitStepProg, hrem, Expr.eval]

lemma splitTailEmitStepProg_two_eval
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ) (σ : Store)
    (hrem : σ remainingReg = 2) :
    (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ =
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
  simp [splitTailEmitStepProg, hrem, Expr.eval]

lemma splitTailEmitStepProg_low_frame_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
      r ≠ remainingReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
      r ≠ var3Reg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ posPolReg ∧
      r ≠ freshReg) :
    (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  rcases hrsafe with ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3,
    hcp, hcv, hpos, hfr⟩
  cases ls with
  | nil =>
      have hrem : σ remainingReg = 0 := by simpa using hrel.remaining
      have heq := splitTailEmitStepProg_zero_eval curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        bound σ hrem
      exact congrArg (fun q : Store => q r) heq
  | cons l rest =>
      cases rest with
      | nil =>
          have hremainingValue : σ remainingReg = 1 := by simpa using hrel.remaining
          rw [splitTailEmitStepProg_one_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
            pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound σ
            hremainingValue]
          exact splitTailEmitTerminalOneProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg varReg
            doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
            freshReg bound base carry l pref tail addr σ (hbound l (by simp)) hrel hr
            ⟨hrc, hrp2, hrv2, hrd, hcp, hcv, hrem⟩
      | cons l2 rest =>
          cases rest with
          | nil =>
              have hremainingValue : σ remainingReg = 2 := by simpa using hrel.remaining
              rw [splitTailEmitStepProg_two_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
                pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound σ
                hremainingValue]
              exact splitTailEmitTerminalTwoProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg varReg
                doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
                freshReg bound base carry l l2 pref tail addr σ (hbound l (by simp))
                (hbound l2 (by simp)) hrel hr
                ⟨hrc, hrp2, hrv2, hrp3, hrv3, hrd, hcp, hcv, hrem⟩
          | cons l3 rest =>
              simpa [splitTailEmitStepProg, hrel.remaining, Expr.eval] using
                (splitTailEmitIntermediateProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
                  varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                  posPolReg freshReg bound base carry l l2 l3 rest pref tail addr σ
                  (hbound l (by simp)) hrel hr
                  ⟨hrc, hrp, hrv, hrd, hcv, hpos, hfr, hrem⟩)

def splitTailEmitProg
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ) : Program :=
  .ifNZ (.eq (.reg remainingReg) (.const 0))
    (splitTailEmitTerminalZeroProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound)
    (.forN (.const (tailBound + 1))
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound))


end NPComplete.CookLevin

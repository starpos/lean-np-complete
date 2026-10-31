module

public import NPComplete.CookLevin.UniformPackaging.WriterRawBounds
public import NPComplete.BoundedWhile.Frame
meta import NPComplete.Meta.ApiLayer

/-!
# Parser state bounds during emission

Decoding a clause advances the cursor while preserving its input-tail and scratch
state. This module proves cursor, frame, and zero-cell facts used to bound the
emitting phases of the producer.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma decodeUnaryStep_cursor_ge
    (cursorReg countReg doneReg : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) :
    σ cursorReg ≤ (decodeUnaryStep cursorReg countReg doneReg).eval σ cursorReg := by
  unfold decodeUnaryStep
  simp only [eval_ifNZ, eval_seq, eval_assign, eval_skip, Expr.eval]
  by_cases hd : σ doneReg = 0
  · split_ifs <;> simp_all [writeReg]
    all_goals split_ifs <;> simp_all [writeReg]
  · simp [hd]

lemma decode_unary_loop_cursor_ge
    (cursorReg countReg doneReg k : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) :
    σ cursorReg ≤
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) k σ) cursorReg := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [uniform_loopEval_succ_right]
      have hs := decodeUnaryStep_cursor_ge cursorReg countReg doneReg
        (loopEval (decodeUnaryStep cursorReg countReg doneReg) k σ) hcc hcd
      have hi := ih σ
      omega

lemma decodeNatProgramAt_cursor_ge
    (cursorReg countReg doneReg boundReg : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) :
    σ cursorReg ≤
      (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ cursorReg := by
  unfold decodeNatProgramAt decodeUnaryProgAt
  rw [eval_forN]
  simp only [Expr.eval]
  exact decode_unary_loop_cursor_ge cursorReg countReg doneReg (σ boundReg) σ hcc hcd

lemma decodeLiteralValueProgramAt_cursor_ge
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) :
    σ cursorReg + 1 ≤
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        cursorReg := by
  unfold decodeLiteralValueProgramAt
  rw [eval_seq, eval_seq, eval_seq]
  let σ1 := (readBitAdvanceProg cursorReg polReg).eval σ
  have hσ1 : σ1 cursorReg = σ cursorReg + 1 := by
    simpa [σ1] using (readBitAdvanceProg_eval cursorReg polReg σ hcp).2
  let σ2 := (Program.assign varReg (.const 0)).eval σ1
  have hσ2 : σ2 cursorReg = σ1 cursorReg := by
    simpa [σ2, eval_assign, Expr.eval] using
      (writeReg_diff σ1 varReg 0 cursorReg hcv)
  let σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hσ3 : σ3 cursorReg = σ2 cursorReg := by
    simpa [σ3, eval_assign, Expr.eval] using
      (writeReg_diff σ2 doneReg 0 cursorReg hcd)
  have hnat := decodeNatProgramAt_cursor_ge cursorReg varReg doneReg boundReg σ3 hcv hcd
  simp only [decodeNatProgramAt] at hnat
  rw [hσ3, hσ2, hσ1] at hnat
  omega

lemma decodeLiteralValueProgramAt_root
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (h0c : cursorReg ≠ 0) (h0p : polReg ≠ 0) (h0v : varReg ≠ 0)
    (h0d : doneReg ≠ 0) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ 0 = σ 0 := by
  exact (decodeLiteralValueProgramAt_avoids_frame cursorReg polReg varReg doneReg boundReg).eval_frame
    σ ⟨h0c.symm, h0p.symm, h0v.symm, h0d.symm⟩

export NPComplete.SAT (decodeLiteralValueProgramAt_frame decodeLiteralValueProgramAt_bounded)

/-- The polarity register of a literal decoder always ends up holding the cell
    the cursor started on — independent of what that cell contains. -/
lemma decodeLiteralValueProgramAt_pol_eq
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ polReg =
      σ (σ cursorReg) := by
  unfold decodeLiteralValueProgramAt
  rw [eval_seq, eval_seq, eval_seq]
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ with hσ1
  set σ2 := (Program.assign varReg (.const 0)).eval σ1 with hσ2
  set σ3 := (Program.assign doneReg (.const 0)).eval σ2 with hσ3
  have p1 : σ1 polReg = σ (σ cursorReg) := (readBitAdvanceProg_eval cursorReg polReg σ hcp).1
  have p2 : σ2 polReg = σ1 polReg := by
    simp [hσ2, eval_assign, Expr.eval, writeReg_diff _ varReg _ polReg hpv]
  have p3 : σ3 polReg = σ2 polReg := by
    simp [hσ3, eval_assign, Expr.eval, writeReg_diff _ doneReg _ polReg hpd]
  have p4 : (decodeNatProgramAt cursorReg varReg doneReg boundReg).eval σ3 polReg = σ3 polReg :=
    decodeNatProgramAt_frame cursorReg varReg doneReg boundReg polReg σ3
      (Ne.symm hcp) hpv hpd
  exact p4.trans (p3.trans (p2.trans p1))

lemma cellsZeroFrom_decodeNatProgramAt
    (cursorReg countReg doneReg boundReg : ℕ) {n : ℕ} (σ : Store)
    (hc : cursorReg < n) (hk : countReg < n) (hd : doneReg < n)
    (h : CellsZeroFrom n σ) :
    CellsZeroFrom n
      ((decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ) := by
  intro i hi
  rw [decodeNatProgramAt_frame cursorReg countReg doneReg boundReg i σ
    (by omega) (by omega) (by omega)]
  exact h i hi

/-! The scratch reset only writes control registers below the input window, so
    the zero tail of the input survives one outer iteration's reset and length
    decode; combined with the tight window, this supplies the Boolean-cell
    premise of the short-clause long branch along the real pipeline. -/

lemma cellsZeroFrom_uniformEmitScratchResetProg {n : ℕ} (σ : Store)
    (hlow : ∀ r ∈ uniformEmitScratchRegs, r < n)
    (hpos : uctPosPolReg < n) (hneg : uctNegPolReg < n)
    (h : CellsZeroFrom n σ) :
    CellsZeroFrom n (uniformEmitScratchResetProg.eval σ) := by
  intro i hi
  have hnot : i ∉ uniformEmitScratchRegs := by
    intro hmem
    have := hlow i hmem
    omega
  rw [uniformEmitScratchResetProg_frame σ hnot (by omega) (by omega)]
  exact h i hi

/-- A tight input window plus the zero tail makes every cell from the window
    start onward Boolean — the read-side premise the short-clause long branch
    needs for its unselected decodes. -/
lemma cells_le_one_of_window_zero (σ : Store) (addr inputEnd : ℕ) (bits : Bits)
    (hbits : BitsFrom σ addr bits) (hlen : addr + bits.length = inputEnd)
    (hz : CellsZeroFrom inputEnd σ) (i : ℕ) (hlo : addr ≤ i) :
    σ i ≤ 1 := by
  by_cases hi : i < inputEnd
  · have hlt : i - addr < bits.length := by omega
    have hbi := hbits (i - addr) hlt
    have haddr : addr + (i - addr) = i := by omega
    rw [haddr] at hbi
    have h01 : σ i = 0 ∨ σ i = 1 := by
      cases bits[i - addr] <;> simp [hbi]
    omega
  · have h0 := hz i (by omega)
    omega

lemma cnfEmitRel_named_values_le
    {M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ}
    {clauses : List Clause} {tail pref : Bits} {addr : ℕ} {σ : Store}
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base clauses tail pref addr σ)
     (K : ℕ) (hbase : base ≤ K)
    (hclauses : clauses.length ≤ K) (haddr : addr ≤ K)
    (hwriter : start + pref.length ≤ K) :
    σ cursorReg ≤ K ∧ σ outerReg ≤ K ∧ σ freshReg ≤ K ∧
      σ lengthReg ≤ K ∧ σ doneReg ≤ K ∧ σ posPolReg ≤ K ∧
      σ negPolReg ≤ K ∧ σ (M + curJ) ≤ K := by
  have hK1 : 1 ≤ K := by
    exact hrel.writer.start_pos.trans
      (Nat.le_trans (Nat.le_add_right _ _) hwriter)
  refine ⟨by rw [hrel.cursor]; exact haddr,
    by rw [hrel.outer]; exact hclauses,
    by rw [hrel.fresh]; exact hbase,
    by rw [hrel.length_zero]; omega,
    by rw [hrel.done_zero]; omega,
    by rw [hrel.pos]; omega,
    by rw [hrel.neg]; omega,
      by rw [hrel.writer.cursor]; exact hwriter⟩

lemma splitTail_emit_long_clause_eval_end_to_end_after_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
      bound tailBound : ℕ)
    (base : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal) (rest : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
        M + curJ)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref)
    (hpos : σ posPolReg = 0) (hfresh : σ freshReg = base)
    (hremaining : σ remainingReg = (l1 :: l2 :: l3 :: l4 :: rest).length)
    (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg bound tailBound).eval σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg posPolReg ∧
      base' = (splitTail (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: l4 :: rest)).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var 0 base) ++
          splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: l4 :: rest) ∧
      τ cursorReg = (addr + l1.var + 2 + l2.var + 2) +
        (splitTailInputBits (l3 :: l4 :: rest) []).length ∧
      (∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r) := by
  let setup := splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  obtain ⟨hpost, hsetupHigh, _⟩ := splitTailEmitLongClauseSetup_eval
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base l1 l2 (l3 :: l4 :: rest) pref tail addr σ hbound1 hbound2 hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety
  let σsetup := setup.eval σ
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hdone, hbase', hpayload', hcursor', hafter⟩ :=
    splitTailEmitRel_nonempty_fixed_eval_after_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound
      (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: l4 :: rest)
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) tail
      (addr + l1.var + 2 + l2.var + 2) σsetup hboundTail (by simp) hls hpost
  have hframe : SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry'
      ls' pref' tail addr' cursorReg remainingReg freshReg posPolReg := by
    refine ⟨hdone.done, ?_, hdone.pos⟩
    intro r hr
    exact (hdone.high_frame r hr).trans (by simpa [σsetup, setup] using hsetupHigh r hr)
  have hlong : τ = (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg bound tailBound).eval σ := by
    rw [splitTailEmitLongClauseProg, eval_seq]
    simpa [σsetup, setup] using hτ
  have hprefix : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length ≤ τ (M + curJ) := by
    rw [hdone.done.writer.cursor, hpayload']
    simp [List.length_append]
  refine ⟨τ, base', carry', ls', pref', addr', hlong, hframe, hbase', hpayload', hcursor', ?_⟩
  intro r hr hrc hrt
  have hrprefix : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length ≤ r := hprefix.trans hr
  have hrsetup : start + pref.length + l1.var + l2.var + base + 6 ≤ r := by
    simp [encodedThreeLiteralBits, encodedLiteralBits, encodeNat_length,
      List.length_append] at hrprefix ⊢
    omega
  have hsetup := splitTailEmitLongClauseSetup_frame_after
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
    var3Reg carryPolReg carryValReg posPolReg freshReg bound base l1 l2 l3 l4 rest pref tail addr σ
    hbound1 hbound2 hroom hinput hcurJ htmpJ hstartAtInput hwriter hpos hfresh hcursor hsafety
    hrsetup hrc hrt
  exact (hafter r hr hrc hrt).trans (by simpa [σsetup, setup] using hsetup)

def LongClauseLowWriteSet (cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    lengthReg outerReg negPolReg : ℕ) (r : ℕ) : Prop :=
  r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨
  r = remainingReg ∨ r = pol2Reg ∨ r = var2Reg ∨ r = pol3Reg ∨
  r = var3Reg ∨ r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
  r = freshReg ∨ r = lengthReg ∨ r = outerReg ∨ r = negPolReg

lemma storeValuesLe_of_long_clause_frames
    (K M curJ tmpJ start : ℕ) (σ τ : Store) (bits : Bits)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg : ℕ)
    (hK1 : 1 ≤ K) (hσ : StoreValuesLe K σ)
    (hwriter : WriterState τ M curJ start bits)
    (hcursor : τ (M + curJ) ≤ K) (htmp : τ (M + tmpJ) ≤ K)
    (hframeLow : ∀ r, r < start →
      ¬ LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r = σ r)
    (hsmall : ∀ r, r < start →
      LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r ≤ K)
    (hafter : ∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r) :
    StoreValuesLe K τ := by
  intro r
  by_cases hlow : r < start
  · by_cases hw : LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        lengthReg outerReg negPolReg r
    · exact hsmall r hlow hw
    · rw [hframeLow r hlow hw]
      exact hσ r
  · by_cases hout : r < (τ (M + curJ))
    · have hlen : r - start < bits.length := by
        have hc := hwriter.cursor
        omega
      have hb := hwriter.bits (r - start) hlen
      have hidx : start + (r - start) = r := by omega
      have hb' : τ r = if bits[r - start] then 1 else 0 := by
        simpa [hidx] using hb
      rw [hb']
      split <;> omega
    · by_cases hrc : r = M + curJ
      · simpa [hrc] using hcursor
      · by_cases hrt : r = M + tmpJ
        · simpa [hrt] using htmp
        · exact (hafter r (by omega) hrc hrt).trans_le (hσ r)

lemma storeValuesLe_uniformEmitIterBody_of_frames
    (N K : ℕ) (σ τ : Store) (bits : Bits)
    (hK1 : 1 ≤ K) (hσ : StoreValuesLe K σ)
    (hwriter : WriterState τ (uniformMNat N) uctCurJ uniformStartNat bits)
    (hcursor : τ (uniformMNat N + uctCurJ) ≤ K)
    (htmp : τ (uniformMNat N + uctTmpJ) ≤ K)
    (hframeLow : ∀ r, r < uniformStartNat →
      ¬ LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg
        uctOuterReg uctNegPolReg r → τ r = σ r)
    (hsmall : ∀ r, r < uniformStartNat →
      LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg
        uctOuterReg uctNegPolReg r → τ r ≤ K)
    (hafter : ∀ r, τ (uniformMNat N + uctCurJ) ≤ r →
      r ≠ uniformMNat N + uctCurJ → r ≠ uniformMNat N + uctTmpJ → τ r = σ r) :
    StoreValuesLe K τ := by
  exact storeValuesLe_of_long_clause_frames K (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat σ τ bits uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg uctOuterReg uctNegPolReg
    hK1 hσ hwriter hcursor htmp hframeLow hsmall hafter

lemma uniformEmitIterBody_scratch_values (σ τ : Store)
    (hτ : uniformEmitIterBody.eval σ = τ) :
    τ uctPolReg = 0 ∧ τ uctVarReg = 0 ∧ τ uctDoneReg = 0 ∧
      τ uctLengthReg = 0 ∧ τ uctRemainingReg = 0 ∧ τ uctPol2Reg = 0 ∧
      τ uctVar2Reg = 0 ∧ τ uctPol3Reg = 0 ∧ τ uctVar3Reg = 0 ∧
      τ uctCarryPolReg = 0 ∧ τ uctCarryValReg = 0 := by
  let σe := uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ)
  obtain ⟨_, _, hpol, hvar, hdone, hlen, hrem, hpol2, hvar2, hpol3, hvar3,
    hcarryPol, hcarryVal⟩ := uniformEmitScratchResetProg_values σe
  have heq : uniformEmitIterBody.eval σ = uniformEmitScratchResetProg.eval σe := by
    simp [uniformEmitIterBody, σe, eval_seq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [← hτ, heq]
  · exact hpol
  · exact hvar
  · exact hdone
  · exact hlen
  · exact hrem
  · exact hpol2
  · exact hvar2
  · exact hpol3
  · exact hvar3
  · exact hcarryPol
  · exact hcarryVal

lemma uniformEmitIterBody_low_frame_of_core (σ : Store) (r : ℕ)
    (hr : r < uniformStartNat)
    (hnot : ¬ LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
      uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg uctOuterReg uctNegPolReg r)
    (hcore : uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ) r =
      uniformEmitScratchResetProg.eval σ r) :
    uniformEmitIterBody.eval σ r = σ r := by
  have hne : r ≠ uctCursorReg ∧ r ≠ uctPolReg ∧ r ≠ uctVarReg ∧ r ≠ uctDoneReg ∧
      r ≠ uctRemainingReg ∧ r ≠ uctPol2Reg ∧ r ≠ uctVar2Reg ∧ r ≠ uctPol3Reg ∧
      r ≠ uctVar3Reg ∧ r ≠ uctCarryPolReg ∧ r ≠ uctCarryValReg ∧ r ≠ uctPosPolReg ∧
      r ≠ uctFreshReg ∧ r ≠ uctLengthReg ∧ r ≠ uctOuterReg ∧ r ≠ uctNegPolReg := by
    simpa only [LongClauseLowWriteSet, not_or] using hnot
  obtain ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3, hrcp, hrcv,
    hrpos, hrfresh, hrlen, hrout, hrneg⟩ := hne
  have hscratch : r ∉ uniformEmitScratchRegs := by
    intro hmem
    simp [uniformEmitScratchRegs] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      contradiction
  have hfirst : uniformEmitScratchResetProg.eval σ r = σ r :=
    uniformEmitScratchResetProg_frame σ hscratch hrpos hrneg
  have hlast : uniformEmitScratchResetProg.eval
      (uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ)) r =
      uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ) r :=
    uniformEmitScratchResetProg_frame _ hscratch hrpos hrneg
  unfold uniformEmitIterBody
  rw [eval_seq, eval_seq]
  exact hlast.trans (hcore.trans hfirst)

lemma uniformEmitIterBody_low_frame_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) (r : ℕ) (hr : r < uniformStartNat)
    (hnot : ¬ LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
      uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg uctOuterReg uctNegPolReg r) :
    uniformEmitIterBody.eval σ r = σ r := by
  let σr := uniformEmitScratchResetProg.eval σ
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hbr : σr uctSavedBoundReg = N := by
    exact (uniformEmitScratchResetProg_frame σ (r := uctSavedBoundReg)
      (by decide) (by decide) (by decide)).trans hb
  have hne : r ≠ uctCursorReg ∧ r ≠ uctPolReg ∧ r ≠ uctVarReg ∧ r ≠ uctDoneReg ∧
      r ≠ uctRemainingReg ∧ r ≠ uctPol2Reg ∧ r ≠ uctVar2Reg ∧ r ≠ uctPol3Reg ∧
      r ≠ uctVar3Reg ∧ r ≠ uctCarryPolReg ∧ r ≠ uctCarryValReg ∧ r ≠ uctPosPolReg ∧
      r ≠ uctFreshReg ∧ r ≠ uctLengthReg ∧ r ≠ uctOuterReg ∧ r ≠ uctNegPolReg := by
    simpa only [LongClauseLowWriteSet, not_or] using hnot
  obtain ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3, hrcp, hrcv,
    hrpos, hrfresh, hrlen, hrout, hrneg⟩ := hne
  have hok : EmitClauseBoundRegOk r uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
      uctFreshReg uctOuterReg := by
    refine {
      split := {
        below := hr
        ne_cursor := hrc
        ne_pol := hrp
        ne_var := hrv
        ne_done := hrd
        ne_remaining := hrem
        ne_pol2 := hrp2
        ne_var2 := hrv2
        ne_pol3 := hrp3
        ne_var3 := hrv3
        ne_carry_pol := hrcp
        ne_carry_val := hrcv
        ne_pos_pol := hrpos
        ne_fresh := hrfresh }
      ne_length := hrlen
      ne_outer := hrout
      ne_neg_pol := hrneg }
  have hbound := emitClauseIterProgram_bound_frame_of_rel
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
    (varReg := uctVarReg) (doneReg := uctDoneReg) (lengthReg := uctLengthReg)
    (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg)
    (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg)
    (negPolReg := uctNegPolReg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (freshReg := uctFreshReg) (outerReg := uctOuterReg)
    (boundReg := r) (bound := N) (tailBound := N) (base := base)
    c cs tail pref addr σr uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hrelr hok
  have hAt := emitClauseIterProgramAt_eval_of_rel
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ) (start := uniformStartNat)
    (cursorReg := uctCursorReg) (polReg := uctPolReg) (varReg := uctVarReg)
    (doneReg := uctDoneReg) (lengthReg := uctLengthReg) (remainingReg := uctRemainingReg)
    (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg)
    (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg) (negPolReg := uctNegPolReg)
    (carryPolReg := uctCarryPolReg) (carryValReg := uctCarryValReg)
    (freshReg := uctFreshReg) (outerReg := uctOuterReg) (boundReg := uctSavedBoundReg)
    (bound := N) (tailBound := N) (base := base) c cs tail pref addr σr
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  have hcore : uniformEmitIterCoreBody.eval σr r = σr r := by
    have heq := congrArg (fun s : Store => s r) hAt
    simpa [uniformEmitIterCoreBody] using heq.trans hbound
  exact uniformEmitIterBody_low_frame_of_core σ r hr hnot hcore

lemma uniformEmitIterBody_low_values_of_rel
    (N K : ℕ) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ τ : Store)
    (hτ : uniformEmitIterBody.eval σ = τ)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      cs tail pref addr τ)
    (hcursor : τ uctCursorReg ≤ K) (houter : τ uctOuterReg ≤ K)
    (hfresh : τ uctFreshReg ≤ K) (hK1 : 1 ≤ K) :
    ∀ r, r < uniformStartNat →
      LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg
        uctOuterReg uctNegPolReg r → τ r ≤ K := by
  obtain ⟨hpol, hvar, hdone, hlen, hrem, hpol2, hvar2, hpol3, hvar3,
    hcarryPol, hcarryVal⟩ := uniformEmitIterBody_scratch_values σ τ hτ
  intro r hr hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hcursor
  · rw [hpol]
    omega
  · rw [hvar]
    omega
  · rw [hdone]
    omega
  · rw [hrem]
    omega
  · rw [hpol2]
    omega
  · rw [hvar2]
    omega
  · rw [hpol3]
    omega
  · rw [hvar3]
    omega
  · rw [hcarryPol]
    omega
  · rw [hcarryVal]
    omega
  · rw [hrel.pos]
    omega
  · exact hfresh
  · rw [hrel.length_zero]
    omega
  · exact houter
  · rw [hrel.neg]
    omega

lemma uniformEmitIterBody_store_tight_of_frame
    (N K : ℕ) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ τ : Store)
    (hτ : uniformEmitIterBody.eval σ = τ)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      cs tail pref addr τ)
    (hK1 : 1 ≤ K) (hσ : StoreValuesLe K σ)
    (hcursor : τ uctCursorReg ≤ K) (houter : τ uctOuterReg ≤ K)
    (hfresh : τ uctFreshReg ≤ K)
    (hwriterCursor : τ (uniformMNat N + uctCurJ) ≤ K)
    (hframeLow : ∀ r, r < uniformStartNat →
      ¬ LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg
        uctOuterReg uctNegPolReg r → τ r = σ r)
    (htmp : τ (uniformMNat N + uctTmpJ) ≤ K)
    (hafter : ∀ r, τ (uniformMNat N + uctCurJ) ≤ r →
      r ≠ uniformMNat N + uctCurJ → r ≠ uniformMNat N + uctTmpJ → τ r = σ r) :
    StoreValuesLe K τ := by
  have hsmall := uniformEmitIterBody_low_values_of_rel N K cs tail pref addr base σ τ
    hτ hrel hcursor houter hfresh hK1
  exact storeValuesLe_uniformEmitIterBody_of_frames N K σ τ pref hK1 hσ hrel.writer
    hwriterCursor htmp hframeLow hsmall hafter

end NPComplete.CookLevin

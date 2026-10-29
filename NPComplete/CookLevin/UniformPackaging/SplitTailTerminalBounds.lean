module

public import NPComplete.CookLevin.UniformPackaging.SplitTailReachability

/-!
# Terminal split-tail bounds

The terminal branches need explicit register values and frames not settled by
the intermediate-step bounds. This module bounds their temporary values and
proves the conditions needed for one- and two-literal terminal emission.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral encodeThreeClause)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma splitTailEmitTerminalOneProgAt_tmp_value
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ
      (M + tmpJ) = l.var := by
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧ doneReg < start :=
    ⟨hrel.safety.second.below.1, hrel.safety.second.below.2.1,
      hrel.safety.second.below.2.2.1, hrel.safety.second.below.2.2.2⟩
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0 :=
    hrel.safety.second.nonzero
  obtain ⟨hcp, hcv, hcd, hpv, hpd, hvd⟩ := hrel.safety.second.distinct
  have hdec := decodeLiteralValueProgramAt_correct cursorReg pol2Reg var2Reg doneReg boundReg
    bound addr l tail σ hcp hcv hcd hpv hpd hvd hok.ne_cursor hok.ne_pol2 hok.ne_var2
    hok.ne_done
    (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
    (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
    (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
    (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
    hbound hb hrel.cursor hbits
  set σw := (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
  have hws : WriterState σw M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ σw cursorReg pol2Reg var2Reg doneReg
      hrel.writer hdec.2.2.2.2 hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2
  have hcpw : σw carryPolReg = 1 :=
    (hdec.2.2.2.2 carryPolReg
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.2.2.1
      (hrel.safety.writer_parser carryPolReg (Or.inl rfl)).2.2.2.1).trans hrel.carry_pol
  have hcvw : σw carryValReg = carry.var :=
    (hdec.2.2.2.2 carryValReg
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.2.2.1
      (hrel.safety.writer_parser carryValReg (Or.inr (Or.inl rfl))).2.2.2.1).trans hrel.carry_val
  have hpolw : σw pol2Reg = literalPolarity l := by
    cases l <;> simpa [literalPolarity] using hdec.2.1
  have hvarw : σw var2Reg = l.var := hdec.2.2.1
  have hpol01 : literalPolarity l = 0 ∨ literalPolarity l = 1 := by
    cases l <;> simp [literalPolarity]
  have hroom : start + pref.length + carry.var + l.var + l.var + 6 < M + curJ := by
    have hc := hrel.capacity
    have hlen : carry.var + 2 * l.var + 6 ≤ (splitTailPayload base carry [l]).length := by
      cases carry <;> cases l <;>
        simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
          NPComplete.SAT.Literal.var] <;> omega
    omega
  have htmp := writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg 1 carry.var
    (literalPolarity l) l.var l.var σw hrel.cur_j_pos hrel.tmp_j_pos
    hcpw hcvw hpolw hvarw hvarw (by omega) hpol01
    hrel.safety.writer_below.2.1
    ⟨hbelow.2.1, hbelow.2.2.1⟩ ⟨hbelow.2.1, hbelow.2.2.1⟩ hws hroom
  unfold splitTailEmitTerminalOneProgAt
  rw [eval_seq, eval_seq]
  simp only [eval_assign, Expr.eval]
  have hne : M + tmpJ ≠ remainingReg := by
    have h1 : start < M + curJ := by
      have hs := hrel.writer.safe
      omega
    have hrem := hrel.safety.writer_below.2.2.2
    have htmpJ := hrel.tmp_j_pos
    omega
  rw [writeReg_diff _ remainingReg 0 (M + tmpJ) hne]
  exact htmp

/-- Capacity slack of a two-literal terminal split-tail step. -/
lemma split_tail_emit_terminal_two_hsmall_of_rel_room
    {M curJ tmpJ start base : ℕ} {carry l1 l2 : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    start + pref.length + carry.var + l1.var + l2.var + 6 < M + curJ := by
  have hc := hrel.capacity
  have hlen : carry.var + l1.var + l2.var + 6 ≤
      (splitTailPayload base carry [l1, l2]).length := by
    cases carry <;> cases l1 <;> cases l2 <;>
      simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
        NPComplete.SAT.Literal.var] <;> omega
  omega

/-- Decoding the two literals leaves the writer state and carry registers intact and
    puts both literals and the done flag in the scratch registers. -/
lemma split_tail_emit_terminal_two_hsmall_of_rel_decode
    {M curJ tmpJ start base : ℕ} {carry l1 l2 : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τp υp : Store,
      τp = (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ ∧
      υp = (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval τp ∧
      WriterState υp M curJ start pref ∧ υp carryPolReg = 1 ∧ υp carryValReg = carry.var ∧
      υp pol2Reg = literalPolarity l1 ∧ υp var2Reg = l1.var ∧
      υp pol3Reg = literalPolarity l2 ∧ υp var3Reg = l2.var ∧ υp doneReg = 1 := by
  have hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++ tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  obtain ⟨hb1, hb2, hb3, hb7⟩ := hrel.safety.second.below
  obtain ⟨-, hb5, hb6, -⟩ := hrel.safety.third.below
  have hstartAddr := hrel.start_at_input
  obtain ⟨τp, υp, hτp, hυp, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg bound
      addr l1 l2 tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      hrel.safety.third.distinct.1 hrel.safety.third.distinct.2.1
      hrel.safety.third.distinct.2.2.2.1 hrel.safety.third.distinct.2.2.2.2.1
      hrel.safety.third.distinct.2.2.2.2.2
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      hbound1 hbound2 hrel.cursor hbits
  have htailσ : BitsFrom σ (addr + l1.var + 2) (encodeLiteral l2 ++ tail) := by
    obtain ⟨_, ht⟩ := bitsFrom_append σ addr (encodeLiteral l1)
      (encodeLiteral l2 ++ tail) (by simpa [List.append_assoc] using hbits)
    have hlen : (encodeLiteral l1).length = l1.var + 2 := by
      cases l1 <;> simp [encodeLiteral, encodeNat_length, NPComplete.SAT.Literal.var]
    rw [hlen] at ht
    exact ht
  have htailτ : BitsFrom τp (addr + l1.var + 2) (encodeLiteral l2 ++ tail) := fun k hk =>
    (hframe1 (addr + l1.var + 2 + k) (by omega) (by omega) (by omega) (by omega)).trans
      (htailσ k hk)
  obtain ⟨-, -, -, hdoneDec, -⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol3Reg var3Reg doneReg bound
      (addr + l1.var + 2) l2 tail τp
      hrel.safety.third.distinct.1 hrel.safety.third.distinct.2.1
      hrel.safety.third.distinct.2.2.1 hrel.safety.third.distinct.2.2.2.1
      hrel.safety.third.distinct.2.2.2.2.1 hrel.safety.third.distinct.2.2.2.2.2
      (by omega) (by omega) (by omega) (by omega) hbound2 hcur1 htailτ
  have hτstate : WriterState τp M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ τp cursorReg pol2Reg var2Reg doneReg
      hrel.writer hframe1 hrel.safety.second.nonzero.1 hrel.safety.second.nonzero.2.1
      hrel.safety.second.nonzero.2.2.1 hrel.safety.second.nonzero.2.2.2 hb1 hb2 hb3 hb7
  have hkeep : ∀ r, (r = carryPolReg ∨ r = carryValReg) → ∀ v, σ r = v → υp r = v := by
    intro r hr v hv
    have hw := hrel.safety.writer_parser r (by rcases hr with rfl | rfl <;> simp)
    exact (hframe2 r hw.1 hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2 hw.2.2.2.1).trans
      ((hframe1 r hw.1 hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.2.1).trans hv)
  refine ⟨τp, υp, hτp, hυp, ?_, hkeep _ (Or.inl rfl) _ hrel.carry_pol,
    hkeep _ (Or.inr rfl) _ hrel.carry_val, ?_, ?_, hpol2, hvar2, by rw [hυp]; exact hdoneDec⟩
  · exact writerState_transport_of_frame4 M curJ start pref τp υp cursorReg pol3Reg var3Reg
      doneReg hτstate hframe2 hrel.safety.third.nonzero.1 hrel.safety.third.nonzero.2.1
      hrel.safety.third.nonzero.2.2.1 hrel.safety.third.nonzero.2.2.2 hb1 hb5 hb6 hb7
  · exact (hframe2 pol2Reg hrel.safety.second.distinct.1.symm hrel.safety.cross.1
      hrel.safety.cross.2.1 hrel.safety.second.distinct.2.2.2.2.1).trans hpol1
  · exact (hframe2 var2Reg hrel.safety.second.distinct.2.1.symm hrel.safety.cross.2.2.1
      hrel.safety.cross.2.2.2 hrel.safety.second.distinct.2.2.2.2.2).trans hvar1

lemma splitTailEmitTerminalTwoProgAt_tmp_value
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ
        (M + tmpJ) = l2.var := by
  have hroom := split_tail_emit_terminal_two_hsmall_of_rel_room hrel
  obtain ⟨τ, υ, hτ, hυ, hυstate, hcarryPol, hcarryVal,
      hpol1, hvar1, hpol2, hvar2, _⟩ :=
    split_tail_emit_terminal_two_hsmall_of_rel_decode hbound1 hbound2 hrel
  have hpol01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpol02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have htmp := writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg 1 carry.var
    (literalPolarity l1) l1.var l2.var υ hrel.cur_j_pos hrel.tmp_j_pos
    hcarryPol hcarryVal hpol1 hvar1 hvar2 (by simp) hpol01
    hrel.safety.writer_below.2.1
    ⟨hrel.safety.second.below.2.1, hrel.safety.second.below.2.2.1⟩
    ⟨hrel.safety.third.below.2.1, hrel.safety.third.below.2.2.1⟩ hυstate hroom
  have heqAt := splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound σ hb hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  rw [heqAt]
  unfold splitTailEmitTerminalTwoProg
  rw [eval_seq, eval_seq, eval_seq, ← hτ, ← hυ]
  change (Program.assign remainingReg (.const 0)).eval
    ((writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg).eval υ)
      (M + tmpJ) = l2.var
  have hne : M + tmpJ ≠ remainingReg := by
    have hs := hrel.writer.safe
    have hrem := hrel.safety.writer_below.2.2.2
    have htmpJ := hrel.tmp_j_pos
    omega
  rw [eval_assign, Expr.eval, writeReg_diff _ remainingReg _ _ hne]
  exact htmp

lemma uniform_split_tail_emit_prog_at_tmp_bound_of_rel
    (N K : ℕ) (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N) (hbase : base + ls.length ≤ K)
    (htmp : σ (uniformMNat N + uctTmpJ) ≤ K)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry
      ls pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N) (n : ℕ) (hNK : N ≤ K) :
    (loopEval
      (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) n σ)
      (uniformMNat N + uctTmpJ) ≤ K := by
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hstate⟩ :=
    splitTailEmitProgAt_tmp_bound_of_rel K (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
      uctSavedBoundReg N base carry ls pref tail addr σ hbound hbase htmp hrel hb
      uniform_emit_bound_reg_ok.split hNK
      (fun base carry l pref tail addr τ hbound hrel hb =>
        splitTailEmitTerminalOneProgAt_tmp_value
          (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
          (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
          (varReg := uctVarReg) (doneReg := uctDoneReg) (remainingReg := uctRemainingReg)
          (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg)
          (var3Reg := uctVar3Reg) (carryPolReg := uctCarryPolReg)
          (carryValReg := uctCarryValReg) (posPolReg := uctPosPolReg)
          (freshReg := uctFreshReg) (boundReg := uctSavedBoundReg) (bound := N)
          base carry l pref tail addr τ hbound hrel hb uniform_emit_bound_reg_ok.split)
      (fun base carry l1 l2 pref tail addr τ hbound1 hbound2 hrel hb =>
        splitTailEmitTerminalTwoProgAt_tmp_value
          (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
          (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
          (varReg := uctVarReg) (doneReg := uctDoneReg) (remainingReg := uctRemainingReg)
          (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg)
          (var3Reg := uctVar3Reg) (carryPolReg := uctCarryPolReg)
          (carryValReg := uctCarryValReg) (posPolReg := uctPosPolReg)
          (freshReg := uctFreshReg) (boundReg := uctSavedBoundReg) (bound := N)
          base carry l1 l2 pref tail addr τ hbound1 hbound2 hrel hb uniform_emit_bound_reg_ok.split)
      n
  rw [← hτ]
  rcases hstate with hrel' | hdone'
  · exact hrel'.2.2.2.1
  · exact hdone'.2.2

lemma uniform_splitTailEmitProgAt_tmp_bound_of_rel_exit
    (N K : ℕ) (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N) (hbase : base + ls.length ≤ K)
    (htmp : σ (uniformMNat N + uctTmpJ) ≤ K)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry
      ls pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N) (hne : ls ≠ []) (hNK : N ≤ K) :
    (splitTailEmitProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
      uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
      (uniformMNat N + uctTmpJ) ≤ K := by
  have hloop := uniform_split_tail_emit_prog_at_tmp_bound_of_rel N K base carry ls pref tail addr σ
    hbound hbase htmp hrel hb (ls.length + 1) hNK
  have hlen : 0 < ls.length := by
    cases ls with
    | nil => exact False.elim (hne rfl)
    | cons _ _ => simp
  rw [splitTailEmitProgAt_pos_eval uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg ls.length σ hrel.remaining hlen]
  exact hloop

lemma splitTailEmitTerminalOneProgAt_bound_frame_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ : Store) (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ boundReg = bound := by
  have hlow := splitTailEmitTerminalOneProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l pref tail addr σ hbound hrel hok.below
    ⟨hok.ne_cursor, hok.ne_pol2, hok.ne_var2, hok.ne_done, hok.ne_carry_pol,
      hok.ne_carry_val, hok.ne_remaining⟩
  have heq := splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  calc
    _ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ boundReg := by
        rw [heq]
    _ = σ boundReg := hlow
    _ = bound := hb

lemma splitTailEmitTerminalTwoProgAt_bound_frame_of_rel
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ : Store) (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ
        boundReg = bound := by
  have hlow := splitTailEmitTerminalTwoProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel
    hok.below ⟨hok.ne_cursor, hok.ne_pol2, hok.ne_var2, hok.ne_pol3, hok.ne_var3,
      hok.ne_done, hok.ne_carry_pol, hok.ne_carry_val, hok.ne_remaining⟩
  have heq := splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound σ hb hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  calc
    _ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
        boundReg := by rw [heq]
    _ = σ boundReg := hlow
    _ = bound := hb

lemma split_tail_emit_terminal_hsmall_of_changed
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg lengthReg
      outerReg negPolReg : ℕ)
    (Changed : ℕ → Prop) (σ τ : Store)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hchanged : ∀ {r}, Changed r → τ r ≤ K)
    (hframe : ∀ r, r < start → ¬ Changed r → τ r = σ r) :
    ∀ r, r < start →
      LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r ≤ K := by
  intro r hr _
  by_cases hc : Changed r
  · exact hchanged hc
  · rw [hframe r hr hc]
    exact hraw.store r

/-- Capacity slack of a one-literal terminal split-tail step. -/
lemma split_tail_emit_terminal_one_hsmall_of_rel_room
    {M curJ tmpJ start base : ℕ} {carry l : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    start + pref.length + carry.var + l.var + l.var + 6 < M + curJ := by
  have hc := hrel.capacity
  have hlen : carry.var + 2 * l.var + 6 ≤ (splitTailPayload base carry [l]).length := by
    cases carry <;> cases l <;>
      simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
        NPComplete.SAT.Literal.var] <;> omega
  omega

/-- Decoding the literal leaves the writer state and carry registers intact and puts the
    literal and the done flag in the scratch registers. -/
lemma split_tail_emit_terminal_one_hsmall_of_rel_decode
    {M curJ tmpJ start base : ℕ} {carry l : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τp : Store,
      τp = (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ ∧
      WriterState τp M curJ start pref ∧ τp carryPolReg = 1 ∧ τp carryValReg = carry.var ∧
      τp pol2Reg = literalPolarity l ∧ τp var2Reg = l.var ∧ τp doneReg = 1 := by
  have hbits : BitsFrom σ addr (encodeLiteral l ++ tail) := by
    simpa [splitTailInputBits] using hrel.input
  obtain ⟨hb1, hb2, hb3, hb7⟩ := hrel.safety.second.below
  have hstartAddr := hrel.start_at_input
  obtain ⟨_, hpol, hvar, hdone, hframe⟩ :=
    decodeLiteralValueProgram_correct cursorReg pol2Reg var2Reg doneReg bound addr l tail σ
      hrel.safety.second.distinct.1 hrel.safety.second.distinct.2.1
      hrel.safety.second.distinct.2.2.1 hrel.safety.second.distinct.2.2.2.1
      hrel.safety.second.distinct.2.2.2.2.1 hrel.safety.second.distinct.2.2.2.2.2
      (by omega) (by omega) (by omega) (by omega) hbound hrel.cursor hbits
  have hkeep : ∀ r, (r = carryPolReg ∨ r = carryValReg) → ∀ v, σ r = v →
      (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ r = v := by
    intro r hr v hv
    have hw := hrel.safety.writer_parser r (by rcases hr with rfl | rfl <;> simp)
    exact (hframe r hw.1 hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.2.1).trans hv
  refine ⟨_, rfl, ?_, hkeep _ (Or.inl rfl) _ hrel.carry_pol,
    hkeep _ (Or.inr rfl) _ hrel.carry_val, ?_, hvar, hdone⟩
  · exact writerState_transport_of_frame4 M curJ start pref σ _ cursorReg pol2Reg var2Reg doneReg
      hrel.writer hframe hrel.safety.second.nonzero.1 hrel.safety.second.nonzero.2.1
      hrel.safety.second.nonzero.2.2.1 hrel.safety.second.nonzero.2.2.2 hb1 hb2 hb3 hb7
  · cases l <;> simpa [literalPolarity] using hpol

/-- The linking-triple writer leaves every parser scratch register and carry register of the
    one-literal terminal step unchanged. -/
lemma split_tail_emit_terminal_one_hsmall_of_rel_writer_frame
    {M curJ tmpJ start base : ℕ} {carry l : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ τp : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hτstate : WriterState τp M curJ start pref)
    (hcp : τp carryPolReg = 1) (hcv : τp carryValReg = carry.var)
    (hp : τp pol2Reg = literalPolarity l) (hv : τp var2Reg = l.var) :
    ∀ r, r = pol2Reg ∨ r = var2Reg ∨ r = doneReg ∨ r = carryPolReg ∨ r = carryValReg →
      (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
        pol2Reg var2Reg).eval τp r = τp r := by
  have hroom := split_tail_emit_terminal_one_hsmall_of_rel_room hrel
  obtain ⟨-, hb2, hb3, hb7⟩ := hrel.safety.second.below
  intro r hr
  refine writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg
    1 carry.var (literalPolarity l) l.var (literalPolarity l) l.var τp
    hrel.cur_j_pos hrel.tmp_j_pos hcp hcv hp hv hp hv
    (Or.inr rfl) (by cases l <;> simp [literalPolarity])
    (by cases l <;> simp [literalPolarity])
    hrel.safety.writer_below.2.1 ⟨hb2, hb3⟩ ⟨hb2, hb3⟩
    hτstate hroom ?_
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [hb2, hb3, hb7, hrel.safety.writer_below.1, hrel.safety.writer_below.2.1]

/-- The final register values of the one-literal terminal step: carry registers kept,
    scratch registers holding the decoded literal, and the remaining count cleared. -/
lemma split_tail_emit_terminal_one_hsmall_of_rel_post_values
    {M curJ tmpJ start base : ℕ} {carry l : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ τ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hτ : τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ) :
    τ carryPolReg = 1 ∧ τ carryValReg = carry.var ∧ τ remainingReg = 0 ∧
      τ pol2Reg = literalPolarity l ∧ τ var2Reg = l.var ∧ τ doneReg = 1 := by
  obtain ⟨τp, hτp, hτstate, hcp, hcv, hp, hv, hdone⟩ :=
    split_tail_emit_terminal_one_hsmall_of_rel_decode hbound hrel
  have hwf := split_tail_emit_terminal_one_hsmall_of_rel_writer_frame hrel hτstate hcp hcv hp hv
  have hrem := hrel.safety.writer_parser remainingReg (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨-, -, -, hcpr, -, -, hcvr, -, -, -⟩ := hrel.safety.writer_distinct
  have hτr : ∀ r, r ≠ remainingReg →
      (r = pol2Reg ∨ r = var2Reg ∨ r = doneReg ∨ r = carryPolReg ∨ r = carryValReg) →
        τ r = τp r := by
    intro r hr hmem
    rw [hτ]
    unfold splitTailEmitTerminalOneProg
    rw [eval_seq, eval_seq, ← hτp]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ remainingReg _ r hr]
    exact hwf r hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hτr _ hcpr (by simp)).trans hcp
  · exact (hτr _ hcvr (by simp)).trans hcv
  · rw [hτ]
    simp [splitTailEmitTerminalOneProg, eval_seq, eval_assign, Expr.eval, writeReg]
  · exact (hτr _ hrem.2.2.2.2.1.symm (by simp)).trans hp
  · exact (hτr _ hrem.2.2.2.2.2.1.symm (by simp)).trans hv
  · exact (hτr _ hrem.2.2.2.1.symm (by simp)).trans hdone

lemma split_tail_emit_terminal_one_hsmall_of_rel
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound lengthReg
      outerReg negPolReg : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ τ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hτ : τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hcursor1 : τ cursorReg + 1 + τ boundReg ≤ K) :
    ∀ r, r < start →
      LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r ≤ K := by
  have hK1 : 1 ≤ K := by omega
  have hboundK : bound ≤ K := by
    rw [← hb]
    exact hraw.store boundReg
  have hcarryK : carry.var ≤ K := by
    rw [← hrel.carry_val]
    exact hraw.store carryValReg
  obtain ⟨hcp, hcv, hrem, hp, hv, hdone⟩ :=
    split_tail_emit_terminal_one_hsmall_of_rel_post_values hbound hrel hτ
  have hpolK : literalPolarity l ≤ K := by
    cases l <;> simp [literalPolarity, hK1]
  have hchanged : ∀ {r}, r = cursorReg ∨ r = pol2Reg ∨ r = var2Reg ∨ r = doneReg ∨
      r = carryPolReg ∨ r = carryValReg ∨ r = remainingReg → τ r ≤ K := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  exact split_tail_emit_terminal_hsmall_of_changed
    (K := K) (B := B) (M := M) (curJ := curJ) (tmpJ := tmpJ) (start := start)
    (cursorReg := cursorReg) (polReg := polReg) (varReg := varReg)
    (doneReg := doneReg) (remainingReg := remainingReg) (pol2Reg := pol2Reg)
    (var2Reg := var2Reg) (pol3Reg := pol3Reg) (var3Reg := var3Reg)
    (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (boundReg := boundReg)
    (lengthReg := lengthReg) (outerReg := outerReg) (negPolReg := negPolReg)
    (Changed := fun r => r = cursorReg ∨ r = pol2Reg ∨ r = var2Reg ∨ r = doneReg ∨
      r = carryPolReg ∨ r = carryValReg ∨ r = remainingReg)
    (σ := σ) (τ := τ) hraw hchanged (by
      intro r hr hc
      have hne : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ doneReg ∧
          r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ remainingReg := by
        simpa only [not_or] using hc
      rw [hτ]
      exact splitTailEmitTerminalOneProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
        varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg bound base carry l pref tail addr σ hbound hrel hr
        ⟨hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
          hne.2.2.2.2.2.1, hne.2.2.2.2.2.2⟩)


/-- The linking-triple writer leaves every parser scratch register and carry register of the
    two-literal terminal step unchanged. -/
lemma split_tail_emit_terminal_two_hsmall_of_rel_writer_frame
    {M curJ tmpJ start base : ℕ} {carry l1 l2 : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ υp : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hυstate : WriterState υp M curJ start pref)
    (hcp : υp carryPolReg = 1) (hcv : υp carryValReg = carry.var)
    (hp1 : υp pol2Reg = literalPolarity l1) (hv1 : υp var2Reg = l1.var)
    (hp2 : υp pol3Reg = literalPolarity l2) (hv2 : υp var3Reg = l2.var) :
    ∀ r, r = pol2Reg ∨ r = var2Reg ∨ r = pol3Reg ∨ r = var3Reg ∨
      r = doneReg ∨ r = carryPolReg ∨ r = carryValReg →
      (writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
        pol3Reg var3Reg).eval υp r = υp r := by
  have hroom := split_tail_emit_terminal_two_hsmall_of_rel_room hrel
  obtain ⟨-, hb2, hb3, hb7⟩ := hrel.safety.second.below
  obtain ⟨-, hb5, hb6, -⟩ := hrel.safety.third.below
  intro r hr
  refine writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg
    1 carry.var (literalPolarity l1) l1.var (literalPolarity l2) l2.var υp
    hrel.cur_j_pos hrel.tmp_j_pos hcp hcv hp1 hv1 hp2 hv2
    (Or.inr rfl) (by cases l1 <;> simp [literalPolarity])
    (by cases l2 <;> simp [literalPolarity])
    hrel.safety.writer_below.2.1 ⟨hb2, hb3⟩ ⟨hb5, hb6⟩
    hυstate hroom ?_
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hb2, hb3, hb5, hb6, hb7, hrel.safety.writer_below.1, hrel.safety.writer_below.2.1]

/-- The final register values of the two-literal terminal step: carry registers kept,
    scratch registers holding the decoded literals, and the remaining count cleared. -/
lemma split_tail_emit_terminal_two_hsmall_of_rel_post_values
    {M curJ tmpJ start base : ℕ} {carry l1 l2 : NPComplete.SAT.Literal}
    {pref tail : Bits} {addr : ℕ} {σ τ : Store}
    {cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ}
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hτ : τ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound).eval σ) :
    τ carryPolReg = 1 ∧ τ carryValReg = carry.var ∧ τ remainingReg = 0 ∧
      τ pol2Reg = literalPolarity l1 ∧ τ var2Reg = l1.var ∧
      τ pol3Reg = literalPolarity l2 ∧ τ var3Reg = l2.var ∧ τ doneReg = 1 := by
  obtain ⟨τp, υp, hτp, hυp, hυstate, hcp, hcv, hp1, hv1, hp2, hv2, hdone⟩ :=
    split_tail_emit_terminal_two_hsmall_of_rel_decode hbound1 hbound2 hrel
  have hwf := split_tail_emit_terminal_two_hsmall_of_rel_writer_frame hrel hυstate hcp hcv
    hp1 hv1 hp2 hv2
  have hrem := hrel.safety.writer_parser remainingReg (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨-, -, -, hcpr, -, -, hcvr, -, -, -⟩ := hrel.safety.writer_distinct
  have hτr : ∀ r, r ≠ remainingReg →
      (r = pol2Reg ∨ r = var2Reg ∨ r = pol3Reg ∨ r = var3Reg ∨ r = doneReg ∨
        r = carryPolReg ∨ r = carryValReg) → τ r = υp r := by
    intro r hr hmem
    rw [hτ]
    unfold splitTailEmitTerminalTwoProg
    rw [eval_seq, eval_seq, eval_seq, ← hτp, ← hυp]
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ remainingReg _ r hr]
    exact hwf r hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hτr _ hcpr (by simp)).trans hcp
  · exact (hτr _ hcvr (by simp)).trans hcv
  · rw [hτ]
    simp [splitTailEmitTerminalTwoProg, eval_seq, eval_assign, Expr.eval, writeReg]
  · exact (hτr _ hrem.2.2.2.2.1.symm (by simp)).trans hp1
  · exact (hτr _ hrem.2.2.2.2.2.1.symm (by simp)).trans hv1
  · exact (hτr _ hrem.2.2.2.2.2.2.1.symm (by simp)).trans hp2
  · exact (hτr _ hrem.2.2.2.2.2.2.2.symm (by simp)).trans hv2
  · exact (hτr _ hrem.2.2.2.1.symm (by simp)).trans hdone

lemma split_tail_emit_terminal_two_hsmall_of_rel
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound lengthReg
      outerReg negPolReg : ℕ)
    (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ τ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hτ : τ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound).eval σ)
    (hcursor1 : τ cursorReg + 1 + τ boundReg ≤ K) :
    ∀ r, r < start →
      LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r ≤ K := by
  have hK1 : 1 ≤ K := by omega
  have hboundK : bound ≤ K := by
    rw [← hb]
    exact hraw.store boundReg
  have hcarryK : carry.var ≤ K := by
    rw [← hrel.carry_val]
    exact hraw.store carryValReg
  obtain ⟨hcp, hcv, hrem, hp1, hv1, hp2, hv2, hdone⟩ :=
    split_tail_emit_terminal_two_hsmall_of_rel_post_values hbound1 hbound2 hrel hτ
  have hpolK : ∀ l : NPComplete.SAT.Literal, literalPolarity l ≤ K := fun l => by
    cases l <;> simp [literalPolarity, hK1]
  have hl1 := hpolK l1
  have hl2 := hpolK l2
  have hchanged : ∀ {r}, r = cursorReg ∨ r = pol2Reg ∨ r = var2Reg ∨ r = pol3Reg ∨
      r = var3Reg ∨ r = doneReg ∨ r = carryPolReg ∨ r = carryValReg ∨
      r = remainingReg → τ r ≤ K := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  exact split_tail_emit_terminal_hsmall_of_changed
    (K := K) (B := B) (M := M) (curJ := curJ) (tmpJ := tmpJ) (start := start)
    (cursorReg := cursorReg) (polReg := polReg) (varReg := varReg)
    (doneReg := doneReg) (remainingReg := remainingReg) (pol2Reg := pol2Reg)
    (var2Reg := var2Reg) (pol3Reg := pol3Reg) (var3Reg := var3Reg)
    (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (boundReg := boundReg)
    (lengthReg := lengthReg) (outerReg := outerReg) (negPolReg := negPolReg)
    (Changed := fun r => r = cursorReg ∨ r = pol2Reg ∨ r = var2Reg ∨ r = pol3Reg ∨
      r = var3Reg ∨ r = doneReg ∨ r = carryPolReg ∨ r = carryValReg ∨
      r = remainingReg)
    (σ := σ) (τ := τ) hraw hchanged (by
      intro r hr hc
      have hne : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
          r ≠ var3Reg ∧ r ≠ doneReg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧
          r ≠ remainingReg := by
        simpa only [not_or] using hc
      rw [hτ]
      exact splitTailEmitTerminalTwoProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
        varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel hr
        ⟨hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
          hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1,
          hne.2.2.2.2.2.2.2.2⟩)


lemma splitTailEmitRel_one_to_done_raw_bounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound lengthReg
      outerReg negPolReg : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ τ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hτ : τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hcursor1 : τ cursorReg + 1 + τ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ
      cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ boundReg ≤ K) :
    SplitTailEmitDoneRawBounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound base carry [l] pref tail addr τ := by
  have hboundPost := splitTailEmitTerminalOneProgAt_bound_frame_of_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg carryPolReg
    carryValReg posPolReg freshReg boundReg bound base carry l pref tail addr σ hbound hrel
    hb hok
  have htmpAt := splitTailEmitTerminalOneProgAt_tmp_value M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg boundReg bound base carry l pref tail addr σ hbound hrel hb hok
  have hboundK : bound ≤ K := by
    rw [← hb]
    exact hraw.store boundReg
  have heqAt := splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  have htmpNonAt :
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ (M + tmpJ) = l.var := by
    rw [← heqAt]
    exact htmpAt
  have htmp : τ (M + tmpJ) ≤ K := by
    rw [hτ, htmpNonAt]
    omega
  have hsmallPost := split_tail_emit_terminal_one_hsmall_of_rel K B M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
    freshReg boundReg bound lengthReg outerReg negPolReg base carry l pref tail addr σ τ hbound hrel
    hb hraw hτ hcursor1
  have hframeLow : ∀ r, r < start →
      ¬ LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r = σ r := by
    intro r hr hnot
    have hneAll : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
        r ≠ var3Reg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ posPolReg ∧
        r ≠ freshReg ∧ r ≠ lengthReg ∧ r ≠ outerReg ∧ r ≠ negPolReg := by
      simpa only [LongClauseLowWriteSet, not_or] using hnot
    rcases hneAll with ⟨hrc, _, _, hrd, hrem, hrp2, hrv2, _, _, hcp, hcv, _, _, _, _, _⟩
    have hne : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ doneReg ∧
        r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ remainingReg := by
      exact ⟨hrc, hrp2, hrv2, hrd, hcp, hcv, hrem⟩
    rw [hτ]
    exact splitTailEmitTerminalOneProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
      varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l pref tail addr σ hbound hrel hr hne
  obtain ⟨τ', hτ', hdone⟩ := splitTailEmitRel_one_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l pref tail addr σ
    hbound hrel
  have hτeq : τ = τ' := hτ.trans hτ'.symm
  rw [← hτeq] at hdone
  have hafter : ∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r := by
    intro r hr hrc hrt
    have hr' : start + pref.length + carry.var + 2 * l.var + 6 ≤ r := by
      have hlen : carry.var + 2 * l.var + 6 ≤
          (splitTailPayload base carry [l]).length := by
        cases carry <;> cases l <;>
          simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
            NPComplete.SAT.Literal.var] <;> omega
      rw [hdone.done.writer.cursor] at hr
      simp [List.length_append] at hr ⊢
      omega
    rw [hτ]
    exact splitTailEmitTerminalOneProg_after_frame_of_rel M curJ tmpJ start cursorReg polReg
      varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l pref tail addr σ hbound hrel hr' hrc hrt
  have heqAt := splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  have hboundNonAt :
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ boundReg = bound := by
    rw [← heqAt]
    exact hboundPost
  have hboundPost' : τ boundReg = bound := by rw [hτ]; exact hboundNonAt
  have hK1 : 1 ≤ K := by omega
  have hcursor := SplitTailEmitDoneFrame.writer_cursor_le_of_raw K M curJ σ τ hraw hdone
  have hstore := storeValuesLe_of_long_clause_frames K M curJ tmpJ start σ τ
    (pref ++ splitTailPayload base carry [l]) cursorReg polReg varReg doneReg remainingReg pol2Reg
    var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg
    hK1 hraw.store hdone.done.writer hcursor htmp hframeLow hsmallPost hafter
  exact SplitTailEmitDoneFrame.to_raw_bounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound base carry [l] pref tail addr σ τ hraw hdone
    hboundPost' hstore hcursor1 hcursor2

lemma splitTailEmitRel_two_to_done_raw_bounds
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound lengthReg
      outerReg negPolReg : ℕ)
    (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ τ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hτ : τ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hcursor1 : τ cursorReg + 1 + τ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ
      cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval τ boundReg ≤ K) :
    SplitTailEmitDoneRawBounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound base carry [l1, l2] pref tail addr τ := by
  have hboundPost := splitTailEmitTerminalTwoProgAt_bound_frame_of_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg boundReg bound base carry l1 l2 pref tail addr σ hbound1
    hbound2 hrel hb hok
  have htmpAt := splitTailEmitTerminalTwoProgAt_tmp_value M curJ tmpJ start cursorReg polReg varReg
    doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel hb hok
  have hboundK : bound ≤ K := by
    rw [← hb]
    exact hraw.store boundReg
  have heqAt := splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound σ hb hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  have htmpNonAt :
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
        (M + tmpJ) = l2.var := by
    rw [← heqAt]
    exact htmpAt
  have htmp : τ (M + tmpJ) ≤ K := by
    rw [hτ, htmpNonAt]
    omega
  have hsmallPost := split_tail_emit_terminal_two_hsmall_of_rel K B M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
    freshReg boundReg bound lengthReg outerReg negPolReg base carry l1 l2 pref tail addr σ τ
    hbound1 hbound2 hrel hb hraw hτ hcursor1
  have hframeLow : ∀ r, r < start →
      ¬ LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg r →
      τ r = σ r := by
    intro r hr hnot
    have hneAll : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
        r ≠ var3Reg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ posPolReg ∧
        r ≠ freshReg ∧ r ≠ lengthReg ∧ r ≠ outerReg ∧ r ≠ negPolReg := by
      simpa only [LongClauseLowWriteSet, not_or] using hnot
    rcases hneAll with ⟨hrc, _, _, hrd, hrem, hrp2, hrv2, hrp3, hrv3,
      hcp, hcv, _, _, _, _, _⟩
    rw [hτ]
    exact splitTailEmitTerminalTwoProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
      varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel hr
      ⟨hrc, hrp2, hrv2, hrp3, hrv3, hrd, hcp, hcv, hrem⟩
  obtain ⟨τ', hτ', hdone⟩ := splitTailEmitRel_two_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2 pref tail addr σ
     hbound1 hbound2 hrel
  have hτeq : τ = τ' := hτ.trans hτ'.symm
  rw [← hτeq] at hdone
  have hafter : ∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r := by
    intro r hr hrc hrt
    have hr' : start + pref.length + carry.var + l1.var + l2.var + 6 ≤ r := by
      have hlen : carry.var + l1.var + l2.var + 6 ≤
          (splitTailPayload base carry [l1, l2]).length := by
        cases carry <;> cases l1 <;> cases l2 <;>
          simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
            NPComplete.SAT.Literal.var] <;> omega
      rw [hdone.done.writer.cursor] at hr
      simp [List.length_append] at hr ⊢
      omega
    rw [hτ]
    exact splitTailEmitTerminalTwoProg_after_frame_of_rel M curJ tmpJ start cursorReg polReg
      varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
      posPolReg freshReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2 hrel hr' hrc hrt
  have hboundNonAt :
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
        boundReg = bound := by
    rw [← heqAt]
    exact hboundPost
  have hboundPost' : τ boundReg = bound := by rw [hτ]; exact hboundNonAt
  have hK1 : 1 ≤ K := by omega
  have hcursor := SplitTailEmitDoneFrame.writer_cursor_le_of_raw K M curJ σ τ hraw hdone
  have hstore := storeValuesLe_of_long_clause_frames K M curJ tmpJ start σ τ
    (pref ++ splitTailPayload base carry [l1, l2]) cursorReg polReg varReg doneReg remainingReg pol2Reg
    var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg
    hK1 hraw.store hdone.done.writer hcursor htmp hframeLow hsmallPost hafter
  exact SplitTailEmitDoneFrame.to_raw_bounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound base carry [l1, l2] pref tail addr σ τ hraw hdone
    hboundPost' hstore hcursor1 hcursor2

lemma splitTailEmitRel_one_to_done_raw_bounds_of_window
    (K B M curJ tmpJ inputEnd baseLimit start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg
      bound lengthReg outerReg negPolReg : ℕ)
    (base : ℕ) (carry l : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base [l] tail addr)
    (hend : inputEnd + 2 + 2 * bound ≤ K) :
    SplitTailEmitDoneRawBounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound base carry [l] pref tail addr
      ((splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ) := by
  have hboundAt := splitTailEmitTerminalOneProgAt_bound_frame_of_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg carryPolReg carryValReg
    posPolReg freshReg boundReg bound base carry l pref tail addr σ hbound hrel hb hok
  have heqAt := splitTailEmitTerminalOneProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  have hboundPost :
      (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ boundReg = bound := by
    rw [← heqAt]
    exact hboundAt
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_one_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l pref tail addr σ
    hbound hrel
  have hcursor : τ cursorReg = addr + (splitTailInputBits [l] []).length := hdone.done.cursor
  have hwinPost : SplitTailEmitWindow inputEnd baseLimit base [] tail
      (addr + (splitTailInputBits [l] []).length) := by
    constructor
    · have hleft := hwin.1
      simp [splitTailInputBits, List.length_append] at hleft ⊢
      omega
    · have hbase := hwin.2
      simp at hbase ⊢
      omega
  have hτbound : τ boundReg = bound := by rw [hτ]; exact hboundPost
  have hcursors := split_tail_emit_cursor_budgets_of_window K inputEnd baseLimit base [] tail
    (addr + (splitTailInputBits [l] []).length) τ
    cursorReg pol2Reg var2Reg doneReg boundReg hrel.safety.second.distinct.1
    hrel.safety.second.distinct.2.1 hrel.safety.second.distinct.2.2.1 hok.ne_cursor
    hok.ne_pol2 hok.ne_var2 hok.ne_done hwinPost hcursor (by rw [hτbound]; exact hend)
  have hrawDone := splitTailEmitRel_one_to_done_raw_bounds
    (K := K) (B := B) (M := M) (curJ := curJ) (tmpJ := tmpJ) (start := start)
    (cursorReg := cursorReg) (polReg := polReg) (varReg := varReg) (doneReg := doneReg)
    (remainingReg := remainingReg) (pol2Reg := pol2Reg) (var2Reg := var2Reg)
    (pol3Reg := pol3Reg) (var3Reg := var3Reg) (carryPolReg := carryPolReg)
    (carryValReg := carryValReg) (posPolReg := posPolReg) (freshReg := freshReg)
    (boundReg := boundReg) (bound := bound) (lengthReg := lengthReg) (outerReg := outerReg)
    (negPolReg := negPolReg) (base := base) (carry := carry) (l := l) (pref := pref)
    (tail := tail) (addr := addr) (σ := σ) (τ := τ)
    hbound hrel hb hok hraw hτ hcursors.1 hcursors.2
  simpa [hτ] using hrawDone

lemma splitTailEmitRel_two_to_done_raw_bounds_of_window
    (K B M curJ tmpJ inputEnd baseLimit start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg
      bound lengthReg outerReg negPolReg : ℕ)
    (base : ℕ) (carry l1 l2 : NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l1, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base [l1, l2] tail addr)
    (hend : inputEnd + 2 + 2 * bound ≤ K) :
    SplitTailEmitDoneRawBounds K B M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg bound base carry [l1, l2] pref tail addr
      ((splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ) := by
  have hboundAt := splitTailEmitTerminalTwoProgAt_bound_frame_of_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg boundReg bound base carry l1 l2 pref tail addr σ hbound1 hbound2
    hrel hb hok
  have heqAt := splitTailEmitTerminalTwoProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg bound σ hb hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  have hboundPost :
      (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
        boundReg = bound := by
    rw [← heqAt]
    exact hboundAt
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_two_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2 pref tail addr σ
    hbound1 hbound2 hrel
  have hcursor : τ cursorReg = addr + (splitTailInputBits [l1, l2] []).length := hdone.done.cursor
  have hwinPost : SplitTailEmitWindow inputEnd baseLimit base [] tail
      (addr + (splitTailInputBits [l1, l2] []).length) := by
    constructor
    · have hleft := hwin.1
      simp [splitTailInputBits, List.length_append] at hleft ⊢
      omega
    · have hbase := hwin.2
      simp at hbase ⊢
      omega
  have hτbound : τ boundReg = bound := by rw [hτ]; exact hboundPost
  have hcursors := split_tail_emit_cursor_budgets_of_window K inputEnd baseLimit base [] tail
    (addr + (splitTailInputBits [l1, l2] []).length) τ
    cursorReg pol2Reg var2Reg doneReg boundReg hrel.safety.second.distinct.1
    hrel.safety.second.distinct.2.1 hrel.safety.second.distinct.2.2.1 hok.ne_cursor
    hok.ne_pol2 hok.ne_var2 hok.ne_done hwinPost hcursor (by rw [hτbound]; exact hend)
  have hrawDone := splitTailEmitRel_two_to_done_raw_bounds
    (K := K) (B := B) (M := M) (curJ := curJ) (tmpJ := tmpJ) (start := start)
    (cursorReg := cursorReg) (polReg := polReg) (varReg := varReg) (doneReg := doneReg)
    (remainingReg := remainingReg) (pol2Reg := pol2Reg) (var2Reg := var2Reg)
    (pol3Reg := pol3Reg) (var3Reg := var3Reg) (carryPolReg := carryPolReg)
    (carryValReg := carryValReg) (posPolReg := posPolReg) (freshReg := freshReg)
    (boundReg := boundReg) (bound := bound) (lengthReg := lengthReg) (outerReg := outerReg)
    (negPolReg := negPolReg) (base := base) (carry := carry) (l1 := l1) (l2 := l2)
    (pref := pref) (tail := tail) (addr := addr) (σ := σ) (τ := τ)
    hbound1 hbound2 hrel hb hok hraw hτ hcursors.1 hcursors.2
  simpa [hτ] using hrawDone

end NPComplete.CookLevin

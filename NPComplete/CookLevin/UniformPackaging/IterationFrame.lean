module

public import NPComplete.CookLevin.UniformPackaging.ClauseFrame

/-!
# Frame invariants for emitter iterations

Composing an iteration body requires unrelated cells to remain unchanged across
its branches and setup stages. This module transports the semantic emitter
relation into those frame facts, including the long-clause path used by the loop.
It also derives `ProgramBoundedIn` for the outer loop using outer accounting and a
body bound.
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

lemma uniform_emit_prep_state_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    ∃ σr σdec,
      σr = uniformEmitScratchResetProg.eval σ ∧
      σdec = (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg
        uctSavedBoundReg).eval σr ∧
      EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
        uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
        ((cs.map encodeClause).flatten ++ tail) pref σr σdec := by
  let σr := uniformEmitScratchResetProg.eval σ
  let σdec := (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg
    uctSavedBoundReg).eval σr
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hbr : σr uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  have hdecEq : σdec =
      (decodeNatProgram uctCursorReg uctLengthReg uctDoneReg N).eval σr := by
    simpa [σdec] using decodeNatProgramAt_eq uctCursorReg uctLengthReg uctDoneReg
      uctSavedBoundReg N σr hbr
  have hhead := cnfEmitRel_head_input (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
    uctCarryValReg uctFreshReg uctOuterReg N N base c cs tail pref addr σr hrelr
  have hroom : uniformStartNat + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c.lits).1).length + 2 <
      uniformMNat N + uctCurJ := by
    have hc := hrelr.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
      ((cs.map encodeClause).flatten ++ tail) pref σr σdec := by
    apply emitClausePrepState_of_pre_eq (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg uctFreshReg
      uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
      ((cs.map encodeClause).flatten ++ tail) pref σr σdec hdecEq uniform_cur_j_bounds.1
      uniform_cur_j_bounds.2 (hrelr.clause_bound c (by simp)) hrelr.start_at_input hhead
      hrelr.cursor hrelr.length_zero hrelr.done_zero hrelr.outer hrelr.fresh hrelr.pos hrelr.neg
      hrelr.input_above hrelr.writer hroom hrelr.safety
  exact ⟨σr, σdec, rfl, rfl, hprep⟩

/-- Room bounds of the long clause head, derived from the total payload capacity. -/
lemma uniformEmitIterCoreBody_frame_of_long_room
    (N : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref : Bits) (base : ℕ)
    (h : uniformStartNat + pref.length +
      (encodeThreeClausesPayload
        (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length + 2 <
      uniformMNat N + uctCurJ) :
    uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ ∧
    uniformStartNat +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base)
        (l3 :: l4 :: rest)).length + 2 < uniformMNat N + uctCurJ := by
  refine ⟨?_, ?_⟩
  · have hlenPayload : l1.var + l2.var + base + 6 ≤
        (encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length + 2 := by
      cases l1 <;> cases l2 <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral,
          NPComplete.BitEncoding.encodeNat_length,
          NPComplete.SAT.Literal.var, List.length_append] <;> omega
    omega
  · rw [← split_tail_emit_long_clause_payload] at h
    simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

/-- The long-branch preparation block leaves every register at or above the
parser start unchanged. -/
lemma uniformEmitIterCoreBody_frame_of_long_prep_frame
    (hsafe : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (σdec : Store) (r : ℕ) (hr : uniformStartNat ≤ r) :
    ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
      (Program.seq (.assign uctCarryPolReg (.const 1))
        (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (Program.seq (.assign uctPosPolReg (.const 0)) (.skip))))).eval σdec) r =
      σdec r :=
  emit_clause_long_prep_frame uctLengthReg uctRemainingReg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg r σdec
    (by have hs := hsafe.writer_below.2.2.2.2; omega)
    (by have hs := hsafe.writer_below.1; omega)
    (by have hs := hsafe.writer_below.2.1; omega)
    (by have hs := hsafe.writer_below.2.2.1; omega)

/-- State facts of the long-branch preparation block executed on the decoded store. -/
lemma uniformEmitIterCoreBody_frame_of_long_prep_state
    (N : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs) tail pref addr σr)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs).length addr
      (l1 :: l2 :: l3 :: l4 :: rest) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec) :
    ∃ σprep : Store,
      σprep = (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0)) (.skip))))).eval σdec ∧
      BitsFrom σprep (addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest)
          ((cs.map encodeClause).flatten ++ tail)) ∧
      WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref ∧
      σprep uctPosPolReg = 0 ∧ σprep uctFreshReg = base ∧
      σprep uctRemainingReg = (l1 :: l2 :: l3 :: l4 :: rest).length ∧
      σprep uctCursorReg = addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1 ∧
      ∀ r, uniformStartNat ≤ r → σprep r = σr r := by
  have hsafe := hrelr.long_safety.to_split_tail_safety
  have hwd := hsafe.writer_distinct
  have hstartInput : uniformStartNat ≤
      addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1 := by
    simpa using hprep.start_at_input
  have hvals := cnf_emit_long_prep_prog_values
    uctLengthReg uctRemainingReg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg σdec base
    (l1 :: l2 :: l3 :: l4 :: rest).length hprep.length hprep.fresh_value
    hwd.2.2.2.1 hwd.1.symm hwd.2.2.2.2.1.symm
    hwd.2.2.2.2.2.2.1.symm hwd.2.2.2.2.2.2.2.2.1.symm
    hwd.2.1 hwd.2.2.1.symm hwd.2.2.2.2.2.2.2.2.2
  have hframe := uniformEmitIterCoreBody_frame_of_long_prep_frame hsafe σdec
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply bitsFrom_of_eq_on (hb := by simpa [splitTailInputBits] using hprep.input)
    intro i hi
    exact hframe _ (by omega)
  · exact emit_clause_long_prep_writer
      (uniformMNat N) uctCurJ uniformStartNat uctRemainingReg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctLengthReg uctFreshReg
      pref σdec hprep.writer hsafe hrelr.safety.pos_nonzero
  · simpa using hvals.2.2.2
  · have hf := emit_clause_long_prep_frame
      uctLengthReg uctRemainingReg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg uctFreshReg σdec
      hwd.2.2.2.2.2.2.2.2.2
      hwd.2.2.1.symm hwd.2.2.2.2.2.1.symm
      hwd.2.2.2.2.2.2.2.1.symm
    exact hf.trans hprep.fresh_value
  · simpa using hvals.1
  · have hf := emit_clause_long_prep_frame
      uctLengthReg uctRemainingReg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg uctCursorReg σdec
      (Ne.symm (hsafe.writer_parser uctRemainingReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser uctCarryPolReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser uctCarryValReg (by simp)).1)
      (Ne.symm (hsafe.writer_parser uctPosPolReg (by simp)).1)
    exact hf.trans hprep.cursor
  · intro r hr
    exact (hframe r hr).trans (hprep.frame r
      (by have hs := hprep.safety.cursor_below; omega)
      (by have hs := hprep.safety.length_below; omega)
      (by have hs := hprep.safety.done_below; omega))

/-- The split-tail run of the long branch, started from the preparation state,
leaves every register at or above the final output cursor unchanged. -/
lemma uniformEmitIterCoreBody_frame_of_long_split
    (N : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs) tail pref addr σr)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs).length addr
      (l1 :: l2 :: l3 :: l4 :: rest) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length ≤ r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    ∃ σprep τlong : Store,
      σprep = (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0)) (.skip))))).eval σdec ∧
      τlong = (splitTailEmitLongClauseProg uctCurJ uctTmpJ uctCursorReg
        uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
        uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
        uctPosPolReg uctFreshReg N N).eval σprep ∧
      τlong r = σr r := by
  have hbound1 : l1.var + 1 ≤ N :=
    hrelr.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause)
      (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ N :=
    hrelr.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause)
      (by simp) l2 (by simp)
  have hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ N := by
    intro l hl
    exact hrelr.literal_bound (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause)
      (by simp) l (by simp [hl])
  have hls : (l3 :: l4 :: rest).length ≤ N := by
    have h := hrelr.clause_bound
      (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) (by simp)
    simp only [List.length_cons] at h ⊢
    omega
  have hroom := uniformEmitIterCoreBody_frame_of_long_room N l1 l2 l3 l4 rest pref base
    hprep.room
  obtain ⟨σprep, hσprep, hinput, hwriter, hpos, hfresh, hrem, hcursor, hframe⟩ :=
    uniformEmitIterCoreBody_frame_of_long_prep_state N l1 l2 l3 l4 rest cs tail pref
      addr base σr σdec hrelr hprep
  obtain ⟨τlong, base', carry', ls', pref', addr', hlong, hdone,
    hbase', hpayload', hcursor', hafterLong⟩ :=
    splitTail_emit_long_clause_eval_end_to_end_after_frame
      (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
      (start := uniformStartNat) (cursorReg := uctCursorReg)
      (polReg := uctPolReg) (varReg := uctVarReg) (doneReg := uctDoneReg)
      (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg)
      (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg)
      (carryPolReg := uctCarryPolReg) (carryValReg := uctCarryValReg)
      (posPolReg := uctPosPolReg) (freshReg := uctFreshReg)
      (bound := N) (tailBound := N) (base := base) (l1 := l1) (l2 := l2)
      (l3 := l3) (l4 := l4) (rest := rest) (pref := pref)
      (tail := (cs.map encodeClause).flatten ++ tail)
      (addr := addr + (l1 :: l2 :: l3 :: l4 :: rest).length + 1)
      (σ := σprep)
      hbound1 hbound2 hboundTail hls hroom.1 hroom.2 hinput
      hprep.cur_j_pos hprep.tmp_j_pos hprep.input_above hprep.start_at_input
      hwriter hpos hfresh hrem hcursor hrelr.long_safety.to_split_tail_safety
  have hcursorLong : τlong (uniformMNat N + uctCurJ) =
      uniformStartNat +
        (pref ++ encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length := by
    rw [hdone.done.writer.cursor, hpayload']
    simp [List.append_assoc, split_tail_emit_long_clause_payload,
      List.length_append]
  have hpostLong : τlong (uniformMNat N + uctCurJ) ≤ r := by
    rw [hcursorLong]
    exact hpostCursor
  refine ⟨σprep, τlong, hσprep, hlong, ?_⟩
  exact (hafterLong r hpostLong hrc hrt).trans
    (hframe r (le_trans (Nat.le_add_right _ _) hpostCursor))

/-- The clause program on a long head clause leaves register `r` unchanged once
the split-tail run is known to preserve it. -/
lemma uniformEmitIterCoreBody_frame_of_long_program
    (N : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec σprep τlong : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs).length addr
      (l1 :: l2 :: l3 :: l4 :: rest) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hr : uniformStartNat ≤ r)
    (hσprep : σprep = (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0)) (.skip))))).eval σdec)
    (hlong : τlong = (splitTailEmitLongClauseProg uctCurJ uctTmpJ uctCursorReg
        uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
        uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
        uctPosPolReg uctFreshReg N N).eval σprep)
    (hτ : τlong r = σr r) :
    (emitClauseProgram uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg N N).eval σr r = σr r := by
  have hcommit : (emitClauseCommitProg uctOuterReg).eval τlong r = τlong r := by
    dsimp [emitClauseCommitProg]
    simp only [eval_assign, Expr.eval]
    exact writeReg_diff _ uctOuterReg _ r (by
      have hs := hprep.safety.outer_below
      omega)
  have hlenGe : 4 ≤ σdec uctLengthReg := by
    rw [hprep.length]
    simp
  have hdispatch : (emitClauseDispatchProg uctCurJ uctTmpJ uctCursorReg uctPolReg
        uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
        uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N).eval σdec =
      (emitClauseCommitProg uctOuterReg).eval τlong := by
    rw [emitClauseDispatchProg_long_eval uctCurJ uctTmpJ
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
      uctFreshReg uctOuterReg N N σdec hlenGe, hlong, hσprep]
    simp [eval_seq]
  rw [emitClauseProgram, eval_seq, hprep.decoded.symm, hdispatch]
  exact hcommit.trans hτ

lemma uniformEmitIterCoreBody_frame_of_long
    (N : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs).length addr
      (l1 :: l2 :: l3 :: l4 :: rest) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  obtain ⟨σprep, τlong, hσprep, hlong, hτ⟩ :=
    uniformEmitIterCoreBody_frame_of_long_split N l1 l2 l3 l4 rest cs tail pref addr
      base r σr σdec hrelr hprep hpostCursor hrc hrt
  have hprog := uniformEmitIterCoreBody_frame_of_long_program N l1 l2 l3 l4 rest cs
    tail pref addr base r σr σdec σprep τlong hprep
    (le_trans (Nat.le_add_right _ _) hpostCursor) hσprep hlong hτ
  have hAt := emitClauseIterProgramAt_eval_of_rel_long
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
    uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg N N base
    l1 l2 l3 l4 rest cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  unfold uniformEmitIterCoreBody
  rw [hAt, emitClauseIterProgram, eval_seq]
  exact (hresetFrame _).trans hprog

/-- The iteration core body does not write above the output cursor when the head clause is empty. -/
lemma uniformEmitIterBody_after_frame_of_rel_nil
    (N : ℕ) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨[]⟩ : Clause) :: cs).length addr
      ([]) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base ([])).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  have hroom : uniformStartNat + pref.length + 6 * (base + 2) <
      uniformMNat N + uctCurJ := by
    have h := hprep.room
    simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
      NPComplete.BitEncoding.encodeNat_length,
      List.length_append] at h ⊢
    omega
  have hpayload :
      (encodeThreeClausesPayload (clauseToThree base []).1).length = 6 * (base + 2) := by
    simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
      NPComplete.BitEncoding.encodeNat_length, List.length_append]
    omega
  have hrw : uniformStartNat + pref.length + 6 * (base + 2) ≤ r := by
    simp only [List.length_append, hpayload] at hpostCursor ⊢
    omega
  have hAt := emitClauseIterProgramAt_eval_of_rel_nil
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr
  have hprog := emitClauseProgram_nil_frame_after_of_prep
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
    (varReg := uctVarReg) (doneReg := uctDoneReg) (lengthReg := uctLengthReg)
    (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg)
    (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg)
    (negPolReg := uctNegPolReg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (freshReg := uctFreshReg)
    (outerReg := uctOuterReg) (bound := N) (tailBound := N)
    (base := base) (outer := List.length (⟨[]⟩ :: cs)) (addr := addr)
    (rest := (cs.map encodeClause).flatten ++ tail) (pref := pref)
    (σ := σr) (σ0 := σdec) (by simpa using hprep) hroom r hrw hrc hrt
  unfold uniformEmitIterCoreBody
  rw [hAt, emitClauseIterProgram, eval_seq]
  exact (hresetFrame _).trans hprog

/-- The iteration core body does not write above the output cursor when the head clause is a unit clause. -/
lemma uniformEmitIterBody_after_frame_of_rel_one
    (N : ℕ) (l1 : NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l1]⟩ : Clause) :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨[l1]⟩ : Clause) :: cs).length addr
      ([l1]) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base ([l1])).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  have hbound : l1.var + 1 ≤ N := hrelr.literal_bound (⟨[l1]⟩ : Clause)
    (by simp) l1 (by simp)
  have hroom : uniformStartNat + pref.length + 3 * (l1.var + 2) <
      uniformMNat N + uctCurJ := by
    have h := hprep.room
    cases l1 <;>
      simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var,
        List.length_append] at h ⊢ <;> omega
  have hpayload :
      (encodeThreeClausesPayload (clauseToThree base [l1]).1).length =
        3 * (l1.var + 2) := by
    cases l1 <;>
      simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var,
        List.length_append] <;> omega
  have hrw : uniformStartNat + pref.length + 3 * (l1.var + 2) ≤ r := by
    simp only [List.length_append, hpayload] at hpostCursor ⊢
    omega
  have hAt := emitClauseIterProgramAt_eval_of_rel_one
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base l1 cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  have hprog := emitClauseProgram_one_frame_after_of_prep
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
    (varReg := uctVarReg) (doneReg := uctDoneReg) (lengthReg := uctLengthReg)
    (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg)
    (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg)
    (negPolReg := uctNegPolReg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (freshReg := uctFreshReg)
    (outerReg := uctOuterReg) (bound := N) (tailBound := N)
    (base := base) (outer := List.length (⟨[l1]⟩ :: cs)) (addr := addr)
    (l := l1) (rest := (cs.map encodeClause).flatten ++ tail) (pref := pref)
    (σ := σr) (σ0 := σdec) (by simpa using hprep) hbound hroom r hrw hrc hrt
  unfold uniformEmitIterCoreBody
  rw [hAt, emitClauseIterProgram, eval_seq]
  exact (hresetFrame _).trans hprog

/-- The iteration core body does not write above the output cursor when the head clause is a two-literal clause. -/
lemma uniformEmitIterBody_after_frame_of_rel_two
    (N : ℕ) (l1 l2 : NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨[l1, l2]⟩ : Clause) :: cs).length addr
      ([l1, l2]) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base ([l1, l2])).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  have hbound1 : l1.var + 1 ≤ N := hrelr.literal_bound (⟨[l1, l2]⟩ : Clause)
    (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ N := hrelr.literal_bound (⟨[l1, l2]⟩ : Clause)
    (by simp) l2 (by simp)
  have hpairBelow : uctPol2Reg < uniformStartNat ∧ uctVar2Reg < uniformStartNat :=
    ⟨hrelr.long_safety.below _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.below _ (by simp [longClauseRegisterList])⟩
  have hpairNonzero : uctPol2Reg ≠ 0 ∧ uctVar2Reg ≠ 0 :=
    ⟨hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
  have hpairSafe : RegisterPairwise
      [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctPol2Reg, uctVar2Reg,
        uctFreshReg, uctOuterReg] :=
    registerPairwise_of_nodup hrelr.long_safety.pair_register_nodup
  have hroom : uniformStartNat + pref.length + l1.var + 2 * l2.var + 6 <
      uniformMNat N + uctCurJ := by
    have h := hprep.room
    cases l1 <;> cases l2 <;>
      simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var,
        List.length_append] at h ⊢ <;> omega
  have hpayload :
      (encodeThreeClausesPayload (clauseToThree base [l1, l2]).1).length =
        l1.var + 2 * l2.var + 6 := by
    cases l1 <;> cases l2 <;>
      simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var,
        List.length_append] <;> omega
  have hrw : uniformStartNat + pref.length + l1.var + 2 * l2.var + 6 ≤ r := by
    simp only [List.length_append, hpayload] at hpostCursor ⊢
    omega
  have hAt := emitClauseIterProgramAt_eval_of_rel_two
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base l1 l2 cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  have hprog := emitClauseProgram_two_frame_after_of_prep
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
    (varReg := uctVarReg) (doneReg := uctDoneReg) (lengthReg := uctLengthReg)
    (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg)
    (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg)
    (negPolReg := uctNegPolReg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (freshReg := uctFreshReg)
    (outerReg := uctOuterReg) (bound := N) (tailBound := N)
    (base := base) (outer := List.length (⟨[l1, l2]⟩ :: cs)) (addr := addr)
    (l1 := l1) (l2 := l2) (rest := (cs.map encodeClause).flatten ++ tail)
    (pref := pref) (σ := σr) (σ0 := σdec) (by simpa using hprep)
    hbound1 hbound2 hpairBelow hpairNonzero hpairSafe hroom r hrw hrc hrt
  unfold uniformEmitIterCoreBody
  rw [hAt, emitClauseIterProgram, eval_seq]
  exact (hresetFrame _).trans hprog

/-- The iteration core body does not write above the output cursor when the head clause is a three-literal clause. -/
lemma uniformEmitIterBody_after_frame_of_rel_three
    (N : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal) (cs : List Clause)
    (tail pref : Bits) (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs).length addr
      ([l1, l2, l3]) ((cs.map encodeClause).flatten ++ tail)
      pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload
        (clauseToThree base ([l1, l2, l3])).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  have hbound1 : l1.var + 1 ≤ N := hrelr.literal_bound (⟨[l1, l2, l3]⟩ : Clause)
    (by simp) l1 (by simp)
  have hbound2 : l2.var + 1 ≤ N := hrelr.literal_bound (⟨[l1, l2, l3]⟩ : Clause)
    (by simp) l2 (by simp)
  have hbound3 : l3.var + 1 ≤ N := hrelr.literal_bound (⟨[l1, l2, l3]⟩ : Clause)
    (by simp) l3 (by simp)
  have htripleBelow : uctPol2Reg < uniformStartNat ∧ uctVar2Reg < uniformStartNat ∧
      uctPol3Reg < uniformStartNat ∧ uctVar3Reg < uniformStartNat :=
    ⟨hrelr.long_safety.below _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.below _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.below _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.below _ (by simp [longClauseRegisterList])⟩
  have htripleNonzero : uctPol2Reg ≠ 0 ∧ uctVar2Reg ≠ 0 ∧
      uctPol3Reg ≠ 0 ∧ uctVar3Reg ≠ 0 :=
    ⟨hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList]),
      hrelr.long_safety.nonzero _ (by simp [longClauseRegisterList])⟩
  have htripleSafe : RegisterPairwise
      [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctPol2Reg, uctVar2Reg,
        uctPol3Reg, uctVar3Reg, uctPosPolReg, uctNegPolReg, uctFreshReg,
        uctOuterReg] :=
    registerPairwise_of_nodup hrelr.long_safety.triple_register_nodup
  have hroom : uniformStartNat + pref.length + l1.var + l2.var +
      2 * base + 2 * l3.var + 12 < uniformMNat N + uctCurJ := by
    have h := hprep.room
    cases l1 <;> cases l2 <;> cases l3 <;>
       simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
         encodeLiteral, NPComplete.BitEncoding.encodeNat_length,
         splitTail, NPComplete.SAT.Literal.var,
         List.length_append] at h ⊢ <;> omega
  have hpayload :
      (encodeThreeClausesPayload (clauseToThree base [l1, l2, l3]).1).length =
        l1.var + l2.var + 2 * base + 2 * l3.var + 12 := by
    cases l1 <;> cases l2 <;> cases l3 <;>
       simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
         encodeLiteral, NPComplete.BitEncoding.encodeNat_length,
         splitTail, NPComplete.SAT.Literal.var,
         List.length_append] <;> omega
  have hrw : uniformStartNat + pref.length + l1.var + l2.var +
      2 * base + 2 * l3.var + 12 ≤ r := by
    simp only [List.length_append, hpayload] at hpostCursor ⊢
    omega
  have hAt := emitClauseIterProgramAt_eval_of_rel_three
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base l1 l2 l3 cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  have hprog := emitClauseProgram_three_frame_after_of_prep
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (start := uniformStartNat) (cursorReg := uctCursorReg) (polReg := uctPolReg)
    (varReg := uctVarReg) (doneReg := uctDoneReg) (lengthReg := uctLengthReg)
    (remainingReg := uctRemainingReg) (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg)
    (pol3Reg := uctPol3Reg) (var3Reg := uctVar3Reg) (posPolReg := uctPosPolReg)
    (negPolReg := uctNegPolReg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (freshReg := uctFreshReg)
    (outerReg := uctOuterReg) (bound := N) (tailBound := N)
    (base := base) (outer := List.length (⟨[l1, l2, l3]⟩ :: cs)) (addr := addr)
    (l1 := l1) (l2 := l2) (l3 := l3)
    (rest := (cs.map encodeClause).flatten ++ tail) (pref := pref)
    (σ := σr) (σ0 := σdec) (by simpa using hprep)
    hbound1 hbound2 hbound3 htripleBelow htripleNonzero htripleSafe hroom r hrw hrc hrt
  unfold uniformEmitIterCoreBody
  rw [hAt, emitClauseIterProgram, eval_seq]
  exact (hresetFrame _).trans hprog

/-- The scratch reset program only writes registers below the frame start. -/
lemma uniformEmitIterBody_after_frame_of_rel_scratch_frame
    (r : ℕ) (hrstart : uniformStartNat ≤ r) (s : Store) :
    uniformEmitScratchResetProg.eval s r = s r := by
  have hs20 : 20 < uniformStartNat := by simp [uniformStartNat, relocateControlGap]
  have hmem : r ∉ uniformEmitScratchRegs := by
    intro hm
    have hm' := uniformEmitScratchRegs_mem_le r hm
    omega
  have hp : r ≠ uctPosPolReg := by
    intro heq
    subst r
    norm_num [uctPosPolReg, uniformStartNat, relocateControlGap] at hrstart
  have hn : r ≠ uctNegPolReg := by
    intro heq
    subst r
    norm_num [uctNegPolReg, uniformStartNat, relocateControlGap] at hrstart
  exact uniformEmitScratchResetProg_frame s hmem hp hn

/-- Dispatch on the head clause length: the iteration core body does not write above the
    output cursor. -/
lemma uniformEmitIterBody_after_frame_of_rel_core
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base r : ℕ) (σr σdec : Store)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σr)
    (hbr : σr uctSavedBoundReg = N)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
      ((cs.map encodeClause).flatten ++ tail) pref σr σdec)
    (hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1).length ≤ r)
    (hresetFrame : ∀ s : Store,
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r)
    (hrc : r ≠ uniformMNat N + uctCurJ)
    (hrt : r ≠ uniformMNat N + uctTmpJ) :
    uniformEmitIterCoreBody.eval σr r = σr r := by
  cases c with
  | mk lits =>
    match lits with
    | [] =>
      exact uniformEmitIterBody_after_frame_of_rel_nil N cs tail pref addr base r σr σdec
        hrelr hbr hprep hpostCursor hresetFrame hrc hrt
    | [l1] =>
      exact uniformEmitIterBody_after_frame_of_rel_one N l1 cs tail pref addr base r
        σr σdec hrelr hbr hprep hpostCursor hresetFrame hrc hrt
    | [l1, l2] =>
      exact uniformEmitIterBody_after_frame_of_rel_two N l1 l2 cs tail pref addr
        base r σr σdec hrelr hbr hprep hpostCursor hresetFrame hrc hrt
    | [l1, l2, l3] =>
      exact uniformEmitIterBody_after_frame_of_rel_three N l1 l2 l3 cs tail pref
        addr base r σr σdec hrelr hbr hprep hpostCursor hresetFrame hrc hrt
    | l1 :: l2 :: l3 :: l4 :: rest =>
      exact uniformEmitIterCoreBody_frame_of_long
        (N := N) (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
        (rest := rest) (cs := cs) (tail := tail) (pref := pref)
        (addr := addr) (base := base) (r := r) (σr := σr) (σdec := σdec)
        hrelr hbr hprep hpostCursor hresetFrame hrc hrt

lemma uniformEmitIterBody_after_frame_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ τ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hτ : uniformEmitIterBody.eval σ = τ)
    (hrelτ : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
      (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ) :
    ∀ r, τ (uniformMNat N + uctCurJ) ≤ r →
      r ≠ uniformMNat N + uctCurJ → r ≠ uniformMNat N + uctTmpJ → τ r = σ r := by
  obtain ⟨σr, σdec, hσrEq, _, hprep⟩ :=
    uniform_emit_prep_state_of_rel N c cs tail pref addr base σ hrel hb
  have hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σr := by
    simpa [hσrEq] using
      (uniformEmitScratchResetProg_cnfEmitRel
        (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel)
  have hbr : σr uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with ⟨_, _, _, _, _, hsaved⟩
    rw [hσrEq]
    exact hsaved.trans hb
  intro r hr hrc hrt
  have hpostCursor : uniformStartNat +
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1).length ≤ r := by
    calc
      _ = τ (uniformMNat N + uctCurJ) := hrelτ.writer.cursor.symm
      _ ≤ r := hr
  have hrstart : uniformStartNat ≤ r := by omega
  have hpreFrame : σr r = σ r := by
    rw [hσrEq]
    exact uniformEmitIterBody_after_frame_of_rel_scratch_frame r hrstart σ
  have hpostScratchFrame := uniformEmitIterBody_after_frame_of_rel_scratch_frame r hrstart
  have hresetFrame (s : Store) :
      (emitClauseResetProg uctLengthReg uctDoneReg).eval s r = s r := by
    exact emitClauseResetProg_frame uctLengthReg uctDoneReg s
      (by have hs := hrelr.safety.length_below; omega)
      (by have hs := hrelr.safety.done_below; omega)
  have hcore := uniformEmitIterBody_after_frame_of_rel_core N c cs tail pref addr base r σr σdec
    hrelr hbr hprep hpostCursor hresetFrame hrc hrt
  have hbodyEq : τ = uniformEmitScratchResetProg.eval
      (uniformEmitIterCoreBody.eval σr) := by
    rw [← hτ]
    simp [uniformEmitIterBody, hσrEq, eval_seq]
  calc
    τ r = uniformEmitScratchResetProg.eval (uniformEmitIterCoreBody.eval σr) r := by rw [hbodyEq]
    _ = uniformEmitIterCoreBody.eval σr r := hpostScratchFrame _
    _ = σr r := hcore
    _ = σ r := hpreFrame

lemma uniformEmitIterBody_tight_of_outer_rel
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ)
    (hK1 : 1 ≤ uniformEmitTightEnvelope (encodeCNF φ).length) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (uniformEmitIterBody.eval σ) := by
  obtain ⟨τ, hτ, hrelτ, _⟩ := uniformEmitIterBody_eval_of_rel
    (encodeCNF φ).length c cs tail pref addr base σ hrel hb
  have hafter := uniformEmitIterBody_after_frame_of_rel
    (encodeCNF φ).length c cs tail pref addr base σ τ hrel hb hτ hrelτ
  have hstore := uniformEmitIterBody_tight_of_outer_frames φ consumed c cs tail pref addr base
    σ τ hsplit hacc hrel hb hσ hK1 hτ hrelτ hafter
  simpa [hτ] using hstore

lemma uniform_emit_loop_prefix_accounting_tight
    (φ : CNF) (consumed clauses : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hsplit : consumed ++ clauses = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base clauses tail pref addr σ)
    (hb : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ) :
    ∀ m ≤ clauses.length, ∃ τ clauses' base' pref' addr' consumed',
      τ = loopEval uniformEmitIterBody m σ ∧
      consumed'.length = consumed.length + m ∧
      consumed' ++ clauses' = consumed ++ clauses ∧
      CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
        (encodeCNF φ).length (encodeCNF φ).length base' clauses' tail pref' addr' τ ∧
      OuterEmitAccounting (cnfVarBound φ)
        (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
        (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
        consumed' base' pref' addr' ∧
      τ uctSavedBoundReg = (encodeCNF φ).length ∧
      StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) τ := by
  have hK1 : 1 ≤ uniformEmitTightEnvelope (encodeCNF φ).length := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  induction clauses generalizing consumed base pref addr σ with
  | nil =>
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      exact ⟨σ, [], base, pref, addr, consumed, by simp, by simp, by simp,
        hrel, hacc, hb, hσ⟩
  | cons c cs ih =>
      intro m hm
      cases m with
      | zero =>
          exact ⟨σ, c :: cs, base, pref, addr, consumed, by simp, by simp, by simp,
            hrel, hacc, hb, hσ⟩
      | succ m =>
          have hm' : m ≤ cs.length := by simpa using hm
          obtain ⟨σ₁, hstep, hrel₁, hb₁⟩ := uniformEmitIterBody_eval_of_rel
            (encodeCNF φ).length c cs tail pref addr base σ hrel hb
          have hstore₁ := uniformEmitIterBody_tight_of_outer_rel φ consumed c cs tail
            pref addr base σ hsplit hacc hrel hb hσ hK1
          have hσ₁ : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ₁ := by
            simpa [hstep] using hstore₁
          have hacc₁ : OuterEmitAccounting (cnfVarBound φ)
              (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
              (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
              (consumed ++ [c]) (clauseToThree base c.lits).2
              (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
              (addr + (encodeList encodeLiteral c.lits).length) :=
            OuterEmitAccounting.step (cnfVarBound φ)
              (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
              (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
              consumed c base pref addr hacc
          obtain ⟨τ, clauses', base', pref', addr', consumed', hτ, hlen', hsplit',
            hrel', hacc', hb', hσ'⟩ :=
            ih (consumed := consumed ++ [c])
              (base := (clauseToThree base c.lits).2)
              (pref := pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
              (addr := addr + (encodeList encodeLiteral c.lits).length)
              (σ := σ₁) (by simpa [List.append_assoc] using hsplit) hacc₁ hrel₁ hb₁ hσ₁ m hm'
          refine ⟨τ, clauses', base', pref', addr', consumed', ?_, ?_, ?_, hrel', hacc', hb', hσ'⟩
          · calc
              τ = loopEval uniformEmitIterBody m σ₁ := hτ
              _ = loopEval uniformEmitIterBody m (uniformEmitIterBody.eval σ) := by rw [hstep]
              _ = loopEval uniformEmitIterBody (m + 1) σ := by rw [loopEval_succ]
          · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen'
          · simpa [List.append_assoc] using hsplit'

lemma programBoundedIn_uniformEmitIterBody_of_outer_accounting
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (pref : Bits) (addr base : ℕ) (σ : Store)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base (c :: cs) ([] : Bits) pref addr σ)
    (hb : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ)
    (hzero : CellsZeroFrom
      (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length) σ) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope (encodeCNF φ).length)
      σ uniformEmitIterBody := by
  let N := (encodeCNF φ).length
  let inputEnd := uniformAddrNat N + N
  have hwin := OuterEmitAccounting.clause_window φ consumed c cs base pref addr hsplit hacc
  have hwin' : SplitTailEmitWindow inputEnd (base + c.lits.length) base c.lits
      ((cs.map encodeClause).flatten ++ ([] : Bits)) (addr + c.lits.length + 1) := by
    refine ⟨?_, le_rfl⟩
    simpa [inputEnd] using hwin.1
  have hcell := OuterEmitAccounting.clause_input_cells_le_one φ consumed c cs base pref addr σ
    hsplit hacc hrel hzero
  have hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N := by
    exact (uniform_split_tail_input_end_le_tight N).trans
      (uniformEmitTightEnvelope_le_long_value_envelope N)
  have hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N := by
    simpa [inputEnd] using uniform_split_tail_cursor_budget_le_long_value_envelope N
  have hbaseLimit : base + c.lits.length ≤ uniformEmitLongValueEnvelope N := by
    have hbase : base ≤ uniformEmitTightEnvelope N := by
      rw [← hrel.fresh]
      exact hσ uctFreshReg
    have hclause : c.lits.length ≤ N := by
      have h := hrel.clause_bound c (by simp)
      omega
    have hK := uniformEmitTightEnvelope_le_long_value_envelope N
    have hN := uniform_emit_n_le_long_value_envelope N
    simp only [uniformEmitLongValueEnvelope] at ⊢
    omega
  have hwr := uniform_emit_outer_writer_room φ consumed c cs base pref addr hsplit hacc
  exact programBoundedIn_uniformEmitIterBody_of_cnfEmitRel N inputEnd c cs [] pref addr base σ
    hrel hb hσ hcell hwin' hinputEnd hend hwr

end NPComplete.CookLevin

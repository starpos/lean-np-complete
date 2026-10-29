module

public import NPComplete.CookLevin.UniformPackaging.DispatchShortBounds
public import NPComplete.CookLevin.UniformPackaging.DispatchTmp

/-!
# Long-clause dispatch bounds

Long clauses use the split-tail path, where decoding and output writing interact
across several stages. This module bounds that branch and tracks the resulting
temporary and writer state needed by dispatch assembly.
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

lemma programBoundedIn_uniform_emit_dispatch_long_prologue
    (D : ℕ) (σ : Store) (p1 p2 p3 p4 body commit : Program)
    (h1 : ProgramBoundedIn D σ p1)
    (h2 : ProgramBoundedIn D (p1.eval σ) p2)
    (h3 : ProgramBoundedIn D ((Program.seq p1 p2).eval σ) p3)
    (h4 : ProgramBoundedIn D ((Program.seq p1 (Program.seq p2 p3)).eval σ) p4)
    (hbody : ProgramBoundedIn D
      ((Program.seq p1 (Program.seq p2 (Program.seq p3 p4))).eval σ) body)
    (hcommit : ProgramBoundedIn D (body.eval
      ((Program.seq p1 (Program.seq p2 (Program.seq p3 p4))).eval σ)) commit) :
    ProgramBoundedIn D σ
      (Program.seq p1 (Program.seq p2 (Program.seq p3 (Program.seq p4
        (Program.seq body commit))))) := by
  have hseq : ProgramBoundedInSequence D σ [p1, p2, p3, p4, body, commit] := by
    exact .cons _ _ _ h1 (.cons _ _ _ h2 (.cons _ _ _ (by simpa [eval_seq] using h3)
      (.cons _ _ _ (by simpa [eval_seq] using h4)
        (.cons _ _ _ (by simpa [eval_seq] using hbody)
          (.cons _ _ _ (by simpa [eval_seq] using hcommit) (.nil _))))))
  simpa [programSequence] using programBoundedIn_programSequence D σ _ hseq

lemma programBoundedIn_uniform_emit_dispatch_long_branch_of_reach
    (N inputEnd baseLimit base : ℕ)
    (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hprep : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))))
    (hsetup : ProgramBoundedIn (uniformEmitSyntaxEnvelope N)
      ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))).eval σ)
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg))
    (hσsetup : StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ)))
    (hzero : ProgramBoundedIn (uniformEmitSyntaxEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ))
      (splitTailEmitTerminalZeroProg uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg))
    (hremainingValue :
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ)) uctRemainingReg + 1 ≤
        uniformEmitSyntaxEnvelope N)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ))
      (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry ls pref tail addr
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (hb :
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ)) uctSavedBoundReg = N)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hcommit : ProgramBoundedIn (uniformEmitDispatchEnvelope N)
      ((splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval
        ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
          (Program.seq (.assign uctCarryPolReg (.const 1))
            (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
              (.assign uctPosPolReg (.const 0))))).eval σ))
      (emitClauseCommitProg uctOuterReg)) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
                  uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
                  uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
                  uctSavedBoundReg)
                (emitClauseCommitProg uctOuterReg)))))) := by
  have hSD : uniformEmitSyntaxEnvelope N ≤ uniformEmitDispatchEnvelope N :=
    uniformEmitSyntaxEnvelope_le_dispatch_envelope N
  let σprep :=
    (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
      (Program.seq (.assign uctCarryPolReg (.const 1))
        (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.assign uctPosPolReg (.const 0))))).eval σ
  have hlongS := programBoundedIn_uniform_splitTailEmitLongClauseProgAt_of_reach
    N inputEnd baseLimit σprep hsetup hσsetup hzero hremainingValue base carry ls pref tail addr
    hbound hrel hb hwin hinputEnd hbaseLimit hend
  have hlongD : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σprep
      (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
    exact programBoundedIn_of_le hSD hlongS
  rcases hprep with ⟨h1, h2, h3, h4⟩
  exact programBoundedIn_uniform_emit_dispatch_long_prologue
    (uniformEmitDispatchEnvelope N) σ
    (.assign uctRemainingReg (.reg uctLengthReg))
    (.assign uctCarryPolReg (.const 1))
    (.assign uctCarryValReg (.reg uctFreshReg))
    (.assign uctPosPolReg (.const 0))
    (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)
    (emitClauseCommitProg uctOuterReg) h1 h2 h3 h4 hlongD hcommit

/-- The four prologue assignments of the long branch only touch their own registers and fix
the values of the remaining counter, carry polarity, carry value and position polarity. -/
lemma uniform_emit_dispatch_long_prep_state_assign
    (ls : List NPComplete.SAT.Literal) (σdec : Store)
    (hlen : σdec uctLengthReg = ls.length) :
    ∃ σprep : Store,
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))).eval σdec = σprep ∧
      (∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
        r ≠ uctPosPolReg → σprep r = σdec r) ∧
      σprep uctRemainingReg = ls.length ∧
      σprep uctPosPolReg = 0 ∧
      σprep uctCarryValReg = σdec uctFreshReg ∧
      σprep uctCarryPolReg = 1 := by
  let σ1 : Store := (Program.assign uctRemainingReg (.reg uctLengthReg)).eval σdec
  let σ2 : Store := (Program.assign uctCarryPolReg (.const 1)).eval σ1
  let σ3 : Store := (Program.assign uctCarryValReg (.reg uctFreshReg)).eval σ2
  let σprep : Store := (Program.assign uctPosPolReg (.const 0)).eval σ3
  have hunf : (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
      (Program.seq (.assign uctCarryPolReg (.const 1))
        (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.assign uctPosPolReg (.const 0))))).eval σdec = σprep := by
    simp [σprep, σ3, σ2, σ1]
  have hframe : ∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
      r ≠ uctPosPolReg → σprep r = σdec r := by
    intro r h1 h2 h3 h4
    simp only [σprep, σ3, σ2, σ1, eval_assign]
    rw [writeReg_diff _ _ _ _ h4, writeReg_diff _ _ _ _ h3, writeReg_diff _ _ _ _ h2,
      writeReg_diff _ _ _ _ h1]
  have hdist : uctRemainingReg ≠ uctPosPolReg ∧ uctRemainingReg ≠ uctCarryValReg ∧
      uctRemainingReg ≠ uctCarryPolReg ∧ uctCarryValReg ≠ uctPosPolReg ∧
      uctCarryPolReg ≠ uctPosPolReg ∧ uctCarryPolReg ≠ uctCarryValReg ∧
      uctFreshReg ≠ uctRemainingReg ∧ uctFreshReg ≠ uctCarryPolReg := by
    simp only [uctRemainingReg, uctCarryPolReg, uctCarryValReg, uctPosPolReg, uctFreshReg]
    omega
  have hrem : σprep uctRemainingReg = ls.length := by
    simp only [σprep, σ3, σ2, σ1, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ hdist.1, writeReg_diff _ _ _ _ hdist.2.1,
      writeReg_diff _ _ _ _ hdist.2.2.1, writeReg_same]
    exact hlen
  have hposVal : σprep uctPosPolReg = 0 := by
    simp only [σprep, eval_assign, Expr.eval, writeReg_same]
  have hcarryVal : σprep uctCarryValReg = σdec uctFreshReg := by
    simp only [σprep, σ3, σ2, σ1, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ hdist.2.2.2.1, writeReg_same,
      writeReg_diff _ _ _ _ hdist.2.2.2.2.2.2.2, writeReg_diff _ _ _ _ hdist.2.2.2.2.2.2.1]
  have hcarryPol : σprep uctCarryPolReg = 1 := by
    simp only [σprep, σ3, σ2, σ1, eval_assign, Expr.eval]
    rw [writeReg_diff _ _ _ _ hdist.2.2.2.2.1, writeReg_diff _ _ _ _ hdist.2.2.2.2.2.1,
      writeReg_same]
  exact ⟨σprep, hunf, hframe, hrem, hposVal, hcarryVal, hcarryPol⟩

/-- The prologue assignments leave the root cell, the writer cell and the writer state of the
decoded store untouched. -/
lemma uniform_emit_dispatch_long_prep_state_writer
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec σprep : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hframe : ∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
      r ≠ uctPosPolReg → σprep r = σdec r) :
    σprep 0 = uniformMNat N ∧
    σprep (uniformMNat N + uctCurJ) ≠ 0 ∧
    WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref := by
  have hcellne : uniformMNat N + uctCurJ ≠ uctRemainingReg ∧
      uniformMNat N + uctCurJ ≠ uctCarryPolReg ∧
      uniformMNat N + uctCurJ ≠ uctCarryValReg ∧
      uniformMNat N + uctCurJ ≠ uctPosPolReg := by
    have h1 := (uniform_emit_dispatch_writer_cell_ne N uctRemainingReg
      (by simp only [uctRemainingReg]; omega)).1
    have h2 := (uniform_emit_dispatch_writer_cell_ne N uctCarryPolReg
      (by simp only [uctCarryPolReg]; omega)).1
    have h3 := (uniform_emit_dispatch_writer_cell_ne N uctCarryValReg
      (by simp only [uctCarryValReg]; omega)).1
    have h4 := (uniform_emit_dispatch_writer_cell_ne N uctPosPolReg
      (by simp only [uctPosPolReg]; omega)).1
    exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4⟩
  have hbelow : uctRemainingReg < uniformStartNat ∧ uctCarryPolReg < uniformStartNat ∧
      uctCarryValReg < uniformStartNat ∧ uctPosPolReg < uniformStartNat := by
    simp only [uctRemainingReg, uctCarryPolReg, uctCarryValReg, uctPosPolReg,
      uniformStartNat, relocateControlGap]
    omega
  have hframeGe : ∀ r, uniformStartNat ≤ r → σprep r = σdec r := by
    intro r hr
    exact hframe r (by omega) (by omega) (by omega) (by omega)
  have hrootP : σprep 0 = uniformMNat N := by
    rw [hframe 0 (by simp only [uctRemainingReg]; omega)
      (by simp only [uctCarryPolReg]; omega)
      (by simp only [uctCarryValReg]; omega)
      (by simp only [uctPosPolReg]; omega)]
    exact hprep.writer.root
  have hq0 : σprep (uniformMNat N + uctCurJ) ≠ 0 := by
    rw [hframe _ hcellne.1 hcellne.2.1 hcellne.2.2.1 hcellne.2.2.2, hprep.writer.cursor]
    have hstart := hprep.writer.start_pos
    omega
  have hwriterP : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref := by
    rcases hprep.writer with ⟨hroot, hcur, hbitsat, hstart, hsafe⟩
    refine ⟨hrootP, ?_, ?_, hstart, hsafe⟩
    · have hs := hprep.writer.safe
      exact (hframeGe (uniformMNat N + uctCurJ) (by omega)).trans hcur
    · apply bitsAt_of_frame σdec σprep uniformStartNat pref hbitsat
      intro r hlo hhi
      exact hframeGe r hlo
  exact ⟨hrootP, hq0, hwriterP⟩

/-- The input bits above the cursor are not disturbed by the prologue assignments. -/
lemma uniform_emit_dispatch_long_prep_state_bits
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec σprep : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hframe : ∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
      r ≠ uctPosPolReg → σprep r = σdec r) :
    BitsFrom σprep (addr + ls.length + 1) (splitTailInputBits ls rest) := by
  have hMbig : 24 ≤ uniformMNat N + uctTmpJ := by
    simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap, uctTmpJ]
    omega
  have hregs : uctRemainingReg ≤ 24 ∧ uctCarryPolReg ≤ 24 ∧ uctCarryValReg ≤ 24 ∧
      uctPosPolReg ≤ 24 := by
    simp only [uctRemainingReg, uctCarryPolReg, uctCarryValReg, uctPosPolReg]
    omega
  have habove := hprep.input_above
  intro i hi
  have hcell := hframe (addr + ls.length + 1 + i) (by omega) (by omega) (by omega)
    (by omega)
  rw [hcell]
  exact hprep.input i hi

/-- The prologue assignments keep the decoded store inside the long value envelope. -/
lemma uniform_emit_dispatch_long_prep_state_store
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec σprep : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hframe : ∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
      r ≠ uctPosPolReg → σprep r = σdec r)
    (hrem : σprep uctRemainingReg = ls.length) (hposVal : σprep uctPosPolReg = 0)
    (hcarryVal : σprep uctCarryValReg = σdec uctFreshReg)
    (hcarryPol : σprep uctCarryPolReg = 1) :
    StoreValuesLe (uniformEmitLongValueEnvelope N) σprep := by
  have hK1 : 1 ≤ uniformEmitLongValueEnvelope N := by
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  have hN := uniform_emit_n_le_long_value_envelope N
  have hb := hprep.bound
  have hfresh := hstore uctFreshReg
  intro i
  by_cases hi : i = uctRemainingReg ∨ i = uctCarryPolReg ∨ i = uctCarryValReg ∨
    i = uctPosPolReg
  · rcases hi with rfl | rfl | rfl | rfl <;> omega
  · rw [hframe i (fun h => hi (Or.inl h))
      (fun h => hi (Or.inr (Or.inl h)))
      (fun h => hi (Or.inr (Or.inr (Or.inl h))))
      (fun h => hi (Or.inr (Or.inr (Or.inr h))))]
    exact hstore i

/-! The four-assignment prologue of the long branch copies the decoded length
    into the remaining counter, sets the carry polarity to 1, copies the fresh
    counter into the carry value, and sets the position polarity to 0.
    Every long-branch premise is transported from the decoded state through the
    frame below; no premise of the decoded state is lost. -/

lemma uniform_emit_dispatch_long_prep_state
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N) :
    ∃ σprep : Store,
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))).eval σdec = σprep ∧
      σprep 0 = uniformMNat N ∧
      σprep uctSavedBoundReg = N ∧
      σprep uctCursorReg = addr + ls.length + 1 ∧
      σprep uctRemainingReg = ls.length ∧
      σprep uctPosPolReg = 0 ∧
      σprep uctFreshReg = base ∧
      σprep (uniformMNat N + uctCurJ) ≠ 0 ∧
      BitsFrom σprep (addr + ls.length + 1) (splitTailInputBits ls rest) ∧
      WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref ∧
      StoreValuesLe (uniformEmitLongValueEnvelope N) σprep ∧
      (∀ r, r ≠ uctRemainingReg → r ≠ uctCarryPolReg → r ≠ uctCarryValReg →
        r ≠ uctPosPolReg → σprep r = σdec r) ∧
      uniformStartNat ≤ addr + ls.length + 1 ∧
      uniformMNat N + uctTmpJ < addr + ls.length + 1 := by
  obtain ⟨σprep, hunf, hframe, hrem, hposVal, hcarryVal, hcarryPol⟩ :=
    uniform_emit_dispatch_long_prep_state_assign ls σdec hprep.length
  obtain ⟨hrootP, hq0, hwriterP⟩ :=
    uniform_emit_dispatch_long_prep_state_writer N base outer addr ls rest pref σr σdec σprep
      hprep hframe
  have hbits := uniform_emit_dispatch_long_prep_state_bits N base outer addr ls rest pref σr σdec
    σprep hprep hframe
  have hstoreP := uniform_emit_dispatch_long_prep_state_store N base outer addr ls rest pref σr
    σdec σprep hprep hstore hframe hrem hposVal hcarryVal hcarryPol
  refine ⟨σprep, hunf, hrootP, ?_, ?_, hrem, hposVal, ?_, hq0, hbits, hwriterP, hstoreP,
    hframe, hprep.start_at_input, hprep.input_above⟩
  · exact (hframe uctSavedBoundReg (by simp only [uctSavedBoundReg, uctRemainingReg]; omega)
      (by simp only [uctSavedBoundReg, uctCarryPolReg]; omega)
      (by simp only [uctSavedBoundReg, uctCarryValReg]; omega)
      (by simp only [uctSavedBoundReg, uctPosPolReg]; omega)).trans hsaved
  · exact (hframe uctCursorReg (by simp only [uctCursorReg, uctRemainingReg]; omega)
      (by simp only [uctCursorReg, uctCarryPolReg]; omega)
      (by simp only [uctCursorReg, uctCarryValReg]; omega)
      (by simp only [uctCursorReg, uctPosPolReg]; omega)).trans hprep.cursor
  · exact (hframe uctFreshReg (by simp only [uctFreshReg, uctRemainingReg]; omega)
      (by simp only [uctFreshReg, uctCarryPolReg]; omega)
      (by simp only [uctFreshReg, uctCarryValReg]; omega)
      (by simp only [uctFreshReg, uctPosPolReg]; omega)).trans hprep.fresh_value

/-! The concrete long branch on the decoded state: the preparation assignments,
    the split-tail setup, the split-tail loop, and the commit are all bounded by
    the dispatch envelope.  The capacity premises of the setup are derived from
    the preparation state's payload room via the split-form bridge, and the
    register safety comes from the uniform layout, so the only quantitative
    inputs are the decoded-state envelope, the window, and the clause bounds. -/

/-- The third-register writer append reads back the fresh base from the temporary cell after
the two literals are decoded; this is the writer half of the long-clause setup. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_long_writer_tmp
    (N base addr : ℕ) (l1 l2 : NPComplete.SAT.Literal) (lsTail : List NPComplete.SAT.Literal)
    (pref tail : Bits) (σprep : Store)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hcursor : σprep uctCursorReg = addr)
    (hinput : BitsFrom σprep addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (hwriter : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σprep uctPosPolReg = 0) (hfresh : σprep uctFreshReg = base)
    (hstart : uniformStartNat ≤ addr) :
    (writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctPosPolReg uctFreshReg).eval
      ((decodeLiteralValueProgram uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg N).eval
        ((decodeLiteralValueProgram uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg N).eval σprep))
      (uniformMNat N + uctTmpJ) = base := by
  have hinput2 : BitsFrom σprep addr (encodeLiteral l1 ++ encodeLiteral l2 ++
      splitTailInputBits lsTail tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hinput
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  obtain ⟨τ1, υ1, hτ1, hυ1, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2, hframe1, hframe2⟩ :=
    decode_two_literal_value_correct uctCursorReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctDoneReg N addr l1 l2 (splitTailInputBits lsTail tail) σprep
      hsafety.second.distinct.1 hsafety.second.distinct.2.1
      hsafety.second.distinct.2.2.1 hsafety.second.distinct.2.2.2.1
      hsafety.second.distinct.2.2.2.2.1 hsafety.second.distinct.2.2.2.2.2
      hsafety.third.distinct.1 hsafety.third.distinct.2.1
      hsafety.third.distinct.2.2.2.1 hsafety.third.distinct.2.2.2.2.1
      hsafety.third.distinct.2.2.2.2.2
      ⟨lt_of_lt_of_le hsafety.second.below.1 hstart,
        lt_of_lt_of_le hsafety.second.below.2.1 hstart,
        lt_of_lt_of_le hsafety.second.below.2.2.1 hstart,
        lt_of_lt_of_le hsafety.third.below.2.1 hstart,
        lt_of_lt_of_le hsafety.third.below.2.2.1 hstart,
        lt_of_lt_of_le hsafety.second.below.2.2.2 hstart⟩
      hbound1 hbound2 hcursor hinput2
  have hτ1state : WriterState τ1 (uniformMNat N) uctCurJ uniformStartNat pref :=
    writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref
      σprep τ1 uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg hwriter hframe1
      hsafety.second.nonzero.1 hsafety.second.nonzero.2.1
      hsafety.second.nonzero.2.2.1 hsafety.second.nonzero.2.2.2
      hsafety.second.below.1 hsafety.second.below.2.1
      hsafety.second.below.2.2.1 hsafety.second.below.2.2.2
  have hυ1state : WriterState υ1 (uniformMNat N) uctCurJ uniformStartNat pref :=
    writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref
      τ1 υ1 uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg hτ1state hframe2
      hsafety.third.nonzero.1 hsafety.third.nonzero.2.1
      hsafety.third.nonzero.2.2.1 hsafety.third.nonzero.2.2.2
      hsafety.third.below.1 hsafety.third.below.2.1
      hsafety.third.below.2.2.1 hsafety.third.below.2.2.2
  have hpos1 : υ1 uctPosPolReg = 0 :=
    (hframe2 uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe1 uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans hpos)
  have hfresh1 : υ1 uctFreshReg = base :=
    (hframe2 uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe1 uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans hfresh)
  have hpol1' : υ1 uctPol2Reg = literalPolarity l1 :=
    (hframe2 uctPol2Reg (by decide) (by decide) (by decide) (by decide)).trans hpol1
  have hvar1' : υ1 uctVar2Reg = l1.var :=
    (hframe2 uctVar2Reg (by decide) (by decide) (by decide) (by decide)).trans hvar1
  rw [← hτ1, ← hυ1]
  exact writerAppendThreeRegsProg_tmp_value
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctFreshReg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var base υ1
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hpol1' hvar1' hpol2 hvar2 hfresh1
    (by cases l1 <;> simp [literalPolarity]) (by cases l2 <;> simp [literalPolarity])
    hsafety.second.below.2.2.1
    ⟨hsafety.third.below.2.1, hsafety.third.below.2.2.1⟩
    ⟨hsafety.writer_below.2.2.1, hsafety.writer_below.2.2.2.1⟩
    hυ1state hroom

/-- The long-clause setup leaves the fresh base in the temporary cell: the four trailing
assignments of the setup do not touch it. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_long_setup_tmp
    (N base addr : ℕ) (l1 l2 : NPComplete.SAT.Literal) (lsTail : List NPComplete.SAT.Literal)
    (pref tail : Bits) (σprep : Store)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hcursor : σprep uctCursorReg = addr)
    (hinput : BitsFrom σprep addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (hwriter : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σprep uctPosPolReg = 0) (hfresh : σprep uctFreshReg = base)
    (hstart : uniformStartNat ≤ addr) :
    (splitTailEmitLongClauseSetup uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg N).eval σprep (uniformMNat N + uctTmpJ) = base := by
  have hw := uniformEmitIterBody_tmp_bound_of_rel_long_writer_tmp N base addr l1 l2 lsTail pref
    tail σprep hbound1 hbound2 hroom hcursor hinput hwriter hpos hfresh hstart
  have hcp : uctCarryPolReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctCarryPolReg, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctTmpJ]; omega
  have hcv : uctCarryValReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctCarryValReg, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctTmpJ]; omega
  have hfr : uctFreshReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctFreshReg, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctTmpJ]; omega
  have hrem : uctRemainingReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctRemainingReg, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctTmpJ]; omega
  simp only [splitTailEmitLongClauseSetup, eval_seq, eval_assign, Expr.eval, eval_skip]
  rw [writeReg_diff _ _ _ _ hrem.symm, writeReg_diff _ _ _ _ hfr.symm,
    writeReg_diff _ _ _ _ hcv.symm, writeReg_diff _ _ _ _ hcp.symm]
  exact hw

/-- The long-clause setup preserves the saved bound register, since that register lies below
the writer region and outside every register the setup touches. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_long_setup_saved_bound
    (N base addr : ℕ) (l1 l2 : NPComplete.SAT.Literal) (lsTail : List NPComplete.SAT.Literal)
    (pref tail : Bits) (σprep : Store)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hcapacity : uniformStartNat +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base) lsTail).length + 2 <
      uniformMNat N + uctCurJ)
    (hinput : BitsFrom σprep addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (hstart : uniformStartNat ≤ addr)
    (hwriter : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σprep uctPosPolReg = 0) (hfresh : σprep uctFreshReg = base)
    (hrem : σprep uctRemainingReg = (l1 :: l2 :: lsTail).length)
    (hcursor : σprep uctCursorReg = addr) (hb : σprep uctSavedBoundReg = N) :
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep
      uctSavedBoundReg = N := by
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  rw [splitTailEmitLongClauseSetupAt_eq uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg N σprep hb
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact (splitTailEmitLongClauseSetup_low_frame
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg N
    base l1 l2 lsTail pref tail addr σprep
    hbound1 hbound2 hroom hcapacity hinput uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hstart hwriter hpos hfresh hrem
    hcursor hsafety (r := uctSavedBoundReg) (by decide) (by decide)).trans hb

/-- On the prepared long-clause state, the split-tail long-clause program keeps the temporary
cell within `K`: the setup preserves the saved bound and the remaining loop is bounded by the
split-tail exit bound. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_long_exit
    (N K base addr : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (litRest : List NPComplete.SAT.Literal) (rest pref : Bits) (σprep : Store)
    (hbound : ∀ l ∈ l1 :: l2 :: l3 :: l4 :: litRest, l.var + 1 ≤ N)
    (hbase : base + (l1 :: l2 :: l3 :: l4 :: litRest).length ≤ K) (hNK : N ≤ K)
    (hroomPayload : uniformStartNat + pref.length +
      (encodeThreeClausesPayload (clauseToThree base (l1 :: l2 :: l3 :: l4 :: litRest)).1).length
        + 2 < uniformMNat N + uctCurJ)
    (hbP : σprep uctSavedBoundReg = N)
    (hcursorP : σprep uctCursorReg = addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
    (hremP : σprep uctRemainingReg = (l1 :: l2 :: l3 :: l4 :: litRest).length)
    (hposP : σprep uctPosPolReg = 0) (hfreshP : σprep uctFreshReg = base)
    (hinputP : BitsFrom σprep (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: litRest) rest))
    (hwriterP : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hstartP : uniformStartNat ≤ addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1)
    (haboveP : uniformMNat N + uctTmpJ < addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) :
    (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
      uctSavedBoundReg).eval σprep (uniformMNat N + uctTmpJ) ≤ K := by
  have hbound1 : l1.var + 1 ≤ N := hbound l1 (by simp)
  have hbound2 : l2.var + 1 ≤ N := hbound l2 (by simp)
  obtain ⟨hroom, hcapacity⟩ := splitTailPayload_room_of_encodeThreeClausesPayload
    (uniformMNat N) uctCurJ uniformStartNat base l1 l2 l3 (l4 :: litRest) pref hroomPayload
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  have hsetupEq := splitTailEmitLongClauseSetupAt_eq uctCurJ uctTmpJ
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg uctSavedBoundReg N σprep hbP
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsetupTmp : (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
      uctSavedBoundReg).eval σprep (uniformMNat N + uctTmpJ) ≤ K := by
    rw [hsetupEq,
      uniformEmitIterBody_tmp_bound_of_rel_long_setup_tmp N base
        (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) l1 l2 (l3 :: l4 :: litRest) pref
        rest σprep hbound1 hbound2 hroom hcursorP hinputP hwriterP hposP hfreshP hstartP]
    simp only [List.length_cons] at hbase ⊢
    omega
  obtain ⟨hrelSetup, _, _⟩ := splitTailEmitLongClauseSetup_eval
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg N
    base l1 l2 (l3 :: l4 :: litRest) pref rest
    (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) σprep
    hbound1 hbound2 hroom hcapacity hinputP uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 haboveP hstartP hwriterP hposP hfreshP hremP
    hcursorP hsafety
  have hbSetup := uniformEmitIterBody_tmp_bound_of_rel_long_setup_saved_bound N base
    (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1) l1 l2 (l3 :: l4 :: litRest) pref
    rest σprep hbound1 hbound2 hroom hcapacity hinputP hstartP hwriterP hposP hfreshP
    hremP hcursorP hbP
  have htmpExit := uniform_splitTailEmitProgAt_tmp_bound_of_rel_exit N K
    (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: l4 :: litRest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base) rest
    (addr + (l1 :: l2 :: l3 :: l4 :: litRest).length + 1 + l1.var + 2 + l2.var + 2)
    _ (fun l hl => hbound l (by simp [hl]))
    (by simp only [List.length_cons] at hbase ⊢; omega) hsetupTmp
    (by rw [hsetupEq]; exact hrelSetup) hbSetup (by simp) hNK
  simpa [splitTailEmitLongClauseProgAt, eval_seq, hsetupEq] using htmpExit

/-- The long branch of the clause dispatch, run from the decoded state, keeps the temporary
cell within `K`: the preparation assignments feed the long-clause program and the commit
assignment does not touch the temporary cell. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_long_dispatch
    (N K base outer addr : ℕ) (l1 l2 l3 l4 : NPComplete.SAT.Literal)
    (litRest : List NPComplete.SAT.Literal) (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr
      (l1 :: l2 :: l3 :: l4 :: litRest) rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound : ∀ l ∈ l1 :: l2 :: l3 :: l4 :: litRest, l.var + 1 ≤ N)
    (hbase : base + (l1 :: l2 :: l3 :: l4 :: litRest).length ≤ K) (hNK : N ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval
      σdec (uniformMNat N + uctTmpJ) ≤ K := by
  obtain ⟨σprep, hunf, _, hbP, hcursorP, hremP, hposP, hfreshP, _, hinputP, hwriterP, _,
    _, hstartP, haboveP⟩ :=
    uniform_emit_dispatch_long_prep_state N base outer addr (l1 :: l2 :: l3 :: l4 :: litRest) rest
      pref σr σdec hprep hstore hsaved
  have hexit := uniformEmitIterBody_tmp_bound_of_rel_long_exit N K base addr l1 l2 l3 l4 litRest
    rest pref σprep hbound hbase hNK hprep.room hbP hcursorP hremP hposP hfreshP hinputP
    hwriterP hstartP haboveP
  have hlen4 : 4 ≤ σdec uctLengthReg := by
    have h := hprep.length
    simp only [List.length_cons] at h
    omega
  have hout : uctOuterReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctOuterReg, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  rw [emitClauseDispatchProgAt_long_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σdec hlen4]
  simp only [eval_seq] at hunf ⊢
  rw [hunf]
  simpa [emitClauseCommitProg, eval_assign, Expr.eval,
    writeReg_diff _ uctOuterReg _ _ hout.symm] using hexit

/-- The clause dispatch from a prepared decoded state keeps the temporary cell within `K`,
whether the clause is short or long. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_dispatch
    (N K base outer addr : ℕ) (ls : List NPComplete.SAT.Literal) (rest pref : Bits)
    (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hbase : base + ls.length ≤ K) (hNK : N ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval
      σdec (uniformMNat N + uctTmpJ) ≤ K := by
  by_cases hshort : ls.length ≤ 3
  · exact uniform_emit_dispatch_short_tmp_value_of_prep N K base outer addr ls rest pref σr σdec
      hprep hsaved hbound hNK (by omega) hshort
  · rcases ls with _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, _ | ⟨l4, litRest⟩⟩⟩⟩
    · simp at hshort
    · simp at hshort
    · simp at hshort
    · simp at hshort
    · exact uniformEmitIterBody_tmp_bound_of_rel_long_dispatch N K base outer addr l1 l2 l3 l4
        litRest rest pref σr σdec hprep hstore hsaved hbound hbase hNK

/-- The prepared decoded state of the first clause: the scratch reset followed by the natural
number decode of the clause length yields the clause preparation state. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_prep
    (N : ℕ) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
      ((cs.map encodeClause).flatten ++ tail) pref (uniformEmitScratchResetProg.eval σ)
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) := by
  have hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hhead := cnfEmitRel_head_input (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
    uctCarryValReg uctFreshReg uctOuterReg N N base c cs tail pref addr _ hrelr
  have hroom : uniformStartNat + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c.lits).1).length + 2 <
      uniformMNat N + uctCurJ := by
    have hc := hrelr.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  exact emitClausePrepState_of_pre_eq (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg uctFreshReg
    uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
    ((cs.map encodeClause).flatten ++ tail) pref _ _
    (decodeNatProgramAt_eq _ _ _ _ N _ hbr) uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 (hrelr.clause_bound c (by simp)) hrelr.start_at_input hhead
    hrelr.cursor hrelr.length_zero hrelr.done_zero hrelr.outer hrelr.fresh hrelr.pos hrelr.neg
    hrelr.input_above hrelr.writer hroom hrelr.safety

/-- After the scratch reset and the decode of the clause length, the decoded state still
satisfies the long-value envelope. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_decode_store
    (N : ℕ) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ) :
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) := by
  have hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hσrT := storeValuesLe_uniformEmitScratchResetProg_tight N σ hσ
  have hσr : StoreValuesLe (uniformEmitLongValueEnvelope N) (uniformEmitScratchResetProg.eval σ) :=
    fun i => (hσrT i).trans (uniformEmitTightEnvelope_le_long_value_envelope N)
  have hidxDecode : uctCursorReg ≤ uniformEmitLongValueEnvelope N ∧
      uctLengthReg ≤ uniformEmitLongValueEnvelope N ∧
      uctDoneReg ≤ uniformEmitLongValueEnvelope N ∧
      uctSavedBoundReg ≤ uniformEmitLongValueEnvelope N := by
    simp only [uctCursorReg, uctLengthReg, uctDoneReg, uctSavedBoundReg,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap]
    omega
  have haddr : addr ≤ uniformEmitTightEnvelope N := by
    have := hσrT uctCursorReg
    rwa [hrelr.cursor] at this
  have hdecode := programBoundedIn_decodeNatProgramAt_of_bounds uctCursorReg uctLengthReg
    uctDoneReg uctSavedBoundReg (uniformEmitLongValueEnvelope N) (uniformEmitScratchResetProg.eval σ)
    (by decide) (by decide) (by decide) hidxDecode
    (by
      rw [hrelr.cursor, hbr]
      simp only [uniformEmitLongValueEnvelope]
      omega)
    (by
      rw [hrelr.length_zero, hbr]
      simpa using uniform_emit_n_le_long_value_envelope N)
  exact program_eval_storeValuesLe _ _ (by
      simp [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
        uniformStartNat, uniformSlackNat, relocateControlGap]; omega)
      hσr hdecode
      (scanFree_decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg)

/-- The temporary cell of the whole iteration body equals the temporary cell after the clause
dispatch on the decoded state: the trailing resets do not touch it. -/
lemma uniformEmitIterBody_tmp_bound_of_rel_body_tmp_eq (N : ℕ) (σ : Store) :
    uniformEmitIterBody.eval σ (uniformMNat N + uctTmpJ) =
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
        uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval
        ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
          (uniformEmitScratchResetProg.eval σ)) (uniformMNat N + uctTmpJ) := by
  have htmpParser : uniformMNat N + uctTmpJ ≠ uctLengthReg ∧
      uniformMNat N + uctTmpJ ≠ uctDoneReg := by
    simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap,
      uctTmpJ, uctLengthReg, uctDoneReg]
    omega
  have htmpScratch : uniformMNat N + uctTmpJ ∉ uniformEmitScratchRegs := by
    simp [uniformEmitScratchRegs, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctTmpJ, uctPolReg, uctVarReg, uctDoneReg, uctLengthReg,
      uctRemainingReg, uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg,
      uctCarryPolReg, uctCarryValReg] at ⊢
    omega
  have hpos : uniformMNat N + uctTmpJ ≠ uctPosPolReg := by
    simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap,
      uctTmpJ, uctPosPolReg]; omega
  have hneg : uniformMNat N + uctTmpJ ≠ uctNegPolReg := by
    simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap,
      uctTmpJ, uctNegPolReg]; omega
  set dispatch := emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg
  set σdec := (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
    (uniformEmitScratchResetProg.eval σ)
  calc
    uniformEmitIterBody.eval σ (uniformMNat N + uctTmpJ) =
        uniformEmitScratchResetProg.eval
          ((emitClauseResetProg uctLengthReg uctDoneReg).eval (dispatch.eval σdec))
          (uniformMNat N + uctTmpJ) := by
      simp [uniformEmitIterBody, uniformEmitIterCoreBody, emitClauseIterProgramAt,
        emitClauseProgramAt, σdec, dispatch, eval_seq]
    _ = (emitClauseResetProg uctLengthReg uctDoneReg).eval (dispatch.eval σdec)
          (uniformMNat N + uctTmpJ) :=
      uniformEmitScratchResetProg_frame _ htmpScratch hpos hneg
    _ = dispatch.eval σdec (uniformMNat N + uctTmpJ) :=
      emitClauseResetProg_frame uctLengthReg uctDoneReg _ htmpParser.1 htmpParser.2

lemma uniformEmitIterBody_tmp_bound_of_rel
    (N K : ℕ) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ)
    (hbase : base + c.lits.length ≤ K)
    (hNK : N ≤ K) :
    uniformEmitIterBody.eval σ (uniformMNat N + uctTmpJ) ≤ K := by
  rw [uniformEmitIterBody_tmp_bound_of_rel_body_tmp_eq]
  exact uniformEmitIterBody_tmp_bound_of_rel_dispatch N K base (c :: cs).length addr c.lits
    ((cs.map encodeClause).flatten ++ tail) pref _ _
    (uniformEmitIterBody_tmp_bound_of_rel_prep N c cs tail pref addr base σ hrel hb)
    (uniformEmitIterBody_tmp_bound_of_rel_decode_store N c cs tail pref addr base σ hrel hb hσ)
    ((decodeNatProgramAt_bound_frame uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg _
      (by decide) (by decide) (by decide)).trans
      ((uniformEmitScratchResetProg_persistent_values σ).2.2.2.2.2.trans hb))
    (fun l hl => hrel.literal_bound c (by simp) l hl) hbase hNK


/-- After the long-branch setup the split-tail relation holds for the remaining literals,
    with the two decoded literals appended to the writer prefix. -/
lemma uniform_emit_dispatch_long_branch_setup_rel
    (N base : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal) (litRest : List NPComplete.SAT.Literal)
    (rest pref : Bits) (addr : ℕ) (σprep : Store)
    (hb1 : l1.var + 1 ≤ N) (hb2 : l2.var + 1 ≤ N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hcapacity : uniformStartNat +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
        l2.var 0 base).length +
      (splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: litRest)).length + 2 <
      uniformMNat N + uctCurJ)
    (hinput : BitsFrom σprep (addr + (l1 :: l2 :: l3 :: litRest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: litRest) rest))
    (habove : uniformMNat N + uctTmpJ < addr + (l1 :: l2 :: l3 :: litRest).length + 1)
    (hstart : uniformStartNat ≤ addr + (l1 :: l2 :: l3 :: litRest).length + 1)
    (hwriter : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σprep uctPosPolReg = 0) (hfresh : σprep uctFreshReg = base)
    (hrem : σprep uctRemainingReg = (l1 :: l2 :: l3 :: litRest).length)
    (hcursor : σprep uctCursorReg = addr + (l1 :: l2 :: l3 :: litRest).length + 1)
    (hbP : σprep uctSavedBoundReg = N) :
    SplitTailEmitRel
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
      (uniformMNat N) uctCurJ uctTmpJ uniformStartNat (base + 1)
      (NPComplete.SAT.Literal.neg base) (l3 :: litRest)
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
        l2.var 0 base) rest
      (addr + (l1 :: l2 :: l3 :: litRest).length + 1 + l1.var + 2 + l2.var + 2)
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg := by
  have hsetupEq := splitTailEmitLongClauseSetupAt_eq uctCurJ uctTmpJ uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg N σprep hbP
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h0 := splitTailEmitLongClauseSetup_eval (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    N base l1 l2 (l3 :: litRest) pref rest
    (addr + (l1 :: l2 :: l3 :: litRest).length + 1) σprep hb1 hb2 hroom hcapacity hinput
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 habove hstart hwriter hpos hfresh hrem hcursor
    uniform_longClauseRegisterSafety.to_split_tail_safety
  rw [← hsetupEq] at h0
  exact h0.1

/-- The long-branch setup leaves the saved bound register untouched. -/
lemma uniform_emit_dispatch_long_branch_setup_bound
    (N base : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal) (litRest : List NPComplete.SAT.Literal)
    (rest pref : Bits) (addr : ℕ) (σprep : Store)
    (hb1 : l1.var + 1 ≤ N) (hb2 : l2.var + 1 ≤ N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hcapacity : uniformStartNat +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
        l2.var 0 base).length +
      (splitTailPayload (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: litRest)).length + 2 <
      uniformMNat N + uctCurJ)
    (hinput : BitsFrom σprep (addr + (l1 :: l2 :: l3 :: litRest).length + 1)
      (splitTailInputBits (l1 :: l2 :: l3 :: litRest) rest))
    (hstart : uniformStartNat ≤ addr + (l1 :: l2 :: l3 :: litRest).length + 1)
    (hwriter : WriterState σprep (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σprep uctPosPolReg = 0) (hfresh : σprep uctFreshReg = base)
    (hrem : σprep uctRemainingReg = (l1 :: l2 :: l3 :: litRest).length)
    (hcursor : σprep uctCursorReg = addr + (l1 :: l2 :: l3 :: litRest).length + 1)
    (hbP : σprep uctSavedBoundReg = N) :
    ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
      uctSavedBoundReg = N := by
  have hsetupEq := splitTailEmitLongClauseSetupAt_eq uctCurJ uctTmpJ uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg N σprep hbP
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hsetupEq]
  have hlow1 : uctSavedBoundReg < uniformStartNat := by
    simp only [uctSavedBoundReg, uniformStartNat, relocateControlGap]
    omega
  have hlow2 : uctSavedBoundReg ≠ uctCursorReg ∧ uctSavedBoundReg ≠ uctPol2Reg ∧
      uctSavedBoundReg ≠ uctVar2Reg ∧ uctSavedBoundReg ≠ uctPol3Reg ∧
      uctSavedBoundReg ≠ uctVar3Reg ∧ uctSavedBoundReg ≠ uctDoneReg ∧
      uctSavedBoundReg ≠ uctCarryPolReg ∧ uctSavedBoundReg ≠ uctCarryValReg ∧
      uctSavedBoundReg ≠ uctPosPolReg ∧ uctSavedBoundReg ≠ uctFreshReg ∧
      uctSavedBoundReg ≠ uctRemainingReg := by
    decide
  rw [splitTailEmitLongClauseSetup_low_frame (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    N base l1 l2 (l3 :: litRest) pref rest
    (addr + (l1 :: l2 :: l3 :: litRest).length + 1) σprep hb1 hb2 hroom hcapacity hinput
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hstart hwriter hpos hfresh hrem hcursor
    uniform_longClauseRegisterSafety.to_split_tail_safety (r := uctSavedBoundReg) hlow1 hlow2]
  exact hbP

/-- The terminal zero-arm of the split-tail loop is bounded by the syntax envelope from any
    long-envelope state with a live writer cell. -/
lemma uniform_emit_dispatch_long_branch_zero
    (N : ℕ) (σ : Store) (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hM : σ 0 = uniformMNat N) (hq0 : σ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitTerminalZeroProg uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg) := by
  have hstatic : uniformMNat N + uctCurJ ≤ uniformEmitLongValueEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitLongValueEnvelope N ∧ uctCurJ ≤
        uniformEmitLongValueEnvelope N ∧ uctTmpJ ≤ uniformEmitLongValueEnvelope N := by
    have h1 := (uniform_emit_writer_layout_le_tight N).2.2.1.trans
      (uniformEmitTightEnvelope_le_long_value_envelope N)
    have h2 := (uniform_emit_writer_layout_le_tight N).2.2.2.trans
      (uniformEmitTightEnvelope_le_long_value_envelope N)
    omega
  have hidx : uctRemainingReg ≤ uniformEmitLongValueEnvelope N ∧
      uctCarryPolReg ≤ uniformEmitLongValueEnvelope N ∧
      uctCarryValReg ≤ uniformEmitLongValueEnvelope N ∧
      uctPosPolReg ≤ uniformEmitLongValueEnvelope N ∧
      uctFreshReg ≤ uniformEmitLongValueEnvelope N ∧
      uctSavedBoundReg ≤ uniformEmitLongValueEnvelope N := by
    simp only [uctRemainingReg, uctCarryPolReg, uctCarryValReg, uctPosPolReg, uctFreshReg,
      uctSavedBoundReg, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  exact programBoundedIn_splitTailEmitTerminalZeroProg_raw_bounds
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    uctSavedBoundReg σ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hstatic hidx hσ hM hq0
    (by simp [uniformEmitSyntaxEnvelope])

/-- The four-assignment prologue of the long branch is bounded by the dispatch envelope in
    every store. -/
lemma uniform_emit_dispatch_long_branch_assign_prologue (N : ℕ) (σ : Store) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))) := by
  simp only [ProgramBoundedIn, ExprBoundedIn, uctRemainingReg, uctLengthReg,
    uctCarryPolReg, uctCarryValReg, uctFreshReg, uctPosPolReg, uniformEmitDispatchEnvelope,
    writerAppendRawSixBound, writerAppendRawThreeBound, writerAppendRawStepBound,
    uniformEmitSyntaxEnvelope, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
    uniformMNat, uniformStartNat, uniformSlackNat]
  omega

/-- The remaining counter after the long-branch setup fits the syntax envelope. -/
lemma uniform_emit_dispatch_long_branch_remaining_value
    (N len : ℕ) (x : Store) (hx : x uctRemainingReg = len + 1) (hlen : len + 2 ≤ N) :
    x uctRemainingReg + 1 ≤ uniformEmitSyntaxEnvelope N := by
  have hNK : N ≤ uniformEmitSyntaxEnvelope N :=
    (uniform_emit_n_le_long_value_envelope N).trans (uniformEmitLongValueEnvelope_le_syntax_envelope N)
  omega

/-- The commit step after the long clause loop is bounded by the dispatch envelope whenever the
    loop's result stays in the long value envelope. -/
lemma uniform_emit_dispatch_long_branch_commit
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitLongValueEnvelope N) τ) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ (emitClauseCommitProg uctOuterReg) := by
  have houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  exact programBoundedIn_emitClauseCommitProg_of_bounds (uniformEmitDispatchEnvelope N)
    uctOuterReg _ (uniformEmitDispatchEnvelope_pos N) houter
    (fun i => (hτ i).trans (uniformEmitLongValueEnvelope_le_dispatch_envelope N))

lemma programBoundedIn_uniform_emit_dispatch_long_branch
    (N inputEnd baseLimit base outer addr : ℕ)
    (l1 l2 l3 : NPComplete.SAT.Literal) (litRest : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr
      (l1 :: l2 :: l3 :: litRest) rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound : ∀ l ∈ l1 :: l2 :: l3 :: litRest, l.var + 1 ≤ N)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base
      (l1 :: l2 :: l3 :: litRest) rest (addr + (l1 :: l2 :: l3 :: litRest).length
        + 1))
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
                  uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
                  uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
                  uctSavedBoundReg)
                (emitClauseCommitProg uctOuterReg)))))) := by
  have hKS : uniformEmitLongValueEnvelope N ≤ uniformEmitSyntaxEnvelope N :=
    uniformEmitLongValueEnvelope_le_syntax_envelope N
  have hKD : uniformEmitLongValueEnvelope N ≤ uniformEmitDispatchEnvelope N :=
    uniformEmitLongValueEnvelope_le_dispatch_envelope N
  obtain ⟨σprep, hunf, hM, hbP, hcursorP, hremP, hposP, hfreshP, hq0P, hinputP, hwriterP,
    hstoreP, hframeP, hstartP, haboveP⟩ :=
    uniform_emit_dispatch_long_prep_state N base outer addr (l1 :: l2 :: l3 :: litRest)
      rest pref σr σdec hprep hstore hsaved
  have hcursorBudget : σprep uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N := by
    rw [hcursorP]
    have h1 := hwin.1
    omega
  have hbase1 : base + 1 ≤ uniformEmitLongValueEnvelope N := by
    have h2 := hwin.2
    simp only [List.length_cons] at h2
    omega
  obtain ⟨hroom, hcapacity⟩ := splitTailPayload_room_of_encodeThreeClausesPayload (uniformMNat N)
    uctCurJ uniformStartNat base l1 l2 l3 litRest pref hprep.room
  have hrelSetup := uniform_emit_dispatch_long_branch_setup_rel N base l1 l2 l3 litRest rest pref
    addr σprep (hbound l1 (by simp)) (hbound l2 (by simp)) hroom hcapacity hinputP haboveP
    hstartP hwriterP hposP hfreshP hremP hcursorP hbP
  have hbSetup := uniform_emit_dispatch_long_branch_setup_bound N base l1 l2 l3 litRest rest pref
    addr σprep (hbound l1 (by simp)) (hbound l2 (by simp)) hroom hcapacity hinputP
    hstartP hwriterP hposP hfreshP hremP hcursorP hbP
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  have hsyn := uniform_splitTailEmitLongClauseSetupAt_syntax N σprep hstoreP hM hbP hq0P
    hcursorBudget
  have hσsetup : StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep) :=
    storeValuesLe_uniform_long_clause_setup_at_tight_of_state N base l1 l2 l3 litRest pref
      rest (addr + (l1 :: l2 :: l3 :: litRest).length + 1) σprep
      (hbound l1 (by simp)) (hbound l2 (by simp)) hinputP hcursorP hposP hfreshP hwriterP
      hstartP hsafety hbP hstoreP hcursorBudget hroom hbase1
  have hzero := uniform_emit_dispatch_long_branch_zero N _ hσsetup hsyn.2.2.1 hsyn.2.2.2.2
  have hremainingValue := uniform_emit_dispatch_long_branch_remaining_value N litRest.length
    ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
    (by rw [hrelSetup.remaining]; simp) (by have := hprep.bound; simp at this; omega)
  have hwinSetup : SplitTailEmitWindow inputEnd baseLimit (base + 1) (l3 :: litRest)
      rest (addr + (l1 :: l2 :: l3 :: litRest).length + 1 + l1.var + 2 + l2.var + 2) :=
    SplitTailEmitWindow.long_setup inputEnd baseLimit base l1 l2 (l3 :: litRest) rest
      (addr + (l1 :: l2 :: l3 :: litRest).length + 1) hwin
  have hraw := uniform_split_tail_emit_step_syntax_bounds_of_rel N (base + 1) inputEnd baseLimit
    (NPComplete.SAT.Literal.neg base) (l3 :: litRest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
      l2.var 0 base) rest
    (addr + (l1 :: l2 :: l3 :: litRest).length + 1 + l1.var + 2 + l2.var + 2)
    _ hrelSetup hwinSetup hbSetup hend hσsetup
  have hpost := storeValuesLe_uniform_splitTailEmitLongClauseProgAt_of_setup_raw N inputEnd
    baseLimit (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: litRest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
      l2.var 0 base) rest
    (addr + (l1 :: l2 :: l3 :: litRest).length + 1 + l1.var + 2 + l2.var + 2) σprep
    ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
    (l3 :: litRest).length rfl hrelSetup.remaining
    (by simp only [List.length_cons]; omega)
    (fun l hl => hbound l (by simp [hl])) hrelSetup hbSetup hσsetup hraw hwinSetup hinputEnd
    hbaseLimit hend
  have hcommit := uniform_emit_dispatch_long_branch_commit N _ hpost
  have hprep4 := uniform_emit_dispatch_long_branch_assign_prologue N σdec
  have hsetupD : ProgramBoundedIn (uniformEmitSyntaxEnvelope N)
      ((Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (.assign uctPosPolReg (.const 0))))).eval σdec)
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
    rw [hunf]
    exact hsyn.1
  rw [← hunf] at hσsetup hzero hremainingValue hrelSetup hbSetup hcommit
  exact programBoundedIn_uniform_emit_dispatch_long_branch_of_reach N inputEnd baseLimit
    (base + 1) (NPComplete.SAT.Literal.neg base) (l3 :: litRest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2)
      l2.var 0 base) rest
    (addr + (l1 :: l2 :: l3 :: litRest).length + 1 + l1.var + 2 + l2.var + 2) σdec
    hprep4 hsetupD hσsetup hzero hremainingValue
    (fun l hl => hbound l (by simp [hl])) hrelSetup hbSetup hwinSetup hinputEnd hbaseLimit
    hend hcommit

/-! Register-level behavior of the long-branch setup on a clause of at most two
    literals. Both decodes consume at most 1 + N cells. The writer append and
    closing assignments leave the cursor and bound in place; subtracting two
    from the remaining counter with truncated subtraction yields zero. The cell
    premise keeps every cell the decodes can read Boolean, which makes the
    writer append's polarity operands well-formed without knowing what was read. -/

/-- The first decode of the short long-branch setup keeps the cursor within one decoded literal,
    the saved bound, a Boolean polarity and the writer state, and frames every other register. -/
lemma uniform_emit_long_clause_setup_at_short_state_decode_first
    (N addr : ℕ) (pref : Bits) (σ τ : Store)
    (hτ : τ = (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
      uctSavedBoundReg).eval σ)
    (hb : σ uctSavedBoundReg = N)
    (hstartAtInput : uniformStartNat ≤ addr)
    (hcell01 : ∀ i, addr ≤ i → i < addr + 2 + 2 * N → σ i ≤ 1)
    (hcursor : σ uctCursorReg = addr)
    (hwriter : WriterState σ (uniformMNat N) uctCurJ uniformStartNat pref) :
    τ uctCursorReg ≤ addr + 1 + N ∧ addr ≤ τ uctCursorReg ∧ τ uctSavedBoundReg = N ∧
    τ uctVar2Reg ≤ N ∧ τ uctPol2Reg ≤ 1 ∧
    (∀ i, addr ≤ i → i < addr + 2 + 2 * N → τ i ≤ 1) ∧
    WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg → r ≠ uctDoneReg → τ r = σ r) := by
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  have haddrBig : 25 ≤ addr := by
    simp only [uniformStartNat, relocateControlGap] at hstartAtInput
    omega
  have hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg →
      r ≠ uctDoneReg → τ r = σ r := by
    intro r h1 h2 h3 h4
    rw [hτ]
    exact decodeLiteralValueProgramAt_frame uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
      uctSavedBoundReg r σ h1 h2 h3 h4
  have hcur : τ uctCursorReg ≤ addr + 1 + N := by
    have h := decodeLiteralValueProgramAt_cursor_le uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hcursor, hb] at h
    rw [hτ]
    exact h
  have hcurGe : addr ≤ τ uctCursorReg := by
    have h := decodeLiteralValueProgramAt_cursor_ge uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide)
    rw [hcursor] at h
    rw [hτ]
    omega
  have hbound : τ uctSavedBoundReg = N := by
    have h := decodeLiteralValueProgramAt_bound_frame uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide) (by decide)
    rw [hτ]
    exact h.trans hb
  have hvar : τ uctVar2Reg ≤ N := by
    have h := decodeLiteralValueProgramAt_var_le uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    rw [hτ]
    exact h.trans hb.le
  have hcells : ∀ i, addr ≤ i → i < addr + 2 + 2 * N → τ i ≤ 1 := by
    intro i hlo hhi
    rw [hframe i (by simp only [uctCursorReg]; omega) (by simp only [uctPol2Reg]; omega)
      (by simp only [uctVar2Reg]; omega) (by simp only [uctDoneReg]; omega)]
    exact hcell01 i hlo hhi
  have hpol : τ uctPol2Reg ≤ 1 := by
    have heq := decodeLiteralValueProgramAt_pol_eq uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide)
    rw [hτ, heq, hcursor]
    exact hcell01 addr (le_refl _) (by omega)
  have hstate : WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref :=
    writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref σ τ
      uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg hwriter hframe
      hsafety.second.nonzero.1 hsafety.second.nonzero.2.1
      hsafety.second.nonzero.2.2.1 hsafety.second.nonzero.2.2.2
      hsafety.second.below.1 hsafety.second.below.2.1
      hsafety.second.below.2.2.1 hsafety.second.below.2.2.2
  exact ⟨hcur, hcurGe, hbound, hvar, hpol, hcells, hstate, hframe⟩

/-- The second decode of the short long-branch setup extends the cursor bound to two decoded
    literals and again preserves the saved bound, polarity and writer state. -/
lemma uniform_emit_long_clause_setup_at_short_state_decode_second
    (N addr : ℕ) (pref : Bits) (τ υ : Store)
    (hυ : υ = (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
      uctSavedBoundReg).eval τ)
    (hcur : τ uctCursorReg ≤ addr + 1 + N) (hcurGe : addr ≤ τ uctCursorReg)
    (hb : τ uctSavedBoundReg = N)
    (hcells : ∀ i, addr ≤ i → i < addr + 2 + 2 * N → τ i ≤ 1)
    (hwriter : WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref) :
    υ uctCursorReg ≤ addr + 2 + 2 * N ∧ υ uctSavedBoundReg = N ∧ υ uctVar3Reg ≤ N ∧
    υ uctPol3Reg ≤ 1 ∧
    WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPol3Reg → r ≠ uctVar3Reg → r ≠ uctDoneReg → υ r = τ r) := by
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  have hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctPol3Reg → r ≠ uctVar3Reg →
      r ≠ uctDoneReg → υ r = τ r := by
    intro r h1 h2 h3 h4
    rw [hυ]
    exact decodeLiteralValueProgramAt_frame uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
      uctSavedBoundReg r τ h1 h2 h3 h4
  have hc := decodeLiteralValueProgramAt_cursor_le uctCursorReg uctPol3Reg uctVar3Reg
    uctDoneReg uctSavedBoundReg τ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hbound := decodeLiteralValueProgramAt_bound_frame uctCursorReg uctPol3Reg uctVar3Reg
    uctDoneReg uctSavedBoundReg τ (by decide) (by decide) (by decide) (by decide)
  have hvar := decodeLiteralValueProgramAt_var_le uctCursorReg uctPol3Reg uctVar3Reg
    uctDoneReg uctSavedBoundReg τ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have heq := decodeLiteralValueProgramAt_pol_eq uctCursorReg uctPol3Reg uctVar3Reg
    uctDoneReg uctSavedBoundReg τ (by decide) (by decide) (by decide)
  rw [hb] at hc hbound hvar
  refine ⟨?_, ?_, ?_, ?_, ?_, hframe⟩
  · rw [hυ]; omega
  · rw [hυ]; exact hbound
  · rw [hυ]; exact hvar
  · rw [hυ, heq]
    exact hcells (τ uctCursorReg) hcurGe (by omega)
  · exact writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref τ υ
      uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg hwriter hframe
      hsafety.third.nonzero.1 hsafety.third.nonzero.2.1
      hsafety.third.nonzero.2.2.1 hsafety.third.nonzero.2.2.2
      hsafety.third.below.1 hsafety.third.below.2.1
      hsafety.third.below.2.2.1 hsafety.third.below.2.2.2


/-- The four closing assignments of the long-branch setup only touch the carry, fresh and
    remaining registers, and the last one truncates the remaining counter by two. -/
lemma uniform_emit_long_clause_setup_at_short_state_closing
    (σw : Store) :
    (∀ r, r ≠ uctCarryPolReg → r ≠ uctCarryValReg → r ≠ uctFreshReg →
      r ≠ uctRemainingReg →
      (Program.seq (.assign uctCarryPolReg (.const 1))
        (.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.seq (.assign uctFreshReg (.add (.reg uctFreshReg) (.const 1)))
            (.seq (.assign uctRemainingReg (.sub (.reg uctRemainingReg) (.const 2)))
              (.skip))))).eval σw r = σw r) ∧
    (Program.seq (.assign uctCarryPolReg (.const 1))
        (.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.seq (.assign uctFreshReg (.add (.reg uctFreshReg) (.const 1)))
            (.seq (.assign uctRemainingReg (.sub (.reg uctRemainingReg) (.const 2)))
              (.skip))))).eval σw uctRemainingReg = σw uctRemainingReg - 2 := by
  constructor
  · intro r h1 h2 h3 h4
    simp [eval_seq, eval_skip, eval_assign, Expr.eval, writeReg, h1, h2, h3, h4]
  · simp [eval_seq, eval_skip, eval_assign, Expr.eval, writeReg, uctCarryPolReg,
      uctCarryValReg, uctFreshReg, uctRemainingReg]


/-- After the writer append and the closing assignments the cursor is within range, the remaining
    counter is zero and the saved bound is intact. -/
lemma uniform_emit_long_clause_setup_at_short_state_finish
    (N base addr : ℕ) (ls : List NPComplete.SAT.Literal) (pref : Bits) (υ : Store)
    (hυcur : υ uctCursorReg ≤ addr + 2 + 2 * N) (hυb : υ uctSavedBoundReg = N)
    (hυvar2 : υ uctVar2Reg ≤ N) (hυvar3 : υ uctVar3Reg ≤ N)
    (hυpol2 : υ uctPol2Reg ≤ 1) (hυpol3 : υ uctPol3Reg ≤ 1)
    (hυstate : WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref)
    (hposυ : υ uctPosPolReg = 0) (hfreshυ : υ uctFreshReg = base)
    (hremυ : υ uctRemainingReg = ls.length) (hlen : ls.length ≤ 2)
    (hwr : uniformStartNat + pref.length + N + N + base + 6 < uniformMNat N + uctCurJ) :
    let σ6 := (Program.seq (.assign uctCarryPolReg (.const 1))
        (.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.seq (.assign uctFreshReg (.add (.reg uctFreshReg) (.const 1)))
            (.seq (.assign uctRemainingReg (.sub (.reg uctRemainingReg) (.const 2)))
              (.skip))))).eval
      ((writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg).eval υ)
    σ6 uctCursorReg ≤ addr + 2 + 2 * N ∧ σ6 uctRemainingReg = 0 ∧
      σ6 uctSavedBoundReg = N := by
  intro σ6
  have hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg :=
    uniform_longClauseRegisterSafety.to_split_tail_safety
  have hframeW : ∀ r, r < uniformStartNat →
      (writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg).eval υ r = υ r := fun r hr =>
    writerAppendThreeRegsProg_frame (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctFreshReg
      (υ uctPol2Reg) (υ uctVar2Reg) (υ uctPol3Reg) (υ uctVar3Reg) 0 base υ
      uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 rfl rfl rfl rfl hposυ hfreshυ
      (by omega) (by omega) (Or.inl rfl)
      hsafety.second.below.2.2.1
      ⟨hsafety.third.below.2.1, hsafety.third.below.2.2.1⟩
      ⟨hsafety.writer_below.2.2.1, hsafety.writer_below.2.2.2.1⟩
      hυstate (by omega) hr
  have hclose := uniform_emit_long_clause_setup_at_short_state_closing
    ((writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg).eval υ)
  have hcurW := hframeW uctCursorReg (by decide)
  have hremW := hframeW uctRemainingReg (by decide)
  have hbW := hframeW uctSavedBoundReg (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [σ6]
    rw [hclose.1 uctCursorReg (by decide) (by decide) (by decide) (by decide), hcurW]
    exact hυcur
  · simp only [σ6]
    rw [hclose.2, hremW, hremυ]
    omega
  · simp only [σ6]
    rw [hclose.1 uctSavedBoundReg (by decide) (by decide) (by decide) (by decide), hbW]
    exact hυb

lemma uniform_emit_long_clause_setup_at_short_state
    (N base : ℕ) (ls : List NPComplete.SAT.Literal) (pref : Bits)
    (addr : ℕ) (σ : Store)
    (hb : σ uctSavedBoundReg = N)
    (hstartAtInput : uniformStartNat ≤ addr)
    (hcell01 : ∀ i, addr ≤ i → i < addr + 2 + 2 * N → σ i ≤ 1)
    (hcursor : σ uctCursorReg = addr)
    (hwriter : WriterState σ (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpos : σ uctPosPolReg = 0) (hfresh : σ uctFreshReg = base)
    (hremaining : σ uctRemainingReg = ls.length)
    (hlen : ls.length ≤ 2)
    (hwr : uniformStartNat + pref.length + N + N + base + 6 <
      uniformMNat N + uctCurJ) :
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
      uctCursorReg ≤ addr + 2 + 2 * N ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
      uctRemainingReg = 0 ∧
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
      uctSavedBoundReg = N := by
  obtain ⟨hτcur, hτcurGe, hτb, hτvar2, hτpol2, hτcells, hτstate, hτframe⟩ :=
    uniform_emit_long_clause_setup_at_short_state_decode_first N addr pref σ
      ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ) rfl hb hstartAtInput hcell01 hcursor hwriter
  obtain ⟨hυcur, hυb, hυvar3, hυpol3, hυstate, hυframe⟩ :=
    uniform_emit_long_clause_setup_at_short_state_decode_second N addr pref
      ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ)
      ((decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
        uctSavedBoundReg).eval ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg
          uctVar2Reg uctDoneReg uctSavedBoundReg).eval σ)) rfl hτcur hτcurGe hτb hτcells
      hτstate
  have hυvar2 := hυframe uctVar2Reg (by decide) (by decide) (by decide) (by decide)
  have hυpol2 := hυframe uctPol2Reg (by decide) (by decide) (by decide) (by decide)
  have hposυ := (hυframe uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans
    ((hτframe uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans hpos)
  have hfreshυ := (hυframe uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans
    ((hτframe uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans hfresh)
  have hremυ := (hυframe uctRemainingReg (by decide) (by decide) (by decide) (by decide)).trans
    ((hτframe uctRemainingReg (by decide) (by decide) (by decide) (by decide)).trans
      hremaining)
  have hfinish := uniform_emit_long_clause_setup_at_short_state_finish N base addr ls pref _
    hυcur hυb (by omega) hυvar3 (by omega) hυpol3 hυstate hposυ hfreshυ hremυ hlen hwr
  simpa only [splitTailEmitLongClauseSetupAt, eval_seq, eval_skip] using hfinish

/-- The zero-counter proof uses one syntax layout and a larger dispatch budget. -/
lemma uniformEmitSyntaxEnvelope_uniformEmitDispatchEnvelope_bounds
    (N : ℕ) :
    (uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧
      uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uctTmpJ ≤ uniformEmitSyntaxEnvelope N) ∧
    (writerAppendRawThreeBound (uniformEmitSyntaxEnvelope N) + 1 ≤
        uniformEmitDispatchEnvelope N ∧
      2 ≤ uniformEmitDispatchEnvelope N ∧ 1 ≤ uniformEmitDispatchEnvelope N) ∧
    (uctCursorReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctVarReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctDoneReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctRemainingReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol2Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctVar2Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol3Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctVar3Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctCarryPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctCarryValReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPosPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctFreshReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctSavedBoundReg ≤ uniformEmitSyntaxEnvelope N) ∧
    uctRemainingReg ≤ uniformEmitDispatchEnvelope N := by
  have henv : 24 ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧
      uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧ uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧
      writerAppendRawThreeBound (uniformEmitSyntaxEnvelope N) + 1 ≤
        uniformEmitDispatchEnvelope N ∧
      2 ≤ uniformEmitDispatchEnvelope N ∧ 1 ≤ uniformEmitDispatchEnvelope N := by
    have hKD := uniform_emit_raw_three_bound_syntax_le_dispatch_envelope N
    have hlt := uniform_emit_writer_layout_le_tight N
    have htl := uniformEmitTightEnvelope_le_long_value_envelope N
    have htlS := uniformEmitLongValueEnvelope_le_syntax_envelope N
    simp only [uniformEmitSyntaxEnvelope, uniformEmitDispatchEnvelope,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, uctCurJ, uctTmpJ, writerAppendRawThreeBound,
      writerAppendRawSixBound, writerAppendRawStepBound, relocateControlGap] at hKD ⊢
    omega
  obtain ⟨h24, hMcur, hMtmp, hcurJK, htmpJK, hbudget, hB2, hB1⟩ := henv
  have hregs : uctCursorReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPolReg ≤ uniformEmitSyntaxEnvelope N ∧ uctVarReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctDoneReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctRemainingReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol2Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctVar2Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol3Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctVar3Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctCarryPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctCarryValReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPosPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctFreshReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctSavedBoundReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctRemainingReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg,
      uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg,
      uctPosPolReg, uctFreshReg, uctSavedBoundReg, uniformEmitSyntaxEnvelope,
      uniformEmitDispatchEnvelope, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
      uniformMNat, uniformStartNat, uniformSlackNat, uctCurJ, writerAppendRawThreeBound,
      writerAppendRawSixBound, writerAppendRawStepBound, relocateControlGap] at h24 hB2 ⊢
    omega
  obtain ⟨hcK, hpK, hvK, hdK, hremK, hp2K, hv2K, hp3K, hv3K, hcpK, hcvK, hposK,
    hfreshK, hboundK, hremD⟩ := hregs
  exact ⟨⟨hMcur, hMtmp, hcurJK, htmpJK⟩, ⟨hbudget, hB2, hB1⟩,
    ⟨hcK, hpK, hvK, hdK, hremK, hp2K, hv2K, hp3K, hv3K, hcpK, hcvK, hposK,
      hfreshK, hboundK⟩, hremD⟩

/-- The raw zero, terminal and intermediate bounds cover one zero-counter iteration. -/
lemma programBoundedIn_uniform_split_tail_emit_prog_at_of_remaining_zero_branch_bounds
    (K B M : ℕ) (σ : Store)
    (hstatic : M + uctCurJ ≤ K ∧ M + uctTmpJ ≤ K ∧ uctCurJ ≤ K ∧ uctTmpJ ≤ K)
    (hidx : uctCursorReg ≤ K ∧ uctPolReg ≤ K ∧ uctVarReg ≤ K ∧ uctDoneReg ≤ K ∧
      uctRemainingReg ≤ K ∧ uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧ uctPol3Reg ≤ K ∧
      uctVar3Reg ≤ K ∧ uctCarryPolReg ≤ K ∧ uctCarryValReg ≤ K ∧ uctPosPolReg ≤ K ∧
      uctFreshReg ≤ K ∧ uctSavedBoundReg ≤ K)
    (hctrl : ∀ r : ℕ, r ≤ 24 → M + uctCurJ ≠ r ∧ M + uctTmpJ ≠ r)
    (hstore : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + uctCurJ) ≠ 0)
    (hcursor : σ uctCursorReg + 1 + σ uctSavedBoundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg
      uctDoneReg uctSavedBoundReg).eval σ uctCursorReg + 1 +
      (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg
        uctDoneReg uctSavedBoundReg).eval σ uctSavedBoundReg ≤ K)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitTerminalZeroProg uctCurJ uctTmpJ 0 0 0 0 uctRemainingReg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    ProgramBoundedIn B σ
      (splitTailEmitTerminalOneProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctCarryPolReg uctCarryValReg
        uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    ProgramBoundedIn B σ
      (splitTailEmitTerminalTwoProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    ProgramBoundedIn B σ
      (splitTailEmitIntermediateProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg) := by
  obtain ⟨hMcur, hMtmp, hcurJK, htmpJK⟩ := hstatic
  obtain ⟨hcK, hpK, hvK, hdK, hremK, hp2K, hv2K, hp3K, hv3K, hcpK, hcvK, hposK,
    hfreshK, hboundK⟩ := hidx
  have hwriterBudget : writerAppendRawThreeBound K ≤ B := by omega
  have hzero := programBoundedIn_splitTailEmitTerminalZeroProg_raw_bounds K B M uctCurJ
    uctTmpJ uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    uctSavedBoundReg σ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    ⟨hMcur, hMtmp, hcurJK, htmpJK⟩
    ⟨hremK, hcpK, hcvK, hposK, hfreshK, hboundK⟩ hstore hM hq0 hwriterBudget
  have hone := programBoundedIn_splitTailEmitTerminalOneProgAt_raw_bounds K B M uctCurJ
    uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 ⟨hMcur, hMtmp, hcurJK, htmpJK⟩
    ⟨hcK, hpK, hvK, hdK, hremK, hp2K, hv2K, hcpK, hcvK, hposK, hfreshK, hboundK⟩
    (by simp only [uctCursorReg, uctPol2Reg, uctVar2Reg, uctDoneReg, uctSavedBoundReg]; decide)
    (by simp only [uctCursorReg, uctPol2Reg, uctVar2Reg, uctDoneReg]; decide)
    ⟨(hctrl uctCursorReg (by decide)).1, (hctrl uctPol2Reg (by decide)).1,
      (hctrl uctVar2Reg (by decide)).1, (hctrl uctDoneReg (by decide)).1⟩
    hstore hM hq0 hcursor hwriterBudget
  have htwo := programBoundedIn_splitTailEmitTerminalTwoProgAt_raw_bounds K B M uctCurJ
    uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg
    uctFreshReg uctSavedBoundReg σ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    ⟨hMcur, hMtmp, hcurJK, htmpJK⟩
    ⟨hcK, hpK, hvK, hdK, hremK, hp2K, hv2K, hp3K, hv3K, hcpK, hcvK, hposK, hfreshK,
      hboundK⟩
    (by simp only [uctCursorReg, uctPol2Reg, uctVar2Reg, uctDoneReg, uctSavedBoundReg]; decide)
    (by simp only [uctCursorReg, uctPol3Reg, uctVar3Reg, uctDoneReg, uctSavedBoundReg]; decide)
    (by simp only [uctCursorReg, uctPol2Reg, uctVar2Reg, uctDoneReg]; decide)
    (by simp only [uctCursorReg, uctPol3Reg, uctVar3Reg, uctDoneReg]; decide)
    ⟨(hctrl uctCursorReg (by decide)).1, (hctrl uctPol2Reg (by decide)).1,
      (hctrl uctVar2Reg (by decide)).1, (hctrl uctDoneReg (by decide)).1⟩
    ⟨(hctrl uctCursorReg (by decide)).1, (hctrl uctPol3Reg (by decide)).1,
      (hctrl uctVar3Reg (by decide)).1, (hctrl uctDoneReg (by decide)).1⟩
    hstore hM hq0 hcursor hcursor2 hwriterBudget
  have hinter := programBoundedIn_splitTailEmitIntermediateProgAt_raw_bounds K B M uctCurJ
    uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 ⟨hMcur, hMtmp, hcurJK, htmpJK⟩
    ⟨hcK, hpK, hvK, hdK, hremK, hcpK, hcvK, hposK, hfreshK, hboundK⟩
    (by simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctSavedBoundReg]; decide)
    (by simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg]; decide)
    ⟨(hctrl uctCursorReg (by decide)).1, (hctrl uctPolReg (by decide)).1,
      (hctrl uctVarReg (by decide)).1, (hctrl uctDoneReg (by decide)).1⟩
    hstore hM hq0 hcursor (by decide) (by decide)
    ((hctrl uctCarryValReg (by decide)).1).symm
    ((hctrl uctFreshReg (by decide)).1).symm hbudget
  exact ⟨hzero, hone, htwo, hinter⟩

/-! The split-tail loop at a state whose remaining counter is already zero: the
    runtime takes the zero-termination arm, and the single inspected `forN`
    iteration reduces to the step program at the entry state, which the raw
    branch bounds cover at the syntax/dispatch envelope pair. -/

lemma programBoundedIn_uniform_splitTailEmitProgAt_of_remaining_zero
    (N : ℕ) (σ : Store)
    (hstore : StoreValuesLe (uniformEmitSyntaxEnvelope N) σ)
    (hM : σ 0 = uniformMNat N)
    (hq0 : σ (uniformMNat N + uctCurJ) ≠ 0)
    (hcursor : σ uctCursorReg + 1 + σ uctSavedBoundReg ≤ uniformEmitSyntaxEnvelope N)
    (hcursor2 : (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg
        uctDoneReg uctSavedBoundReg).eval σ uctCursorReg + 1 +
      (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ uctSavedBoundReg ≤ uniformEmitSyntaxEnvelope N)
    (hremaining : σ uctRemainingReg = 0) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
      (splitTailEmitProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
  obtain ⟨hstatic, hbudgets, hidx, hremD⟩ :=
    uniformEmitSyntaxEnvelope_uniformEmitDispatchEnvelope_bounds N
  obtain ⟨hbudget, hB2, hB1⟩ := hbudgets
  have hctrl : ∀ r : ℕ, r ≤ 24 → uniformMNat N + uctCurJ ≠ r ∧
      uniformMNat N + uctTmpJ ≠ r := by
    intro r hr
    exact ⟨(uniform_emit_dispatch_writer_cell_ne N r hr).1.symm,
      (uniform_emit_dispatch_writer_cell_ne N r hr).2.symm⟩
  obtain ⟨hzeroB, honeB, htwoB, hinterB⟩ :=
    programBoundedIn_uniform_split_tail_emit_prog_at_of_remaining_zero_branch_bounds
      (uniformEmitSyntaxEnvelope N) (uniformEmitDispatchEnvelope N) (uniformMNat N) σ
      hstatic hidx hctrl hstore hM hq0 hcursor hcursor2 hbudget
  have hremainingValue : σ uctRemainingReg + 1 ≤ uniformEmitDispatchEnvelope N := by
    rw [hremaining]
    exact hB1
  have hstep := programBoundedIn_splitTailEmitStepProgAt_raw_of_branches
    (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ
    hB2 hremD honeB htwoB hinterB
  refine programBoundedIn_splitTailEmitProgAt_raw_of_step
    (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ
    hB1 hremD hremainingValue hzeroB ?_
  intro m hm
  rw [hremaining] at hm
  have hm0 : m = 0 := by omega
  subst hm0
  simp only [loopEval]
  exact hstep


/-- Room above the long value envelope for two more decodes, at the syntax envelope. -/
lemma uniformEmitLongValueEnvelope_le_uniformEmitSyntaxEnvelope (N : ℕ) :
    uniformEmitLongValueEnvelope N + 2 + 2 * N ≤ uniformEmitSyntaxEnvelope N := by
  have hNle : N ≤ uniformEmitLongValueEnvelope N := uniform_emit_n_le_long_value_envelope N
  simp only [uniformEmitSyntaxEnvelope, uniformEmitLongValueEnvelope,
    uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat, uctCurJ,
    writerAppendRawThreeBound, writerAppendRawStepBound, relocateControlGap] at hNle ⊢
  omega

/-- The second decode started after the long-clause setup stays within the syntax envelope. -/
lemma decodeLiteralValueProgramAt_eval_le_uniformEmitSyntaxEnvelope
    (N : ℕ) (x : Store) (hb : x uctSavedBoundReg = N)
    (hx : x uctCursorReg + 2 + 2 * N ≤ uniformEmitSyntaxEnvelope N) :
    (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg
        uctDoneReg uctSavedBoundReg).eval x uctCursorReg + 1 +
      (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval x uctSavedBoundReg ≤ uniformEmitSyntaxEnvelope N := by
  have hc := decodeLiteralValueProgramAt_cursor_le uctCursorReg uctPol2Reg uctVar2Reg
    uctDoneReg uctSavedBoundReg x
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hb' := decodeLiteralValueProgramAt_bound_frame uctCursorReg uctPol2Reg uctVar2Reg
    uctDoneReg uctSavedBoundReg x (by decide) (by decide) (by decide) (by decide)
  rw [hb] at hc hb'
  omega

/-- After the long-clause setup of a short clause, the zero-remaining split-tail loop is
bounded at the dispatch envelope, and so is the setup itself. -/
lemma programBoundedIn_uniform_emit_dispatch_long_branch_short_loop
    (N : ℕ) (σprep : Store)
    (hstoreP : StoreValuesLe (uniformEmitLongValueEnvelope N) σprep)
    (hM : σprep 0 = uniformMNat N) (hbP : σprep uctSavedBoundReg = N)
    (hq0P : σprep (uniformMNat N + uctCurJ) ≠ 0)
    (hcursorBudget : σprep uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hbS : (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep
      uctSavedBoundReg = N)
    (hremS : (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep
      uctRemainingReg = 0)
    (hx : (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep
      uctCursorReg + 2 + 2 * N ≤ uniformEmitSyntaxEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σprep
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    ProgramBoundedIn (uniformEmitDispatchEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
      (splitTailEmitProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
  have hsyn := uniform_splitTailEmitLongClauseSetupAt_syntax N σprep hstoreP hM hbP hq0P
    hcursorBudget
  refine ⟨programBoundedIn_of_le (uniformEmitSyntaxEnvelope_le_dispatch_envelope N) hsyn.1, ?_⟩
  exact programBoundedIn_uniform_splitTailEmitProgAt_of_remaining_zero N _
    hsyn.2.1 hsyn.2.2.1 hsyn.2.2.2.2 (by omega)
    (decodeLiteralValueProgramAt_eval_le_uniformEmitSyntaxEnvelope N _ hbS hx) hremS

/-- The long-clause program and the commit step that follows it are bounded at the dispatch
envelope, given the bounded setup and zero-remaining loop. -/
lemma programBoundedIn_uniform_emit_dispatch_long_branch_short_tail
    (N : ℕ) (σprep : Store)
    (hstoreP : StoreValuesLe (uniformEmitLongValueEnvelope N) σprep)
    (hsetupD : ProgramBoundedIn (uniformEmitDispatchEnvelope N) σprep
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg))
    (hloop : ProgramBoundedIn (uniformEmitDispatchEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
      (splitTailEmitProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σprep
      (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) ∧
    ProgramBoundedIn (uniformEmitDispatchEnvelope N)
      ((splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σprep)
      (emitClauseCommitProg uctOuterReg) := by
  have hlong := programBoundedIn_splitTailEmitLongClauseProgAt_of_parts
    (uniformEmitDispatchEnvelope N) uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σprep hsetupD hloop
  have hstorePrepD : StoreValuesLe (uniformEmitDispatchEnvelope N) σprep := fun i =>
    (hstoreP i).trans (uniformEmitLongValueEnvelope_le_dispatch_envelope N)
  have houterD : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  refine ⟨hlong, programBoundedIn_emitClauseCommitProg_of_bounds (uniformEmitDispatchEnvelope N)
    uctOuterReg _ (uniformEmitDispatchEnvelope_pos N) houterD ?_⟩
  exact program_eval_storeValuesLe σprep _ (uniformEmitDispatchEnvelope_pos N) hstorePrepD hlong
    (scanFree_splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)

/-! The unselected long branch on a short clause (at most two literals): the
    preparation assignments, the split-tail setup, and the zero-remaining loop
    are all delivered at the dispatch envelope.  The read-side premise keeps the
    two garbage decodes Boolean; the writer-room premise bounds the emission of
    the three writer literals the setup would append. -/

lemma programBoundedIn_uniform_emit_dispatch_long_branch_short
    (N inputEnd baseLimit base outer addr : ℕ)
    (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hlen : ls.length ≤ 2)
     (hcell01 : ∀ i, addr + ls.length + 1 ≤ i →
       i < addr + ls.length + 1 + 2 + 2 * N → σdec i ≤ 1)
     (hwin : SplitTailEmitWindow inputEnd baseLimit base ls rest (addr + ls.length + 1))
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hwr : uniformStartNat + pref.length + N + N + base + 6 <
      uniformMNat N + uctCurJ) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq (.assign uctRemainingReg (.reg uctLengthReg))
        (Program.seq (.assign uctCarryPolReg (.const 1))
          (Program.seq (.assign uctCarryValReg (.reg uctFreshReg))
            (Program.seq (.assign uctPosPolReg (.const 0))
              (Program.seq
                (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
                  uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
                  uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
                  uctSavedBoundReg)
                (emitClauseCommitProg uctOuterReg)))))) := by
  have hroom := uniformEmitLongValueEnvelope_le_uniformEmitSyntaxEnvelope N
  obtain ⟨σprep, hunf, hM, hbP, hcursorP, hremP, hposP, hfreshP, hq0P, hinputP, hwriterP,
    hstoreP, hframeP, hstartP, haboveP⟩ :=
    uniform_emit_dispatch_long_prep_state N base outer addr ls rest pref σr σdec hprep hstore
      hsaved
  have haddrBig : 25 ≤ addr + ls.length + 1 := by
    simp only [uniformStartNat, relocateControlGap] at hstartP
    omega
  have hcellP : ∀ i, addr + ls.length + 1 ≤ i →
      i < addr + ls.length + 1 + 2 + 2 * N → σprep i ≤ 1 := by
    intro i hlo hhi
    rw [hframeP i (by have := haddrBig; simp only [uctRemainingReg]; omega)
      (by have := haddrBig; simp only [uctCarryPolReg]; omega)
      (by have := haddrBig; simp only [uctCarryValReg]; omega)
      (by have := haddrBig; simp only [uctPosPolReg]; omega)]
    exact hcell01 i hlo hhi
  obtain ⟨hcurS, hremS, hbS⟩ :=
    uniform_emit_long_clause_setup_at_short_state N base ls pref (addr + ls.length + 1) σprep
      hbP hstartP hcellP hcursorP hwriterP hposP hfreshP hremP hlen hwr
  have haddrLE : addr + ls.length + 1 ≤ inputEnd := by
    have h1 := hwin.1
    omega
  have hcursorBudget : σprep uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N := by
    rw [hcursorP]
    omega
  obtain ⟨hsetupD, hloop⟩ := programBoundedIn_uniform_emit_dispatch_long_branch_short_loop N
    σprep hstoreP hM hbP hq0P hcursorBudget hbS hremS (by omega)
  obtain ⟨hlong, hcommit⟩ :=
    programBoundedIn_uniform_emit_dispatch_long_branch_short_tail N σprep hstoreP hsetupD hloop
  have hpre4 := uniform_emit_dispatch_long_branch_assign_prologue N σdec
  rw [← hunf] at hlong hcommit
  simp only [eval_seq] at hlong hcommit
  rcases hpre4 with ⟨h1, h2, h3, h4⟩
  exact programBoundedIn_uniform_emit_dispatch_long_prologue
    (uniformEmitDispatchEnvelope N) σdec
    (.assign uctRemainingReg (.reg uctLengthReg))
    (.assign uctCarryPolReg (.const 1))
    (.assign uctCarryValReg (.reg uctFreshReg))
    (.assign uctPosPolReg (.const 0))
    (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)
    (emitClauseCommitProg uctOuterReg) h1 h2 h3 h4
    (by simpa [eval_seq] using hlong) (by simpa [eval_seq] using hcommit)

end NPComplete.CookLevin

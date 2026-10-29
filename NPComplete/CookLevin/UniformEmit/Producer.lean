module

public import NPComplete.CookLevin.UniformEmit.ProducerRelation

/-!
# Producer loop invariants

At each outer iteration the writer relation and persistent registers must survive clause emission.
This module proves those loop and frame invariants so startup state and final correctness can compose
without repeating per-clause reasoning.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral encodeThreeCNF encodeThreeClause)


/-! ## Clause loop, ABI suffix, and the top-level producer theorem -/

open NPComplete.RAMToTM.Generic (ReductionOutput outAddrCell outLenCell)

def uniformProducerResetStore (φ : CNF) : Store :=
  let bits := encodeCNF φ
  let σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  let σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  let σp := uniformPostDecodeStatsProg.eval σd
  let σs := uniformSaveBoundProg.eval σp
  let σa := uniformSetArenaProg.eval σs
  let σst :=
    (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa
  let σx := uniformEmitAuxInitProg.eval σst
  let σf := uniformFreshFromMaxProg.eval σx
  uniformEmitResetProg.eval σf

lemma uniform_cur_j_bounds : 1 ≤ uctCurJ ∧ uctCurJ < uctTmpJ := by
  simp [uctCurJ, uctTmpJ]

lemma encodeThreeCNF_eq_header_payload (φ : CNF) :
    encodeThreeCNF (toThreeCNF φ) =
      encodeNat (toThreeCNF φ).numVars ++
        encodeNat (toThreeCNF φ).clauses.length ++
        encodeThreeClausesPayload (toThreeCNF φ).clauses := by
  simp [encodeThreeCNF, encodeList, encodeThreeClausesPayload]

lemma uniform_producer_pref_eq (φ : CNF) :
    encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length ++
        encodeThreeClausesPayload (clausesToThree (cnfVarBound φ) φ.clauses).1 =
      encodeThreeCNF (toThreeCNF φ) := by
  rw [clausesToThree_toThreeCNF, encodeThreeCNF_eq_header_payload]

lemma uniform_emit_bound_reg_ok :
    EmitClauseBoundRegOk uctSavedBoundReg uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg := by
  refine ⟨?_, by decide, by decide, by decide⟩
  simp [uctSavedBoundReg, uniformStartNat, relocateControlGap, uctCursorReg, uctPolReg,
    uctVarReg, uctDoneReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
    uctPol3Reg, uctCarryPolReg, uctCarryValReg]
  exact
    { below := by decide
      ne_cursor := by decide
      ne_pol := by decide
      ne_var := by decide
      ne_done := by decide
      ne_remaining := by decide
      ne_pol2 := by decide
      ne_var2 := by decide
      ne_pol3 := by decide
      ne_var3 := by decide
      ne_carry_pol := by decide
      ne_carry_val := by decide
      ne_pos_pol := by decide
      ne_fresh := by decide }

lemma uniformEmitIterBody_eval_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    ∃ τ, uniformEmitIterBody.eval σ = τ ∧
      CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
        (clauseToThree base c.lits).2 cs tail
        (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
        (addr + (encodeList encodeLiteral c.lits).length) τ ∧
      τ uctSavedBoundReg = N := by
  let σr := uniformEmitScratchResetProg.eval σ
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hbr : σr uctSavedBoundReg = N := by
    exact (uniformEmitScratchResetProg_frame σ
      (r := uctSavedBoundReg)
      (by simp [uniformEmitScratchRegs, uctSavedBoundReg, uctPolReg, uctVarReg,
        uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
        uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg])
      (by decide) (by decide)).trans hb
  obtain ⟨τ, hτ, hrelτ⟩ := cnfEmitRel_cons_step
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
    base c cs tail pref addr σr uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hrelr
  have hat := emitClauseIterProgramAt_eval_of_rel
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base c cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr hbr uniform_emit_bound_reg_ok
  have hcore : uniformEmitIterCoreBody.eval σr = τ := by
    simpa [uniformEmitIterCoreBody] using hat.trans hτ.symm
  have hframe := emitClauseIterProgram_bound_frame_of_rel
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base c cs tail pref addr σr uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hrelr uniform_emit_bound_reg_ok
  have hboundτ : τ uctSavedBoundReg = N := by
    rw [hτ]
    exact hframe.trans hbr
  let σe := uniformEmitScratchResetProg.eval τ
  have hrelE := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N (clauseToThree base c.lits).2
    cs tail (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
    (addr + (encodeList encodeLiteral c.lits).length) τ hrelτ
  have hbe : σe uctSavedBoundReg = N := by
    exact (uniformEmitScratchResetProg_frame τ
      (r := uctSavedBoundReg)
      (by simp [uniformEmitScratchRegs, uctSavedBoundReg, uctPolReg, uctVarReg,
        uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
        uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg])
      (by decide) (by decide)).trans hboundτ
  have hτeq : uniformEmitIterBody.eval σ = σe := by
    simp [uniformEmitIterBody, σr, σe, eval_seq, hcore]
  refine ⟨σe, hτeq, hrelE, hbe⟩

/-! ## High frame of one outer iteration body

Every cell above `M + tmpJ` survives a clause emission untouched.  The writer
only appends below the cursor cell, the parsers only advance low control
registers, and the closing scratch reset only touches registers below 25.
This is what lets the input tail's zero cells and any region above the
workspace be carried through the outer loop as a separate invariant. -/

lemma uniformEmitScratchRegs_mem_le (r : ℕ) (hr : r ∈ uniformEmitScratchRegs) :
    r ≤ 20 := by
  simp [uniformEmitScratchRegs, uctPolReg, uctVarReg, uctDoneReg, uctLengthReg,
    uctRemainingReg, uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg,
    uctCarryValReg] at hr
  omega

lemma uniformMNat_ge_25 (N : ℕ) : 25 ≤ uniformMNat N := by
  have h := uniformAddrNat_ge_start N
  simp [uniformAddrNat, uniformAddrOffset, uniformMNat, uniformStartNat,
    uniformSlackNat, relocateControlGap] at h ⊢
  omega

/-- Assemble the outer body's post-state from a clause-emitter postcondition:
the emitted state passes through the closing scratch reset, keeps the saved
bound, and every cell above `M + tmpJ` is unchanged from the iteration-start
state. -/
lemma uniformEmitIterBody_result_of_post
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits) (addr base : ℕ)
    (σ τ₀ : Store)
    (hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N)
    (hrelr : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr (uniformEmitScratchResetProg.eval σ))
    (hpost : CNFEmitIterPost (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base c cs tail
      pref addr (uniformEmitScratchResetProg.eval σ) τ₀)
    (hAt : (emitClauseIterProgramAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ) =
      (emitClauseIterProgram uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
      uctFreshReg uctOuterReg N N).eval (uniformEmitScratchResetProg.eval σ)) :
    ∃ τ, uniformEmitIterBody.eval σ = τ ∧
      CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
        (clauseToThree base c.lits).2 cs tail
        (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
        (addr + (encodeList encodeLiteral c.lits).length) τ ∧
      τ uctSavedBoundReg = N ∧
      (∀ r, uniformMNat N + uctTmpJ < r → τ r = σ r) := by
  have hτ₀eq : τ₀ = (emitClauseIterProgram uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
      uctFreshReg uctOuterReg N N).eval (uniformEmitScratchResetProg.eval σ) :=
    cnfEmitIterPost_eval (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base c cs tail pref
      addr (uniformEmitScratchResetProg.eval σ) τ₀ hpost
  have hcore : uniformEmitIterCoreBody.eval (uniformEmitScratchResetProg.eval σ) = τ₀ := by
    unfold uniformEmitIterCoreBody
    rw [hAt]
    exact hτ₀eq.symm
  have hboundτ₀ : τ₀ uctSavedBoundReg = N := by
    rw [hτ₀eq, emitClauseIterProgram_bound_frame_of_rel (uniformMNat N) uctCurJ
      uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
      uctOuterReg uctSavedBoundReg N N base c cs tail pref addr
      (uniformEmitScratchResetProg.eval σ) uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
      hrelr uniform_emit_bound_reg_ok]
    exact hbr
  have hnext := cnfEmitRel_step_of_iter_post_core (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg
    uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
    uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base c cs
    tail pref addr (uniformEmitScratchResetProg.eval σ) τ₀ hrelr hpost
  have hrelE := uniformEmitScratchResetProg_cnfEmitRel (uniformMNat N) uctCurJ
    uctTmpJ N N (clauseToThree base c.lits).2 cs tail
    (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
    (addr + (encodeList encodeLiteral c.lits).length) τ₀ hnext
  have hsaved : (uniformEmitScratchResetProg.eval τ₀) uctSavedBoundReg = N :=
    (uniformEmitScratchResetProg_frame τ₀ (r := uctSavedBoundReg)
      (by simp [uniformEmitScratchRegs, uctSavedBoundReg, uctPolReg, uctVarReg,
        uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
        uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg])
      (by decide) (by decide)).trans hboundτ₀
  refine ⟨uniformEmitScratchResetProg.eval τ₀, ?_, hrelE, hsaved, ?_⟩
  · rw [uniformEmitIterBody, eval_seq, eval_seq, hcore]
  · intro r hr
    have hr25 : 25 ≤ r := (uniformMNat_ge_25 N).trans (by omega)
    have hrnot : r ∉ uniformEmitScratchRegs := by
      intro hmem
      have := uniformEmitScratchRegs_mem_le r hmem
      omega
    calc
      (uniformEmitScratchResetProg.eval τ₀) r = τ₀ r :=
        uniformEmitScratchResetProg_frame τ₀ hrnot (by simp [uctPosPolReg]; omega)
          (by simp [uctNegPolReg]; omega)
      _ = (uniformEmitScratchResetProg.eval σ) r := hpost.frame r hr
      _ = σ r := uniformEmitScratchResetProg_frame σ hrnot (by simp [uctPosPolReg]; omega)
          (by simp [uctNegPolReg]; omega)

/-- Conclusion of the framed outer-iteration step, named so that each clause-shape case
can be proved separately. -/
def UniformEmitIterBodyFrameGoal
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store) : Prop :=
  ∃ τ, uniformEmitIterBody.eval σ = τ ∧
    CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
      (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ ∧
    τ uctSavedBoundReg = N ∧
    (∀ r, uniformMNat N + uctTmpJ < r → τ r = σ r)

/-- The reset-then-emit preparation shared by every clause shape: the reset store satisfies the
relation, keeps the saved bound, and the concrete emitter agrees with the abstract one. -/
lemma uniformEmitIterBody_eval_frame_of_rel_prepared
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr (uniformEmitScratchResetProg.eval σ) ∧
    (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N ∧
    (emitClauseIterProgramAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ) =
      (emitClauseIterProgram uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
      uctFreshReg uctOuterReg N N).eval (uniformEmitScratchResetProg.eval σ) := by
  have hrelr := uniformEmitScratchResetProg_cnfEmitRel
    (uniformMNat N) uctCurJ uctTmpJ N N base (c :: cs) tail pref addr σ hrel
  have hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with
      ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  exact ⟨hrelr, hbr, emitClauseIterProgramAt_eval_of_rel (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg
    uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
    uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    uctSavedBoundReg N N base c cs tail pref addr
    (uniformEmitScratchResetProg.eval σ) uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hrelr hbr uniform_emit_bound_reg_ok⟩

lemma uniformEmitIterBody_eval_frame_of_rel_nil
    (N : ℕ) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    UniformEmitIterBodyFrameGoal N (⟨[]⟩ : Clause) cs tail pref addr base σ := by
  obtain ⟨hrelr, hbr, hAt⟩ := uniformEmitIterBody_eval_frame_of_rel_prepared N _ cs tail pref
    addr base σ hrel hb
  obtain ⟨τ₀, hpost⟩ := cnfEmitRel_nil_step_of_iter_post (uniformMNat N) uctCurJ
    uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
    uctOuterReg N N base cs tail pref addr (uniformEmitScratchResetProg.eval σ)
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hrelr
  exact uniformEmitIterBody_result_of_post N (⟨[]⟩ : Clause) cs tail pref addr
    base σ τ₀ hbr hrelr hpost hAt

lemma uniformEmitIterBody_eval_frame_of_rel_one
    (N : ℕ) (l : Literal) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    UniformEmitIterBodyFrameGoal N (⟨[l]⟩ : Clause) cs tail pref addr base σ := by
  obtain ⟨hrelr, hbr, hAt⟩ := uniformEmitIterBody_eval_frame_of_rel_prepared N _ cs tail pref
    addr base σ hrel hb
  obtain ⟨τ₀, hpost⟩ := cnfEmitRel_one_step_of_iter_post (uniformMNat N) uctCurJ
    uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
    uctOuterReg N N base l cs tail pref addr (uniformEmitScratchResetProg.eval σ)
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hrelr
  exact uniformEmitIterBody_result_of_post N (⟨[l]⟩ : Clause) cs tail pref addr
    base σ τ₀ hbr hrelr hpost hAt

lemma uniformEmitIterBody_eval_frame_of_rel_two
    (N : ℕ) (l1 l2 : Literal) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l1, l2]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    UniformEmitIterBodyFrameGoal N (⟨[l1, l2]⟩ : Clause) cs tail pref addr base σ := by
  obtain ⟨hrelr, hbr, hAt⟩ := uniformEmitIterBody_eval_frame_of_rel_prepared N _ cs tail pref
    addr base σ hrel hb
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
  have hpairPosNegSafe : RegisterPairwise
      [uctCursorReg, uctLengthReg, uctPolReg, uctVarReg, uctDoneReg, uctPol2Reg,
        uctVar2Reg, uctFreshReg, uctOuterReg, uctPosPolReg, uctNegPolReg] :=
    registerPairwise_of_nodup hrelr.long_safety.pair_pos_neg_nodup
  obtain ⟨τ₀, hpost⟩ := cnfEmitRel_two_step_of_iter_post (uniformMNat N) uctCurJ
    uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
    uctOuterReg N N base l1 l2 cs tail pref addr
    (uniformEmitScratchResetProg.eval σ) uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hpairBelow hpairNonzero hpairSafe hpairPosNegSafe hrelr
  exact uniformEmitIterBody_result_of_post N (⟨[l1, l2]⟩ : Clause) cs tail pref
    addr base σ τ₀ hbr hrelr hpost hAt

lemma uniformEmitIterBody_eval_frame_of_rel_three
    (N : ℕ) (l1 l2 l3 : Literal) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨[l1, l2, l3]⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    UniformEmitIterBodyFrameGoal N (⟨[l1, l2, l3]⟩ : Clause) cs tail pref addr base σ := by
  obtain ⟨hrelr, hbr, hAt⟩ := uniformEmitIterBody_eval_frame_of_rel_prepared N _ cs tail pref
    addr base σ hrel hb
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
  have htriplePosNegSafe : RegisterPairwise
      [uctCursorReg, uctLengthReg, uctPolReg, uctVarReg, uctDoneReg, uctPol2Reg,
        uctVar2Reg, uctPol3Reg, uctVar3Reg, uctFreshReg, uctOuterReg,
        uctPosPolReg, uctNegPolReg] :=
    registerPairwise_of_nodup hrelr.long_safety.triple_pos_neg_nodup
  obtain ⟨τ₀, hpost⟩ := cnfEmitRel_three_step_of_iter_post (uniformMNat N) uctCurJ
    uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
    uctOuterReg N N base l1 l2 l3 cs tail pref addr
    (uniformEmitScratchResetProg.eval σ) uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 htripleBelow htripleNonzero htripleSafe
    htriplePosNegSafe hrelr
  exact uniformEmitIterBody_result_of_post N (⟨[l1, l2, l3]⟩ : Clause) cs tail
    pref addr base σ τ₀ hbr hrelr hpost hAt

lemma uniformEmitIterBody_eval_frame_of_rel_long
    (N : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      ((⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    UniformEmitIterBodyFrameGoal N (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) cs tail pref
      addr base σ := by
  obtain ⟨hrelr, hbr, hAt⟩ := uniformEmitIterBody_eval_frame_of_rel_prepared N _ cs tail pref
    addr base σ hrel hb
  have hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ := by
    have hlenPayload : l1.var + l2.var + base + 6 ≤
        (encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).1).length + 2 := by
      cases l1 <;> cases l2 <;>
        simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause,
          encodeLiteral, encodeNat_length, List.length_append, Literal.var] <;> omega
    have hc := hrelr.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hcapacity : uniformStartNat +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base)
        (l3 :: l4 :: rest)).length + 2 < uniformMNat N + uctCurJ := by
    have hc := hrelr.capacity
    rw [clausesToThree_payload_cons] at hc
    rw [← split_tail_emit_long_clause_payload] at hc
    simp only [List.length_append] at hc ⊢
    omega
  obtain ⟨τ₀, hpost⟩ := cnfEmitRel_long_step_of_iter_post_concrete
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
    uctCarryValReg uctFreshReg uctOuterReg N N base l1 l2 l3 l4 rest cs tail
    pref addr (uniformEmitScratchResetProg.eval σ) uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hroom hcapacity hrelr
  exact uniformEmitIterBody_result_of_post N
    (⟨l1 :: l2 :: l3 :: l4 :: rest⟩ : Clause) cs tail pref addr base σ τ₀ hbr
    hrelr hpost hAt

/-- The semantic step of one outer iteration body, strengthened with the high
frame: cells above `M + tmpJ` are unchanged, so the zero tail above the input
window survives every clause emission. -/
lemma uniformEmitIterBody_eval_frame_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N) :
    ∃ τ, uniformEmitIterBody.eval σ = τ ∧
      CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
        uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
        uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N
        (clauseToThree base c.lits).2 cs tail
        (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
        (addr + (encodeList encodeLiteral c.lits).length) τ ∧
      τ uctSavedBoundReg = N ∧
      (∀ r, uniformMNat N + uctTmpJ < r → τ r = σ r) := by
  cases c with
  | mk lits =>
    match lits with
    | [] => exact uniformEmitIterBody_eval_frame_of_rel_nil N cs tail pref addr base σ hrel hb
    | [l] => exact uniformEmitIterBody_eval_frame_of_rel_one N l cs tail pref addr base σ hrel hb
    | [l1, l2] =>
        exact uniformEmitIterBody_eval_frame_of_rel_two N l1 l2 cs tail pref addr base σ hrel hb
    | [l1, l2, l3] =>
        exact uniformEmitIterBody_eval_frame_of_rel_three N l1 l2 l3 cs tail pref addr base σ
          hrel hb
    | l1 :: l2 :: l3 :: l4 :: rest =>
        exact uniformEmitIterBody_eval_frame_of_rel_long N l1 l2 l3 l4 rest cs tail pref addr
          base σ hrel hb

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailReachability

/-!
# Short-clause dispatch envelope

The dispatcher must cover empty clauses and clauses with one, two, or three
literals using a shared numerical envelope. This module defines that envelope
and proves it dominates the syntax, step, and short-branch bounds.
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

/-! ## Concrete dispatch bounds on the decoded state

`EmitClauseDispatchRawBounds` inspects every dispatch branch regardless of the
decoded length, so the package needs an envelope that absorbs even the branches
that are not selected.  `uniformEmitLongValueEnvelope N` bounds the decoded
state. Each branch sub-program consumes one raw writer bound per appended
literal chain, and the split-tail loop chains two such bounds. The two envelopes
below provide the needed slack: `uniformEmitDispatchSetupEnvelope N` for one
post-setup or post-step state, and `uniformEmitDispatchEnvelope N` for every
branch obligation, including a chained garbage step. -/

def uniformEmitDispatchSetupEnvelope (N : ℕ) : ℕ :=
  writerAppendRawThreeBound (uniformEmitSyntaxEnvelope N) + 1

def uniformEmitDispatchEnvelope (N : ℕ) : ℕ :=
  writerAppendRawSixBound (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N)) + 1

lemma uniform_emit_n_le_long_value_envelope (N : ℕ) :
    N ≤ uniformEmitLongValueEnvelope N := by
  simp [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
    uniformStartNat, uniformSlackNat, uctCurJ]
  omega

lemma uniformEmitSyntaxEnvelope_le_dispatch_setup_envelope (N : ℕ) :
    uniformEmitSyntaxEnvelope N ≤ uniformEmitDispatchSetupEnvelope N := by
  simp only [uniformEmitDispatchSetupEnvelope, writerAppendRawThreeBound,
    writerAppendRawStepBound]
  omega

lemma uniformEmitDispatchSetupEnvelope_le_dispatch_envelope (N : ℕ) :
    uniformEmitDispatchSetupEnvelope N ≤ uniformEmitDispatchEnvelope N := by
  simp only [uniformEmitDispatchSetupEnvelope, uniformEmitDispatchEnvelope,
    writerAppendRawSixBound, writerAppendRawThreeBound, writerAppendRawStepBound]
  omega

lemma uniformEmitSyntaxEnvelope_le_dispatch_envelope (N : ℕ) :
    uniformEmitSyntaxEnvelope N ≤ uniformEmitDispatchEnvelope N :=
  (uniformEmitSyntaxEnvelope_le_dispatch_setup_envelope N).trans
    (uniformEmitDispatchSetupEnvelope_le_dispatch_envelope N)

lemma uniformEmitLongValueEnvelope_le_dispatch_envelope (N : ℕ) :
    uniformEmitLongValueEnvelope N ≤ uniformEmitDispatchEnvelope N :=
  (uniformEmitLongValueEnvelope_le_syntax_envelope N).trans
    (uniformEmitSyntaxEnvelope_le_dispatch_envelope N)

lemma uniform_emit_raw_six_bound_syntax_le_dispatch_envelope (N : ℕ) :
    writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) + 1 ≤
      uniformEmitDispatchEnvelope N := by
  simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound]
  omega

lemma uniform_emit_raw_three_bound_syntax_le_dispatch_envelope (N : ℕ) :
    writerAppendRawThreeBound (uniformEmitSyntaxEnvelope N) + 1 ≤
      uniformEmitDispatchEnvelope N := by
  have h := uniform_emit_raw_six_bound_syntax_le_dispatch_envelope N
  simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound] at h ⊢
  omega

/-! Envelope monotonicity for the boundedness predicates. -/

lemma exprBoundedIn_of_le {B₁ B₂ : ℕ} (σ : Store) (hB : B₁ ≤ B₂) {e : Expr}
    (h : ExprBoundedIn B₁ σ e) : ExprBoundedIn B₂ σ e := by
  induction e generalizing B₁ B₂ with
  | const n => exact h.trans hB
  | reg r => exact h.trans hB
  | regInd e' ih =>
      rcases h with ⟨h1, h2⟩
      exact ⟨ih hB h1, h2.trans hB⟩
  | add e1 e2 ih1 ih2 =>
      rcases h with ⟨h1, h2, h3⟩
      exact ⟨ih1 hB h1, ih2 hB h2, h3.trans hB⟩
  | sub e1 e2 ih1 ih2 =>
      rcases h with ⟨h1, h2, h3⟩
      exact ⟨ih1 hB h1, ih2 hB h2, h3.trans hB⟩
  | mul e1 e2 ih1 ih2 =>
      rcases h with ⟨h1, h2, h3⟩
      exact ⟨ih1 hB h1, ih2 hB h2, h3.trans hB⟩
  | lt e1 e2 ih1 ih2 =>
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 hB h1, ih2 hB h2⟩
  | eq e1 e2 ih1 ih2 =>
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 hB h1, ih2 hB h2⟩

lemma programBoundedIn_of_le {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) {p : Program} {σ : Store}
    (h : ProgramBoundedIn B₁ σ p) : ProgramBoundedIn B₂ σ p := by
  induction p generalizing B₁ B₂ σ with
  | skip => trivial
  | assign r e =>
      rcases h with ⟨h1, h2⟩
      exact ⟨h1.trans hB, exprBoundedIn_of_le σ hB h2⟩
  | assignInd eA eV =>
      rcases h with ⟨h1, h2, h3⟩
      exact ⟨exprBoundedIn_of_le σ hB h1, exprBoundedIn_of_le σ hB h2,
        h3.trans hB⟩
  | seq p1 p2 ih1 ih2 =>
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 hB h1, ih2 hB h2⟩
  | ifNZ e t f iht ihf =>
      rcases h with ⟨h1, h2, h3⟩
      exact ⟨exprBoundedIn_of_le σ hB h1, iht hB h2, ihf hB h3⟩
  | forN n body ihbody =>
      rcases h with ⟨h1, h2⟩
      exact ⟨exprBoundedIn_of_le σ hB h1, fun m hm => ihbody hB (h2 m hm)⟩
  | scanList _ _ _ _ => trivial
  | lookup _ _ _ => trivial

/-! The scratch-reset image of a clause-boundary relation keeps the relation and
    lifts the tight store bound to the long value envelope. -/

lemma uniform_emit_scratch_reset_state (N : ℕ) (clauses : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      clauses tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ) :
    CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      clauses tail pref addr (uniformEmitScratchResetProg.eval σ) ∧
    (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N ∧
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      (uniformEmitScratchResetProg.eval σ) := by
  have hK1 : 1 ≤ uniformEmitLongValueEnvelope N := by
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  have hK25 : 25 ≤ uniformEmitLongValueEnvelope N := by
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  exact ⟨uniformEmitScratchResetProg_cnfEmitRel _ _ _ N N base clauses tail pref addr σ
    hrel, by
      rcases uniformEmitScratchResetProg_persistent_values σ with ⟨_, _, _, _, _, hsaved⟩
      exact hsaved.trans hb,
    storeValuesLe_uniformEmitScratchResetProg _ σ hK1
      (fun i => (hσ i).trans (uniformEmitTightEnvelope_le_long_value_envelope N)) hK25⟩

/-! The state right after the length decode: a preparation state whose parser
    cells are pinned by the input window, and whose store stays inside the long
    value envelope. -/

lemma uniform_emit_decoded_state (N inputEnd : ℕ) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ)
    (hwin : SplitTailEmitWindow inputEnd (base + c.lits.length) base c.lits
      ((cs.map encodeClause).flatten ++ tail) addr)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
      ((cs.map encodeClause).flatten ++ tail) pref
      (uniformEmitScratchResetProg.eval σ)
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) ∧
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) := by
  obtain ⟨hrelr, hbr, hσr⟩ :=
    uniform_emit_scratch_reset_state N (c :: cs) tail pref addr base σ hrel hb hσ
  have hhead := cnfEmitRel_head_input (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
    uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base c cs tail pref addr
    (uniformEmitScratchResetProg.eval σ) hrelr
  have hbound : c.lits.length + 1 ≤ N := hrel.clause_bound c (by simp)
  have hroomPayload : uniformStartNat + pref.length +
      (encodeThreeClausesPayload (clauseToThree base c.lits).1).length + 2 <
      uniformMNat N + uctCurJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hσ0 : (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg
      uctSavedBoundReg).eval (uniformEmitScratchResetProg.eval σ) =
      (decodeNatProgram uctCursorReg uctLengthReg uctDoneReg N).eval
      (uniformEmitScratchResetProg.eval σ) :=
    decodeNatProgramAt_eq uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg N _ hbr
  have hprep := emitClausePrepState_of_pre_eq (uniformMNat N) uctCurJ uctTmpJ
    uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
    uctFreshReg uctPosPolReg uctNegPolReg N base (c :: cs).length addr c.lits
    ((cs.map encodeClause).flatten ++ tail) pref
    (uniformEmitScratchResetProg.eval σ)
    ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
      (uniformEmitScratchResetProg.eval σ))
    hσ0 uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hbound hrel.start_at_input hhead
    hrelr.cursor hrelr.length_zero hrelr.done_zero hrelr.outer hrelr.fresh hrelr.pos
    hrelr.neg hrelr.input_above hrelr.writer hroomPayload hrelr.safety
  refine ⟨hprep, ?_⟩
  intro i
  by_cases hC : i = uctCursorReg
  · rw [hC, hprep.cursor]
    have haddr := hwin.1
    simp only [splitTailInputBits] at haddr
    have hlenapp : (c.lits.map encodeLiteral).flatten.length ≤
        ((c.lits.map encodeLiteral).flatten ++
          ((cs.map encodeClause).flatten ++ tail)).length := by
      simp [List.length_append]
    have h2 : c.lits.length ≤ (c.lits.map encodeLiteral).flatten.length := by
      have hind : ∀ ls : List NPComplete.SAT.Literal,
          2 * ls.length ≤ (ls.map encodeLiteral).flatten.length := by
        intro ls
        induction ls with
        | nil => simp
        | cons l rest ih =>
            have h1 : 2 ≤ (encodeLiteral l).length := by
              cases l <;> simp [encodeLiteral, encodeNat_length]
            simp only [List.map_cons, List.flatten_cons, List.length_append,
              List.length_cons]
            omega
      have := hind c.lits
      omega
    omega
  · by_cases hL : i = uctLengthReg
    · rw [hL, hprep.length]
      have hlenN : c.lits.length ≤ uniformEmitLongValueEnvelope N := by
        omega
      exact hlenN
    · by_cases hD : i = uctDoneReg
      · rw [hD, hprep.done]
        have hK1 : 1 ≤ uniformEmitLongValueEnvelope N := by
          simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
            uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
          omega
        omega
      · rw [hprep.frame i hC hL hD]
        exact hσr i

/-! Shared facts about the decoded state that every dispatch branch consumes:
the writer cells are live and every control register index is below `K`. -/

lemma uniform_emit_dispatch_base_facts (N base outer addr : ℕ)
    (ls : List NPComplete.SAT.Literal) (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    {K : ℕ} (hK25 : 25 ≤ K) (hMK : uniformMNat N + uctTmpJ ≤ K) :
    σdec 0 = uniformMNat N ∧
    σdec (uniformMNat N + uctCurJ) ≠ 0 ∧
    (uniformMNat N + uctCurJ ≤ K ∧ uniformMNat N + uctTmpJ ≤ K ∧ uctCurJ ≤ K ∧
      uctTmpJ ≤ K) ∧
    (uctCursorReg ≤ K ∧ uctPolReg ≤ K ∧ uctVarReg ≤ K ∧ uctDoneReg ≤ K ∧
      uctLengthReg ≤ K ∧ uctRemainingReg ≤ K ∧ uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧
      uctPol3Reg ≤ K ∧ uctVar3Reg ≤ K ∧ uctPosPolReg ≤ K ∧ uctNegPolReg ≤ K ∧
      uctCarryPolReg ≤ K ∧ uctCarryValReg ≤ K ∧ uctFreshReg ≤ K ∧
      uctSavedBoundReg ≤ K) := by
  have hq0 : σdec (uniformMNat N + uctCurJ) ≠ 0 := by
    rw [hprep.writer.cursor]
    have hstart := hprep.writer.start_pos
    omega
  have hstatic : uniformMNat N + uctCurJ ≤ K ∧ uniformMNat N + uctTmpJ ≤ K ∧
      uctCurJ ≤ K ∧ uctTmpJ ≤ K := by
    have hc1 : uctCurJ = 1 := rfl
    have ht2 : uctTmpJ = 2 := rfl
    omega
  have hidx : (uctCursorReg ≤ K ∧ uctPolReg ≤ K ∧ uctVarReg ≤ K ∧ uctDoneReg ≤ K ∧
      uctLengthReg ≤ K ∧ uctRemainingReg ≤ K ∧ uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧
      uctPol3Reg ≤ K ∧ uctVar3Reg ≤ K ∧ uctPosPolReg ≤ K ∧ uctNegPolReg ≤ K ∧
      uctCarryPolReg ≤ K ∧ uctCarryValReg ≤ K ∧ uctFreshReg ≤ K ∧
      uctSavedBoundReg ≤ K) := by
    simp only [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctLengthReg,
      uctRemainingReg, uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg,
      uctPosPolReg, uctNegPolReg, uctCarryPolReg, uctCarryValReg, uctFreshReg,
      uctSavedBoundReg]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩
  exact ⟨hprep.writer.root, hq0, hstatic, hidx⟩

lemma uniform_emit_dispatch_writer_cell_ne (N r : ℕ) (hr : r ≤ 24) :
    r ≠ uniformMNat N + uctCurJ ∧ r ≠ uniformMNat N + uctTmpJ := by
  simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap,
    uctCurJ, uctTmpJ]
  omega

/-! Shared envelopes and register facts for the short dispatch branches. -/

structure UniformProducerPreStartupFacts (φ : CNF) (N : ℕ) (σ : Store) where
  root : σ 0 = uniformMNat N
  savedBound : σ uctSavedBoundReg = N
  inputBase : σ uctInputBaseReg = uniformAddrNat N
  fresh : σ uctFreshReg = (toThreeCNF φ).numVars
  count : σ uctCountReg = (toThreeCNF φ).clauses.length
  maxValue : σ uctMaxReg = cnfVarBound φ
  inputBits : BitsFrom σ (uniformAddrNat N) (encodeCNF φ)

structure UniformEmitDispatchPrologue (N : ℕ) (σ : Store) where
  root : σ 0 = uniformMNat N
  cursor_nonzero : σ (uniformMNat N + uctCurJ) ≠ 0
  static : uniformMNat N + uctCurJ ≤ uniformEmitLongValueEnvelope N ∧
    uniformMNat N + uctTmpJ ≤ uniformEmitLongValueEnvelope N ∧
    uctCurJ ≤ uniformEmitLongValueEnvelope N ∧ uctTmpJ ≤ uniformEmitLongValueEnvelope N
  indices : uctCursorReg ≤ uniformEmitLongValueEnvelope N ∧
    uctPolReg ≤ uniformEmitLongValueEnvelope N ∧ uctVarReg ≤ uniformEmitLongValueEnvelope N ∧
    uctDoneReg ≤ uniformEmitLongValueEnvelope N ∧ uctLengthReg ≤ uniformEmitLongValueEnvelope N ∧
    uctRemainingReg ≤ uniformEmitLongValueEnvelope N ∧ uctPol2Reg ≤ uniformEmitLongValueEnvelope N ∧
    uctVar2Reg ≤ uniformEmitLongValueEnvelope N ∧ uctPol3Reg ≤ uniformEmitLongValueEnvelope N ∧
    uctVar3Reg ≤ uniformEmitLongValueEnvelope N ∧ uctPosPolReg ≤ uniformEmitLongValueEnvelope N ∧
    uctNegPolReg ≤ uniformEmitLongValueEnvelope N ∧ uctCarryPolReg ≤ uniformEmitLongValueEnvelope N ∧
    uctCarryValReg ≤ uniformEmitLongValueEnvelope N ∧ uctFreshReg ≤ uniformEmitLongValueEnvelope N ∧
    uctSavedBoundReg ≤ uniformEmitLongValueEnvelope N
  storeLong : StoreValuesLe (uniformEmitLongValueEnvelope N) σ
  storeSyntax : StoreValuesLe (uniformEmitSyntaxEnvelope N) σ
  storeDispatch : StoreValuesLe (uniformEmitDispatchEnvelope N) σ

lemma uniformEmitDispatchPrologue_of_prep
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec) :
    UniformEmitDispatchPrologue N σdec := by
  have hK25 : 25 ≤ uniformEmitLongValueEnvelope N := by
    have hgap : relocateControlGap = 100 := rfl
    have hc1 : uctCurJ = 1 := rfl
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat] at ⊢
    omega
  have hMK : uniformMNat N + uctTmpJ ≤ uniformEmitLongValueEnvelope N := by
    have hc1 : uctCurJ = 1 := rfl
    have ht : uctTmpJ = 2 := rfl
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope] at ⊢
    omega
  obtain ⟨hroot, hq0, hstatic, hidx⟩ :=
    uniform_emit_dispatch_base_facts N base outer addr ls rest pref σr σdec hprep hK25 hMK
  have hKS : uniformEmitLongValueEnvelope N ≤ uniformEmitSyntaxEnvelope N :=
    uniformEmitLongValueEnvelope_le_syntax_envelope N
  have hSD : uniformEmitSyntaxEnvelope N ≤ uniformEmitDispatchEnvelope N :=
    uniformEmitSyntaxEnvelope_le_dispatch_envelope N
  exact {
    root := hroot
    cursor_nonzero := hq0
    static := hstatic
    indices := hidx
    storeLong := hstore
    storeSyntax := fun i => (hstore i).trans hKS
    storeDispatch := fun i => (hstore i).trans (hKS.trans hSD)
  }

/-! An arity-indexed sequence packages the nested `.seq` shape used by the
    dispatch branches without hiding the state passed between adjacent stages. -/

inductive ProgramBoundedInSequence (B : ℕ) : Store → List Program → Prop where
  | nil (σ : Store) : ProgramBoundedInSequence B σ []
  | cons (σ : Store) (p : Program) (ps : List Program) :
      ProgramBoundedIn B σ p →
      ProgramBoundedInSequence B (p.eval σ) ps →
      ProgramBoundedInSequence B σ (p :: ps)

def programSequence : List Program → Program
  | [] => .skip
  | [p] => p
  | p :: q :: ps => .seq p (programSequence (q :: ps))

lemma programBoundedIn_programSequence
    (B : ℕ) (σ : Store) (ps : List Program)
    (h : ProgramBoundedInSequence B σ ps) :
    ProgramBoundedIn B σ (programSequence ps) := by
  induction h with
  | nil => trivial
  | cons σ p ps hp hs ih =>
      cases ps with
      | nil => exact hp
      | cons q qs => exact ⟨hp, ih⟩

lemma storeValuesLe_of_frame
    (B : ℕ) (σ τ : Store) (changed : List ℕ)
    (hσ : StoreValuesLe B σ)
    (hframe : ∀ i, i ∉ changed → τ i = σ i)
    (hchanged : ∀ i, i ∈ changed → τ i ≤ B) :
    StoreValuesLe B τ := by
  intro i
  by_cases hi : i ∈ changed
  · exact hchanged i hi
  · rw [hframe i hi]
    exact hσ i

/-! The one-literal branch: decode one literal, append one clause, commit. -/

lemma programBoundedIn_uniform_emit_dispatch_one_branch
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq (writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg)
          (emitClauseCommitProg uctOuterReg))) := by
  have hp := uniformEmitDispatchPrologue_of_prep N base outer addr ls rest pref σr σdec hprep hstore
  rcases hp.indices with ⟨hcurB, hpolB, hvarB, hdoneB, hlenB, hremB, hpol2B, hvar2B,
    hpol3B, hvar3B, hposB, hnegB, hcpB, hcvB, hfreshB, hsavedB⟩
  have hKS : uniformEmitLongValueEnvelope N ≤ uniformEmitSyntaxEnvelope N :=
    uniformEmitLongValueEnvelope_le_syntax_envelope N
  have hSD : uniformEmitSyntaxEnvelope N ≤ uniformEmitDispatchEnvelope N :=
    uniformEmitSyntaxEnvelope_le_dispatch_envelope N
  have hKD : uniformEmitLongValueEnvelope N ≤ uniformEmitDispatchEnvelope N := hKS.trans hSD
  have hcursorBudget : σdec uctCursorReg + 1 + σdec uctSavedBoundReg ≤
      uniformEmitSyntaxEnvelope N := by
    have hcur := hp.storeLong uctCursorReg
    rw [hsaved]
    have hN := uniform_emit_n_le_long_value_envelope N
    have h2K : 2 * uniformEmitLongValueEnvelope N + 1 ≤ uniformEmitSyntaxEnvelope N := by
      simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
        writerAppendRawStepBound]
      omega
    omega
  have hK1 : 1 ≤ uniformEmitLongValueEnvelope N := by
    have hK25 : 25 ≤ uniformEmitLongValueEnvelope N := by
      simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
        uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
      omega
    omega
  have hidxLong : uctCursorReg ≤ uniformEmitLongValueEnvelope N ∧
      uctPolReg ≤ uniformEmitLongValueEnvelope N ∧ uctVarReg ≤ uniformEmitLongValueEnvelope N ∧
      uctDoneReg ≤ uniformEmitLongValueEnvelope N ∧ uctSavedBoundReg ≤ uniformEmitLongValueEnvelope N :=
    ⟨hcurB, hpolB, hvarB, hdoneB, hsavedB⟩
  have hdecS := programBoundedIn_decodeLiteralValueProgramAt_syntax_bounds
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N)
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctSavedBoundReg σdec hidxLong
    (by decide) (by decide) hp.storeLong hcursorBudget hKS
  have hdecD := programBoundedIn_decodeLiteralValueProgramAt_syntax_bounds
    (uniformEmitLongValueEnvelope N) (uniformEmitDispatchEnvelope N)
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctSavedBoundReg σdec hidxLong
    (by decide) (by decide) hp.storeLong (hcursorBudget.trans hSD) hKD
  have hM1 : (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctSavedBoundReg).eval σdec 0 = uniformMNat N := by
    rw [hdecS.2.2.1]
    exact hp.root
  have hq01 : (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctSavedBoundReg).eval σdec (uniformMNat N + uctCurJ) ≠ 0 := by
    have hw := uniform_emit_dispatch_writer_cell_ne N uctCursorReg (by decide)
    have hp' := uniform_emit_dispatch_writer_cell_ne N uctPolReg (by decide)
    have hv := uniform_emit_dispatch_writer_cell_ne N uctVarReg (by decide)
    have hd := uniform_emit_dispatch_writer_cell_ne N uctDoneReg (by decide)
    rw [decodeLiteralValueProgramAt_frame uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctSavedBoundReg (uniformMNat N + uctCurJ) σdec (Ne.symm hw.1) (Ne.symm hp'.1)
      (Ne.symm hv.1) (Ne.symm hd.1)]
    exact hp.cursor_nonzero
  have hstaticS : uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧ uctCurJ ≤
        uniformEmitSyntaxEnvelope N ∧ uctTmpJ ≤ uniformEmitSyntaxEnvelope N :=
    ⟨hp.static.1.trans hKS, hp.static.2.1.trans hKS, hp.static.2.2.1.trans hKS,
      hp.static.2.2.2.trans hKS⟩
  let τ := (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctSavedBoundReg).eval σdec
  have hMτ : τ 0 = uniformMNat N := by simpa [τ] using hM1
  have hqτ : τ (uniformMNat N + uctCurJ) ≠ 0 := by simpa [τ] using hq01
  have happ := programBoundedIn_writerAppendClauseOneProg_raw_bounds
    (uniformEmitSyntaxEnvelope N) (uniformEmitDispatchEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctPolReg uctVarReg τ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hstaticS ⟨hpolB.trans hKS, hvarB.trans hKS⟩ hdecS.2.1 hMτ hqτ
    (Nat.le_of_succ_le (uniform_emit_raw_three_bound_syntax_le_dispatch_envelope N))
  have hpost : StoreValuesLe (uniformEmitDispatchEnvelope N)
      ((writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg).eval τ) :=
    program_eval_storeValuesLe τ _ (by
      have h1 := uniformEmitLongValueEnvelope_le_syntax_envelope N
      omega) hdecD.2.1 happ
      (scanFree_writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg)
  have houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hcommit := programBoundedIn_emitClauseCommitProg_of_bounds
    (uniformEmitDispatchEnvelope N) uctOuterReg _ (by
      simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
        writerAppendRawThreeBound, writerAppendRawStepBound]
      omega)
    houter hpost
  have hseq : ProgramBoundedInSequence (uniformEmitDispatchEnvelope N) σdec
      [decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg uctSavedBoundReg,
        writerAppendClauseOneProg uctCurJ uctTmpJ uctPolReg uctVarReg,
        emitClauseCommitProg uctOuterReg] := by
    exact .cons _ _ _ hdecD.1 (.cons _ _ _ happ (.cons _ _ _ hcommit (.nil _)))
  simpa [programSequence] using programBoundedIn_programSequence
    (uniformEmitDispatchEnvelope N) σdec _ hseq

lemma uniformEmitDispatchEnvelope_pos (N : ℕ) : 1 ≤ uniformEmitDispatchEnvelope N := by
  simp only [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound]
  omega

lemma uniformEmitDispatchEnvelope_sub (N : ℕ) :
    writerAppendRawSixBound (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N)) + 1 ≤
      uniformEmitDispatchEnvelope N := by
  simp only [uniformEmitDispatchEnvelope]
  omega

/-! The empty-clause branch: two polarity/fresh triples, fresh bump, commit. -/

/-- The empty-branch writer fits, preserves the store bound, and leaves room for the bump. -/
lemma programBoundedIn_uniform_emit_dispatch_zero_branch_writer
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitSyntaxEnvelope N) τ)
    (hroot : τ 0 = uniformMNat N) (hq : τ (uniformMNat N + uctCurJ) ≠ 0)
    (hpos : uctPosPolReg ≤ uniformEmitSyntaxEnvelope N)
    (hneg : uctNegPolReg ≤ uniformEmitSyntaxEnvelope N)
    (hfresh : uctFreshReg ≤ uniformEmitSyntaxEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ
      (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg) ∧
    StoreValuesLe (uniformEmitDispatchEnvelope N)
      ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval τ) ∧
    ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval τ)
      uctFreshReg + 1 ≤ uniformEmitDispatchEnvelope N := by
  have hstatic : uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧
      uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧ uctTmpJ ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound, writerAppendRawStepBound,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap, uctCurJ, uctTmpJ]
    omega
  have hS6 : uniformEmitSyntaxEnvelope N ≤
      writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) := by
    simp only [writerAppendRawSixBound, writerAppendRawThreeBound,
      writerAppendRawStepBound]
    omega
  have hrawPos : 1 ≤ writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) := by
    simp only [writerAppendRawSixBound, writerAppendRawThreeBound,
      writerAppendRawStepBound]
    omega
  have hrawBound := uniform_emit_raw_six_bound_syntax_le_dispatch_envelope N
  have hrawWriter := programBoundedIn_writerAppendClauseEmptyProg_raw_bounds
    (uniformEmitSyntaxEnvelope N) (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N))
    (uniformMNat N) uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg τ
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hstatic ⟨hpos, hneg, hfresh⟩ hτ hroot hq le_rfl
  have hτRaw : StoreValuesLe (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N)) τ :=
    fun i => (hτ i).trans hS6
  have hrawPost := program_eval_storeValuesLe τ _ hrawPos hτRaw hrawWriter
    (scanFree_writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg)
  have hfreshBudget :
      ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval τ)
        uctFreshReg + 1 ≤ uniformEmitDispatchEnvelope N := by
    calc
      _ ≤ writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) + 1 :=
        Nat.add_le_add_right (hrawPost uctFreshReg) 1
      _ ≤ uniformEmitDispatchEnvelope N := hrawBound
  have hwriter := programBoundedIn_writerAppendClauseEmptyProg_raw_bounds
    (uniformEmitSyntaxEnvelope N) (uniformEmitDispatchEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg τ uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hstatic ⟨hpos, hneg, hfresh⟩ hτ hroot hq
    (Nat.le_of_succ_le hrawBound)
  have hpost := program_eval_storeValuesLe τ _ (uniformEmitDispatchEnvelope_pos N)
    (fun i => (hτ i).trans (uniformEmitSyntaxEnvelope_le_dispatch_envelope N)) hwriter
    (scanFree_writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg)
  exact ⟨hwriter, hpost, hfreshBudget⟩

/-- The fresh-cell increment fits when the writer leaves one unit of headroom. -/
lemma programBoundedIn_uniform_emit_dispatch_zero_branch_fresh
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitDispatchEnvelope N) τ)
    (hfreshReg : uctFreshReg ≤ uniformEmitDispatchEnvelope N)
    (hfreshBudget : τ uctFreshReg + 1 ≤ uniformEmitDispatchEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ (emitClauseEmptyFreshProg uctFreshReg) ∧
    StoreValuesLe (uniformEmitDispatchEnvelope N)
      ((emitClauseEmptyFreshProg uctFreshReg).eval τ) := by
  have hempty := programBoundedIn_emitClauseEmptyFreshProg_of_bounds
    (uniformEmitDispatchEnvelope N) uctFreshReg _ hfreshReg hfreshBudget
  have hpost := program_eval_storeValuesLe τ _ (uniformEmitDispatchEnvelope_pos N) hτ hempty
    (scanFree_emitClauseEmptyFreshProg uctFreshReg)
  exact ⟨hempty, hpost⟩

/-- The final commit is bounded once the fresh bump's store is bounded. -/
lemma programBoundedIn_uniform_emit_dispatch_zero_branch_commit
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitDispatchEnvelope N) τ)
    (houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ (emitClauseCommitProg uctOuterReg) := by
  exact programBoundedIn_emitClauseCommitProg_of_bounds
    (uniformEmitDispatchEnvelope N) uctOuterReg _ (uniformEmitDispatchEnvelope_pos N) houter hτ

/-- The empty-branch writer, fresh-cell bump, and commit fit the dispatch envelope. -/
lemma programBoundedIn_uniform_emit_dispatch_zero_branch_tail
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitSyntaxEnvelope N) τ)
    (hroot : τ 0 = uniformMNat N) (hq : τ (uniformMNat N + uctCurJ) ≠ 0)
    (hpos : uctPosPolReg ≤ uniformEmitSyntaxEnvelope N)
    (hneg : uctNegPolReg ≤ uniformEmitSyntaxEnvelope N)
    (hfresh : uctFreshReg ≤ uniformEmitSyntaxEnvelope N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ
      (Program.seq
        (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg)
        (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
          (emitClauseCommitProg uctOuterReg))) := by
  have hw := programBoundedIn_uniform_emit_dispatch_zero_branch_writer N τ hτ hroot hq
    hpos hneg hfresh
  have hfreshReg : uctFreshReg ≤ uniformEmitDispatchEnvelope N :=
    hfresh.trans (uniformEmitSyntaxEnvelope_le_dispatch_envelope N)
  have hf := programBoundedIn_uniform_emit_dispatch_zero_branch_fresh N
    ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval τ)
    hw.2.1 hfreshReg hw.2.2
  have houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hc := programBoundedIn_uniform_emit_dispatch_zero_branch_commit N
    ((emitClauseEmptyFreshProg uctFreshReg).eval
      ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval τ))
    hf.2 houter
  exact ⟨hw.1, ⟨hf.1, hc⟩⟩

lemma programBoundedIn_uniform_emit_dispatch_zero_branch
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq
        (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg)
        (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
          (emitClauseCommitProg uctOuterReg))) := by
  have hp := uniformEmitDispatchPrologue_of_prep N base outer addr ls rest pref σr σdec hprep hstore
  rcases hp.indices with ⟨_, _, _, _, _, _, _, _, _, _, hposK, hnegK, _, _, hfreshK, _⟩
  have hKS := uniformEmitLongValueEnvelope_le_syntax_envelope N
  exact programBoundedIn_uniform_emit_dispatch_zero_branch_tail N σdec hp.storeSyntax
    hp.root hp.cursor_nonzero (hposK.trans hKS) (hnegK.trans hKS) (hfreshK.trans hKS)

/-- One literal decode step of a dispatch branch: bounded, store-preserving, and it keeps the
    saved bound, the root cell and the live writer cursor cell. -/
lemma programBoundedIn_uniform_emit_dispatch_three_branch_decode_step
    (N K B polReg varReg : ℕ) (τ : Store)
    (hlow : polReg ≤ 24 ∧ varReg ≤ 24)
    (hdist : uctCursorReg ≠ polReg ∧ uctCursorReg ≠ varReg ∧ uctCursorReg ≠ uctDoneReg ∧
      varReg ≠ uctDoneReg ∧ uctSavedBoundReg ≠ uctCursorReg ∧ uctSavedBoundReg ≠ polReg ∧
      uctSavedBoundReg ≠ varReg ∧ uctSavedBoundReg ≠ uctDoneReg)
    (hzero : uctCursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ uctDoneReg ≠ 0)
    (hK25 : 25 ≤ K) (hσ : StoreValuesLe K τ) (hsaved : τ uctSavedBoundReg = N)
    (hcursor : τ uctCursorReg + 1 + N ≤ B) (hKB : K ≤ B)
    (hq : τ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn B τ
        (decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg uctSavedBoundReg) ∧
      StoreValuesLe B
        ((decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg
          uctSavedBoundReg).eval τ) ∧
      (decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg
        uctSavedBoundReg).eval τ 0 = τ 0 ∧
      (decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg
        uctSavedBoundReg).eval τ uctCursorReg ≤ τ uctCursorReg + 1 + N ∧
      (decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg
        uctSavedBoundReg).eval τ uctSavedBoundReg = N ∧
      (decodeLiteralValueProgramAt uctCursorReg polReg varReg uctDoneReg
        uctSavedBoundReg).eval τ (uniformMNat N + uctCurJ) ≠ 0 := by
  have hidx : uctCursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ uctDoneReg ≤ K ∧
      uctSavedBoundReg ≤ K := by
    simp only [uctCursorReg, uctDoneReg, uctSavedBoundReg]
    omega
  have hsyn := programBoundedIn_decodeLiteralValueProgramAt_syntax_bounds K B uctCursorReg
    polReg varReg uctDoneReg uctSavedBoundReg τ hidx hdist hzero hσ
    (by rwa [hsaved]) hKB
  have hbound := decodeLiteralValueProgramAt_bound_frame uctCursorReg polReg varReg uctDoneReg
    uctSavedBoundReg τ hdist.2.2.2.2.1 hdist.2.2.2.2.2.1 hdist.2.2.2.2.2.2.1
    hdist.2.2.2.2.2.2.2
  have hw := uniform_emit_dispatch_writer_cell_ne N uctCursorReg (by decide)
  have hp := uniform_emit_dispatch_writer_cell_ne N polReg hlow.1
  have hv := uniform_emit_dispatch_writer_cell_ne N varReg hlow.2
  have hd := uniform_emit_dispatch_writer_cell_ne N uctDoneReg (by decide)
  refine ⟨hsyn.1, hsyn.2.1, hsyn.2.2.1, hsyn.2.2.2.trans (by omega), hbound.trans hsaved, ?_⟩
  rw [decodeLiteralValueProgramAt_frame uctCursorReg polReg varReg uctDoneReg uctSavedBoundReg
    (uniformMNat N + uctCurJ) τ (Ne.symm hw.1) (Ne.symm hp.1) (Ne.symm hv.1) (Ne.symm hd.1)]
  exact hq

/-- The two chained decodes stay within the dispatch envelope and syntax envelope,
preserve cell 0, and leave the writer cursor cell nonzero. -/
lemma programBoundedIn_uniform_emit_dispatch_two_branch_decodes
    (N : ℕ) (σ : Store) (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hsaved : σ uctSavedBoundReg = N) (hq : σ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)) ∧
      StoreValuesLe (uniformEmitSyntaxEnvelope N)
        ((Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)).eval σ) ∧
      (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)).eval σ 0 = σ 0 ∧
      (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)).eval σ (uniformMNat N + uctCurJ) ≠ 0 := by
  have hKS := uniformEmitLongValueEnvelope_le_syntax_envelope N
  have hSD := uniformEmitSyntaxEnvelope_le_dispatch_envelope N
  have hN := uniform_emit_n_le_long_value_envelope N
  have h3K : 3 * uniformEmitLongValueEnvelope N + 2 ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
      writerAppendRawStepBound, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
      uniformMNat, uniformStartNat, uniformSlackNat]
    omega
  have hK25 : 25 ≤ uniformEmitLongValueEnvelope N := by
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  have hc := hstore uctCursorReg
  have hd1 := programBoundedIn_uniform_emit_dispatch_three_branch_decode_step N
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N) uctPolReg uctVarReg σ
    (by decide) (by decide) (by decide) hK25 hstore hsaved (by omega) hKS hq
  have hd2 := programBoundedIn_uniform_emit_dispatch_three_branch_decode_step N
    (uniformEmitSyntaxEnvelope N) (uniformEmitSyntaxEnvelope N) uctPol2Reg uctVar2Reg _
    (by decide) (by decide) (by decide) (hK25.trans hKS) hd1.2.1 hd1.2.2.2.2.1 (by omega)
    le_rfl hd1.2.2.2.2.2
  refine ⟨⟨programBoundedIn_of_le hSD hd1.1, programBoundedIn_of_le hSD hd2.1⟩, ?_⟩
  simp only [eval_seq]
  exact ⟨hd2.2.1, hd2.2.2.1.trans hd1.2.2.1, hd2.2.2.2.2.2⟩

/-- The writer append and commit that follow the two decodes, from any syntax-bounded state
    with live writer cells. -/
lemma programBoundedIn_uniform_emit_dispatch_two_branch_tail
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitSyntaxEnvelope N) τ)
    (hroot : τ 0 = uniformMNat N) (hq : τ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ
      (Program.seq
        (writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg)
        (emitClauseCommitProg uctOuterReg)) := by
  have hD1 := uniformEmitDispatchEnvelope_pos N
  have hstatic : uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧ uctCurJ ≤
        uniformEmitSyntaxEnvelope N ∧ uctTmpJ ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound, writerAppendRawStepBound,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap, uctCurJ, uctTmpJ]
    omega
  have hidx : uctPolReg ≤ uniformEmitSyntaxEnvelope N ∧ uctVarReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol2Reg ≤ uniformEmitSyntaxEnvelope N ∧ uctVar2Reg ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uctPolReg, uctVarReg, uctPol2Reg, uctVar2Reg, uniformEmitSyntaxEnvelope,
      writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitLongValueEnvelope,
      uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctCurJ]
    omega
  have hwriter := programBoundedIn_writerAppendClauseTwoProg_raw_bounds
    (uniformEmitSyntaxEnvelope N) (uniformEmitDispatchEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg τ uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 hstatic hidx hτ hroot hq
    (Nat.le_of_succ_le (uniform_emit_raw_three_bound_syntax_le_dispatch_envelope N))
  have hpost := program_eval_storeValuesLe τ _ hD1
    (fun i => (hτ i).trans (uniformEmitSyntaxEnvelope_le_dispatch_envelope N)) hwriter
    (scanFree_writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
      uctVar2Reg)
  have houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  exact ⟨hwriter, programBoundedIn_emitClauseCommitProg_of_bounds _ uctOuterReg _ hD1
    houter hpost⟩

lemma programBoundedIn_uniform_emit_dispatch_two_branch
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (writerAppendClauseTwoProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
              uctVar2Reg)
            (emitClauseCommitProg uctOuterReg)))) := by
  have hp := uniformEmitDispatchPrologue_of_prep N base outer addr ls rest pref σr σdec hprep hstore
  obtain ⟨⟨hd1, hd2⟩, hdecS, hroot, hq⟩ :=
    programBoundedIn_uniform_emit_dispatch_two_branch_decodes N σdec hstore hsaved hp.cursor_nonzero
  refine ⟨hd1, hd2, ?_⟩
  have htail := programBoundedIn_uniform_emit_dispatch_two_branch_tail N _ hdecS
    (hroot.trans hp.root) hq
  simpa only [eval_seq] using htail

/-- The three chained decodes stay within the dispatch envelope and syntax envelope,
preserve cell 0, and leave the writer cursor cell nonzero. -/
lemma programBoundedIn_uniform_emit_dispatch_three_branch_decodes
    (N : ℕ) (σ : Store) (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hsaved : σ uctSavedBoundReg = N) (hq : σ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σ
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
              uctSavedBoundReg)
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg))) ∧
      StoreValuesLe (uniformEmitSyntaxEnvelope N)
        ((Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
              uctSavedBoundReg)
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg))).eval σ) ∧
      (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
              uctSavedBoundReg)
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg))).eval σ 0 = σ 0 ∧
      (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
              uctSavedBoundReg)
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg))).eval σ (uniformMNat N + uctCurJ) ≠ 0 := by
  have hKS := uniformEmitLongValueEnvelope_le_syntax_envelope N
  have hSD := uniformEmitSyntaxEnvelope_le_dispatch_envelope N
  have hN := uniform_emit_n_le_long_value_envelope N
  have h4K : 4 * uniformEmitLongValueEnvelope N + 3 ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
      writerAppendRawStepBound, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
      uniformMNat, uniformStartNat, uniformSlackNat]
    omega
  have hK25 : 25 ≤ uniformEmitLongValueEnvelope N := by
    simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
    omega
  have hc := hstore uctCursorReg
  have hd1 := programBoundedIn_uniform_emit_dispatch_three_branch_decode_step N
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N) uctPolReg uctVarReg σ
    (by decide) (by decide) (by decide) hK25 hstore hsaved (by omega) hKS hq
  have hd2 := programBoundedIn_uniform_emit_dispatch_three_branch_decode_step N
    (uniformEmitSyntaxEnvelope N) (uniformEmitSyntaxEnvelope N) uctPol2Reg uctVar2Reg _
    (by decide) (by decide) (by decide) (hK25.trans hKS) hd1.2.1 hd1.2.2.2.2.1 (by omega)
    le_rfl hd1.2.2.2.2.2
  have hd3 := programBoundedIn_uniform_emit_dispatch_three_branch_decode_step N
    (uniformEmitSyntaxEnvelope N) (uniformEmitSyntaxEnvelope N) uctPol3Reg uctVar3Reg _
    (by decide) (by decide) (by decide) (hK25.trans hKS) hd2.2.1 hd2.2.2.2.2.1 (by omega)
    le_rfl hd2.2.2.2.2.2
  refine ⟨⟨programBoundedIn_of_le hSD hd1.1, programBoundedIn_of_le hSD hd2.1,
    programBoundedIn_of_le hSD hd3.1⟩, ?_⟩
  simp only [eval_seq]
  exact ⟨hd3.2.1, hd3.2.2.1.trans (hd2.2.2.1.trans hd1.2.2.1), hd3.2.2.2.2.2⟩


/-- The writer append, fresh bump and commit that follow the three decodes, from any
    syntax-bounded state with live writer cells. -/
lemma programBoundedIn_uniform_emit_dispatch_three_branch_tail
    (N : ℕ) (τ : Store) (hτ : StoreValuesLe (uniformEmitSyntaxEnvelope N) τ)
    (hroot : τ 0 = uniformMNat N) (hq : τ (uniformMNat N + uctCurJ) ≠ 0) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) τ
      (Program.seq
        (writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
          uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg)
        (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
          (emitClauseCommitProg uctOuterReg))) := by
  have hS6 : uniformEmitSyntaxEnvelope N ≤
      writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) := by
    simp only [writerAppendRawSixBound, writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  have hstatic : uniformMNat N + uctCurJ ≤ uniformEmitSyntaxEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitSyntaxEnvelope N ∧ uctCurJ ≤
        uniformEmitSyntaxEnvelope N ∧ uctTmpJ ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound, writerAppendRawStepBound,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap, uctCurJ, uctTmpJ]
    omega
  have hidx : uctPolReg ≤ uniformEmitSyntaxEnvelope N ∧ uctVarReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol2Reg ≤ uniformEmitSyntaxEnvelope N ∧ uctVar2Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPol3Reg ≤ uniformEmitSyntaxEnvelope N ∧ uctVar3Reg ≤ uniformEmitSyntaxEnvelope N ∧
      uctPosPolReg ≤ uniformEmitSyntaxEnvelope N ∧ uctNegPolReg ≤ uniformEmitSyntaxEnvelope N ∧
      uctFreshReg ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uctPolReg, uctVarReg, uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg,
      uctPosPolReg, uctNegPolReg, uctFreshReg, uniformEmitSyntaxEnvelope,
      writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitLongValueEnvelope,
      uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap, uctCurJ]
    omega
  have hD1 := uniformEmitDispatchEnvelope_pos N
  have hwriter := programBoundedIn_writerAppendClauseThreeProg_raw_bounds
    (uniformEmitSyntaxEnvelope N) (uniformEmitDispatchEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctFreshReg τ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hstatic hidx hτ hroot hq
    (Nat.le_of_succ_le (uniform_emit_raw_six_bound_syntax_le_dispatch_envelope N))
  have hsf := scanFree_writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg
  have hτ4 : StoreValuesLe (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N))
      ((writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
        uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg).eval τ) :=
    program_eval_storeValuesLe τ _ (by simp only [writerAppendRawSixBound, writerAppendRawThreeBound, writerAppendRawStepBound]; omega) (fun i => (hτ i).trans hS6)
      (programBoundedIn_writerAppendClauseThreeProg_raw_bounds
        (uniformEmitSyntaxEnvelope N) (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N))
        (uniformMNat N) uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg τ uniform_cur_j_bounds.1
        uniform_cur_j_bounds.2 hstatic hidx hτ hroot hq le_rfl) hsf
  have hfresh : (writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
        uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg).eval τ
        uctFreshReg + 1 ≤ uniformEmitDispatchEnvelope N := by
    have hf := hτ4 uctFreshReg
    have hsub := uniformEmitDispatchEnvelope_sub N
    have hmono : writerAppendRawSixBound (uniformEmitSyntaxEnvelope N) ≤
        writerAppendRawSixBound (writerAppendRawSixBound (uniformEmitSyntaxEnvelope N)) := by
      simp only [writerAppendRawSixBound, writerAppendRawThreeBound, writerAppendRawStepBound]
      omega
    omega
  have hempty := programBoundedIn_emitClauseEmptyFreshProg_of_bounds
    (uniformEmitDispatchEnvelope N) uctFreshReg _ (by
      simp only [uctFreshReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
        writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitSyntaxEnvelope,
        uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
        uniformSlackNat, relocateControlGap, uctCurJ]
      omega) hfresh
  have hpost := program_eval_storeValuesLe _ _ hD1
    (program_eval_storeValuesLe τ _ hD1 (fun i => (hτ i).trans
      (uniformEmitSyntaxEnvelope_le_dispatch_envelope N)) hwriter hsf) hempty
    (scanFree_emitClauseEmptyFreshProg uctFreshReg)
  have houter : uctOuterReg ≤ uniformEmitDispatchEnvelope N := by
    simp only [uctOuterReg, uniformEmitDispatchEnvelope, writerAppendRawSixBound,
      writerAppendRawThreeBound, writerAppendRawStepBound]
    omega
  exact ⟨hwriter, hempty, programBoundedIn_emitClauseCommitProg_of_bounds _ uctOuterReg _ hD1
    houter hpost⟩

lemma programBoundedIn_uniform_emit_dispatch_three_branch
    (N base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hstore : StoreValuesLe (uniformEmitLongValueEnvelope N) σdec)
    (hsaved : σdec uctSavedBoundReg = N) :
    ProgramBoundedIn (uniformEmitDispatchEnvelope N) σdec
      (Program.seq
        (decodeLiteralValueProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctSavedBoundReg)
        (Program.seq
          (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
            uctSavedBoundReg)
          (Program.seq
            (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
              uctSavedBoundReg)
            (Program.seq
              (writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
                uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg)
              (Program.seq (emitClauseEmptyFreshProg uctFreshReg)
                (emitClauseCommitProg uctOuterReg)))))) := by
  have hp := uniformEmitDispatchPrologue_of_prep N base outer addr ls rest pref σr σdec hprep hstore
  obtain ⟨⟨hd1, hd2, hd3⟩, hdecS, hroot, hq⟩ :=
    programBoundedIn_uniform_emit_dispatch_three_branch_decodes N σdec hstore hsaved hp.cursor_nonzero
  refine ⟨hd1, hd2, hd3, ?_⟩
  have htail := programBoundedIn_uniform_emit_dispatch_three_branch_tail N _ hdecS
    (hroot.trans hp.root) hq
  simpa only [eval_seq] using htail

end NPComplete.CookLevin

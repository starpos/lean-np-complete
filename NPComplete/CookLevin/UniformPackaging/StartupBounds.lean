module

public import NPComplete.CookLevin.UniformPackaging.IterationFrame
public import NPComplete.CookLevin.UniformPackaging.DispatchShortBounds
public import NPComplete.BoundedWhile.Frame

/-!
# Startup register and frame bounds

Later bounds rely on setup values and high-register frame facts surviving
relocation and parsing. This module proves those startup invariants, including
frame preservation for decoder registers and stores.
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

/-- Along the relocation loop, a register that is neither an output cell nor the source or
destination cursor keeps its post-setup value; the invariant is carried to the same step. -/
lemma storeValuesLe_uniformRelocateProg_tight_frame_upto (bits : Bits) (r : ℕ)
    (hout : ∀ q < bits.length, r ≠ uniformAddrNat bits.length + q)
    (h1 : r ≠ bits.length + relocateSrcJ) (h2 : r ≠ bits.length + relocateDstJ) :
    ∀ t ≤ bits.length,
      RelocateInvariant (bitInputStore bits)
        (loopEval relocateStep t (uniformRelocateSetup.eval (bitInputStore bits)))
        bits.length (uniformAddrNat bits.length) t ∧
      (loopEval relocateStep t (uniformRelocateSetup.eval (bitInputStore bits))) r =
        (uniformRelocateSetup.eval (bitInputStore bits)) r := by
  have h0 : (bitInputStore bits) 0 = bits.length := rfl
  intro t
  induction t with
  | zero =>
      intro _
      exact ⟨by simpa using uniformRelocateSetup_invariant (bitInputStore bits) bits.length h0,
        by simp⟩
  | succ t ih =>
      intro ht
      have hi := ih (by omega)
      rw [uniform_loopEval_succ_right]
      have hInv := relocateStep_invariant (bitInputStore bits)
        (loopEval relocateStep t (uniformRelocateSetup.eval (bitInputStore bits)))
        bits.length (uniformAddrNat bits.length) t (uniformAddrNat_ge_gap bits.length)
        (by omega) hi.1
      refine ⟨hInv, ?_⟩
      have hstep := relocateStep_eval bits.length (uniformAddrNat bits.length) t
        (loopEval relocateStep t (uniformRelocateSetup.eval (bitInputStore bits))) hi.1.1
        (by simpa [relocateSrcJ] using hi.1.2.1) (by simpa [relocateDstJ] using hi.1.2.2.1)
        (uniformAddrNat_ge_gap bits.length)
      rw [hstep, writeReg_diff _ (bits.length + relocateDstJ) _ r h2,
        writeReg_diff _ (bits.length + relocateSrcJ) _ r h1,
        writeReg_diff _ (uniformAddrNat bits.length + t) _ r (hout t (by omega))]
      exact hi.2

/-- Registers outside the relocated block and the two cursors are unchanged by the whole
relocation loop. -/
lemma storeValuesLe_uniformRelocateProg_tight_frame (bits : Bits) (r : ℕ)
    (hout : ∀ q < bits.length, r ≠ uniformAddrNat bits.length + q)
    (h1 : r ≠ bits.length + relocateSrcJ) (h2 : r ≠ bits.length + relocateDstJ) :
    (loopEval relocateStep bits.length
      (uniformRelocateSetup.eval (bitInputStore bits))) r =
      (uniformRelocateSetup.eval (bitInputStore bits)) r :=
  (storeValuesLe_uniformRelocateProg_tight_frame_upto bits r hout h1 h2 bits.length le_rfl).2

/-- The four control cells of the relocation loop end at values bounded by the tight envelope. -/
lemma storeValuesLe_uniformRelocateProg_tight_ctrl (bits : Bits) (K r : ℕ)
    (hC : uniformAddrNat bits.length + bits.length ≤ K)
    (hr : r = bits.length + relocateSrcJ ∨ r = bits.length + relocateDstJ ∨
      r = bits.length + relocateLenJ ∨ r = bits.length + relocateBaseJ) :
    (loopEval relocateStep bits.length
      (uniformRelocateSetup.eval (bitInputStore bits))) r ≤ K := by
  have hInv := uniform_relocate_loop_invariant (bitInputStore bits) bits.length rfl bits.length
    le_rfl
  have hgap := uniformAddrNat_ge_gap bits.length
  simp only [relocateControlGap] at hgap
  rcases hr with rfl | rfl | rfl | rfl
  · have := hInv.2.1
    simp only [relocateSrcJ] at this ⊢
    omega
  · have := hInv.2.2.1
    simp only [relocateDstJ] at this ⊢
    omega
  · have := hInv.2.2.2.1
    simp only [relocateLenJ] at this ⊢
    omega
  · have := hInv.2.2.2.2.1
    simp only [relocateBaseJ] at this ⊢
    omega

/-- A relocated output cell holds an input bit, so it is at most `1` and hence at most `K`. -/
lemma storeValuesLe_uniformRelocateProg_tight_out (bits : Bits) (K q : ℕ)
    (hK1 : 1 ≤ K) (hq : q < bits.length) :
    (loopEval relocateStep bits.length (uniformRelocateSetup.eval (bitInputStore bits)))
      (uniformAddrNat bits.length + q) ≤ K := by
  have hInv := uniform_relocate_loop_invariant (bitInputStore bits) bits.length rfl bits.length
    le_rfl
  have hbit : (bitInputStore bits) (1 + q) ≤ 1 := by
    simp [bitInputStore, Nat.add_comm]
    split <;> omega
  rw [hInv.2.2.2.2.2.1 q hq]
  omega

/-- Every register after the relocation loop is inside the tight envelope: the input cells are
kept, the four control cells are bounded by the block end, and the output cells hold bits. -/
lemma storeValuesLe_uniformRelocateProg_tight_cell (bits : Bits) (K r : ℕ)
    (hK1 : 1 ≤ K) (hC : uniformAddrNat bits.length + bits.length ≤ K)
    (hinit : StoreValuesLe K (bitInputStore bits)) :
    (loopEval relocateStep bits.length
      (uniformRelocateSetup.eval (bitInputStore bits))) r ≤ K := by
  have h0 : (bitInputStore bits) 0 = bits.length := rfl
  have hInv := uniform_relocate_loop_invariant (bitInputStore bits) bits.length rfl bits.length
    le_rfl
  by_cases hctrl : r = bits.length + relocateSrcJ ∨ r = bits.length + relocateDstJ ∨
      r = bits.length + relocateLenJ ∨ r = bits.length + relocateBaseJ
  · exact storeValuesLe_uniformRelocateProg_tight_ctrl bits K r hC hctrl
  by_cases hout : ∃ q < bits.length, r = uniformAddrNat bits.length + q
  · obtain ⟨q, hq, rfl⟩ := hout
    exact storeValuesLe_uniformRelocateProg_tight_out bits K q hK1 hq
  by_cases hlow : r < bits.length + 1
  · rw [hInv.2.2.2.2.2.2 r hlow]
    exact hinit r
  simp only [not_or] at hctrl
  rw [storeValuesLe_uniformRelocateProg_tight_frame bits r (fun q hq heq => hout ⟨q, hq, heq⟩)
    hctrl.1 hctrl.2.1, uniformRelocateSetup_eval bits.length (bitInputStore bits) h0]
  simp [hctrl.1, hctrl.2.1, hctrl.2.2.1, hctrl.2.2.2]
  exact hinit r


lemma storeValuesLe_uniformRelocateProg_tight (φ : CNF) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))) := by
  have hC : uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length ≤
      uniformEmitTightEnvelope (encodeCNF φ).length :=
    uniform_split_tail_input_end_le_tight _
  have hK1 : 1 ≤ uniformEmitTightEnvelope (encodeCNF φ).length := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hinit : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (bitInputStore (encodeCNF φ)) := by
    intro r
    cases r with
    | zero => simpa [bitInputStore] using (by omega : (encodeCNF φ).length ≤
        uniformEmitTightEnvelope (encodeCNF φ).length)
    | succ r =>
        simp [bitInputStore]
        split <;> omega
  intro r
  rw [uniformRelocateProg_eval_eq_loop (bitInputStore (encodeCNF φ)) _ rfl]
  exact storeValuesLe_uniformRelocateProg_tight_cell (encodeCNF φ) _ r hK1 hC hinit

lemma decodeCNFProgramAtSeen_uct_tmp_frame (σ : Store) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctTmpReg = σ uctTmpReg := by
  exact (of_decide_eq_true (by decide +kernel) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).Avoids (fun r => r = uctTmpReg)).eval_frame σ rfl

/-- The clause payload after the outer count stays readable when the count decode changes
only the cursor, outer and done registers. -/
lemma uniform_decode_cursor_le_tight_outer_tail (φ : CNF) (σ0 σ2 : Store)
    (hlists : BitsFrom σ0 (uniformAddrNat (encodeCNF φ).length)
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits)))
    (hframe0 : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r) :
    BitsFrom σ2 (uniformAddrNat (encodeCNF φ).length +
        (φ.clauses.map (fun c => c.lits)).length + 1)
      (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
        ([] : Bits)) := by
  have haddr : 12 ≤ uniformAddrNat (encodeCNF φ).length :=
    (by decide : 12 ≤ 25).trans (uniformAddrNat_ge_25 _)
  have hshape : encodeList (encodeList encodeLiteral)
      (φ.clauses.map (fun c => c.lits)) ++ ([] : Bits) =
      encodeNat (φ.clauses.map (fun c => c.lits)).length ++
        (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
          ([] : Bits)) := by
    simp [encodeList]
  rw [hshape] at hlists
  obtain ⟨_, htailBits0⟩ := bitsFrom_append _ (uniformAddrNat (encodeCNF φ).length)
    (encodeNat (φ.clauses.map (fun c => c.lits)).length)
    (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
      ([] : Bits)) hlists
  intro i hi
  have hfr := hframe0 (uniformAddrNat (encodeCNF φ).length +
    (φ.clauses.map (fun c => c.lits)).length + 1 + i)
    (by simp [uctCursorReg]; omega) (by simp [uctOuterReg]; omega)
    (by simp [uctDoneReg]; omega)
  have haddrEq : uniformAddrNat (encodeCNF φ).length +
      (φ.clauses.map (fun c => c.lits)).length + 1 + i =
      uniformAddrNat (encodeCNF φ).length +
        (encodeNat (φ.clauses.map (fun c => c.lits)).length).length + i := by
    simp only [encodeNat_length]
    omega
  calc
    σ2 (uniformAddrNat (encodeCNF φ).length +
        (φ.clauses.map (fun c => c.lits)).length + 1 + i) =
        σ0 (uniformAddrNat (encodeCNF φ).length +
          (φ.clauses.map (fun c => c.lits)).length + 1 + i) := hfr
    _ = if (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
          ([] : Bits))[i] then 1 else 0 := by
      rw [haddrEq]
      exact htailBits0 i hi

/-- The outer clause-count decode of the uniform producer: the cursor moves past the count,
the outer register holds the number of clauses, the accumulators stay zero and the clause
payload remains readable. -/
lemma uniform_decode_cursor_le_tight_outer (φ : CNF) (σ0 : Store)
    (hb0 : σ0 uctBoundReg = (encodeCNF φ).length)
    (hcursor0 : σ0 uctCursorReg = uniformAddrNat (encodeCNF φ).length)
    (hrem0 : σ0 uctRemainingReg = 0) (hmax0 : σ0 uctMaxReg = 0)
    (hfresh0 : σ0 uctFreshReg = 0) (hcount0 : σ0 uctCountReg = 0)
    (hseen0 : σ0 uctSeenReg = 0)
    (hlists : BitsFrom σ0 (uniformAddrNat (encodeCNF φ).length)
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits))) :
    ∃ σ2 : Store,
      (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval
        ((Program.assign uctOuterReg (.const 0)).eval
          ((Program.assign uctDoneReg (.const 0)).eval σ0)) = σ2 ∧
      σ2 uctOuterReg = (φ.clauses.map (fun c => c.lits)).length ∧
      σ2 uctCursorReg = uniformAddrNat (encodeCNF φ).length +
        (φ.clauses.map (fun c => c.lits)).length + 1 ∧
      σ2 uctMaxReg = 0 ∧ σ2 uctFreshReg = 0 ∧ σ2 uctCountReg = 0 ∧ σ2 uctSeenReg = 0 ∧
      σ2 uctRemainingReg = 0 ∧ σ2 uctBoundReg = (encodeCNF φ).length ∧
      BitsFrom σ2 (uniformAddrNat (encodeCNF φ).length +
          (φ.clauses.map (fun c => c.lits)).length + 1)
        (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
          ([] : Bits)) := by
  have haddr : 12 ≤ uniformAddrNat (encodeCNF φ).length :=
    (by decide : 12 ≤ 25).trans (uniformAddrNat_ge_25 _)
  have houterBelow :
      uctCursorReg < uniformAddrNat (encodeCNF φ).length ∧
        uctOuterReg < uniformAddrNat (encodeCNF φ).length ∧
        uctDoneReg < uniformAddrNat (encodeCNF φ).length := by
    simp [uctCursorReg, uctOuterReg, uctDoneReg]
    omega
  obtain ⟨hcursorEnd, houterEnd, hdoneEnd, hframe0⟩ :=
    decode_cnf_outer_decode uctCursorReg uctOuterReg uctDoneReg (encodeCNF φ).length
      (uniformAddrNat (encodeCNF φ).length)
      (φ.clauses.map (fun c => c.lits)) ([] : Bits) σ0
      (by decide) (by decide) (by decide) houterBelow hcursor0
      (by simpa using encodeCNF_length_ge_clauseCount φ) hlists
  set σ2 := (decodeNatProgram uctCursorReg uctOuterReg uctDoneReg (encodeCNF φ).length).eval
    ((Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval σ0)) with hσ2def
  have hAtEq : (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval
      ((Program.assign uctOuterReg (.const 0)).eval
        ((Program.assign uctDoneReg (.const 0)).eval σ0)) = σ2 := by
    have hb2 : ((Program.assign uctOuterReg (.const 0)).eval
        ((Program.assign uctDoneReg (.const 0)).eval σ0)) uctBoundReg =
        (encodeCNF φ).length := by
      simp only [eval_assign, Expr.eval]
      rw [writeReg_diff _ uctOuterReg 0 uctBoundReg (by decide),
        writeReg_diff σ0 uctDoneReg 0 uctBoundReg (by decide)]
      exact hb0
    rw [hσ2def]
    exact decodeNatProgramAt_eq uctCursorReg uctOuterReg uctDoneReg uctBoundReg _ _ hb2
  have htailBits2 := uniform_decode_cursor_le_tight_outer_tail φ σ0 σ2 hlists hframe0
  exact ⟨σ2, hAtEq, houterEnd, hcursorEnd,
    (hframe0 uctMaxReg (by decide) (by decide) (by decide)).trans hmax0,
    (hframe0 uctFreshReg (by decide) (by decide) (by decide)).trans hfresh0,
    (hframe0 uctCountReg (by decide) (by decide) (by decide)).trans hcount0,
    (hframe0 uctSeenReg (by decide) (by decide) (by decide)).trans hseen0,
    (hframe0 uctRemainingReg (by decide) (by decide) (by decide)).trans hrem0,
    (hframe0 uctBoundReg (by decide) (by decide) (by decide)).trans hb0, htailBits2⟩

/-- Once the outer count is decoded, the clause loop of the uniform decoder leaves the cursor
at the end of the clause payload. -/
lemma uniform_decode_cursor_le_tight_loop (φ : CNF) (σ0 σ2 : Store)
    (hAtEq : (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval
        ((Program.assign uctOuterReg (.const 0)).eval
          ((Program.assign uctDoneReg (.const 0)).eval σ0)) = σ2)
    (houter : σ2 uctOuterReg = (φ.clauses.map (fun c => c.lits)).length)
    (hcursor : σ2 uctCursorReg = uniformAddrNat (encodeCNF φ).length +
      (φ.clauses.map (fun c => c.lits)).length + 1)
    (hmax : σ2 uctMaxReg = 0) (hfresh : σ2 uctFreshReg = 0) (hcount : σ2 uctCountReg = 0)
    (hseen : σ2 uctSeenReg = 0) (hrem : σ2 uctRemainingReg = 0)
    (hbound : σ2 uctBoundReg = (encodeCNF φ).length)
    (hbits : BitsFrom σ2 (uniformAddrNat (encodeCNF φ).length +
          (φ.clauses.map (fun c => c.lits)).length + 1)
        (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten ++
          ([] : Bits))) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0 uctCursorReg =
      uniformAddrNat (encodeCNF φ).length + (φ.clauses.map (fun c => c.lits)).length + 1 +
        ((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten.length := by
  have hbelow : 25 ≤ uniformAddrNat (encodeCNF φ).length +
      (φ.clauses.map (fun c => c.lits)).length + 1 := by
    have h := uniformAddrNat_ge_25 (encodeCNF φ).length
    omega
  have hloop := decodeCNFStepAtSeen_seen_loop_uct_eval (encodeCNF φ).length
    (φ.clauses.map (fun c => c.lits)) ([] : Bits)
    (uniformAddrNat (encodeCNF φ).length + (φ.clauses.map (fun c => c.lits)).length + 1)
    0 0 0 0 σ2 houter hcursor hmax hfresh hcount hseen hrem hbound
    hbelow (encodeCNF_scan_bounds φ) hbits
  have hprogeq : (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0 = loopEval
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg)
      (φ.clauses.map (fun c => c.lits)).length σ2 := by
    unfold decodeCNFProgramAtSeen
    rw [eval_seq, eval_seq, eval_seq, eval_forN, hAtEq]
    simp only [Expr.eval, houter]
  rw [hprogeq, hloop.1]

/-- The end of the clause payload lies inside the tight envelope. -/
lemma uniform_decode_cursor_le_tight_end (φ : CNF) :
    uniformAddrNat (encodeCNF φ).length + (φ.clauses.map (fun c => c.lits)).length + 1 +
      ((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten.length ≤
      uniformEmitTightEnvelope (encodeCNF φ).length := by
  have hC := uniform_split_tail_input_end_le_tight (encodeCNF φ).length
  have hwindow := uniform_producer_input_end_window φ
  have henc :
      ((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten =
        (φ.clauses.map encodeClause).flatten := by
    rw [List.map_map]
    have hfun : (encodeList encodeLiteral ∘ fun c : Clause => c.lits) = encodeClause := by
      funext c
      simp [NPComplete.CookLevin.encodeClause]
    rw [hfun]
  rw [henc]
  simpa [List.length_map] using hwindow.trans hC

lemma uniform_decode_cursor_le_tight (φ : CNF) :
    let bits := encodeCNF φ
    let N := bits.length
    let σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    let σd :=
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0
    σd uctCursorReg ≤ uniformEmitTightEnvelope N := by
  set bits := encodeCNF φ
  set N := bits.length
  set σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  set σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  change σd uctCursorReg ≤ uniformEmitTightEnvelope N
  obtain ⟨hb0, hbase0, hcursor0, hpol0, hvar0, hdone0, houter0, hrem0, hmax0, hlen0,
    hfresh0, hcount0, htmp0, hseen0⟩ := uniformControlInitProg_after_cursor bits
  have hlists : BitsFrom σ0 (uniformAddrNat N)
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits)) := by
    simpa [σ0, bits, N, encodeCNF_eq_lists, List.append_nil] using
      uniformControlInitProg_bitsFrom bits
  obtain ⟨σ2, hAtEq, houter, hcursor, hmax, hfresh, hcount, hseen, hrem, hbound, hbits⟩ :=
    uniform_decode_cursor_le_tight_outer φ σ0 hb0 hcursor0 hrem0 hmax0 hfresh0 hcount0 hseen0
      hlists
  have hloop := uniform_decode_cursor_le_tight_loop φ σ0 σ2 hAtEq houter hcursor hmax hfresh
    hcount hseen hrem hbound hbits
  change (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
    uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
    uctBoundReg uctSeenReg).eval σ0 uctCursorReg ≤ _
  rw [hloop]
  exact uniform_decode_cursor_le_tight_end φ

lemma storeValuesLe_uniform_start_assign_tight (K M : ℕ) (σr : Store)
    (hσr : StoreValuesLe K σr) (h0r : σr 0 = M)
    (hstart : uniformStartNat ≤ K) :
    StoreValuesLe K ((ctlAssign uctCurJ uniformStartE).eval σr) := by
  intro r
  by_cases hr : r = M + uctCurJ
  · subst r
    have hi := ctlAssign_eval_same uctCurJ uniformStartE σr
    rw [h0r, uniformStartE_eval] at hi
    have hval : ((ctlAssign uctCurJ uniformStartE).eval σr) (M + uctCurJ) =
        uniformStartNat := by
      simpa [uctCurJ] using hi
    calc
      ((ctlAssign uctCurJ uniformStartE).eval σr) (M + uctCurJ) = uniformStartNat := hval
      _ ≤ K := hstart
  · have hi := ctlAssign_eval_diff uctCurJ uniformStartE σr r
      (by rw [h0r]; exact hr)
    calc
      ((ctlAssign uctCurJ uniformStartE).eval σr) r = σr r := hi
      _ ≤ K := hσr r

lemma storeValuesLe_uniform_rewind_tight (φ : CNF) (σa : Store)
    (hσa : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σa)
    (hrew :
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σa uctCursorReg =
        uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1 ∧
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σa uctOuterReg = φ.clauses.length ∧
      (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σa uctDoneReg = 1 ∧
      (∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg →
        (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
          uctSavedBoundReg).eval σa r = σa r)) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      ((secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σa) := by
  set N := (encodeCNF φ).length
  set K := uniformEmitTightEnvelope N
  set C := uniformAddrNat N
  have hK1 : 1 ≤ K := by
    change 1 ≤ uniformEmitTightEnvelope N
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hC : C + N ≤ K := by
    change uniformAddrNat N + N ≤ uniformEmitTightEnvelope N
    exact uniform_split_tail_input_end_le_tight N
  have hN : N ≤ K := by omega
  have hcountPhi : φ.clauses.length ≤ K := by
    have h : φ.clauses.length + 1 ≤ N := by
      simpa [N] using encodeCNF_length_ge_clauseCount φ
    omega
  have hσaK : StoreValuesLe K σa := by
    simpa [K, N] using hσa
  have hresult : StoreValuesLe K
      ((secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg).eval σa) := by
    intro r
    by_cases hc : r = uctCursorReg
    · subst r
      rw [hrew.1]
      have h : φ.clauses.length + 1 ≤ N := by
        simpa [N] using encodeCNF_length_ge_clauseCount φ
      omega
    by_cases ho : r = uctOuterReg
    · subst r
      rw [hrew.2.1]
      exact hcountPhi
    by_cases hd : r = uctDoneReg
    · subst r
      rw [hrew.2.2.1]
      exact hK1
    have hframe := hrew.2.2.2 r hc ho hd
    calc
      _ = σa r := hframe
      _ ≤ K := hσaK r
  simpa [K, N] using hresult

lemma programBoundedIn_uniform_writer_append_header_tight (φ : CNF) (σi : Store)
    (hstartI : WriterState σi (uniformMNat (encodeCNF φ).length) uctCurJ uniformStartNat [])
    (hnumI : σi uctFreshReg = (toThreeCNF φ).numVars)
    (hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length) :
    ProgramBoundedIn (uniformEmitTightEnvelope (encodeCNF φ).length) σi
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg) := by
  set bits := encodeCNF φ
  set N := bits.length
  set K := uniformEmitTightEnvelope N
  set M := uniformMNat N
  set start := uniformStartNat
  set numVars := (toThreeCNF φ).numVars
  set clauseCount := (toThreeCNF φ).clauses.length
  have hK25 : 25 ≤ K := by
    change 25 ≤ uniformEmitTightEnvelope N
    have hM := uniformMNat_ge_25 N
    simp [uniformEmitTightEnvelope]
  have hM25 : 25 ≤ M := by
    change 25 ≤ uniformMNat N
    exact uniformMNat_ge_25 N
  have hC : uniformAddrNat N + N ≤ K := by
    change uniformAddrNat N + N ≤ uniformEmitTightEnvelope N
    exact uniform_split_tail_input_end_le_tight N
  have hN : N ≤ K := by omega
  have hMA : M + 2 < uniformAddrNat N := by
    change uniformMNat N + 2 < uniformAddrNat N
    exact uniformMNat_add_two_lt_addr N
  have hMbound : M ≤ K := by omega
  have hnum : numVars ≤ K := by
    have h := toThreeCNF_numVars_le_tight_envelope φ
    simpa [numVars, K, N, bits] using h
  have hcount : clauseCount ≤ K := by
    have h : clauseCount + 1 ≤ N := by
      simpa [clauseCount, N, bits] using toThreeCNF_count_le_encodeCNF φ
    omega
  have hstartI' : WriterState σi M uctCurJ start [] := by
    simpa [M, start, N, bits] using hstartI
  have hnumI' : σi uctFreshReg = numVars := by
    simpa [numVars] using hnumI
  have hcountI' : σi uctCountReg = clauseCount := by
    simpa [clauseCount] using hcountI
  have hroom1 : start + numVars + 1 < M + uctCurJ := by
    have h : start + numVars + clauseCount + 2 < M + uctCurJ := by
      simpa [start, M, numVars, clauseCount, N, bits] using uniform_header_room φ
    omega
  have hroom1' : start + ([] : Bits).length +
      (.reg uctFreshReg : Expr).eval σi + 1 < M + uctCurJ := by
    change start + 0 + σi uctFreshReg + 1 < M + uctCurJ
    rw [hnumI']
    exact hroom1
  have hp1 := programBoundedIn_writerAppendNatProg_of_state K M uctCurJ uctTmpJ
    start [] (.reg uctFreshReg) σi hstartI' uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    (by simp [uctCurJ]; omega) (by simp [uctTmpJ]; omega)
    (by have := uniform_emit_writer_layout_le_tight N; simpa [K, M] using this.2.2.1)
    (by have := uniform_emit_writer_layout_le_tight N; simpa [K, M] using this.2.2.2)
    (by simp only [ExprBoundedIn, uctFreshReg]; omega) hroom1'
  let σh1 := (writerAppendNatProg uctCurJ uctTmpJ (.reg uctFreshReg)).eval σi
  have hs1 : WriterState σh1 M uctCurJ start (encodeNat numVars) := by
    simpa [σh1, Expr.eval, hnumI'] using writerAppendNatProg_eval M uctCurJ uctTmpJ start []
      (.reg uctFreshReg) σi uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hstartI'
      (by simpa [hnumI'] using hroom1')
  have hcount1 : σh1 uctCountReg = clauseCount := by
    have hf := writerAppendNatProg_frame M uctCurJ uctTmpJ start []
      (.reg uctFreshReg) σi uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hstartI'
      (by simpa [hnumI'] using hroom1')
      (r := uctCountReg)
      (by norm_num [start, uctCountReg, uniformStartNat, relocateControlGap])
    simpa [σh1] using hf.trans hcountI'
  have hroom2 : start + (encodeNat numVars).length + clauseCount + 1 < M + uctCurJ := by
    have h : start + numVars + clauseCount + 2 < M + uctCurJ := by
      simpa [start, M, numVars, clauseCount, N, bits] using uniform_header_room φ
    simp only [encodeNat_length]
    omega
  have hroom2' : start + (encodeNat numVars).length +
      (.reg uctCountReg : Expr).eval σh1 + 1 < M + uctCurJ := by
    change start + (encodeNat numVars).length + σh1 uctCountReg + 1 < M + uctCurJ
    rw [hcount1]
    exact hroom2
  have hp2 := programBoundedIn_writerAppendNatProg_of_state K M uctCurJ uctTmpJ
    start (encodeNat numVars) (.reg uctCountReg) σh1 hs1 uniform_cur_j_bounds.1
    uniform_cur_j_bounds.2 (by simp [uctCurJ]; omega) (by simp [uctTmpJ]; omega)
    (by have := uniform_emit_writer_layout_le_tight N; simpa [K, M] using this.2.2.1)
    (by have := uniform_emit_writer_layout_le_tight N; simpa [K, M] using this.2.2.2)
    (by simp only [ExprBoundedIn, uctCountReg]; omega) hroom2'
  have hheader : ProgramBoundedIn K σi
      (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg) := by
    simpa [writerAppendHeaderProg, σh1, eval_seq] using ⟨hp1, hp2⟩
  simpa [K, N, bits] using hheader

/-- The control-initialised store (relocated input, cursor and control registers) respects the
tight envelope. -/
lemma uniformProducerResetStore_tight_init (φ : CNF) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))) := by
  set bits := encodeCNF φ
  set N := bits.length
  set K := uniformEmitTightEnvelope N
  set σI := bitInputStore bits
  set σR := uniformRelocateProg.eval σI
  have hK1 : 1 ≤ K := by
    change 1 ≤ uniformEmitTightEnvelope N
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hK25 : 25 ≤ K := by
    change 25 ≤ uniformEmitTightEnvelope N
    have hM := uniformMNat_ge_25 N
    simp [uniformEmitTightEnvelope]
  have hC : uniformAddrNat N + N ≤ K := by
    change uniformAddrNat N + N ≤ uniformEmitTightEnvelope N
    exact uniform_split_tail_input_end_le_tight N
  have hN : N ≤ K := by omega
  have hσI : StoreValuesLe K σI := by
    intro r
    cases r with
    | zero =>
        change bits.length ≤ K
        exact hN
    | succ r =>
        simp [σI, bitInputStore]
        split <;> omega
  have hσR : StoreValuesLe K σR := by
    simpa [σR, σI, bits, N, K] using storeValuesLe_uniformRelocateProg_tight φ
  have hR0 : σR 0 = N := by
    simpa [σR, σI] using (uniformRelocateProg_bitInputStore bits).1
  have haddr : uniformAddrE.eval σR ≤ K := by
    rw [uniformAddrE_eval, hR0]
    have h := uniform_split_tail_input_end_le_tight N
    change uniformAddrNat N ≤ uniformEmitTightEnvelope N
    omega
  have hσ1 : StoreValuesLe K ((Program.assign uctInputBaseReg uniformAddrE).eval σR) :=
    storeValuesLe_assign hσR haddr
  have hσC : StoreValuesLe K ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval σR) := by
    have hcursorExpr : (.reg uctInputBaseReg : Expr).eval
        ((Program.assign uctInputBaseReg uniformAddrE).eval σR) ≤ K := by
      simpa [Expr.eval] using hσ1 uctInputBaseReg
    simpa [uniformCursorInitProg, eval_seq] using storeValuesLe_assign hσ1 hcursorExpr
  exact program_eval_storeValuesLe _ uniformControlInitProg hK1 hσC
    (programBoundedIn_uniformControlInitProg K _ hK25) scanFree_uniformControlInitProg

/-- The decoder pass computes the variable maximum, fresh base, clause count and seen flag
statistics, and fixes every register outside its working set. -/
lemma uniformProducerResetStore_tight_decode_stats (φ : CNF) (σ0 σd : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
    (hσd : σd = (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0) :
    σd uctMaxReg = cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    σd uctFreshReg = cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    σd uctCountReg = (toThreeCNF φ).clauses.length ∧
    σd uctSeenReg = cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    σd uctRemainingReg = 0 ∧ σd uctOuterReg = 0 ∧ σd uctBoundReg = (encodeCNF φ).length ∧
    ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg → σd r = σ0 r := by
  set bits := encodeCNF φ
  set N := bits.length
  obtain ⟨hb0, hbase0, hcursor0, hpol0, hvar0, hdone0, houter0, hrem0, hmax0, hlen0, hfresh0,
    hcount0, htmp0, hseen0⟩ := uniformControlInitProg_after_cursor bits
  have hscan : ∀ ls ∈ φ.clauses.map (fun c => c.lits),
      ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N := by
    simpa [N, bits] using encodeCNF_scan_bounds φ
  have hbits0 : BitsFrom σ0 (uniformAddrNat N)
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits)) := by
    simpa [hσ0, bits, N, encodeCNF_eq_lists, List.append_nil] using
      uniformControlInitProg_bitsFrom bits
  subst hσd
  obtain ⟨hmaxD, hfreshD, hcountD, hseenD, hremD, houterD, hboundD, hframeD⟩ :=
    decodeCNFProgramAtSeen_uct_append N (φ.clauses.map (fun c => c.lits)) ([] : Bits)
      (uniformAddrNat N) 0 0 0 0 σ0
      (by simpa using encodeCNF_length_ge_clauseCount φ) (uniformAddrNat_ge_25 N)
      (by simpa [hσ0, bits, N] using hcursor0) (by simpa [hσ0, bits, N] using hrem0)
      (by simpa [hσ0, bits, N] using hmax0) (by simpa [hσ0, bits, N] using hfresh0)
      (by simpa [hσ0, bits, N] using hcount0) (by simpa [hσ0, bits, N] using hseen0)
      (by simpa [hσ0, bits, N] using hb0) hscan hbits0
  exact ⟨hmaxD, hfreshD,
    by simpa using hcountD.trans (by simpa using cnfThreeCountStat_toThreeCNF φ),
    hseenD, hremD, houterD, hboundD, hframeD⟩

/-- The fresh base counted by the decoder never exceeds the final number of variables, because
the post-decode statistics add it to the largest variable. -/
lemma uniformProducerResetStore_tight_fresh_base_le (φ : CNF) :
    cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)) ≤ (toThreeCNF φ).numVars := by
  have hpre := uniform_producer_pre_startup φ
  simp only at hpre
  set σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))) with hσ0
  set σd := (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0 with hσd
  obtain ⟨hmaxD, hfreshD, -, hseenD, -⟩ :=
    uniformProducerResetStore_tight_decode_stats φ σ0 σd hσ0 hσd
  have hpost := uniformPostDecodeStatsProg_eval σd _ _ _ hmaxD hfreshD hseenD
  have hσpFresh : (uniformPostDecodeStatsProg.eval σd) uctFreshReg = (toThreeCNF φ).numVars := by
    have ha := uniformSetArenaProg_frame
      (uniformSaveBoundProg.eval (uniformPostDecodeStatsProg.eval σd)) (r := uctFreshReg)
      (by decide)
    have hs := (uniformSaveBoundProg_eval (uniformPostDecodeStatsProg.eval σd)).2 uctFreshReg
      (by decide)
    exact (ha.trans hs).symm.trans hpre.2.2.2.1
  rw [hpost.2.1] at hσpFresh
  omega

/-- The store after the decoder pass respects the tight envelope. -/
lemma uniformProducerResetStore_tight_decoded_store (φ : CNF) (σ0 σd : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
    (hσd : σd = (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0)
    (hσ0le : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ0) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σd := by
  set N := (encodeCNF φ).length
  set K := uniformEmitTightEnvelope N
  have hK25 : 25 ≤ K := by
    change 25 ≤ uniformEmitTightEnvelope N
    have hM := uniformMNat_ge_25 N
    simp [uniformEmitTightEnvelope]
  have hC : uniformAddrNat N + N ≤ K := uniform_split_tail_input_end_le_tight N
  have hN : N ≤ K := by omega
  have hnum : (toThreeCNF φ).numVars ≤ K := by
    simpa [K, N] using toThreeCNF_numVars_le_tight_envelope φ
  have hcount : (toThreeCNF φ).clauses.length ≤ K := by
    have h : (toThreeCNF φ).clauses.length + 1 ≤ N := by
      simpa [N] using toThreeCNF_count_le_encodeCNF φ
    omega
  have hscan : ∀ ls ∈ φ.clauses.map (fun c => c.lits),
      ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N := by
    simpa [N] using encodeCNF_scan_bounds φ
  obtain ⟨hmaxD, hfreshD, hcountD, hseenD, hremD, houterD, -, hframeD⟩ :=
    uniformProducerResetStore_tight_decode_stats φ σ0 σd hσ0 hσd
  have hcursorD : σd uctCursorReg ≤ K := by
    subst hσ0 hσd
    simpa [N, K] using uniform_decode_cursor_le_tight φ
  obtain ⟨hpolD, hvarD, hdoneD, hlenD, hseenDlow⟩ := uniform_decode_state_low_regs φ
  have hmaxN : cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) ≤ N :=
    cnfLiteralVarMaxStat_le N 0 _ (by omega) (fun ls hls l hl => (hscan ls hls).2 l hl)
  have hfd : σd uctFreshReg ≤ (toThreeCNF φ).numVars := by
    rw [hfreshD]; exact uniformProducerResetStore_tight_fresh_base_le φ
  have htmpD : σd uctTmpReg ≤ K := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, htmp0, -⟩ :=
      uniformControlInitProg_after_cursor (encodeCNF φ)
    have htmpFrame := decodeCNFProgramAtSeen_uct_tmp_frame σ0
    rw [show σd uctTmpReg = σ0 uctTmpReg by subst hσd; simpa using htmpFrame,
      show σ0 uctTmpReg = 0 by subst hσ0; simpa using htmp0]
    omega
  subst hσ0 hσd
  intro r
  by_cases hr : r ∈ ([uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctOuterReg,
      uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg,
      uctTmpReg, uctSeenReg] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcursorD
    · exact hpolD.trans (by omega)
    · exact hvarD.trans hN
    · exact hdoneD.trans (by omega)
    · rw [houterD]; omega
    · rw [hremD]; omega
    · rw [hmaxD]; exact hmaxN.trans hN
    · exact hlenD.trans hN
    · exact hfd.trans hnum
    · rw [hcountD]; exact hcount
    · exact htmpD
    · rw [hseenD]
      have hs := cnfSeenStat_le_one 0 (φ.clauses.map (fun c => c.lits)) (by decide)
      omega
  · rw [hframeD r (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])
      (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])
      (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])
      (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])
      (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])
      (by intro h; apply hr; simp [h]) (by intro h; apply hr; simp [h])]
    exact hσ0le r

/-- The pre-startup facts of the arena store, restated from the producer relation. -/
lemma uniformProducerResetStore_tight_pre_facts (φ : CNF) (σa : Store)
    (hσa : σa = uniformSetArenaProg.eval (uniformSaveBoundProg.eval
      (uniformPostDecodeStatsProg.eval
        ((decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg).eval
          (uniformControlInitProg.eval
            ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
              (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))))))) :
    UniformProducerPreStartupFacts φ (encodeCNF φ).length σa := by
  have hpre := uniform_producer_pre_startup φ
  simp only at hpre
  rw [← hσa] at hpre
  exact {
    root := hpre.1
    savedBound := hpre.2.1
    inputBase := hpre.2.2.1
    fresh := hpre.2.2.2.1
    count := hpre.2.2.2.2.1
    maxValue := hpre.2.2.2.2.2.1
    inputBits := hpre.2.2.2.2.2.2
  }

/-- The arena store (post-decode statistics, saved bound and arena root) respects the tight
envelope: the statistics are bounded by the variable and clause counts and the root is `M`. -/
lemma uniformProducerResetStore_tight_arena_store (φ : CNF) (σd σa : Store)
    (hσa : σa = uniformSetArenaProg.eval (uniformSaveBoundProg.eval
      (uniformPostDecodeStatsProg.eval σd)))
    (hσd : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σd)
    (hmaxD : σd uctMaxReg = cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)))
    (hfreshD : σd uctFreshReg = cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)))
    (hseenD : σd uctSeenReg = cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)))
    (hboundD : σd uctBoundReg = (encodeCNF φ).length)
    (hpre : UniformProducerPreStartupFacts φ (encodeCNF φ).length σa) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σa := by
  set N := (encodeCNF φ).length
  set K := uniformEmitTightEnvelope N
  set σp := uniformPostDecodeStatsProg.eval σd
  set σs := uniformSaveBoundProg.eval σp
  have hK25 : 25 ≤ K := by
    change 25 ≤ uniformEmitTightEnvelope N
    have hM := uniformMNat_ge_25 N
    simp [uniformEmitTightEnvelope]
  have hC : uniformAddrNat N + N ≤ K := uniform_split_tail_input_end_le_tight N
  have hN : N ≤ K := by omega
  have hnum : (toThreeCNF φ).numVars ≤ K := by
    simpa [K, N] using toThreeCNF_numVars_le_tight_envelope φ
  have hvarBound : cnfVarBound φ ≤ N := by simpa [N] using cnfVarBound_le_encodeCNF φ
  have hfreshStat := uniformProducerResetStore_tight_fresh_base_le φ
  have hpost := uniformPostDecodeStatsProg_eval σd _ _ _ hmaxD hfreshD hseenD
  have hσpFresh : σp uctFreshReg = (toThreeCNF φ).numVars := by
    have ha := uniformSetArenaProg_frame σs (r := uctFreshReg) (by decide)
    have hs := (uniformSaveBoundProg_eval σp).2 uctFreshReg (by decide)
    rw [hσa] at hpre
    exact (ha.trans hs).symm.trans hpre.fresh
  have hσpMax : σp uctMaxReg = cnfVarBound φ := by
    have ha := uniformSetArenaProg_frame σs (r := uctMaxReg) (by decide)
    have hs := (uniformSaveBoundProg_eval σp).2 uctMaxReg (by decide)
    rw [hσa] at hpre
    exact (ha.trans hs).symm.trans hpre.maxValue
  have hσpFrame : ∀ r, r ∉ ([uctTmpReg, uctMaxReg, uctFreshReg] : List ℕ) → σp r = σd r := by
    intro r hr
    apply uniformPostDecodeStatsProg_frame σd
    · intro h; apply hr; simp [h]
    · intro h; apply hr; simp [h]
    · intro h; apply hr; simp [h]
  have hσpChanged : ∀ r, r ∈ ([uctTmpReg, uctMaxReg, uctFreshReg] : List ℕ) → σp r ≤ K := by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [show σp uctTmpReg = _ from hpost.2.2.1]
      exact hfreshStat.trans hnum
    · rw [hσpMax]; exact hvarBound.trans hN
    · rw [hσpFresh]; exact hnum
    · simp at hr
  have hσp : StoreValuesLe K σp :=
    storeValuesLe_of_frame K σd σp [uctTmpReg, uctMaxReg, uctFreshReg] hσd hσpFrame hσpChanged
  have hσp0 : σp 0 = N := by
    have hf := uniformPostDecodeStatsProg_frame σd (r := 0) (by decide) (by decide) (by decide)
    exact hf.trans (by simpa [uctBoundReg] using hboundD)
  have hsaved : σs uctSavedBoundReg = N := (uniformSaveBoundProg_eval σp).1.trans hσp0
  have hσs : StoreValuesLe K σs := by
    refine storeValuesLe_of_frame K σp σs [uctSavedBoundReg] hσp ?_ ?_
    · intro r hr
      simp only [List.mem_singleton] at hr
      exact (uniformSaveBoundProg_eval σp).2 r hr
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [hsaved]
      exact hN
  have hMbound : uniformMNat N ≤ K := by
    have := uniformMNat_add_two_lt_addr N
    omega
  refine storeValuesLe_of_frame K σs σa [0] hσs ?_ ?_
  · intro r hr
    simp only [List.mem_singleton] at hr
    rw [hσa]
    exact uniformSetArenaProg_frame σs hr
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hm : uniformME.eval σs = uniformMNat N := uniformME_eval σs N hsaved
    rw [hσa, uniformSetArenaProg_eval, hm]
    exact hMbound

/-- From the arena store, the second-pass startup (rewind, start assignment, header append)
followed by the auxiliary initialisation, fresh-from-max and reset programs respects the
tight envelope. -/
lemma uniformProducerResetStore_tight_startup (φ : CNF) (σa : Store)
    (hσa : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σa)
    (hpre : UniformProducerPreStartupFacts φ (encodeCNF φ).length σa) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (uniformEmitResetProg.eval (uniformFreshFromMaxProg.eval (uniformEmitAuxInitProg.eval
        ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
          uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa)))) := by
  set N := (encodeCNF φ).length
  set K := uniformEmitTightEnvelope N
  have hK1 : 1 ≤ K := by
    change 1 ≤ uniformEmitTightEnvelope N
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hK25 : 25 ≤ K := by
    change 25 ≤ uniformEmitTightEnvelope N
    have hM := uniformMNat_ge_25 N
    simp [uniformEmitTightEnvelope]
  have hCstart : uniformStartNat ≤ K := by
    have h := uniformAddrNat_ge_start N
    have hC : uniformAddrNat N + N ≤ K := uniform_split_tail_input_end_le_tight N
    omega
  have hM25 : 25 ≤ uniformMNat N := uniformMNat_ge_25 N
  have hrew := uniform_rewind_eval φ σa hpre.savedBound hpre.inputBase hpre.inputBits
  set σr := (secondPassRewindProgramAt uctCursorReg uctInputBaseReg uctOuterReg
    uctDoneReg uctSavedBoundReg).eval σa
  have hσr : StoreValuesLe K σr := storeValuesLe_uniform_rewind_tight φ σa hσa hrew
  have h0r : σr 0 = uniformMNat N :=
    (hrew.2.2.2 0 (by decide) (by decide) (by decide)).trans hpre.root
  set σi := (ctlAssign uctCurJ uniformStartE).eval σr
  have hσi : StoreValuesLe K σi := storeValuesLe_uniform_start_assign_tight K _ σr hσr h0r hCstart
  have hstartI : WriterState σi (uniformMNat N) uctCurJ uniformStartNat [] := by
    have h0i : σi 0 = uniformMNat N :=
      (ctlAssign_zero uctCurJ uniformStartE σr (by decide)).trans h0r
    have hcuri : σi (uniformMNat N + uctCurJ) = uniformStartNat := by
      have hi := ctlAssign_eval_same uctCurJ uniformStartE σr
      rw [h0r, uniformStartE_eval] at hi
      simpa [σi, uctCurJ] using hi
    exact writerInit_mk _ uctCurJ _ σi h0i hcuri
      (by simp [uniformStartNat, relocateControlGap]) (uniform_layout_start_lt_M N)
  have hnumI : σi uctFreshReg = (toThreeCNF φ).numVars := by
    have hr : σr uctFreshReg = σa uctFreshReg :=
      hrew.2.2.2 uctFreshReg (by decide) (by decide) (by decide)
    have hi := ctlAssign_eval_diff uctCurJ uniformStartE σr uctFreshReg
      (by simp [h0r, uctFreshReg, uctCurJ]; omega)
    exact hi.trans (hr.trans hpre.fresh)
  have hcountI : σi uctCountReg = (toThreeCNF φ).clauses.length := by
    have hr : σr uctCountReg = σa uctCountReg :=
      hrew.2.2.2 uctCountReg (by decide) (by decide) (by decide)
    have hi := ctlAssign_eval_diff uctCurJ uniformStartE σr uctCountReg
      (by simp [h0r, uctCountReg, uctCurJ]; omega)
    exact hi.trans (hr.trans hpre.count)
  have hheader := programBoundedIn_uniform_writer_append_header_tight φ σi hstartI hnumI hcountI
  have hσst : StoreValuesLe K
      ((secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa) := by
    have hseq : (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
        uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg).eval σa =
        (writerAppendHeaderProg uctCurJ uctTmpJ uctFreshReg uctCountReg).eval σi := by
      simp [secondPassStartupProgramAt, σr, σi, eval_seq]
    rw [hseq]
    exact program_eval_storeValuesLe σi _ hK1 hσi hheader
      (scanFree_writerAppendHeaderProg _ _ _ _)
  exact storeValuesLe_uniformEmitResetProg K _ hK1
    (storeValuesLe_uniformFreshFromMaxProg K _ hK1
      (storeValuesLe_uniformEmitAuxInitProg K _ hK1 hσst hK25) hK25) hK25

lemma uniformProducerResetStore_tight (φ : CNF) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (uniformProducerResetStore φ) := by
  have hσ0 := uniformProducerResetStore_tight_init φ
  obtain ⟨hmaxD, hfreshD, -, hseenD, -, -, hboundD, -⟩ :=
    uniformProducerResetStore_tight_decode_stats φ _ _ rfl rfl
  have hσd := uniformProducerResetStore_tight_decoded_store φ _ _ rfl rfl hσ0
  have hpre := uniformProducerResetStore_tight_pre_facts φ _ rfl
  exact uniformProducerResetStore_tight_startup φ _
    (uniformProducerResetStore_tight_arena_store φ _ _ rfl hσd hmaxD hfreshD hseenD hboundD
      hpre)
    hpre

end NPComplete.CookLevin

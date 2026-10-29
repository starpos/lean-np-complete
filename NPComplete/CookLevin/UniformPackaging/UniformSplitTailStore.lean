module

public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailBounds

/-!
# Uniform split-tail store and cost bounds

The split-tail loop executes over a store whose register values and costs must
stay within a common envelope. This module proves store bounds from semantic
reachability and bounds the primitive writer-operation costs on that path.
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

lemma programBoundedIn_uniform_emit_decode_of_rel
    (N : ℕ) (c : Clause) (cs : List Clause) (tail pref : Bits)
    (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N)
      (uniformEmitScratchResetProg.eval σ)
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg) := by
  let K := uniformEmitTightEnvelope N
  let B := uniformEmitSyntaxEnvelope N
  have hK25 : 25 ≤ K := by
    simp [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap]
  have hK1 : 1 ≤ K := by omega
  have hN : N ≤ K := by
    simp [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
      uniformSlackNat, relocateControlGap]
    omega
  have hKB : K ≤ B := by
    exact uniformEmitTightEnvelope_le_syntax_envelope N
  have haddr : addr ≤ K := by
    rw [← hrel.cursor]
    exact hσ uctCursorReg
  have hσB : StoreValuesLe B σ := fun i => (hσ i).trans hKB
  have hσr : StoreValuesLe B (uniformEmitScratchResetProg.eval σ) := by
    exact storeValuesLe_uniformEmitScratchResetProg B σ (by omega) hσB
      (hK25.trans hKB)
  have hbr : (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
    rcases uniformEmitScratchResetProg_persistent_values σ with
      ⟨_, _, _, _, _, hsaved⟩
    exact hsaved.trans hb
  have hcursor : (uniformEmitScratchResetProg.eval σ) uctCursorReg = addr := by
    rcases uniformEmitScratchResetProg_persistent_values σ with
      ⟨_, hcursor, _, _, _, _⟩
    exact hcursor.trans hrel.cursor
  have hlength : (uniformEmitScratchResetProg.eval σ) uctLengthReg = 0 := by
    exact (uniformEmitScratchResetProg_values σ).2.2.2.2.2.1
  have hidx : uctCursorReg ≤ B ∧ uctLengthReg ≤ B ∧ uctDoneReg ≤ B ∧
      uctSavedBoundReg ≤ B := by
    have hc := hrel.safety.cursor_below
    have hl := hrel.safety.length_below
    have hd := hrel.safety.done_below
    have hs : uniformStartNat ≤ K := by
      simp [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat,
        uniformSlackNat, relocateControlGap]
      omega
    have hbnd : uctSavedBoundReg < uniformStartNat := by
      norm_num [uctSavedBoundReg, uniformStartNat, relocateControlGap]
    omega
  apply programBoundedIn_decodeNatProgramAt_of_bounds uctCursorReg uctLengthReg
    uctDoneReg uctSavedBoundReg B (uniformEmitScratchResetProg.eval σ)
  · decide
  · decide
  · decide
  · exact hidx
  · calc
      (uniformEmitScratchResetProg.eval σ) uctCursorReg +
          (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = addr + N := by
        rw [hcursor, hbr]
      _ ≤ K + K := by omega
      _ ≤ B := by
        dsimp [B, K]
        simp [uniformEmitSyntaxEnvelope, uniformEmitLongValueEnvelope,
          uniformEmitTightEnvelope, writerAppendRawThreeBound,
          writerAppendRawStepBound]
        omega

  · calc
      (uniformEmitScratchResetProg.eval σ) uctLengthReg +
          (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = N := by
        rw [hlength, hbr]
        simp
      _ ≤ K := by omega
      _ ≤ B := by
        dsimp [B, K]
        simp [uniformEmitSyntaxEnvelope, uniformEmitLongValueEnvelope,
          uniformEmitTightEnvelope, writerAppendRawThreeBound,
          writerAppendRawStepBound]
        omega

/-- Capacity of the writer region after appending the link triple of the first literal. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_room
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    start + pref.length + carry.var + l1.var + base + 8 < M + curJ := by
  have hc := hrel.capacity
  rw [splitTailPayload_cons3, hrel.carry_one, List.length_append,
    encodedThreeLiteralBits_length] at hc
  omega

/-- After decoding the first literal, the writer state and the link registers are intact and
    the parser registers hold the decoded literal. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_decode_values
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τp : Store)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ) :
    WriterState τp M curJ start pref ∧ τp carryPolReg = 1 ∧ τp carryValReg = carry.var ∧
      τp posPolReg = 0 ∧ τp freshReg = base ∧ τp polReg = literalPolarity l1 ∧
      τp varReg = l1.var ∧ τp doneReg = 1 := by
  have hbits : BitsFrom σ addr
      (encodeLiteral l1 ++ splitTailInputBits (l2 :: l3 :: rest) tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hrel.input
  have hbelow := hrel.safety.main.below
  obtain ⟨_, hpol, hvar, hdone, hdecFrame⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l1
      (splitTailInputBits (l2 :: l3 :: rest) tail) σ
      hrel.safety.main.distinct.1 hrel.safety.main.distinct.2.1
      hrel.safety.main.distinct.2.2.1 hrel.safety.main.distinct.2.2.2.1
      hrel.safety.main.distinct.2.2.2.2.1 hrel.safety.main.distinct.2.2.2.2.2
      (lt_of_lt_of_le hbelow.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.1 hrel.start_at_input)
      (lt_of_lt_of_le hbelow.2.2.2 hrel.start_at_input)
      hbound hrel.cursor hbits
  subst hτp
  have hnz := hrel.safety.main.nonzero
  have hw := hrel.safety.writer_parser
  refine ⟨writerState_transport_of_frame4 M curJ start pref σ _ cursorReg polReg varReg doneReg
    hrel.writer hdecFrame hnz.1 hnz.2.1 hnz.2.2.1 hnz.2.2.2 hbelow.1 hbelow.2.1
    hbelow.2.2.1 hbelow.2.2.2, ?_, ?_, ?_, ?_, ?_, hvar, hdone⟩
  · have h := hw carryPolReg (Or.inl rfl)
    exact (hdecFrame _ h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans hrel.carry_pol
  · have h := hw carryValReg (Or.inr (Or.inl rfl))
    exact (hdecFrame _ h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans hrel.carry_val
  · have h := hw posPolReg (Or.inr (Or.inr (Or.inl rfl)))
    exact (hdecFrame _ h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans hrel.pos
  · have h := hw freshReg (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    exact (hdecFrame _ h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans hrel.fresh
  · cases l1 <;> simpa [literalPolarity] using hpol

/-- The link-append block does not write the parser registers that hold the decoded literal. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_parser_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τp : Store)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτp : τp = (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ) :
    ∀ r, r = polReg ∨ r = varReg ∨ r = doneReg →
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg).eval τp r = τp r := by
  obtain ⟨hstate, hcp, hcv, hpos, hfresh, hpol, hvar, -⟩ :=
    storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_decode_values M curJ tmpJ start
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τp hbound
      hrel hτp
  have hroom := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_room M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg base carry l1 l2 l3 rest pref tail addr σ hrel
  have hbelow := hrel.safety.main.below
  have hw := hrel.safety.writer_parser
  have hwv := hw carryValReg (Or.inr (Or.inl rfl))
  have hwf := hw freshReg (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hpol01 : τp polReg = 0 ∨ τp polReg = 1 := by
    rw [hpol]
    cases l1 <;> simp [literalPolarity]
  intro r hr
  have hrLow : r < start := by
    rcases hr with h | h | h <;> subst h
    exacts [hbelow.2.1, hbelow.2.2.1, hbelow.2.2.2]
  have hrNot : r ≠ carryValReg ∧ r ≠ freshReg := by
    rcases hr with h | h | h <;> subst h
    exacts [⟨hwv.2.1.symm, hwf.2.1.symm⟩, ⟨hwv.2.2.1.symm, hwf.2.2.1.symm⟩,
      ⟨hwv.2.2.2.1.symm, hwf.2.2.2.1.symm⟩]
  have hthree := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    carryPolReg carryValReg polReg varReg posPolReg freshReg
    1 carry.var (τp polReg) l1.var 0 base τp hrel.cur_j_pos hrel.tmp_j_pos
    hcp hcv rfl hvar hpos hfresh
    (Or.inr rfl) hpol01 (Or.inl rfl)
    hrel.safety.writer_below.2.1
    ⟨hbelow.2.1, hbelow.2.2.1⟩
    ⟨hrel.safety.writer_below.2.2.1, hrel.safety.writer_below.2.2.2.1⟩ hstate
    (by omega) hrLow
  unfold writerAppendSplitTailLinkDynamicProg
  rw [eval_seq, eval_seq, eval_assign, eval_assign, Expr.eval,
    writeReg_diff _ freshReg _ r hrNot.2, writeReg_diff _ carryValReg _ r hrNot.1]
  exact hthree

/-- The intermediate program leaves the decoded literal in the parser registers. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_parser_values
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ polReg = literalPolarity l1 ∧
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ varReg = l1.var ∧
    (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      carryPolReg carryValReg posPolReg freshReg bound).eval σ doneReg = 1 := by
  obtain ⟨τp, hτp⟩ : ∃ τp, τp =
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, hpol, hvar, hdone⟩ :=
    storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_decode_values M curJ tmpJ start
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τp hbound
      hrel hτp
  have hw := hrel.safety.writer_parser remainingReg (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  exact splitTailEmitIntermediateProg_parser_values curJ tmpJ cursorReg polReg varReg
    doneReg remainingReg carryPolReg carryValReg posPolReg freshReg bound σ τp
    (literalPolarity l1) l1.var hτp hpol hvar hdone
    (storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_parser_frame M curJ tmpJ start
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τp hbound
      hrel hτp)
    hw.2.1 hw.2.2.1 hw.2.2.2.1

/-- The temporary writer cell after the intermediate program is at most `K`. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_tmp_le
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hbase1 : base + 1 ≤ K) (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ) :
    τ (M + tmpJ) ≤ K := by
  obtain ⟨τp, hτp⟩ : ∃ τp, τp =
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ := ⟨_, rfl⟩
  obtain ⟨hstate, hcp, hcv, hpos, hfresh, hpol, hvar, -⟩ :=
    storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_decode_values M curJ tmpJ start
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τp hbound
      hrel hτp
  have hroom := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_room M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg base carry l1 l2 l3 rest pref tail addr σ hrel
  have hbelow := hrel.safety.main.below
  have hwb := hrel.safety.writer_below
  have htmp' := writerAppendThreeRegsProg_tmp_value M curJ tmpJ start pref
    carryPolReg carryValReg polReg varReg posPolReg freshReg
    1 carry.var (literalPolarity l1) l1.var base τp hrel.cur_j_pos hrel.tmp_j_pos
    hcp hcv hpol hvar hfresh
    (by simp) (by cases l1 <;> simp [literalPolarity])
    hwb.2.1 ⟨hbelow.2.1, hbelow.2.2.1⟩ ⟨hwb.2.2.1, hwb.2.2.2.1⟩
    hstate (by omega)
  have hstart : start < M + curJ := by omega
  have hcurJtmpJ : M + curJ < M + tmpJ := Nat.add_lt_add_left hrel.tmp_j_pos M
  have hfreshne : freshReg ≠ M + tmpJ :=
    Nat.ne_of_lt (lt_trans hwb.2.2.2.1 (lt_trans hstart hcurJtmpJ))
  have hcarryne : carryValReg ≠ M + tmpJ :=
    Nat.ne_of_lt (lt_trans hwb.2.1 (lt_trans hstart hcurJtmpJ))
  have hremne : remainingReg ≠ M + tmpJ :=
    Nat.ne_of_lt (lt_trans hwb.2.2.2.2 (lt_trans hstart hcurJtmpJ))
  have htmpLink :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg).eval τp (M + tmpJ) = base := by
    unfold writerAppendSplitTailLinkDynamicProg
    rw [eval_seq, eval_seq, eval_assign, eval_assign, Expr.eval,
      writeReg_diff _ freshReg _ (M + tmpJ) hfreshne.symm,
      writeReg_diff _ carryValReg _ (M + tmpJ) hcarryne.symm]
    exact htmp'
  rw [hτ]
  unfold splitTailEmitIntermediateProg
  rw [eval_seq, eval_seq, ← hτp, eval_assign, Expr.eval,
    writeReg_diff _ remainingReg _ (M + tmpJ) hremne.symm, htmpLink]
  omega

/-- Every register written by the intermediate program stays below the value bound. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_changed_le
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hbase1 : base + 1 ≤ K) (hpostCursor : addr + l1.var + 2 ≤ K)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hσK : StoreValuesLe K σ)
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hrel' : SplitTailEmitRel τ M curJ tmpJ start (base + 1) (NPComplete.SAT.Literal.neg base)
      (l2 :: l3 :: rest)
      (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l1) l1.var 0 base)
      tail (addr + l1.var + 2) cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∀ r, r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨
      r = remainingReg ∨ r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
      r = freshReg → τ r ≤ K := by
  have hparser := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_parser_values M curJ
    tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ
    hbound hrel
  have hrem0 : (l1 :: l2 :: l3 :: rest).length ≤ K := by
    rw [← hrel.remaining]
    exact hσK remainingReg
  have hremK : (l2 :: l3 :: rest).length ≤ K := by
    simp only [List.length_cons] at hrem0 ⊢
    omega
  have hK1 : 1 ≤ K := by omega
  intro r hr
  rcases hr with h | h | h | h | h | h | h | h | h
  · rw [h, hrel'.cursor]
    exact hpostCursor
  · rw [h, hτ, hparser.1]
    cases l1 <;> simp [literalPolarity, hK1]
  · rw [h, hτ, hparser.2.1]
    omega
  · rw [h, hτ, hparser.2.2]
    omega
  · rw [h, hrel'.remaining]
    exact hremK
  · rw [h, hrel'.carry_pol]
    omega
  · rw [h, hrel'.carry_val]
    change base ≤ K
    omega
  · rw [h, hrel'.pos]
    omega
  · rw [h, hrel'.fresh]
    exact hbase1

/-- Registers below the frame start that the intermediate program does not write keep their
    value. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_low_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ) :
    ∀ r, r < start →
      (r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ carryValReg ∧ r ≠ posPolReg ∧ r ≠ freshReg ∧ r ≠ remainingReg) →
      τ r = σ r := by
  intro r hr hne
  rw [hτ]
  exact splitTailEmitIntermediateProg_low_frame_of_rel M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ hbound hrel hr hne

/-- Registers above the writer cursor are untouched by the intermediate program. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_after_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hrel' : SplitTailEmitRel τ M curJ tmpJ start (base + 1) (NPComplete.SAT.Literal.neg base)
      (l2 :: l3 :: rest)
      (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l1) l1.var 0 base)
      tail (addr + l1.var + 2) cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r := by
  intro r hr hrc hrt
  have hlen := encodedThreeLiteralBits_length 1 carry.var (literalPolarity l1) l1.var 0 base
  have hthreshold : start + pref.length + carry.var + l1.var + base + 6 ≤ r := by
    rw [hrel'.writer.cursor] at hr
    simp only [List.length_append] at hr
    omega
  rw [hτ]
  exact splitTailEmitIntermediateProg_after_frame_of_rel M curJ tmpJ start cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ hbound hrel hthreshold
    hrc hrt

/-- Value bound for the store after the intermediate program, given its post-relation. -/
lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_post
    (K M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg
      bound base : ℕ)
    (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ τ : Store)
    (hbase1 : base + 1 ≤ K) (hpostCursor : addr + l1.var + 2 ≤ K)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hσK : StoreValuesLe K σ) (hstatic : M + curJ ≤ K)
    (hτ : τ = (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
    (hrel' : SplitTailEmitRel τ M curJ tmpJ start (base + 1) (NPComplete.SAT.Literal.neg base)
      (l2 :: l3 :: rest)
      (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l1) l1.var 0 base)
      tail (addr + l1.var + 2) cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    StoreValuesLe K τ := by
  have hchanged := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_changed_le K M curJ
    tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τ
    hbase1 hpostCursor hbound hrel hσK hτ hrel'
  have hlow := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_low_frame M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τ hbound
    hrel hτ
  have hcursorK : τ (M + curJ) ≤ K :=
    (Nat.le_of_lt (by rw [hrel'.writer.cursor]; exact hrel'.writer.safe)).trans hstatic
  have hframeLow : ∀ r, r < start →
      ¬ LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg
        negPolReg r → τ r = σ r := by
    intro r hr hw
    refine hlow r hr ?_
    simp only [LongClauseLowWriteSet, not_or] at hw
    aesop
  have hsmall : ∀ r, r < start →
      LongClauseLowWriteSet cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg lengthReg outerReg
        negPolReg r → τ r ≤ K := by
    intro r hr _
    by_cases hc : r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨ r = remainingReg ∨
        r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg
    · exact hchanged r hc
    · simp only [not_or] at hc
      rw [hlow r hr ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.2.2.1,
        hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2, hc.2.2.2.2.1⟩]
      exact hσK r
  exact storeValuesLe_of_long_clause_frames K M curJ tmpJ start σ τ
    (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l1) l1.var 0 base)
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg lengthReg outerReg negPolReg (by omega) hσK
    hrel'.writer hcursorK
    (storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_tmp_le K M curJ tmpJ start cursorReg
      polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τ hbase1
      hbound hrel hτ)
    hframeLow hsmall
    (storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_after_frame M curJ tmpJ start
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
      carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ τ hbound
      hrel hτ hrel')

lemma storeValuesLe_splitTailEmitIntermediateProgAt_of_rel
    (K B M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg lengthReg outerReg
      negPolReg bound : ℕ)
    (base : ℕ) (carry l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbase1 : base + 1 ≤ K) (hpostCursor : addr + l1.var + 2 ≤ K)
    (hbound : l1.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry
      (l1 :: l2 :: l3 :: rest) pref tail addr cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hraw : SplitTailEmitStepRawBounds K B M curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg σ) :
    StoreValuesLe K
      ((splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ) := by
  obtain ⟨τ, hτ, hrel'⟩ := splitTailEmitRel_intermediate_to_rel M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound base carry l1 l2 l3 rest pref tail addr σ
    hbound hrel
  have hpost := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel_post K M curJ tmpJ start
    cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg
    carryValReg posPolReg freshReg lengthReg outerReg negPolReg bound base carry l1 l2 l3 rest pref tail addr σ τ hbase1
    hpostCursor hbound hrel hraw.store hraw.static.1 hτ hrel'
  rw [splitTailEmitIntermediateProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    carryPolReg carryValReg posPolReg freshReg boundReg bound σ hb
    hraw.dist.2.2.2.2.1 hraw.dist.2.2.2.2.2.1
    hraw.dist.2.2.2.2.2.2.1 hraw.dist.2.2.2.2.2.2.2, ← hτ]
  exact hpost

end NPComplete.CookLevin

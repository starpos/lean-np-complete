module

public import NPComplete.CookLevin.UniformPackaging.SplitTailTmp

/-!
# Three-literal dispatch temporaries

The three-literal branch stages encoded operands in shared scratch registers. This module proves
the intermediate values and available writer room, giving later raw-bound proofs a single branch
invariant to reuse. It then bounds the writer's temporary cell after the dispatch by `K` for the
empty and three-literal shapes, and `uniform_emit_dispatch_short_tmp_value_of_prep` combines these
with the one- and two-literal results for clauses of length at most three, given that the variable
count and the fresh base are at most `K`.
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

lemma writerAppendClauseThreeProg_tmp_value
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg : ℕ)
    (pol1 val1 pol2 val2 pol3 val3 base : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hp1 : σ p1 = pol1) (hv1 : σ v1 = val1)
    (hp2 : σ p2 = pol2) (hv2 : σ v2 = val2)
    (hpos : σ posPolReg = 0) (hneg : σ negPolReg = 1) (hfresh : σ freshReg = base)
    (hpol1 : pol1 = 0 ∨ pol1 = 1) (hpol2 : pol2 = 0 ∨ pol2 = 1)
    (hpol3 : pol3 = 0 ∨ pol3 = 1)
    (hlow1 : p1 < start ∧ v1 < start) (hlow2 : p2 < start ∧ v2 < start)
    (hlow3 : p3 < start ∧ v3 < start)
    (hlowPos : posPolReg < start) (hlowNeg : negPolReg < start)
    (hlowFresh : freshReg < start) (hs : WriterState σ M curJ start pref)
    (hroom1 : start + pref.length + val1 + val2 + base + 6 < M + curJ)
    (hroom2 : start + (pref ++ encodedLiteralBits pol1 val1 ++
      encodedLiteralBits pol2 val2 ++ encodedLiteralBits 0 base).length +
      base + val3 + val3 + 6 < M + curJ)
    (hp3Post : (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg).eval σ
      p3 = pol3)
    (hv3Post : (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg).eval σ
      v3 = val3) :
    (writerAppendClauseThreeProg curJ tmpJ p1 v1 p2 v2 p3 v3 posPolReg negPolReg freshReg).eval σ
      (M + tmpJ) = val3 := by
  have hfirst := writerAppendThreeRegsProg_eval M curJ tmpJ start pref
    p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ hcurJ htmpJ
    hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp) hlow1.2 hlow2
    ⟨hlowPos, hlowFresh⟩ hs hroom1
  let σ1 := (writerAppendThreeRegsProg curJ tmpJ p1 v1 p2 v2 posPolReg freshReg).eval σ
  have hneg1 : σ1 negPolReg = 1 := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ hcurJ htmpJ
      hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp) hlow1.2 hlow2
      ⟨hlowPos, hlowFresh⟩ hs hroom1 (r := negPolReg) hlowNeg
    exact hf.trans hneg
  have hfresh1 : σ1 freshReg = base := by
    have hf := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      p1 v1 p2 v2 posPolReg freshReg pol1 val1 pol2 val2 0 base σ hcurJ htmpJ
      hp1 hv1 hp2 hv2 hpos hfresh hpol1 hpol2 (by simp) hlow1.2 hlow2
      ⟨hlowPos, hlowFresh⟩ hs hroom1 (r := freshReg) hlowFresh
    exact hf.trans hfresh
  have hsecond := writerAppendThreeRegsProg_tmp_value M curJ tmpJ
    start (pref ++ encodedLiteralBits pol1 val1 ++ encodedLiteralBits pol2 val2 ++
      encodedLiteralBits 0 base)
    negPolReg freshReg p3 v3 p3 v3 1 base pol3 val3 val3 σ1 hcurJ htmpJ
    hneg1 hfresh1 hp3Post hv3Post hv3Post (by simp) hpol3
    hlowFresh hlow3 hlow3 hfirst hroom2
  simpa [writerAppendClauseThreeProg, σ1, List.append_assoc] using hsecond

/-- Skipping the encodings of two literals leaves the encoding of the third. -/
lemma uniform_emit_dispatch_three_tmp_value_tail_bits
    (σ : Store) (a : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal) (rest : Bits)
    (hbits : BitsFrom σ a
      (encodeLiteral l1 ++ (encodeLiteral l2 ++ (encodeLiteral l3 ++ rest)))) :
    BitsFrom σ (a + l1.var + 2 + l2.var + 2) (encodeLiteral l3 ++ rest) := by
  obtain ⟨_, ht1⟩ := bitsFrom_append σ a (encodeLiteral l1)
    (encodeLiteral l2 ++ (encodeLiteral l3 ++ rest)) hbits
  obtain ⟨_, ht2⟩ := bitsFrom_append σ (a + (encodeLiteral l1).length) (encodeLiteral l2)
    (encodeLiteral l3 ++ rest) ht1
  have hl1 : (encodeLiteral l1).length = l1.var + 2 := by
    cases l1 <;> simp [encodeLiteral, encodeNat_length, var_pos, var_neg]
  have hl2 : (encodeLiteral l2).length = l2.var + 2 := by
    cases l2 <;> simp [encodeLiteral, encodeNat_length, var_pos, var_neg]
  simpa [hl1, hl2, Nat.add_assoc] using ht2

/-- Decoding the three literals of a short clause in the uniform register layout:
the three decode programs, their frames, and the decoded polarity and variable. -/
lemma uniform_emit_dispatch_three_tmp_value_decode
    (N base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2, l3] rest pref σr σdec)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hbound3 : l3.var + 1 ≤ N) :
    ∃ τ υ ξ, τ = (decodeLiteralValueProgram uctCursorReg uctPolReg uctVarReg uctDoneReg N).eval σdec ∧
      υ = (decodeLiteralValueProgram uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg N).eval τ ∧
      ξ = (decodeLiteralValueProgram uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg N).eval υ ∧
      (∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg → τ r = σdec r) ∧
      (∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg → r ≠ uctDoneReg → υ r = τ r) ∧
      (∀ r, r ≠ uctCursorReg → r ≠ uctPol3Reg → r ≠ uctVar3Reg → r ≠ uctDoneReg → ξ r = υ r) ∧
      τ uctPolReg = literalPolarity l1 ∧ τ uctVarReg = l1.var ∧
      υ uctPol2Reg = literalPolarity l2 ∧ υ uctVar2Reg = l2.var ∧
      ξ uctPol3Reg = literalPolarity l3 ∧ ξ uctVar3Reg = l3.var := by
  have haddr : addr + [l1, l2, l3].length + 1 = addr + 4 := by simp
  have hbits' : BitsFrom σdec (addr + 4)
      (encodeLiteral l1 ++ (encodeLiteral l2 ++ (encodeLiteral l3 ++ rest))) := by
    simpa [haddr, splitTailInputBits, List.append_assoc] using hprep.input
  have hstart := hprep.start_at_input
  obtain ⟨τ, υ, hτ, hυ, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2,
      hframe1, hframe2⟩ :=
    decode_two_literal_value_correct uctCursorReg uctPolReg uctVarReg uctPol2Reg uctVar2Reg
      uctDoneReg N (addr + 4) l1 l2 (encodeLiteral l3 ++ rest) σdec
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨by have := hprep.safety.cursor_below; omega,
       by have := hprep.safety.pol_below; omega,
       by have := hprep.safety.var_below; omega,
       by simp [uctPol2Reg, uniformStartNat, relocateControlGap] at *; omega,
       by simp [uctVar2Reg, uniformStartNat, relocateControlGap] at *; omega,
       by have := hprep.safety.done_below; omega⟩
      hbound1 hbound2 hprep.cursor (by simpa [List.append_assoc] using hbits')
  have htailσ : BitsFrom σdec (addr + 4 + l1.var + 2 + l2.var + 2)
      (encodeLiteral l3 ++ rest) :=
    uniform_emit_dispatch_three_tmp_value_tail_bits σdec (addr + 4) l1 l2 l3 rest hbits'
  have htailυ : BitsFrom υ (addr + 4 + l1.var + 2 + l2.var + 2)
      (encodeLiteral l3 ++ rest) := by
    apply bitsFrom_of_eq_on (hb := htailσ)
    intro i _
    rw [hframe2 _ (by simp [uctCursorReg, uniformStartNat, relocateControlGap] at *; omega)
      (by simp [uctPol2Reg, uniformStartNat, relocateControlGap] at *; omega)
      (by simp [uctVar2Reg, uniformStartNat, relocateControlGap] at *; omega)
      (by simp [uctDoneReg, uniformStartNat, relocateControlGap] at *; omega)]
    exact hframe1 _ (by have := hprep.safety.cursor_below; omega)
      (by have := hprep.safety.pol_below; omega) (by have := hprep.safety.var_below; omega)
      (by have := hprep.safety.done_below; omega)
  obtain ⟨hcur3, hpol3v, hvar3, _, hframe3⟩ :=
    decodeLiteralValueProgram_correct uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
      N (addr + 4 + l1.var + 2 + l2.var + 2) l3 rest υ
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [uctCursorReg, uniformStartNat, relocateControlGap] at *)
      (by simp [uctPol3Reg, uniformStartNat, relocateControlGap] at *; omega)
      (by simp [uctVar3Reg, uniformStartNat, relocateControlGap] at *; omega)
      (by simp [uctDoneReg, uniformStartNat, relocateControlGap] at *; omega)
      hbound3 (by simpa [hυ] using hcur2) htailυ
  refine ⟨τ, υ, _, hτ, hυ, rfl, hframe1, hframe2, hframe3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases l1 <;> simpa [hτ, literalPolarity] using hpol1
  · simpa [hτ] using hvar1
  · cases l2 <;> simpa [hυ, literalPolarity] using hpol2
  · cases l2 <;> simpa [hυ] using hvar2
  · cases l3 <;> simpa [literalPolarity] using hpol3v
  · simpa using hvar3

/-- Under the three decoder frame hypotheses, the writer invariant is preserved
through the decoded states. -/
lemma uniform_emit_dispatch_three_tmp_value_writer
    (N base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec τ υ ξ : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2, l3] rest pref σr σdec)
    (hframe1 : ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      τ r = σdec r)
    (hframe2 : ∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg → r ≠ uctDoneReg →
      υ r = τ r)
    (hframe3 : ∀ r, r ≠ uctCursorReg → r ≠ uctPol3Reg → r ≠ uctVar3Reg → r ≠ uctDoneReg →
      ξ r = υ r) :
    WriterState ξ (uniformMNat N) uctCurJ uniformStartNat pref := by
  have hτstate : WriterState τ (uniformMNat N) uctCurJ uniformStartNat pref :=
    writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref σdec τ
      uctCursorReg uctPolReg uctVarReg uctDoneReg hprep.writer hframe1
      hprep.safety.cursor_nonzero hprep.safety.pol_nonzero
      hprep.safety.var_nonzero hprep.safety.done_nonzero
      hprep.safety.cursor_below hprep.safety.pol_below hprep.safety.var_below hprep.safety.done_below
  have hυstate : WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref := by
    apply writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref τ υ
      uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg hτstate hframe2
      (by decide) (by decide) (by decide) (by decide)
      (by have := hprep.start_at_input; simp [uctCursorReg, uniformStartNat, relocateControlGap] at *)
      (by have := hprep.start_at_input; simp [uctPol2Reg, uniformStartNat, relocateControlGap] at *)
      (by have := hprep.start_at_input; simp [uctVar2Reg, uniformStartNat, relocateControlGap] at *)
      (by have := hprep.start_at_input; simp [uctDoneReg, uniformStartNat, relocateControlGap] at *)
  apply writerState_transport_of_frame4 (uniformMNat N) uctCurJ uniformStartNat pref υ ξ
    uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg hυstate hframe3
  · exact hprep.safety.cursor_nonzero
  · decide
  · decide
  · exact hprep.safety.done_nonzero
  · exact hprep.safety.cursor_below
  · decide
  · decide
  · exact hprep.safety.done_below

/-- Under the three decoder frame hypotheses, registers consumed by the writer
keep their pre-decode values or the decoded literal parts. -/
lemma uniform_emit_dispatch_three_tmp_value_registers
    (N base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec τ υ ξ : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2, l3] rest pref σr σdec)
    (hframe1 : ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      τ r = σdec r)
    (hframe2 : ∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg → r ≠ uctDoneReg →
      υ r = τ r)
    (hframe3 : ∀ r, r ≠ uctCursorReg → r ≠ uctPol3Reg → r ≠ uctVar3Reg → r ≠ uctDoneReg →
      ξ r = υ r)
    (hp1 : τ uctPolReg = literalPolarity l1) (hv1 : τ uctVarReg = l1.var)
    (hp2 : υ uctPol2Reg = literalPolarity l2) (hv2 : υ uctVar2Reg = l2.var) :
    ξ uctPolReg = literalPolarity l1 ∧ ξ uctVarReg = l1.var ∧
      ξ uctPol2Reg = literalPolarity l2 ∧ ξ uctVar2Reg = l2.var ∧
      ξ uctPosPolReg = 0 ∧ ξ uctNegPolReg = 1 ∧ ξ uctFreshReg = base := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hframe3 uctPolReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe2 uctPolReg (by decide) (by decide) (by decide) (by decide)).trans hp1)
  · exact (hframe3 uctVarReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe2 uctVarReg (by decide) (by decide) (by decide) (by decide)).trans hv1)
  · exact (hframe3 uctPol2Reg (by decide) (by decide) (by decide) (by decide)).trans hp2
  · exact (hframe3 uctVar2Reg (by decide) (by decide) (by decide) (by decide)).trans hv2
  · exact (hframe3 uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe2 uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hframe1 uctPosPolReg (by decide) (by decide) (by decide) (by decide)).trans
          hprep.pos_value))
  · exact (hframe3 uctNegPolReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe2 uctNegPolReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hframe1 uctNegPolReg (by decide) (by decide) (by decide) (by decide)).trans
          hprep.neg_value))
  · exact (hframe3 uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans
      ((hframe2 uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hframe1 uctFreshReg (by decide) (by decide) (by decide) (by decide)).trans
          hprep.fresh_value))

/-- The payload-capacity facts needed by the two writer calls, extracted from the
prep state's room bound. -/
lemma uniform_emit_dispatch_three_tmp_value_rooms
    (N base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2, l3] rest pref σr σdec) :
    uniformStartNat + pref.length + l1.var + l2.var + base + 6 < uniformMNat N + uctCurJ ∧
    uniformStartNat +
      (pref ++ encodedLiteralBits (literalPolarity l1) l1.var ++
        encodedLiteralBits (literalPolarity l2) l2.var ++
        encodedLiteralBits 0 base).length + base + l3.var + l3.var + 6 <
      uniformMNat N + uctCurJ := by
  have hr := hprep.room
  constructor
  · cases l1 <;> cases l2 <;> cases l3 <;>
      simp [clauseToThree, splitTail, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var, List.length_append] at hr ⊢ <;> omega
  · cases l1 <;> cases l2 <;> cases l3 <;>
      simp [clauseToThree, splitTail, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
        encodedLiteralBits, NPComplete.BitEncoding.encodeNat_length,
        NPComplete.SAT.Literal.var, List.length_append] at hr ⊢ <;> omega

/-- After the three decoders, the clause writer leaves the third variable in the
temporary output cell. -/
lemma uniform_emit_dispatch_three_tmp_value_append
    (N base : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal) (pref : Bits) (ξ : Store)
    (hsafety : ClauseEmitSafety uniformStartNat uctCursorReg uctLengthReg uctPolReg uctVarReg
      uctDoneReg uctOuterReg uctFreshReg uctPosPolReg uctNegPolReg)
    (hξstate : WriterState ξ (uniformMNat N) uctCurJ uniformStartNat pref)
    (hp1 : ξ uctPolReg = literalPolarity l1) (hv1 : ξ uctVarReg = l1.var)
    (hp2 : ξ uctPol2Reg = literalPolarity l2) (hv2 : ξ uctVar2Reg = l2.var)
    (hp3 : ξ uctPol3Reg = literalPolarity l3) (hv3 : ξ uctVar3Reg = l3.var)
    (hpos : ξ uctPosPolReg = 0) (hneg : ξ uctNegPolReg = 1) (hfresh : ξ uctFreshReg = base)
    (hroom1 : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hroom2 : uniformStartNat +
      (pref ++ encodedLiteralBits (literalPolarity l1) l1.var ++
        encodedLiteralBits (literalPolarity l2) l2.var ++
        encodedLiteralBits 0 base).length + base + l3.var + l3.var + 6 <
      uniformMNat N + uctCurJ) :
    (writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg).eval ξ
      (uniformMNat N + uctTmpJ) = l3.var := by
  have hp01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hp02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hp03 : literalPolarity l3 = 0 ∨ literalPolarity l3 = 1 := by
    cases l3 <;> simp [literalPolarity]
  have hlow2 : uctPol2Reg < uniformStartNat ∧ uctVar2Reg < uniformStartNat := by
    simp [uctPol2Reg, uctVar2Reg, uniformStartNat, relocateControlGap]
  have hlow3 : uctPol3Reg < uniformStartNat ∧ uctVar3Reg < uniformStartNat := by
    simp [uctPol3Reg, uctVar3Reg, uniformStartNat, relocateControlGap]
  have hpost := fun r (hr : r < uniformStartNat) =>
    writerAppendThreeRegsProg_frame (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
      uctPolReg uctVarReg uctPol2Reg uctVar2Reg uctPosPolReg uctFreshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base ξ
      uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hp1 hv1 hp2 hv2 hpos hfresh
      hp01 hp02 (by simp) hsafety.var_below hlow2
      ⟨hsafety.pos_below, hsafety.fresh_below⟩ hξstate hroom1 hr
  exact writerAppendClauseThreeProg_tmp_value (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
    uctPolReg uctVarReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
    uctFreshReg (literalPolarity l1) l1.var (literalPolarity l2) l2.var (literalPolarity l3) l3.var
    base ξ uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hp1 hv1 hp2 hv2 hpos hneg hfresh
    hp01 hp02 hp03 ⟨hsafety.pol_below, hsafety.var_below⟩ hlow2 hlow3 hsafety.pos_below
    hsafety.neg_below hsafety.fresh_below hξstate hroom1 hroom2
    (by rw [hpost uctPol3Reg hlow3.1]; exact hp3) (by rw [hpost uctVar3Reg hlow3.2]; exact hv3)

/-- The uniform dispatcher on a three-literal clause is the three decoders, the
clause writer, the fresh-variable bump and the counter decrement. -/
lemma uniform_emit_dispatch_three_tmp_value_dispatch_eval
    (N : ℕ) (σdec τ υ ξ : Store)
    (hsaved : σdec uctSavedBoundReg = N) (hlen : σdec uctLengthReg = 3)
    (hτ : τ = (decodeLiteralValueProgram uctCursorReg uctPolReg uctVarReg uctDoneReg N).eval σdec)
    (hυ : υ = (decodeLiteralValueProgram uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg N).eval τ)
    (hξ : ξ = (decodeLiteralValueProgram uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg N).eval υ)
    (hframe1 : ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      τ r = σdec r)
    (hframe2 : ∀ r, r ≠ uctCursorReg → r ≠ uctPol2Reg → r ≠ uctVar2Reg → r ≠ uctDoneReg →
      υ r = τ r) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec =
    (emitClauseCommitProg uctOuterReg).eval
      ((emitClauseEmptyFreshProg uctFreshReg).eval
        ((writerAppendClauseThreeProg uctCurJ uctTmpJ uctPolReg uctVarReg uctPol2Reg
          uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctFreshReg).eval ξ)) := by
  have hbτ : τ uctSavedBoundReg = N :=
    (hframe1 uctSavedBoundReg (by decide) (by decide) (by decide) (by decide)).trans hsaved
  have hbυ : υ uctSavedBoundReg = N :=
    (hframe2 uctSavedBoundReg (by decide) (by decide) (by decide) (by decide)).trans hbτ
  have hA1 := decodeLiteralValueProgramAt_eq uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctSavedBoundReg N σdec hsaved (by decide) (by decide) (by decide) (by decide)
  have hA2 := decodeLiteralValueProgramAt_eq uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
    uctSavedBoundReg N τ hbτ (by decide) (by decide) (by decide) (by decide)
  have hA3 := decodeLiteralValueProgramAt_eq uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
    uctSavedBoundReg N υ hbυ (by decide) (by decide) (by decide) (by decide)
  subst hξ hυ hτ
  simp only [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, eval_ifNZ]
  rw [ite_eq_right (by simp [Expr.eval, hlen]), ite_eq_right (by simp [Expr.eval, hlen]),
    ite_eq_right (by simp [Expr.eval, hlen]), ite_eq_left (by simp [Expr.eval, hlen])]
  simp only [eval_seq]
  rw [hA1, hA2, hA3]

/-- Bumping the fresh counter and decrementing the outer counter do not touch the
temporary output cell. -/
lemma uniform_emit_dispatch_three_tmp_value_commit_bound
    (N K : ℕ) (σ : Store) (h : σ (uniformMNat N + uctTmpJ) ≤ K) :
    (emitClauseCommitProg uctOuterReg).eval
      ((emitClauseEmptyFreshProg uctFreshReg).eval σ) (uniformMNat N + uctTmpJ) ≤ K := by
  have hout : uctOuterReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctOuterReg, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hne : uctFreshReg ≠ uniformMNat N + uctTmpJ := by
    have hm := uniformMNat_ge_25 N
    simp [uctFreshReg, uctTmpJ]
    omega
  simpa [emitClauseCommitProg, emitClauseEmptyFreshProg, eval_assign, Expr.eval,
    writeReg_diff _ uctOuterReg _ _ hout.symm, writeReg_diff _ uctFreshReg _ _ hne.symm] using h

lemma uniform_emit_dispatch_three_tmp_value
    (N K base outer addr : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [l1, l2, l3] rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hbound3 : l3.var + 1 ≤ N)
    (hN : N ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec
      (uniformMNat N + uctTmpJ) ≤ K := by
  obtain ⟨τ, υ, ξ, hτ, hυ, hξ, hframe1, hframe2, hframe3, hp1, hv1, hp2, hv2, hp3, hv3⟩ :=
    uniform_emit_dispatch_three_tmp_value_decode N base outer addr l1 l2 l3 rest pref σr σdec
      hprep hbound1 hbound2 hbound3
  have hstate := uniform_emit_dispatch_three_tmp_value_writer N base outer addr l1 l2 l3 rest
    pref σr σdec τ υ ξ hprep hframe1 hframe2 hframe3
  obtain ⟨hp1ξ, hv1ξ, hp2ξ, hv2ξ, hposξ, hnegξ, hfreshξ⟩ :=
    uniform_emit_dispatch_three_tmp_value_registers N base outer addr l1 l2 l3 rest pref σr σdec
      τ υ ξ hprep hframe1 hframe2 hframe3 hp1 hv1 hp2 hv2
  obtain ⟨hroom1, hroom2⟩ := uniform_emit_dispatch_three_tmp_value_rooms N base outer addr l1 l2 l3
    rest pref σr σdec hprep
  have htmp := uniform_emit_dispatch_three_tmp_value_append N base l1 l2 l3 pref ξ hprep.safety
    hstate hp1ξ hv1ξ hp2ξ hv2ξ hp3 hv3 hposξ hnegξ hfreshξ hroom1 hroom2
  have hlen : σdec uctLengthReg = 3 := by simpa using hprep.length
  rw [uniform_emit_dispatch_three_tmp_value_dispatch_eval N σdec τ υ ξ hsaved hlen hτ hυ hξ
    hframe1 hframe2]
  exact uniform_emit_dispatch_three_tmp_value_commit_bound N K _ (by omega)

lemma uniform_emit_dispatch_empty_tmp_value
    (N K base outer addr : ℕ) (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr [] rest pref σr σdec)
    (hKbase : base ≤ K) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec
      (uniformMNat N + uctTmpJ) ≤ K := by
  have hroom1 : uniformStartNat + pref.length + base + base + base + 6 <
      uniformMNat N + uctCurJ := by
    have hr := hprep.room
    simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
      NPComplete.BitEncoding.encodeNat_length,
      List.length_append] at hr ⊢
    omega
  have hroom2 : uniformStartNat +
      (pref ++ encodedLiteralBits 0 base ++ encodedLiteralBits 0 base ++
        encodedLiteralBits 0 base).length + 1 + base + base + base + 6 <
      uniformMNat N + uctCurJ := by
    have hr := hprep.room
    simp [clauseToThree, encodeThreeClausesPayload, encodeThreeClause, encodeLiteral,
      encodedLiteralBits,
      NPComplete.BitEncoding.encodeNat_length, List.length_append] at hr ⊢
    omega
  have hfirst := writerAppendClauseThreeProg_tmp_value
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
    uctPosPolReg uctFreshReg uctPosPolReg uctFreshReg uctNegPolReg uctFreshReg
    uctPosPolReg uctNegPolReg uctFreshReg 0 base 0 base 1 base base (σ := σdec)
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
    hprep.pos_value hprep.fresh_value hprep.pos_value hprep.fresh_value
    hprep.pos_value hprep.neg_value hprep.fresh_value
    (by simp) (by simp) (by simp)
    ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩
    ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩
    ⟨hprep.safety.neg_below, hprep.safety.fresh_below⟩
    hprep.safety.pos_below hprep.safety.neg_below hprep.safety.fresh_below
    hprep.writer hroom1 (by omega)
    (by
      have hf := writerAppendThreeRegsProg_frame (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
        uctPosPolReg uctFreshReg uctPosPolReg uctFreshReg uctPosPolReg uctFreshReg
        0 base 0 base 0 base σdec uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
        hprep.pos_value hprep.fresh_value hprep.pos_value hprep.fresh_value hprep.pos_value
        hprep.fresh_value (by simp) (by simp) (by simp)
        hprep.safety.fresh_below
        ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩
        ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩ hprep.writer hroom1
        (r := uctNegPolReg) hprep.safety.neg_below
      exact hf.trans hprep.neg_value)
    (by
      have hf := writerAppendThreeRegsProg_frame (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
        uctPosPolReg uctFreshReg uctPosPolReg uctFreshReg uctPosPolReg uctFreshReg
        0 base 0 base 0 base σdec uniform_cur_j_bounds.1 uniform_cur_j_bounds.2
        hprep.pos_value hprep.fresh_value hprep.pos_value hprep.fresh_value hprep.pos_value
        hprep.fresh_value (by simp) (by simp) (by simp)
        hprep.safety.fresh_below
        ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩
        ⟨hprep.safety.pos_below, hprep.safety.fresh_below⟩ hprep.writer hroom1
        (r := uctFreshReg) hprep.safety.fresh_below
      exact hf.trans hprep.fresh_value)
  have htmpLe :
      (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval σdec
        (uniformMNat N + uctTmpJ) ≤ K := by
    have hbaseK : base ≤ K := hKbase
    have htmp :
        (writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval σdec
          (uniformMNat N + uctTmpJ) = base := by
      simpa [writerAppendClauseEmptyProg, writerAppendClauseThreeProg] using hfirst
    exact htmp ▸ hbaseK
  have hlen : σdec uctLengthReg = 0 := by simpa using hprep.length
  have hdispatch :
      (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
        uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec =
      (emitClauseCommitProg uctOuterReg).eval
        ((emitClauseEmptyFreshProg uctFreshReg).eval
          ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval σdec)) := by
    simp only [emitClauseDispatchProgAt, emitClauseDispatchProgAtWithLong, eval_ifNZ]
    rw [ite_eq_left (by simp [Expr.eval, hlen])]
    simp [eval_seq]
  rw [hdispatch]
  have htmpFresh :
      (emitClauseEmptyFreshProg uctFreshReg).eval
          ((writerAppendClauseEmptyProg uctCurJ uctTmpJ uctPosPolReg uctNegPolReg uctFreshReg).eval σdec)
        (uniformMNat N + uctTmpJ) ≤ K := by
    have hne : uctFreshReg ≠ uniformMNat N + uctTmpJ := by
      have hm := uniformMNat_ge_25 N
      simp [uctFreshReg, uctTmpJ]
      omega
    simpa [emitClauseEmptyFreshProg, eval_assign, Expr.eval,
      writeReg_diff _ uctFreshReg _ _ hne.symm] using htmpLe
  have hout : uctOuterReg ≠ uniformMNat N + uctTmpJ := by
    simp only [uctOuterReg, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  simpa [emitClauseCommitProg, eval_assign, Expr.eval,
    writeReg_diff _ uctOuterReg _ _ hout.symm] using htmpFresh

lemma uniform_emit_dispatch_short_tmp_value_of_prep
    (N K base outer addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest pref : Bits) (σr σdec : Store)
    (hprep : EmitClausePrepState (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctOuterReg
      uctFreshReg uctPosPolReg uctNegPolReg N base outer addr ls rest pref σr σdec)
    (hsaved : σdec uctSavedBoundReg = N)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hN : N ≤ K) (hbase : base ≤ K) (hlen : ls.length ≤ 3) :
    (emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg).eval σdec
      (uniformMNat N + uctTmpJ) ≤ K := by
  cases ls with
  | nil =>
      simpa using uniform_emit_dispatch_empty_tmp_value N K base outer addr rest pref σr σdec
        hprep hbase
  | cons l1 restLs =>
      cases restLs with
      | nil =>
          simpa using uniform_emit_dispatch_one_tmp_value N K base outer addr l1 rest pref σr σdec
            hprep hsaved (hbound l1 (by simp)) hN
      | cons l2 restLs =>
          cases restLs with
          | nil =>
              simpa using uniform_emit_dispatch_two_tmp_value N K base outer addr l1 l2 rest pref σr σdec
                hprep hsaved (hbound l1 (by simp)) (hbound l2 (by simp)) hN
          | cons l3 restLs =>
              cases restLs with
              | nil =>
                  simpa using uniform_emit_dispatch_three_tmp_value N K base outer addr l1 l2 l3 rest pref
                    σr σdec hprep hsaved (hbound l1 (by simp)) (hbound l2 (by simp))
                    (hbound l3 (by simp)) hN
              | cons l4 restLs =>
                  simp only [List.length_cons] at hlen
                  omega

end NPComplete.CookLevin

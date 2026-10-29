module

public import NPComplete.CookLevin.ToThreeCNF.LongLoop

/-!
# Long-clause split-tail program

The short-clause writer cannot directly emit an arbitrarily long clause, so the
long case is generated incrementally from a tail payload. This module defines
that setup and emission program and proves its evaluation establishes the
expected writer state.
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
/-! A long-clause emitter is split into a fixed two-literal prefix and the
dynamic tail emitter.  The prefix writes only the first clause
`(l1,l2,pos base)`; the tail starts with carry `neg base` and fresh variable
`base + 1`.  Keeping this setup explicit makes the endpoint theorem reusable
by the outer clause scanner without changing the split-tail machine. -/

def splitTailEmitLongClauseSetup
    (curJ tmpJ cursorReg _polReg _varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ) : Program :=
  .seq
    (decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound)
    (.seq
      (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound)
      (.seq
        (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
          posPolReg freshReg)
        (.seq
          (.assign carryPolReg (.const 1))
          (.seq
            (.assign carryValReg (.reg freshReg))
            (.seq
              (.assign freshReg (.add (.reg freshReg) (.const 1)))
              (.seq
                (.assign remainingReg (.sub (.reg remainingReg) (.const 2)))
                (.skip)))))))

def splitTailEmitLongClauseProg
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound : ℕ) : Program :=
  .seq
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
    (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound)

lemma splitTailEmitLongClauseProg_eval_of_post
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound : ℕ)
    (base : ℕ) (l1 l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ l3 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: rest).length ≤ tailBound)
    (hpost : SplitTailEmitRel
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
      M curJ tmpJ start (base + 1) (Literal.neg base) (l3 :: rest)
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) tail
      (addr + l1.var + 2 + l2.var + 2)
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg bound tailBound).eval σ ∧
      SplitTailEmitDone τ M curJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg ∧
      base' = (splitTail (base + 1) (Literal.neg base) (l3 :: rest)).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var 0 base) ++
          splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest) ∧
      τ cursorReg =
        (addr + l1.var + 2 + l2.var + 2) +
          (splitTailInputBits (l3 :: rest) []).length := by
  let σsetup :=
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hdone, hbase', hpayload', hcursor'⟩ :=
    splitTailEmitRel_nonempty_fixed_eval
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound
    (base + 1) (Literal.neg base) (l3 :: rest)
    (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base) tail
    (addr + l1.var + 2 + l2.var + 2) σsetup hbound (by simp) hls hpost
  refine ⟨τ, base', carry', ls', pref', addr', ?_, hdone, hbase', hpayload', hcursor'⟩
  rw [splitTailEmitLongClauseProg, eval_seq]
  simpa [σsetup] using hτ

lemma split_tail_emit_long_clause_payload
    (base : ℕ) (l1 l2 l3 : Literal) (rest : List Literal) :
    encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base ++
      splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest) =
      encodeThreeClausesPayload (clauseToThree base (l1 :: l2 :: l3 :: rest)).1 := by
  have hfirst := encodedThreeLiteralBits_eq_encodeThreeClause
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base
    (by cases l1 <;> simp [literalPolarity])
    (by cases l2 <;> simp [literalPolarity]) (Or.inl rfl)
  rw [clauseToThree_cons4_splitTail_entry, splitTailPayload_eq_encode]
  simp only [encodeThreeClausesPayload, List.map_cons, List.flatten_cons]
  have hfirst' : encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base =
      encodeThreeClause ⟨l1, l2, Literal.pos base⟩ := by
    cases l1 <;> cases l2 <;>
      simpa [Literal.var, literalPolarity, literalOfPolarity] using hfirst
  rw [hfirst']

lemma encodedThreeLiteralBits_length
    (pol1 val1 pol2 val2 pol3 val3 : ℕ) :
    (encodedThreeLiteralBits pol1 val1 pol2 val2 pol3 val3).length =
      val1 + val2 + val3 + 6 := by
  simp [encodedThreeLiteralBits, encodedLiteralBits, List.length_append, encodeNat_length]
  omega

/-- Both capacity obligations of the long-clause setup follow from the outer
    clause payload bound: the two-literal prefix emitted by the setup is exactly
    the first clause of the outer payload, so the split form and the outer form
    describe the same total emission. -/
lemma splitTailPayload_room_of_encodeThreeClausesPayload
    (M curJ start base : ℕ) (l1 l2 l3 : Literal) (rest : List Literal)
    (pref : Bits)
    (hroom : start + pref.length +
      (encodeThreeClausesPayload (clauseToThree base (l1 :: l2 :: l3 :: rest)).1).length
      + 2 < M + curJ) :
    start + pref.length + l1.var + l2.var + base + 6 < M + curJ ∧
    start + (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest)).length + 2 <
      M + curJ := by
  have hpayload := split_tail_emit_long_clause_payload base l1 l2 l3 rest
  have hlen : (encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base).length = l1.var + l2.var + base + 6 := by
    rw [encodedThreeLiteralBits_length]
  have happ : (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base).length =
      pref.length + (encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length := by
    rw [List.length_append]
  have hsecond : start + (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
      (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest)).length + 2 <
      M + curJ := by
    have hjoin : (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
        (splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest)).length =
        pref.length +
        (encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: rest)).1).length := by
      have h1 : (pref ++ (encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var 0 base ++
          splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest))).length =
          pref.length + (encodedThreeLiteralBits (literalPolarity l1) l1.var
            (literalPolarity l2) l2.var 0 base).length +
          (splitTailPayload (base + 1) (Literal.neg base) (l3 :: rest)).length := by
        simp only [List.length_append]
        omega
      rw [hpayload] at h1
      simp only [List.length_append] at h1
      omega
    omega
  exact ⟨by omega, hsecond⟩

/-- Parsing the first two literals of a long clause: the writer state is preserved,
    the remaining input sits above the consumed literals, and the writer-side
    registers and the high memory are untouched. -/
lemma splitTailEmitLongClauseSetup_eval_parse
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ)
    (l1 l2 : Literal) (lsTail : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (htmpJ : curJ < tmpJ) (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref) (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    ∃ υ, υ = (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval
        ((decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ) ∧
      WriterState υ M curJ start pref ∧
      BitsFrom σ (addr + l1.var + 2 + l2.var + 2) (splitTailInputBits lsTail tail) ∧
      υ pol2Reg = literalPolarity l1 ∧ υ var2Reg = l1.var ∧
      υ pol3Reg = literalPolarity l2 ∧ υ var3Reg = l2.var ∧
      υ cursorReg = addr + l1.var + 2 + l2.var + 2 ∧
      (∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg ∨
        r = remainingReg → υ r = σ r) ∧
      (∀ r, M + tmpJ < r → υ r = σ r) := by
  have hbits12 : BitsFrom σ addr
      (encodeLiteral l1 ++ encodeLiteral l2 ++ splitTailInputBits lsTail tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hinput
  obtain ⟨τ, υ, hτ, hυ, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2,
      hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg bound
      addr l1 l2 (splitTailInputBits lsTail tail) σ
      hsafety.second.distinct.1 hsafety.second.distinct.2.1
      hsafety.second.distinct.2.2.1 hsafety.second.distinct.2.2.2.1
      hsafety.second.distinct.2.2.2.2.1 hsafety.second.distinct.2.2.2.2.2
      hsafety.third.distinct.1 hsafety.third.distinct.2.1
      hsafety.third.distinct.2.2.2.1 hsafety.third.distinct.2.2.2.2.1
      hsafety.third.distinct.2.2.2.2.2
      ⟨lt_of_lt_of_le hsafety.second.below.1 hstartAtInput,
        lt_of_lt_of_le hsafety.second.below.2.1 hstartAtInput,
        lt_of_lt_of_le hsafety.second.below.2.2.1 hstartAtInput,
        lt_of_lt_of_le hsafety.third.below.2.1 hstartAtInput,
        lt_of_lt_of_le hsafety.third.below.2.2.1 hstartAtInput,
        lt_of_lt_of_le hsafety.second.below.2.2.2 hstartAtInput⟩
      hbound1 hbound2 hcursor hbits12
  have hlen1 : (encodeLiteral l1).length = l1.var + 2 := by
    cases l1 <;> simp [encodeLiteral, encodeNat_length, var_pos, var_neg]
  have hlen2 : (encodeLiteral l2).length = l2.var + 2 := by
    cases l2 <;> simp [encodeLiteral, encodeNat_length, var_pos, var_neg]
  have htailσ : BitsFrom σ (addr + l1.var + 2 + l2.var + 2)
      (splitTailInputBits lsTail tail) := by
    have h := (bitsFrom_append σ addr (encodeLiteral l1 ++ encodeLiteral l2) _ hbits12).2
    convert h using 1
    simp [hlen1, hlen2, List.length_append]
    omega
  have hτstate : WriterState τ M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref σ τ
      cursorReg pol2Reg var2Reg doneReg hwriter
      (by simpa [hτ] using hframe1)
      hsafety.second.nonzero.1 hsafety.second.nonzero.2.1
      hsafety.second.nonzero.2.2.1 hsafety.second.nonzero.2.2.2
      hsafety.second.below.1 hsafety.second.below.2.1
      hsafety.second.below.2.2.1 hsafety.second.below.2.2.2
  have hυstate : WriterState υ M curJ start pref :=
    writerState_transport_of_frame4 M curJ start pref τ υ
      cursorReg pol3Reg var3Reg doneReg hτstate
      (by simpa [hυ] using hframe2)
      hsafety.third.nonzero.1 hsafety.third.nonzero.2.1
      hsafety.third.nonzero.2.2.1 hsafety.third.nonzero.2.2.2
      hsafety.third.below.1 hsafety.third.below.2.1
      hsafety.third.below.2.2.1 hsafety.third.below.2.2.2
  have hwriterFrame : ∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
      r = freshReg ∨ r = remainingReg → υ r = σ r := by
    intro r hr
    have hs := hsafety.writer_parser r hr
    exact (hframe2 r hs.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hs.2.2.2.1).trans
      (hframe1 r hs.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.1)
  have hhigh : ∀ r, M + tmpJ < r → υ r = σ r := by
    intro r hr
    have := hsafety.second.below.1
    have := hsafety.second.below.2.1
    have := hsafety.second.below.2.2.1
    have := hsafety.second.below.2.2.2
    have := hsafety.third.below.2.1
    have := hsafety.third.below.2.2.1
    have := hwriter.safe
    exact (hframe2 r (by omega) (by omega) (by omega) (by omega)).trans
      (hframe1 r (by omega) (by omega) (by omega) (by omega))
  refine ⟨υ, hυ.trans (by rw [hτ]), hυstate, htailσ, ?_, ?_, hpol2, hvar2, hcur2,
    hwriterFrame, hhigh⟩
  · exact (hframe2 pol2Reg (Ne.symm hsafety.second.distinct.1) hsafety.cross.1
      hsafety.cross.2.1 hsafety.second.distinct.2.2.2.2.1).trans hpol1
  · exact (hframe2 var2Reg (Ne.symm hsafety.second.distinct.2.1) hsafety.cross.2.2.1
      hsafety.cross.2.2.2 hsafety.second.distinct.2.2.2.2.2).trans hvar1
/-- Appending the two parsed literals to the writer keeps the writer state and the
    remaining input, and only touches memory strictly between the writer registers
    and the temporary cell. -/
lemma splitTailEmitLongClauseSetup_eval_writer
    (M curJ tmpJ start pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg : ℕ)
    (base : ℕ) (l1 l2 : Literal) (pref bits : Bits) (addr2 : ℕ) (υ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hfirstPol : υ pol2Reg = literalPolarity l1) (hfirstVar : υ var2Reg = l1.var)
    (hsecondPol : υ pol3Reg = literalPolarity l2) (hsecondVar : υ var3Reg = l2.var)
    (hpos : υ posPolReg = 0) (hfresh : υ freshReg = base)
    (hlow1 : pol2Reg < start ∧ var2Reg < start)
    (hlow2 : pol3Reg < start ∧ var3Reg < start)
    (hlow3 : posPolReg < start ∧ freshReg < start)
    (hυstate : WriterState υ M curJ start pref)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hinputAbove : M + tmpJ < addr2) (hbits : BitsFrom υ addr2 bits) :
    WriterState ((writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
        posPolReg freshReg).eval υ) M curJ start
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) ∧
    BitsFrom ((writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
        posPolReg freshReg).eval υ) addr2 bits ∧
    (∀ r, r < start →
      (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
        posPolReg freshReg).eval υ r = υ r) ∧
    (∀ r, M + tmpJ < r →
      (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
        posPolReg freshReg).eval υ r = υ r) := by
  have hpol1 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpol2 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  refine ⟨?_, ?_, fun r hr => ?_, fun r hr => ?_⟩
  · simpa [encodedThreeLiteralBits, List.append_assoc] using
      writerAppendThreeRegsProg_eval M curJ tmpJ start pref
        pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
        (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
        hcurJ htmpJ hfirstPol hfirstVar hsecondPol hsecondVar hpos hfresh
        hpol1 hpol2 (Or.inl rfl) hlow1.2 hlow2 hlow3 hυstate hroom
  · exact writerAppendThreeRegsProg_bitsFrom_frame M curJ tmpJ start pref bits addr2
      pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
      hcurJ htmpJ hfirstPol hfirstVar hsecondPol hsecondVar hpos hfresh
      hpol1 hpol2 (Or.inl rfl) hlow1.2 hlow2 hlow3 hυstate hroom hinputAbove hbits
  · exact writerAppendThreeRegsProg_frame M curJ tmpJ start pref
      pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
      hcurJ htmpJ hfirstPol hfirstVar hsecondPol hsecondVar hpos hfresh
      hpol1 hpol2 (Or.inl rfl) hlow1.2 hlow2 hlow3 hυstate hroom hr
  · exact writerAppendThreeRegsProg_frame_high M curJ tmpJ start pref
      pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
      (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
      hcurJ htmpJ hfirstPol hfirstVar hsecondPol hsecondVar hpos hfresh
      hpol1 hpol2 (Or.inl rfl) hlow1.2 hlow2 hlow3 hυstate hroom hr

/-- Values and frame of the four trailing assignments of the long-clause setup. -/
lemma splitTailEmitLongClauseSetup_eval_assign_values
    (carryPolReg carryValReg freshReg remainingReg base n : ℕ) (σw σ4 : Store)
    (hσ4 : σ4 = writeReg (writeReg (writeReg (writeReg σw carryPolReg 1)
      carryValReg base) freshReg (base + 1)) remainingReg n)
    (hcpcv : carryPolReg ≠ carryValReg) (hcpfr : carryPolReg ≠ freshReg)
    (hcprem : carryPolReg ≠ remainingReg) (hcvfr : carryValReg ≠ freshReg)
    (hcvrem : carryValReg ≠ remainingReg) (hfrrem : freshReg ≠ remainingReg) :
    σ4 carryPolReg = 1 ∧ σ4 carryValReg = base ∧ σ4 freshReg = base + 1 ∧
      σ4 remainingReg = n ∧
      ∀ r, r ≠ carryPolReg → r ≠ carryValReg → r ≠ freshReg → r ≠ remainingReg →
        σ4 r = σw r := by
  subst hσ4
  refine ⟨?_, ?_, ?_, ?_, fun r hcp hcv hfr hr => ?_⟩
  · rw [writeReg_diff _ _ _ _ hcprem, writeReg_diff _ _ _ _ hcpfr,
      writeReg_diff _ _ _ _ hcpcv, writeReg_same]
  · rw [writeReg_diff _ _ _ _ hcvrem, writeReg_diff _ _ _ _ hcvfr, writeReg_same]
  · rw [writeReg_diff _ _ _ _ hfrrem, writeReg_same]
  · rw [writeReg_same]
  · rw [writeReg_diff _ _ _ _ hr, writeReg_diff _ _ _ _ hfr,
      writeReg_diff _ _ _ _ hcv, writeReg_diff _ _ _ _ hcp]

/-- The four trailing assignments of the long-clause setup keep the writer state,
    since all written registers lie below `start`. -/
lemma splitTailEmitLongClauseSetup_eval_assign_writer
    (M curJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg : ℕ)
    (base n : ℕ) (pref : Bits) (σw : Store)
    (hw : WriterState σw M curJ start pref)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    WriterState (writeReg (writeReg (writeReg (writeReg σw carryPolReg 1)
      carryValReg base) freshReg (base + 1)) remainingReg n) M curJ start pref := by
  have h1 := writerState_assign_value M curJ start pref carryPolReg 1 σw hw
    hsafety.writer_below.1 hsafety.carry_pol_nonzero
  have h2 := writerState_assign_value M curJ start pref carryValReg base _ h1
    hsafety.writer_below.2.1 hsafety.writer_nonzero.1
  have h3 := writerState_assign_value M curJ start pref freshReg (base + 1) _ h2
    hsafety.writer_below.2.2.2.1 hsafety.writer_nonzero.2
  exact writerState_assign_value M curJ start pref remainingReg n _ h3
    hsafety.writer_below.2.2.2.2 hsafety.remaining_nonzero

/-- Closed form of the long-clause setup output as four register writes on top of the
    writer-appended store. -/
lemma splitTailEmitLongClauseSetup_eval_eq_assigns
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ)
    (base : ℕ) (l1 l2 : Literal) (lsTail : List Literal) (σ υ σw : Store)
    (hυ : υ = (decodeLiteralValueProgram cursorReg pol3Reg var3Reg doneReg bound).eval
        ((decodeLiteralValueProgram cursorReg pol2Reg var2Reg doneReg bound).eval σ))
    (hσw : σw = (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg var3Reg
      posPolReg freshReg).eval υ)
    (hfresh : σw freshReg = base)
    (hrem : σw remainingReg = (l1 :: l2 :: lsTail).length)
    (hcpfr : carryPolReg ≠ freshReg) (hcprem : carryPolReg ≠ remainingReg)
    (hcvfr : carryValReg ≠ freshReg) (hcvrem : carryValReg ≠ remainingReg)
    (hfrrem : freshReg ≠ remainingReg) :
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ =
    writeReg (writeReg (writeReg (writeReg σw carryPolReg 1)
      carryValReg base) freshReg (base + 1)) remainingReg lsTail.length := by
  simp only [splitTailEmitLongClauseSetup, eval_seq]
  rw [← hυ, ← hσw]
  simp [eval_assign, Expr.eval, writeReg_diff _ _ _ _ hcpfr.symm,
    writeReg_diff _ _ _ _ hcvfr.symm, writeReg_diff _ _ _ _ hcprem.symm,
    writeReg_diff _ _ _ _ hcvrem.symm, writeReg_diff _ _ _ _ hfrrem.symm,
    hfresh, hrem]

/-! The concrete setup theorem for a long clause.  The incoming relation
already contains the writer/input separation and the register safety facts;
the setup only consumes the first two literals and prepares the split-tail
carry/fresh counters. -/

lemma splitTailEmitLongClauseSetup_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ)
    (base : ℕ) (l1 l2 : Literal) (lsTail : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) lsTail).length + 2 <
      M + curJ)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hinputAbove : M + tmpJ < addr) (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref)
    (hpos : σ posPolReg = 0) (hfresh : σ freshReg = base)
    (hremaining : σ remainingReg = (l1 :: l2 :: lsTail).length)
    (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    SplitTailEmitRel
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
      M curJ tmpJ start (base + 1) (Literal.neg base) lsTail
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) tail
      (addr + l1.var + 2 + l2.var + 2)
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg ∧
    (∀ r, M + tmpJ < r →
      (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r) ∧
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
      posPolReg = 0 := by
  obtain ⟨υ, hυ, hυstate, htailσ, hfirstPol, hfirstVar, hsecondPol, hsecondVar, hcurυ,
      hwf, hhighυ⟩ :=
    splitTailEmitLongClauseSetup_eval_parse M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound l1 l2 lsTail pref tail addr σ hbound1 hbound2 hinput htmpJ
      hstartAtInput hwriter hcursor hsafety
  have htailυ : BitsFrom υ (addr + l1.var + 2 + l2.var + 2) (splitTailInputBits lsTail tail) :=
    fun i hi => by
      rw [hhighυ _ (by omega)]
      exact htailσ i hi
  have hposυ : υ posPolReg = 0 := (hwf posPolReg (by simp)).trans hpos
  have hfreshυ : υ freshReg = base := (hwf freshReg (by simp)).trans hfresh
  have hremυ : υ remainingReg = (l1 :: l2 :: lsTail).length :=
    (hwf remainingReg (by simp)).trans hremaining
  obtain ⟨hw', htailw, hwlow, hwhigh⟩ :=
    splitTailEmitLongClauseSetup_eval_writer M curJ tmpJ start pol2Reg var2Reg pol3Reg var3Reg
      posPolReg freshReg base l1 l2 pref _ (addr + l1.var + 2 + l2.var + 2) υ hcurJ htmpJ
      hfirstPol hfirstVar hsecondPol hsecondVar hposυ hfreshυ
      ⟨hsafety.second.below.2.1, hsafety.second.below.2.2.1⟩
      ⟨hsafety.third.below.2.1, hsafety.third.below.2.2.1⟩
      ⟨hsafety.writer_below.2.2.1, hsafety.writer_below.2.2.2.1⟩ hυstate hroom
      (lt_of_lt_of_le hinputAbove (by omega)) htailυ
  obtain ⟨σw, hσw⟩ : ∃ σw, σw = (writerAppendThreeRegsProg curJ tmpJ pol2Reg var2Reg pol3Reg
    var3Reg posPolReg freshReg).eval υ := ⟨_, rfl⟩
  rw [← hσw] at hw' htailw hwlow hwhigh
  obtain ⟨hcpcv, hcppos, hcpfr, hcprem, hcvpos, hcvfr, hcvrem, hposfr, hposrem, hfrrem⟩ :=
    hsafety.writer_distinct
  have hσwFresh : σw freshReg = base :=
    (hwlow freshReg hsafety.writer_below.2.2.2.1).trans hfreshυ
  have hσwRem : σw remainingReg = (l1 :: l2 :: lsTail).length :=
    (hwlow remainingReg hsafety.writer_below.2.2.2.2).trans hremυ
  obtain ⟨σ4, hσ4⟩ : ∃ σ4, σ4 = writeReg (writeReg (writeReg (writeReg σw carryPolReg 1)
    carryValReg base) freshReg (base + 1)) remainingReg lsTail.length := ⟨_, rfl⟩
  have hsetup := splitTailEmitLongClauseSetup_eval_eq_assigns curJ tmpJ cursorReg polReg
    varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg bound base l1 l2 lsTail σ υ σw hυ hσw hσwFresh hσwRem hcpfr hcprem
    hcvfr hcvrem hfrrem
  rw [← hσ4] at hsetup
  obtain ⟨h4cp, h4cv, h4fr, h4rem, hframe4⟩ :=
    splitTailEmitLongClauseSetup_eval_assign_values carryPolReg carryValReg freshReg
      remainingReg base lsTail.length σw σ4 hσ4 hcpcv hcpfr hcprem hcvfr hcvrem hfrrem
  have hw4 : WriterState σ4 M curJ start (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base) :=
    hσ4 ▸ splitTailEmitLongClauseSetup_eval_assign_writer M curJ start cursorReg polReg varReg
      doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg base lsTail.length _ σw hw' hsafety
  have hnotCursor : ∀ r, r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨ r = freshReg ∨
      r = remainingReg → r ≠ cursorReg := fun r hr => (hsafety.writer_parser r hr).1
  have hpos4 : σ4 posPolReg = 0 :=
    (hframe4 posPolReg hcppos.symm hcvpos.symm hposfr hposrem).trans
      ((hwlow posPolReg hsafety.writer_below.2.2.1).trans hposυ)
  have hcur4 : σ4 cursorReg = addr + l1.var + 2 + l2.var + 2 :=
    (hframe4 cursorReg (hnotCursor _ (Or.inl rfl)).symm
      (hnotCursor _ (Or.inr (Or.inl rfl))).symm
      (hnotCursor _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).symm
      (hnotCursor _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).symm).trans
      ((hwlow cursorReg hsafety.main.below.1).trans hcurυ)
  have htail4 : BitsFrom σ4 (addr + l1.var + 2 + l2.var + 2) (splitTailInputBits lsTail tail) := by
    intro i hi
    have hlt : ∀ r, r < start → addr + l1.var + 2 + l2.var + 2 + i ≠ r := by omega
    rw [hframe4 _ (hlt _ hsafety.writer_below.1) (hlt _ hsafety.writer_below.2.1)
      (hlt _ hsafety.writer_below.2.2.2.1) (hlt _ hsafety.writer_below.2.2.2.2)]
    exact htailw i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hsetup]
    exact ⟨htail4, hcurJ, htmpJ, lt_of_lt_of_le hinputAbove (by omega),
      le_trans hstartAtInput (by omega), hw4, h4cp, by simp [literalPolarity], h4cv, hpos4,
      h4fr, h4rem, hcur4, hcapacity, hsafety⟩
  · intro r hr
    have hs := hwriter.safe
    have hrs : ∀ s, s < start → r ≠ s := by omega
    rw [hsetup, hframe4 r (hrs _ hsafety.writer_below.1) (hrs _ hsafety.writer_below.2.1)
      (hrs _ hsafety.writer_below.2.2.2.1) (hrs _ hsafety.writer_below.2.2.2.2)]
    exact (hwhigh r hr).trans (hhighυ r hr)
  · rw [hsetup]
    exact hpos4

/-- Writer temporaries avoid the parser registers, so parser decode phases preserve them. -/
lemma splitTailEmitLongClauseSetup_write_regs_avoid_parser
    {start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r = carryPolReg ∨ r = carryValReg ∨ r = posPolReg ∨
      r = freshReg ∨ r = remainingReg) :
    r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧ r ≠ var3Reg ∧ r ≠ doneReg := by
  rcases hsafety.writer_parser r (by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) with
      ⟨hrc, _, _, hrd, hrp2, hrv2, hrp3, hrv3⟩
  exact ⟨hrc, hrp2, hrv2, hrp3, hrv3, hrd⟩

lemma splitTailEmitLongClauseSetup_low_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound : ℕ)
    (base : ℕ) (l1 l2 : Literal) (lsTail : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) lsTail).length + 2 <
      M + curJ)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: lsTail) tail))
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hstartAtInput : start ≤ addr)
    (hwriter : WriterState σ M curJ start pref)
    (hpos : σ posPolReg = 0) (hfresh : σ freshReg = base)
    (hremaining : σ remainingReg = (l1 :: l2 :: lsTail).length)
    (hcursor : σ cursorReg = addr)
    (hsafety : SplitTailRegisterSafety start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ} (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
      r ≠ var3Reg ∧ r ≠ doneReg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧
      r ≠ posPolReg ∧ r ≠ freshReg ∧ r ≠ remainingReg) :
    (splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ r = σ r := by
  rcases hrsafe with ⟨hrc, hrp2, hrv2, hrp3, hrv3, hrd, hrcp, hrcv, hrpos, hrfr, hrrem⟩
  have hbits : BitsFrom σ addr (encodeLiteral l1 ++ encodeLiteral l2 ++
      splitTailInputBits lsTail tail) := by
    simpa [splitTailInputBits, List.append_assoc] using hinput
  have hbelow : cursorReg < start ∧ pol2Reg < start ∧ var2Reg < start ∧
      pol3Reg < start ∧ var3Reg < start ∧ doneReg < start := by
    exact ⟨hsafety.second.below.1, hsafety.second.below.2.1,
      hsafety.second.below.2.2.1, hsafety.third.below.2.1,
      hsafety.third.below.2.2.1, hsafety.second.below.2.2.2⟩
  have hnonzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧
      pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0 := by
    exact ⟨hsafety.second.nonzero.1, hsafety.second.nonzero.2.1,
      hsafety.second.nonzero.2.2.1, hsafety.third.nonzero.2.1,
      hsafety.third.nonzero.2.2.1, hsafety.second.nonzero.2.2.2⟩
  have hwd : ∀ x, x = carryPolReg ∨ x = carryValReg ∨ x = posPolReg ∨
      x = freshReg ∨ x = remainingReg →
      x ≠ cursorReg ∧ x ≠ pol2Reg ∧ x ≠ var2Reg ∧ x ≠ pol3Reg ∧
        x ≠ var3Reg ∧ x ≠ doneReg := by
    intro x hx
    exact splitTailEmitLongClauseSetup_write_regs_avoid_parser hsafety hx
  obtain ⟨τ, υ, hτ, hυ, hcur1, hpol1, hvar1, hcur2, hpol2, hvar2,
      hframe1, hframe2⟩ :=
    decode_two_literal_value_correct cursorReg pol2Reg var2Reg pol3Reg var3Reg doneReg bound addr
      l1 l2 (splitTailInputBits lsTail tail) σ
      hsafety.second.distinct.1 hsafety.second.distinct.2.1
      hsafety.second.distinct.2.2.1 hsafety.second.distinct.2.2.2.1
      hsafety.second.distinct.2.2.2.2.1 hsafety.second.distinct.2.2.2.2.2
      hsafety.third.distinct.1 hsafety.third.distinct.2.1
      hsafety.third.distinct.2.2.2.1
      hsafety.third.distinct.2.2.2.2.1
      hsafety.third.distinct.2.2.2.2.2
      ⟨lt_of_lt_of_le hbelow.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.2.1 hstartAtInput,
        lt_of_lt_of_le hbelow.2.2.2.2.2 hstartAtInput⟩
      hbound1 hbound2 hcursor hbits
  have hτstate : WriterState τ M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref σ τ
      cursorReg pol2Reg var2Reg doneReg hwriter hframe1
      hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2.2.2
      hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2.2.2
  have hυstate : WriterState υ M curJ start pref := by
    apply writerState_transport_of_frame4 M curJ start pref τ υ
      cursorReg pol3Reg var3Reg doneReg hτstate hframe2
      hnonzero.1 hnonzero.2.2.2.1 hnonzero.2.2.2.2.1 hnonzero.2.2.2.2.2
      hbelow.1 hbelow.2.2.2.1 hbelow.2.2.2.2.1 hbelow.2.2.2.2.2
  have hposυ : υ posPolReg = 0 := by
    have hw := hwd posPolReg (Or.inr (Or.inr (Or.inl rfl)))
    simpa [hυ] using (hframe2 posPolReg hw.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2).trans
      ((hframe1 posPolReg hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2.2).trans hpos)
  have hfreshυ : υ freshReg = base := by
    have hw := hwd freshReg (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    simpa [hυ] using (hframe2 freshReg hw.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2).trans
      ((hframe1 freshReg hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2.2).trans hfresh)
  have hp1 : τ pol2Reg = literalPolarity l1 := by
    cases l1 <;> simpa [hτ, literalPolarity] using hpol1
  have hv1 : τ var2Reg = l1.var := by simpa [hτ] using hvar1
  have hp2 : υ pol3Reg = literalPolarity l2 := by
    cases l2 <;> simpa [hυ, literalPolarity] using hpol2
  have hv2 : υ var3Reg = l2.var := by simpa [hυ] using hvar2
  have hpol01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpol02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hp1υ : υ pol2Reg = literalPolarity l1 := by
    have hf := hframe2 pol2Reg hsafety.second.distinct.1.symm hsafety.cross.1
      hsafety.cross.2.1 hsafety.second.distinct.2.2.2.2.1
    rw [hf]; exact hp1
  have hv1υ : υ var2Reg = l1.var := by
    have hf := hframe2 var2Reg hsafety.second.distinct.2.1.symm hsafety.cross.2.2.1
      hsafety.cross.2.2.2 hsafety.second.distinct.2.2.2.2.2
    rw [hf]; exact hv1
  have hw := writerAppendThreeRegsProg_frame M curJ tmpJ start pref
    pol2Reg var2Reg pol3Reg var3Reg posPolReg freshReg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
    hcurJ htmpJ hp1υ hv1υ hp2 hv2 hposυ hfreshυ
    hpol01 hpol02 (Or.inl rfl)
    hsafety.second.below.2.2.1
    ⟨hsafety.third.below.2.1, hsafety.third.below.2.2.1⟩
    ⟨hsafety.writer_below.2.2.1, hsafety.writer_below.2.2.2.1⟩
    hυstate (by omega) hr
  simp only [splitTailEmitLongClauseSetup, eval_seq, eval_assign,
    NPComplete.BoundedWhile.eval_skip, Expr.eval]
  rw [writeReg_diff _ remainingReg _ r hrrem,
    writeReg_diff _ freshReg _ r hrfr, writeReg_diff _ carryValReg _ r hrcv,
    writeReg_diff _ carryPolReg _ r hrcp, ← hτ, ← hυ]
  exact (hw.trans (hframe2 r hrc hrp3 hrv3 hrd)).trans
    (hframe1 r hrc hrp2 hrv2 hrd)

lemma splitTailEmitLongClauseProg_eval_end_to_end
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound : ℕ)
    (base : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
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
    ∃ τ,
      τ = (splitTailEmitLongClauseProg curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg bound tailBound).eval σ ∧
      WriterState τ M curJ start
        (pref ++ encodeThreeClausesPayload (clauseToThree base
          (l1 :: l2 :: l3 :: l4 :: rest)).1) ∧
      τ remainingReg = 0 ∧
      τ freshReg = (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).2 ∧
      τ cursorReg = addr +
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length := by
  have hpost : SplitTailEmitRel
      ((splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ)
      M curJ tmpJ start (base + 1) (Literal.neg base) (l3 :: l4 :: rest)
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) tail
      (addr + l1.var + 2 + l2.var + 2)
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg := by
    exact (splitTailEmitLongClauseSetup_eval
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base l1 l2 (l3 :: l4 :: rest) pref tail addr σ hbound1 hbound2 hroom hcapacity
      hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety).1
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hdone, hbase', hpayload', hcursor'⟩ :=
    splitTailEmitLongClauseProg_eval_of_post
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound base l1 l2 l3 (l4 :: rest) pref tail addr σ hboundTail hls hpost
  have hpayloadFinal :
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ encodeThreeClausesPayload (clauseToThree base
          (l1 :: l2 :: l3 :: l4 :: rest)).1 := by
    calc
      pref' ++ splitTailPayload base' carry' ls' =
          (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
            (literalPolarity l2) l2.var 0 base) ++
            splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest) := hpayload'
      _ = pref ++
          (encodedThreeLiteralBits (literalPolarity l1) l1.var
            (literalPolarity l2) l2.var 0 base ++
            splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)) := by
              simp [List.append_assoc]
      _ = pref ++ encodeThreeClausesPayload (clauseToThree base
          (l1 :: l2 :: l3 :: l4 :: rest)).1 := by
            rw [split_tail_emit_long_clause_payload]
  have hfreshFinal :
      τ freshReg = (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).2 := by
    calc
      τ freshReg = base' := hdone.fresh
      _ = (splitTail (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).2 := hbase'
      _ = (clauseToThree base (l1 :: l2 :: l3 :: l4 :: rest)).2 := by
        exact (congrArg Prod.snd
          (clauseToThree_cons4_splitTail_entry base l1 l2 l3 (l4 :: rest))).symm
  have hcursorFinal :
      τ cursorReg = addr +
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length := by
    have hlen1 : (encodeLiteral l1).length = l1.var + 2 := by
      cases l1 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
    have hlen2 : (encodeLiteral l2).length = l2.var + 2 := by
      cases l2 <;> simp [encodeLiteral, encodeNat_length, Literal.var]
    have hsplit :
        (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length =
          l1.var + 2 + (l2.var + 2 +
            (splitTailInputBits (l3 :: l4 :: rest) []).length) := by
      simp [splitTailInputBits, List.length_append, hlen1, hlen2]
    calc
      τ cursorReg =
          (addr + l1.var + 2 + l2.var + 2) +
            (splitTailInputBits (l3 :: l4 :: rest) []).length := hcursor'
      _ = addr + (splitTailInputBits (l1 :: l2 :: l3 :: l4 :: rest) []).length := by
        rw [hsplit]
        simp [splitTailInputBits, List.length_append]
        omega
  refine ⟨τ, hτ, ?_, hdone.remaining, hfreshFinal, hcursorFinal⟩
  rw [← hpayloadFinal]
  exact hdone.writer

/-! The frame-strengthened long-clause endpoint.  The terminal frame is
    transported across the two-literal setup, so callers retain the input
    suffix and high-register frame relative to the original clause state. -/

lemma splitTailEmitLongClauseProg_eval_end_to_end_frame
    (M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound : ℕ)
    (base : ℕ) (l1 l2 l3 l4 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hboundTail : ∀ l ∈ l3 :: l4 :: rest, l.var + 1 ≤ bound)
    (hls : (l3 :: l4 :: rest).length ≤ tailBound)
    (hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ)
    (hcapacity : start +
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base).length +
      (splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).length + 2 <
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
      base' = (splitTail (base + 1) (Literal.neg base) (l3 :: l4 :: rest)).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
          (literalPolarity l2) l2.var 0 base) ++
          splitTailPayload (base + 1) (Literal.neg base) (l3 :: l4 :: rest) ∧
      τ cursorReg =
        (addr + l1.var + 2 + l2.var + 2) +
          (splitTailInputBits (l3 :: l4 :: rest) []).length := by
  let setup := splitTailEmitLongClauseSetup curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    bound
  obtain ⟨hpost, hsetupHigh, hsetupPos⟩ := splitTailEmitLongClauseSetup_eval
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    bound base l1 l2 (l3 :: l4 :: rest) pref tail addr σ hbound1 hbound2 hroom hcapacity
    hinput hcurJ htmpJ hinputAbove hstartAtInput hwriter hpos hfresh hremaining hcursor hsafety
  let σsetup := setup.eval σ
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hdone, hbase', hpayload', hcursor'⟩ :=
    splitTailEmitRel_nonempty_fixed_eval_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound tailBound (base + 1) (Literal.neg base) (l3 :: l4 :: rest)
      (pref ++ encodedThreeLiteralBits (literalPolarity l1) l1.var
        (literalPolarity l2) l2.var 0 base) tail
      (addr + l1.var + 2 + l2.var + 2) σsetup
      hboundTail (by simp) hls hpost
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
  exact ⟨τ, base', carry', ls', pref', addr', hlong, hframe, hbase', hpayload', hcursor'⟩


end NPComplete.CookLevin

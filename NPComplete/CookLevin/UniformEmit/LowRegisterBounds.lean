module

public import NPComplete.CookLevin.UniformEmit.DecodeBounds

/-! ## Low-register bounds of the CNF decoder's exit state

The decode exit-value theorems track cursor, counters, and statistics, but
not the polarity/variable/done scratch registers.  The startup store bound
needs those too: `pol` stays Boolean, `var` stays within the bound, and
`done` stays Boolean, at every scanner state. -/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral)

/-- The literal scanner leaves the polarity register Boolean. -/
lemma decodeClauseStep_pol_le_one
    (cursorReg polReg varReg doneReg remainingReg maxReg bound addr k : ℕ)
    (l : Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrp : remainingReg ≠ polReg) (hmp : maxReg ≠ polReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr)
    (hrem : σ remainingReg = k + 1)
    (hbound : l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest)) :
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ
        polReg ≤ 1 := by
  obtain ⟨_, hpol, _, _, _⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l rest σ
      hcp hcv hcd hpv hpd hvd hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2.1
      hbound hc hbits
  have hpolle : ((decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ)
      polReg ≤ 1 := by
    rw [hpol]
    cases l <;> simp
  unfold decodeClauseStep
  rw [eval_ifNZ, eval_seq, eval_seq]
  simp only [Expr.eval, hrem, eval_skip, eval_assign]
  rw [ite_eq_left (by omega : k + 1 ≠ 0), eval_ifNZ]
  set τ := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ with hτ
  set υ := writeReg τ remainingReg (τ remainingReg - 1) with hυ
  by_cases hlt : (Expr.lt (.reg maxReg) (.reg varReg)).eval υ ≠ 0
  · rw [ite_eq_left hlt, eval_assign]
    simp only [Expr.eval]
    rw [writeReg_diff υ maxReg _ polReg (Ne.symm hmp), hυ,
      writeReg_diff τ remainingReg _ polReg (Ne.symm hrp)]
    omega
  · rw [ite_eq_right hlt, eval_skip, hυ,
    writeReg_diff τ remainingReg _ polReg (Ne.symm hrp)]
    omega

/-- The literal scanner loop keeps `pol` Boolean, `var` within the bound, and
    `done` Boolean, whatever the clause's literal payload is. -/
lemma decodeClauseStep_low_regs
    (cursorReg polReg varReg doneReg remainingReg maxReg bound addr m : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hrm : remainingReg ≠ maxReg)
    (hmc : maxReg ≠ cursorReg) (hmp : maxReg ≠ polReg)
    (hmv : maxReg ≠ varReg) (hmd : maxReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr)
    (hrem : σ remainingReg = xs.length) (hc : σ cursorReg = addr)
    (hmax : σ maxReg = m)
    (hbound : ∀ l ∈ xs, l.var + 1 ≤ bound)
    (hpol : σ polReg ≤ 1) (hvar : σ varReg ≤ bound) (hdone : σ doneReg ≤ 1)
    (hbits : BitsFrom σ addr ((xs.map encodeLiteral).flatten ++ rest)) :
    (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg
        bound) xs.length σ) polReg ≤ 1 ∧
      (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg
        bound) xs.length σ) varReg ≤ bound ∧
      (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg
        bound) xs.length σ) doneReg ≤ 1 := by
  induction xs generalizing addr m σ with
  | nil =>
      simp only [List.length_nil, NPComplete.BoundedWhile.loopEval_zero]
      exact ⟨hpol, hvar, hdone⟩
  | cons l ls ih =>
      have hshape : ((l :: ls).map encodeLiteral).flatten ++ rest =
          encodeLiteral l ++ ((ls.map encodeLiteral).flatten ++ rest) := by
        simp
      rw [hshape] at hbits
      obtain ⟨hhead, htail⟩ := bitsFrom_append σ addr (encodeLiteral l)
        ((ls.map encodeLiteral).flatten ++ rest) hbits
      have hrem' : σ remainingReg = ls.length + 1 := by simpa using hrem
      have hbound_l : l.var + 1 ≤ bound := hbound l (by simp)
      obtain ⟨hcur1, hvar1, hdone1, hrem1, hmax1, hframe1⟩ :=
        decodeClauseStep_eval cursorReg polReg varReg doneReg remainingReg maxReg bound
          addr ls.length m l ((ls.map encodeLiteral).flatten ++ rest) σ
          hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hrm hmc hmp hmv hmd hbelow
          hrem' hmax hbound_l hc hbits
      have hpol1 :=
        decodeClauseStep_pol_le_one cursorReg polReg varReg doneReg remainingReg maxReg
          bound addr ls.length l ((ls.map encodeLiteral).flatten ++ rest) σ
          hcp hcv hcd hpv hpd hvd hrp hmp hbelow
          hrem' hbound_l hc hbits
      set σ1 := (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg
        bound).eval σ with hσ1
      have hlen : (encodeLiteral l).length = l.var + 2 := by
        cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
      set addr' := addr + (encodeLiteral l).length with haddr'
      have hc1 : σ1 cursorReg = addr' := by
        calc
          σ1 cursorReg = addr + l.var + 2 := hcur1
          _ = addr + (encodeLiteral l).length := by rw [hlen]; omega
          _ = addr' := by omega
      have hbits1 : BitsFrom σ1 addr' ((ls.map encodeLiteral).flatten ++ rest) := by
        intro i hi
        have hfr := hframe1 (addr' + i)
          (by rw [haddr']; omega) (by rw [haddr']; omega) (by rw [haddr']; omega)
          (by rw [haddr']; omega) (by rw [haddr']; omega) (by rw [haddr']; omega)
        calc
          σ1 (addr' + i) = σ (addr' + i) := hfr
          _ = σ (addr + (encodeLiteral l).length + i) := by rw [haddr']
          _ = if ((ls.map encodeLiteral).flatten ++ rest)[i] then 1 else 0 := htail i hi
      have hvar1' : σ1 varReg ≤ bound := by
        calc
          σ1 varReg = l.var := hvar1
          _ ≤ bound := by omega
      have hdone1' : σ1 doneReg ≤ 1 := by
        calc
          σ1 doneReg = 1 := hdone1
          _ ≤ 1 := le_rfl
      have hbelow' : cursorReg < addr' ∧ polReg < addr' ∧ varReg < addr' ∧
          doneReg < addr' ∧ remainingReg < addr' ∧ maxReg < addr' := by
        rw [haddr']
        omega
      have hbound_ls : ∀ l' ∈ ls, l'.var + 1 ≤ bound := by
        intro l' hl'
        exact hbound l' (by simp [hl'])
      have hrest := ih (addr := addr') (m := max m l.var) (σ := σ1)
        (hrem := by simpa using hrem1) (hbelow := hbelow') (hc := hc1)
        (hmax := by simpa [hσ1] using hmax1) (hbound := hbound_ls) (hpol := hpol1)
        (hvar := hvar1') (hdone := hdone1') (hbits := hbits1)
      rw [List.length_cons, loopEval_succ]
      exact hrest

/-- Prefix phase of the dynamic clause step: after reading the length prefix, the scratch
    registers keep their bounds and the cursor/remaining/length registers are positioned at the
    literal payload. -/
lemma decodeCNFStepDynamic_low_regs_prefix
    (bound a m : ℕ) (ls : List Literal) (tail : Bits) (τ : Store)
    (ha : 12 ≤ a) (hc : τ uctCursorReg = a) (hmax : τ uctMaxReg = m)
    (hbound : ls.length + 1 ≤ bound)
    (hpol : τ uctPolReg ≤ 1) (hvar : τ uctVarReg ≤ bound)
    (hbits : BitsFrom τ a (encodeList encodeLiteral ls ++ tail)) :
    ∃ τ4, τ4 = (decodeClauseWithLengthPrefix uctCursorReg uctDoneReg uctRemainingReg
        uctLengthReg bound).eval τ ∧
      τ4 uctPolReg ≤ 1 ∧ τ4 uctVarReg ≤ bound ∧ τ4 uctDoneReg = 0 ∧
      τ4 uctLengthReg = ls.length ∧ τ4 uctRemainingReg = ls.length ∧
      τ4 uctCursorReg = a + ls.length + 1 ∧ τ4 uctMaxReg = m ∧
      BitsFrom τ4 (a + ls.length + 1) ((ls.map encodeLiteral).flatten ++ tail) := by
  have hshape : encodeList encodeLiteral ls ++ tail =
      encodeNat ls.length ++ ((ls.map encodeLiteral).flatten ++ tail) := by
    simp [encodeList, List.append_assoc]
  have hbitsSplit := hbits
  rw [hshape] at hbitsSplit
  obtain ⟨hpre, htail⟩ := bitsFrom_append τ a (encodeNat ls.length)
    ((ls.map encodeLiteral).flatten ++ tail) hbitsSplit
  set τ0 := (Program.assign uctDoneReg (.const 0)).eval τ with hτ0
  have hτ0frame : ∀ r, r ≠ uctDoneReg → τ0 r = τ r := by
    intro r hr
    simp [τ0, eval_assign, Expr.eval, writeReg_diff _ uctDoneReg _ r hr]
  set τ1 := (Program.assign uctLengthReg (.const 0)).eval τ0 with hτ1
  have hτ1len : τ1 uctLengthReg = 0 := by
    simp [τ1, eval_assign, Expr.eval]
  have hτ1frame : ∀ r, r ≠ uctLengthReg → τ1 r = τ0 r := by
    intro r hr
    simp [τ1, eval_assign, Expr.eval, writeReg_diff _ uctLengthReg _ r hr]
  have hτ1cur : τ1 uctCursorReg = a :=
    (hτ1frame uctCursorReg (by decide)).trans ((hτ0frame uctCursorReg (by decide)).trans hc)
  have hτ1done : τ1 uctDoneReg = 0 := (hτ1frame uctDoneReg (by decide)).trans
    (by simp [τ0, eval_assign, Expr.eval])
  have hτ1bits : BitsFrom τ1 a (encodeList encodeLiteral ls ++ tail) := by
    intro i hi
    rw [hτ1frame (a + i) (by simp [uctLengthReg]; omega),
      hτ0frame (a + i) (by simp [uctDoneReg]; omega)]
    exact hbits i hi
  obtain ⟨hncur, hnlen, hndone, hnframe⟩ :=
    decodeNatProgram_encodeList_length_append encodeLiteral uctCursorReg uctLengthReg
      uctDoneReg bound a 0 ls tail τ1 (by decide) (by decide) (by decide) hbound
      (by simp [uctCursorReg]; omega) (by simp [uctLengthReg]; omega)
      (by simp [uctDoneReg]; omega) hτ1cur hτ1len hτ1done hτ1bits
  set τ2 := (decodeNatProgram uctCursorReg uctLengthReg uctDoneReg bound).eval τ1 with hτ2
  set τ3 := (Program.assign uctDoneReg (.const 0)).eval τ2 with hτ3
  set τ4 := (Program.assign uctRemainingReg (.reg uctLengthReg)).eval τ3 with hτ4
  have hτ3frame : ∀ r, r ≠ uctDoneReg → τ3 r = τ2 r := by
    intro r hr
    simp [τ3, eval_assign, Expr.eval, writeReg_diff _ uctDoneReg _ r hr]
  have hτ4frame : ∀ r, r ≠ uctRemainingReg → τ4 r = τ3 r := by
    intro r hr
    simp [τ4, eval_assign, Expr.eval, writeReg_diff _ uctRemainingReg _ r hr]
  have hframeLow : ∀ q, 12 ≤ q → τ2 q = τ q := by
    intro q hq
    rw [hnframe q (by simp [uctCursorReg]; omega) (by simp [uctLengthReg]; omega)
      (by simp [uctDoneReg]; omega), hτ1frame q (by simp [uctLengthReg]; omega),
      hτ0frame q (by simp [uctDoneReg]; omega)]
  have hτ3len : τ3 uctLengthReg = ls.length := by
    rw [hτ3frame _ (by decide)]
    simpa using hnlen
  have hτ3done : τ3 uctDoneReg = 0 := by
    simp only [τ3, eval_assign, Expr.eval, writeReg_same]
  have hτ4pol : τ4 uctPolReg ≤ 1 := by
    rw [hτ4frame _ (by decide), hτ3frame _ (by decide),
      hnframe uctPolReg (by decide) (by decide) (by decide),
      hτ1frame _ (by decide), hτ0frame _ (by decide)]
    exact hpol
  have hτ4var : τ4 uctVarReg ≤ bound := by
    rw [hτ4frame _ (by decide), hτ3frame _ (by decide),
      hnframe uctVarReg (by decide) (by decide) (by decide),
      hτ1frame _ (by decide), hτ0frame _ (by decide)]
    exact hvar
  have hτ4done : τ4 uctDoneReg = 0 := (hτ4frame uctDoneReg (by decide)).trans hτ3done
  have hτ4len : τ4 uctLengthReg = ls.length := by
    rw [hτ4frame _ (by decide)]
    exact hτ3len
  have hτ4rem : τ4 uctRemainingReg = ls.length := by
    simp only [τ4, eval_assign, Expr.eval, writeReg_same, hτ3len]
  have hτ4cur : τ4 uctCursorReg = a + ls.length + 1 := by
    rw [hτ4frame _ (by decide), hτ3frame _ (by decide)]
    exact hncur
  have hτ4max : τ4 uctMaxReg = m := by
    rw [hτ4frame _ (by decide), hτ3frame _ (by decide),
      hnframe uctMaxReg (by decide) (by decide) (by decide),
      hτ1frame _ (by decide), hτ0frame _ (by decide)]
    exact hmax
  have hτ4bits : BitsFrom τ4 (a + ls.length + 1)
      ((ls.map encodeLiteral).flatten ++ tail) := by
    intro i hi
    have hq : 12 ≤ a + ls.length + 1 + i := by omega
    have haddr : a + ls.length + 1 + i = a + (encodeNat ls.length).length + i := by
      rw [encodeNat_length]
      omega
    rw [hτ4frame (a + ls.length + 1 + i) (by simp [uctRemainingReg]; omega),
      hτ3frame (a + ls.length + 1 + i) (by simp [uctDoneReg]; omega),
      hframeLow (a + ls.length + 1 + i) hq, haddr]
    exact htail i hi
  have hpre : (decodeClauseWithLengthPrefix uctCursorReg uctDoneReg uctRemainingReg
      uctLengthReg bound).eval τ = τ4 := by
    unfold decodeClauseWithLengthPrefix
    simp only [eval_seq, ← hτ0, ← hτ1, ← hτ2, ← hτ3, ← hτ4]
  exact ⟨τ4, hpre.symm, hτ4pol, hτ4var, hτ4done, hτ4len, hτ4rem, hτ4cur, hτ4max, hτ4bits⟩

/-- Loop phase of the dynamic clause step: the literal scanner loop started after the length
    prefix keeps `pol`, `var`, `done` bounded and leaves `length` untouched. -/
lemma decodeCNFStepDynamic_low_regs_loop
    (bound a m : ℕ) (ls : List Literal) (tail : Bits) (τ4 : Store)
    (ha : 12 ≤ a)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hpol : τ4 uctPolReg ≤ 1) (hvar : τ4 uctVarReg ≤ bound) (hdone : τ4 uctDoneReg = 0)
    (hlen : τ4 uctLengthReg = ls.length) (hrem : τ4 uctRemainingReg = ls.length)
    (hcur : τ4 uctCursorReg = a + ls.length + 1) (hmax : τ4 uctMaxReg = m)
    (hbits : BitsFrom τ4 (a + ls.length + 1) ((ls.map encodeLiteral).flatten ++ tail)) :
    ∃ τ5, τ5 = loopEval (decodeClauseStep uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctMaxReg bound) ls.length τ4 ∧
      τ5 uctPolReg ≤ 1 ∧ τ5 uctVarReg ≤ bound ∧ τ5 uctDoneReg ≤ 1 ∧
      τ5 uctLengthReg = ls.length := by
  have hbelow4 : uctCursorReg < a + ls.length + 1 ∧ uctPolReg < a + ls.length + 1 ∧
      uctVarReg < a + ls.length + 1 ∧ uctDoneReg < a + ls.length + 1 ∧
      uctRemainingReg < a + ls.length + 1 ∧ uctMaxReg < a + ls.length + 1 := by
    simp [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg, uctMaxReg]
    omega
  have hloop := decodeClauseStep_low_regs uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctRemainingReg uctMaxReg bound (a + ls.length + 1) m ls tail τ4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hbelow4 (by rw [hrem])
    hcur hmax hvarbound hpol hvar (by rw [hdone]; omega) hbits
  have hloopFrame := decode_clause_loop_eval uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctRemainingReg uctMaxReg bound (a + ls.length + 1) m ls tail τ4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hbelow4 (by rw [hrem])
    hcur hmax hvarbound hbits
  refine ⟨_, rfl, hloop.1, hloop.2.1, hloop.2.2, ?_⟩
  exact (hloopFrame.2.2.2 uctLengthReg (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hlen

/-- One clause step of the dynamic CNF scanner keeps `pol` Boolean, `var`
    within the bound, `done` Boolean, and `length` within the bound. -/
lemma decodeCNFStepDynamic_low_regs
    (bound a m : ℕ) (ls : List Literal) (tail : Bits) (τ : Store)
    (ha : 12 ≤ a)
    (hc : τ uctCursorReg = a) (hmax : τ uctMaxReg = m)
    (hbound : ls.length + 1 ≤ bound)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hpol : τ uctPolReg ≤ 1) (hvar : τ uctVarReg ≤ bound)
    (hbits : BitsFrom τ a (encodeList encodeLiteral ls ++ tail)) :
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctPolReg ≤ 1 ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctVarReg ≤ bound ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctDoneReg ≤ 1 ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctLengthReg ≤ bound := by
  obtain ⟨τ4, hτ4, hpol4, hvar4, hdone4, hlen4, hrem4, hcur4, hmax4, hbits4⟩ :=
    decodeCNFStepDynamic_low_regs_prefix bound a m ls tail τ ha hc hmax hbound hpol hvar hbits
  obtain ⟨τ5, hτ5, hpol5, hvar5, hdone5, hlen5⟩ :=
    decodeCNFStepDynamic_low_regs_loop bound a m ls tail τ4 ha hvarbound hpol4 hvar4 hdone4
      hlen4 hrem4 hcur4 hmax4 hbits4
  have hprogEq : (decodeClauseWithLengthProgramDynamic uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctMaxReg uctLengthReg bound).eval τ = τ5 := by
    rw [hτ5, hτ4]
    unfold decodeClauseWithLengthProgramDynamic
    rw [eval_seq, eval_forN]
    simp only [Expr.eval, ← hτ4, hrem4]
  have hstepEq : (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
      uctTmpReg bound).eval τ =
      (Program.assign uctOuterReg (.sub (.reg uctOuterReg) (.const 1))).eval
        ((clauseStatsProgram uctLengthReg uctFreshReg uctCountReg uctTmpReg).eval τ5) := by
    unfold decodeCNFStepDynamic decodeCNFClauseStepWithStatsDynamic
    rw [eval_seq, eval_seq, hprogEq]
  rw [hstepEq]
  have hstatFrame (r : ℕ) (hrf : r ≠ uctFreshReg) (hrn : r ≠ uctCountReg) :
      (clauseStatsProgram uctLengthReg uctFreshReg uctCountReg uctTmpReg).eval τ5 r =
        τ5 r :=
    clauseStatsProgram_frame uctLengthReg uctFreshReg uctCountReg uctTmpReg τ5 r hrf hrn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ uctOuterReg _ uctPolReg (by decide),
      hstatFrame uctPolReg (by decide) (by decide)]
    exact hpol5
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ uctOuterReg _ uctVarReg (by decide),
      hstatFrame uctVarReg (by decide) (by decide)]
    exact hvar5
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ uctOuterReg _ uctDoneReg (by decide),
      hstatFrame uctDoneReg (by decide) (by decide)]
    exact hdone5
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ uctOuterReg _ uctLengthReg (by decide),
      hstatFrame uctLengthReg (by decide) (by decide)]
    omega

/-- The CNF scanner loop keeps `pol` Boolean, `var` within the bound, `done`
    Boolean, and `length` within the bound along the whole clause list. -/
lemma decodeCNFStepAtSeen_loop_low_regs
    (bound : ℕ) (clauses : List (List Literal)) (rest : Bits)
    (addr m base c s : ℕ) (σ : Store)
    (houter : σ uctOuterReg = clauses.length) (hc : σ uctCursorReg = addr)
    (hmax : σ uctMaxReg = m) (hbase : σ uctFreshReg = base)
    (hcount : σ uctCountReg = c) (hseen : σ uctSeenReg = s)
    (hrem : σ uctRemainingReg = 0) (hb : σ uctBoundReg = bound)
    (hbelow : 25 ≤ addr)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ bound ∧ ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hpol : σ uctPolReg ≤ 1) (hvar : σ uctVarReg ≤ bound) (hdone : σ uctDoneReg ≤ 1)
    (hlen : σ uctLengthReg ≤ bound)
    (hbits : BitsFrom σ addr
      ((clauses.map (encodeList encodeLiteral)).flatten ++ rest)) :
    (loopEval (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg) clauses.length σ) uctPolReg ≤ 1 ∧
    (loopEval (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg) clauses.length σ) uctVarReg ≤ bound ∧
    (loopEval (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg) clauses.length σ) uctDoneReg ≤ 1 ∧
    (loopEval (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg) clauses.length σ) uctLengthReg ≤ bound := by
  induction clauses generalizing addr m base c s σ with
  | nil =>
      simp only [List.length_nil, NPComplete.BoundedWhile.loopEval_zero]
      exact ⟨hpol, hvar, hdone, hlen⟩
  | cons ls restClauses ih =>
      have hshape :
          ((ls :: restClauses).map (encodeList encodeLiteral)).flatten ++ rest =
            encodeList encodeLiteral ls ++
              ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
        simp
      rw [hshape] at hbits
      obtain ⟨hheadBits, htailBits0⟩ := bitsFrom_append σ addr (encodeList encodeLiteral ls)
        ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) hbits
      have houter' : σ uctOuterReg = restClauses.length + 1 := by simpa using houter
      have hheadBound := hbounds ls (by simp)
      have hstep := decodeCNFStepAtSeen_uct_eval bound addr m base c
        (restClauses.length) s ls
        ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) σ hbelow houter'
        hc hmax hbase hcount hseen hb hheadBound.1 hheadBound.2 hbits
      set σ1 := (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg).eval σ with hσ1
      have hstepLow := decodeCNFStepDynamic_low_regs bound addr m ls
        ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) σ (by omega)
        hc hmax hheadBound.1 hheadBound.2 hpol hvar hbits
      have hexcept (r : ℕ) (hr : r ≠ uctSeenReg) : σ1 r =
          (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
            uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
            bound).eval σ r :=
        decodeCNFStepAtSeen_uct_except_seen bound σ hb r hr
      have hlow : σ1 uctPolReg ≤ 1 ∧ σ1 uctVarReg ≤ bound ∧ σ1 uctDoneReg ≤ 1 ∧
          σ1 uctLengthReg ≤ bound :=
        ⟨hexcept uctPolReg (by decide) ▸ hstepLow.1,
          hexcept uctVarReg (by decide) ▸ hstepLow.2.1,
          hexcept uctDoneReg (by decide) ▸ hstepLow.2.2.1,
          hexcept uctLengthReg (by decide) ▸ hstepLow.2.2.2⟩
      have htailBits : BitsFrom σ1 (addr + (encodeList encodeLiteral ls).length)
          ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
        intro i hi
        have hfr := hstep.2.2.2.2.2.2.2.2.2 (addr + (encodeList encodeLiteral ls).length + i)
          (by simp [uctCursorReg]; omega) (by simp [uctPolReg]; omega)
          (by simp [uctVarReg]; omega) (by simp [uctDoneReg]; omega)
          (by simp [uctOuterReg]; omega) (by simp [uctRemainingReg]; omega)
          (by simp [uctMaxReg]; omega) (by simp [uctLengthReg]; omega)
          (by simp [uctFreshReg]; omega) (by simp [uctCountReg]; omega)
          (by simp [uctTmpReg]; omega) (by simp [uctSeenReg]; omega)
        calc
          σ1 (addr + (encodeList encodeLiteral ls).length + i) =
              σ (addr + (encodeList encodeLiteral ls).length + i) := hfr
          _ = if ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest)[i]
                then 1 else 0 := htailBits0 i hi
      have hrest := ih (addr + (encodeList encodeLiteral ls).length)
        (max m (literalVarMax ls)) (base + clauseFreshIncByLength ls.length)
        (c + clauseThreeCountByLength ls.length)
        (if ls.length = 0 then s else 1) σ1
        (by rw [hσ1]; exact hstep.2.1)
        (by rw [hσ1]; exact hstep.1)
        (by rw [hσ1]; exact hstep.2.2.2.1)
        (by rw [hσ1]; exact hstep.2.2.2.2.2.1)
        (by rw [hσ1]; exact hstep.2.2.2.2.2.2.1)
        (by rw [hσ1]; exact hstep.2.2.2.2.2.2.2.1)
        (by rw [hσ1]; exact hstep.2.2.1)
        (by rw [hσ1]; exact hstep.2.2.2.2.2.2.2.2.1)
        (by omega)
        (fun d hd => hbounds d (by simp [hd]))
        hlow.1 hlow.2.1 hlow.2.2.1 hlow.2.2.2 htailBits
      rw [List.length_cons, loopEval_succ]
      exact hrest

lemma uniformPostDecodeStatsProg_frame (σ : Store) {r : ℕ}
    (h1 : r ≠ uctTmpReg) (h2 : r ≠ uctMaxReg) (h3 : r ≠ uctFreshReg) :
    uniformPostDecodeStatsProg.eval σ r = σ r :=
  (by decide +kernel : uniformPostDecodeStatsProg.Avoids
    (fun x => x ≠ uctTmpReg ∧ x ≠ uctMaxReg ∧ x ≠ uctFreshReg)).eval_frame σ ⟨h1, h2, h3⟩

end NPComplete.CookLevin

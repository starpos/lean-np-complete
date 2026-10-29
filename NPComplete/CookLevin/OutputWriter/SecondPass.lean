module

public import NPComplete.CookLevin.OutputWriter.Basic

/-!
# Header and second-pass writes

The output pass must prepend variable and clause counts without discarding the
parser state that supplies them. These lemmas provide the header append and
rewind/startup contracts so later clause emitters can continue under the same
prefix invariant.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd writeReg writeReg_same writeReg_diff
    loopEval loopCost loopCost_le_of_body_le cost_seq cost_forN cost_assignInd eval_forN)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

/-! ## Second-pass header and emission state -/

/-- A frame lemma for a natural append.  The parser and scanner controls are
below the output window, so a later append can still read them. -/
lemma writerAppendNatProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits) (e : Expr) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + e.eval σ + 1 < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendNatProg curJ tmpJ e).eval σ r = σ r := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hnat := emitNatProg_eval_state curJ tmpJ M cur e σ hcurJ
    (by omega : 1 ≤ tmpJ) (by omega : curJ ≠ tmpJ) hroot hcur
    (by dsimp [cur]; omega) (by dsimp [cur]; omega)
  change (emitNatProg curJ tmpJ e).eval σ r = σ r
  exact hnat.2.2.1 r (by dsimp [cur]; omega) (by dsimp [cur]; omega)
    (Or.inl (by dsimp [cur]; omega))

/-- Append the two header fields used by the second tableau pass. -/
def writerAppendHeaderProg (curJ tmpJ numVarsReg clauseCountReg : ℕ) : Program :=
  .seq (writerAppendNatProg curJ tmpJ (.reg numVarsReg))
    (writerAppendNatProg curJ tmpJ (.reg clauseCountReg))

lemma writerAppendHeaderProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (numVarsReg clauseCountReg numVars clauseCount : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hnum : σ numVarsReg = numVars) (hcount : σ clauseCountReg = clauseCount)
    (hcountLow : clauseCountReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + numVars + clauseCount + 2 < M + curJ) :
    WriterState ((writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ)
      M curJ start (pref ++ encodeNat numVars ++ encodeNat clauseCount) := by
  let σ1 := (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ
  have hnumEval : (.reg numVarsReg : Expr).eval σ = numVars := by
    simpa [Expr.eval] using hnum
  have hroom1 : start + pref.length + (.reg numVarsReg : Expr).eval σ + 1 < M + curJ := by
    rw [hnumEval]
    omega
  have hs1 : WriterState σ1 M curJ start (pref ++ encodeNat numVars) := by
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    simpa [hnumEval] using
      (writerAppendNatProg_eval M curJ tmpJ start pref (.reg numVarsReg) σ
        hcurJ htmpJ hs hroom1)
  have hcount1 : σ1 clauseCountReg = clauseCount := by
    have hframe := writerAppendNatProg_frame M curJ tmpJ start pref
      (.reg numVarsReg) σ hcurJ htmpJ hs hroom1 hcountLow
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    exact hframe.trans hcount
  have hcountEval : (.reg clauseCountReg : Expr).eval σ1 = clauseCount := by
    simpa [Expr.eval] using hcount1
  have hroom2 : start + (pref ++ encodeNat numVars).length +
      (.reg clauseCountReg : Expr).eval σ1 + 1 < M + curJ := by
    rw [hcountEval]
    simp only [List.length_append, encodeNat_length]
    omega
  have hs2 := writerAppendNatProg_eval M curJ tmpJ start
    (pref ++ encodeNat numVars) (.reg clauseCountReg) σ1
    hcurJ htmpJ hs1 hroom2
  rw [show (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ =
      (writerAppendNatProg curJ tmpJ (.reg clauseCountReg)).eval σ1 by
        simp [writerAppendHeaderProg, σ1, eval_seq]]
  simpa [hcountEval, List.append_assoc] using hs2

lemma writerAppendHeaderProg_frame
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (numVarsReg clauseCountReg numVars clauseCount : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hnum : σ numVarsReg = numVars) (hcount : σ clauseCountReg = clauseCount)
    (hcountLow : clauseCountReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + numVars + clauseCount + 2 < M + curJ)
    {r : ℕ} (hr : r < start) :
    (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ r = σ r := by
  let σ1 := (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ
  have hroom1 : start + pref.length + (.reg numVarsReg : Expr).eval σ + 1 < M + curJ := by
    simpa [Expr.eval, hnum] using (show start + pref.length + numVars + 1 < M + curJ by omega)
  have hs1 : WriterState σ1 M curJ start (pref ++ encodeNat numVars) := by
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    simpa [Expr.eval, hnum] using
      (writerAppendNatProg_eval M curJ tmpJ start pref (.reg numVarsReg) σ
        hcurJ htmpJ hs hroom1)
  have hroom2 : start + (pref ++ encodeNat numVars).length +
      (.reg clauseCountReg : Expr).eval σ1 + 1 < M + curJ := by
    have hcount1 := writerAppendNatProg_frame M curJ tmpJ start pref
      (.reg numVarsReg) σ hcurJ htmpJ hs hroom1 hcountLow
    have hcountEval : (.reg clauseCountReg : Expr).eval σ1 = clauseCount := by
      rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
      simpa [Expr.eval] using hcount1.trans hcount
    rw [hcountEval]
    simp only [List.length_append, encodeNat_length]
    omega
  have hframe1 := writerAppendNatProg_frame M curJ tmpJ start pref
    (.reg numVarsReg) σ hcurJ htmpJ hs hroom1 hr
  have hframe2 := writerAppendNatProg_frame M curJ tmpJ start
    (pref ++ encodeNat numVars) (.reg clauseCountReg) σ1 hcurJ htmpJ hs1 hroom2 hr
  rw [show (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ =
      (writerAppendNatProg curJ tmpJ (.reg clauseCountReg)).eval σ1 by
        simp [writerAppendHeaderProg, σ1, eval_seq]]
  exact hframe2.trans hframe1

/-! The header writer also preserves cells above the dynamic scratch region.
    This direction is needed when the input tape is placed strictly above
    `M + tmpJ`, while the output window starts at `start`. -/
lemma writerAppendHeaderProg_frame_high
    (M curJ tmpJ start : ℕ) (pref : Bits)
    (numVarsReg clauseCountReg numVars clauseCount : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hnum : σ numVarsReg = numVars) (hcount : σ clauseCountReg = clauseCount)
    (hcountLow : clauseCountReg < start)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + numVars + clauseCount + 2 < M + curJ)
    {r : ℕ} (hr : M + tmpJ < r) :
    (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ r = σ r := by
  let σ1 := (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ
  have hnumEval : (.reg numVarsReg : Expr).eval σ = numVars := by
    simpa [Expr.eval] using hnum
  have hs1 : WriterState σ1 M curJ start (pref ++ encodeNat numVars) := by
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    have hroom1 : start + pref.length + numVars + 1 < M + curJ := by omega
    simpa [hnumEval] using
      (writerAppendNatProg_eval M curJ tmpJ start pref (.reg numVarsReg) σ
        hcurJ htmpJ hs (by simpa [hnumEval] using hroom1))
  have hcount1 : σ1 clauseCountReg = clauseCount := by
    have hframe := writerAppendNatProg_frame M curJ tmpJ start pref
      (.reg numVarsReg) σ hcurJ htmpJ hs (by omega) hcountLow
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    exact hframe.trans hcount
  have hcursor1 : σ1 (M + curJ) = start + (pref ++ encodeNat numVars).length := by
    simpa [σ1, hnumEval] using hs1.cursor
  have hroot1 : σ1 0 = M := hs1.root
  have hframe1 : σ1 r = σ r := by
    have hstate := emitNatProg_eval_state curJ tmpJ M (start + pref.length)
      (.reg numVarsReg) σ hcurJ (by omega) (by omega) hs.root hs.cursor
      (by omega) (by omega)
    rw [show σ1 = (writerAppendNatProg curJ tmpJ (.reg numVarsReg)).eval σ from rfl]
    exact hstate.2.2.1 r (by omega) (by omega) (by omega)
  have hroom2 : start + (pref ++ encodeNat numVars).length + clauseCount + 1 < M + curJ := by
    simp only [List.length_append, encodeNat_length]
    omega
  have hcur2 : 1 ≤ start + (pref ++ encodeNat numVars).length := by
    have := hs1.start_pos
    omega
  have hcountEval2 : (.reg clauseCountReg : Expr).eval σ1 = clauseCount := by
    simpa [Expr.eval] using hcount1
  have hsep2 : start + (pref ++ encodeNat numVars).length +
      (.reg clauseCountReg : Expr).eval σ1 < M + curJ := by
    rw [hcountEval2]
    omega
  have hstate2 := emitNatProg_eval_state curJ tmpJ M
    (start + (pref ++ encodeNat numVars).length)
    (.reg clauseCountReg) σ1 hcurJ (by omega) (by omega) hroot1 hcursor1
    hcur2 hsep2
  have hframe2 :
      (writerAppendNatProg curJ tmpJ (.reg clauseCountReg)).eval σ1 r = σ1 r := by
    apply hstate2.2.2.1 r
    · omega
    · omega
    · rw [hcountEval2]
      simp only [List.length_append, encodeNat_length]
      omega
  rw [show (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg).eval σ r =
      (writerAppendNatProg curJ tmpJ (.reg clauseCountReg)).eval σ1 r by
        simp [writerAppendHeaderProg, σ1, eval_seq]]
  exact hframe2.trans hframe1


/-- State of the writer, input cursor, remaining clauses, and fresh counter. -/
structure CNFEmissionState (σ : Store) (M curJ start : ℕ) (pref : Bits)
    (inputCursorReg remainingReg freshReg inputBase remaining fresh : ℕ) : Prop where
  writer : WriterState σ M curJ start pref
  input_cursor : σ inputCursorReg = inputBase
  clauses_remaining : σ remainingReg = remaining
  fresh_counter : σ freshReg = fresh

def secondPassRewindProgram
    (cursorReg inputBaseReg outerReg doneReg bound : ℕ) : Program :=
  .seq (.assign cursorReg (.reg inputBaseReg))
    (.seq (.assign doneReg (.const 0))
      (.seq (.assign outerReg (.const 0))
        (decodeNatProgram cursorReg outerReg doneReg bound)))

lemma secondPassRewindProgram_eval
    {α : Type} (enc : α → Bits)
    (cursorReg inputBaseReg outerReg doneReg bound addr : ℕ)
    (clauses : List α) (rest : Bits) (σ : Store)
    (hco : cursorReg ≠ outerReg)
    (hcd : cursorReg ≠ doneReg) (hod : outerReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ inputBaseReg < addr ∧
      outerReg < addr ∧ doneReg < addr)
    (hbase : σ inputBaseReg = addr)
    (hbound : clauses.length + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList enc clauses ++ rest)) :
    let σ' := (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ
    σ' cursorReg = addr + clauses.length + 1 ∧
    σ' outerReg = clauses.length ∧ σ' doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ outerReg → r ≠ doneReg → σ' r = σ r) := by
  let σ0 := (Program.assign cursorReg (.reg inputBaseReg)).eval σ
  have hσ0cur : σ0 cursorReg = addr := by
    rw [show σ0 = (Program.assign cursorReg (.reg inputBaseReg)).eval σ from rfl]
    simp [eval_assign, Expr.eval, hbase, writeReg_same]
  have hσ0frame : ∀ r, r ≠ cursorReg → σ0 r = σ r := by
    intro r hr
    rw [show σ0 = (Program.assign cursorReg (.reg inputBaseReg)).eval σ from rfl]
    simp [eval_assign, Expr.eval, writeReg_diff _ cursorReg _ r hr]
  let σ1 := (Program.assign doneReg (.const 0)).eval σ0
  have hσ1done : σ1 doneReg = 0 := by
    rw [show σ1 = (Program.assign doneReg (.const 0)).eval σ0 from rfl]
    simp [eval_assign, Expr.eval, writeReg_same]
  have hσ1frame : ∀ r, r ≠ doneReg → σ1 r = σ0 r := by
    intro r hr
    rw [show σ1 = (Program.assign doneReg (.const 0)).eval σ0 from rfl]
    simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  let σ2 := (Program.assign outerReg (.const 0)).eval σ1
  have hσ2outer : σ2 outerReg = 0 := by
    rw [show σ2 = (Program.assign outerReg (.const 0)).eval σ1 from rfl]
    simp [eval_assign, Expr.eval, writeReg_same]
  have hσ2frame : ∀ r, r ≠ outerReg → σ2 r = σ1 r := by
    intro r hr
    rw [show σ2 = (Program.assign outerReg (.const 0)).eval σ1 from rfl]
    simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ r hr]
  have hσ2cur : σ2 cursorReg = addr := by
    exact (hσ2frame cursorReg hco).trans ((hσ1frame cursorReg hcd).trans hσ0cur)
  have hσ2done : σ2 doneReg = 0 := by
    exact (hσ2frame doneReg (Ne.symm hod)).trans hσ1done
  have hσ2bits : BitsFrom σ2 addr (encodeList enc clauses ++ rest) := by
    intro i hi
    calc
      σ2 (addr + i) = σ1 (addr + i) := hσ2frame _ (by omega)
      _ = σ0 (addr + i) := hσ1frame _ (by omega)
      _ = σ (addr + i) := hσ0frame _ (by omega)
      _ = if (encodeList enc clauses ++ rest)[i] then 1 else 0 := hbits i hi
  obtain ⟨hcur, houter, hdone, hframe⟩ :=
    decodeNatProgram_encodeList_length_append enc cursorReg outerReg doneReg bound
      addr 0 clauses rest σ2 hco hcd hod hbound hbelow.1 hbelow.2.2.1 hbelow.2.2.2
      hσ2cur hσ2outer hσ2done hσ2bits
  have hrew : (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ =
      (decodeNatProgram cursorReg outerReg doneReg bound).eval σ2 := by
    simp [secondPassRewindProgram, σ0, σ1, σ2, eval_seq]
  have hcur' : (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ cursorReg =
      addr + clauses.length + 1 := by
    rw [hrew]
    exact hcur
  have houter' : (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ outerReg =
      clauses.length := by
    rw [hrew]
    simpa using houter
  have hdone' : (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ doneReg = 1 := by
    rw [hrew]
    exact hdone
  change (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ cursorReg =
      addr + clauses.length + 1 ∧
    (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ outerReg =
      clauses.length ∧
    (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ outerReg → r ≠ doneReg →
      (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound).eval σ r = σ r)
  refine ⟨hcur', houter', hdone', ?_⟩
  · intro r h1 h2 h3
    have h0 := hframe r h1 h2 h3
    have h2' := hσ2frame r h2
    have h1' := hσ1frame r h3
    have h0' := hσ0frame r h1
    rw [hrew]
    exact h0.trans (h2'.trans (h1'.trans h0'))

def secondPassStartupProgram
    (cursorReg inputBaseReg outerReg doneReg bound curJ tmpJ start
      numVarsReg clauseCountReg : ℕ) : Program :=
  .seq (secondPassRewindProgram cursorReg inputBaseReg outerReg doneReg bound)
    (.seq (ctlAssign curJ (.const start))
      (writerAppendHeaderProg curJ tmpJ numVarsReg clauseCountReg))

end NPComplete.CookLevin

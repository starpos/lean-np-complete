module

public import NPComplete.CookLevin.Verifier.ClauseEval
public import NPComplete.CookLevin.NatParser.LengthPrefix
public import NPComplete.CookLevin.ToThreeCNF.Encode

/-!
The CNF-level evaluator scans one length-prefixed clause at a time
(`decodeClauseWithLengthPrefix`, reused from `NatParser/LengthPrefix.lean`),
then folds its literals against the certificate (`decodeClauseEvalStep`,
`ClauseEval.lean`).  This module is the bridge between the two: it tracks the
cursor/bit-region shift the length prefix introduces, so the clause-level
literal loop can start from the right offset.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal encodeLiteral)

/-- Companion of `decodeClauseWithLengthPrefix_remaining_eval`: the prefix's
    effect on `cursorReg`, needed to chain into the eval loop (which reads
    bits starting right after the length-encoded prefix, not at `addr`). -/
lemma decodeClauseWithLengthPrefix_full_eval
    (cursorReg doneReg remainingReg lengthReg bound addr : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hlc : lengthReg ≠ cursorReg)
    (hld : lengthReg ≠ doneReg) (hrc' : remainingReg ≠ cursorReg)
    (hbelow : cursorReg < addr ∧ doneReg < addr ∧ lengthReg < addr ∧ remainingReg < addr)
    (hc : σ cursorReg = addr)
    (hbound : xs.length + 1 ≤ bound)
    (hbits : BitsFrom σ addr (encodeList encodeLiteral xs ++ rest)) :
    (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
      cursorReg = addr + xs.length + 1 ∧
    BitsFrom ((decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg
        bound).eval σ) (addr + xs.length + 1) ((xs.map encodeLiteral).flatten ++ rest) ∧
    (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
      remainingReg = xs.length ∧
    (∀ r, r ≠ cursorReg → r ≠ doneReg → r ≠ remainingReg → r ≠ lengthReg →
      (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ r = σ r) := by
  unfold decodeClauseWithLengthPrefix
  rw [eval_seq, eval_seq, eval_seq, eval_seq]
  have hshape : encodeList encodeLiteral xs ++ rest =
      encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  have hbitsOrig := hbits
  rw [hshape] at hbits
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0
  have hσ0done : σ0 doneReg = 0 := by rw [hσ0]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσ0frame : ∀ r, r ≠ doneReg → σ0 r = σ r := by
    intro r hr; rw [hσ0]; simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ r hr]
  have hbits0 : BitsFrom σ0 addr
      (encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest)) := by
    intro i hi; rw [hσ0frame _ (by omega)]; exact hbits i hi
  set σlen := (Program.assign lengthReg (.const 0)).eval σ0 with hσlen
  have hlen0 : σlen lengthReg = 0 := by rw [hσlen]; simp [eval_assign, Expr.eval, writeReg_same]
  have hσlenFrame : ∀ r, r ≠ lengthReg → σlen r = σ0 r := by
    intro r hr; rw [hσlen]; simp [eval_assign, Expr.eval, writeReg_diff _ lengthReg _ r hr]
  have hσlendone : σlen doneReg = 0 := (hσlenFrame doneReg (Ne.symm hld)).trans hσ0done
  have hbitsLen : BitsFrom σlen addr
      (encodeNat xs.length ++ ((xs.map encodeLiteral).flatten ++ rest)) := by
    intro i hi; rw [hσlenFrame _ (by omega)]; exact hbits0 i hi
  have hclen : σlen cursorReg = addr :=
    (hσlenFrame cursorReg (Ne.symm hlc)).trans ((hσ0frame cursorReg hcd).trans hc)
  obtain ⟨hcurE, hcnt, hdoneE, hframeE⟩ :=
    decodeNatProgram_encodeNat_append cursorReg lengthReg doneReg xs.length bound addr 0
      ((xs.map encodeLiteral).flatten ++ rest) σlen (Ne.symm hlc) hcd hld hbound
      hbelow.1 hbelow.2.2.1 hbelow.2.1 hclen hlen0 hσlendone hbitsLen
  set σ1 := (decodeNatProgram cursorReg lengthReg doneReg bound).eval σlen with hσ1
  have hbits1 : BitsFrom σ1 (addr + xs.length + 1) ((xs.map encodeLiteral).flatten ++ rest) := by
    obtain ⟨_, htailBits⟩ := bitsFrom_append σlen addr (encodeNat xs.length)
      ((xs.map encodeLiteral).flatten ++ rest) hbitsLen
    intro i hi
    have hfr := hframeE (addr + xs.length + 1 + i) (by omega) (by omega) (by omega)
    rw [hfr]
    have heq : addr + xs.length + 1 + i = addr + (encodeNat xs.length).length + i := by
      rw [encodeNat_length]; omega
    rw [heq]
    exact htailBits i hi
  have hlen1 : σ1 lengthReg = xs.length := by simpa using hcnt
  set σ2 := (Program.assign doneReg (.const 0)).eval σ1 with hσ2
  have h2cur : σ2 cursorReg = σ1 cursorReg := by
    rw [hσ2]; simp only [eval_assign, Expr.eval]; exact writeReg_diff _ doneReg _ cursorReg hcd
  have h2len : σ2 lengthReg = σ1 lengthReg := by
    rw [hσ2]; simp only [eval_assign, Expr.eval]; exact writeReg_diff _ doneReg _ lengthReg hld
  have h2bits : BitsFrom σ2 (addr + xs.length + 1) ((xs.map encodeLiteral).flatten ++ rest) := by
    intro i hi
    have hne : addr + xs.length + 1 + i ≠ doneReg := by have := hbelow.2.1; omega
    rw [hσ2]; simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ (addr + xs.length + 1 + i) hne]
    exact hbits1 i hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Program.assign remainingReg (.reg lengthReg)).eval σ2 cursorReg = addr + xs.length + 1
    rw [eval_assign, Expr.eval, writeReg_diff _ remainingReg _ cursorReg (Ne.symm hrc'),
      h2cur, hcurE]
  · show BitsFrom ((Program.assign remainingReg (.reg lengthReg)).eval σ2)
      (addr + xs.length + 1) ((xs.map encodeLiteral).flatten ++ rest)
    intro i hi
    have hne : addr + xs.length + 1 + i ≠ remainingReg := by have := hbelow.2.2.2; omega
    rw [eval_assign, Expr.eval, writeReg_diff _ remainingReg _ (addr + xs.length + 1 + i) hne]
    exact h2bits i hi
  · show (Program.assign remainingReg (.reg lengthReg)).eval σ2 remainingReg = xs.length
    rw [eval_assign, Expr.eval, writeReg_same, h2len, hlen1]
  · intro r h1 h2 h3 h4
    show (Program.assign remainingReg (.reg lengthReg)).eval σ2 r = σ r
    rw [eval_assign, Expr.eval, writeReg_diff _ remainingReg _ r h3]
    have hg2 : σ2 r = σ1 r := by
      rw [hσ2]; simp only [eval_assign, Expr.eval]; exact writeReg_diff _ doneReg _ r h2
    have hfr := hframeE r h1 h4 h2
    rw [hg2, hfr]
    have hg0 : σ0 r = σ r := hσ0frame r h2
    have hglen : σlen r = σ0 r := hσlenFrame r h4
    rw [hglen, hg0]

/-- Decode one clause's length prefix and evaluate all its literals against
    the certificate, folding into `satReg` via `decodeClauseEvalStep`'s OR
    accumulator (seeded fresh at `0` since a clause's own accumulator starts
    unsatisfied). -/
def decodeClauseEvalWithLengthProgram
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg bound : ℕ) : Program :=
  .seq (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound)
    <| .seq (.assign satReg (.const 0))
      (.forN (.reg remainingReg)
        (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg bound))

/-- After the length-prefixed clause evaluator runs, the cursor is past the
    clause encoding and the satisfaction register holds its Boolean value. The
    evaluator's control registers and `lengthReg` lie strictly below the certificate base `wBase`,
    which lies strictly below the bit region `addr`. -/
lemma decodeClauseEvalWithLengthProgram_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
      bound addr wBase : ℕ) (c : Clause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)
    (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg) (hwlen : wBaseReg ≠ lengthReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hlenW : lengthReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      lengthReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase)
    (hbound : c.lits.length + 1 ≤ bound) (hvarbound : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeClause c ++ rest))
    (w : List Bool) (hwbits : ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound).eval σ cursorReg = addr + (encodeClause c).length ∧
    (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound).eval σ satReg =
      (if clauseSatBool w c then 1 else 0) ∧
    (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound).eval σ wBaseReg = wBase := by
  unfold decodeClauseEvalWithLengthProgram
  rw [eval_seq, eval_seq]
  have hbitsList : BitsFrom σ addr (encodeList encodeLiteral c.lits ++ rest) := by
    simpa [encodeClause] using hbits
  obtain ⟨hcurP, hbitsP, hremP, hframeP⟩ := decodeClauseWithLengthPrefix_full_eval
    cursorReg doneReg remainingReg lengthReg bound addr c.lits rest σ
    hcd hlc hld hrc
    ⟨hbelow.1, hbelow.2.2.2.1, hbelow.2.2.2.2.2.2.2.2.2, hbelow.2.2.2.2.1⟩
    hc hbound hbitsList
  set σp := (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
    with hσp
  set σs := (Program.assign satReg (.const 0)).eval σp with hσs
  have hssat : σs satReg = 0 := by rw [hσs]; simp [eval_assign, Expr.eval, writeReg_same]
  have hscur : σs cursorReg = σp cursorReg := by
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ cursorReg hsc.symm]
  have hsrem : σs remainingReg = σp remainingReg := by
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ remainingReg hsr.symm]
  have hswbase : σs wBaseReg = wBase := by
    have hpwbase : σp wBaseReg = wBase := (hframeP wBaseReg hwc hwd hwr hwlen).trans hwbase
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ wBaseReg hsw.symm, hpwbase]
  have hswbits : ∀ l ∈ c.lits, σs (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro l hl
    have hne : wBase + l.var ≠ satReg := by have := hbelowW.2.2.2.2.2.1; omega
    have hpb : σp (wBase + l.var) = σ (wBase + l.var) := by
      have hne1 : wBase + l.var ≠ cursorReg := by have := hbelowW.1; omega
      have hne2 : wBase + l.var ≠ doneReg := by have := hbelowW.2.2.2.1; omega
      have hne3 : wBase + l.var ≠ remainingReg := by have := hbelowW.2.2.2.2.1; omega
      have hne4 : wBase + l.var ≠ lengthReg := by omega
      exact hframeP (wBase + l.var) hne1 hne2 hne3 hne4
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ (wBase + l.var) hne, hpb]
    exact hwbits l hl
  have hbitsS : BitsFrom σs (addr + c.lits.length + 1) ((c.lits.map encodeLiteral).flatten ++ rest) := by
    intro i hi
    have hne : addr + c.lits.length + 1 + i ≠ satReg := by have := hbelow.2.2.2.2.2.1; omega
    rw [hσs]; simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ satReg _ (addr + c.lits.length + 1 + i) hne]
    exact hbitsP i hi
  have hbelowAddr' : cursorReg < addr + c.lits.length + 1 ∧ polReg < addr + c.lits.length + 1 ∧
      varReg < addr + c.lits.length + 1 ∧ doneReg < addr + c.lits.length + 1 ∧
      remainingReg < addr + c.lits.length + 1 ∧ satReg < addr + c.lits.length + 1 ∧
      bitReg < addr + c.lits.length + 1 ∧ valReg < addr + c.lits.length + 1 ∧
      wBaseReg < addr + c.lits.length + 1 := by omega
  have hWA' : wBase < addr + c.lits.length + 1 := by omega
  obtain ⟨hcurL, hremL, hsatL, hframeL⟩ := decode_clause_eval_loop_eval
    cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg bound
    (addr + c.lits.length + 1) 0 wBase c.lits rest σs
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl
    hsc hsp hsv hsd hsr hsb hsl hsw hbelowW hbelowAddr' hWA'
    (by rw [hsrem, hremP]) hssat (Or.inl rfl) hswbase hvarbound
    (by rw [hscur, hcurP]) hbitsS w hswbits
  rw [eval_forN, Expr.eval, hsrem, hremP]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcurL]
    unfold encodeClause encodeList
    simp only [List.length_append]
    rw [encodeNat_length]
    ring
  · rw [hsatL]
    unfold clauseSatBool
    simp only [Nat.zero_ne_one, false_or, List.any_eq_true]
  · rw [hframeL wBaseReg hwc hwp hwv hwd hwr hsw.symm hwb hwl, hswbase]

/-- Frame lemma for `decodeClauseEvalWithLengthProgram`: any register outside
    the ten it uses (`cursorReg`, `polReg`, `varReg`, `doneReg`,
    `remainingReg`, `satReg`, `bitReg`, `valReg`, `wBaseReg`, `lengthReg`) is
    untouched.  Needed by the outer CNF loop to carry `wBaseReg`/`cnfReg`
    across clauses. -/
lemma decodeClauseEvalWithLengthProgram_frame
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
      bound addr wBase : ℕ) (c : Clause) (rest : Bits) (σ : Store) (r : ℕ)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)
    (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg) (hwlen : wBaseReg ≠ lengthReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hlenW : lengthReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      lengthReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase)
    (hbound : c.lits.length + 1 ≤ bound) (hvarbound : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeClause c ++ rest))
    (w : List Bool) (hwbits : ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0)
    (hr1 : r ≠ cursorReg) (hr2 : r ≠ polReg) (hr3 : r ≠ varReg) (hr4 : r ≠ doneReg)
    (hr5 : r ≠ remainingReg) (hr6 : r ≠ satReg) (hr7 : r ≠ bitReg) (hr8 : r ≠ valReg)
    (hr10 : r ≠ lengthReg) :
    (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound).eval σ r = σ r := by
  unfold decodeClauseEvalWithLengthProgram
  rw [eval_seq, eval_seq]
  have hbitsList : BitsFrom σ addr (encodeList encodeLiteral c.lits ++ rest) := by
    simpa [encodeClause] using hbits
  obtain ⟨hcurP, hbitsP, hremP, hframeP⟩ := decodeClauseWithLengthPrefix_full_eval
    cursorReg doneReg remainingReg lengthReg bound addr c.lits rest σ
    hcd hlc hld hrc
    ⟨hbelow.1, hbelow.2.2.2.1, hbelow.2.2.2.2.2.2.2.2.2, hbelow.2.2.2.2.1⟩
    hc hbound hbitsList
  set σp := (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
    with hσp
  have hpr : σp r = σ r := hframeP r hr1 hr4 hr5 hr10
  set σs := (Program.assign satReg (.const 0)).eval σp with hσs
  have hsr' : σs r = σp r := by
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ r hr6]
  have hssat : σs satReg = 0 := by rw [hσs]; simp [eval_assign, Expr.eval, writeReg_same]
  have hscur : σs cursorReg = σp cursorReg := by
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ cursorReg hsc.symm]
  have hsrem : σs remainingReg = σp remainingReg := by
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ remainingReg hsr.symm]
  have hswbase : σs wBaseReg = wBase := by
    have hpwbase : σp wBaseReg = wBase := (hframeP wBaseReg hwc hwd hwr hwlen).trans hwbase
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ wBaseReg hsw.symm, hpwbase]
  have hswbits : ∀ l ∈ c.lits, σs (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro l hl
    have hne : wBase + l.var ≠ satReg := by have := hbelowW.2.2.2.2.2.1; omega
    have hpb : σp (wBase + l.var) = σ (wBase + l.var) := by
      have hne1 : wBase + l.var ≠ cursorReg := by have := hbelowW.1; omega
      have hne2 : wBase + l.var ≠ doneReg := by have := hbelowW.2.2.2.1; omega
      have hne3 : wBase + l.var ≠ remainingReg := by have := hbelowW.2.2.2.2.1; omega
      have hne4 : wBase + l.var ≠ lengthReg := by omega
      exact hframeP (wBase + l.var) hne1 hne2 hne3 hne4
    rw [hσs]; simp [eval_assign, Expr.eval, writeReg_diff _ satReg _ (wBase + l.var) hne, hpb]
    exact hwbits l hl
  have hbitsS : BitsFrom σs (addr + c.lits.length + 1) ((c.lits.map encodeLiteral).flatten ++ rest) := by
    intro i hi
    have hne : addr + c.lits.length + 1 + i ≠ satReg := by have := hbelow.2.2.2.2.2.1; omega
    rw [hσs]; simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ satReg _ (addr + c.lits.length + 1 + i) hne]
    exact hbitsP i hi
  have hbelowAddr' : cursorReg < addr + c.lits.length + 1 ∧ polReg < addr + c.lits.length + 1 ∧
      varReg < addr + c.lits.length + 1 ∧ doneReg < addr + c.lits.length + 1 ∧
      remainingReg < addr + c.lits.length + 1 ∧ satReg < addr + c.lits.length + 1 ∧
      bitReg < addr + c.lits.length + 1 ∧ valReg < addr + c.lits.length + 1 ∧
      wBaseReg < addr + c.lits.length + 1 := by omega
  have hWA' : wBase < addr + c.lits.length + 1 := by omega
  obtain ⟨hcurL, hremL, hsatL, hframeL⟩ := decode_clause_eval_loop_eval
    cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg bound
    (addr + c.lits.length + 1) 0 wBase c.lits rest σs
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl
    hsc hsp hsv hsd hsr hsb hsl hsw hbelowW hbelowAddr' hWA'
    (by rw [hsrem, hremP]) hssat (Or.inl rfl) hswbase hvarbound
    (by rw [hscur, hcurP]) hbitsS w hswbits
  have hfrL := hframeL r hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
  show (Program.forN (.reg remainingReg)
    (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg bound)).eval σs r = σ r
  rw [eval_forN, Expr.eval, hsrem, hremP, hfrL, hsr', hpr]

end NPComplete.CookLevin

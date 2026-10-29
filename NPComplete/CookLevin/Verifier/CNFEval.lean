module

public import NPComplete.CookLevin.Verifier.ClauseLengthEval

/-!
The CNF-level evaluator folds `clauseSatBool`'s per-clause result across the
formula with AND, one length-prefixed clause at a time
(`decodeClauseEvalWithLengthProgram`, `ClauseLengthEval.lean`).  This module
adds only the AND-accumulator step and its loop correctness; the length-
prefix/literal-loop machinery is unchanged and fully reused.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

/-- AND a clause's fold result into the CNF accumulator: once `cnfReg` is `0`
    it stays `0` (short-circuit); a zero `clauseSatReg` clears it. -/
def andIntoProg (clauseSatReg cnfReg : ℕ) : Program :=
  .ifNZ (.reg clauseSatReg) .skip (.assign cnfReg (.const 0))

lemma andIntoProg_eval (clauseSatReg cnfReg : ℕ) (σ : Store) :
    (andIntoProg clauseSatReg cnfReg).eval σ cnfReg =
      (if σ clauseSatReg = 0 then 0 else σ cnfReg) := by
  unfold andIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases h : σ clauseSatReg = 0
  · simp [eval_assign, Expr.eval, writeReg_same, h]
  · simp [eval_skip, h]

lemma andIntoProg_frame (clauseSatReg cnfReg r : ℕ) (σ : Store) (hr : r ≠ cnfReg) :
    (andIntoProg clauseSatReg cnfReg).eval σ r = σ r := by
  unfold andIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases h : σ clauseSatReg = 0
  · simp [eval_assign, Expr.eval, writeReg_diff σ cnfReg 0 r hr, h]
  · simp [eval_skip, h]

/-- Decode one clause (length prefix + literal eval) and AND its Boolean
    value into the CNF accumulator `cnfReg`. -/
def decodeCNFEvalClauseStep
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg bound : ℕ) : Program :=
  .seq (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
      bitReg valReg wBaseReg lengthReg bound)
    (andIntoProg satReg cnfReg)

/-- One-clause stage of the CNF evaluation loop: the clause evaluator advances the cursor past
`c`, ANDs its Boolean value into `cnfReg`, and leaves the remaining input and witness cells
untouched, so the tail satisfies the same invariants. -/
lemma decode_cnf_eval_clause_loop_eval_step
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg
      bound addr s0 wBase : ℕ) (c : Clause) (cs : List Clause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)      (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg)      (hvr : valReg ≠ remainingReg)     (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg) (hwlen : wBaseReg ≠ lengthReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
        (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hkl : cnfReg ≠ lengthReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hlenW : lengthReg < wBase)  (hcnfregW : cnfReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      lengthReg < addr ∧ cnfReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hcnf : σ cnfReg = s0)
    (hbound_c : c.lits.length + 1 ≤ bound)
    (hvarbound_c : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeClause c ++ rest))
    (w : List Bool)
    (hwbits_c : ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0)
    (hwbits_cs : ∀ cc ∈ cs, ∀ l ∈ cc.lits,
      σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    ∃ σ2, σ2 = (decodeCNFEvalClauseStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg bound).eval σ ∧
      σ2 cursorReg = addr + (encodeClause c).length ∧ σ2 wBaseReg = wBase ∧
      σ2 cnfReg = (if clauseSatBool w c then s0 else 0) ∧
      BitsFrom σ2 (addr + (encodeClause c).length) rest ∧
      (∀ cc ∈ cs, ∀ l ∈ cc.lits,
        σ2 (wBase + l.var) = if w.getD l.var false then 1 else 0) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hbelow
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hbelowW
  have hbelow' : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧
      wBaseReg < addr ∧ lengthReg < addr := ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  have hbelowW' : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase :=
    ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩
  obtain ⟨hcurE, hsatE, hwbaseE⟩ := decodeClauseEvalWithLengthProgram_eval
    cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
    bound addr wBase c rest σ
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl hwlen
    hsc hsp hsv hsd hsr hsb hsl hsw hlc hld
    hbelowW' hlenW hbelow' hWA hwbase hbound_c hvarbound_c hc hbits w hwbits_c
  have hfrAll : ∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ satReg → r ≠ bitReg → r ≠ valReg →
      r ≠ lengthReg →
      (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg bound).eval σ r = σ r := fun r h1 h2 h3 h4 h5 h6 h7 h8
        h10 =>
    decodeClauseEvalWithLengthProgram_frame
      cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
      bound addr wBase c rest σ r
      hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
      hvc hvr hwc hwp hwv hwd hwr hwb hwl hwlen
      hsc hsp hsv hsd hsr hsb hsl hsw hlc hld
      hbelowW' hlenW hbelow' hWA hwbase hbound_c hvarbound_c hc hbits w hwbits_c
      h1 h2 h3 h4 h5 h6 h7 h8 h10
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg lengthReg bound).eval σ := ⟨_, rfl⟩
  rw [← hσ1] at hcurE hsatE hwbaseE hfrAll
  have hcnf1 : σ1 cnfReg = s0 := (hfrAll cnfReg hkc hkp hkv hkd hkr hks hkb hkval hkl).trans hcnf
  have hbits1 : BitsFrom σ1 (addr + (encodeClause c).length) rest := by
    obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeClause c) rest hbits
    intro i hi
    rw [hfrAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact htail i hi
  have hwbits1 : ∀ cc ∈ cs, ∀ l ∈ cc.lits,
      σ1 (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro cc hcc l hl
    rw [hfrAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact hwbits_cs cc hcc l hl
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = (andIntoProg satReg cnfReg).eval σ1 := ⟨_, rfl⟩
  have hfr2 : ∀ r, r ≠ cnfReg → σ2 r = σ1 r := fun r hr => by
    rw [hσ2]; exact andIntoProg_frame satReg cnfReg r σ1 hr
  have h2cnf : σ2 cnfReg = (if σ1 satReg = 0 then 0 else σ1 cnfReg) := by
    rw [hσ2]; exact andIntoProg_eval satReg cnfReg σ1
  refine ⟨σ2, ?_, (hfr2 _ hkc.symm).trans hcurE, (hfr2 _ hkw.symm).trans hwbaseE, ?_,
    bitsFrom_of_eq_on (fun i _ => hfr2 _ (by omega)) hbits1,
    fun cc hcc l hl => (hfr2 _ (by omega)).trans (hwbits1 cc hcc l hl)⟩
  · unfold decodeCNFEvalClauseStep
    rw [eval_seq, ← hσ1, ← hσ2]
  · rw [h2cnf, hsatE, hcnf1]
    cases clauseSatBool w c <;> simp

/-- After one iteration per clause, the cursor has passed the clause-list
    encoding, and the accumulator holds the conjunction of the per-clause
    satisfaction values, seeded by its initial Boolean value. The accumulator
    register is distinct from every other evaluator register and lies below
    the certificate base. -/
lemma decode_cnf_eval_clause_loop_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg
      bound addr s0 wBase : ℕ) (cs : List Clause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)      (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg)      (hvr : valReg ≠ remainingReg)     (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg) (hwlen : wBaseReg ≠ lengthReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hlc : lengthReg ≠ cursorReg) (hld : lengthReg ≠ doneReg)
        (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hkl : cnfReg ≠ lengthReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hlenW : lengthReg < wBase)  (hcnfregW : cnfReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      lengthReg < addr ∧ cnfReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hcnf : σ cnfReg = s0) (hs0 : s0 = 0 ∨ s0 = 1)
    (hbound : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr ((cs.map encodeClause).flatten ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ cs, ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (loopEval (decodeCNFEvalClauseStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg bound) cs.length σ) cursorReg =
      addr + (cs.map encodeClause).flatten.length ∧
    (loopEval (decodeCNFEvalClauseStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg bound) cs.length σ) cnfReg =
      (if s0 = 1 ∧ ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) := by
  induction cs generalizing addr s0 σ with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero, loopEval]
      refine ⟨hc, ?_⟩
      rcases hs0 with h0 | h1
      · simp [hcnf, h0]
      · simp [hcnf, h1]
  | cons c cs ih =>
      have hshape : ((c :: cs).map encodeClause).flatten ++ rest =
          encodeClause c ++ ((cs.map encodeClause).flatten ++ rest) := by simp
      rw [hshape] at hbits
      obtain ⟨σ2, hσ2, hcur2, hwb2, hcnf2, hbits2, hwbits2⟩ :=
        decode_cnf_eval_clause_loop_eval_step cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg bound addr s0 wBase c cs
          ((cs.map encodeClause).flatten ++ rest) σ
          hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
          hvc hvr hwc hwp hwv hwd hwr hwb hwl hwlen
          hsc hsp hsv hsd hsr hsb hsl hsw hlc hld
          hkc hkp hkv hkd hkr hks hkb hkval hkw hkl
          hbelowW hlenW hcnfregW hbelow hWA hwbase hcnf
          (hbound c (by simp)) (hvarbound c (by simp)) hc hbits w
          (hwbits c (by simp)) (fun cc hcc => hwbits cc (by simp [hcc]))
      have hbelow1 : cursorReg < addr + (encodeClause c).length ∧
          polReg < addr + (encodeClause c).length ∧ varReg < addr + (encodeClause c).length ∧
          doneReg < addr + (encodeClause c).length ∧
          remainingReg < addr + (encodeClause c).length ∧
          satReg < addr + (encodeClause c).length ∧ bitReg < addr + (encodeClause c).length ∧
          valReg < addr + (encodeClause c).length ∧
          wBaseReg < addr + (encodeClause c).length ∧
          lengthReg < addr + (encodeClause c).length ∧ cnfReg < addr + (encodeClause c).length := by
        omega
      have hs0' : (if clauseSatBool w c then s0 else 0) = 0 ∨
          (if clauseSatBool w c then s0 else 0) = 1 := by
        split_ifs
        · exact hs0
        · exact Or.inl rfl
      obtain ⟨hcurTail, hcnfTail⟩ := ih (addr + (encodeClause c).length)
        (if clauseSatBool w c then s0 else 0) σ2 hbelow1 (by omega) (hwb2.trans rfl) hcnf2 hs0'
        (fun cc hcc => hbound cc (by simp [hcc]))
        (fun cc hcc => hvarbound cc (by simp [hcc])) hcur2 hbits2 hwbits2
      rw [show (c :: cs).length = cs.length + 1 by simp, loopEval_succ, ← hσ2]
      refine ⟨?_, ?_⟩
      · rw [hcurTail]
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        ring
      · rw [hcnfTail]
        cases hcs : clauseSatBool w c <;> simp [hcs]

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Verifier.ThreeCNFEvalAt
public import NPComplete.CookLevin.Verifier.CNFEval

/-!
`ThreeCNFEvalAt.lean`'s `decodeThreeClauseEvalStepAt` evaluates one `ThreeClause`; the CNF-level
fold ANDs that result across a clause list, mirroring `CNFEval.lean`'s `andIntoProg`/
`decodeCNFEvalClauseStep`/`decode_cnf_eval_clause_loop_eval` pattern for the unbounded-width `CNF`
type. Reusing `andIntoProg` directly (it is register-shape agnostic) keeps this module to the
loop-correctness induction alone.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeThreeClause)

/-- The Boolean `ThreeCNF` satisfaction check against a certificate `w`, mirroring
    `SATBool.lean`'s `cnfSatBool` for the width-3 clause type. -/
def threeCnfSatBool (w : List Bool) (f : ThreeCNF) : Bool :=
  f.clauses.all (fun c => c.is_satisfied (decodeAssignment w))

lemma threeCnfSatBool_iff (w : List Bool) (f : ThreeCNF) :
    threeCnfSatBool w f = true ↔ f.Satisfied (decodeAssignment w) := by
  unfold threeCnfSatBool ThreeCNF.Satisfied
  simp [List.all_eq_true, ThreeClause.is_satisfied_iff_satisfied]

/-- Decode one `ThreeClause` and AND its Boolean value into the CNF accumulator `cnfReg`.
    Mirrors `decodeCNFEvalClauseStep` (`CNFEval.lean`), swapping the length-prefixed
    `Clause` decode for the fixed-arity `decodeThreeClauseEvalStepAt`. -/
def decodeThreeCNFEvalClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) : Program :=
  .seq (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
      valReg wBaseReg boundReg)
    (andIntoProg satReg cnfReg)

/-- Transports the tail bit window and the tail clauses' certificate-bit readings across any
    store `σ1` that agrees with `σ` off `decodeThreeClauseEvalStepAt`'s eight control
    registers, at the address/base just past a decoded `ThreeClause` `c`. Isolates the
    bookkeeping shared by `decodeThreeCNFEvalClauseStepAt_step`'s two frame obligations. -/
lemma frame_shift_tail
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg addr wBase : ℕ)
    (c : ThreeClause) (cs : List ThreeClause) (rest : Bits) (σ σ1 : Store)
    (hframeE : ∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → r ≠ remainingReg →
      r ≠ satReg → r ≠ bitReg → r ≠ valReg → σ1 r = σ r)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hbits : BitsFrom σ addr (encodeThreeClause c ++ ((cs.map encodeThreeClause).flatten ++ rest)))
    (w : List Bool)
    (hwbitsTail : ∀ cc ∈ cs,
      (σ (wBase + cc.l1.var) = if w.getD cc.l1.var false then 1 else 0) ∧
      (σ (wBase + cc.l2.var) = if w.getD cc.l2.var false then 1 else 0) ∧
      (σ (wBase + cc.l3.var) = if w.getD cc.l3.var false then 1 else 0)) :
    BitsFrom σ1 (addr + (encodeThreeClause c).length) ((cs.map encodeThreeClause).flatten ++ rest) ∧
    (∀ cc ∈ cs, (σ1 (wBase + cc.l1.var) = if w.getD cc.l1.var false then 1 else 0) ∧
      (σ1 (wBase + cc.l2.var) = if w.getD cc.l2.var false then 1 else 0) ∧
      (σ1 (wBase + cc.l3.var) = if w.getD cc.l3.var false then 1 else 0)) := by
  have hoffA : ∀ (v r : ℕ), r < addr → addr + (encodeThreeClause c).length + v ≠ r :=
    fun v r hr => by omega
  have hoffW : ∀ (v r : ℕ), r < wBase → wBase + v ≠ r := fun v r hr => by omega
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [hframeE _ (hoffA i _ hbelow.1) (hoffA i _ hbelow.2.1) (hoffA i _ hbelow.2.2.1)
      (hoffA i _ hbelow.2.2.2.1) (hoffA i _ hbelow.2.2.2.2.1) (hoffA i _ hbelow.2.2.2.2.2.1)
      (hoffA i _ hbelow.2.2.2.2.2.2.1) (hoffA i _ hbelow.2.2.2.2.2.2.2)]
    obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeThreeClause c)
      ((cs.map encodeThreeClause).flatten ++ rest) hbits
    exact htail i hi
  · intro cc hcc
    have hb1 := hwbitsTail cc hcc
    refine ⟨?_, ?_, ?_⟩ <;>
      [rw [hframeE _ (hoffW _ _ hbelowW.1) (hoffW _ _ hbelowW.2.1) (hoffW _ _ hbelowW.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.2.2)];
       rw [hframeE _ (hoffW _ _ hbelowW.1) (hoffW _ _ hbelowW.2.1) (hoffW _ _ hbelowW.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.2.2)];
       rw [hframeE _ (hoffW _ _ hbelowW.1) (hoffW _ _ hbelowW.2.1) (hoffW _ _ hbelowW.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.1) (hoffW _ _ hbelowW.2.2.2.2.2.2.1)
          (hoffW _ _ hbelowW.2.2.2.2.2.2.2)]] <;>
      [exact hb1.1; exact hb1.2.1; exact hb1.2.2]

/-- One iteration of `decodeThreeCNFEvalClauseStepAt`: decoding-and-evaluating a single
    `ThreeClause` `c` advances the cursor past `c`'s encoding, ANDs `c`'s satisfaction value
    into the `cnfReg` accumulator (seeded at `s0`), and leaves `boundReg`/`wBaseReg`, the
    tail bit window, and the certificate-bit readings for `cs` frame-preserved. -/
lemma decodeThreeCNFEvalClauseStepAt_step
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg
      addr s0 bound wBase : ℕ) (c : ThreeClause) (cs : List ThreeClause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg) (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hbc0 : boundReg ≠ cursorReg) (hbp0 : boundReg ≠ polReg) (hbv0 : boundReg ≠ varReg)
    (hbd0 : boundReg ≠ doneReg) (hbr0 : boundReg ≠ remainingReg) (hbs0 : boundReg ≠ satReg)
    (hbbit0 : boundReg ≠ bitReg) (hbval0 : boundReg ≠ valReg)
    (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hkbnd : cnfReg ≠ boundReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hcnfregW : cnfReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hb : σ boundReg = bound) (hcnf : σ cnfReg = s0)
    (hbound_c : c.l1.var + 1 ≤ bound ∧ c.l2.var + 1 ≤ bound ∧ c.l3.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeClause c ++ ((cs.map encodeThreeClause).flatten ++ rest)))
    (w : List Bool)
    (hwbits_c : (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0))
    (hwbitsTail : ∀ cc ∈ cs,
      (σ (wBase + cc.l1.var) = if w.getD cc.l1.var false then 1 else 0) ∧
      (σ (wBase + cc.l2.var) = if w.getD cc.l2.var false then 1 else 0) ∧
      (σ (wBase + cc.l3.var) = if w.getD cc.l3.var false then 1 else 0)) :
    ∃ σ2 : Store,
    (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg cnfReg boundReg).eval σ = σ2 ∧
    σ2 cursorReg = addr + (encodeThreeClause c).length ∧
    σ2 cnfReg = (if c.is_satisfied (decodeAssignment w) then s0 else 0) ∧
    σ2 wBaseReg = wBase ∧ σ2 boundReg = bound ∧
    BitsFrom σ2 (addr + (encodeThreeClause c).length) ((cs.map encodeThreeClause).flatten ++ rest) ∧
    (∀ cc ∈ cs, (σ2 (wBase + cc.l1.var) = if w.getD cc.l1.var false then 1 else 0) ∧
      (σ2 (wBase + cc.l2.var) = if w.getD cc.l2.var false then 1 else 0) ∧
      (σ2 (wBase + cc.l3.var) = if w.getD cc.l3.var false then 1 else 0)) ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → r ≠ remainingReg →
      r ≠ satReg → r ≠ bitReg → r ≠ valReg → r ≠ cnfReg → σ2 r = σ r) := by
  obtain ⟨hcurE, hsatE, hwbaseE, hframeE⟩ := decodeThreeClauseEvalStepAt_eval
    cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg
    addr bound wBase c ((cs.map encodeThreeClause).flatten ++ rest) σ
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl
    hsc hsp hsv hsd hsr hsb hsl hsw hbc0 hbp0 hbv0 hbd0 hbr0 hbs0 hbbit0 hbval0
    hbelowW hbelow hWA hwbase hb hbound_c hc hbits w hwbits_c
  set σ1 := (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg boundReg).eval σ with hσ1def
  have hcnfE1 : σ1 cnfReg = s0 := (hframeE cnfReg hkc hkp hkv hkd hkr hks hkb hkval).trans hcnf
  have hboundE1 : σ1 boundReg = bound :=
    (hframeE boundReg hbc0 hbp0 hbv0 hbd0 hbr0 hbs0 hbbit0 hbval0).trans hb
  obtain ⟨hbitsTail1, hwbitsTail1⟩ := frame_shift_tail cursorReg polReg varReg doneReg
    remainingReg satReg bitReg valReg addr wBase c cs rest σ σ1 hframeE
    ⟨hbelow.1, hbelow.2.1, hbelow.2.2.1, hbelow.2.2.2.1, hbelow.2.2.2.2.1,
      hbelow.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.2.1⟩
    hbelowW hbits w hwbitsTail
  have hcnfA : cnfReg < addr := by have := hcnfregW; omega
  refine ⟨(andIntoProg satReg cnfReg).eval σ1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold decodeThreeCNFEvalClauseStepAt; rw [eval_seq, ← hσ1def]
  · rw [andIntoProg_frame satReg cnfReg cursorReg σ1 hkc.symm, hcurE]
  · rw [andIntoProg_eval satReg cnfReg σ1, hcnfE1, hsatE]
    cases c.is_satisfied (decodeAssignment w) <;> simp
  · rw [andIntoProg_frame satReg cnfReg wBaseReg σ1 hkw.symm, hwbaseE]
  · rw [andIntoProg_frame satReg cnfReg boundReg σ1 hkbnd.symm, hboundE1]
  · intro i hi
    rw [andIntoProg_frame satReg cnfReg _ σ1 (by omega)]
    exact hbitsTail1 i hi
  · intro cc hcc
    have hb1 := hwbitsTail1 cc hcc
    exact ⟨(andIntoProg_frame satReg cnfReg _ σ1 (by have := hbelowW.1; omega)).trans hb1.1,
      (andIntoProg_frame satReg cnfReg _ σ1 (by have := hbelowW.1; omega)).trans hb1.2.1,
      (andIntoProg_frame satReg cnfReg _ σ1 (by have := hbelowW.1; omega)).trans hb1.2.2⟩
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [andIntoProg_frame satReg cnfReg r σ1 h9, hframeE r h1 h2 h3 h4 h5 h6 h7 h8]


/-- Loop correctness for `decodeThreeCNFEvalClauseStepAt` over a clause list `cs`: after
    running `cs.length` iterations, the cursor has advanced past all of `cs`'s encoding, and
    `cnfReg` holds the AND-fold of `cs`'s per-clause `is_satisfied` results, seeded at the
    initial `cnfReg` value `s0 ∈ {0, 1}`.  Mirrors `decode_cnf_eval_clause_loop_eval`
    (`CNFEval.lean`). -/
lemma decode_three_cnf_eval_clause_loop_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg
      addr s0 wBase : ℕ) (cs : List ThreeClause) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg) (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hbc0 : boundReg ≠ cursorReg) (hbp0 : boundReg ≠ polReg) (hbv0 : boundReg ≠ varReg)
    (hbd0 : boundReg ≠ doneReg) (hbr0 : boundReg ≠ remainingReg) (hbs0 : boundReg ≠ satReg)
    (hbbit0 : boundReg ≠ bitReg) (hbval0 : boundReg ≠ valReg)
    (hkc : cnfReg ≠ cursorReg) (hkp : cnfReg ≠ polReg) (hkv : cnfReg ≠ varReg)
    (hkd : cnfReg ≠ doneReg) (hkr : cnfReg ≠ remainingReg) (hks : cnfReg ≠ satReg)
    (hkb : cnfReg ≠ bitReg) (hkval : cnfReg ≠ valReg) (hkw : cnfReg ≠ wBaseReg)
    (hkbnd : cnfReg ≠ boundReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hcnfregW : cnfReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
      cnfReg < addr)
    (hWA : wBase < addr)
    (hwbase : σ wBaseReg = wBase) (hb : σ boundReg = bound) (hcnf : σ cnfReg = s0)
    (hs0 : s0 = 0 ∨ s0 = 1)
    (hbound : ∀ c ∈ cs, c.l1.var + 1 ≤ bound ∧ c.l2.var + 1 ≤ bound ∧ c.l3.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr ((cs.map encodeThreeClause).flatten ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ cs, (σ (wBase + c.l1.var) = if w.getD c.l1.var false then 1 else 0) ∧
      (σ (wBase + c.l2.var) = if w.getD c.l2.var false then 1 else 0) ∧
      (σ (wBase + c.l3.var) = if w.getD c.l3.var false then 1 else 0)) :
    (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg cnfReg boundReg) cs.length σ) cursorReg =
      addr + (cs.map encodeThreeClause).flatten.length ∧
    (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg cnfReg boundReg) cs.length σ) cnfReg =
      (if s0 = 1 ∧ ∀ c ∈ cs, c.is_satisfied (decodeAssignment w) = true then 1 else 0) := by
  induction cs generalizing addr s0 σ with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero, loopEval]
      refine ⟨hc, ?_⟩
      rcases hs0 with h0 | h1
      · simp [hcnf, h0]
      · simp [hcnf, h1]
  | cons c cs ih =>
      have hshape : ((c :: cs).map encodeThreeClause).flatten ++ rest =
          encodeThreeClause c ++ ((cs.map encodeThreeClause).flatten ++ rest) := by simp
      rw [hshape] at hbits
      have hbelow' : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
          remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr :=
        ⟨hbelow.1, hbelow.2.1, hbelow.2.2.1, hbelow.2.2.2.1, hbelow.2.2.2.2.1,
          hbelow.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.1, hbelow.2.2.2.2.2.2.2.1,
          hbelow.2.2.2.2.2.2.2.2.1⟩
      obtain ⟨σ2, hstepEq, hcurTail0, hcnfTail0, hwbaseTail0, hboundTail0, hbitsTail0,
        hwbitsTail0, hframeTail0⟩ := decodeThreeCNFEvalClauseStepAt_step
        cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
        boundReg addr s0 bound wBase c cs rest σ
        hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
        hvc hvr hwc hwp hwv hwd hwr hwb hwl
        hsc hsp hsv hsd hsr hsb hsl hsw hbc0 hbp0 hbv0 hbd0 hbr0 hbs0 hbbit0 hbval0
        hkc hkp hkv hkd hkr hks hkb hkval hkw hkbnd
        hbelowW hcnfregW hbelow' hWA hwbase hb hcnf (hbound c (by simp)) hc hbits w
        (hwbits c (by simp)) (fun cc hcc => hwbits cc (by simp [hcc]))
      set addr' := addr + (encodeThreeClause c).length with haddr'
      have hbelow1 : cursorReg < addr' ∧ polReg < addr' ∧ varReg < addr' ∧ doneReg < addr' ∧
          remainingReg < addr' ∧ satReg < addr' ∧ bitReg < addr' ∧ valReg < addr' ∧
          wBaseReg < addr' ∧ cnfReg < addr' := by rw [haddr']; omega
      have hWA1 : wBase < addr' := by rw [haddr']; omega
      set s0' := (if c.is_satisfied (decodeAssignment w) then s0 else 0) with hs0'def
      have hs0'01 : s0' = 0 ∨ s0' = 1 := by
        rw [hs0'def]; split_ifs with h
        · exact hs0
        · left; rfl
      obtain ⟨hcurTail, hcnfTail⟩ := ih addr' s0' σ2 hbelow1 hWA1
        hwbaseTail0 hboundTail0 hcnfTail0 hs0'01
        (fun cc hcc => hbound cc (by simp [hcc])) hcurTail0 hbitsTail0 hwbitsTail0
      rw [show (c :: cs).length = cs.length + 1 by simp, loopEval_succ, hstepEq]
      refine ⟨?_, ?_⟩
      · rw [hcurTail, haddr']
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        ring
      · rw [hcnfTail, hs0'def]
        simp only [List.forall_mem_cons]
        cases c.is_satisfied (decodeAssignment w) <;> by_cases hs0 : s0 = 1 <;> simp [hs0]

end NPComplete.CookLevin

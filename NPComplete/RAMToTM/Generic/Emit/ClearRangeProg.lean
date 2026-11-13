module

public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
meta import NPComplete.Meta.ApiLayer

/-!
# A general-purpose "zero a memory range" primitive over ordinary registers

`zeroRangeProg` (`CanonicalStoreFinalize.lean`) zeroes a dynamic range too, but only reads its
base/length off the *dynamic-register* convention `ctlCell j = σ (σ 0 + j)`. Some callers need a
different layout, so `clearRangeProg` instead reads its base/length from two arbitrary `Expr`s,
snapshotting both into caller-chosen scratch registers *once* at entry —
never re-evaluating them mid-loop — because the registers those expressions read may themselves
sit inside the range being cleared (the store is a single `ℕ → ℕ` space shared by registers and
memory, so a low-numbered register can coincide with a high memory address and vice versa).
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

/-! ## The program -/

/-- One iteration of `clearRangeProg`'s clearing loop: zero the cell at `(base register) +
    (cursor register)`, reading both fresh from the store, then advance the cursor. Reading
    `baseReg` fresh (rather than folding it into a constant address) is what lets the range's
    base be a run-time value; it is only safe because callers keep `baseReg`/`curReg` themselves
    outside the range being cleared (`clearRangeBody_loop_invariant`'s separation hypotheses). -/
@[construction_api] def clearRangeBody (baseReg curReg : ℕ) : Program :=
  .seq (.assignInd (.add (.reg baseReg) (.reg curReg)) (.const 0))
       (.assign curReg (.add (.reg curReg) (.const 1)))

/-- Zero every cell in `[base, base + len)` where `base := baseE.eval σ` and `len := lenE.eval σ`
    are computed *once* at entry and snapshotted into `baseReg`/`lenReg`, then `curReg` is reset
    to `0` and used as the loop cursor. `baseReg`, `lenReg`, `curReg` are ordinary registers
    chosen by the caller (not cell-`0`-relative control cells), so this works uniformly regardless
    of which addressing convention, if any, the calling stage otherwise follows. -/
@[construction_api] def clearRangeProg (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) : Program :=
  .seq (.assign baseReg baseE)
    (.seq (.assign lenReg lenE)
      (.seq (.assign curReg (.const 0))
        (.forN (.reg lenReg) (clearRangeBody baseReg curReg))))

@[construction_api] lemma ScanFree_clearRangeBody (baseReg curReg : ℕ) : ScanFree (clearRangeBody baseReg curReg) := by
  unfold clearRangeBody ScanFree; trivial

@[construction_api] lemma ScanFree_clearRangeProg (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) :
    ScanFree (clearRangeProg baseReg lenReg curReg baseE lenE) := by
  unfold clearRangeProg ScanFree
  exact ⟨trivial, trivial, trivial, ScanFree_clearRangeBody baseReg curReg⟩

/-! ## Loop invariant -/

/-- Loop invariant for `clearRangeBody`, tracked across `t` iterations from a store where the
    cursor register already reads `c`: the base register and cursor register evolve as expected,
    the just-cleared window `[base + c, base + c + t)` is zero, and every other cell (other than
    the cursor register) is left exactly as it was. `hsepB`/`hsepC` keep `baseReg`/`curReg`
    themselves *outside* the whole range `[b, b + L)` being cleared across all `L` iterations
    (via the threaded bound `c + t ≤ L`) — without this, a coincidence between a register number
    and a memory address inside the range would let the loop corrupt its own bookkeeping cells
    mid-run. -/
@[construction_api] lemma clearRangeBody_loop_invariant (baseReg curReg b L : ℕ)
    (hbc : baseReg ≠ curReg)
    (hsepB : baseReg < b ∨ b + L ≤ baseReg) (hsepC : curReg < b ∨ b + L ≤ curReg) :
    ∀ t c (τ : Store), c + t ≤ L → τ baseReg = b → τ curReg = c →
      (loopEval (clearRangeBody baseReg curReg) t τ) baseReg = b ∧
      (loopEval (clearRangeBody baseReg curReg) t τ) curReg = c + t ∧
      (∀ q, q < t → (loopEval (clearRangeBody baseReg curReg) t τ) (b + c + q) = 0) ∧
      (∀ r, r ≠ curReg → (r < b + c ∨ b + c + t ≤ r) →
        (loopEval (clearRangeBody baseReg curReg) t τ) r = τ r) := by
  intro t
  induction t with
  | zero =>
    intro c τ _ hb hc
    rw [loopEval_zero]
    exact ⟨hb, by omega, fun q hq => absurd hq (by omega), fun r _ _ => rfl⟩
  | succ t ih =>
    intro c τ hcL hb hc
    have haddrB : b + c ≠ baseReg := by rcases hsepB with h | h <;> omega
    have haddrC : b + c ≠ curReg := by rcases hsepC with h | h <;> omega
    have hAeval : (Program.assignInd (Expr.add (Expr.reg baseReg) (Expr.reg curReg))
        (Expr.const 0)).eval τ = writeReg τ (b + c) 0 := by
      rw [eval_assignInd]
      have e1 : (Expr.add (Expr.reg baseReg) (Expr.reg curReg)).eval τ = b + c := by
        simp only [Expr.eval, hb, hc]
      have e2 : (Expr.const 0).eval τ = 0 := by simp [Expr.eval]
      rw [e1, e2]
    set τ' := writeReg τ (b + c) 0 with hτ'def
    have hτ'base : τ' baseReg = b := by
      rw [hτ'def, writeReg_diff τ (b + c) 0 baseReg haddrB.symm, hb]
    have hτ'cur : τ' curReg = c := by
      rw [hτ'def, writeReg_diff τ (b + c) 0 curReg haddrC.symm, hc]
    have hτ'zero : τ' (b + c) = 0 := by rw [hτ'def, writeReg_same]
    have hBeval : (Program.assign curReg (Expr.add (Expr.reg curReg) (Expr.const 1))).eval τ' =
        writeReg τ' curReg (c + 1) := by
      rw [eval_assign]
      have e2 : (Expr.add (Expr.reg curReg) (Expr.const 1)).eval τ' = c + 1 := by
        simp only [Expr.eval, hτ'cur]
      rw [e2]
    set τ1 := (clearRangeBody baseReg curReg).eval τ with hτ1def
    have hτ1eq : τ1 = writeReg τ' curReg (c + 1) := by
      rw [hτ1def]; unfold clearRangeBody; rw [eval_seq, hAeval, hBeval]
    have hτ1base : τ1 baseReg = b := by
      rw [hτ1eq, writeReg_diff τ' curReg (c + 1) baseReg hbc, hτ'base]
    have hτ1cur : τ1 curReg = c + 1 := by rw [hτ1eq, writeReg_same]
    have hτ1zero : τ1 (b + c) = 0 := by
      rw [hτ1eq, writeReg_diff τ' curReg (c + 1) (b + c) haddrC, hτ'zero]
    have hcL' : (c + 1) + t ≤ L := by omega
    obtain ⟨hf0, hfb, hfzero, hfframe⟩ := ih (c + 1) τ1 hcL' hτ1base hτ1cur
    have hloopstep : loopEval (clearRangeBody baseReg curReg) (t + 1) τ =
        loopEval (clearRangeBody baseReg curReg) t τ1 := by rw [loopEval_succ]
    rw [hloopstep]
    refine ⟨hf0, by rw [hfb]; omega, ?_, ?_⟩
    · intro q hq
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        have heq := hfframe (b + c) (by omega) (Or.inl (by omega))
        simpa using heq.trans hτ1zero
      · have hlt : q - 1 < t := by omega
        have heq := hfzero (q - 1) hlt
        have hidx : b + (c + 1) + (q - 1) = b + c + q := by omega
        rwa [hidx] at heq
    · intro r hr hrange
      rcases hrange with hlt | hge
      · have hne : r ≠ b + c := by omega
        have hcond : r < b + (c + 1) ∨ b + (c + 1) + t ≤ r := Or.inl (by omega)
        have heq := hfframe r hr hcond
        rw [heq, hτ1eq, writeReg_diff τ' curReg (c + 1) r hr, hτ'def, writeReg_diff τ (b + c) 0 r hne]
      · have hne : r ≠ b + c := by omega
        have hcond : r < b + (c + 1) ∨ b + (c + 1) + t ≤ r := Or.inr (by omega)
        have heq := hfframe r hr hcond
        rw [heq, hτ1eq, writeReg_diff τ' curReg (c + 1) r hr, hτ'def, writeReg_diff τ (b + c) 0 r hne]

/-! ## Unfolding `eval` to the loop, and register-set hypotheses -/

/-- `clearRangeProg`'s effect unfolds to `L := lenE.eval σ` iterations of `clearRangeBody`,
    starting from the store where `baseReg`/`lenReg` hold the entry-time snapshots and `curReg`
    holds `0`. `hlenE` is the "does not read `baseReg`" side condition `lenE` must satisfy — the
    same shape `relocProg_correct`'s `hlen` hypothesis takes — needed because `lenE` is evaluated
    *after* `baseReg` has already been written. -/
@[construction_api] lemma clearRangeProg_eval_eq (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) (σ : Store)
    (_hbl : baseReg ≠ lenReg) (_hbc : baseReg ≠ curReg) (hlc : lenReg ≠ curReg)
    (hlenE : lenE.eval (writeReg σ baseReg (baseE.eval σ)) = lenE.eval σ) :
    (clearRangeProg baseReg lenReg curReg baseE lenE).eval σ =
      loopEval (clearRangeBody baseReg curReg) (lenE.eval σ)
        (writeReg (writeReg (writeReg σ baseReg (baseE.eval σ)) lenReg (lenE.eval σ)) curReg 0) := by
  unfold clearRangeProg
  simp only [eval_seq, eval_assign, eval_forN, Expr.eval]
  set σ1 := writeReg σ baseReg (baseE.eval σ) with hσ1def
  have hlenEσ1 : lenE.eval σ1 = lenE.eval σ := hlenE
  rw [hlenEσ1]
  set σ2 := writeReg σ1 lenReg (lenE.eval σ) with hσ2def
  have hσ2len : σ2 lenReg = lenE.eval σ := by rw [hσ2def, writeReg_same]
  have hlenread : (writeReg σ2 curReg 0) lenReg = lenE.eval σ := by
    rw [writeReg_diff σ2 curReg 0 lenReg hlc, hσ2len]
  rw [hlenread]

/-! ## Correctness: zeroed / frame -/

/-- **The cleared range really is zero.** -/
@[construction_api] lemma clearRangeProg_zeroed (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) (σ : Store)
    (hbl : baseReg ≠ lenReg) (hbc : baseReg ≠ curReg) (hlc : lenReg ≠ curReg)
    (hlenE : lenE.eval (writeReg σ baseReg (baseE.eval σ)) = lenE.eval σ)
    (hsepB : baseReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ baseReg)
    (hsepC : curReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ curReg) :
    ∀ i, baseE.eval σ ≤ i → i < baseE.eval σ + lenE.eval σ →
      (clearRangeProg baseReg lenReg curReg baseE lenE).eval σ i = 0 := by
  set b := baseE.eval σ with hbdef
  set L := lenE.eval σ with hLdef
  rw [clearRangeProg_eval_eq baseReg lenReg curReg baseE lenE σ hbl hbc hlc hlenE]
  set σ3 := writeReg (writeReg (writeReg σ baseReg b) lenReg L) curReg 0 with hσ3def
  have hσ3base : σ3 baseReg = b := by
    rw [hσ3def, writeReg_diff _ curReg 0 baseReg hbc,
      writeReg_diff _ lenReg L baseReg hbl, writeReg_same]
  have hσ3cur : σ3 curReg = 0 := by rw [hσ3def, writeReg_same]
  obtain ⟨_, _, hzeroed, _⟩ :=
    clearRangeBody_loop_invariant baseReg curReg b L hbc hsepB hsepC L 0 σ3 (by omega) hσ3base hσ3cur
  intro i hi1 hi2
  have hq : i - b < L := by omega
  have heq := hzeroed (i - b) hq
  have hidx : b + 0 + (i - b) = i := by omega
  rwa [hidx] at heq

/-- **Everything outside the range and outside the three work registers is untouched.** -/
@[construction_api] lemma clearRangeProg_frame (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) (σ : Store)
    (hbl : baseReg ≠ lenReg) (hbc : baseReg ≠ curReg) (hlc : lenReg ≠ curReg)
    (hlenE : lenE.eval (writeReg σ baseReg (baseE.eval σ)) = lenE.eval σ)
    (hsepB : baseReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ baseReg)
    (hsepC : curReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ curReg) :
    ∀ i, i ≠ baseReg → i ≠ lenReg → i ≠ curReg →
      (i < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ i) →
      (clearRangeProg baseReg lenReg curReg baseE lenE).eval σ i = σ i := by
  set b := baseE.eval σ with hbdef
  set L := lenE.eval σ with hLdef
  rw [clearRangeProg_eval_eq baseReg lenReg curReg baseE lenE σ hbl hbc hlc hlenE]
  set σ3 := writeReg (writeReg (writeReg σ baseReg b) lenReg L) curReg 0 with hσ3def
  have hσ3base : σ3 baseReg = b := by
    rw [hσ3def, writeReg_diff _ curReg 0 baseReg hbc,
      writeReg_diff _ lenReg L baseReg hbl, writeReg_same]
  have hσ3cur : σ3 curReg = 0 := by rw [hσ3def, writeReg_same]
  obtain ⟨_, _, _, hframe⟩ :=
    clearRangeBody_loop_invariant baseReg curReg b L hbc hsepB hsepC L 0 σ3 (by omega) hσ3base hσ3cur
  intro i hib hil hic hrange
  have hcond : i < b + 0 ∨ b + 0 + L ≤ i := by
    rcases hrange with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [hframe i hic hcond, hσ3def, writeReg_diff _ curReg 0 i hic,
    writeReg_diff _ lenReg L i hil, writeReg_diff _ baseReg b i hib]

/-! ## Cost -/

/-- `clearRangeBody`'s cost is a store-independent constant: `Expr.cost` never inspects a store,
    and the body itself contains no loop or branch. -/
@[construction_api] lemma clearRangeBody_cost (baseReg curReg : ℕ) (τ : Store) :
    (clearRangeBody baseReg curReg).cost τ = 9 := by
  simp [clearRangeBody, Expr.cost]

/-- `clearRangeProg`'s cost: the three constant-cost setup assignments, plus the `forN`'s own
    `1`-cost bound-expression evaluation, plus `L := lenE.eval σ` iterations at `9` each. Stated
    as a coarse linear-in-`L` bound (not exact), matching `zeroRangeProg_cost_le`'s style. -/
@[construction_api] lemma clearRangeProg_cost_le (baseReg lenReg curReg : ℕ) (baseE lenE : Expr) (σ : Store)
    (_hbl : baseReg ≠ lenReg) (_hbc : baseReg ≠ curReg) (hlc : lenReg ≠ curReg)
    (hlenE : lenE.eval (writeReg σ baseReg (baseE.eval σ)) = lenE.eval σ) :
    (clearRangeProg baseReg lenReg curReg baseE lenE).cost σ ≤
      baseE.cost + lenE.cost + 9 * lenE.eval σ + 6 := by
  unfold clearRangeProg
  simp only [cost_seq, cost_assign, cost_forN, eval_assign, Expr.eval, Expr.cost]
  set σ1 := writeReg σ baseReg (baseE.eval σ) with hσ1def
  have hlenEσ1 : lenE.eval σ1 = lenE.eval σ := hlenE
  rw [hlenEσ1]
  set σ2 := writeReg σ1 lenReg (lenE.eval σ) with hσ2def
  have hσ2len : σ2 lenReg = lenE.eval σ := by rw [hσ2def, writeReg_same]
  have hlenread : (writeReg σ2 curReg 0) lenReg = lenE.eval σ := by
    rw [writeReg_diff σ2 curReg 0 lenReg hlc, hσ2len]
  rw [hlenread]
  have hbodyle : ∀ τ, (clearRangeBody baseReg curReg).cost τ ≤ 9 :=
    fun τ => (clearRangeBody_cost baseReg curReg τ).le
  have hloop := loopCost_le_of_body_le (clearRangeBody baseReg curReg) 9 hbodyle
    (lenE.eval σ) (writeReg σ2 curReg 0)
  omega

/-! ## `ProgramBoundedIn` -/

/-- `ProgramBoundedIn` for one `clearRangeBody` step at cursor value `c`, given the write address
    `b + c` differs from `curReg` (guaranteed across the whole run by `hsepC`, instantiated per
    iteration). -/
@[construction_api] lemma ProgramBoundedIn_clearRangeBody (Bp baseReg curReg b c : ℕ) (τ : Store)
    (hbase : τ baseReg = b) (hcur : τ curReg = c) (hne : b + c ≠ curReg)
    (hbaseBp : baseReg ≤ Bp) (hcurBp : curReg ≤ Bp) (haddr : b + c ≤ Bp) (hc1 : c + 1 ≤ Bp) :
    ProgramBoundedIn Bp τ (clearRangeBody baseReg curReg) := by
  unfold clearRangeBody
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_assignInd, hbase, hcur]
  have hτ' : (writeReg τ (b + c) 0) curReg = c := by
    rw [writeReg_diff τ (b + c) 0 curReg hne.symm, hcur]
  simp only [hτ']
  omega

/-- `clearRangeProg`'s syntactic operand bound: every address/value it computes stays `≤ Bp`,
    given `baseE`/`lenE` themselves are `ExprBoundedIn`-bounded (at the stores where they are
    actually evaluated), `Bp` dominates the whole range `[b, b + L)` and the three work
    registers, and the same separation `hsepB`/`hsepC` the correctness lemmas need. -/
@[construction_api] lemma ProgramBoundedIn_clearRangeProg (Bp baseReg lenReg curReg : ℕ) (baseE lenE : Expr) (σ : Store)
    (hbl : baseReg ≠ lenReg) (hbc : baseReg ≠ curReg) (hlc : lenReg ≠ curReg)
    (hlenE : lenE.eval (writeReg σ baseReg (baseE.eval σ)) = lenE.eval σ)
    (hsepB : baseReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ baseReg)
    (hsepC : curReg < baseE.eval σ ∨ baseE.eval σ + lenE.eval σ ≤ curReg)
    (hbaseEv : ExprBoundedIn Bp σ baseE)
    (hlenEv : ExprBoundedIn Bp (writeReg σ baseReg (baseE.eval σ)) lenE)
    (hbaseBp : baseReg ≤ Bp) (hlenRegBp : lenReg ≤ Bp) (hcurBp : curReg ≤ Bp)
    (haddrBp : baseE.eval σ + lenE.eval σ ≤ Bp) :
    ProgramBoundedIn Bp σ (clearRangeProg baseReg lenReg curReg baseE lenE) := by
  set b := baseE.eval σ with hbdef
  set L := lenE.eval σ with hLdef
  unfold clearRangeProg
  simp only [ProgramBoundedIn, eval_assign]
  set σ1 := writeReg σ baseReg b with hσ1def
  have hlenEσ1 : lenE.eval σ1 = L := hlenE
  rw [hlenEσ1]
  set σ2 := writeReg σ1 lenReg L with hσ2def
  refine ⟨⟨hbaseBp, hbaseEv⟩, ⟨hlenRegBp, hlenEv⟩, ⟨hcurBp, by simp [ExprBoundedIn]⟩, ?_⟩
  have hσ3base : (writeReg σ2 curReg 0) baseReg = b := by
    rw [writeReg_diff σ2 curReg 0 baseReg hbc, hσ2def, writeReg_diff σ1 lenReg L baseReg hbl,
      hσ1def, writeReg_same]
  have hσ3cur : (writeReg σ2 curReg 0) curReg = 0 := writeReg_same σ2 curReg 0
  have hlenread : (writeReg σ2 curReg 0) lenReg = L := by
    rw [writeReg_diff σ2 curReg 0 lenReg hlc, hσ2def, writeReg_same]
  refine ⟨hlenRegBp, ?_⟩
  simp only [Expr.eval, hlenread]
  intro m' hm'
  obtain ⟨hib, hic, _, _⟩ :=
    clearRangeBody_loop_invariant baseReg curReg b L hbc hsepB hsepC m' 0
      (writeReg σ2 curReg 0) (by omega) hσ3base hσ3cur
  have hne : b + m' ≠ curReg := by rcases hsepC with h | h <;> omega
  refine ProgramBoundedIn_clearRangeBody Bp baseReg curReg b m'
    (loopEval (clearRangeBody baseReg curReg) m' (writeReg σ2 curReg 0)) ?_ ?_ hne
    hbaseBp hcurBp (by omega) (by omega)
  · simpa using hib
  · simpa using hic

end NPComplete.RAMToTM

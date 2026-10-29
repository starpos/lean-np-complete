module

public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider

/-!
# Canonical-store finalize toolkit

A producer program and an arbitrary decision program are joined with `Program.seq` into a
single program compiled to a Turing machine exactly once. The decision program's only usable
fact is an equation of the form `(decisionProg).eval (bitInputStore inputBits) 0 = 1`, and the
program may read any cells, so the join is only sound if
`producerProg.eval (bitInputStore inputBits) = bitInputStore outputBits` holds as a *function*
`ℕ → ℕ`, not merely on some finite prefix. A producer program therefore needs a finalize phase:
after computing its answer bits, it must place them at the canonical output addresses and zero
every other cell.

## Address convention for the finalize phase

* Cell `0` ends up holding the final output bit length `M`. The producer emits while cell `0`
  holds an emit bound `S ≥ M` (the emitters here are stated for whatever value cell `0` holds and
  preserve it); `finalizePivotProg` (`CanonicalStoreFinalizeBody.lean`) then stages the cleanup
  control cells and lowers cell `0` to `M`, and `finalizeCleanupProg` runs with cell `0` fixed
  at `M`.
* Output bits live in cells `1 .. M`.
* Finalize's own control cells (cursors, bases, lengths for zeroing passes) live
  at cells `M + 1, M + 2, …`. Since cell `0` holds `M`, control cell `j` is
  addressed by the *expression* `.add (.reg 0) (.const j)` rather than a literal
  constant — a "dynamic register" whose address floats with the run-time value of
  `M`, so control cells never collide with the output region `[1, M]` regardless
  of formula size.
* Any working storage (tables, scratch arrays) used earlier in the reduction sits
  at addresses above the control cells and must be zeroed by this same finalize
  phase before the program halts.

This module provides address-independent pieces needed for that finalization: a
cell-by-cell criterion for recognizing `bitInputStore bits` (`store_eq_bitInputStore`),
dynamic control-cell primitives (`ctlAddr`, `ctlCell`, `ctlAssign`), and a generic
range-zeroing loop (`zeroRangeProg`). It also defines output emitters for bits, natural
numbers, lists, natural-number and tuple tables, tagged-entry lists, and row tables, with
lemmas describing their effects on the store.
-/

@[expose] public section
namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr writeReg eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits)

/-! ## Canonical store recognition

`Program.eval` returns a total `Store`, so showing a finalize phase produces
`bitInputStore outputBits` is a `funext` obligation over every address, not just
the output region. `store_eq_bitInputStore` packages the three facts a finalize
phase naturally establishes cell-by-cell (length cell, in-range bits, zero tail)
into that single equality; the tail case reuses the `List.getD` argument from
`bitInputStore_eq_zero_of_ge_inputEnd`. -/

lemma store_eq_bitInputStore (σ : Store) (bits : Bits)
    (h0 : σ 0 = bits.length)
    (hbit : ∀ i, i < bits.length → σ (i + 1) = if bits.getD i false then 1 else 0)
    (hzero : ∀ r, bits.length < r → σ r = 0) :
    σ = bitInputStore bits := by
  funext r
  match r with
  | 0 => simpa [bitInputStore] using h0
  | r' + 1 =>
    simp only [bitInputStore]
    rcases Nat.lt_or_ge r' bits.length with hlt | hge
    · exact hbit r' hlt
    · rw [hzero (r' + 1) (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)]
      simp

/-! ## Control cells as dynamic registers

Finalize control state (cursors, bases, lengths for a zeroing pass) must not
collide with the output bit region `[1, M]`, whose extent `M` is known only at
run time (it is the value already sitting in cell `0` when the phase starts).
Addressing every control cell as `cell 0 + j` for a compile-time offset `j`
keeps `j` static while letting the *address* float with `M`, so one finalize
program works uniformly across formula sizes instead of hand-picking disjoint
literal addresses per instance. -/

/-- Address expression of control cell `j`: `j` past whatever cell `0` currently
    holds. -/
def ctlAddr (j : ℕ) : Expr := .add (.reg 0) (.const j)

/-- Value held in control cell `j`. -/
def ctlCell (j : ℕ) : Expr := .regInd (ctlAddr j)

/-- Write `e` into control cell `j`. -/
def ctlAssign (j : ℕ) (e : Expr) : Program := .assignInd (ctlAddr j) e

lemma ctlAddr_eval (j : ℕ) (σ : Store) : (ctlAddr j).eval σ = σ 0 + j := by
  simp [ctlAddr, Expr.eval]

lemma ctlCell_eval (j : ℕ) (σ : Store) : (ctlCell j).eval σ = σ (σ 0 + j) := by
  simp [ctlCell, Expr.eval, ctlAddr_eval]

lemma ctlAssign_eval_same (j : ℕ) (e : Expr) (σ : Store) :
    ((ctlAssign j e).eval σ) (σ 0 + j) = e.eval σ := by
  simp [ctlAssign, eval_assignInd, ctlAddr_eval, writeReg_same]

lemma ctlAssign_eval_diff (j : ℕ) (e : Expr) (σ : Store) (r : ℕ) (h : r ≠ σ 0 + j) :
    ((ctlAssign j e).eval σ) r = σ r := by
  simp only [ctlAssign, eval_assignInd, ctlAddr_eval]
  exact writeReg_diff σ (σ 0 + j) (e.eval σ) r h

lemma ctlAssign_zero (j : ℕ) (e : Expr) (σ : Store) (hj : 1 ≤ j) :
    ((ctlAssign j e).eval σ) 0 = σ 0 :=
  ctlAssign_eval_diff j e σ 0 (by omega)

/-! ## Zeroing a dynamic range

Scratch space used earlier in the reduction must be cleared before the finalize
phase hands control back, but its base address and length are themselves
run-time values (control cells, per the dynamic-register convention above), not
compile-time constants. `zeroRangeProg` clears `[base, base + len)` reading
`base`/`len` off two control cells and using a third as the loop cursor;
`zeroRangeProg`'s bound is a single `forN` evaluated once at entry
(`Program.eval (.forN n body) σ = loopEval body (n.eval σ) σ`), so the body may
freely disturb the length cell without affecting how many iterations already
ran — it must, however, leave the base cell and cell `0` alone, since the body
keeps reading them every iteration. -/

/-- One iteration of `zeroRangeProg`'s clearing loop: zero the cell at
    `(base cell) + (cursor cell)`, then advance the cursor. -/
def zeroRangeBody (baseJ curJ : ℕ) : Program :=
  .seq (.assignInd (.add (ctlCell baseJ) (ctlCell curJ)) (.const 0))
    (ctlAssign curJ (.add (ctlCell curJ) (.const 1)))

/-- Zero every cell in `[base, base + len)`, where `base` is held in control cell
    `baseJ`, `len` in control cell `lenJ`, and control cell `curJ` is used as the
    cursor. -/
def zeroRangeProg (baseJ lenJ curJ : ℕ) : Program :=
  .seq (ctlAssign curJ (.const 0)) (.forN (ctlCell lenJ) (zeroRangeBody baseJ curJ))

/-- Loop invariant for `zeroRangeBody`, tracked across `t` iterations from a store
    where the cursor cell already reads `c`: the root cell and base cell are
    preserved, the cursor advances to `c + t`, the just-cleared window
    `[base + c, base + c + t)` is zero, and every other cell outside the
    eventual write window `[base + c, base + c + t)` is left exactly as it was —
    the fact that lets a caller compose this with whatever wrote `τ` in the
    first place. -/
lemma zeroRangeBody_loop_invariant (baseJ curJ M base : ℕ)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base) :
    ∀ t c (τ : Store), τ 0 = M → τ (M + baseJ) = base → τ (M + curJ) = c →
      (loopEval (zeroRangeBody baseJ curJ) t τ) 0 = M ∧
      (loopEval (zeroRangeBody baseJ curJ) t τ) (M + baseJ) = base ∧
      (loopEval (zeroRangeBody baseJ curJ) t τ) (M + curJ) = c + t ∧
      (∀ q, q < t → (loopEval (zeroRangeBody baseJ curJ) t τ) (base + c + q) = 0) ∧
      (∀ r, r ≠ M + curJ → (r < base + c ∨ base + c + t ≤ r) →
        (loopEval (zeroRangeBody baseJ curJ) t τ) r = τ r) := by
  intro t
  induction t with
  | zero =>
    intro c τ h0 hb hc
    rw [loopEval_zero]
    exact ⟨h0, hb, by omega, fun q hq => absurd hq (by omega), fun r _ _ => rfl⟩
  | succ t ih =>
    intro c τ h0 hb hc
    have haddr : (ctlCell baseJ).eval τ + (ctlCell curJ).eval τ = base + c := by
      rw [ctlCell_eval, ctlCell_eval, h0, hb, hc]
    have hAeval : (Program.assignInd (Expr.add (ctlCell baseJ) (ctlCell curJ))
        (Expr.const 0)).eval τ = writeReg τ (base + c) 0 := by
      rw [eval_assignInd]
      have e1 : (Expr.add (ctlCell baseJ) (ctlCell curJ)).eval τ = base + c := by
        simpa [Expr.eval] using haddr
      have e2 : (Expr.const 0).eval τ = 0 := by simp [Expr.eval]
      rw [e1, e2]
    set τ' := writeReg τ (base + c) 0 with hτ'def
    have hτ'0 : τ' 0 = M := by
      rw [hτ'def, writeReg_diff τ (base + c) 0 0 (by omega), h0]
    have hτ'b : τ' (M + baseJ) = base := by
      rw [hτ'def, writeReg_diff τ (base + c) 0 (M + baseJ) (by omega), hb]
    have hτ'c : τ' (M + curJ) = c := by
      rw [hτ'def, writeReg_diff τ (base + c) 0 (M + curJ) (by omega), hc]
    have hτ'zero : τ' (base + c) = 0 := by rw [hτ'def, writeReg_same]
    have hBeval : (ctlAssign curJ (Expr.add (ctlCell curJ) (Expr.const 1))).eval τ' =
        writeReg τ' (M + curJ) (c + 1) := by
      unfold ctlAssign
      rw [eval_assignInd]
      have e1 : (ctlAddr curJ).eval τ' = M + curJ := by rw [ctlAddr_eval, hτ'0]
      have e2 : (Expr.add (ctlCell curJ) (Expr.const 1)).eval τ' = c + 1 := by
        have hc' : (ctlCell curJ).eval τ' = c := by rw [ctlCell_eval, hτ'0, hτ'c]
        simpa [Expr.eval] using hc'
      rw [e1, e2]
    set τ1 := (zeroRangeBody baseJ curJ).eval τ with hτ1def
    have hτ1eq : τ1 = writeReg τ' (M + curJ) (c + 1) := by
      rw [hτ1def]
      unfold zeroRangeBody
      rw [eval_seq, hAeval, hBeval]
    have hτ10 : τ1 0 = M := by
      rw [hτ1eq, writeReg_diff τ' (M + curJ) (c + 1) 0 (by omega), hτ'0]
    have hτ1b : τ1 (M + baseJ) = base := by
      rw [hτ1eq, writeReg_diff τ' (M + curJ) (c + 1) (M + baseJ) (by omega), hτ'b]
    have hτ1c : τ1 (M + curJ) = c + 1 := by
      rw [hτ1eq, writeReg_same]
    have hτ1zero : τ1 (base + c) = 0 := by
      rw [hτ1eq, writeReg_diff τ' (M + curJ) (c + 1) (base + c) (by omega), hτ'zero]
    obtain ⟨hf0, hfb, hfc, hfzero, hfframe⟩ := ih (c + 1) τ1 hτ10 hτ1b hτ1c
    have hloopstep : loopEval (zeroRangeBody baseJ curJ) (t + 1) τ =
        loopEval (zeroRangeBody baseJ curJ) t τ1 := by
      rw [loopEval_succ]
    rw [hloopstep]
    refine ⟨hf0, hfb, by rw [hfc]; omega, ?_, ?_⟩
    · intro q hq
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        have heq := hfframe (base + c) (by omega) (Or.inl (by omega))
        simpa using heq.trans hτ1zero
      · have hlt : q - 1 < t := by omega
        have heq := hfzero (q - 1) hlt
        have hidx : base + (c + 1) + (q - 1) = base + c + q := by omega
        rwa [hidx] at heq
    · intro r hr hrange
      rcases hrange with hlt | hge
      · have hne : r ≠ base + c := by omega
        have hcond : r < base + (c + 1) ∨ base + (c + 1) + t ≤ r := Or.inl (by omega)
        have heq := hfframe r hr hcond
        rw [heq, hτ1eq, writeReg_diff τ' (M + curJ) (c + 1) r hr, hτ'def,
          writeReg_diff τ (base + c) 0 r hne]
      · have hne : r ≠ base + c := by omega
        have hcond : r < base + (c + 1) ∨ base + (c + 1) + t ≤ r := Or.inr (by omega)
        have heq := hfframe r hr hcond
        rw [heq, hτ1eq, writeReg_diff τ' (M + curJ) (c + 1) r hr, hτ'def,
          writeReg_diff τ (base + c) 0 r hne]

/-- `zeroRangeProg`'s effect unfolds to a fixed number (`len`, the value in the
    length control cell right after the cursor reset) of `zeroRangeBody`
    iterations, starting from cursor `0`. -/
lemma zeroRangeProg_eval_eq (baseJ lenJ curJ M len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hlc : lenJ ≠ curJ) (hM : σ 0 = M) (hlen : σ (M + lenJ) = len) :
    (zeroRangeProg baseJ lenJ curJ).eval σ =
      loopEval (zeroRangeBody baseJ curJ) len (writeReg σ (M + curJ) 0) := by
  have hσ1 : (ctlAssign curJ (Expr.const 0)).eval σ = writeReg σ (M + curJ) 0 := by
    unfold ctlAssign
    rw [eval_assignInd]
    have e1 : (ctlAddr curJ).eval σ = M + curJ := by rw [ctlAddr_eval, hM]
    have e2 : (Expr.const 0).eval σ = 0 := by simp [Expr.eval]
    rw [e1, e2]
  set σ1 := writeReg σ (M + curJ) 0 with hσ1def
  have hσ10 : σ1 0 = M := by
    rw [hσ1def, writeReg_diff σ (M + curJ) 0 0 (by omega), hM]
  have hσ1len : σ1 (M + lenJ) = len := by
    rw [hσ1def, writeReg_diff σ (M + curJ) 0 (M + lenJ) (by omega), hlen]
  have hbound : (ctlCell lenJ).eval σ1 = len := by
    rw [ctlCell_eval, hσ10, hσ1len]
  unfold zeroRangeProg
  rw [eval_seq, hσ1, eval_forN, hbound]

lemma zeroRangeProg_zeroed (baseJ lenJ curJ M base len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hlen : σ (M + lenJ) = len)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base) :
    ∀ q, q < len → (zeroRangeProg baseJ lenJ curJ).eval σ (base + q) = 0 := by
  rw [zeroRangeProg_eval_eq baseJ lenJ curJ M len σ hc1 hlc hM hlen]
  set τ := writeReg σ (M + curJ) 0 with hτdef
  have hτ0 : τ 0 = M := by rw [hτdef, writeReg_diff σ (M + curJ) 0 0 (by omega), hM]
  have hτb : τ (M + baseJ) = base := by
    rw [hτdef, writeReg_diff σ (M + curJ) 0 (M + baseJ) (by omega), hbase]
  have hτc : τ (M + curJ) = 0 := by rw [hτdef, writeReg_same]
  obtain ⟨_, _, _, hzeroed, _⟩ :=
    zeroRangeBody_loop_invariant baseJ curJ M base hc1 hbc hsepB hsepC len 0 τ hτ0 hτb hτc
  intro q hq
  simpa using hzeroed q hq

lemma zeroRangeProg_frame (baseJ lenJ curJ M base len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hlen : σ (M + lenJ) = len)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base) :
    ∀ r, (r < base ∨ base + len ≤ r) → r ≠ M + curJ →
      (zeroRangeProg baseJ lenJ curJ).eval σ r = σ r := by
  rw [zeroRangeProg_eval_eq baseJ lenJ curJ M len σ hc1 hlc hM hlen]
  set τ := writeReg σ (M + curJ) 0 with hτdef
  have hτ0 : τ 0 = M := by rw [hτdef, writeReg_diff σ (M + curJ) 0 0 (by omega), hM]
  have hτb : τ (M + baseJ) = base := by
    rw [hτdef, writeReg_diff σ (M + curJ) 0 (M + baseJ) (by omega), hbase]
  have hτc : τ (M + curJ) = 0 := by rw [hτdef, writeReg_same]
  obtain ⟨_, _, _, _, hframe⟩ :=
    zeroRangeBody_loop_invariant baseJ curJ M base hc1 hbc hsepB hsepC len 0 τ hτ0 hτb hτc
  intro r hrange hr
  have hcond : r < base + 0 ∨ base + 0 + len ≤ r := by
    rcases hrange with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [hframe r hr hcond, hτdef, writeReg_diff σ (M + curJ) 0 r hr]

lemma zeroRangeProg_ctl (baseJ lenJ curJ M base len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hlen : σ (M + lenJ) = len)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base) :
    (zeroRangeProg baseJ lenJ curJ).eval σ 0 = M := by
  rw [zeroRangeProg_eval_eq baseJ lenJ curJ M len σ hc1 hlc hM hlen]
  set τ := writeReg σ (M + curJ) 0 with hτdef
  have hτ0 : τ 0 = M := by rw [hτdef, writeReg_diff σ (M + curJ) 0 0 (by omega), hM]
  have hτb : τ (M + baseJ) = base := by
    rw [hτdef, writeReg_diff σ (M + curJ) 0 (M + baseJ) (by omega), hbase]
  have hτc : τ (M + curJ) = 0 := by rw [hτdef, writeReg_same]
  obtain ⟨h0, _, _, _, _⟩ :=
    zeroRangeBody_loop_invariant baseJ curJ M base hc1 hbc hsepB hsepC len 0 τ hτ0 hτb hτc
  exact h0

/-! ## Writing a bit string to the output cursor

The finalize phase's other job — after zeroing scratch space — is emitting the
answer bits themselves at the canonical output addresses. `BitsAt` recognizes a
run of cells as holding a `Bits` value; `emitBitProg` writes one bit at the
run-time output cursor and advances it; `emitNatProg` (further below) repeats
this to lay down a whole `encodeNat` value. -/

/-- `σ` holds `bits` as 0/1 cells starting at `addr`. -/
def BitsAt (σ : Store) (addr : ℕ) (bits : Bits) : Prop :=
  ∀ i, (h : i < bits.length) → σ (addr + i) = if bits[i] then 1 else 0

lemma bitsAt_nil (σ : Store) (addr : ℕ) : BitsAt σ addr [] := by
  intro i h
  simp at h

/-- Splitting a `BitsAt` run at the boundary between two concatenated pieces:
    used to assemble the correctness of a multi-bit emitter from its per-piece
    emitters. -/
lemma bitsAt_append (σ : Store) (addr : ℕ) (l1 l2 : Bits) :
    BitsAt σ addr (l1 ++ l2) ↔ BitsAt σ addr l1 ∧ BitsAt σ (addr + l1.length) l2 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i < (l1 ++ l2).length := by simp; omega
      have heq := h i hi'
      simpa [List.getElem_append_left hi] using heq
    · have hi' : l1.length + i < (l1 ++ l2).length := by simp; omega
      have heq := h (l1.length + i) hi'
      have hidx : addr + (l1.length + i) = addr + l1.length + i := by ring
      rw [hidx] at heq
      simpa [List.getElem_append_right (Nat.le_add_right l1.length i)] using heq
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge i l1.length with hlt | hge
    · simpa [List.getElem_append_left hlt] using h1 i hlt
    · have hi2 : i - l1.length < l2.length := by simp at hi; omega
      have heq := h2 (i - l1.length) hi2
      have hidx : addr + l1.length + (i - l1.length) = addr + i := by omega
      rw [hidx] at heq
      simpa [List.getElem_append_right hge] using heq

/-- A `BitsAt` run survives replacing the store by one that agrees with it on the
    run's cells — the frame lemma needed to hand a `BitsAt` fact from an
    intermediate store to the final store of a longer program. -/
lemma bitsAt_of_frame (σ σ' : Store) (addr : ℕ) (bits : Bits) (h : BitsAt σ addr bits)
    (hframe : ∀ r, addr ≤ r → r < addr + bits.length → σ' r = σ r) :
    BitsAt σ' addr bits := by
  intro i hi
  rw [hframe (addr + i) (by omega) (by omega)]
  exact h i hi

/-! ## Emitting one bit at the output cursor

`emitBitProg` writes `v` at the cell the cursor (control cell `curJ`) currently
points to, then advances the cursor by one. Both address and value in the write
are evaluated against the *pre-write* store (per `Program.eval`'s `assignInd`
semantics), so `v` may read any cell — including the one just about to be
overwritten — without a staging concern; the only hazards are positional: the
write target `cur` must not collide with cell `0` (which holds `M`) or with the
cursor cell itself (`M + curJ`), since those are read again by the second
statement. -/

/-- Write one bit (`v`, evaluating to 0 or 1) at the output cursor held in control
    cell `curJ`, then advance the cursor by one. -/
def emitBitProg (curJ : ℕ) (v : Expr) : Program :=
  .seq (.assignInd (ctlCell curJ) v) (ctlAssign curJ (.add (ctlCell curJ) (.const 1)))

/-- Unfolds `emitBitProg`'s net effect on the store: write `v.eval σ` at the cell
    `cur` the cursor pointed to, then set the cursor cell to `cur + 1`. The four
    lemmas below are corollaries reading off one cell each. -/
lemma emitBitProg_eval_eq (curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur)
    (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ) :
    (emitBitProg curJ v).eval σ = writeReg (writeReg σ cur (v.eval σ)) (M + curJ) (cur + 1) := by
  unfold emitBitProg
  rw [eval_seq]
  have hwaddr : (ctlCell curJ).eval σ = cur := by rw [ctlCell_eval, hM, hcur]
  have h1 : (Program.assignInd (ctlCell curJ) v).eval σ = writeReg σ cur (v.eval σ) := by
    rw [eval_assignInd, hwaddr]
  rw [h1]
  set σ1 := writeReg σ cur (v.eval σ) with hσ1def
  have hσ10 : σ1 0 = M := by rw [hσ1def, writeReg_diff σ cur (v.eval σ) 0 (Ne.symm hcur0), hM]
  have hσ1cur : σ1 (M + curJ) = cur := by
    rw [hσ1def, writeReg_diff σ cur (v.eval σ) (M + curJ) (Ne.symm hne), hcur]
  have haddr2 : (ctlAddr curJ).eval σ1 = M + curJ := by rw [ctlAddr_eval, hσ10]
  unfold ctlAssign
  rw [eval_assignInd, haddr2]
  have hval : (Expr.add (ctlCell curJ) (Expr.const 1)).eval σ1 = cur + 1 := by
    simp [Expr.eval, ctlCell_eval, hσ10, hσ1cur]
  rw [hval]

/-- The write target cell ends up holding `v.eval σ`. -/
lemma emitBitProg_eval_cell (curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur)
    (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ) :
    ((emitBitProg curJ v).eval σ) cur = v.eval σ := by
  rw [emitBitProg_eval_eq curJ M cur v σ hM hcur hcur0 hne,
    writeReg_diff _ (M + curJ) (cur + 1) cur hne, writeReg_same]

/-- The cursor cell advances from `cur` to `cur + 1`. -/
lemma emitBitProg_cursor (curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur)
    (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ) :
    ((emitBitProg curJ v).eval σ) (M + curJ) = cur + 1 := by
  rw [emitBitProg_eval_eq curJ M cur v σ hM hcur hcur0 hne, writeReg_same]

/-- Every cell other than the write target and the cursor cell is untouched. -/
lemma emitBitProg_frame (curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur)
    (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ) :
    ∀ r, r ≠ cur → r ≠ M + curJ → ((emitBitProg curJ v).eval σ) r = σ r := by
  intro r hr1 hr2
  rw [emitBitProg_eval_eq curJ M cur v σ hM hcur hcur0 hne,
    writeReg_diff _ (M + curJ) (cur + 1) r hr2, writeReg_diff σ cur (v.eval σ) r hr1]

/-- Cell `0` (holding `M`) is preserved: it differs from both the write target
    (`hcur0`) and the cursor cell, the latter needing `1 ≤ curJ` to keep
    `M + curJ` away from `0`. -/
lemma emitBitProg_ctl (curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hc1 : 1 ≤ curJ) (hM : σ 0 = M) (hcur : σ (M + curJ) = cur)
    (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ) :
    ((emitBitProg curJ v).eval σ) 0 = M := by
  rw [emitBitProg_frame curJ M cur v σ hM hcur hcur0 hne 0 (Ne.symm hcur0) (by omega), hM]

/-- Loop invariant for `t` repetitions of `emitBitProg curJ (.const 0)` (the
    zero-bit body used by `emitNatProg`'s main loop): tracked from a store where
    the cursor cell already reads `c`, provided the whole eventual write window
    `[c, c + t)` and the cursor cell `M + curJ` never collide (`c + t < M + curJ`,
    which also keeps every visited cursor value `≥ 1` away from cell `0`). The
    root cell is preserved, the cursor advances to `c + t`, the window is zeroed,
    and every cell outside the window and the cursor cell is left untouched — the
    shape mirrors `zeroRangeBody_loop_invariant`, minus the extra `base` offset
    since `emitBitProg` writes directly at the cursor value. -/
lemma emit_zero_loop_invariant (curJ M : ℕ) (hc1 : 1 ≤ curJ) :
    ∀ t c (τ : Store), τ 0 = M → τ (M + curJ) = c → 1 ≤ c → c + t < M + curJ →
      (loopEval (emitBitProg curJ (Expr.const 0)) t τ) 0 = M ∧
      (loopEval (emitBitProg curJ (Expr.const 0)) t τ) (M + curJ) = c + t ∧
      (∀ q, q < t → (loopEval (emitBitProg curJ (Expr.const 0)) t τ) (c + q) = 0) ∧
      (∀ r, r ≠ M + curJ → (r < c ∨ c + t ≤ r) →
        (loopEval (emitBitProg curJ (Expr.const 0)) t τ) r = τ r) := by
  intro t
  induction t with
  | zero =>
      intro c τ h0 hc hcpos hsep
      rw [loopEval_zero]
      exact ⟨h0, by omega, fun q hq => absurd hq (by omega), fun r _ _ => rfl⟩
  | succ t ih =>
      intro c τ h0 hc hcpos hsep
      have hne : c ≠ M + curJ := by omega
      have hcur0 : c ≠ 0 := by omega
      set τ1 := (emitBitProg curJ (Expr.const 0)).eval τ with hτ1def
      have hτ1eq : τ1 = writeReg (writeReg τ c 0) (M + curJ) (c + 1) := by
        rw [hτ1def]
        have heq := emitBitProg_eval_eq curJ M c (Expr.const 0) τ h0 hc hcur0 hne
        simpa [Expr.eval] using heq
      have hτ10 : τ1 0 = M := by
        rw [hτ1eq, writeReg_diff _ (M + curJ) (c + 1) 0 (by omega),
          writeReg_diff τ c 0 0 (Ne.symm hcur0), h0]
      have hτ1c : τ1 (M + curJ) = c + 1 := by rw [hτ1eq, writeReg_same]
      have hτ1zero : τ1 c = 0 := by
        rw [hτ1eq, writeReg_diff _ (M + curJ) (c + 1) c hne, writeReg_same]
      have hsep' : (c + 1) + t < M + curJ := by omega
      obtain ⟨hf0, hfc, hfzero, hfframe⟩ := ih (c + 1) τ1 hτ10 hτ1c (by omega) hsep'
      have hloopstep : loopEval (emitBitProg curJ (Expr.const 0)) (t + 1) τ
          = loopEval (emitBitProg curJ (Expr.const 0)) t τ1 := by rw [loopEval_succ]
      rw [hloopstep]
      refine ⟨hf0, by rw [hfc]; omega, ?_, ?_⟩
      · intro q hq
        rcases Nat.eq_zero_or_pos q with hq0 | hqpos
        · subst hq0
          have heq := hfframe c (by omega) (Or.inl (by omega))
          simpa using heq.trans hτ1zero
        · have hlt : q - 1 < t := by omega
          have heq := hfzero (q - 1) hlt
          have hidx : (c + 1) + (q - 1) = c + q := by omega
          rwa [hidx] at heq
      · intro r hr hrange
        rcases hrange with hlt | hge
        · have hcond : r < c + 1 ∨ c + 1 + t ≤ r := Or.inl (by omega)
          have heq := hfframe r hr hcond
          rw [heq, hτ1eq, writeReg_diff _ (M + curJ) (c + 1) r hr,
            writeReg_diff τ c 0 r (by omega)]
        · have hcond : r < c + 1 ∨ c + 1 + t ≤ r := Or.inr (by omega)
          have heq := hfframe r hr hcond
          rw [heq, hτ1eq, writeReg_diff _ (M + curJ) (c + 1) r hr,
            writeReg_diff τ c 0 r (by omega)]

open NPComplete.BitEncoding (encodeNat encodeNat_succ)

/-! ## Emitting a whole unary `Nat`

`emitNatProg` repeats `emitBitProg` to lay down `encodeNat n` at the output
cursor for a run-time value `n := e.eval σ`: it stages `n` into control cell
`tmpJ` first (so the loop bound does not depend on cells the loop body
writes), zeros out `n` bits at the cursor via `emit_zero_loop_invariant`, then
emits the terminating `1` bit. -/

/-- Emit `encodeNat n` (`n` zero bits then a one) at the output cursor, where `n`
    is staged into control cell `tmpJ` first so the loop bound does not depend on
    cells the loop writes. -/
def emitNatProg (curJ tmpJ : ℕ) (e : Expr) : Program :=
  .seq (ctlAssign tmpJ e)
    (.seq (.forN (ctlCell tmpJ) (emitBitProg curJ (.const 0)))
      (emitBitProg curJ (.const 1)))

/-- `encodeNat n` is `n` zero bits followed by a terminating one — the shape
    `bitsAt_encodeNat` reads off cell-by-cell from a zeroed window and a
    trailing `1`. -/
lemma encodeNat_eq_replicate_append (n : ℕ) :
    encodeNat n = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [encodeNat_succ, ih]; simp [List.replicate_succ]

/-- A zeroed window `[cur, cur + n)` followed by a `1` at `cur + n` is exactly
    `encodeNat n` — the store-level counterpart of `encodeNat_eq_replicate_append`,
    used to assemble `emitNatProg`'s correctness from its zero-loop and
    terminal-bit facts. -/
lemma bitsAt_encodeNat (σ : Store) (cur n : ℕ)
    (hzero : ∀ q, q < n → σ (cur + q) = 0) (hone : σ (cur + n) = 1) :
    BitsAt σ cur (encodeNat n) := by
  rw [encodeNat_eq_replicate_append, bitsAt_append]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hilt : i < n := by simpa using hi
    rw [List.getElem_replicate]
    simpa using hzero i hilt
  · have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    have hidx : cur + (List.replicate n false).length + 0 = cur + n := by simp
    rw [hidx]
    simpa using hone

/-- Bundled correctness of `emitNatProg`, proved in one pass since the four facts
    share the same three-stage store unfolding: stage `n` into `tmpJ`, run the
    zero-bit loop (`emit_zero_loop_invariant`) to zero `[cur, cur + n)` and advance
    the cursor to `cur + n`, then emit the terminating `1` bit. -/
lemma emitNatProg_eval_state (curJ tmpJ M cur : ℕ) (e : Expr) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hsep : cur + e.eval σ < M + curJ) :
    BitsAt ((emitNatProg curJ tmpJ e).eval σ) cur (encodeNat (e.eval σ)) ∧
    ((emitNatProg curJ tmpJ e).eval σ) (M + curJ) = cur + e.eval σ + 1 ∧
    (∀ r, r ≠ M + curJ → r ≠ M + tmpJ →
      (r < cur ∨ cur + e.eval σ + 1 ≤ r) →
      ((emitNatProg curJ tmpJ e).eval σ) r = σ r) ∧
    ((emitNatProg curJ tmpJ e).eval σ) 0 = M := by
  set n := e.eval σ with hndef
  have hσ1val : (ctlAssign tmpJ e).eval σ (M + tmpJ) = n := by
    have h := ctlAssign_eval_same tmpJ e σ
    rw [hM] at h
    rw [h, ← hndef]
  have hσ10 : (ctlAssign tmpJ e).eval σ 0 = M := by
    rw [ctlAssign_zero tmpJ e σ hc2, hM]
  have hσ1cur : (ctlAssign tmpJ e).eval σ (M + curJ) = cur := by
    have hne : M + curJ ≠ σ 0 + tmpJ := by rw [hM]; omega
    rw [ctlAssign_eval_diff tmpJ e σ (M + curJ) hne, hcur]
  have hσ1frame : ∀ r, r ≠ M + tmpJ → (ctlAssign tmpJ e).eval σ r = σ r := by
    intro r hr
    exact ctlAssign_eval_diff tmpJ e σ r (by rw [hM]; exact hr)
  set σ1 := (ctlAssign tmpJ e).eval σ with hσ1def
  have hbound : (ctlCell tmpJ).eval σ1 = n := by rw [ctlCell_eval, hσ10, hσ1val]
  have hforNeval : (Program.forN (ctlCell tmpJ) (emitBitProg curJ (Expr.const 0))).eval σ1
      = loopEval (emitBitProg curJ (Expr.const 0)) n σ1 := by
    rw [eval_forN, hbound]
  obtain ⟨hσ2_0, hσ2cur, hσ2zero, hσ2frame⟩ :=
    emit_zero_loop_invariant curJ M hc1 n cur σ1 hσ10 hσ1cur hcur1 hsep
  set σ2 := loopEval (emitBitProg curJ (Expr.const 0)) n σ1 with hσ2def
  have hcurn0 : cur + n ≠ 0 := by omega
  have hcurnne : cur + n ≠ M + curJ := by omega
  have hσ3cell : (emitBitProg curJ (Expr.const 1)).eval σ2 (cur + n) = 1 := by
    have h := emitBitProg_eval_cell curJ M (cur + n) (Expr.const 1) σ2 hσ2_0 hσ2cur hcurn0 hcurnne
    simpa [Expr.eval] using h
  have hσ3cursor : (emitBitProg curJ (Expr.const 1)).eval σ2 (M + curJ) = cur + n + 1 :=
    emitBitProg_cursor curJ M (cur + n) (Expr.const 1) σ2 hσ2_0 hσ2cur hcurn0 hcurnne
  have hσ3frame : ∀ r, r ≠ cur + n → r ≠ M + curJ →
      (emitBitProg curJ (Expr.const 1)).eval σ2 r = σ2 r :=
    emitBitProg_frame curJ M (cur + n) (Expr.const 1) σ2 hσ2_0 hσ2cur hcurn0 hcurnne
  have hσ3ctl : (emitBitProg curJ (Expr.const 1)).eval σ2 0 = M :=
    emitBitProg_ctl curJ M (cur + n) (Expr.const 1) σ2 hc1 hσ2_0 hσ2cur hcurn0 hcurnne
  set σ3 := (emitBitProg curJ (Expr.const 1)).eval σ2 with hσ3def
  have hntop : (emitNatProg curJ tmpJ e).eval σ = σ3 := by
    unfold emitNatProg
    rw [eval_seq, eval_seq, ← hσ1def, hforNeval]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hntop]
    apply bitsAt_encodeNat
    · intro q hq
      rw [hσ3frame (cur + q) (by omega) (by omega)]
      exact hσ2zero q hq
    · exact hσ3cell
  · rw [hntop]; exact hσ3cursor
  · intro r hrM hrtmp hrange
    rw [hntop]
    have hrcurn : r ≠ cur + n := by rcases hrange with h | h <;> omega
    have h1 := hσ3frame r hrcurn hrM
    have hrange2 : r < cur ∨ cur + n ≤ r := by rcases hrange with h | h <;> omega
    have h2 := hσ2frame r hrM hrange2
    have h3 := hσ1frame r hrtmp
    rw [h1, h2, h3]
  · rw [hntop]; exact hσ3ctl

/-! ## A generic emit-loop induction principle

Every length-prefixed table field in the canonical bit encoding
(`encodeList enc l = encodeNat l.length ++ (l.map enc).flatten`) has the same two-part shape:
a unary length prefix, then a loop emitting one list element per iteration.
`emit_loop_flatMap` factors the "loop of `n` iterations, each emitting a declaratively-specified
chunk `f m` and advancing the cursor by its length" argument into a single reusable induction,
so a concrete table's correctness proof only has to supply the per-iteration spec `hbody` instead
of re-deriving the whole loop unfolding.

The start index `k` is generalized rather than fixed at `0`, because the induction peels one
iteration off the *front* at each step (mirroring `zeroRangeBody_loop_invariant`'s cursor
generalization) — the caller instantiates `k := 0`. `Inv` lets a per-iteration spec depend on how
many iterations have already run; it is trivial (`fun _ _ => True`) whenever `f`'s pieces do not
depend on prior iterations. The separation hypothesis bounds the *whole* remaining emitted region
against the cursor register `M + curJ` — mirroring `emitNatProg`'s `hsep` — because a per-iteration
bound alone would not rule out the write window drifting into the cursor cell over many
iterations. The frame conclusion only protects cells strictly below the entry cursor (never above
the written window), which is exactly the direction needed to chain multiple emit calls: each
later call's frame shows the earlier calls' output survives, since later cursors only grow. -/

lemma emit_loop_flatMap (curJ M : ℕ) (body : Program) (f : ℕ → Bits)
    (Inv : ℕ → Store → Prop) (n : ℕ)
    (hbody : ∀ m, m < n → ∀ τ cur, Inv m τ → τ 0 = M → τ (M + curJ) = cur →
      BitsAt (body.eval τ) cur (f m) ∧
      (body.eval τ) (M + curJ) = cur + (f m).length ∧
      (body.eval τ) 0 = M ∧
      (∀ r, r < cur → r ≠ M + curJ → (body.eval τ) r = τ r) ∧
      Inv (m + 1) (body.eval τ)) :
    ∀ (t k : ℕ), k + t ≤ n → ∀ (τ : Store) (cur : ℕ), Inv k τ → τ 0 = M → τ (M + curJ) = cur →
      cur + ((List.range' k t).flatMap f).length ≤ M + curJ →
      BitsAt (loopEval body t τ) cur ((List.range' k t).flatMap f) ∧
      (loopEval body t τ) (M + curJ) = cur + ((List.range' k t).flatMap f).length ∧
      (loopEval body t τ) 0 = M ∧
      Inv (k + t) (loopEval body t τ) ∧
      (∀ r, r < cur → r ≠ M + curJ → (loopEval body t τ) r = τ r) := by
  intro t
  induction t with
  | zero =>
    intro k hk τ cur hInv h0 hcur hsep
    rw [loopEval_zero]
    refine ⟨?_, by simpa using hcur, h0, by simpa using hInv, fun r _ _ => rfl⟩
    simpa using bitsAt_nil τ cur
  | succ t ih =>
    intro k hk τ cur hInv h0 hcur hsep
    have hkn : k < n := by omega
    obtain ⟨hbits, hcursor, h0', hframe, hInv'⟩ := hbody k hkn τ cur hInv h0 hcur
    have hrange' : List.range' k (t + 1) = k :: List.range' (k + 1) t := by
      rw [List.range'_succ]
    have hflat : (List.range' k (t + 1)).flatMap f = f k ++ (List.range' (k + 1) t).flatMap f := by
      rw [hrange', List.flatMap_cons]
    have hlen : ((List.range' k (t + 1)).flatMap f).length
        = (f k).length + ((List.range' (k + 1) t).flatMap f).length := by
      rw [hflat, List.length_append]
    have hsepk : cur + (f k).length ≤ M + curJ := by omega
    have hk1t : (k + 1) + t ≤ n := by omega
    have hsep' : (cur + (f k).length) + ((List.range' (k + 1) t).flatMap f).length ≤ M + curJ := by
      omega
    obtain ⟨hbits2, hcursor2, h0'2, hInv2, hframe2⟩ :=
      ih (k + 1) hk1t (body.eval τ) (cur + (f k).length) hInv' h0' hcursor hsep'
    have hloopstep : loopEval body (t + 1) τ = loopEval body t (body.eval τ) :=
      loopEval_succ body t τ
    rw [hloopstep]
    refine ⟨?_, ?_, h0'2, ?_, ?_⟩
    · rw [hflat, bitsAt_append]
      refine ⟨?_, hbits2⟩
      intro i hi
      have hilt : cur + i < cur + (f k).length := by omega
      have hne : cur + i ≠ M + curJ := by omega
      rw [hframe2 (cur + i) hilt hne]
      exact hbits i hi
    · rw [hcursor2, hlen]; omega
    · have hkeq : k + (t + 1) = (k + 1) + t := by omega
      rw [hkeq]; exact hInv2
    · intro r hr hrne
      have hr1 : r < cur + (f k).length := by omega
      rw [hframe2 r hr1 hrne]
      exact hframe r hr hrne

/-! ## `encodeList`-shaped emission: length prefix then a loop

`emitListProg` composes `emitNatProg` (the unary length prefix) with a `forN` loop reading its
iteration bound from the same control cell (`cntJ`) the caller staged the count into beforehand —
mirroring `zeroRangeProg`'s "stage the bound in a control cell, iterate a bounded loop" pattern.
Because `forN`'s iteration count is read once at loop entry (`Program.eval`'s `forN` case unfolds
to `loopEval body (n.eval σ) σ`), `body` is free to disturb `cntJ` without affecting how many
iterations run, exactly as `zeroRangeProg`'s module comment notes for its own length cell. -/

/-- Emit `encodeList`-shaped output: the element count in unary, then the elements. -/
def emitListProg (curJ tmpJ cntJ : ℕ) (body : Program) : Program :=
  .seq (emitNatProg curJ tmpJ (ctlCell cntJ)) (.forN (ctlCell cntJ) body)

open NPComplete.BitEncoding (encodeNat_length)

/-- Bundled correctness of `emitListProg`: the store after running it holds
    `encodeNat n ++ (List.range n).flatMap f` at the entry cursor, the cursor has advanced past
    the whole emission, cell `0` still holds `M`, and the per-iteration invariant has reached its
    final index `n`. Proved by chaining `emitNatProg_eval_state` (the length prefix) with
    `emit_loop_flatMap` (the loop), so the per-element spec `hbody` is the only fact a caller has
    to supply. -/
lemma emitListProg_eval_state (curJ tmpJ cntJ M cur n : ℕ) (body : Program) (f : ℕ → Bits)
    (Inv : ℕ → Store → Prop) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hcnt : σ (M + cntJ) = n)
    (hsepCnt : cur + n + 1 ≤ M + cntJ)
    (hsepFull : cur + n + 1 + ((List.range n).flatMap f).length ≤ M + curJ)
    (hbody : ∀ m, m < n → ∀ τ cur', Inv m τ → τ 0 = M → τ (M + curJ) = cur' →
      BitsAt (body.eval τ) cur' (f m) ∧
      (body.eval τ) (M + curJ) = cur' + (f m).length ∧
      (body.eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ → (body.eval τ) r = τ r) ∧
      Inv (m + 1) (body.eval τ))
    (hInv0 : Inv 0 ((emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ)) :
    BitsAt ((emitListProg curJ tmpJ cntJ body).eval σ) cur
      (encodeNat n ++ (List.range n).flatMap f) ∧
    ((emitListProg curJ tmpJ cntJ body).eval σ) (M + curJ)
      = cur + n + 1 + ((List.range n).flatMap f).length ∧
    ((emitListProg curJ tmpJ cntJ body).eval σ) 0 = M ∧
    Inv n ((emitListProg curJ tmpJ cntJ body).eval σ) := by
  have hcntEval : (ctlCell cntJ).eval σ = n := by rw [ctlCell_eval, hM, hcnt]
  have hsep' : cur + (ctlCell cntJ).eval σ < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1 hsep'
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ with hσ1def
  have hInv0' : Inv 0 σ1 := hInv0
  have hσ1cnt : σ1 (M + cntJ) = n := by
    rw [hframe1 (M + cntJ) (by omega) (by omega) (Or.inr hsepCnt), hcnt]
  have hbound : (ctlCell cntJ).eval σ1 = n := by rw [ctlCell_eval, hctl1, hσ1cnt]
  have hforNeval : (Program.forN (ctlCell cntJ) body).eval σ1 = loopEval body n σ1 := by
    rw [eval_forN, hbound]
  have hrangeeq : List.range' 0 n = List.range n := by rw [List.range_eq_range']
  have hsepLoop : cur + n + 1 + ((List.range' 0 n).flatMap f).length ≤ M + curJ := by
    rw [hrangeeq]; exact hsepFull
  obtain ⟨hbits2, hcursor2, hctl2, hInvn, hframe2⟩ :=
    emit_loop_flatMap curJ M body f Inv n hbody n 0 (by omega) σ1 (cur + n + 1)
      hInv0' hctl1 hcursor1 hsepLoop
  rw [hrangeeq] at hbits2 hcursor2
  rw [Nat.zero_add] at hInvn
  have htop : (emitListProg curJ tmpJ cntJ body).eval σ = loopEval body n σ1 := by
    unfold emitListProg
    rw [eval_seq, ← hσ1def, hforNeval]
  have hcurJfar : cur + n + 1 ≤ M + curJ := by
    have hnn : (0 : ℕ) ≤ ((List.range n).flatMap f).length := Nat.zero_le _
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htop]
    have hwin : ∀ r, cur ≤ r → r < cur + (encodeNat n).length → (loopEval body n σ1) r = σ1 r := by
      intro r hr1 hr2
      rw [encodeNat_length] at hr2
      exact hframe2 r (by omega) (by omega)
    have hbitsL : BitsAt (loopEval body n σ1) cur (encodeNat n) :=
      bitsAt_of_frame σ1 (loopEval body n σ1) cur (encodeNat n) hbits1 hwin
    have haddr : cur + (encodeNat n).length = cur + n + 1 := by rw [encodeNat_length]; omega
    rw [bitsAt_append, haddr]
    exact ⟨hbitsL, hbits2⟩
  · rw [htop]; exact hcursor2
  · rw [htop]; exact hctl2
  · rw [htop]; exact hInvn

/-! ## Bridging `encodeList` to the `range`-indexed loop shape

`emitListProg_eval_state`'s conclusion is phrased over `(List.range n).flatMap f` because that is
the shape the induction (`emit_loop_flatMap`) naturally produces. `encodeList enc l`
(`BitEncoding.lean`) instead flattens `l.map enc`. `flatten_map_eq_range_flatMap` bridges the two:
re-indexing `l.map enc` by position via `List.getD` turns it into the same `range`-indexed
`flatMap` shape, so a concrete table's per-element spec can be read off as
`fun m => enc (l.getD m default)` and `emitListProg`'s correctness restated directly in terms of
`encodeList`. -/

lemma flatten_map_eq_range_flatMap {α : Type*} [Inhabited α] (enc : α → Bits) (l : List α) :
    (l.map enc).flatten = (List.range l.length).flatMap (fun m => enc (l.getD m default)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_cons, ih]
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.getD_cons_zero]
    rfl

open NPComplete.BitEncoding (encodeList)

/-! ## Zeroing all control cells in one pass

Once finalize's own control state (cursors, bases, lengths) is no longer needed, every control
cell `M + 1, M + 2, …` must itself be zeroed so the final store matches `bitInputStore
outputBits` cell-by-cell. `zeroCtlCellsProg` clears `M + 1 .. M + k` one cell at a time via
`ctlAssign`; since each write target `M + j` (`j ≥ 1`) can never coincide with cell `0`, the
value `M` sitting there is preserved throughout the whole pass regardless of the order cells are
cleared in — the same order-independence the dynamic-register convention was designed for. -/

/-- Zero control cells `M + 1 .. M + k` (cell `0`, holding `M`, stays intact and keeps
    addressing valid throughout). -/
def zeroCtlCellsProg : ℕ → Program
  | 0 => .skip
  | k + 1 => .seq (zeroCtlCellsProg k) (ctlAssign (k + 1) (.const 0))

/-- Bundled invariant for `zeroCtlCellsProg`, proved by a single induction on `k`: the root
    cell survives every zeroing pass (so `ctlAddr` stays valid throughout, regardless of the
    order cells are cleared in), the zeroed cells read `0`, and every cell outside the zeroed
    range is untouched — the corollaries below read off one fact each. -/
lemma zeroCtlCellsProg_invariant (M : ℕ) :
    ∀ k σ, σ 0 = M →
      (zeroCtlCellsProg k).eval σ 0 = M ∧
      (∀ j, 1 ≤ j → j ≤ k → (zeroCtlCellsProg k).eval σ (M + j) = 0) ∧
      (∀ r, (r < M + 1 ∨ M + k < r) → (zeroCtlCellsProg k).eval σ r = σ r) := by
  intro k
  induction k with
  | zero =>
    intro σ h0
    have hz : zeroCtlCellsProg 0 = Program.skip := rfl
    rw [hz, NPComplete.BoundedWhile.eval_skip]
    exact ⟨h0, fun j hj1 hj2 => absurd hj2 (by omega), fun r _ => rfl⟩
  | succ k ih =>
    intro σ h0
    obtain ⟨hctl, hzero, hframe⟩ := ih σ h0
    set τ := (zeroCtlCellsProg k).eval σ with hτdef
    have haddr : (ctlAddr (k + 1)).eval τ = M + (k + 1) := by
      rw [ctlAddr_eval, hctl]
    have hstep : (zeroCtlCellsProg (k + 1)).eval σ = writeReg τ (M + (k + 1)) 0 := by
      show (Program.seq (zeroCtlCellsProg k) (ctlAssign (k + 1) (Expr.const 0))).eval σ = _
      rw [eval_seq, ← hτdef]
      unfold ctlAssign
      rw [eval_assignInd, haddr]
      simp [Expr.eval]
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep, writeReg_diff _ _ _ 0 (by omega), hctl]
    · intro j hj1 hj2
      rw [hstep]
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · rw [writeReg_diff _ _ _ _ (by omega)]
        exact hzero j hj1 (by omega)
      · have : j = k + 1 := by omega
        rw [this, writeReg_same]
    · intro r hr
      rw [hstep, writeReg_diff _ _ _ r (by omega)]
      exact hframe r (by omega)

/-- Every zeroed control cell `M + j` (for `1 ≤ j ≤ k`) reads `0` after `zeroCtlCellsProg k`. -/
lemma zeroCtlCellsProg_zeroed (k : ℕ) (σ : Store) (M : ℕ) (h0 : σ 0 = M) :
    ∀ j, 1 ≤ j → j ≤ k → (zeroCtlCellsProg k).eval σ (M + j) = 0 :=
  (zeroCtlCellsProg_invariant M k σ h0).2.1

/-- Every cell outside the zeroed range `[M + 1, M + k]` is left untouched. -/
lemma zeroCtlCellsProg_frame (k : ℕ) (σ : Store) (M : ℕ) (h0 : σ 0 = M) :
    ∀ r, (r < M + 1 ∨ M + k < r) → (zeroCtlCellsProg k).eval σ r = σ r :=
  (zeroCtlCellsProg_invariant M k σ h0).2.2

/-- Cell `0` (holding `M`) is preserved, keeping `ctlAddr` valid throughout the pass. -/
lemma zeroCtlCellsProg_ctl (k : ℕ) (σ : Store) (M : ℕ) (h0 : σ 0 = M) :
    (zeroCtlCellsProg k).eval σ 0 = M :=
  (zeroCtlCellsProg_invariant M k σ h0).1

/-! ## Emitting a contiguous table of naturals in `encodeList` shape

Each scalar table is stored as a contiguous run of `Nat` ids, one cell per entry, at a run-time
base address held in control cell `tblJ`. `emitNatTableBody` reads the entry the run-time index
(`idxJ`) currently points to and emits it in unary, then advances the index;
`emitNatTableProg` resets the index to `0` and wraps the body in `emitListProg`, matching the
canonical "count, then elements" shape. -/

/-- One iteration: emit the table entry at `tbl + idx` in unary, then advance the index. -/
def emitNatTableBody (curJ tmpJ tblJ idxJ : ℕ) : Program :=
  .seq (emitNatProg curJ tmpJ (.regInd (.add (ctlCell tblJ) (ctlCell idxJ))))
    (ctlAssign idxJ (.add (ctlCell idxJ) (.const 1)))

/-- Emit a contiguous table of naturals in `encodeList` shape: the entry count in unary,
    then each entry in unary. -/
def emitNatTableProg (curJ tmpJ cntJ tblJ idxJ : ℕ) : Program :=
  .seq (ctlAssign idxJ (.const 0))
    (emitListProg curJ tmpJ cntJ (emitNatTableBody curJ tmpJ tblJ idxJ))

/-- Bundled correctness of one `emitNatTableBody` iteration: reading the table entry at
    `tbl + idx` (held via control cells `tblJ`/`idxJ`), emitting it in unary at the output
    cursor, then advancing `idxJ` to `idx + 1`. `hsepIdx`/`hsepTbl` keep the emitted window
    away from the two control cells the *next* iteration still needs to read correctly
    (`tmpJ`'s staging cell needs no such bound: nothing outside this one iteration ever reads
    it again). -/
lemma emitNatTableBody_eval_state (curJ tmpJ tblJ idxJ M cur tbl idx v : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (htblCell : σ (M + tblJ) = tbl) (hidxCell : σ (M + idxJ) = idx)
    (hentry : σ (tbl + idx) = v)
    (hsep : cur + v < M + curJ)
    (hsepIdx : cur + v + 1 ≤ M + idxJ) (hsepTbl : cur + v + 1 ≤ M + tblJ) :
    BitsAt ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) cur (encodeNat v) ∧
    ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) (M + curJ) = cur + v + 1 ∧
    ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) 0 = M ∧
    ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) (M + idxJ) = idx + 1 ∧
    ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) (M + tblJ) = tbl ∧
    (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + idxJ →
      (r < cur ∨ cur + v + 1 ≤ r) →
      ((emitNatTableBody curJ tmpJ tblJ idxJ).eval σ) r = σ r) := by
  have heval : (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))).eval σ = v := by
    have h1 : (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))).eval σ
        = σ (σ (σ 0 + tblJ) + σ (σ 0 + idxJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, htblCell, hidxCell]
    exact hentry
  have hsep' : cur + (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))).eval σ < M + curJ := by
    rw [heval]; exact hsep
  obtain ⟨hbits, hcursor, hframe, hctl⟩ := emitNatProg_eval_state curJ tmpJ M cur
    (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))) σ hc1 hc2 hct hM hcur hcur1 hsep'
  rw [heval] at hbits hcursor hframe
  set σ1 := (emitNatProg curJ tmpJ (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ)))).eval σ
    with hσ1def
  have hσ1idx : σ1 (M + idxJ) = idx := by
    rw [hframe (M + idxJ) (by omega) (by omega) (Or.inr hsepIdx), hidxCell]
  have hσ1tbl : σ1 (M + tblJ) = tbl := by
    rw [hframe (M + tblJ) (by omega) (by omega) (Or.inr hsepTbl), htblCell]
  have haddr : (ctlAddr idxJ).eval σ1 = M + idxJ := by rw [ctlAddr_eval, hctl]
  have hAeval : (ctlAssign idxJ (Expr.add (ctlCell idxJ) (Expr.const 1))).eval σ1 =
      writeReg σ1 (M + idxJ) (idx + 1) := by
    unfold ctlAssign
    rw [eval_assignInd, haddr]
    have hval : (Expr.add (ctlCell idxJ) (Expr.const 1)).eval σ1 = idx + 1 := by
      simp [Expr.eval, ctlCell_eval, hctl, hσ1idx]
    rw [hval]
  have hntop : (emitNatTableBody curJ tmpJ tblJ idxJ).eval σ = writeReg σ1 (M + idxJ) (idx + 1) := by
    unfold emitNatTableBody
    rw [eval_seq, ← hσ1def, hAeval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hntop]
    apply bitsAt_of_frame σ1 _ cur (encodeNat v) hbits
    intro r hr1 hr2
    rw [encodeNat_length] at hr2
    exact writeReg_diff σ1 (M + idxJ) (idx + 1) r (by omega)
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) (M + curJ) (by omega), hcursor]
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) 0 (by omega), hctl]
  · rw [hntop, writeReg_same]
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) (M + tblJ) (by omega), hσ1tbl]
  · intro r hr1 hr2 hr3 hrange
    rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) r (by omega)]
    exact hframe r hr1 hr2 hrange

/-- Splitting `List.range n`'s `flatMap` length at a cut point `m ≤ n`: the prefix `[0, m)` and
    the suffix `[m, n)` account for the whole length between them. Lets a per-iteration cursor
    bound (`cur + (prefix so far).length`) be compared against a *global* length bound (`cur +
    (everything).length ≤ wall`) without re-deriving the comparison by induction at every use
    site. -/
lemma flatMap_range_length_split (f : ℕ → Bits) (n m : ℕ) (hm : m ≤ n) :
    ((List.range m).flatMap f).length + ((List.range' m (n - m)).flatMap f).length
      = ((List.range n).flatMap f).length := by
  rw [List.range_eq_range' (n := m), List.range_eq_range' (n := n)]
  have heq : m + (n - m) = n := by omega
  have happ : List.range' 0 m ++ List.range' m (n - m) = List.range' 0 n := by
    have h := List.range'_append_1 (s := 0) (m := m) (n := n - m)
    simp only [Nat.zero_add] at h
    rwa [heq] at h
  rw [← happ, List.flatMap_append, List.length_append]

/-! ## `emitNatTableProg`'s per-iteration loop invariant

`emitNatTableProg`'s per-element loop (`emitListProg`'s `forN`, run over `emitNatTableBody`)
needs an invariant threaded through `emit_loop_flatMap`/`emitListProg_eval_state`'s generic `Inv`
parameter. `EmitNatTableInv m τ` pins the cursor cell to its *exact* value (`cur0` plus the
length of everything emitted for entries `< m`) rather than merely bounding it, so every
separation fact a per-iteration step needs can be read off a single global length bound
(`hsepFull` and friends, via `flatMap_range_length_split`) instead of re-derived by induction. -/

/-- Invariant for `emitNatTableProg`'s element loop after `m` entries have been emitted from a
    loop that started at cursor `cur0`: the index and base-address control cells still hold `m`
    and `tbl`, the table's own data is untouched, and the cursor sits exactly `m` entries past
    `cur0`. -/
def EmitNatTableInv (curJ tblJ idxJ M cur0 tbl n : ℕ) (g : ℕ → ℕ) (m : ℕ) (τ : Store) : Prop :=
  τ (M + idxJ) = m ∧ τ (M + tblJ) = tbl ∧
  (∀ q, q < n → τ (tbl + q) = g q) ∧
  τ (M + curJ) = cur0 + ((List.range m).flatMap (fun k => encodeNat (g k))).length

/-- The per-iteration correctness `emitListProg_eval_state`/`emit_loop_flatMap` need from
    `emitNatTableBody`, under `EmitNatTableInv`. The four separation bounds (`hsepFull` through
    `hsepTblAll`) all compare `cur0 + (the whole table's encoded length)` against a control-cell
    wall, per the module's convention that scratch storage (here, the table region
    `[tbl, tbl + n)`) sits above every control cell the finalize phase uses; `hloCur`/`hloTmp`/
    `hloIdx` place the table strictly beyond those same three control cells (never written by
    this body, but read again by later iterations, so they must survive every entry's emission —
    together with `hsepIdxAll` this already forces the table region itself past the write
    window, so no separate "table data" bound is needed). -/
lemma emitNatTableProg_hbody (curJ tmpJ tblJ idxJ M cur0 tbl n : ℕ) (g : ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + curJ)
    (hsepTmpAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + tmpJ)
    (hsepIdxAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + idxJ)
    (hsepTblAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl) :
    ∀ m, m < n → ∀ (τ : Store) (cur' : ℕ),
      EmitNatTableInv curJ tblJ idxJ M cur0 tbl n g m τ → τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) cur' (encodeNat (g m)) ∧
      ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) (M + curJ) = cur' + (encodeNat (g m)).length ∧
      ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ →
        (emitNatTableBody curJ tmpJ tblJ idxJ).eval τ r = τ r) ∧
      EmitNatTableInv curJ tblJ idxJ M cur0 tbl n g (m + 1)
        ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) := by
  intro m hmn τ cur' hInv hM hcur'
  obtain ⟨hidxCell, htblCell, htable, hcurpin⟩ := hInv
  have hkey : cur' + (encodeNat (g m)).length
      ≤ cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length := by
    have hsplit := flatMap_range_length_split (fun k => encodeNat (g k)) n m (le_of_lt hmn)
    have hnm : n - m = (n - m - 1) + 1 := by omega
    have hrsplit : List.range' m (n - m) = m :: List.range' (m + 1) (n - m - 1) := by
      conv_lhs => rw [hnm]
      rw [List.range'_succ]
    have hlen_remaining : ((List.range' m (n - m)).flatMap (fun k => encodeNat (g k))).length
        = (encodeNat (g m)).length
          + ((List.range' (m + 1) (n - m - 1)).flatMap (fun k => encodeNat (g k))).length := by
      rw [hrsplit, List.flatMap_cons, List.length_append]
    omega
  rw [encodeNat_length] at hkey
  have hstep : ((List.range m).flatMap (fun k => encodeNat (g k))).length + (encodeNat (g m)).length
      = ((List.range (m + 1)).flatMap (fun k => encodeNat (g k))).length := by
    have hsplit2 := flatMap_range_length_split (fun k => encodeNat (g k)) (m + 1) m (by omega)
    have h1 : (m + 1) - m = 1 := by omega
    rw [h1, List.range'_one] at hsplit2
    simpa using hsplit2
  have hsep_v : cur' + g m < M + curJ := by omega
  have hsepTmp_v : cur' + g m + 1 ≤ M + tmpJ := by omega
  have hsepIdx_v : cur' + g m + 1 ≤ M + idxJ := by omega
  have hsepTbl_v : cur' + g m + 1 ≤ M + tblJ := by omega
  have hsepData_v : cur' + g m + 1 ≤ tbl := by omega
  have hcur'1 : 1 ≤ cur' := by omega
  obtain ⟨hbits, hcursor, hctl0, hidxNew, htblNew, hframe⟩ :=
    emitNatTableBody_eval_state curJ tmpJ tblJ idxJ M cur' tbl m (g m) τ
      hc1 hc2 hct hcb hci htb hti hbi hM hcur' hcur'1 htblCell hidxCell (htable m hmn)
      hsep_v hsepIdx_v hsepTbl_v
  refine ⟨hbits, ?_, hctl0, ?_⟩
  · rw [encodeNat_length]; omega
  · refine ⟨fun r hr1 hr2 => ?_, ⟨hidxNew, htblNew, ?_, ?_⟩⟩
    · exact hframe r hr2 (by omega) (by omega) (Or.inl hr1)
    · intro q hq
      have hne1 : tbl + q ≠ M + curJ := by omega
      have hne2 : tbl + q ≠ M + tmpJ := by omega
      have hne3 : tbl + q ≠ M + idxJ := by omega
      have hrange : cur' + g m + 1 ≤ tbl + q := by omega
      exact (hframe (tbl + q) hne1 hne2 hne3 (Or.inr hrange)).trans (htable q hq)
    · have hln := encodeNat_length (g m)
      omega

/-- Bundled correctness of `emitNatTableProg`: the store after running it holds `encodeNat n ++
    (List.range n).flatMap (fun k => encodeNat (g k))` at the entry cursor (the same shape
    `emitListProg_eval_state` gives for a generic table), the cursor has advanced past the whole
    emission, and cell `0` still holds `M`. Proved by chaining the `idxJ := 0` reset with
    `emitListProg_eval_state`, instantiated at `emitNatTableProg_hbody` for the per-iteration
    obligation. -/
lemma emitNatTableProg_eval_state (curJ tmpJ cntJ tblJ idxJ M cur tbl n : ℕ) (g : ℕ → ℕ)
    (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hc4 : 1 ≤ idxJ)
    (hct : curJ ≠ tmpJ) (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ) (hcnti : cntJ ≠ idxJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hcnt : σ (M + cntJ) = n) (htbl : σ (M + tblJ) = tbl)
    (htable : ∀ q, q < n → σ (tbl + q) = g q)
    (hsepCnt : cur + n + 1 ≤ M + cntJ)
    (hsepFull : cur + n + 1 + ((List.range n).flatMap (fun k => encodeNat (g k))).length
      ≤ M + curJ)
    (hsepTmpAll : cur + n + 1 + ((List.range n).flatMap (fun k => encodeNat (g k))).length
      ≤ M + tmpJ)
    (hsepIdxAll : cur + n + 1 + ((List.range n).flatMap (fun k => encodeNat (g k))).length
      ≤ M + idxJ)
    (hsepTblAll : cur + n + 1 + ((List.range n).flatMap (fun k => encodeNat (g k))).length
      ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl) :
    BitsAt ((emitNatTableProg curJ tmpJ cntJ tblJ idxJ).eval σ) cur
      (encodeNat n ++ (List.range n).flatMap (fun k => encodeNat (g k))) ∧
    ((emitNatTableProg curJ tmpJ cntJ tblJ idxJ).eval σ) (M + curJ)
      = cur + n + 1 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ∧
    ((emitNatTableProg curJ tmpJ cntJ tblJ idxJ).eval σ) 0 = M := by
  have hσ'0 : (ctlAssign idxJ (Expr.const 0)).eval σ 0 = M := by
    rw [ctlAssign_zero idxJ (Expr.const 0) σ hc4, hM]
  have hσ'cur : (ctlAssign idxJ (Expr.const 0)).eval σ (M + curJ) = cur := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + curJ) (by omega), hcur]
  have hσ'cnt : (ctlAssign idxJ (Expr.const 0)).eval σ (M + cntJ) = n := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + cntJ) (by omega), hcnt]
  have hσ'tbl : (ctlAssign idxJ (Expr.const 0)).eval σ (M + tblJ) = tbl := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + tblJ) (by omega), htbl]
  have hσ'idx : (ctlAssign idxJ (Expr.const 0)).eval σ (M + idxJ) = 0 := by
    have h := ctlAssign_eval_same idxJ (Expr.const 0) σ
    rw [hM] at h
    simpa [Expr.eval] using h
  have hσ'table : ∀ q, q < n → (ctlAssign idxJ (Expr.const 0)).eval σ (tbl + q) = g q := by
    intro q hq
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (tbl + q) (by omega), htable q hq]
  set σ' := (ctlAssign idxJ (Expr.const 0)).eval σ with hσ'def
  have hcntEval : (ctlCell cntJ).eval σ' = n := by rw [ctlCell_eval, hσ'0, hσ'cnt]
  have hsep'' : cur + (ctlCell cntJ).eval σ' < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ' hc1 hc2 hct hσ'0 hσ'cur hcur1 hsep''
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ' with hσ1def
  have hσ1idx : σ1 (M + idxJ) = 0 := by
    rw [hframe1 (M + idxJ) (by omega) (by omega) (Or.inr (by omega)), hσ'idx]
  have hσ1tbl : σ1 (M + tblJ) = tbl := by
    rw [hframe1 (M + tblJ) (by omega) (by omega) (Or.inr (by omega)), hσ'tbl]
  have hσ1table : ∀ q, q < n → σ1 (tbl + q) = g q := by
    intro q hq
    have hne1 : tbl + q ≠ M + curJ := by omega
    have hne2 : tbl + q ≠ M + tmpJ := by omega
    have hrange : cur + n + 1 ≤ tbl + q := by omega
    rw [hframe1 (tbl + q) hne1 hne2 (Or.inr hrange), hσ'table q hq]
  have hInv0 : EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g 0 σ1 :=
    ⟨hσ1idx, hσ1tbl, hσ1table, by rw [hcursor1]; simp⟩
  have hbody := emitNatTableProg_hbody curJ tmpJ tblJ idxJ M (cur + n + 1) tbl n g
    hc1 hc2 hct hcb hci htb hti hbi (by omega) hsepFull hsepTmpAll hsepIdxAll hsepTblAll
    hloCur hloTmp hloIdx
  obtain ⟨hbitsFinal, hcursorFinal, hctlFinal, _⟩ :=
    emitListProg_eval_state curJ tmpJ cntJ M cur n (emitNatTableBody curJ tmpJ tblJ idxJ)
      (fun m => encodeNat (g m)) (EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g) σ'
      hc1 hc2 hct hcc hcnt2 hσ'0 hσ'cur hcur1 hσ'cnt hsepCnt hsepFull hbody hInv0
  have htop : (emitNatTableProg curJ tmpJ cntJ tblJ idxJ).eval σ
      = (emitListProg curJ tmpJ cntJ (emitNatTableBody curJ tmpJ tblJ idxJ)).eval σ' := by
    unfold emitNatTableProg
    rw [eval_seq, ← hσ'def]
  exact ⟨htop ▸ hbitsFinal, htop ▸ hcursorFinal, htop ▸ hctlFinal⟩

/-! ## Emitting a contiguous table of fixed-width `Nat` tuples

The fixed-width table stores each record as `w = 3` consecutive `Nat`s at
`tbl + w * idx, …, tbl + w * idx + (w - 1)`, because each record has exactly three fields. This
is different from the one-`Nat`-per-entry shape `emitNatTableProg` handles.
`emitNatTupleFieldsFrom` emits fields
`0, …, k - 1` of one entry by structural recursion on `k`, appending the newest field at the
*end* of the already-built program (mirroring `List.range_succ`'s right-append shape) so the
emission order matches the declarative `(List.range w).flatMap` shape field-by-field;
`emitNatTupleFields` instantiates it at `k := w`.
`emitNatTupleBody`/`emitNatTupleTableProg` then wrap it exactly as `emitNatTableBody`/
`emitNatTableProg` wrap `emitNatProg`, advancing the index once per entry. -/

/-- Emit fields `0, …, k - 1` of the width-`w` entry at `tbl + w * idx` (in that order), where
    `tbl`/`idx`/`w` are all read from control cells (`w` compile-time, `tbl`/`idx` run-time). The
    recursion is on `k` alone — `w` stays fixed across the whole call chain — so the `k`-th
    unfolding appends the field-`k` emitter after everything the `k`-fold recursion already
    built. -/
def emitNatTupleFieldsFrom (curJ tmpJ tblJ idxJ w : ℕ) : ℕ → Program
  | 0 => .skip
  | k + 1 =>
    .seq (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k)
      (emitNatProg curJ tmpJ
        (.regInd (.add (.add (ctlCell tblJ) (.mul (.const w) (ctlCell idxJ))) (.const k))))

/-- Emit all `w` fields of one entry, in order `0, …, w - 1`. -/
def emitNatTupleFields (curJ tmpJ tblJ idxJ w : ℕ) : Program :=
  emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w

/-- One iteration: emit every field of the table entry at `tbl + w * idx` in unary, then advance
    the index. -/
def emitNatTupleBody (curJ tmpJ tblJ idxJ w : ℕ) : Program :=
  .seq (emitNatTupleFields curJ tmpJ tblJ idxJ w)
    (ctlAssign idxJ (.add (ctlCell idxJ) (.const 1)))

/-- Emit a contiguous table of width-`w` `Nat` tuples in `encodeList` shape: the entry count in
    unary, then each entry's `w` fields in unary. -/
def emitNatTupleTableProg (curJ tmpJ cntJ tblJ idxJ w : ℕ) : Program :=
  .seq (ctlAssign idxJ (.const 0))
    (emitListProg curJ tmpJ cntJ (emitNatTupleBody curJ tmpJ tblJ idxJ w))

lemma emitNatTupleFieldsFrom_zero (curJ tmpJ tblJ idxJ w : ℕ) :
    emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w 0 = Program.skip := rfl

lemma emitNatTupleFieldsFrom_succ (curJ tmpJ tblJ idxJ w k : ℕ) :
    emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1) =
      .seq (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k)
        (emitNatProg curJ tmpJ
          (.regInd (.add (.add (ctlCell tblJ) (.mul (.const w) (ctlCell idxJ))) (.const k)))) :=
  rfl

/-- One step of `emitNatTupleFieldsFrom_eval_state`'s induction: given the bundled correctness of
    the first `k` fields (`hbitsK` through `hframeK`) and the `(k + 1)`-level table and separation
    hypotheses, derive the bundled correctness at `k + 1` by running the field-`k` emitter
    (`emitNatProg`) on the `k`-field store. `hloCur`/`hloTmp` place the field-`k` address
    `tbl + w * q + k` past every control cell this step reads or writes, so no separate `idxJ`-side
    table bound is needed. -/
lemma emitNatTupleFieldsFrom_step (curJ tmpJ tblJ idxJ M tbl w q : ℕ) (g : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ) (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (k cur : ℕ) (σ : Store) (hcur1 : 1 ≤ cur)
    (htable : ∀ t, t < k + 1 → σ (tbl + w * q + t) = g q t)
    (hsep : cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length < M + curJ)
    (hsepTmp : cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
      ≤ M + tmpJ)
    (hsepIdx : cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
      ≤ M + idxJ)
    (hsepTbl : cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
      ≤ M + tblJ)
    (hbitsK : BitsAt ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) cur
      ((List.range k).flatMap (fun t => encodeNat (g q t))))
    (hcursorK : ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + curJ)
      = cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length)
    (h0K : ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) 0 = M)
    (hidxK : ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + idxJ) = q)
    (htblK : ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + tblJ) = tbl)
    (hframeK : ∀ r, r ≠ M + curJ → r ≠ M + tmpJ →
      (r < cur ∨ cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ r) →
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) r = σ r) :
    BitsAt ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) cur
      ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))) ∧
    ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) (M + curJ)
      = cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length ∧
    ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) 0 = M ∧
    ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) (M + idxJ) = q ∧
    ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) (M + tblJ) = tbl ∧
    (∀ r, r ≠ M + curJ → r ≠ M + tmpJ →
      (r < cur ∨ cur + ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length ≤ r) →
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ) r = σ r) := by
  have hstepList : (List.range (k + 1)).flatMap (fun t => encodeNat (g q t))
      = (List.range k).flatMap (fun t => encodeNat (g q t)) ++ encodeNat (g q k) := by
    rw [List.range_succ, List.flatMap_append]
    simp
  have hlenStep : ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
      = ((List.range k).flatMap (fun t => encodeNat (g q t))).length + g q k + 1 := by
    rw [hstepList, List.length_append, encodeNat_length]
    omega
  set σK := (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ with hσKdef
  have hsep_v : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
      + g q k < M + curJ := by omega
  have hsepTmp_v : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
      + g q k + 1 ≤ M + tmpJ := by omega
  have hsepIdx_v : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
      + g q k + 1 ≤ M + idxJ := by omega
  have hsepTbl_v : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
      + g q k + 1 ≤ M + tblJ := by omega
  have hkAddr_ge : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
      ≤ tbl + w * q + k := by omega
  have hfieldCurNe : tbl + w * q + k ≠ M + curJ := by omega
  have hfieldTmpNe : tbl + w * q + k ≠ M + tmpJ := by omega
  have hfieldVal : σK (tbl + w * q + k) = g q k := by
    rw [hframeK (tbl + w * q + k) hfieldCurNe hfieldTmpNe (Or.inr hkAddr_ge)]
    exact htable k (by omega)
  have haddrEval : (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
      (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK = g q k := by
    have h1 : (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK
        = σK (σK (σK 0 + tblJ) + w * σK (σK 0 + idxJ) + k) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, h0K, htblK, hidxK]
    exact hfieldVal
  have hcurK1 : 1 ≤ cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length := by
    omega
  have hsepV : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length +
      (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK < M + curJ := by
    rw [haddrEval]; exact hsep_v
  obtain ⟨hbitsField, hcursorField, hframeField, hctlField⟩ :=
    emitNatProg_eval_state curJ tmpJ M
      (cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length)
      (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))) σK
      hc1 hc2 hct h0K hcursorK hcurK1 hsepV
  rw [haddrEval] at hbitsField hcursorField hframeField
  have htop : (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w (k + 1)).eval σ
      = (emitNatProg curJ tmpJ (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
          (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k)))).eval σK := by
    rw [emitNatTupleFieldsFrom_succ, eval_seq, ← hσKdef]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htop, hstepList, bitsAt_append]
    refine ⟨?_, hbitsField⟩
    apply bitsAt_of_frame σK _ cur ((List.range k).flatMap (fun t => encodeNat (g q t))) hbitsK
    intro r hr1 hr2
    exact hframeField r (by omega) (by omega) (Or.inl hr2)
  · rw [htop, hcursorField, hlenStep]; omega
  · rw [htop]; exact hctlField
  · rw [htop, hframeField (M + idxJ) (by omega) (by omega) (Or.inr hsepIdx_v), hidxK]
  · rw [htop, hframeField (M + tblJ) (by omega) (by omega) (Or.inr hsepTbl_v), htblK]
  · intro r hrC hrT hrange
    rw [htop]
    rcases hrange with hlt | hge
    · have hlt' : r < cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length := by
        omega
      rw [hframeField r hrC hrT (Or.inl hlt')]
      exact hframeK r hrC hrT (Or.inl hlt)
    · have hge' : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
          + g q k + 1 ≤ r := by omega
      rw [hframeField r hrC hrT (Or.inr hge')]
      have hgeK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ r := by
        omega
      exact hframeK r hrC hrT (Or.inr hgeK)

/-- Bundled correctness of `emitNatTupleFieldsFrom` for its first `k` fields (entry `q`, table
    base `tbl`, field width `w`): the four separation bounds (`hsep` through `hsepTbl`, all
    against the cumulative length of the `k` fields already spoken for) keep the write region
    away from the cursor register and both control cells this recursion only *reads*
    (`idxJ`/`tblJ`); `hloCur`/`hloTmp` additionally place the table region above those same
    control cells, so a not-yet-emitted field's stored value survives every earlier field's
    emission (`hfieldVal` in the proof, via `emitNatTupleFieldsFrom_step`). The third such bound
    (on `idxJ`) is accepted only for symmetry with the callers of this lemma (`hloCur`/`hloTmp`
    alone already suffice, per `emitNatTupleFieldsFrom_step`'s docstring). Proved by induction on
    `k`, peeling the newest field off the *end* — the same direction `emitNatTupleFieldsFrom`
    itself recurses in. -/
lemma emitNatTupleFieldsFrom_eval_state (curJ tmpJ tblJ idxJ M tbl w q : ℕ) (g : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ) (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) :
    ∀ k cur (σ : Store), σ 0 = M → σ (M + curJ) = cur → 1 ≤ cur →
      σ (M + tblJ) = tbl → σ (M + idxJ) = q →
      (∀ t, t < k → σ (tbl + w * q + t) = g q t) →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length < M + curJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + tmpJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + idxJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + tblJ →
      BitsAt ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) cur
        ((List.range k).flatMap (fun t => encodeNat (g q t))) ∧
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + curJ)
        = cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ∧
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) 0 = M ∧
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + idxJ) = q ∧
      ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) (M + tblJ) = tbl ∧
      (∀ r, r ≠ M + curJ → r ≠ M + tmpJ →
        (r < cur ∨ cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ r) →
        ((emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ) r = σ r) := by
  intro k
  induction k with
  | zero =>
    intro cur σ h0 hcur hcur1 htblCell hidxCell _htable _hsep _hsepTmp _hsepIdx _hsepTbl
    rw [emitNatTupleFieldsFrom_zero, NPComplete.BoundedWhile.eval_skip]
    refine ⟨?_, by simpa using hcur, h0, hidxCell, htblCell, fun r _ _ _ => rfl⟩
    simpa using bitsAt_nil σ cur
  | succ k ih =>
    intro cur σ h0 hcur hcur1 htblCell hidxCell htable hsep hsepTmp hsepIdx hsepTbl
    have hlenStep : ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
        = ((List.range k).flatMap (fun t => encodeNat (g q t))).length + g q k + 1 := by
      have hstepList : (List.range (k + 1)).flatMap (fun t => encodeNat (g q t))
          = (List.range k).flatMap (fun t => encodeNat (g q t)) ++ encodeNat (g q k) := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hstepList, List.length_append, encodeNat_length]
      omega
    have htableK : ∀ t, t < k → σ (tbl + w * q + t) = g q t := fun t ht => htable t (by omega)
    have hsepK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        < M + curJ := by omega
    have hsepTmpK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + tmpJ := by omega
    have hsepIdxK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + idxJ := by omega
    have hsepTblK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + tblJ := by omega
    obtain ⟨hbitsK, hcursorK, h0K, hidxK, htblK, hframeK⟩ :=
      ih cur σ h0 hcur hcur1 htblCell hidxCell htableK hsepK hsepTmpK hsepIdxK hsepTblK
    exact emitNatTupleFieldsFrom_step curJ tmpJ tblJ idxJ M tbl w q g
      hc1 hc2 hct hcb hci htb hti hloCur hloTmp k cur σ hcur1
      htable hsep hsepTmp hsepIdx hsepTbl hbitsK hcursorK h0K hidxK htblK hframeK

/-- Bundled correctness of one `emitNatTupleBody` iteration: reading every field of the
    width-`w` table entry at `tbl + w * idx` (held via control cells `tblJ`/`idxJ`), emitting
    them in unary at the output cursor, then advancing `idxJ` to `idx + 1`. Mirrors
    `emitNatTableBody_eval_state`'s shape exactly, with the single value `v` replaced by the
    `w`-field length `(List.range w).flatMap (fun t => encodeNat (g idx t))` — the field
    emission itself is handed off to `emitNatTupleFieldsFrom_eval_state` at `k := w`, and only
    the trailing index increment is proved directly here. -/
lemma emitNatTupleBody_eval_state (curJ tmpJ tblJ idxJ M cur tbl w idx : ℕ) (g : ℕ → ℕ → ℕ)
    (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (htblCell : σ (M + tblJ) = tbl) (hidxCell : σ (M + idxJ) = idx)
    (hentry : ∀ t, t < w → σ (tbl + w * idx + t) = g idx t)
    (hsep : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length < M + curJ)
    (hsepTmp : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + tmpJ)
    (hsepIdx : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + idxJ)
    (hsepTbl : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) :
    BitsAt ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) cur
      ((List.range w).flatMap (fun t => encodeNat (g idx t))) ∧
    ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) (M + curJ)
      = cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ∧
    ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) 0 = M ∧
    ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) (M + idxJ) = idx + 1 ∧
    ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) (M + tblJ) = tbl ∧
    (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + idxJ →
      (r < cur ∨ cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ r) →
      ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ) r = σ r) := by
  have hfields : emitNatTupleFields curJ tmpJ tblJ idxJ w
      = emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w := rfl
  obtain ⟨hbits, hcursor, hctl, hσ1idx, hσ1tbl, hframe⟩ :=
    emitNatTupleFieldsFrom_eval_state curJ tmpJ tblJ idxJ M tbl w idx g
      hc1 hc2 hct hcb hci htb hti hloCur hloTmp w cur σ
      hM hcur hcur1 htblCell hidxCell hentry hsep hsepTmp hsepIdx hsepTbl
  set σ1 := (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w).eval σ with hσ1def
  have haddr : (ctlAddr idxJ).eval σ1 = M + idxJ := by rw [ctlAddr_eval, hctl]
  have hAeval : (ctlAssign idxJ (Expr.add (ctlCell idxJ) (Expr.const 1))).eval σ1 =
      writeReg σ1 (M + idxJ) (idx + 1) := by
    unfold ctlAssign
    rw [eval_assignInd, haddr]
    have hval : (Expr.add (ctlCell idxJ) (Expr.const 1)).eval σ1 = idx + 1 := by
      simp [Expr.eval, ctlCell_eval, hctl, hσ1idx]
    rw [hval]
  have hntop : (emitNatTupleBody curJ tmpJ tblJ idxJ w).eval σ = writeReg σ1 (M + idxJ) (idx + 1) := by
    unfold emitNatTupleBody
    rw [eval_seq, hfields, ← hσ1def, hAeval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hntop]
    apply bitsAt_of_frame σ1 _ cur ((List.range w).flatMap (fun t => encodeNat (g idx t))) hbits
    intro r hr1 hr2
    exact writeReg_diff σ1 (M + idxJ) (idx + 1) r (by omega)
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) (M + curJ) (by omega), hcursor]
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) 0 (by omega), hctl]
  · rw [hntop, writeReg_same]
  · rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) (M + tblJ) (by omega), hσ1tbl]
  · intro r hr1 hr2 hr3 hrange
    rw [hntop, writeReg_diff σ1 (M + idxJ) (idx + 1) r (by omega)]
    exact hframe r hr1 hr2 hrange

/-! ## `emitNatTupleTableProg`'s per-iteration loop invariant

Generalizes `EmitNatTableInv`/`emitNatTableProg_hbody` from a one-`Nat`-per-entry table to a
width-`w` tuple-per-entry table: the per-entry emitted chunk `f m := (List.range w).flatMap
(fun t => encodeNat (g m t))` replaces the single `encodeNat (g m)`, and the table-data
component of the invariant reads two indices (`q` the entry, `t` the field) instead of one. -/

/-- Invariant for `emitNatTupleTableProg`'s element loop after `m` entries have been emitted
    from a loop that started at cursor `cur0`: the index and base-address control cells still
    hold `m` and `tbl`, every entry's `w` fields are untouched, and the cursor sits exactly the
    combined length of the first `m` entries' emissions past `cur0`. -/
def EmitNatTupleTableInv (curJ tblJ idxJ M cur0 tbl n w : ℕ) (g : ℕ → ℕ → ℕ) (m : ℕ)
    (τ : Store) : Prop :=
  τ (M + idxJ) = m ∧ τ (M + tblJ) = tbl ∧
  (∀ q t, q < n → t < w → τ (tbl + w * q + t) = g q t) ∧
  τ (M + curJ) = cur0
    + ((List.range m).flatMap (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length

/-- The per-iteration correctness `emitListProg_eval_state`/`emit_loop_flatMap` need from
    `emitNatTupleBody`, under `EmitNatTupleTableInv`. Mirrors `emitNatTableProg_hbody`'s four
    separation bounds, with `hsepFull` strengthened to a *strict* inequality: unlike a single
    `encodeNat` value (whose length is always `value + 1`, so subtracting the trailing `1` bit
    manufactures strictness from a non-strict global bound), a width-`w` chunk's length has no
    such uniform "+1" to peel off, so strictness has to be assumed directly. -/
lemma emitNatTupleTableProg_hbody (curJ tmpJ tblJ idxJ M cur0 tbl n w : ℕ) (g : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length < M + curJ)
    (hsepTmpAll : cur0 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + tmpJ)
    (hsepIdxAll : cur0 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + idxJ)
    (hsepTblAll : cur0 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl) :
    ∀ m, m < n → ∀ (τ : Store) (cur' : ℕ),
      EmitNatTupleTableInv curJ tblJ idxJ M cur0 tbl n w g m τ → τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) cur'
        ((List.range w).flatMap (fun t => encodeNat (g m t))) ∧
      ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) (M + curJ)
        = cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length ∧
      ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ →
        (emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ r = τ r) ∧
      EmitNatTupleTableInv curJ tblJ idxJ M cur0 tbl n w g (m + 1)
        ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) := by
  intro m hmn τ cur' hInv hM hcur'
  obtain ⟨hidxCell, htblCell, htable, hcurpin⟩ := hInv
  have hkey : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ cur0 + ((List.range n).flatMap
        (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length := by
    have hsplit := flatMap_range_length_split
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t))) n m (le_of_lt hmn)
    have hnm : n - m = (n - m - 1) + 1 := by omega
    have hrsplit : List.range' m (n - m) = m :: List.range' (m + 1) (n - m - 1) := by
      conv_lhs => rw [hnm]
      rw [List.range'_succ]
    have hlen_remaining :
        ((List.range' m (n - m)).flatMap
          (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length
        = ((List.range w).flatMap (fun t => encodeNat (g m t))).length
          + ((List.range' (m + 1) (n - m - 1)).flatMap
            (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length := by
      rw [hrsplit, List.flatMap_cons, List.length_append]
    omega
  have hstep : ((List.range m).flatMap
        (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length
      + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      = ((List.range (m + 1)).flatMap
        (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length := by
    have hsplit2 := flatMap_range_length_split
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t))) (m + 1) m (by omega)
    have h1 : (m + 1) - m = 1 := by omega
    rw [h1, List.range'_one] at hsplit2
    simpa using hsplit2
  have hsep_v : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      < M + curJ := by omega
  have hsepTmp_v : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + tmpJ := by omega
  have hsepIdx_v : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + idxJ := by omega
  have hsepTbl_v : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + tblJ := by omega
  have hcur'1 : 1 ≤ cur' := by omega
  have hentry : ∀ t, t < w → τ (tbl + w * m + t) = g m t := fun t ht => htable m t hmn ht
  obtain ⟨hbits, hcursor, hctl0, hidxNew, htblNew, hframe⟩ :=
    emitNatTupleBody_eval_state curJ tmpJ tblJ idxJ M cur' tbl w m g τ
      hc1 hc2 hct hcb hci htb hti hbi hM hcur' hcur'1 htblCell hidxCell hentry
      hsep_v hsepTmp_v hsepIdx_v hsepTbl_v hloCur hloTmp
  refine ⟨hbits, hcursor, hctl0, ?_, ?_⟩
  · intro r hr1 hr2
    exact hframe r hr2 (by omega) (by omega) (Or.inl hr1)
  · refine ⟨hidxNew, htblNew, ?_, ?_⟩
    · intro q t hq ht
      have hne1 : tbl + w * q + t ≠ M + curJ := by omega
      have hne2 : tbl + w * q + t ≠ M + tmpJ := by omega
      have hne3 : tbl + w * q + t ≠ M + idxJ := by omega
      have hrange : cur' + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
          ≤ tbl + w * q + t := by omega
      exact (hframe (tbl + w * q + t) hne1 hne2 hne3 (Or.inr hrange)).trans (htable q t hq ht)
    · omega

/-- Bundled correctness of `emitNatTupleTableProg`: the store after running it holds `encodeNat
    n ++ (List.range n).flatMap (fun m => (List.range w).flatMap (fun t => encodeNat (g m t)))`
    at the entry cursor, the cursor has advanced past the whole emission, and cell `0` still
    holds `M`. Proved exactly as `emitNatTableProg_eval_state`, chaining the `idxJ := 0` reset
    with `emitListProg_eval_state` instantiated at `emitNatTupleTableProg_hbody`. -/
lemma emitNatTupleTableProg_eval_state (curJ tmpJ cntJ tblJ idxJ M cur tbl n w : ℕ)
    (g : ℕ → ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hc4 : 1 ≤ idxJ)
    (hct : curJ ≠ tmpJ) (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ) (hcnti : cntJ ≠ idxJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hcnt : σ (M + cntJ) = n) (htbl : σ (M + tblJ) = tbl)
    (htable : ∀ q t, q < n → t < w → σ (tbl + w * q + t) = g q t)
    (hsepCnt : cur + n + 1 ≤ M + cntJ)
    (hsepFull : cur + n + 1 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length < M + curJ)
    (hsepTmpAll : cur + n + 1 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + tmpJ)
    (hsepIdxAll : cur + n + 1 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + idxJ)
    (hsepTblAll : cur + n + 1 + ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl) :
    BitsAt ((emitNatTupleTableProg curJ tmpJ cntJ tblJ idxJ w).eval σ) cur
      (encodeNat n ++ (List.range n).flatMap
        (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))) ∧
    ((emitNatTupleTableProg curJ tmpJ cntJ tblJ idxJ w).eval σ) (M + curJ)
      = cur + n + 1 + ((List.range n).flatMap
        (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length ∧
    ((emitNatTupleTableProg curJ tmpJ cntJ tblJ idxJ w).eval σ) 0 = M := by
  have hσ'0 : (ctlAssign idxJ (Expr.const 0)).eval σ 0 = M := by
    rw [ctlAssign_zero idxJ (Expr.const 0) σ hc4, hM]
  have hσ'cur : (ctlAssign idxJ (Expr.const 0)).eval σ (M + curJ) = cur := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + curJ) (by omega), hcur]
  have hσ'cnt : (ctlAssign idxJ (Expr.const 0)).eval σ (M + cntJ) = n := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + cntJ) (by omega), hcnt]
  have hσ'tbl : (ctlAssign idxJ (Expr.const 0)).eval σ (M + tblJ) = tbl := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + tblJ) (by omega), htbl]
  have hσ'idx : (ctlAssign idxJ (Expr.const 0)).eval σ (M + idxJ) = 0 := by
    have h := ctlAssign_eval_same idxJ (Expr.const 0) σ
    rw [hM] at h
    simpa [Expr.eval] using h
  have hσ'table : ∀ q t, q < n → t < w →
      (ctlAssign idxJ (Expr.const 0)).eval σ (tbl + w * q + t) = g q t := by
    intro q t hq ht
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (tbl + w * q + t) (by omega), htable q t hq ht]
  set σ' := (ctlAssign idxJ (Expr.const 0)).eval σ with hσ'def
  have hcntEval : (ctlCell cntJ).eval σ' = n := by rw [ctlCell_eval, hσ'0, hσ'cnt]
  have hsep'' : cur + (ctlCell cntJ).eval σ' < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ' hc1 hc2 hct hσ'0 hσ'cur hcur1 hsep''
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ' with hσ1def
  have hσ1idx : σ1 (M + idxJ) = 0 := by
    rw [hframe1 (M + idxJ) (by omega) (by omega) (Or.inr (by omega)), hσ'idx]
  have hσ1tbl : σ1 (M + tblJ) = tbl := by
    rw [hframe1 (M + tblJ) (by omega) (by omega) (Or.inr (by omega)), hσ'tbl]
  have hσ1table : ∀ q t, q < n → t < w → σ1 (tbl + w * q + t) = g q t := by
    intro q t hq ht
    have hne1 : tbl + w * q + t ≠ M + curJ := by omega
    have hne2 : tbl + w * q + t ≠ M + tmpJ := by omega
    have hrange : cur + n + 1 ≤ tbl + w * q + t := by omega
    rw [hframe1 (tbl + w * q + t) hne1 hne2 (Or.inr hrange), hσ'table q t hq ht]
  have hInv0 : EmitNatTupleTableInv curJ tblJ idxJ M (cur + n + 1) tbl n w g 0 σ1 :=
    ⟨hσ1idx, hσ1tbl, hσ1table, by rw [hcursor1]; simp⟩
  have hbody := emitNatTupleTableProg_hbody curJ tmpJ tblJ idxJ M (cur + n + 1) tbl n w g
    hc1 hc2 hct hcb hci htb hti hbi (by omega) hsepFull hsepTmpAll hsepIdxAll hsepTblAll
    hloCur hloTmp hloIdx
  obtain ⟨hbitsFinal, hcursorFinal, hctlFinal, _⟩ :=
    emitListProg_eval_state curJ tmpJ cntJ M cur n (emitNatTupleBody curJ tmpJ tblJ idxJ w)
      (fun m => (List.range w).flatMap (fun t => encodeNat (g m t)))
      (EmitNatTupleTableInv curJ tblJ idxJ M (cur + n + 1) tbl n w g) σ'
      hc1 hc2 hct hcc hcnt2 hσ'0 hσ'cur hcur1 hσ'cnt hsepCnt hsepFull.le hbody hInv0
  have htop : (emitNatTupleTableProg curJ tmpJ cntJ tblJ idxJ w).eval σ
      = (emitListProg curJ tmpJ cntJ (emitNatTupleBody curJ tmpJ tblJ idxJ w)).eval σ' := by
    unfold emitNatTupleTableProg
    rw [eval_seq, ← hσ'def]
  exact ⟨htop ▸ hbitsFinal, htop ▸ hcursorFinal, htop ▸ hctlFinal⟩

/-! ## Emitting a variable-length row

A row consists of a unary key and a length-prefixed list of two-cell tagged entries. The fixed-width
table emitters `emitNatTableProg` and `emitNatTupleTableProg` assume fixed entry widths.
`emitRawOpBody` emits one tagged entry: a tag bit followed by a unary value, then advances a
run-time pointer by two cells. `emitOpsListProg` uses `emitListProg` for the complete entry list. It
reads its initial pointer position from a caller-staged control cell at `row + 2`, beyond the key
and count cells, instead of resetting it internally. The pointer's starting position is
data-dependent, unlike fixed-table index cells. -/

/-- Emit one tagged entry: a tag bit, then a value in unary; the pointer control cell
    `ptrJ` (holding the entry's own address) advances by two cells. -/
def emitRawOpBody (curJ tmpJ ptrJ : ℕ) : Program :=
  .seq (.seq (emitBitProg curJ (.regInd (ctlCell ptrJ)))
    (emitNatProg curJ tmpJ (.regInd (.add (ctlCell ptrJ) (.const 1)))))
    (ctlAssign ptrJ (.add (ctlCell ptrJ) (.const 2)))

/-- Bundled correctness of `emitRawOpBody`: reading a tag bit and value from the two cells
    `ptrJ` currently points to (`tag`/`d`), emitting `[tag] ++ encodeNat d` at the output cursor,
    then advancing the pointer to `ptr + 2`. This format stays generic so the table toolkit is
    independent of any concrete encoding function. `hloCur`/`hloTmp` place the tagged entry's
    address `ptr` past the two control cells this body reads or writes, as in
    `emitNatTupleFieldsFrom_step`, so the stored tag and value survive every write. -/
lemma emitRawOpBody_eval_state (curJ tmpJ ptrJ M cur ptr : ℕ) (tag : Bool) (d : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hptrCell : σ (M + ptrJ) = ptr)
    (htag : σ ptr = if tag then 1 else 0)
    (hdata : σ (ptr + 1) = d)
    (hloCur : M + curJ < ptr) (hloTmp : M + tmpJ < ptr)
    (hsep : cur + 1 + d < M + curJ)
    (hsepTmp : cur + 1 + d + 1 ≤ M + tmpJ)
    (hsepPtr : cur + 1 + d + 1 ≤ M + ptrJ) :
    BitsAt ((emitRawOpBody curJ tmpJ ptrJ).eval σ) cur ([tag] ++ encodeNat d) ∧
    ((emitRawOpBody curJ tmpJ ptrJ).eval σ) (M + curJ) = cur + 1 + d + 1 ∧
    ((emitRawOpBody curJ tmpJ ptrJ).eval σ) 0 = M ∧
    ((emitRawOpBody curJ tmpJ ptrJ).eval σ) (M + ptrJ) = ptr + 2 ∧
    (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + ptrJ →
      (r < cur ∨ cur + 1 + d + 1 ≤ r) →
      ((emitRawOpBody curJ tmpJ ptrJ).eval σ) r = σ r) := by
  have heval1 : (Expr.regInd (ctlCell ptrJ)).eval σ = if tag then 1 else 0 := by
    have h1 : (Expr.regInd (ctlCell ptrJ)).eval σ = σ (σ (σ 0 + ptrJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hptrCell]; exact htag
  have hcurNe : cur ≠ M + curJ := by omega
  have hcur0 : cur ≠ 0 := by omega
  obtain ⟨hσ1cell, hσ1cursor, hσ1frame, hσ1ctl⟩ :
      (((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) cur
          = (if tag then 1 else 0)) ∧
      ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) (M + curJ) = cur + 1 ∧
      (∀ r, r ≠ cur → r ≠ M + curJ →
        ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) r = σ r) ∧
      ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) 0 = M := by
    refine ⟨?_, ?_, emitBitProg_frame curJ M cur _ σ hM hcur hcur0 hcurNe,
      emitBitProg_ctl curJ M cur _ σ hc1 hM hcur hcur0 hcurNe⟩
    · rw [emitBitProg_eval_cell curJ M cur _ σ hM hcur hcur0 hcurNe]; exact heval1
    · exact emitBitProg_cursor curJ M cur _ σ hM hcur hcur0 hcurNe
  set σ1 := (emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ with hσ1def
  have hσ1ptr : σ1 (M + ptrJ) = ptr := by
    rw [hσ1frame (M + ptrJ) (by omega) (by omega), hptrCell]
  have hptr1cur : ptr + 1 ≠ cur := by omega
  have hptr1curJ : ptr + 1 ≠ M + curJ := by omega
  have hσ1ptr1 : σ1 (ptr + 1) = d := by
    rw [hσ1frame (ptr + 1) hptr1cur hptr1curJ]; exact hdata
  have heval2 : (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1 = d := by
    have h1 : (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1
        = σ1 (σ1 (σ1 0 + ptrJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hσ1ctl, hσ1ptr]; exact hσ1ptr1
  have hsep2 : (cur + 1) + (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1
      < M + curJ := by rw [heval2]; omega
  obtain ⟨hbits2, hcursor2, hframe2, hctl2⟩ :=
    emitNatProg_eval_state curJ tmpJ M (cur + 1)
      (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))) σ1
      hc1 hc2 hct hσ1ctl hσ1cursor (by omega) hsep2
  rw [heval2] at hbits2 hcursor2 hframe2
  set σ2 := (emitNatProg curJ tmpJ
    (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1)))).eval σ1 with hσ2def
  have hσ2ptr : σ2 (M + ptrJ) = ptr := by
    rw [hframe2 (M + ptrJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσ1ptr
  have haddr3 : (ctlAddr ptrJ).eval σ2 = M + ptrJ := by rw [ctlAddr_eval, hctl2]
  have hval3 : (Expr.add (ctlCell ptrJ) (Expr.const 2)).eval σ2 = ptr + 2 := by
    simp [Expr.eval, ctlCell_eval, hctl2, hσ2ptr]
  have h3eval : (ctlAssign ptrJ (Expr.add (ctlCell ptrJ) (Expr.const 2))).eval σ2
      = writeReg σ2 (M + ptrJ) (ptr + 2) := by
    unfold ctlAssign; rw [eval_assignInd, haddr3, hval3]
  have htop : (emitRawOpBody curJ tmpJ ptrJ).eval σ = writeReg σ2 (M + ptrJ) (ptr + 2) := by
    unfold emitRawOpBody
    rw [eval_seq, eval_seq, ← hσ1def, ← hσ2def, h3eval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htop, bitsAt_append]
    constructor
    · intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      simp only [List.getElem_singleton, Nat.add_zero]
      rw [writeReg_diff σ2 (M + ptrJ) (ptr + 2) cur (by omega)]
      rw [hframe2 cur (by omega) (by omega) (Or.inl (by omega))]
      simpa using hσ1cell
    · have hlen : ([tag] : Bits).length = 1 := rfl
      rw [hlen]
      apply bitsAt_of_frame σ2 _ (cur + 1) (encodeNat d) hbits2
      intro r hr1 hr2
      rw [encodeNat_length] at hr2
      exact writeReg_diff σ2 (M + ptrJ) (ptr + 2) r (by omega)
  · rw [htop, writeReg_diff σ2 (M + ptrJ) (ptr + 2) (M + curJ) (by omega), hcursor2]
  · rw [htop, writeReg_diff σ2 (M + ptrJ) (ptr + 2) 0 (by omega), hctl2]
  · rw [htop, writeReg_same]
  · intro r hrC hrT hrP hrange
    rw [htop, writeReg_diff σ2 (M + ptrJ) (ptr + 2) r hrP]
    rcases hrange with hlt | hge
    · rw [hframe2 r hrC hrT (Or.inl (by omega))]
      rw [hσ1frame r (by omega) hrC]
    · rw [hframe2 r hrC hrT (Or.inr (by omega))]
      rw [hσ1frame r (by omega) hrC]

/-- Emit one row's tagged entry list in `encodeList` shape: `emitListProg` over `emitRawOpBody`,
    with the pointer's initial position staged into `ptrJ` by the caller (usually `row + 2`, past
    the row's key and count cells) rather than reset here, since the pointer's start is
    data-dependent. -/
def emitOpsListProg (curJ tmpJ cntJ ptrJ : ℕ) : Program :=
  emitListProg curJ tmpJ cntJ (emitRawOpBody curJ tmpJ ptrJ)

/-- Invariant for `emitOpsListProg`'s element loop after `m` entries have been emitted from a
    row whose entries start at `rowBase + 2`: the pointer sits exactly `2 * m` cells past that
    start, every not-yet-overwritten entry's tag/value cells are untouched, and the cursor sits
    exactly the total encoded length of the first `m` entries past `cur0`. -/
def EmitOpsListInv (curJ ptrJ M cur0 rowBase cnt : ℕ) (tag : ℕ → Bool) (d : ℕ → ℕ) (m : ℕ)
    (τ : Store) : Prop :=
  τ (M + ptrJ) = rowBase + 2 + 2 * m ∧
  (∀ i, i < cnt → τ (rowBase + 2 + 2 * i) = if tag i then 1 else 0) ∧
  (∀ i, i < cnt → τ (rowBase + 2 + 2 * i + 1) = d i) ∧
  τ (M + curJ) = cur0 + ((List.range m).flatMap (fun i => [tag i] ++ encodeNat (d i))).length

/-- The per-iteration correctness `emitListProg_eval_state`/`emit_loop_flatMap` need from
    `emitRawOpBody`, under `EmitOpsListInv`. It mirrors `emitNatTupleTableProg_hbody`: the
    separation bounds (`hsepFull` through `hsepPtrAll`) are strict on the whole remaining entry
    list, not just the current entry. Unlike a lone `encodeNat`, a run of `[tag] ++ encodeNat d`
    chunks has no uniform spare bit for turning a non-strict global bound into the strict
    per-entry bound required by `emitRawOpBody_eval_state`. -/
lemma emitOpsListProg_hbody (curJ tmpJ ptrJ M cur0 rowBase cnt : ℕ) (tag : ℕ → Bool) (d : ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + curJ)
    (hsepTmpAll : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + tmpJ)
    (hsepPtrAll : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + ptrJ)
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase) :
    ∀ m, m < cnt → ∀ (τ : Store) (cur' : ℕ),
      EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d m τ → τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitRawOpBody curJ tmpJ ptrJ).eval τ) cur' ([tag m] ++ encodeNat (d m)) ∧
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) (M + curJ)
        = cur' + ([tag m] ++ encodeNat (d m)).length ∧
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ → (emitRawOpBody curJ tmpJ ptrJ).eval τ r = τ r) ∧
      EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d (m + 1)
        ((emitRawOpBody curJ tmpJ ptrJ).eval τ) := by
  intro m hmcnt τ cur' hInv hM hcur'
  obtain ⟨hptrCell, htagAll, hdataAll, hcurpin⟩ := hInv
  have hkey : cur' + ([tag m] ++ encodeNat (d m)).length
      ≤ cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    have hsplit := flatMap_range_length_split (fun i => [tag i] ++ encodeNat (d i)) cnt m
      (le_of_lt hmcnt)
    have hnm : cnt - m = (cnt - m - 1) + 1 := by omega
    have hrsplit : List.range' m (cnt - m) = m :: List.range' (m + 1) (cnt - m - 1) := by
      conv_lhs => rw [hnm]
      rw [List.range'_succ]
    have hlen_remaining :
        ((List.range' m (cnt - m)).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
        = ([tag m] ++ encodeNat (d m)).length
          + ((List.range' (m + 1) (cnt - m - 1)).flatMap
            (fun i => [tag i] ++ encodeNat (d i))).length := by
      rw [hrsplit, List.flatMap_cons, List.length_append]
    omega
  have hlenM : ([tag m] ++ encodeNat (d m)).length = d m + 2 := by simp [encodeNat_length]
  rw [hlenM] at hkey
  have hstep : ((List.range m).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      + ([tag m] ++ encodeNat (d m)).length
      = ((List.range (m + 1)).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    have hsplit2 := flatMap_range_length_split (fun i => [tag i] ++ encodeNat (d i)) (m + 1) m
      (by omega)
    have h1 : (m + 1) - m = 1 := by omega
    rw [h1, List.range'_one] at hsplit2
    simpa using hsplit2
  have hsep_v : cur' + 1 + d m < M + curJ := by omega
  have hsepTmp_v : cur' + 1 + d m + 1 ≤ M + tmpJ := by omega
  have hsepPtr_v : cur' + 1 + d m + 1 ≤ M + ptrJ := by omega
  have hcur'1 : 1 ≤ cur' := by omega
  obtain ⟨hbits, hcursor, hctl0, hptrNew, hframe⟩ :=
    emitRawOpBody_eval_state curJ tmpJ ptrJ M cur' (rowBase + 2 + 2 * m) (tag m) (d m) τ
      hc1 hc2 hct hcp htp hM hcur' hcur'1 hptrCell (htagAll m hmcnt) (hdataAll m hmcnt)
      (by omega) (by omega) hsep_v hsepTmp_v hsepPtr_v
  refine ⟨hbits, ?_, hctl0, ?_, ?_⟩
  · rw [hlenM]; omega
  · intro r hr1 hr2
    exact hframe r hr2 (by omega) (by omega) (Or.inl hr1)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have heq : rowBase + 2 + 2 * m + 2 = rowBase + 2 + 2 * (m + 1) := by ring
      rw [hptrNew, heq]
    · intro i hi
      have hne1 : rowBase + 2 + 2 * i ≠ M + curJ := by omega
      have hne2 : rowBase + 2 + 2 * i ≠ M + tmpJ := by omega
      have hne3 : rowBase + 2 + 2 * i ≠ M + ptrJ := by omega
      have hrange : cur' + 1 + d m + 1 ≤ rowBase + 2 + 2 * i := by omega
      exact (hframe (rowBase + 2 + 2 * i) hne1 hne2 hne3 (Or.inr hrange)).trans (htagAll i hi)
    · intro i hi
      have hne1 : rowBase + 2 + 2 * i + 1 ≠ M + curJ := by omega
      have hne2 : rowBase + 2 + 2 * i + 1 ≠ M + tmpJ := by omega
      have hne3 : rowBase + 2 + 2 * i + 1 ≠ M + ptrJ := by omega
      have hrange : cur' + 1 + d m + 1 ≤ rowBase + 2 + 2 * i + 1 := by omega
      exact (hframe (rowBase + 2 + 2 * i + 1) hne1 hne2 hne3 (Or.inr hrange)).trans (hdataAll i hi)
    · have hcur'eq : cur' = cur0
          + ((List.range m).flatMap (fun i => [tag i] ++ encodeNat (d i))).length :=
        hcur'.symm.trans hcurpin
      rw [hcursor, hcur'eq, ← hstep, hlenM]
      omega

/-- Bundled correctness of `emitOpsListProg`. Directly chains `emitNatProg_eval_state` (the length
    prefix) with `emit_loop_flatMap` (the loop) rather than going through `emitListProg_eval_state`'s
    bundled wrapper, so that `emit_loop_flatMap`'s own "cells below the entry cursor survive" frame
    fact can be exposed in the conclusion too: unlike a standalone table emitter, `emitOpsListProg`
    is meant to be chained after an *earlier* emission within the same row (the row key), so
    a caller needs to know that earlier emission's bits survive this one. The final pointer-cell
    value (the next row's head, `rowBase + 2 + 2 * cnt`) is exposed for the same chaining reason. -/
lemma emitOpsListProg_eval_state (curJ tmpJ cntJ ptrJ M cur rowBase cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hcnt : σ (M + cntJ) = cnt) (hptr : σ (M + ptrJ) = rowBase + 2)
    (htagAll : ∀ i, i < cnt → σ (rowBase + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (rowBase + 2 + 2 * i + 1) = d i)
    (hsepCnt : cur + cnt + 1 ≤ M + cntJ)
    (hsepFull : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepPtrAll : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase) :
    BitsAt ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ) cur
      (encodeNat cnt ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))) ∧
    ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ) (M + curJ)
      = cur + cnt + 1 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ∧
    ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ) 0 = M ∧
    ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ) (M + ptrJ) = rowBase + 2 + 2 * cnt ∧
    (∀ r, r < cur → r ≠ M + curJ →
      (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ r = σ r) := by
  have hcntEval : (ctlCell cntJ).eval σ = cnt := by rw [ctlCell_eval, hM, hcnt]
  have hsep'' : cur + (ctlCell cntJ).eval σ < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1 hsep''
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ with hσ1def
  have hInv0 : EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d 0 σ1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hframe1 (M + ptrJ) (by omega) (by omega) (Or.inr (by omega))]; exact hptr
    · intro i hi
      rw [hframe1 (rowBase + 2 + 2 * i) (by omega) (by omega) (Or.inr (by omega))]
      exact htagAll i hi
    · intro i hi
      rw [hframe1 (rowBase + 2 + 2 * i + 1) (by omega) (by omega) (Or.inr (by omega))]
      exact hdataAll i hi
    · rw [hcursor1]; simp
  have hbody := emitOpsListProg_hbody curJ tmpJ ptrJ M (cur + cnt + 1) rowBase cnt tag d
    hc1 hc2 hct hcp htp (by omega) hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
  have hσ1cnt : σ1 (M + cntJ) = cnt := by
    rw [hframe1 (M + cntJ) (by omega) (by omega) (Or.inr (by omega))]; exact hcnt
  have hbound : (ctlCell cntJ).eval σ1 = cnt := by rw [ctlCell_eval, hctl1, hσ1cnt]
  have hforNeval : (Program.forN (ctlCell cntJ) (emitRawOpBody curJ tmpJ ptrJ)).eval σ1
      = loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1 := by rw [eval_forN, hbound]
  have hrangeeq : List.range' 0 cnt = List.range cnt := by rw [List.range_eq_range']
  have hsepLoop : cur + cnt + 1
      + ((List.range' 0 cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ := by
    rw [hrangeeq]; exact hsepFull
  obtain ⟨hbits2, hcursor2, hctl2, hInvn, hframeLoop⟩ :=
    emit_loop_flatMap curJ M (emitRawOpBody curJ tmpJ ptrJ) (fun i => [tag i] ++ encodeNat (d i))
      (EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d) cnt hbody cnt 0 (by omega)
      σ1 (cur + cnt + 1) hInv0 hctl1 hcursor1 hsepLoop
  rw [hrangeeq] at hbits2 hcursor2
  rw [Nat.zero_add] at hInvn
  have htop : (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ
      = loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1 := by
    unfold emitOpsListProg emitListProg
    rw [eval_seq, ← hσ1def, hforNeval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htop]
    have hwin : ∀ r, cur ≤ r → r < cur + (encodeNat cnt).length →
        (loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1) r = σ1 r := by
      intro r hr1 hr2
      rw [encodeNat_length] at hr2
      exact hframeLoop r (by omega) (by omega)
    have hbitsL : BitsAt (loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1) cur (encodeNat cnt) :=
      bitsAt_of_frame σ1 _ cur (encodeNat cnt) hbits1 hwin
    have haddr : cur + (encodeNat cnt).length = cur + cnt + 1 := by rw [encodeNat_length]; omega
    rw [bitsAt_append, haddr]
    exact ⟨hbitsL, hbits2⟩
  · rw [htop]; exact hcursor2
  · rw [htop]; exact hctl2
  · obtain ⟨hptrFinal, -, -, -⟩ := hInvn
    rw [htop]; exact hptrFinal
  · intro r hr1 hr2
    rw [htop, hframeLoop r (by omega) hr2]
    exact hframe1 r hr2 (by omega) (Or.inl hr1)

/-! ## Emitting one whole variable-length row: key, count, then the tagged payload list

The row format is a unary key followed by the length-prefixed tagged payload list that
`emitOpsListProg` handles. `row + 0` holds the key, `row + 1` the payload count (read into `cntJ`),
and `row + 2` the first payload entry's address (staged into `ptrJ` before `emitOpsListProg` runs).
`emitRowBody` chains these four writes plus one more: after the row is fully emitted, `ptrJ`'s
final value (exposed by `emitOpsListProg_eval_state`) is exactly the next row's head, so copying it
into `rowJ` advances to the next row without recomputing `2 * cnt` from scratch. -/

/-- Emit one whole variable-length row: stage the payload count into `cntJ`, emit the row key in
    unary, stage the first payload entry's address into `ptrJ`, emit the tagged payload list, then
    advance `rowJ` to the next row's head by copying `ptrJ`'s final value. -/
def emitRowBody (curJ tmpJ cntJ ptrJ rowJ : ℕ) : Program :=
  .seq (.seq (.seq (.seq
    (ctlAssign cntJ (.regInd (.add (ctlCell rowJ) (.const 1))))
    (emitNatProg curJ tmpJ (.regInd (ctlCell rowJ))))
    (ctlAssign ptrJ (.add (ctlCell rowJ) (.const 2))))
    (emitOpsListProg curJ tmpJ cntJ ptrJ))
    (ctlAssign rowJ (ctlCell ptrJ))

/-- First phase of `emitRowBody`: stage the payload count into `cntJ`, then emit the row key. -/
lemma emitRowBody_eval_state_key_phase (curJ tmpJ cntJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpRow : tmpJ ≠ rowJ) (hCntRow : cntJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hrowKey : σ row = rowKey) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row) (hloCnt : M + cntJ < row)
    (hsepCur : cur + (rowKey + 1) ≤ M + curJ) (hsepCnt : cur + (rowKey + 1) ≤ M + cntJ)
    (hsepRow : cur + (rowKey + 1) ≤ M + rowJ) :
    ∃ σB : Store,
      σB = (emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval
        ((ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ) ∧
      BitsAt σB cur (encodeNat rowKey) ∧
      σB (M + curJ) = cur + rowKey + 1 ∧
      σB 0 = M ∧
      σB (M + cntJ) = cnt ∧
      σB (M + rowJ) = row ∧
      (∀ i, i < cnt → σB (row + 2 + 2 * i) = if tag i then 1 else 0) ∧
      (∀ i, i < cnt → σB (row + 2 + 2 * i + 1) = d i) := by
  have hexprA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    have h1 : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ
        = σ (σ (σ 0 + rowJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hrowCell]; exact hcntCell
  have hAcnt : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + cntJ) = cnt := by
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]; exact hexprA
  have hAframe : ∀ r, r ≠ M + cntJ →
      (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ r = σ r :=
    fun r hr => ctlAssign_eval_diff cntJ _ σ r (by omega)
  generalize (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ = σA
    at hAcnt hAframe
  have hA0 : σA 0 = M := by rw [hAframe 0 (by omega)]; exact hM
  have hAcur : σA (M + curJ) = cur := by rw [hAframe _ (by omega)]; exact hcur
  have hArow : σA (M + rowJ) = row := by rw [hAframe _ (by omega)]; exact hrowCell
  have hexprB : (Expr.regInd (ctlCell rowJ)).eval σA = rowKey := by
    have h1 : (Expr.regInd (ctlCell rowJ)).eval σA = σA (σA (σA 0 + rowJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hA0, hArow, hAframe row (by omega)]; exact hrowKey
  obtain ⟨hbitsB, hcursorB, hframeB, hctlB⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (Expr.regInd (ctlCell rowJ)) σA
      hc1 hc2 hCurTmp hA0 hAcur hcur1 (by rw [hexprB]; omega)
  rw [hexprB] at hbitsB hcursorB hframeB
  refine ⟨_, rfl, hbitsB, hcursorB, hctlB, ?_, ?_, ?_, ?_⟩
  · rw [hframeB _ (by omega) (by omega) (Or.inr (by omega))]; exact hAcnt
  · rw [hframeB _ (by omega) (by omega) (Or.inr (by omega))]; exact hArow
  · intro i hi
    rw [hframeB _ (by omega) (by omega) (Or.inr (by omega)), hAframe _ (by omega)]
    exact htagAll i hi
  · intro i hi
    rw [hframeB _ (by omega) (by omega) (Or.inr (by omega)), hAframe _ (by omega)]
    exact hdataAll i hi

/-- Second phase of `emitRowBody`: stage the first payload entry's address into `ptrJ`. -/
lemma emitRowBody_eval_state_ptr_phase (curJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σB : Store)
    (hCurPtr : curJ ≠ ptrJ) (hCntPtr : cntJ ≠ ptrJ) (hcur1 : 1 ≤ cur)
    (hbitsB : BitsAt σB cur (encodeNat rowKey))
    (hcurB : σB (M + curJ) = cur + rowKey + 1) (h0B : σB 0 = M)
    (hcntB : σB (M + cntJ) = cnt) (hrowB : σB (M + rowJ) = row)
    (htagB : ∀ i, i < cnt → σB (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataB : ∀ i, i < cnt → σB (row + 2 + 2 * i + 1) = d i)
    (hloPtr : M + ptrJ < row) (hsepPtr : cur + (rowKey + 1) ≤ M + ptrJ) :
    ∃ σC : Store,
      σC = (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB ∧
      BitsAt σC cur (encodeNat rowKey) ∧
      σC (M + curJ) = cur + rowKey + 1 ∧
      σC 0 = M ∧
      σC (M + cntJ) = cnt ∧
      σC (M + ptrJ) = row + 2 ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0) ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i) := by
  have hframe : ∀ r, r ≠ M + ptrJ →
      (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB r = σB r :=
    fun r hr => ctlAssign_eval_diff ptrJ _ σB r (by omega)
  have hexprC : (Expr.add (ctlCell rowJ) (Expr.const 2)).eval σB = row + 2 := by
    simp [Expr.eval, ctlCell_eval, h0B, hrowB]
  have hptr : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB
      (M + ptrJ) = row + 2 := by
    have h := ctlAssign_eval_same ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2)) σB
    rw [h0B] at h
    rw [h]; exact hexprC
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, hptr, ?_, ?_⟩
  · refine bitsAt_of_frame σB _ cur (encodeNat rowKey) hbitsB fun r hr1 hr2 => ?_
    rw [encodeNat_length] at hr2
    exact hframe r (by omega)
  · rw [hframe _ (by omega)]; exact hcurB
  · rw [hframe _ (by omega)]; exact h0B
  · rw [hframe _ (by omega)]; exact hcntB
  · intro i hi
    rw [hframe _ (by omega)]; exact htagB i hi
  · intro i hi
    rw [hframe _ (by omega)]; exact hdataB i hi

/-- Final phase of `emitRowBody`: emit the tagged payload list, then advance `rowJ` to the next
    row's head. -/
lemma emitRowBody_eval_state_tail_phase (curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σC : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hC0 : σC 0 = M) (hcurC : σC (M + curJ) = cur + rowKey + 1) (hcntC : σC (M + cntJ) = cnt)
    (hptrC : σC (M + ptrJ) = row + 2)
    (htagC : ∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataC : ∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    ∃ σE : Store,
      σE = (ctlAssign rowJ (ctlCell ptrJ)).eval ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC) ∧
      BitsAt σE (cur + rowKey + 1) (encodeNat cnt
        ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))) ∧
      σE (M + curJ) = cur + (rowKey + 1) + (cnt + 1)
        + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ∧
      σE 0 = M ∧
      σE (M + rowJ) = row + 2 * cnt + 2 ∧
      (∀ r, r < cur + rowKey + 1 → r ≠ M + curJ → r ≠ M + rowJ → σE r = σC r) := by
  obtain ⟨hbitsD, hcursorD, hctlD, hptrD, hframeD⟩ :=
    emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M (cur + rowKey + 1) row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hC0 hcurC (by omega) hcntC hptrC htagC hdataC
      (by omega) (by omega) (by omega) (by omega) hloCur hloTmp hloPtr
  generalize (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC = σD at hbitsD hcursorD hctlD hptrD hframeD
  have hframe : ∀ r, r ≠ M + rowJ → (ctlAssign rowJ (ctlCell ptrJ)).eval σD r = σD r :=
    fun r hr => ctlAssign_eval_diff rowJ _ σD r (by omega)
  have hrow : (ctlAssign rowJ (ctlCell ptrJ)).eval σD (M + rowJ) = row + 2 * cnt + 2 := by
    have h := ctlAssign_eval_same rowJ (ctlCell ptrJ) σD
    rw [hctlD] at h
    rw [h, ctlCell_eval, hctlD, hptrD]; omega
  have hlen : (encodeNat cnt ++ (List.range cnt).flatMap
      (fun i => [tag i] ++ encodeNat (d i))).length
      = cnt + 1 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    rw [List.length_append, encodeNat_length]
  refine ⟨_, rfl, ?_, ?_, ?_, hrow, ?_⟩
  · refine bitsAt_of_frame σD _ _ _ hbitsD fun r _ hr2 => hframe r (by rw [hlen] at hr2; omega)
  · rw [hframe _ (by omega), hcursorD]; omega
  · rw [hframe _ (by omega)]; exact hctlD
  · intro r hr1 hr2 hr3
    rw [hframe r hr3]
    exact hframeD r (by omega) hr2

/-- Bundled correctness of `emitRowBody`: the store after running it holds `encodeNat rowKey ++
    (encodeNat cnt ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i)))` at the
    entry cursor — the canonical variable-row shape once `tag i`/`d i` are supplied — the cursor
    has advanced past the whole row, cell `0` still holds `M`, and
    `rowJ` now points at the next row's head. Chains `ctlAssign`/`emitNatProg_eval_state` (the
    row key) with `emitOpsListProg_eval_state` (the tagged payload list), reading off the latter's
    exposed "cells below the entry cursor survive" frame and final pointer value to carry the
    row key's bits and to advance `rowJ` without recomputing `2 * cnt`. All five separation
    families (`hsepFull` through `hsepRowAll`) are strict on the *whole* row's combined length, for
    the same reason `emitOpsListProg_hbody` needs a strict bound: a run of variable-width chunks has
    no single uniform spare bit to peel off a non-strict bound. -/
lemma emitRowBody_eval_state (curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hrowKey : σ row = rowKey) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    BitsAt ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ) cur
      (encodeNat rowKey ++ (encodeNat cnt
        ++ (List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i)))) ∧
    ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ) (M + curJ)
      = cur + (rowKey + 1) + (cnt + 1)
        + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ∧
    ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ) 0 = M ∧
    ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ) (M + rowJ) = row + 2 * cnt + 2 := by
  obtain ⟨σB, hσB, hbitsB, hcurB, h0B, hcntB, hrowB, htagB, hdataB⟩ :=
    emitRowBody_eval_state_key_phase curJ tmpJ cntJ rowJ M cur row rowKey cnt tag d σ
      hc1 hc2 hCurTmp hCurCnt hCurRow hTmpCnt hTmpRow hCntRow hM hcur hcur1 hrowCell hrowKey
      hcntCell htagAll hdataAll hloCur hloTmp hloCnt (by omega) (by omega) (by omega)
  obtain ⟨σC, hσC, hbitsC, hcurC, h0C, hcntC, hptrC, htagC, hdataC⟩ :=
    emitRowBody_eval_state_ptr_phase curJ cntJ ptrJ rowJ M cur row rowKey cnt tag d σB
      hCurPtr hCntPtr hcur1 hbitsB hcurB h0B hcntB hrowB htagB hdataB hloPtr (by omega)
  obtain ⟨σE, hσE, hbitsE, hcurE, h0E, hrowE, hframeE⟩ :=
    emitRowBody_eval_state_tail_phase curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntRow hPtrRow
      h0C hcurC hcntC hptrC htagC hdataC hloCur hloTmp hloPtr
      hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
  have htop : (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ = σE := by
    unfold emitRowBody
    rw [eval_seq, eval_seq, eval_seq, eval_seq, ← hσB, ← hσC]
    exact hσE.symm
  have haddr : cur + (encodeNat rowKey).length = cur + rowKey + 1 := by
    rw [encodeNat_length]; omega
  rw [htop]
  refine ⟨?_, ?_, h0E, hrowE⟩
  · rw [bitsAt_append, haddr]
    refine ⟨bitsAt_of_frame σC _ cur _ hbitsC fun r hr1 hr2 => ?_, hbitsE⟩
    rw [encodeNat_length] at hr2
    exact hframeE r (by omega) (by omega) (by omega)
  · exact hcurE

/-! ## Frame companion for `emitRowBody`

`emitRowBody_eval_state` does not expose a "cells below the entry cursor survive" frame, unlike
`emitOpsListProg_eval_state` (which does, for the same chaining reason). That frame is exactly the
`hbody` obligation `emitListProg_eval_state`/`emit_loop_flatMap` need to emit a whole *table* of
rows: without it, later rows' emission could not be shown to preserve earlier rows' bits.
`emitRowBody_state_upto_ptr` factors out the state-tracing common to both the data (`emitRowBody`'s
own four chained steps up to staging `ptrJ`) and the frame chain through those steps; it is also
reused directly by `CanonicalStoreFinalizeBody.lean` (cost/`ProgramBoundedIn`), while the
two-sided companion (`emitRowBody_frame_two_sided`) is built separately below from
`emitRowBody_state_upto_ptr_two_sided`. -/

lemma emitRowBody_state_upto_ptr (curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hrowKey : σ row = rowKey) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    ∃ σC : Store,
      σC (M + curJ) = cur + rowKey + 1 ∧
      σC 0 = M ∧
      σC (M + cntJ) = cnt ∧
      σC (M + ptrJ) = row + 2 ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0) ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i) ∧
      ((ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval
        ((emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval
          ((ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ))
        = σC) ∧
      (∀ r, r < cur → r ≠ M + curJ → σC r = σ r) := by
  have hexprA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    have h1 : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ
        = σ (σ (σ 0 + rowJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hrowCell]; exact hcntCell
  have hσAcnt : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + cntJ) = cnt := by
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]; exact hexprA
  set σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
    with hσAdef
  have hσArow : σA (M + rowJ) = row := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by omega)]; exact hrowCell
  have hσAcur : σA (M + curJ) = cur := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + curJ) (by omega)]; exact hcur
  have hσA0 : σA 0 = M := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ 0 (by omega)]; exact hM
  have hσArowKey : σA row = rowKey := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ row (by omega)]; exact hrowKey
  have hσAtagAll : ∀ i, i < cnt → σA (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i) (by omega)]
    exact htagAll i hi
  have hσAdataAll : ∀ i, i < cnt → σA (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i + 1) (by omega)]
    exact hdataAll i hi
  have hexprB : (Expr.regInd (ctlCell rowJ)).eval σA = rowKey := by
    have h1 : (Expr.regInd (ctlCell rowJ)).eval σA = σA (σA (σA 0 + rowJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hσA0, hσArow]; exact hσArowKey
  have hsepB : cur + (Expr.regInd (ctlCell rowJ)).eval σA < M + curJ := by
    rw [hexprB]; omega
  obtain ⟨-, hcursorB, hframeB, hctlB⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (Expr.regInd (ctlCell rowJ)) σA
      hc1 hc2 hCurTmp hσA0 hσAcur hcur1 hsepB
  rw [hexprB] at hcursorB hframeB
  set σB := (emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval σA with hσBdef
  have hσBrow : σB (M + rowJ) = row := by
    rw [hframeB (M + rowJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσArow
  have hσBcnt : σB (M + cntJ) = cnt := by
    rw [hframeB (M + cntJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσAcnt
  have hσBtagAll : ∀ i, i < cnt → σB (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hframeB (row + 2 + 2 * i) (by omega) (by omega) (Or.inr (by omega))]
    exact hσAtagAll i hi
  have hσBdataAll : ∀ i, i < cnt → σB (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hframeB (row + 2 + 2 * i + 1) (by omega) (by omega) (Or.inr (by omega))]
    exact hσAdataAll i hi
  have hexprC : (Expr.add (ctlCell rowJ) (Expr.const 2)).eval σB = row + 2 := by
    simp [Expr.eval, ctlCell_eval, hctlB, hσBrow]
  have hσCptr : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB
      (M + ptrJ) = row + 2 := by
    have h := ctlAssign_eval_same ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2)) σB
    rw [hctlB] at h
    rw [h]; exact hexprC
  refine ⟨(ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB,
    ?_, ?_, ?_, hσCptr, ?_, ?_, rfl, ?_⟩
  · rw [ctlAssign_eval_diff ptrJ _ σB (M + curJ) (by omega)]; exact hcursorB
  · rw [ctlAssign_eval_diff ptrJ _ σB 0 (by omega)]; exact hctlB
  · rw [ctlAssign_eval_diff ptrJ _ σB (M + cntJ) (by omega)]; exact hσBcnt
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σB (row + 2 + 2 * i) (by omega)]
    exact hσBtagAll i hi
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σB (row + 2 + 2 * i + 1) (by omega)]
    exact hσBdataAll i hi
  · intro r hr hrCur
    have e3 : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB r = σB r :=
      ctlAssign_eval_diff ptrJ _ σB r (by omega)
    have e4 : σB r = σA r := hframeB r hrCur (by omega) (Or.inl hr)
    have e5 : σA r = σ r := by
      rw [hσAdef, ctlAssign_eval_diff cntJ _ σ r (by omega)]
    rw [e3, e4, e5]

/-! ## Variable-length row table: cumulative address and cursor bookkeeping

Row `q` of a variable-length row table occupies `2 + 2 * cntG q` physical RAM cells (row key,
payload count, then two cells per payload entry), so row `m`'s physical address is
`tbl + (prefix sum of row widths below m)`, not a closed-form multiple of `m`. Modeling that prefix
sum as the *length* of a `flatMap` of `List.replicate` chunks lets the already-proved
`flatMap_range_length_split` supply the successor step for free, exactly as it does for
`emitNatTableProg`'s and `emitOpsListProg`'s own address bookkeeping. `rowTableBitsLen` does the
same for the cumulative *encoded output length* (needed for the cursor), over the actual
variable-row chunks rather than filler bits. -/

/-- Cumulative physical width, in RAM cells, of the first `m` rows of a variable-length row table
    (row `q` occupies `2 + 2 * cntG q` cells). -/
def rowTableWidth (cntG : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((List.range m).flatMap (fun q => List.replicate (2 + 2 * cntG q) false)).length

lemma rowTableWidth_succ (cntG : ℕ → ℕ) (m : ℕ) :
    rowTableWidth cntG (m + 1) = rowTableWidth cntG m + (2 + 2 * cntG m) := by
  unfold rowTableWidth
  have hsplit := flatMap_range_length_split (fun q => List.replicate (2 + 2 * cntG q) false)
    (m + 1) m (by omega)
  have h1 : (m + 1) - m = 1 := by omega
  rw [h1, List.range'_one] at hsplit
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_replicate] at hsplit
  omega

/-- A uniform per-row cap `c` on `cntG` below `m` bounds the whole table's cumulative width by
    `m` copies of the per-row cap `2 + 2 * c`. -/
lemma rowTableWidth_le_of_count_le (cntG : ℕ → ℕ) (m c : ℕ) (h : ∀ k < m, cntG k ≤ c) :
    rowTableWidth cntG m ≤ m * (2 + 2 * c) := by
  induction m with
  | zero => simp [rowTableWidth]
  | succ m ih =>
    rw [rowTableWidth_succ]
    have hc := h m (by omega)
    have hi := ih (fun k hk => h k (by omega))
    have hmul : (m + 1) * (2 + 2 * c) = m * (2 + 2 * c) + (2 + 2 * c) := by ring
    rw [hmul]
    omega

/-- Cumulative encoded bit-length of the first `m` variable-length rows' output. -/
def rowTableBitsLen (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  ((List.range m).flatMap (fun q => encodeNat (rowKeyG q) ++ (encodeNat (cntG q)
    ++ (List.range (cntG q)).flatMap (fun i => [tagG q i] ++ encodeNat (dG q i))))).length

lemma rowTableBitsLen_succ (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (m : ℕ) :
    rowTableBitsLen rowKeyG cntG tagG dG (m + 1) = rowTableBitsLen rowKeyG cntG tagG dG m
      + ((rowKeyG m + 1) + (cntG m + 1)
        + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length) := by
  unfold rowTableBitsLen
  have hsplit := flatMap_range_length_split
    (fun q => encodeNat (rowKeyG q) ++ (encodeNat (cntG q)
      ++ (List.range (cntG q)).flatMap (fun i => [tagG q i] ++ encodeNat (dG q i))))
    (m + 1) m (by omega)
  have h1 : (m + 1) - m = 1 := by omega
  rw [h1, List.range'_one] at hsplit
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_append, encodeNat_length, encodeNat_length] at hsplit
  omega

/-! ## Two-sided frame companions: preserving scratch data across a whole loop

`emit_loop_flatMap`'s exposed frame only protects cells *below* the entry cursor, which suffices to
chain emitters in sequence but not to show a table emitter's *own scratch/source data* (read, never
written, at addresses past every control cell) survives the emission of entries other than the one
currently being read. `emitNatTableProg_hbody` sidesteps this by never going through
`emitListProg_eval_state`'s bundled wrapper, instead inlining `emit_loop_flatMap` directly so its own
per-iteration body's two-sided frame (`emitNatTableBody_eval_state`'s) is available at every step.
`emitOpsListProg_eval_state`, however, already *is* bundled the same way but only ever exposed the
one-sided half; `emit_loop_flatMap_frame_two_sided` reruns the same induction with a two-sided
per-iteration hypothesis to recover the missing half generically, and
`emitOpsListProg_hbody_two_sided`/`emitOpsListProg_frame_two_sided` instantiate it for
`emitRawOpBody` (whose own frame, like `emitNatTableBody`'s, is already two-sided). A row table's
per-row emitter (`emitRowBody`) needs exactly this two-sided fact one level up, to show *other
rows'* raw data survives emitting the current row. -/

lemma emit_loop_flatMap_frame_two_sided (curJ M : ℕ) (body : Program) (f : ℕ → Bits)
    (Inv : ℕ → Store → Prop) (Ctl : ℕ → Prop) (n : ℕ)
    (hbody : ∀ m, m < n → ∀ τ cur, Inv m τ → τ 0 = M → τ (M + curJ) = cur →
      (body.eval τ) (M + curJ) = cur + (f m).length ∧
      (body.eval τ) 0 = M ∧
      (∀ r, ¬ Ctl r → (r < cur ∨ cur + (f m).length ≤ r) → (body.eval τ) r = τ r) ∧
      Inv (m + 1) (body.eval τ)) :
    ∀ (t k : ℕ), k + t ≤ n → ∀ (τ : Store) (cur : ℕ), Inv k τ → τ 0 = M → τ (M + curJ) = cur →
      ∀ r, ¬ Ctl r → (r < cur ∨ cur + ((List.range' k t).flatMap f).length ≤ r) →
        (loopEval body t τ) r = τ r := by
  intro t
  induction t with
  | zero =>
    intro k _ τ cur _ _ _ r _ _
    rw [loopEval_zero]
  | succ t ih =>
    intro k hk τ cur hInv h0 hcur r hCtl hr
    have hkn : k < n := by omega
    obtain ⟨hcursor, h0', hframe, hInv'⟩ := hbody k hkn τ cur hInv h0 hcur
    have hk1t : (k + 1) + t ≤ n := by omega
    have hloopstep : loopEval body (t + 1) τ = loopEval body t (body.eval τ) :=
      loopEval_succ body t τ
    have hlen : ((List.range' k (t + 1)).flatMap f).length
        = (f k).length + ((List.range' (k + 1) t).flatMap f).length := by
      rw [List.range'_succ, List.flatMap_cons, List.length_append]
    rw [hloopstep]
    rcases hr with hlt | hge
    · have hr1 : r < cur := hlt
      have hr2 : r < cur + (f k).length := by omega
      rw [ih (k + 1) hk1t (body.eval τ) (cur + (f k).length) hInv' h0' hcursor r hCtl (Or.inl hr2)]
      exact hframe r hCtl (Or.inl hr1)
    · have hr1 : cur + ((f k).length + ((List.range' (k + 1) t).flatMap f).length) ≤ r := by
        rw [← hlen]; exact hge
      have hr2 : cur + (f k).length + ((List.range' (k + 1) t).flatMap f).length ≤ r := by omega
      rw [ih (k + 1) hk1t (body.eval τ) (cur + (f k).length) hInv' h0' hcursor r hCtl (Or.inr hr2)]
      exact hframe r hCtl (Or.inr (by omega))

/-- The per-iteration two-sided obligation `emit_loop_flatMap_frame_two_sided` needs from
    `emitRawOpBody`, under `EmitOpsListInv`: identical bookkeeping to `emitOpsListProg_hbody`, but
    exposing `emitRawOpBody_eval_state`'s frame in full instead of narrowing it to the one-sided
    half. -/
lemma emitOpsListProg_hbody_two_sided (curJ tmpJ ptrJ M cur0 rowBase cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + curJ)
    (hsepTmpAll : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + tmpJ)
    (hsepPtrAll : cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      ≤ M + ptrJ)
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase) :
    ∀ m, m < cnt → ∀ (τ : Store) (cur' : ℕ),
      EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d m τ → τ 0 = M → τ (M + curJ) = cur' →
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) (M + curJ)
        = cur' + ([tag m] ++ encodeNat (d m)).length ∧
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) 0 = M ∧
      (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + ptrJ →
        (r < cur' ∨ cur' + ([tag m] ++ encodeNat (d m)).length ≤ r) →
        (emitRawOpBody curJ tmpJ ptrJ).eval τ r = τ r) ∧
      EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d (m + 1)
        ((emitRawOpBody curJ tmpJ ptrJ).eval τ) := by
  intro m hmcnt τ cur' hInv hM hcur'
  obtain ⟨hptrCell, htagAll, hdataAll, hcurpin⟩ := hInv
  have hkey : cur' + ([tag m] ++ encodeNat (d m)).length
      ≤ cur0 + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    have hsplit := flatMap_range_length_split (fun i => [tag i] ++ encodeNat (d i)) cnt m
      (le_of_lt hmcnt)
    have hnm : cnt - m = (cnt - m - 1) + 1 := by omega
    have hrsplit : List.range' m (cnt - m) = m :: List.range' (m + 1) (cnt - m - 1) := by
      conv_lhs => rw [hnm]
      rw [List.range'_succ]
    have hlen_remaining :
        ((List.range' m (cnt - m)).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
        = ([tag m] ++ encodeNat (d m)).length
          + ((List.range' (m + 1) (cnt - m - 1)).flatMap
            (fun i => [tag i] ++ encodeNat (d i))).length := by
      rw [hrsplit, List.flatMap_cons, List.length_append]
    omega
  have hlenM : ([tag m] ++ encodeNat (d m)).length = d m + 2 := by simp [encodeNat_length]
  rw [hlenM] at hkey
  have hstep : ((List.range m).flatMap (fun i => [tag i] ++ encodeNat (d i))).length
      + ([tag m] ++ encodeNat (d m)).length
      = ((List.range (m + 1)).flatMap (fun i => [tag i] ++ encodeNat (d i))).length := by
    have hsplit2 := flatMap_range_length_split (fun i => [tag i] ++ encodeNat (d i)) (m + 1) m
      (by omega)
    have h1 : (m + 1) - m = 1 := by omega
    rw [h1, List.range'_one] at hsplit2
    simpa using hsplit2
  have hsep_v : cur' + 1 + d m < M + curJ := by omega
  have hsepTmp_v : cur' + 1 + d m + 1 ≤ M + tmpJ := by omega
  have hsepPtr_v : cur' + 1 + d m + 1 ≤ M + ptrJ := by omega
  have hcur'1 : 1 ≤ cur' := by omega
  obtain ⟨hbits, hcursor, hctl0, hptrNew, hframe⟩ :=
    emitRawOpBody_eval_state curJ tmpJ ptrJ M cur' (rowBase + 2 + 2 * m) (tag m) (d m) τ
      hc1 hc2 hct hcp htp hM hcur' hcur'1 hptrCell (htagAll m hmcnt) (hdataAll m hmcnt)
      (by omega) (by omega) hsep_v hsepTmp_v hsepPtr_v
  refine ⟨?_, hctl0, ?_, ?_⟩
  · rw [hlenM]; omega
  · intro r hrC hrT hrP hr
    rw [hlenM] at hr
    rcases hr with hlt | hge
    · exact hframe r hrC hrT hrP (Or.inl hlt)
    · exact hframe r hrC hrT hrP (Or.inr (by omega))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have heq : rowBase + 2 + 2 * m + 2 = rowBase + 2 + 2 * (m + 1) := by ring
      rw [hptrNew, heq]
    · intro i hi
      have hne1 : rowBase + 2 + 2 * i ≠ M + curJ := by omega
      have hne2 : rowBase + 2 + 2 * i ≠ M + tmpJ := by omega
      have hne3 : rowBase + 2 + 2 * i ≠ M + ptrJ := by omega
      have hrange : cur' + 1 + d m + 1 ≤ rowBase + 2 + 2 * i := by omega
      exact (hframe (rowBase + 2 + 2 * i) hne1 hne2 hne3 (Or.inr hrange)).trans (htagAll i hi)
    · intro i hi
      have hne1 : rowBase + 2 + 2 * i + 1 ≠ M + curJ := by omega
      have hne2 : rowBase + 2 + 2 * i + 1 ≠ M + tmpJ := by omega
      have hne3 : rowBase + 2 + 2 * i + 1 ≠ M + ptrJ := by omega
      have hrange : cur' + 1 + d m + 1 ≤ rowBase + 2 + 2 * i + 1 := by omega
      exact (hframe (rowBase + 2 + 2 * i + 1) hne1 hne2 hne3 (Or.inr hrange)).trans (hdataAll i hi)
    · have hcur'eq : cur' = cur0
          + ((List.range m).flatMap (fun i => [tag i] ++ encodeNat (d i))).length :=
        hcur'.symm.trans hcurpin
      rw [hcursor, hcur'eq, ← hstep, hlenM]
      omega

/-- Two-sided frame companion for `emitOpsListProg`: cells other than `curJ`/`tmpJ`/`ptrJ` outside
    the whole entry list's write window survive. Chains `emitNatProg_eval_state`'s own
    two-sided frame (length prefix) with `emit_loop_flatMap_frame_two_sided` instantiated at
    `emitOpsListProg_hbody_two_sided`. -/
lemma emitOpsListProg_frame_two_sided (curJ tmpJ cntJ ptrJ M cur rowBase cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hcnt : σ (M + cntJ) = cnt) (hptr : σ (M + ptrJ) = rowBase + 2)
    (htagAll : ∀ i, i < cnt → σ (rowBase + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (rowBase + 2 + 2 * i + 1) = d i)
    (hsepCnt : cur + cnt + 1 ≤ M + cntJ)
    (hsepFull : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepPtrAll : cur + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase) :
    ∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + ptrJ →
      (r < cur ∨ cur + cnt + 1
        + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ r) →
      (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ r = σ r := by
  have hcntEval : (ctlCell cntJ).eval σ = cnt := by rw [ctlCell_eval, hM, hcnt]
  have hsep'' : cur + (ctlCell cntJ).eval σ < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1 hsep''
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ with hσ1def
  have hInv0 : EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d 0 σ1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hframe1 (M + ptrJ) (by omega) (by omega) (Or.inr (by omega))]; exact hptr
    · intro i hi
      rw [hframe1 (rowBase + 2 + 2 * i) (by omega) (by omega) (Or.inr (by omega))]
      exact htagAll i hi
    · intro i hi
      rw [hframe1 (rowBase + 2 + 2 * i + 1) (by omega) (by omega) (Or.inr (by omega))]
      exact hdataAll i hi
    · rw [hcursor1]; simp
  have hbody := emitOpsListProg_hbody_two_sided curJ tmpJ ptrJ M (cur + cnt + 1) rowBase cnt tag d
    hc1 hc2 hct hcp htp (by omega) hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
  have hbody' : ∀ m, m < cnt → ∀ (τ : Store) (cur' : ℕ),
      EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d m τ →
      τ 0 = M → τ (M + curJ) = cur' →
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) (M + curJ)
        = cur' + ([tag m] ++ encodeNat (d m)).length ∧
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) 0 = M ∧
      (∀ r, ¬ (r = M + curJ ∨ r = M + tmpJ ∨ r = M + ptrJ) →
        (r < cur' ∨ cur' + ([tag m] ++ encodeNat (d m)).length ≤ r) →
        (emitRawOpBody curJ tmpJ ptrJ).eval τ r = τ r) ∧
      EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d (m + 1)
        ((emitRawOpBody curJ tmpJ ptrJ).eval τ) := by
    intro m hm τ cur' hInv hτ0 hτcur
    obtain ⟨h1, h2, h3, h4⟩ := hbody m hm τ cur' hInv hτ0 hτcur
    exact ⟨h1, h2, fun r hr => h3 r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
      (fun h => hr (Or.inr (Or.inr h))), h4⟩
  have hσ1cnt : σ1 (M + cntJ) = cnt := by
    rw [hframe1 (M + cntJ) (by omega) (by omega) (Or.inr (by omega))]; exact hcnt
  have hbound : (ctlCell cntJ).eval σ1 = cnt := by rw [ctlCell_eval, hctl1, hσ1cnt]
  have hforNeval : (Program.forN (ctlCell cntJ) (emitRawOpBody curJ tmpJ ptrJ)).eval σ1
      = loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1 := by rw [eval_forN, hbound]
  have hrangeeq : List.range' 0 cnt = List.range cnt := by rw [List.range_eq_range']
  have hframeLoop :=
    emit_loop_flatMap_frame_two_sided curJ M (emitRawOpBody curJ tmpJ ptrJ)
      (fun i => [tag i] ++ encodeNat (d i))
      (EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d)
      (fun r => r = M + curJ ∨ r = M + tmpJ ∨ r = M + ptrJ) cnt hbody'
      cnt 0 (by omega) σ1 (cur + cnt + 1) hInv0 hctl1 hcursor1
  rw [hrangeeq] at hframeLoop
  have htop : (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σ
      = loopEval (emitRawOpBody curJ tmpJ ptrJ) cnt σ1 := by
    unfold emitOpsListProg emitListProg
    rw [eval_seq, ← hσ1def, hforNeval]
  intro r hrC hrT hrP hr
  rw [htop]
  have hNotCtl : ¬ (r = M + curJ ∨ r = M + tmpJ ∨ r = M + ptrJ) := by
    rintro (h | h | h)
    · exact hrC h
    · exact hrT h
    · exact hrP h
  rcases hr with hlt | hge
  · rw [hframeLoop r hNotCtl (Or.inl (by omega))]
    exact hframe1 r hrC hrT (Or.inl hlt)
  · rw [hframeLoop r hNotCtl (Or.inr hge)]
    exact hframe1 r hrC hrT (Or.inr (by omega))

/-! ## Two-sided frame for `emitRowBody`

Reruns `emitRowBody_state_upto_ptr`'s state trace with `emitNatProg_eval_state`'s frame exposed in
full (it is already two-sided, unlike `emitOpsListProg`'s bundled wrapper) so `emitRowBody`'s own
two-sided frame can chain onto `emitOpsListProg_frame_two_sided` instead of the one-sided
`emitOpsListProg_eval_state`. This is the fact a row *table* emitter needs to show one row's
emission leaves every other row's raw data untouched. -/

lemma emitRowBody_state_upto_ptr_two_sided (curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hrowKey : σ row = rowKey) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    ∃ σC : Store,
      σC (M + curJ) = cur + rowKey + 1 ∧
      σC 0 = M ∧
      σC (M + cntJ) = cnt ∧
      σC (M + ptrJ) = row + 2 ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i) = if tag i then 1 else 0) ∧
      (∀ i, i < cnt → σC (row + 2 + 2 * i + 1) = d i) ∧
      ((ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval
        ((emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval
          ((ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ))
        = σC) ∧
      (∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + cntJ → r ≠ M + ptrJ →
        (r < cur ∨ cur + rowKey + 1 ≤ r) → σC r = σ r) := by
  have hexprA : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ = cnt := by
    have h1 : (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))).eval σ
        = σ (σ (σ 0 + rowJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hM, hrowCell]; exact hcntCell
  have hσAcnt : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + cntJ) = cnt := by
    have h := ctlAssign_eval_same cntJ
      (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) σ
    rw [hM] at h
    rw [h]; exact hexprA
  set σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
    with hσAdef
  have hσArow : σA (M + rowJ) = row := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by omega)]; exact hrowCell
  have hσAcur : σA (M + curJ) = cur := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (M + curJ) (by omega)]; exact hcur
  have hσA0 : σA 0 = M := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ 0 (by omega)]; exact hM
  have hσArowKey : σA row = rowKey := by
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ row (by omega)]; exact hrowKey
  have hσAtagAll : ∀ i, i < cnt → σA (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i) (by omega)]
    exact htagAll i hi
  have hσAdataAll : ∀ i, i < cnt → σA (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ (row + 2 + 2 * i + 1) (by omega)]
    exact hdataAll i hi
  have hexprB : (Expr.regInd (ctlCell rowJ)).eval σA = rowKey := by
    have h1 : (Expr.regInd (ctlCell rowJ)).eval σA = σA (σA (σA 0 + rowJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hσA0, hσArow]; exact hσArowKey
  have hsepB : cur + (Expr.regInd (ctlCell rowJ)).eval σA < M + curJ := by
    rw [hexprB]; omega
  obtain ⟨-, hcursorB, hframeB, hctlB⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (Expr.regInd (ctlCell rowJ)) σA
      hc1 hc2 hCurTmp hσA0 hσAcur hcur1 hsepB
  rw [hexprB] at hcursorB hframeB
  set σB := (emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval σA with hσBdef
  have hσBrow : σB (M + rowJ) = row := by
    rw [hframeB (M + rowJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσArow
  have hσBcnt : σB (M + cntJ) = cnt := by
    rw [hframeB (M + cntJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσAcnt
  have hσBtagAll : ∀ i, i < cnt → σB (row + 2 + 2 * i) = if tag i then 1 else 0 := by
    intro i hi
    rw [hframeB (row + 2 + 2 * i) (by omega) (by omega) (Or.inr (by omega))]
    exact hσAtagAll i hi
  have hσBdataAll : ∀ i, i < cnt → σB (row + 2 + 2 * i + 1) = d i := by
    intro i hi
    rw [hframeB (row + 2 + 2 * i + 1) (by omega) (by omega) (Or.inr (by omega))]
    exact hσAdataAll i hi
  have hexprC : (Expr.add (ctlCell rowJ) (Expr.const 2)).eval σB = row + 2 := by
    simp [Expr.eval, ctlCell_eval, hctlB, hσBrow]
  have hσCptr : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB
      (M + ptrJ) = row + 2 := by
    have h := ctlAssign_eval_same ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2)) σB
    rw [hctlB] at h
    rw [h]; exact hexprC
  refine ⟨(ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB,
    ?_, ?_, ?_, hσCptr, ?_, ?_, rfl, ?_⟩
  · rw [ctlAssign_eval_diff ptrJ _ σB (M + curJ) (by omega)]; exact hcursorB
  · rw [ctlAssign_eval_diff ptrJ _ σB 0 (by omega)]; exact hctlB
  · rw [ctlAssign_eval_diff ptrJ _ σB (M + cntJ) (by omega)]; exact hσBcnt
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σB (row + 2 + 2 * i) (by omega)]
    exact hσBtagAll i hi
  · intro i hi
    rw [ctlAssign_eval_diff ptrJ _ σB (row + 2 + 2 * i + 1) (by omega)]
    exact hσBdataAll i hi
  · intro r hrC hrT hrCnt hrP hr
    have e3 : (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))).eval σB r = σB r :=
      ctlAssign_eval_diff ptrJ _ σB r (by omega)
    have e4 : σB r = σA r := hframeB r hrC hrT hr
    have e5 : σA r = σ r := by
      rw [hσAdef, ctlAssign_eval_diff cntJ _ σ r (by omega)]
    rw [e3, e4, e5]

/-- `emitRowBody`'s own two-sided frame: cells other than the five control cells, outside the
    whole row's write window, survive. Chains `emitRowBody_state_upto_ptr_two_sided` with
    `emitOpsListProg_frame_two_sided`, then one more `ctlAssign` frame link for the final `rowJ`
    copy. -/
lemma emitRowBody_frame_two_sided (curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
    (tag : ℕ → Bool) (d : ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCell : σ (M + rowJ) = row) (hrowKey : σ row = rowKey) (hcntCell : σ (row + 1) = cnt)
    (htagAll : ∀ i, i < cnt → σ (row + 2 + 2 * i) = if tag i then 1 else 0)
    (hdataAll : ∀ i, i < cnt → σ (row + 2 + 2 * i + 1) = d i)
    (hloCur : M + curJ < row) (hloTmp : M + tmpJ < row)
    (hloCnt : M + cntJ < row) (hloPtr : M + ptrJ < row)
    (hsepFull : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ)
    (hsepTmpAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ)
    (hsepCntAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + cntJ)
    (hsepPtrAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ)
    (hsepRowAll : cur + (rowKey + 1) + (cnt + 1)
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ) :
    ∀ r, r ≠ M + curJ → r ≠ M + tmpJ → r ≠ M + cntJ → r ≠ M + ptrJ → r ≠ M + rowJ →
      (r < cur ∨ cur + (rowKey + 1) + (cnt + 1)
        + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ r) →
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ) r = σ r := by
  obtain ⟨σC, hσCcur, hσC0, hσCcnt, hσCptr, hσCtagAll, hσCdataAll, hEq, hframeC⟩ :=
    emitRowBody_state_upto_ptr_two_sided curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt tag d σ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur hcur1 hrowCell hrowKey hcntCell htagAll hdataAll hloCur hloTmp hloCnt hloPtr
      hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
  have hsepFullD : cur + rowKey + 1 + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + curJ := by
    omega
  have hsepTmpD : cur + rowKey + 1 + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + tmpJ := by
    omega
  have hsepPtrD : cur + rowKey + 1 + cnt + 1
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + ptrJ := by
    omega
  have hsepCntD : cur + rowKey + 1 + cnt + 1 ≤ M + cntJ := by omega
  have hframeD :=
    emitOpsListProg_frame_two_sided curJ tmpJ cntJ ptrJ M (cur + rowKey + 1) row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hσC0 hσCcur (by omega) hσCcnt hσCptr hσCtagAll hσCdataAll
      hsepCntD hsepFullD hsepTmpD hsepPtrD hloCur hloTmp hloPtr
  have hctlD : ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC) 0 = M := by
    obtain ⟨-, -, hctl0, -, -⟩ :=
      emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M (cur + rowKey + 1) row cnt tag d σC
        hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
        hσC0 hσCcur (by omega) hσCcnt hσCptr hσCtagAll hσCdataAll
        hsepCntD hsepFullD hsepTmpD hsepPtrD hloCur hloTmp hloPtr
    exact hctl0
  set σD := (emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC with hσDdef
  set σE := (ctlAssign rowJ (ctlCell ptrJ)).eval σD with hσEdef
  have htop : (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval σ = σE := by
    unfold emitRowBody
    rw [eval_seq, eval_seq, eval_seq, eval_seq, hEq, ← hσDdef, ← hσEdef]
  intro r hrC hrT hrCnt hrP hrRow hr
  rw [htop]
  have e1 : σE r = σD r := by
    rw [hσEdef, ctlAssign_eval_diff rowJ _ σD r (by omega)]
  rcases hr with hlt | hge
  · have e2 : σD r = σC r := hframeD r hrC hrT hrP (Or.inl (by omega))
    rw [e1, e2, hframeC r hrC hrT hrCnt hrP (Or.inl hlt)]
  · have e2 : σD r = σC r := hframeD r hrC hrT hrP (Or.inr (by omega))
    rw [e1, e2, hframeC r hrC hrT hrCnt hrP (Or.inr (by omega))]

/-! ## Variable-length row table: the whole table

`emitRowTableProg` stages `rowJ` at the table's base and loops `emitRowBody` once per row via
`emitListProg`, exactly as `emitOpsListProg` loops `emitRawOpBody` once per entry. The row
loop's per-iteration separation bound needs a global bound (`cur0` plus the whole table's encoded
length, against each control cell) peeled down to the current row's own bound, using the same
"split off one entry from a `flatMap`-of-`range`" argument as `emitOpsListProg_hbody` and
`emitNatTableProg_hbody`. `rowTableBitsLen_row_le` packages this fact for
`emitRowTableProg_hbody`. -/

/-- The `m`-th row's own encoded length fits between `rowTableBitsLen`'s value at `m` and at any
    later `rowCnt`, mirroring `flatMap_range_length_split` at the level of `rowTableBitsLen`. -/
lemma rowTableBitsLen_row_le (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ)
    (rowCnt m : ℕ) (hm : m < rowCnt) :
    rowTableBitsLen rowKeyG cntG tagG dG m
      + ((rowKeyG m + 1) + (cntG m + 1)
        + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length)
      ≤ rowTableBitsLen rowKeyG cntG tagG dG rowCnt := by
  unfold rowTableBitsLen
  have hsplit := flatMap_range_length_split
    (fun q => encodeNat (rowKeyG q) ++ (encodeNat (cntG q)
      ++ (List.range (cntG q)).flatMap (fun i => [tagG q i] ++ encodeNat (dG q i))))
    rowCnt m (le_of_lt hm)
  have hnm : rowCnt - m = (rowCnt - m - 1) + 1 := by omega
  have hrsplit : List.range' m (rowCnt - m) = m :: List.range' (m + 1) (rowCnt - m - 1) := by
    conv_lhs => rw [hnm]
    rw [List.range'_succ]
  have hlen_remaining :
      ((List.range' m (rowCnt - m)).flatMap
        (fun q => encodeNat (rowKeyG q) ++ (encodeNat (cntG q)
          ++ (List.range (cntG q)).flatMap (fun i => [tagG q i] ++ encodeNat (dG q i))))).length
      = ((rowKeyG m + 1) + (cntG m + 1)
        + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length)
        + ((List.range' (m + 1) (rowCnt - m - 1)).flatMap
          (fun q => encodeNat (rowKeyG q) ++ (encodeNat (cntG q)
            ++ (List.range (cntG q)).flatMap (fun i => [tagG q i] ++ encodeNat (dG q i))))).length
      := by
    rw [hrsplit, List.flatMap_cons, List.length_append, List.length_append, List.length_append,
      encodeNat_length, encodeNat_length]
    ring
  omega

/-- Invariant for `emitRowTableProg`'s row loop after `m` rows have been emitted from a table
    whose rows start at `tbl`: `rowJ` sits at the `m`-th row's physical address (the prefix sum of
    earlier rows' variable widths), the cursor sits exactly the combined encoded length of the
    first `m` rows past `cur0`, and every row's raw data (row key, payload count, and every
    payload entry's tag/data cells) is untouched — for *every* row, not just the ones not yet
    emitted, since `emitRowBody` never writes into the table region at all (mirroring
    `EmitNatTableInv`'s unconditional table-content clause). -/
def EmitRowTableInv (curJ rowJ M cur0 tbl rowCnt : ℕ) (rowKeyG cntG : ℕ → ℕ)
    (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (m : ℕ) (τ : Store) : Prop :=
  τ (M + rowJ) = tbl + rowTableWidth cntG m ∧
  τ (M + curJ) = cur0 + rowTableBitsLen rowKeyG cntG tagG dG m ∧
  (∀ q, q < rowCnt → τ (tbl + rowTableWidth cntG q) = rowKeyG q) ∧
  (∀ q, q < rowCnt → τ (tbl + rowTableWidth cntG q + 1) = cntG q) ∧
  (∀ q, q < rowCnt → ∀ i, i < cntG q →
    τ (tbl + rowTableWidth cntG q + 2 + 2 * i) = if tagG q i then 1 else 0) ∧
  (∀ q, q < rowCnt → ∀ i, i < cntG q →
    τ (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) = dG q i)

/-- The per-iteration correctness `emitListProg_eval_state`/`emit_loop_flatMap` need from
    `emitRowBody`, under `EmitRowTableInv`. The five separation bounds (`hsepFull` through
    `hsepRowAll`) all compare `cur0 + (the whole table's encoded length)` against a control-cell
    wall, per `emitOpsListProg_hbody`'s and `emitNatTableProg_hbody`'s own convention;
    `rowTableBitsLen_row_le` peels the current row's own bound off that global one, and
    `emitRowBody_frame_two_sided`'s two-sided frame (rather than a one-sided frame) is what lets
    every row's raw data — not just the current one — survive each iteration, exactly as
    `emitNatTableProg_hbody` needs `emitNatTableBody_eval_state`'s own two-sided frame for its
    table region. -/
lemma emitRowTableProg_hbody (curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepTmpAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + tmpJ)
    (hsepCntAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + cntJ)
    (hsepPtrAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + ptrJ)
    (hsepRowAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    ∀ m, m < rowCnt → ∀ (τ : Store) (cur' : ℕ),
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG m τ →
      τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) cur'
        (encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
          ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i)))) ∧
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) (M + curJ)
        = cur' + (rowKeyG m + 1) + (cntG m + 1)
          + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length ∧
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ →
        (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ r = τ r) ∧
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG (m + 1)
        ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) := by
  intro m hmrowCnt τ cur' hInv hM hcur'
  obtain ⟨hrowPos, hcurPos, hrowKeyAll, hcntAll, htagAll2, hdataAll2⟩ := hInv
  set row := tbl + rowTableWidth cntG m with hrowdef
  have hrowCell : τ (M + rowJ) = row := hrowPos
  have hrowKey : τ row = rowKeyG m := hrowKeyAll m hmrowCnt
  have hcntCell : τ (row + 1) = cntG m := hcntAll m hmrowCnt
  have htagAllRow : ∀ i, i < cntG m → τ (row + 2 + 2 * i) = if tagG m i then 1 else 0 :=
    fun i hi => htagAll2 m hmrowCnt i hi
  have hdataAllRow : ∀ i, i < cntG m → τ (row + 2 + 2 * i + 1) = dG m i :=
    fun i hi => hdataAll2 m hmrowCnt i hi
  have hloCurRow : M + curJ < row := by omega
  have hloTmpRow : M + tmpJ < row := by omega
  have hloCntRow : M + cntJ < row := by omega
  have hloPtrRow : M + ptrJ < row := by omega
  have hcur'eq : cur' = cur0 + rowTableBitsLen rowKeyG cntG tagG dG m := hcur'.symm.trans hcurPos
  have hkey := rowTableBitsLen_row_le rowKeyG cntG tagG dG rowCnt m hmrowCnt
  have hsepFullRow : cur' + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + curJ := by omega
  have hsepTmpRow : cur' + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + tmpJ := by omega
  have hsepCntRow : cur' + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + cntJ := by omega
  have hsepPtrRow : cur' + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + ptrJ := by omega
  have hsepRowRow : cur' + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + rowJ := by omega
  obtain ⟨hbits, hcursor, hctl0, hrowFinal⟩ :=
    emitRowBody_eval_state curJ tmpJ cntJ ptrJ rowJ M cur' row (rowKeyG m) (cntG m) (tagG m) (dG m) τ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur' (by omega) hrowCell hrowKey hcntCell htagAllRow hdataAllRow
      hloCurRow hloTmpRow hloCntRow hloPtrRow
      hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
  have hframe2 :=
    emitRowBody_frame_two_sided curJ tmpJ cntJ ptrJ rowJ M cur' row
      (rowKeyG m) (cntG m) (tagG m) (dG m) τ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur' (by omega) hrowCell hrowKey hcntCell htagAllRow hdataAllRow
      hloCurRow hloTmpRow hloCntRow hloPtrRow
      hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
  refine ⟨hbits, hcursor, hctl0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr1 hr2
    exact hframe2 r hr2 (by omega) (by omega) (by omega) (by omega) (Or.inl hr1)
  · rw [hrowFinal, hrowdef]
    have hsucc := rowTableWidth_succ cntG m
    omega
  · rw [hcursor, hcur'eq]
    have hsucc := rowTableBitsLen_succ rowKeyG cntG tagG dG m
    omega
  · intro q hq
    exact (hframe2 (tbl + rowTableWidth cntG q) (by omega) (by omega) (by omega) (by omega)
      (by omega) (Or.inr (by omega))).trans (hrowKeyAll q hq)
  · intro q hq
    exact (hframe2 (tbl + rowTableWidth cntG q + 1) (by omega) (by omega) (by omega) (by omega)
      (by omega) (Or.inr (by omega))).trans (hcntAll q hq)
  · intro q hq i hi
    exact (hframe2 (tbl + rowTableWidth cntG q + 2 + 2 * i) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega))).trans (htagAll2 q hq i hi)
  · intro q hq i hi
    exact (hframe2 (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega))).trans (hdataAll2 q hq i hi)

/-! ## Variable-length row table: the whole table -/

/-- Emit a whole table of variable-length rows in `encodeList` shape: stage `rowJ` at the table's
    base, then loop `emitRowBody` once per row via `emitListProg`, exactly as `emitOpsListProg`
    loops `emitRawOpBody` once per entry. The outer row counter (`rowCntJ`) and the inner entry
    counter (`cntJ`) must be distinct cells, since `emitListProg` uses its own third argument as the
    loop bound while `emitRowBody` independently stages `cntJ` from each row's count cell. -/
def emitRowTableProg (curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ : ℕ) : Program :=
  .seq (ctlAssign rowJ (ctlCell tblJ))
    (emitListProg curJ tmpJ rowCntJ (emitRowBody curJ tmpJ cntJ ptrJ rowJ))

/-- Initial row-loop invariant for `emitRowTableProg`: after staging `rowJ := tbl` (the store `σ0`,
    which differs from `σ` only at `M + rowJ`) and emitting the row count, the invariant holds at
    row `0`. Isolates the "everything else is unchanged" bookkeeping from the loop itself. -/
lemma emitRowTableProg_eval_state_inv0 (curJ tmpJ rowJ rowCntJ M cur tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (σ σ0 : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurRow : curJ ≠ rowJ) (hTmpRow : tmpJ ≠ rowJ)
    (hRowRowCnt : rowJ ≠ rowCntJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCnt : σ (M + rowCntJ) = rowCnt)
    (hrowKeyAll : ∀ q, q < rowCnt → σ (tbl + rowTableWidth cntG q) = rowKeyG q)
    (hcntAll : ∀ q, q < rowCnt → σ (tbl + rowTableWidth cntG q + 1) = cntG q)
    (htagAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ (tbl + rowTableWidth cntG q + 2 + 2 * i) = if tagG q i then 1 else 0)
    (hdataAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) = dG q i)
    (hsepFull : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepRowAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloRow : M + rowJ < tbl)
    (hσ0frame : ∀ r, r ≠ M + rowJ → σ0 r = σ r) (hσ0row : σ0 (M + rowJ) = tbl) :
    σ0 0 = M ∧ σ0 (M + curJ) = cur ∧ σ0 (M + rowCntJ) = rowCnt ∧
    EmitRowTableInv curJ rowJ M (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG 0
      ((emitNatProg curJ tmpJ (ctlCell rowCntJ)).eval σ0) := by
  have hσ00 : σ0 0 = M := by rw [hσ0frame 0 (by omega)]; exact hM
  have hσ0cur : σ0 (M + curJ) = cur := by rw [hσ0frame _ (by omega)]; exact hcur
  have hσ0rowCnt : σ0 (M + rowCntJ) = rowCnt := by rw [hσ0frame _ (by omega)]; exact hrowCnt
  have hrowCntEval : (ctlCell rowCntJ).eval σ0 = rowCnt := by
    rw [ctlCell_eval, hσ00, hσ0rowCnt]
  have hsep1 : cur + (ctlCell rowCntJ).eval σ0 < M + curJ := by rw [hrowCntEval]; omega
  obtain ⟨-, hcursor1, hframe1, -⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell rowCntJ) σ0 hc1 hc2 hCurTmp hσ00 hσ0cur
      hcur1 hsep1
  rw [hrowCntEval] at hcursor1 hframe1
  refine ⟨hσ00, hσ0cur, hσ0rowCnt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe1 (M + rowJ) (by omega) (by omega) (Or.inr (by omega)), hσ0row]
    simp [rowTableWidth]
  · rw [hcursor1]; simp [rowTableBitsLen]
  · intro q hq
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact hrowKeyAll q hq
  · intro q hq
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact hcntAll q hq
  · intro q hq i hi
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact htagAll q hq i hi
  · intro q hq i hi
    rw [hframe1 _ (by omega) (by omega) (Or.inr (by omega)), hσ0frame _ (by omega)]
    exact hdataAll q hq i hi

/-- `emitRowTableProg_hbody` restated in the `encodeNat`-length form that `emitListProg_eval_state`
    expects for its per-iteration obligation (the cursor advances by the length of the whole row
    chunk rather than by its componentwise width). -/
lemma emitRowTableProg_eval_state_hbody_len (curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ) (hPtrRow : ptrJ ≠ rowJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepTmpAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + tmpJ)
    (hsepCntAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + cntJ)
    (hsepPtrAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + ptrJ)
    (hsepRowAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    ∀ m, m < rowCnt → ∀ (τ : Store) (cur' : ℕ),
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG m τ →
      τ 0 = M → τ (M + curJ) = cur' →
      BitsAt ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) cur'
        (encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
          ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i)))) ∧
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) (M + curJ)
        = cur' + (encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
          ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i)))).length ∧
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) 0 = M ∧
      (∀ r, r < cur' → r ≠ M + curJ →
        (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ r = τ r) ∧
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG (m + 1)
        ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) := by
  intro m hm τ cur' hInv hτ0 hτcur
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    emitRowTableProg_hbody curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hcur01 hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
      hloCur hloTmp hloCnt hloPtr hloRow m hm τ cur' hInv hτ0 hτcur
  refine ⟨h1, ?_, h3, h4, h5⟩
  rw [h2, List.length_append, encodeNat_length, List.length_append, encodeNat_length]
  omega

/-- Bundled correctness of `emitRowTableProg`: the store after running it holds
    the length-prefixed concatenation of the first `rowCnt` variable-length row encodings at the
    entry cursor, the cursor has advanced past the whole table, and cell `0` still holds `M`.
    Chains staging `rowJ := tbl` with `emitListProg_eval_state`, instantiated at
    `emitRowTableProg_hbody` for the per-row obligation — mirroring
    `emitNatTableProg_eval_state`'s and `emitOpsListProg_eval_state`'s own top-level chaining. -/
lemma emitRowTableProg_eval_state (curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ) (hCurRow : curJ ≠ rowJ)
    (hCurRowCnt : curJ ≠ rowCntJ)
    (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ) (hTmpRow : tmpJ ≠ rowJ)
    (hTmpRowCnt : tmpJ ≠ rowCntJ)
    (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ)
    (hRowRowCnt : rowJ ≠ rowCntJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hrowCnt : σ (M + rowCntJ) = rowCnt) (htbl : σ (M + tblJ) = tbl)
    (hrowKeyAll : ∀ q, q < rowCnt → σ (tbl + rowTableWidth cntG q) = rowKeyG q)
    (hcntAll : ∀ q, q < rowCnt → σ (tbl + rowTableWidth cntG q + 1) = cntG q)
    (htagAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ (tbl + rowTableWidth cntG q + 2 + 2 * i) = if tagG q i then 1 else 0)
    (hdataAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) = dG q i)
    (hsepCnt : cur + rowCnt + 1 ≤ M + rowCntJ)
    (hsepFull : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepTmpAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + tmpJ)
    (hsepCntAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + cntJ)
    (hsepPtrAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + ptrJ)
    (hsepRowAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl) :
    BitsAt ((emitRowTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) cur
      (encodeNat rowCnt ++ (List.range rowCnt).flatMap (fun m => encodeNat (rowKeyG m)
        ++ (encodeNat (cntG m)
          ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))))) ∧
    ((emitRowTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) (M + curJ)
      = cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ∧
    ((emitRowTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ) 0 = M := by
  have hσ0frame : ∀ r, r ≠ M + rowJ → (ctlAssign rowJ (ctlCell tblJ)).eval σ r = σ r :=
    fun r hr => ctlAssign_eval_diff rowJ _ σ r (by rw [hM]; exact hr)
  have hσ0row : (ctlAssign rowJ (ctlCell tblJ)).eval σ (M + rowJ) = tbl := by
    have h := ctlAssign_eval_same rowJ (ctlCell tblJ) σ
    rw [hM, ctlCell_eval, hM, htbl] at h
    exact h
  obtain ⟨hσ00, hσ0cur, hσ0rowCnt, hInv0⟩ :=
    emitRowTableProg_eval_state_inv0 curJ tmpJ rowJ rowCntJ M cur tbl rowCnt rowKeyG cntG tagG dG
      σ _ hc1 hc2 hCurTmp hCurRow hTmpRow hRowRowCnt hM hcur hcur1 hrowCnt
      hrowKeyAll hcntAll htagAll hdataAll hsepFull hsepRowAll hloCur hloTmp hloRow hσ0frame hσ0row
  have hbody' := emitRowTableProg_eval_state_hbody_len curJ tmpJ cntJ ptrJ rowJ M
    (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
    (by omega) hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow
  have hlenEq : rowTableBitsLen rowKeyG cntG tagG dG rowCnt
      = ((List.range rowCnt).flatMap (fun m => encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
        ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))))).length :=
    rfl
  have hsepFull' : cur + rowCnt + 1
      + ((List.range rowCnt).flatMap (fun m => encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
        ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))))).length
      ≤ M + curJ := by rw [← hlenEq]; exact hsepFull
  have hstate := emitListProg_eval_state curJ tmpJ rowCntJ M cur rowCnt
    (emitRowBody curJ tmpJ cntJ ptrJ rowJ)
    (fun m => encodeNat (rowKeyG m) ++ (encodeNat (cntG m)
      ++ (List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))))
    (EmitRowTableInv curJ rowJ M (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG)
    ((ctlAssign rowJ (ctlCell tblJ)).eval σ)
    hc1 hc2 hCurTmp hCurRowCnt.symm hTmpRowCnt.symm
    hσ00 hσ0cur hcur1 hσ0rowCnt hsepCnt hsepFull' hbody' hInv0
  have htop : (emitRowTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ).eval σ
      = (emitListProg curJ tmpJ rowCntJ (emitRowBody curJ tmpJ cntJ ptrJ rowJ)).eval
        ((ctlAssign rowJ (ctlCell tblJ)).eval σ) := by
    unfold emitRowTableProg
    rw [eval_seq]
  refine ⟨?_, ?_, ?_⟩
  · rw [htop]; exact hstate.1
  · rw [htop, hlenEq]; exact hstate.2.1
  · rw [htop]; exact hstate.2.2.1

end NPComplete.RAMToTM

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowWrite

/-!
Nested loops generate the five clause families, and a proof specialized to every
nest would repeat the same row-writing argument. This module gives a shared
contract for fixed-width leaves and proves that loop iterations append their rows
at successive table offsets.

The body contract is stated for arbitrary stores and uses pins for enclosing
counters, so it composes independently of a particular loop run. Frame conditions
preserve rows already written. Run-time-width leaves are treated separately.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Rows live below the table's total width

`RowsWritten` constrains cells at explicit offsets from the base; a caller
composing two write phases needs to know those offsets stay inside the region
the first phase claims, so that anything written above it is harmless. -/

lemma rowTableWidth_le_succ (f : ℕ → ℕ) (m : ℕ) :
    rowTableWidth f m ≤ rowTableWidth f (m + 1) := by
  rw [rowTableWidth_succ]; omega

lemma rowTableWidth_mono (f : ℕ → ℕ) : Monotone (rowTableWidth f) :=
  monotone_nat_of_le_succ (rowTableWidth_le_succ f)

/-- A row's count cell sits strictly inside the table's total width. -/
lemma rowsWritten_cnt_addr_lt (cs : List Clause) (q : ℕ) (hq : q < cs.length) :
    rowTableWidth (rowW cs) q + 1 < rowTableWidth (rowW cs) cs.length := by
  have h1 := rowTableWidth_mono (rowW cs) (show q + 1 ≤ cs.length by omega)
  rw [rowTableWidth_succ] at h1
  omega

/-- A row's literal cells sit strictly inside the table's total width. -/
lemma rowsWritten_addr_lt (cs : List Clause) (q : ℕ) (hq : q < cs.length)
    (i : ℕ) (hi : i < rowW cs q) :
    rowTableWidth (rowW cs) q + 2 + 2 * i + 1 < rowTableWidth (rowW cs) cs.length := by
  have h1 := rowTableWidth_mono (rowW cs) (show q + 1 ≤ cs.length by omega)
  rw [rowTableWidth_succ] at h1
  omega

/-- Rewriting cells outside a clause list's own region leaves its rows intact —
the frame condition that lets one write phase run after another. -/
lemma rowsWritten_of_agree (σ σ' : Store) (base : ℕ) (cs : List Clause)
    (h : RowsWritten σ base cs)
    (hagree : ∀ r, base ≤ r → r < base + rowTableWidth (rowW cs) cs.length → σ' r = σ r) :
    RowsWritten σ' base cs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq
  · rw [hagree _ (by omega) (by have := rowsWritten_cnt_addr_lt cs q hq; omega)]
    exact h1 q hq
  · intro i hi
    rw [hagree _ (by omega) (by have := rowsWritten_addr_lt cs q hq i hi; omega)]
    exact h2 q hq i hi
  · intro i hi
    rw [hagree _ (by omega) (by have := rowsWritten_addr_lt cs q hq i hi; omega)]
    exact h3 q hq i hi

/-- The pointer after two lists is the pointer after the first plus the second's
own width, so a loop can add one iteration's width at a time. -/
lemma rowTableWidth_append_total (cs ds : List Clause) :
    rowTableWidth (rowW (cs ++ ds)) (cs ++ ds).length
      = rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) ds.length := by
  rw [List.length_append]
  exact rowTableWidth_app_shift cs ds ds.length

/-! ## The control block

Fixing the control cells to one contiguous block turns every frame condition
into an arithmetic side condition: a cell is either inside the block (where
bodies write freely) or outside it (where bodies preserve). -/

/-- A cell outside the control block `[M+1, M+Jmax]`, which every body preserves
below its write pointer. -/
def CtlFree (M Jmax r : ℕ) : Prop := r < M + 1 ∨ M + Jmax < r

/-- The values an inner loop may read from the levels enclosing it: control cell
`p.1` holds `p.2`.  Pinning them as data rather than as an opaque predicate is
what makes preservation across a body mechanical. -/
def PinsHold (M : ℕ) (pins : List (ℕ × ℕ)) (τ : Store) : Prop :=
  ∀ p ∈ pins, τ (M + p.1) = p.2

lemma pinsHold_tail (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ)) (τ : Store)
    (h : PinsHold M (p :: pins) τ) : PinsHold M pins τ :=
  fun q hq => h q (List.mem_cons_of_mem p hq)

lemma pinsHold_head (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ)) (τ : Store)
    (h : PinsHold M (p :: pins) τ) : τ (M + p.1) = p.2 :=
  h p List.mem_cons_self

lemma pinsHold_cons (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ)) (τ : Store)
    (h1 : τ (M + p.1) = p.2) (h2 : PinsHold M pins τ) : PinsHold M (p :: pins) τ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact h1
  · exact h2 q hq'

/-! ## The loop

`ClauseLoopBody` names what one iteration must do; `rowsWritten_loop` is its
`forN` closure. The counter is bumped by the body itself, so the loop's program
is a bare `forN` with no separate increment. -/

/-- One iteration writes `g i` at the write pointer, advances the pointer by that
    list's width, bumps its counter, and preserves everything outside the control
    block below the pointer — all at an arbitrary store satisfying the caller's
    `Frozen` predicate, which the iteration must itself preserve. -/
def ClauseLoopBody (body : Program) (M Jmax wpJ iJ : ℕ) (Frozen : Store → Prop)
    (g : ℕ → List Clause) : Prop :=
  ∀ (τ : Store) (i wp : ℕ), Frozen τ → τ 0 = M → τ (M + iJ) = i → τ (M + wpJ) = wp →
    M + Jmax < wp →
    Frozen (body.eval τ) ∧
    (body.eval τ) 0 = M ∧
    (body.eval τ) (M + iJ) = i + 1 ∧
    (body.eval τ) (M + wpJ) = wp + rowTableWidth (rowW (g i)) (g i).length ∧
    RowsWritten (body.eval τ) wp (g i) ∧
    (∀ r, r < wp → CtlFree M Jmax r → (body.eval τ) r = τ r)

/-- Iterating the body `k` times writes the clause lists of `k` consecutive
    indices, back to back, starting at the entry pointer.  Generalizing over the
    starting index `i0` is what lets the induction peel a single iteration off
    the front, matching `loopEval`'s own recursion. -/
lemma rowsWritten_loop (body : Program) (M Jmax wpJ iJ : ℕ) (Frozen : Store → Prop)
    (g : ℕ → List Clause) (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g) :
    ∀ (k i0 : ℕ) (τ : Store) (wp0 : ℕ), Frozen τ → τ 0 = M → τ (M + iJ) = i0 →
      τ (M + wpJ) = wp0 → M + Jmax < wp0 →
      Frozen (loopEval body k τ) ∧
      (loopEval body k τ) 0 = M ∧
      (loopEval body k τ) (M + iJ) = i0 + k ∧
      (loopEval body k τ) (M + wpJ)
        = wp0 + rowTableWidth (rowW ((List.range' i0 k).flatMap g))
            ((List.range' i0 k).flatMap g).length ∧
      RowsWritten (loopEval body k τ) wp0 ((List.range' i0 k).flatMap g) ∧
      (∀ r, r < wp0 → CtlFree M Jmax r → (loopEval body k τ) r = τ r) := by
  intro k
  induction k with
  | zero =>
      intro i0 τ wp0 hF h0 hi hw _
      have hnil : (List.range' i0 0).flatMap g = [] := by
        rw [List.range'_zero, List.flatMap_nil]
      rw [loopEval_zero, hnil, List.length_nil, rowTableWidth_zero, Nat.add_zero, Nat.add_zero]
      exact ⟨hF, h0, hi, hw, rowsWritten_nil τ wp0, fun r _ _ => rfl⟩
  | succ k ih =>
      intro i0 τ wp0 hF h0 hi hw hsep
      obtain ⟨bF, b0, bi, bw, brows, bframe⟩ := hbody τ i0 wp0 hF h0 hi hw hsep
      set d := rowTableWidth (rowW (g i0)) (g i0).length with hd
      obtain ⟨rF, r0, ri, rw', rrows, rframe⟩ :=
        ih (i0 + 1) (body.eval τ) (wp0 + d) bF b0 bi bw (by omega)
      have hrange : List.range' i0 (k + 1) = i0 :: List.range' (i0 + 1) k := by
        simp [List.range'_succ]
      have hstep : loopEval body (k + 1) τ = loopEval body k (body.eval τ) := loopEval_succ _ _ _
      have hkeep : RowsWritten (loopEval body k (body.eval τ)) wp0 (g i0) := by
        refine rowsWritten_of_agree _ _ wp0 (g i0) brows (fun r h1 h2 => ?_)
        exact rframe r (by omega) (Or.inr (by omega))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep]; exact rF
      · rw [hstep]; exact r0
      · rw [hstep, ri]; omega
      · rw [hstep, rw', hrange, List.flatMap_cons,
          rowTableWidth_append_total (g i0) ((List.range' (i0 + 1) k).flatMap g), ← hd]
        omega
      · rw [hstep, hrange, List.flatMap_cons]
        exact rowsWritten_append _ wp0 (g i0) _ hkeep rrows
      · intro r hr1 hr2
        rw [hstep, rframe r (by omega) hr2]
        exact bframe r hr1 hr2

/-- The `forN` form: the bound is an expression evaluated at entry and the
    counter cell must already hold zero, so the clause lists written are those of
    `List.range n` — the shape every family's `flatMap` actually has. -/
lemma rowsWritten_forN (body : Program) (M Jmax wpJ iJ : ℕ) (Frozen : Store → Prop)
    (g : ℕ → List Clause) (cntE : Expr) (n wp0 : ℕ) (τ : Store)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g)
    (hF : Frozen τ) (h0 : τ 0 = M) (hi : τ (M + iJ) = 0) (hw : τ (M + wpJ) = wp0)
    (hcnt : cntE.eval τ = n) (hsep : M + Jmax < wp0) :
    Frozen ((Program.forN cntE body).eval τ) ∧
    ((Program.forN cntE body).eval τ) 0 = M ∧
    ((Program.forN cntE body).eval τ) (M + iJ) = n ∧
    ((Program.forN cntE body).eval τ) (M + wpJ)
      = wp0 + rowTableWidth (rowW ((List.range n).flatMap g))
          ((List.range n).flatMap g).length ∧
    RowsWritten ((Program.forN cntE body).eval τ) wp0 ((List.range n).flatMap g) ∧
    (∀ r, r < wp0 → CtlFree M Jmax r → ((Program.forN cntE body).eval τ) r = τ r) := by
  have heval : (Program.forN cntE body).eval τ = loopEval body n τ := by
    rw [eval_forN, hcnt]
  have hrng : List.range n = List.range' 0 n := List.range_eq_range'
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ :=
    rowsWritten_loop body M Jmax wpJ iJ Frozen g hbody n 0 τ wp0 hF h0 hi hw hsep
  rw [heval, hrng]
  exact ⟨f1, f2, by omega, f4, f5, f6⟩

/-! ## The leaf

The innermost level writes one clause per iteration, of a width fixed at compile
time: the literal *expressions* are fixed, and only the values they read from
control cells vary with the counters.  `hdep` is what says so — every literal
expression reads control cells other than the write pointer, and nothing else. -/

/-- The innermost body: write one clause, then bump the counter. -/
def leafProg (wpJ iJ : ℕ) (lits : List (Expr × Expr)) : Program :=
  .seq (writeClauseProg wpJ lits) (ctlAssign iJ (.add (ctlCell iJ) (.const 1)))

lemma clauseLoopBody_leaf (M Jmax wpJ iJ : ℕ) (lits : List (Expr × Expr))
    (pins : List (ℕ × ℕ)) (c : ℕ → Clause)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hdep : ∀ p ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ)
    (hlen : ∀ i, (c i).lits.length = lits.length)
    (hlit : ∀ (τ : Store) (i k : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      k < lits.length →
      (lits.getD k defLit).1.eval τ = (if litTag ((c i).lits.getD k default) then 1 else 0) ∧
      (lits.getD k defLit).2.eval τ = litVar ((c i).lits.getD k default)) :
    ClauseLoopBody (leafProg wpJ iJ lits) M Jmax wpJ iJ (PinsHold M pins)
      (fun i => [c i]) := by
  intro τ i wp hF h0 hi hw hsep
  have hinv : ∀ p ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ := by
    intro p hp σ σ' hσ hσ' hagree
    exact hdep p hp σ σ' hσ hσ' (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ lits M wp τ hwpJ h0 hw (by omega) hinv
  set σ2 := (writeClauseProg wpJ lits).eval τ with hσ2def
  have hσ2i : σ2 (M + iJ) = i := by rw [w5 (M + iJ) (by omega) (by omega), hi]
  set σ3 := (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1))).eval σ2 with hσ3def
  have hσ3eq : σ3 = writeReg σ2 (M + iJ) (i + 1) := by
    rw [hσ3def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, w4]
    congr 1
    simp [Expr.eval, ctlCell_eval, w4, hσ2i]
  have hgoal : (leafProg wpJ iJ lits).eval τ = σ3 := by
    rw [hσ3def, hσ2def]; unfold leafProg; rw [eval_seq]
  rw [hgoal]
  have hσ30 : σ3 0 = M := by
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) 0 (by omega), w4]
  have hwidth : rowTableWidth (rowW [c i]) [c i].length = 2 + 2 * lits.length := by
    rw [show [c i].length = 1 from rfl, rowTableWidth_singleton, hlen]
  refine ⟨?_, hσ30, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨_, _, hpne, hpne2⟩ := hpin p hp
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (M + p.1) (by omega),
      w5 (M + p.1) (by omega) (by omega)]
    exact hF p hp
  · rw [hσ3eq, writeReg_same]
  · rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (M + wpJ) (by omega), w3, hwidth]
    omega
  · refine rowsWritten_singleton σ3 wp (c i) ?_ ?_ ?_
    · rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 1) (by omega), w1, hlen]
    · intro k hk
      rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 2 + 2 * k) (by omega)]
      rw [(w2 k (by rw [hlen] at hk; exact hk)).1]
      exact (hlit τ i k hF h0 hi (by rw [hlen] at hk; exact hk)).1
    · intro k hk
      rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 2 + 2 * k + 1) (by omega)]
      rw [(w2 k (by rw [hlen] at hk; exact hk)).2]
      exact (hlit τ i k hF h0 hi (by rw [hlen] at hk; exact hk)).2
  · intro r hr1 hr2
    have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) r hrne,
      w5 r hr1 (by rcases hr2 with h | h <;> omega)]

end NPComplete.CookLevin

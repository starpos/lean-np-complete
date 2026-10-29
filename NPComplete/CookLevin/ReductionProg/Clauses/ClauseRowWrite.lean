module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowsWritten

/-!
`RowsWritten` fixes what a finished clause table must look like; this file gives
the primitive RAM routines a producer actually runs to reach that state.
Both routines share the same shape as the generic emit toolkit's `emitBitProg`/
`ctlAssign`-based primitives: a run-time write pointer held in a control cell is
read, written through, and advanced, entirely via `assignInd`/`ctlAssign` so no
compile-time address is ever baked into the program.

`writeLitProg` writes one literal (tag bit, then variable number) at the current
write pointer and advances it by two cells — the atomic unit every clause row is
built from. `writeClauseProg` writes a whole clause of a *compile-time* known
width (a `List (Expr × Expr)` of literal expressions) by writing the count cell
once and then folding `writeLitProg` over the list.
`writeAtLeastOneProg` handles a single clause whose width is given at run time
by `cntE`. It writes one literal per loop iteration, with the variable
expression parameterized by that literal's counter. This is the form used for
"at-least-one-of-these-`n`-cells" clauses in the tableau reduction.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Writing one literal

`writeLitProg` is `emitBitProg` specialized to a two-cell payload: it writes the
tag bit at the write pointer, the variable number one cell past it, then advances
the pointer by two. As with `Program.eval` on `.seq`, the second `assignInd`
statement evaluates `varE` against the store *after* the tag write, and the
third statement re-reads the write-pointer control cell against the store after
*that*. `writeLitProg_eval_state` unfolds all three stages explicitly rather than
assuming `tagE`/`varE` see the original store — callers whose expressions only
read control cells and constants (a sufficient condition) discharge the
expression-stability hypothesis by `rfl`/`omega`-level reasoning at the call site. -/

/-- Write literal `(tagE, varE)` at the write pointer held in control cell `wpJ`,
    then advance the pointer by two cells (tag cell, then variable cell). -/
def writeLitProg (wpJ : ℕ) (tagE varE : Expr) : Program :=
  .seq (.seq
    (.assignInd (ctlCell wpJ) tagE)
    (.assignInd (.add (ctlCell wpJ) (.const 1)) varE))
    (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))

/-- Unfolds `writeLitProg`'s net effect: the tag cell gets `tagE.eval σ` (read
    against the *original* store, since it is the first write), the variable
    cell gets `varE.eval` of the *tag-updated* store (per `.seq`'s left-to-right
    evaluation) — packaged as `hvarE` so a caller whose `varE` only reads
    control cells (unaffected by the tag write into `wp`) discharges it
    trivially — and the pointer cell advances to `wp + 2`. -/
lemma writeLitProg_eval_state (wpJ : ℕ) (tagE varE : Expr) (M wp : ℕ) (σ : Store)
    (hwpJ : 1 ≤ wpJ) (hM : σ 0 = M) (hwp : σ (M + wpJ) = wp)
    (hsep : M + wpJ < wp) (hwp0 : wp ≠ 0)
    (hvarE : varE.eval ((Program.assignInd (ctlCell wpJ) tagE).eval σ) = varE.eval σ) :
    ((writeLitProg wpJ tagE varE).eval σ) wp = tagE.eval σ ∧
    ((writeLitProg wpJ tagE varE).eval σ) (wp + 1) = varE.eval σ ∧
    ((writeLitProg wpJ tagE varE).eval σ) (M + wpJ) = wp + 2 ∧
    ((writeLitProg wpJ tagE varE).eval σ) 0 = M ∧
    (∀ r, r ≠ wp → r ≠ wp + 1 → r ≠ M + wpJ →
      ((writeLitProg wpJ tagE varE).eval σ) r = σ r) := by
  unfold writeLitProg
  have haddr1 : (ctlCell wpJ).eval σ = wp := by rw [ctlCell_eval, hM, hwp]
  set σ1 := (Program.assignInd (ctlCell wpJ) tagE).eval σ with hσ1def
  have hσ1eq : σ1 = writeReg σ wp (tagE.eval σ) := by
    rw [hσ1def, eval_assignInd, haddr1]
  have hσ1wp : σ1 wp = tagE.eval σ := by rw [hσ1eq, writeReg_same]
  have hσ10 : σ1 0 = M := by
    rw [hσ1eq, writeReg_diff σ wp (tagE.eval σ) 0 (Ne.symm hwp0), hM]
  have hσ1ctl : σ1 (M + wpJ) = wp := by
    rw [hσ1eq, writeReg_diff σ wp (tagE.eval σ) (M + wpJ) (by omega), hwp]
  have haddr2 : (Expr.add (ctlCell wpJ) (Expr.const 1)).eval σ1 = wp + 1 := by
    simp [Expr.eval, ctlCell_eval, hσ10, hσ1ctl]
  set σ2 := (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) varE).eval σ1 with hσ2def
  have hσ2eq : σ2 = writeReg σ1 (wp + 1) (varE.eval σ1) := by
    rw [hσ2def, eval_assignInd, haddr2]
  have hσ2wp1 : σ2 (wp + 1) = varE.eval σ1 := by rw [hσ2eq, writeReg_same]
  have hσ2wp : σ2 wp = tagE.eval σ := by
    rw [hσ2eq, writeReg_diff σ1 (wp + 1) (varE.eval σ1) wp (by omega), hσ1wp]
  have hσ20 : σ2 0 = M := by
    rw [hσ2eq, writeReg_diff σ1 (wp + 1) (varE.eval σ1) 0 (by omega), hσ10]
  have hσ2ctl : σ2 (M + wpJ) = wp := by
    rw [hσ2eq, writeReg_diff σ1 (wp + 1) (varE.eval σ1) (M + wpJ) (by omega), hσ1ctl]
  have haddr3 : (ctlAddr wpJ).eval σ2 = M + wpJ := by rw [ctlAddr_eval, hσ20]
  have hval3 : (Expr.add (ctlCell wpJ) (Expr.const 2)).eval σ2 = wp + 2 := by
    simp [Expr.eval, ctlCell_eval, hσ20, hσ2ctl]
  have hfinal : (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σ2
      = writeReg σ2 (M + wpJ) (wp + 2) := by
    unfold ctlAssign
    rw [eval_assignInd, haddr3, hval3]
  set τ := (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σ2 with hτdef
  have hτeq : τ = writeReg σ2 (M + wpJ) (wp + 2) := hfinal
  have hgoal : (Program.seq (Program.seq (Program.assignInd (ctlCell wpJ) tagE)
      (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) varE))
      (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2)))).eval σ = τ := by
    rw [eval_seq, eval_seq, ← hσ1def, ← hσ2def, ← hτdef]
  rw [hgoal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hτeq, writeReg_diff σ2 (M + wpJ) (wp + 2) wp (by omega), hσ2wp]
  · rw [hτeq, writeReg_diff σ2 (M + wpJ) (wp + 2) (wp + 1) (by omega), hσ2wp1, hvarE]
  · rw [hτeq, writeReg_same]
  · rw [hτeq, writeReg_diff σ2 (M + wpJ) (wp + 2) 0 (by omega), hσ20]
  · intro r hr1 hr2 hr3
    rw [hτeq, writeReg_diff σ2 (M + wpJ) (wp + 2) r (by omega)]
    rw [hσ2eq, writeReg_diff σ1 (wp + 1) (varE.eval σ1) r (by omega)]
    rw [hσ1eq, writeReg_diff σ wp (tagE.eval σ) r (by omega)]

/-! ## Writing a clause of fixed (compile-time) width

`writeClauseProg` writes the row-key slot's successor (the payload count cell)
and then folds `writeLitProg` over a compile-time list of literal expressions —
exactly the shape `RowsWritten` requires for one clause, up to the row-key cell
itself, which the emitter never reads and this routine leaves untouched.
`writeLitsProg` is the fold; its correctness lemma is stated with an explicit
bound `bound` so a caller can compose it with an entry pointer separated from
control cells by any amount, matching how `writeClauseProg_eval_state` instantiates it
at `bound = wp + 2` (past the count cell). -/

/-- Default placeholder literal expression pair, used only to give `List.getD`
    a total default value — never actually read, since every access below is
    guarded by an index bound. -/
def defLit : Expr × Expr := (Expr.const 0, Expr.const 0)

/-- Fold `writeLitProg` over a literal list, writing each literal at the write
    pointer in turn. -/
def writeLitsProg (wpJ : ℕ) : List (Expr × Expr) → Program
  | [] => .skip
  | (tagE, varE) :: rest => .seq (writeLitProg wpJ tagE varE) (writeLitsProg wpJ rest)

/-- Unfolds `writeLitsProg`'s net effect: literal `i`'s tag/variable cells sit at
    `wp0 + 2*i`/`wp0 + 2*i + 1`, evaluated against the *original* store `σ` (not
    an intermediate one) — this needs `hinv`, the same "does not read the cells
    being written" condition as `writeLitProg_eval_state`, but phrased over the
    whole list at once: every literal expression, evaluated at any store that
    agrees with `σ` below the caller-supplied `bound` and off the write-pointer
    control cell, agrees with its value at `σ`. The pointer advances by two
    cells per literal, and cells below the entry pointer are untouched. -/
lemma writeLitsProg_eval_state (wpJ : ℕ) (lits : List (Expr × Expr)) (M bound : ℕ) :
    ∀ (wp0 : ℕ) (σ : Store),
    1 ≤ wpJ → σ 0 = M → σ (M + wpJ) = wp0 → M + wpJ < bound → bound ≤ wp0 → wp0 ≠ 0 →
    (∀ p ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ) →
    (∀ i, i < lits.length →
      ((writeLitsProg wpJ lits).eval σ) (wp0 + 2 * i) = (lits.getD i defLit).1.eval σ ∧
      ((writeLitsProg wpJ lits).eval σ) (wp0 + 2 * i + 1) = (lits.getD i defLit).2.eval σ) ∧
    ((writeLitsProg wpJ lits).eval σ) (M + wpJ) = wp0 + 2 * lits.length ∧
    ((writeLitsProg wpJ lits).eval σ) 0 = M ∧
    (∀ r, r < wp0 → r ≠ M + wpJ → ((writeLitsProg wpJ lits).eval σ) r = σ r) := by
  induction lits with
  | nil =>
      intro wp0 σ hwpJ hM hwp0cell hsep hbwp hwp0pos hinv
      simp [writeLitsProg, hM, hwp0cell]
  | cons hd tail ih =>
      intro wp0 σ hwpJ hM hwp0cell hsep hbwp hwp0pos hinv
      obtain ⟨tagE, varE⟩ := hd
      have hmemhd : (tagE, varE) ∈ (tagE, varE) :: tail := List.mem_cons_self
      have hvarE : varE.eval ((Program.assignInd (ctlCell wpJ) tagE).eval σ) = varE.eval σ := by
        have hσ1eq : (Program.assignInd (ctlCell wpJ) tagE).eval σ
            = writeReg σ wp0 (tagE.eval σ) := by
          rw [eval_assignInd, ctlCell_eval, hM, hwp0cell]
        rw [hσ1eq]
        exact (hinv (tagE, varE) hmemhd σ (writeReg σ wp0 (tagE.eval σ)) hM
          (by rw [writeReg_diff σ wp0 (tagE.eval σ) 0 (by omega), hM])
          (fun r hr1 hr2 => writeReg_diff σ wp0 (tagE.eval σ) r (by omega))).2
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        writeLitProg_eval_state wpJ tagE varE M wp0 σ hwpJ hM hwp0cell (by omega) hwp0pos hvarE
      set σ1 := (writeLitProg wpJ tagE varE).eval σ with hσ1def
      have hagree1 : ∀ r, r < bound → r ≠ M + wpJ → σ1 r = σ r := by
        intro r hr1 hr2
        exact h5 r (by omega) (by omega) hr2
      have hinv' : ∀ p ∈ tail, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
          (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) →
          p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ :=
        fun p hp => hinv p (List.mem_cons_of_mem _ hp)
      obtain ⟨itail, jtail, ktail, ltail⟩ :=
        ih (wp0 + 2) σ1 hwpJ h4 h3 hsep (by omega) (by omega) hinv'
      have hltailwp0 : (writeLitsProg wpJ tail).eval σ1 wp0 = σ1 wp0 :=
        ltail wp0 (by omega) (by omega)
      have hltailwp1 : (writeLitsProg wpJ tail).eval σ1 (wp0 + 1) = σ1 (wp0 + 1) :=
        ltail (wp0 + 1) (by omega) (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]
            unfold writeLitsProg
            rw [eval_seq, ← hσ1def]
            rw [hltailwp0, hltailwp1]
            exact ⟨h1, h2⟩
        | succ i =>
            have hilt : i < tail.length := by simp [List.length_cons] at hi; omega
            have hi1 := itail i hilt
            have heq1 : wp0 + 2 * (i + 1) = wp0 + 2 + 2 * i := by ring
            unfold writeLitsProg
            rw [eval_seq, ← hσ1def]
            rw [heq1]
            have hmemp : (tail.getD i defLit) ∈ tail := by
              rw [List.getD_eq_getElem tail defLit hilt]
              exact List.getElem_mem hilt
            obtain ⟨hpEq1, hpEq2⟩ := hinv' (tail.getD i defLit) hmemp σ σ1 hM h4 hagree1
            simp only [List.getD_cons_succ]
            exact ⟨by rw [hi1.1, hpEq1], by rw [hi1.2, hpEq2]⟩
      · unfold writeLitsProg
        rw [eval_seq, ← hσ1def]
        rw [jtail, List.length_cons]
        ring
      · unfold writeLitsProg
        rw [eval_seq, ← hσ1def]
        exact ktail
      · intro r hr1 hr2
        unfold writeLitsProg
        rw [eval_seq, ← hσ1def]
        rw [ltail r (by omega) hr2]
        exact h5 r (by omega) (by omega) hr2

/-- Write clause `lits` (a compile-time list of tag/variable expression pairs)
    at the row base the write pointer `wpJ` points to on entry: the payload
    count cell (`wp + 1`) gets `lits.length`, the pointer advances past it, and
    the literals follow via `writeLitsProg`. The row-key cell (`wp + 0`) is
    never written — the emitter's `RowsWritten` contract does not read it
    either. -/
def writeClauseProg (wpJ : ℕ) (lits : List (Expr × Expr)) : Program :=
  .seq (.seq
    (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const lits.length))
    (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))))
    (writeLitsProg wpJ lits)

/-- Unfolds `writeClauseProg`'s net effect: the count cell gets `lits.length`,
    each literal `i` lands at `wp + 2 + 2*i`/`wp + 2 + 2*i + 1` — matching the
    offsets `RowsWritten` requires — and the pointer ends at
    `wp + 2 + 2 * lits.length`, ready for the next clause. -/
lemma writeClauseProg_eval_state (wpJ : ℕ) (lits : List (Expr × Expr)) (M wp : ℕ) (σ : Store)
    (hwpJ : 1 ≤ wpJ) (hM : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + wpJ < wp)
    (hinv : ∀ p ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ) :
    ((writeClauseProg wpJ lits).eval σ) (wp + 1) = lits.length ∧
    (∀ i, i < lits.length →
      ((writeClauseProg wpJ lits).eval σ) (wp + 2 + 2 * i) = (lits.getD i defLit).1.eval σ ∧
      ((writeClauseProg wpJ lits).eval σ) (wp + 2 + 2 * i + 1) = (lits.getD i defLit).2.eval σ) ∧
    ((writeClauseProg wpJ lits).eval σ) (M + wpJ) = wp + 2 + 2 * lits.length ∧
    ((writeClauseProg wpJ lits).eval σ) 0 = M ∧
    (∀ r, r < wp → r ≠ M + wpJ → ((writeClauseProg wpJ lits).eval σ) r = σ r) := by
  unfold writeClauseProg
  have haddr1 : (Expr.add (ctlCell wpJ) (Expr.const 1)).eval σ = wp + 1 := by
    simp [Expr.eval, ctlCell_eval, hM, hwp]
  set σA := (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1))
    (Expr.const lits.length)).eval σ with hσAdef
  have hσAeq : σA = writeReg σ (wp + 1) lits.length := by
    rw [hσAdef, eval_assignInd, haddr1]; rfl
  have hσA0 : σA 0 = M := by
    rw [hσAeq, writeReg_diff σ (wp + 1) lits.length 0 (by omega), hM]
  have hσActl : σA (M + wpJ) = wp := by
    rw [hσAeq, writeReg_diff σ (wp + 1) lits.length (M + wpJ) (by omega), hwp]
  have hσAcnt : σA (wp + 1) = lits.length := by rw [hσAeq, writeReg_same]
  have haddr2 : (ctlAddr wpJ).eval σA = M + wpJ := by rw [ctlAddr_eval, hσA0]
  have hval2 : (Expr.add (ctlCell wpJ) (Expr.const 2)).eval σA = wp + 2 := by
    simp [Expr.eval, ctlCell_eval, hσA0, hσActl]
  set σB := (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σA with hσBdef
  have hσBeq : σB = writeReg σA (M + wpJ) (wp + 2) := by
    unfold ctlAssign at hσBdef
    rw [hσBdef, eval_assignInd, haddr2, hval2]
  have hσB0 : σB 0 = M := by
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) 0 (by omega), hσA0]
  have hσBctl : σB (M + wpJ) = wp + 2 := by rw [hσBeq, writeReg_same]
  have hσBcnt : σB (wp + 1) = lits.length := by
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) (wp + 1) (by omega), hσAcnt]
  have hagreeσB : ∀ r, r < wp → r ≠ M + wpJ → σB r = σ r := by
    intro r hr1 hr2
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) r hr2]
    rw [hσAeq, writeReg_diff σ (wp + 1) lits.length r (by omega)]
  obtain ⟨itail, jtail, ktail, ltail⟩ :=
    writeLitsProg_eval_state wpJ lits M wp (wp + 2) σB hwpJ hσB0 hσBctl hsep (by omega) (by omega)
      hinv
  have hgoal : (Program.seq (Program.seq
      (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) (Expr.const lits.length))
      (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))))
      (writeLitsProg wpJ lits)).eval σ = (writeLitsProg wpJ lits).eval σB := by
    rw [eval_seq, eval_seq, ← hσAdef, ← hσBdef]
  rw [hgoal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ltail (wp + 1) (by omega) (by omega), hσBcnt]
  · intro i hi
    have hmemp : (lits.getD i defLit) ∈ lits := by
      rw [List.getD_eq_getElem lits defLit hi]
      exact List.getElem_mem hi
    obtain ⟨hpEq1, hpEq2⟩ := hinv (lits.getD i defLit) hmemp σ σB hM hσB0 hagreeσB
    exact ⟨by rw [(itail i hi).1, hpEq1], by rw [(itail i hi).2, hpEq2]⟩
  · exact jtail
  · exact ktail
  · intro r hr1 hr2
    rw [ltail r (by omega) hr2, hagreeσB r hr1 hr2]

/-! ## Writing a clause of run-time width, over positive literals only

`writeAtLeastOneProg` handles the complementary case to `writeClauseProg`: the
clause width is not known at compile time but held in a run-time expression
`cntE`, and every one of its literals is `(false, varE i)` for a fixed variable
expression parameterized by the loop counter — exactly the "some register is one
of these `n` cells" clause family. It stages `cntE` into the count cell first,
resets the loop counter `iJ` to zero, then runs `writeAtLeastOneBody` (a
`writeLitProg` call plus a counter bump) `cntE`-many times via `forN`. -/

/-- One iteration of `writeAtLeastOneProg`'s loop: write literal
    `(false, varE)` at the current write pointer, then bump the loop counter
    held in control cell `iJ`. -/
def writeAtLeastOneBody (wpJ iJ : ℕ) (varE : Expr) : Program :=
  .seq (writeLitProg wpJ (.const 0) varE) (ctlAssign iJ (.add (ctlCell iJ) (.const 1)))

/-- The loop's observable state after a fixed number of literal writes. -/
def WriteAtLeastOneBodyLoopGoal (wpJ iJ : ℕ) (varE : Expr) (M wp : ℕ)
    (σ0 : Store) (t idx : ℕ) (τ : Store) : Prop :=
  (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) 0 = M ∧
  (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (M + wpJ) = wp + 2 * (idx + t) ∧
  (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (M + iJ) = idx + t ∧
  (∀ q, q < t →
    (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (wp + 2 * (idx + q)) = 0) ∧
  (∀ q, q < t →
    (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (wp + 2 * (idx + q) + 1) =
      varE.eval (writeReg σ0 (M + iJ) (idx + q))) ∧
  (∀ r, r ≠ M + wpJ → r ≠ M + iJ →
    (r < wp + 2 * idx ∨ wp + 2 * (idx + t) ≤ r) →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) r = τ r)

/-- The temporary zeroing of the write pointer does not change `varE`. -/
lemma writeAtLeastOneBody_loop_iteration_var_frame
    (wpJ : ℕ) (varE : Expr) (M B wp idx : ℕ) (τ : Store)
    (hB : B ≤ wp)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ')
    (h0 : τ 0 = M) (hwp : τ (M + wpJ) = wp + 2 * idx)
    (hwpval : wp + 2 * idx ≠ 0) :
    varE.eval ((Program.assignInd (ctlCell wpJ) (Expr.const 0)).eval τ) = varE.eval τ := by
  have heval : (Program.assignInd (ctlCell wpJ) (Expr.const 0)).eval τ =
      writeReg τ (wp + 2 * idx) 0 := by
    rw [eval_assignInd, ctlCell_eval, h0, hwp]
    rfl
  rw [heval]
  apply hvarE
  · rw [writeReg_diff τ (wp + 2 * idx) 0 0 (Ne.symm hwpval)]
    exact h0
  · exact h0
  · intro r hr1 hr2
    rw [writeReg_diff τ (wp + 2 * idx) 0 r (by omega)]

/-- One loop iteration writes its literal, advances both controls, and preserves outside cells. -/
lemma writeAtLeastOneBody_loop_iteration
    (wpJ iJ : ℕ) (varE : Expr) (M B wp : ℕ) (σ0 : Store)
    (hwpJ : 1 ≤ wpJ) (hiJ : 1 ≤ iJ) (hne : wpJ ≠ iJ) (hB : B ≤ wp)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ')
    (idx : ℕ) (τ : Store) (h0 : τ 0 = M)
    (hwp : τ (M + wpJ) = wp + 2 * idx) (hiJcell : τ (M + iJ) = idx)
    (hsepW : M + wpJ < B) (hsepI : M + iJ < B)
    (hbase : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ r = σ0 r) :
    ∃ τ2, (writeAtLeastOneBody wpJ iJ varE).eval τ = τ2 ∧
      τ2 0 = M ∧ τ2 (M + wpJ) = wp + 2 * (idx + 1) ∧
      τ2 (M + iJ) = idx + 1 ∧ τ2 (wp + 2 * idx) = 0 ∧
      τ2 (wp + 2 * idx + 1) = varE.eval τ ∧
      (∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ2 r = σ0 r) ∧
      (∀ r, r ≠ M + wpJ → r ≠ M + iJ →
        (r < wp + 2 * idx ∨ wp + 2 * (idx + 1) ≤ r) → τ2 r = τ r) := by
  have hwpval : wp + 2 * idx ≠ 0 := by omega
  have hvarEbody := writeAtLeastOneBody_loop_iteration_var_frame wpJ varE M B wp idx τ
    hB hvarE h0 hwp hwpval
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    writeLitProg_eval_state wpJ (Expr.const 0) varE M (wp + 2 * idx) τ hwpJ h0 hwp
      (by omega) hwpval hvarEbody
  set τ1 := (writeLitProg wpJ (Expr.const 0) varE).eval τ with hτ1def
  have hτ1wp0 : τ1 (wp + 2 * idx) = 0 := by rw [h1]; rfl
  have hτ1wp1 : τ1 (wp + 2 * idx + 1) = varE.eval τ := h2
  have hτ1ctlw : τ1 (M + wpJ) = wp + 2 * idx + 2 := h3
  have hτ1eq0 : τ1 0 = M := h4
  have haddrI : (ctlAddr iJ).eval τ1 = M + iJ := by rw [ctlAddr_eval, hτ1eq0]
  have hiJval : τ1 (M + iJ) = idx := by
    rw [h5 (M + iJ) (by omega) (by omega) (by omega)]
    exact hiJcell
  have hvalI : (Expr.add (ctlCell iJ) (Expr.const 1)).eval τ1 = idx + 1 := by
    simp [Expr.eval, ctlCell_eval, hτ1eq0, hiJval]
  set τ2 := (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1))).eval τ1 with hτ2def
  have hτ2eq : τ2 = writeReg τ1 (M + iJ) (idx + 1) := by
    unfold ctlAssign at hτ2def
    rw [hτ2def, eval_assignInd, haddrI, hvalI]
  have hτ20 : τ2 0 = M := by
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) 0 (by omega), hτ1eq0]
  have hτ2ctlw : τ2 (M + wpJ) = wp + 2 * idx + 2 := by
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) (M + wpJ) (by omega), hτ1ctlw]
  have hτ2ctli : τ2 (M + iJ) = idx + 1 := by rw [hτ2eq, writeReg_same]
  have hτ2wp0 : τ2 (wp + 2 * idx) = 0 := by
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) (wp + 2 * idx) (by omega), hτ1wp0]
  have hτ2wp1 : τ2 (wp + 2 * idx + 1) = varE.eval τ := by
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) (wp + 2 * idx + 1) (by omega), hτ1wp1]
  have hτ2ctlw' : τ2 (M + wpJ) = wp + 2 * (idx + 1) := by
    rw [hτ2ctlw]
    omega
  have hbase2 : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ2 r = σ0 r := by
    intro r hr1 hr2 hr3
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) r hr3,
      h5 r (by omega) (by omega) hr2]
    exact hbase r hr1 hr2 hr3
  have hframeStep : ∀ r, r ≠ M + wpJ → r ≠ M + iJ →
      (r < wp + 2 * idx ∨ wp + 2 * (idx + 1) ≤ r) → τ2 r = τ r := by
    intro r hrW hrI hrange
    rw [hτ2eq, writeReg_diff τ1 (M + iJ) (idx + 1) r hrI, h5 r (by omega) (by omega) hrW]
  have hbodyeval : (writeAtLeastOneBody wpJ iJ varE).eval τ = τ2 := by
    unfold writeAtLeastOneBody
    rw [eval_seq, ← hτ1def, ← hτ2def]
  exact ⟨τ2, hbodyeval, hτ20, hτ2ctlw', hτ2ctli, hτ2wp0, hτ2wp1, hbase2, hframeStep⟩

/-- The prepended iteration supplies the first false output cell. -/
lemma writeAtLeastOneBody_loop_step_false_first
    (wpJ iJ : ℕ) (varE : Expr) (wp t idx : ℕ) (τ τ2 : Store)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hpreserved : (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
      (wp + 2 * idx) = τ2 (wp + 2 * idx))
    (hwrite : τ2 (wp + 2 * idx) = 0) :
    (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
      (wp + 2 * (idx + 0)) = 0 := by
  rw [hstep]
  simp only [Nat.add_zero]
  rw [hpreserved]
  exact hwrite

/-- False output cells after the first are inherited from the induction hypothesis. -/
lemma writeAtLeastOneBody_loop_step_false_later
    (wpJ iJ : ℕ) (varE : Expr) (wp t idx : ℕ) (τ τ2 : Store)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hprev : ∀ q, q < t →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
        (wp + 2 * (idx + 1 + q)) = 0) :
    ∀ q, 0 < q → q < t + 1 →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
        (wp + 2 * (idx + q)) = 0 := by
  intro q hqpos hq
  have hlt : q - 1 < t := by omega
  have hprevq := hprev (q - 1) hlt
  have hidx : idx + 1 + (q - 1) = idx + q := by omega
  rw [hstep]
  rw [hidx] at hprevq
  exact hprevq

/-- The false-cell clause combines the first and later iterations. -/
lemma writeAtLeastOneBody_loop_step_false_at
    (wpJ iJ : ℕ) (varE : Expr) (wp t idx : ℕ) (τ τ2 : Store)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hpreserved : (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
      (wp + 2 * idx) = τ2 (wp + 2 * idx))
    (hwrite : τ2 (wp + 2 * idx) = 0)
    (hprev : ∀ q, q < t →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
        (wp + 2 * (idx + 1 + q)) = 0) :
    ∀ q, q < t + 1 →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
        (wp + 2 * (idx + q)) = 0 := by
  intro q hq
  rcases Nat.eq_zero_or_pos q with hzero | hpos
  · subst q
    exact writeAtLeastOneBody_loop_step_false_first wpJ iJ varE wp t idx τ τ2
      hstep hpreserved hwrite
  · exact writeAtLeastOneBody_loop_step_false_later wpJ iJ varE wp t idx τ τ2
      hstep hprev q hpos hq

/-- The first variable cell uses the counter value before it is advanced. -/
lemma writeAtLeastOneBody_loop_step_var_first
    (wpJ iJ : ℕ) (varE : Expr) (M B wp t idx : ℕ) (σ0 τ τ2 : Store)
    (hσ00 : σ0 0 = M) (hiJ : 1 ≤ iJ) (hB : B ≤ wp)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ')
    (h0 : τ 0 = M) (hwp : τ (M + wpJ) = wp + 2 * idx)
    (hiJcell : τ (M + iJ) = idx) (hsepW : M + wpJ < B) (hsepI : M + iJ < B)
    (hbase : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ r = σ0 r)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hτ2wp1 : τ2 (wp + 2 * idx + 1) = varE.eval τ)
    (hprevFrame : ∀ r, r ≠ M + wpJ → r ≠ M + iJ →
      (r < wp + 2 * (idx + 1) ∨ wp + 2 * ((idx + 1) + t) ≤ r) →
        (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2) r = τ2 r) :
    (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
      (wp + 2 * (idx + 0) + 1) =
        varE.eval (writeReg σ0 (M + iJ) (idx + 0)) := by
  have hidx : wp + 2 * (idx + 0) + 1 = wp + 2 * idx + 1 := by omega
  rw [hstep, hidx]
  have hframe := hprevFrame (wp + 2 * idx + 1) (by omega) (by omega) (Or.inl (by omega))
  rw [hframe, hτ2wp1]
  have heval := hvarE τ (writeReg σ0 (M + iJ) idx) h0
    (by rw [writeReg_diff σ0 (M + iJ) idx 0 (by omega)]; exact hσ00)
    (by
      intro r hr1 hr2
      rcases eq_or_ne r (M + iJ) with rfl | hrne
      · rw [writeReg_same]
        exact hiJcell
      · rw [writeReg_diff σ0 (M + iJ) idx r hrne]
        exact hbase r hr1 hr2 hrne)
  simpa only [Nat.add_zero] using heval

/-- Later variable cells are inherited from the induction hypothesis. -/
lemma writeAtLeastOneBody_loop_step_var_later
    (wpJ iJ : ℕ) (varE : Expr) (M : ℕ) (σ0 : Store) (wp t idx : ℕ) (τ τ2 : Store)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hprev : ∀ q, q < t →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
        (wp + 2 * (idx + 1 + q) + 1) =
          varE.eval (writeReg σ0 (M + iJ) (idx + 1 + q))) :
    ∀ q, 0 < q → q < t + 1 →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
        (wp + 2 * (idx + q) + 1) =
          varE.eval (writeReg σ0 (M + iJ) (idx + q)) := by
  intro q hqpos hq
  have hlt : q - 1 < t := by omega
  have hprevq := hprev (q - 1) hlt
  have hidx : idx + 1 + (q - 1) = idx + q := by omega
  rw [hstep]
  rw [hidx] at hprevq
  exact hprevq

/-- The variable-cell clause combines the first and later iterations. -/
lemma writeAtLeastOneBody_loop_step_var_at
    (wpJ iJ : ℕ) (varE : Expr) (M B wp t idx : ℕ) (σ0 τ τ2 : Store)
    (hσ00 : σ0 0 = M) (hiJ : 1 ≤ iJ) (hB : B ≤ wp)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ')
    (h0 : τ 0 = M) (hwp : τ (M + wpJ) = wp + 2 * idx)
    (hiJcell : τ (M + iJ) = idx) (hsepW : M + wpJ < B) (hsepI : M + iJ < B)
    (hbase : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ r = σ0 r)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hτ2wp1 : τ2 (wp + 2 * idx + 1) = varE.eval τ)
    (hprevFrame : ∀ r, r ≠ M + wpJ → r ≠ M + iJ →
      (r < wp + 2 * (idx + 1) ∨ wp + 2 * ((idx + 1) + t) ≤ r) →
        (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2) r = τ2 r)
    (hprev : ∀ q, q < t →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
        (wp + 2 * (idx + 1 + q) + 1) =
          varE.eval (writeReg σ0 (M + iJ) (idx + 1 + q))) :
    ∀ q, q < t + 1 →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ)
        (wp + 2 * (idx + q) + 1) =
          varE.eval (writeReg σ0 (M + iJ) (idx + q)) := by
  intro q hq
  rcases Nat.eq_zero_or_pos q with hzero | hpos
  · subst q
    exact writeAtLeastOneBody_loop_step_var_first wpJ iJ varE M B wp t idx σ0 τ τ2
      hσ00 hiJ hB hvarE h0 hwp hiJcell hsepW hsepI hbase hstep hτ2wp1 hprevFrame
  · exact writeAtLeastOneBody_loop_step_var_later wpJ iJ varE M σ0 wp t idx τ τ2
      hstep hprev q hpos hq

/-- The inductive step transports the loop invariant across one prepended iteration. -/
lemma writeAtLeastOneBody_loop_step
    (wpJ iJ : ℕ) (varE : Expr) (M B wp : ℕ) (σ0 : Store)
    (hσ00 : σ0 0 = M) (hiJ : 1 ≤ iJ) (hB : B ≤ wp)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ')
    (t idx : ℕ) (τ τ2 : Store) (h0 : τ 0 = M)
    (hwp : τ (M + wpJ) = wp + 2 * idx) (hiJcell : τ (M + iJ) = idx)
    (hsepW : M + wpJ < B) (hsepI : M + iJ < B)
    (hbase : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ r = σ0 r)
    (hstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
      loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2)
    (hτ2wp0 : τ2 (wp + 2 * idx) = 0)
    (hτ2wp1 : τ2 (wp + 2 * idx + 1) = varE.eval τ)
    (hframeStep : ∀ r, r ≠ M + wpJ → r ≠ M + iJ →
      (r < wp + 2 * idx ∨ wp + 2 * (idx + 1) ≤ r) → τ2 r = τ r)
    (ih : WriteAtLeastOneBodyLoopGoal wpJ iJ varE M wp σ0 t (idx + 1) τ2) :
    WriteAtLeastOneBodyLoopGoal wpJ iJ varE M wp σ0 (t + 1) idx τ := by
  rcases ih with ⟨g0, g1, g2, g3, g4, g5⟩
  have hfirstPreserved := g5 (wp + 2 * idx) (by omega) (by omega) (Or.inl (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
    exact g0
  · rw [hstep, g1]
    ring_nf
  · rw [hstep, g2]
    ring
  · exact writeAtLeastOneBody_loop_step_false_at wpJ iJ varE wp t idx τ τ2
      hstep hfirstPreserved hτ2wp0 g3
  · exact writeAtLeastOneBody_loop_step_var_at wpJ iJ varE M B wp t idx σ0 τ τ2
      hσ00 hiJ hB hvarE h0 hwp hiJcell hsepW hsepI hbase hstep hτ2wp1 g5 g4
  · intro r hr1 hr2 hrange
    rcases hrange with hlt | hge
    · rw [hstep]
      calc
        _ = τ2 r := g5 r hr1 hr2 (Or.inl (by omega))
        _ = τ r := hframeStep r hr1 hr2 (Or.inl hlt)
    · rw [hstep]
      calc
        _ = τ2 r := g5 r hr1 hr2 (Or.inr (by omega))
        _ = τ r := hframeStep r hr1 hr2 (Or.inr (by omega))

/-- Loop invariant for `t` repetitions of `writeAtLeastOneBody`, generalized over
    the starting counter value `idx` (mirroring `emit_zero_loop_invariant`'s cursor
    generalization) so the induction peels one iteration off the front at each
    step: `varE` may read the loop counter, so its value at iteration `idx + q`
    is stated against `writeReg σ0 (M + iJ) (idx + q)` — the fixed store `σ0`
    with only the counter cell set to that iteration's value.

    `hvarE` is a *frame* condition rather than a dependency-on-one-cell
    condition: `varE` may read any cell below the freeze bound `B` except the
    write pointer.  Callers whose variable numbers are dense-layout arithmetic
    read the enclosing loops' counters and the run-time sizes out of control
    cells, so a hypothesis naming only the counter cell would be false for them;
    stating it as "agree below `B`, off the pointer" keeps every such caller
    dischargeable while still pinning the pointer as the only cell the routine
    is allowed to move under `varE`'s feet. -/
lemma writeAtLeastOneBody_loop_invariant (wpJ iJ : ℕ) (varE : Expr) (M B wp : ℕ)
    (hwpJ : 1 ≤ wpJ) (hiJ : 1 ≤ iJ) (hne : wpJ ≠ iJ) (hB : B ≤ wp)
    (σ0 : Store) (hσ00 : σ0 0 = M)
    (hvarE : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ r = σ' r) → varE.eval σ = varE.eval σ') :
    ∀ t idx (τ : Store), τ 0 = M → τ (M + wpJ) = wp + 2 * idx → τ (M + iJ) = idx →
      M + wpJ < B → M + iJ < B →
      (∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → τ r = σ0 r) →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) 0 = M ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (M + wpJ) = wp + 2 * (idx + t) ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (M + iJ) = idx + t ∧
      (∀ q, q < t →
        (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (wp + 2 * (idx + q)) = 0) ∧
      (∀ q, q < t → (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) (wp + 2 * (idx + q) + 1)
        = varE.eval (writeReg σ0 (M + iJ) (idx + q))) ∧
      (∀ r, r ≠ M + wpJ → r ≠ M + iJ → (r < wp + 2 * idx ∨ wp + 2 * (idx + t) ≤ r) →
        (loopEval (writeAtLeastOneBody wpJ iJ varE) t τ) r = τ r) := by
  intro t
  induction t with
  | zero =>
      intro idx τ h0 hwp hiJcell hsepW hsepI _hbase
      rw [loopEval_zero]
      exact ⟨h0, by omega, by omega, fun q hq => absurd hq (by omega),
        fun q hq => absurd hq (by omega), fun r _ _ _ => rfl⟩
  | succ t ih =>
      intro idx τ h0 hwp hiJcell hsepW hsepI hbase
      obtain ⟨τ2, hbodyeval, hτ20, hτ2ctlw, hτ2ctli, hτ2wp0, hτ2wp1, hbase2,
          hframeStep⟩ :=
        writeAtLeastOneBody_loop_iteration wpJ iJ varE M B wp σ0 hwpJ hiJ hne hB hvarE
          idx τ h0 hwp hiJcell hsepW hsepI hbase
      have hloopstep : loopEval (writeAtLeastOneBody wpJ iJ varE) (t + 1) τ =
          loopEval (writeAtLeastOneBody wpJ iJ varE) t τ2 := by
        rw [loopEval_succ, hbodyeval]
      exact writeAtLeastOneBody_loop_step wpJ iJ varE M B wp σ0 hσ00 hiJ hB hvarE
        t idx τ τ2 h0 hwp hiJcell hsepW hsepI hbase hloopstep hτ2wp0 hτ2wp1 hframeStep
        (ih (idx + 1) τ2 hτ20 hτ2ctlw hτ2ctli hsepW hsepI hbase2)

/-- Write an `atLeastOne` clause of run-time width `cntE.eval σ`, whose `i`-th
    literal is `(false, varE)` at loop counter `i`: stage `cntE` into the count
    cell, advance the pointer past it, reset the loop counter, then run
    `writeAtLeastOneBody` once per iteration. -/
def writeAtLeastOneProg (wpJ iJ : ℕ) (cntE varE : Expr) : Program :=
  .seq (.assignInd (.add (ctlCell wpJ) (.const 1)) cntE)
  (.seq (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))
  (.seq (ctlAssign iJ (.const 0))
  (.forN cntE (writeAtLeastOneBody wpJ iJ varE))))

/-- Unfolds `writeAtLeastOneProg`'s net effect: the count cell gets
    `cntE.eval σ`, each literal `i < cntE.eval σ` lands as `(false, varE)` at
    the counter value `i` (via `writeReg σ (M + iJ) i` — the entry store with
    only the counter cell set to `i`, since `writeAtLeastOneBody_loop_invariant`
    tracks values against the fixed pre-loop store `σ`), and the pointer ends at
    `wp + 2 + 2 * cntE.eval σ`.

    Both `hcntE` and `hvarE` are frame conditions against a freeze bound `B`
    below the entry pointer: the routine's own writes all land at or above `wp`,
    or in the two control cells, so an expression reading only cells below `B`
    other than those sees the same values throughout.  `cntE` additionally may
    not read the counter cell, which the routine resets; `varE` is expected to
    read it, and does so through the counter's own iteration value. -/
lemma writeAtLeastOneProg_eval_state (wpJ iJ : ℕ) (cntE varE : Expr) (M B wp : ℕ) (σ : Store)
    (hwpJ : 1 ≤ wpJ) (hiJ : 1 ≤ iJ) (hne : wpJ ≠ iJ)
    (hM : σ 0 = M) (hwp : σ (M + wpJ) = wp)
    (hsepW : M + wpJ < B) (hsepI : M + iJ < B) (hBwp : B ≤ wp)
    (hcntE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → σ1 r = σ2 r) → cntE.eval σ1 = cntE.eval σ2)
    (hvarE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < B → r ≠ M + wpJ → σ1 r = σ2 r) → varE.eval σ1 = varE.eval σ2) :
    ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) (wp + 1) = cntE.eval σ ∧
    (∀ i, i < cntE.eval σ →
      ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) (wp + 2 + 2 * i) = 0 ∧
      ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) (wp + 2 + 2 * i + 1)
        = varE.eval (writeReg σ (M + iJ) i)) ∧
    ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) (M + wpJ) = wp + 2 + 2 * cntE.eval σ ∧
    ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) (M + iJ) = cntE.eval σ ∧
    ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) 0 = M ∧
    (∀ r, r ≠ M + wpJ → r ≠ M + iJ → (r < wp ∨ wp + 2 + 2 * cntE.eval σ ≤ r) →
      ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) r = σ r) := by
  set n := cntE.eval σ with hndef
  have haddrA : (Expr.add (ctlCell wpJ) (Expr.const 1)).eval σ = wp + 1 := by
    simp [Expr.eval, ctlCell_eval, hM, hwp]
  set σA := (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) cntE).eval σ with hσAdef
  have hσAeq : σA = writeReg σ (wp + 1) n := by
    rw [hσAdef, eval_assignInd, haddrA]
  have hσA0 : σA 0 = M := by rw [hσAeq, writeReg_diff σ (wp + 1) n 0 (by omega), hM]
  have hσActl : σA (M + wpJ) = wp := by
    rw [hσAeq, writeReg_diff σ (wp + 1) n (M + wpJ) (by omega), hwp]
  have haddrB : (Expr.add (ctlCell wpJ) (Expr.const 2)).eval σA = wp + 2 := by
    simp [Expr.eval, ctlCell_eval, hσA0, hσActl]
  set σB := (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σA with hσBdef
  have hσBeq : σB = writeReg σA (M + wpJ) (wp + 2) := by
    unfold ctlAssign at hσBdef
    rw [hσBdef, eval_assignInd, ctlAddr_eval, hσA0, haddrB]
  have hσB0 : σB 0 = M := by
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) 0 (by omega), hσA0]
  have hσBctl : σB (M + wpJ) = wp + 2 := by rw [hσBeq, writeReg_same]
  set σC := (ctlAssign iJ (Expr.const 0)).eval σB with hσCdef
  have hσCeq : σC = writeReg σB (M + iJ) 0 := by
    unfold ctlAssign at hσCdef
    rw [hσCdef, eval_assignInd, ctlAddr_eval, hσB0]
    simp [Expr.eval]
  have hσC0 : σC 0 = M := by
    rw [hσCeq, writeReg_diff σB (M + iJ) 0 0 (by omega), hσB0]
  have hσCctl : σC (M + wpJ) = wp + 2 := by
    rw [hσCeq, writeReg_diff σB (M + iJ) 0 (M + wpJ) (by omega), hσBctl]
  have hσCiJ : σC (M + iJ) = 0 := by rw [hσCeq, writeReg_same]
  have hagreeC : ∀ r, r ≠ wp + 1 → r ≠ M + wpJ → r ≠ M + iJ → σC r = σ r := by
    intro r hr1 hr2 hr3
    rw [hσCeq, writeReg_diff σB (M + iJ) 0 r hr3, hσBeq,
      writeReg_diff σA (M + wpJ) (wp + 2) r hr2, hσAeq,
      writeReg_diff σ (wp + 1) n r hr1]
  have hbaseC : ∀ r, r < B → r ≠ M + wpJ → r ≠ M + iJ → σC r = σ r :=
    fun r hr1 hr2 hr3 => hagreeC r (by omega) hr2 hr3
  have hcntEC : cntE.eval σC = n := hcntE σC σ hσC0 hM hbaseC
  have hforNeval : (Program.forN cntE (writeAtLeastOneBody wpJ iJ varE)).eval σC
      = loopEval (writeAtLeastOneBody wpJ iJ varE) n σC := by
    rw [eval_forN, hcntEC]
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ :=
    writeAtLeastOneBody_loop_invariant wpJ iJ varE M B (wp + 2) hwpJ hiJ hne (by omega)
      σ hM hvarE n 0 σC hσC0 (by rw [hσCctl]) hσCiJ (by omega) (by omega) hbaseC
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p1 p2 p3 p4 p5
  have hgoal : (writeAtLeastOneProg wpJ iJ cntE varE).eval σ
      = loopEval (writeAtLeastOneBody wpJ iJ varE) n σC := by
    unfold writeAtLeastOneProg
    rw [eval_seq, eval_seq, eval_seq, ← hσAdef, ← hσBdef, ← hσCdef, hforNeval]
  rw [hgoal]
  refine ⟨?_, ?_, p1, p2, p0, ?_⟩
  · rw [p5 (wp + 1) (by omega) (by omega) (Or.inl (by omega)), hσCeq,
      writeReg_diff σB (M + iJ) 0 (wp + 1) (by omega), hσBeq,
      writeReg_diff σA (M + wpJ) (wp + 2) (wp + 1) (by omega), hσAeq, writeReg_same]
  · intro i hi
    exact ⟨p3 i hi, p4 i hi⟩
  · intro r hr1 hr2 hrange
    have hcond : r < wp + 2 ∨ wp + 2 + 2 * n ≤ r := by
      rcases hrange with h | h
      · left; omega
      · right; omega
    rw [p5 r hr1 hr2 hcond]
    exact hagreeC r (by rcases hrange with h | h <;> omega) hr1 hr2

end NPComplete.CookLevin

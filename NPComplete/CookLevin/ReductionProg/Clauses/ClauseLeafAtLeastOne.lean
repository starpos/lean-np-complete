module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteLoop

/-!
`clauseLoopBody_leaf` fixes the literal *expressions* at compile time, so it can
only end a nest whose clause width is a numeral.  Two of the generated CNF's
clauses are not of that shape: the accept family's halt-state clause ranges over
`descHaltStates`, and the init family's free-cell clause ranges over the allowed
alphabet — both run-time lists, whose lengths are values the producer computes
rather than constants it was compiled with.

Both are `atLeastOne`, so all their literals are positive and differ only in the
variable number.  That is exactly `writeAtLeastOneProg`'s shape, and this file
wraps it as a second leaf: one clause per iteration, of run-time width, ending a
nest the same way the fixed-width leaf does.

The variable expression uses an *inner* counter over the clause's literals,
separate from the outer clause counter, so this leaf uses two control cells.
`hvarE` says the variable expression is stable under stores that agree below the
freeze bound except at the write pointer, matching the primitive's own frame
condition; `hvar` gives its value once the pins hold and the outer and inner
counters are fixed.  A caller therefore supplies one fact about its dense-layout
expression rather than one per literal.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## The shape of an `atLeastOne` clause

`atLeastOne` maps `Literal.pos` over its variable list, so its `k`-th literal is
determined by the list's `k`-th entry.  Reading that off once here keeps the leaf
lemma's obligations free of `List.map` reasoning. -/

lemma atLeastOne_getD (vs : List ℕ) (k : ℕ) (hk : k < vs.length) :
    (atLeastOne vs).lits.getD k default = Literal.pos (vs.getD k 0) := by
  unfold atLeastOne
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some]
  rfl

lemma atLeastOne_length (vs : List ℕ) : (atLeastOne vs).lits.length = vs.length := by
  unfold atLeastOne; simp

/-- Every literal is positive, so every tag cell the routine writes is `0`. -/
lemma atLeastOne_tag (vs : List ℕ) (k : ℕ) (hk : k < vs.length) :
    litTag ((atLeastOne vs).lits.getD k default) = false := by
  rw [atLeastOne_getD vs k hk]; rfl

lemma atLeastOne_var (vs : List ℕ) (k : ℕ) (hk : k < vs.length) :
    litVar ((atLeastOne vs).lits.getD k default) = vs.getD k 0 := by
  rw [atLeastOne_getD vs k hk]; rfl

/-! ## The run-time-width leaf

Same shape as `leafProg`: write the clause, then bump the clause counter.  The
clause writer is the run-time-width primitive, which owns a second control cell
`iInner` for its own literal counter. -/

/-- The innermost body for a run-time-width `atLeastOne`: write the clause, then
    bump the enclosing loop's clause counter. -/
def leafAtLeastOneProg (wpJ iJ iInner : ℕ) (cntE varE : Expr) : Program :=
  .seq (writeAtLeastOneProg wpJ iInner cntE varE)
    (ctlAssign iJ (.add (ctlCell iJ) (.const 1)))

/-- Staging the inner counter into a store leaves the enclosing levels' pinned
    cells alone, since the pins are disjoint from it — the step that lets the
    caller's `hvar`, stated at a store where the pins hold, be applied at the
    per-iteration store the primitive reports values against. -/
lemma pinsHold_writeReg_inner (M iInner k : ℕ) (pins : List (ℕ × ℕ)) (τ : Store)
    (hF : PinsHold M pins τ)
    (hpin : ∀ p ∈ pins, p.1 ≠ iInner) :
    PinsHold M pins (writeReg τ (M + iInner) k) := by
  intro p hp
  rw [writeReg_diff τ (M + iInner) k (M + p.1) (by have := hpin p hp; omega)]
  exact hF p hp

/-- The run-time-width counterpart of `clauseLoopBody_leaf`.  The frame
    conditions `hcntE`/`hvarE` are stated against the freeze bound `M + Jmax + 1`
    — the first address above the control block — so an expression built from
    `ctlCell`s of the block satisfies them by reading only cells the bound
    covers.  Both exclude the write pointer `M + wpJ`; `hcntE` also excludes the
    inner counter `M + iInner`, which the count must not consult.

    `hcnt` and `hvar` then say what those expressions *mean*: the count is the
    clause's width, and the variable at inner counter `k` is the `k`-th entry of
    the clause's variable list. -/
lemma clauseLoopBody_atLeastOne (M Jmax wpJ iJ iInner : ℕ) (cntE varE : Expr)
    (pins : List (ℕ × ℕ)) (vs : ℕ → List ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax)
    (hiIn : 1 ≤ iInner) (hiInmax : iInner ≤ Jmax)
    (hne1 : iJ ≠ wpJ) (hne2 : iInner ≠ wpJ) (hne3 : iInner ≠ iJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ ∧ p.1 ≠ iInner)
    (hcnt : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      cntE.eval τ = (vs i).length)
    (hcntE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → r ≠ M + iInner → σ1 r = σ2 r) →
      cntE.eval σ1 = cntE.eval σ2)
    (hvarE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) → varE.eval σ1 = varE.eval σ2)
    (hvar : ∀ (τ : Store) (i k : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      τ (M + iInner) = k → k < (vs i).length → varE.eval τ = (vs i).getD k 0) :
    ClauseLoopBody (leafAtLeastOneProg wpJ iJ iInner cntE varE) M Jmax wpJ iJ
      (PinsHold M pins) (fun i => [atLeastOne (vs i)]) := by
  intro τ i wp hF h0 hi hw hsep
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    writeAtLeastOneProg_eval_state wpJ iInner cntE varE M (M + Jmax + 1) wp τ
      hwpJ hiIn (Ne.symm hne2) h0 hw (by omega) (by omega) (by omega) hcntE hvarE
  have hn : cntE.eval τ = (vs i).length := hcnt τ i hF h0 hi
  set σ2 := (writeAtLeastOneProg wpJ iInner cntE varE).eval τ with hσ2def
  have hσ2i : σ2 (M + iJ) = i := by rw [w6 (M + iJ) (by omega) (by omega) (Or.inl (by omega)), hi]
  set σ3 := (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1))).eval σ2 with hσ3def
  have hσ3eq : σ3 = writeReg σ2 (M + iJ) (i + 1) := by
    rw [hσ3def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, w5]
    congr 1
    simp [Expr.eval, ctlCell_eval, w5, hσ2i]
  have hgoal : (leafAtLeastOneProg wpJ iJ iInner cntE varE).eval τ = σ3 := by
    rw [hσ3def, hσ2def]; unfold leafAtLeastOneProg; rw [eval_seq]
  rw [hgoal]
  have hσ30 : σ3 0 = M := by
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) 0 (by omega), w5]
  have hwidth : rowTableWidth (rowW [atLeastOne (vs i)]) [atLeastOne (vs i)].length
      = 2 + 2 * (vs i).length := by
    rw [show [atLeastOne (vs i)].length = 1 from rfl, rowTableWidth_singleton, atLeastOne_length]
  have hvarval : ∀ k, k < (vs i).length →
      varE.eval (writeReg τ (M + iInner) k) = (vs i).getD k 0 := by
    intro k hk
    refine hvar (writeReg τ (M + iInner) k) i k
      (pinsHold_writeReg_inner M iInner k pins τ hF (fun p hp => (hpin p hp).2.2.2.2))
      ?_ ?_ ?_ hk
    · rw [writeReg_diff τ (M + iInner) k 0 (by omega)]; exact h0
    · rw [writeReg_diff τ (M + iInner) k (M + iJ) (by omega)]; exact hi
    · rw [writeReg_same]
  refine ⟨?_, hσ30, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨_, _, hpne, hpne2, hpne3⟩ := hpin p hp
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (M + p.1) (by omega),
      w6 (M + p.1) (by omega) (by omega) (Or.inl (by omega))]
    exact hF p hp
  · rw [hσ3eq, writeReg_same]
  · rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (M + wpJ) (by omega), w3, hn, hwidth]
    omega
  · refine rowsWritten_singleton σ3 wp (atLeastOne (vs i)) ?_ ?_ ?_
    · rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 1) (by omega), w1, hn,
        atLeastOne_length]
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 2 + 2 * k) (by omega),
        (w2 k (by omega)).1, atLeastOne_tag (vs i) k hk]
      rfl
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) (wp + 2 + 2 * k + 1) (by omega),
        (w2 k (by omega)).2, atLeastOne_var (vs i) k hk]
      exact hvarval k hk
  · intro r hr1 hr2
    have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
    rw [hσ3eq, writeReg_diff σ2 (M + iJ) (i + 1) r hrne,
      w6 r (by rcases hr2 with h | h <;> omega) (by rcases hr2 with h | h <;> omega)
        (Or.inl hr1)]

/-! ## The hypotheses are jointly satisfiable

A leaf combinator whose side conditions contradicted each other would prove
anything and refine nothing, and the conditions here relate five control indices,
two frame conditions and two meaning conditions — enough moving parts that their
consistency is worth exhibiting rather than assuming.  Instantiating them at a
one-literal clause discharges every one, so the conclusion above is reachable. -/

lemma clauseLoopBody_atLeastOne_nonvacuous :
    ∃ (M Jmax wpJ iJ iInner : ℕ) (cntE varE : Expr) (pins : List (ℕ × ℕ)) (vs : ℕ → List ℕ),
      vs = (fun _ => [7]) ∧
      ClauseLoopBody (leafAtLeastOneProg wpJ iJ iInner cntE varE) M Jmax wpJ iJ
        (PinsHold M pins) (fun i => [atLeastOne (vs i)]) := by
  refine ⟨5, 3, 1, 2, 3, .const 1, .const 7, [], fun _ => [7], rfl, ?_⟩
  refine clauseLoopBody_atLeastOne 5 3 1 2 3 (.const 1) (.const 7) [] (fun _ => [7])
    (le_refl 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
  · intro p hp; exact absurd hp List.not_mem_nil
  · intro τ i _ _ _; rfl
  · intro σ1 σ2 _ _ _; rfl
  · intro σ1 σ2 _ _ _; rfl
  · intro τ i k _ _ _ _ hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0; rfl

end NPComplete.CookLevin

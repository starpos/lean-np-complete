module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafPair
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafAtLeastOne
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq
public import NPComplete.CookLevin.Tableau.TableauRamLoops

/-!
The uniqueness family is `exactlyOne` applied three times per row: once over the
states, once over the head positions, once over each cell's letters.  Every one
of those calls is the same shape — a run-time-width `atLeastOne` clause followed
by the `atMostOneRange` double loop — so this file proves that shape once, as a
`ClauseWriter` parameterized by the pair of variable expressions
(`clauseWriter_exactlyOne_range`), and instantiates it three times rather than
repeating the argument.

The three instantiations share the same *pair* of control cells for their own
loop counters, at different nesting depths: the state and head calls at depth 1
(pinned only on `t`, using `lvJ1`/`lvJ2`), and the cell call at depth 2 (pinned
on `t` and `p`, using `lvJ2`/`lvJ3`).  Because `loopProg` resets its own counter
to `0` on entry, sequential reuse of the same cells across the state and head
calls needs no extra bookkeeping — the second call simply overwrites what the
first left behind. This keeps every level of the whole family inside the four
range counters `lvJ0`..`lvJ3` already budgeted by `ctlJmax`, with `litJ`/`tmpJ`
unused.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## `List.range`'s own `getD`

A family stated over `S.map (fun q => ...)` with `S = List.range n` reduces its
`k`-th entry to `k` itself once `k` is in range, which is what turns a family's
list-driven variable numbering into a plain arithmetic one. -/

lemma range_map_getD (n : ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i < n) :
    ((List.range n).map g).getD i 0 = g i := by
  have hlt : i < ((List.range n).map g).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]

lemma range_map_length (n : ℕ) (g : ℕ → ℕ) : ((List.range n).map g).length = n := by simp

/-! ## `exactlyOne` as an `atLeastOne` clause followed by `atMostOneRange`

`exactlyOne_eq_atLeastOne_cons` (in `ClauseLeafPair.lean`) already states this as
a `::`; restating it as `++` is what lets `clauseWriter_seq` combine the two
writers directly. -/

lemma exactlyOne_eq_atLeastOne_append (vs : List ℕ) :
    exactlyOne vs = [atLeastOne vs] ++ atMostOneRange vs := by
  rw [exactlyOne_eq_atLeastOne_cons]; rfl

/-! ## From a one-cell dependency to a bound-shaped one

`clauseWriter_atLeastOne` is stated against `writeAtLeastOneProg_eval_state`'s
own frame hypotheses, which are phrased as agreement below a bound rather than
agreement on the control block off the write pointer.  Every variable
expression this file uses is built from `ctlCell`s only, so it already satisfies
the *stronger* control-block condition; this lemma is the one-line bridge from
that condition to the bound-shaped one the primitive asks for. -/

lemma hdep_pins_to_bound (M Jmax wpJ : ℕ) (e : Expr)
    (hdep : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) → e.eval σ' = e.eval σ) :
    ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) → e.eval σ1 = e.eval σ2 := by
  intro σ1 σ2 h1 h2 hagree
  exact hdep σ2 σ1 h2 h1 (fun k hk1 hk2 hk3 => hagree (M + k) (by omega) (by omega))

/-! ## The run-time-width `atLeastOne` clause as a `ClauseWriter`

`clauseLoopBody_atLeastOne` bundles the write with a counter bump, for use
inside a range nest; a family's `atLeastOne` clause is a single row with no
enclosing loop of its own, so this is the counter-free half — `writeAtLeastOneProg`
run once, with its effect read off `writeAtLeastOneProg_eval_state`. -/

lemma clauseWriter_atLeastOne (M Jmax wpJ iInner : ℕ) (cntE varE : Expr)
    (pins : List (ℕ × ℕ)) (vs : List ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiIn : 1 ≤ iInner) (hiInmax : iInner ≤ Jmax) (hne : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ ∧ p.1 ≠ iInner)
    (hcnt : ∀ τ : Store, PinsHold M pins τ → τ 0 = M → cntE.eval τ = vs.length)
    (hcntE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → r ≠ M + iInner → σ1 r = σ2 r) →
      cntE.eval σ1 = cntE.eval σ2)
    (hvarE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) → varE.eval σ1 = varE.eval σ2)
    (hvar : ∀ (τ : Store) (k : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iInner) = k →
      k < vs.length → varE.eval τ = vs.getD k 0) :
    ClauseWriter (writeAtLeastOneProg wpJ iInner cntE varE) M Jmax wpJ (PinsHold M pins)
      [atLeastOne vs] := by
  intro τ wp hF h0 hw hsep
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    writeAtLeastOneProg_eval_state wpJ iInner cntE varE M (M + Jmax + 1) wp τ
      hwpJ hiIn (Ne.symm hne) h0 hw (by omega) (by omega) (by omega) hcntE hvarE
  have hn : cntE.eval τ = vs.length := hcnt τ hF h0
  set σ2 := (writeAtLeastOneProg wpJ iInner cntE varE).eval τ with hσ2def
  have hwidth : rowTableWidth (rowW [atLeastOne vs]) [atLeastOne vs].length
      = 2 + 2 * vs.length := by
    rw [show [atLeastOne vs].length = 1 from rfl, rowTableWidth_singleton, atLeastOne_length]
  have hvarval : ∀ k, k < vs.length →
      varE.eval (writeReg τ (M + iInner) k) = vs.getD k 0 := by
    intro k hk
    refine hvar (writeReg τ (M + iInner) k) k
      (pinsHold_writeReg_inner M iInner k pins τ hF (fun p hp => (hpin p hp).2.2.2))
      ?_ ?_ hk
    · rw [writeReg_diff τ (M + iInner) k 0 (by omega)]; exact h0
    · rw [writeReg_same]
  refine ⟨?_, w5, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨_, _, hpne, hpne2⟩ := hpin p hp
    rw [w6 (M + p.1) (by omega) (by omega) (Or.inl (by omega))]
    exact hF p hp
  · rw [w3, hn, hwidth]; omega
  · refine rowsWritten_singleton σ2 wp (atLeastOne vs) ?_ ?_ ?_
    · rw [w1, hn, atLeastOne_length]
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [(w2 k (by rw [hn]; exact hk)).1, atLeastOne_tag vs k hk]
      rfl
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [(w2 k (by rw [hn]; exact hk)).2, atLeastOne_var vs k hk]
      exact hvarval k hk
  · intro r hr1 hr2
    refine w6 r ?_ ?_ (Or.inl hr1)
    · rcases hr2 with h | h <;> omega
    · rcases hr2 with h | h <;> omega

/-! ## The `atMostOneRange` all-pairs family as a `ClauseWriter`

Restating `atMostOneRange` at a `range`-indexed value function (rather than an
arbitrary list) is what lets the two loop counters read `vals` directly off
their own control cells, mirroring `persist_range_split`'s treatment of the
persistence family's excluded index. -/

lemma atMostOneRange_range_map_flatMap (len : ℕ) (vals : ℕ → ℕ) :
    atMostOneRange ((List.range len).map vals)
      = (List.range len).flatMap fun i =>
          (List.range (len - i - 1)).flatMap fun j => [negPair (vals i) (vals (i + 1 + j))] := by
  rw [atMostOneRange_eq_negPair, range_map_length]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < len := List.mem_range.mp hi
  rw [map_eq_flatMap_singleton]
  apply List.flatMap_congr
  intro j hj
  have hj' : j < len - i - 1 := List.mem_range.mp hj
  rw [range_map_getD len vals i hi', range_map_getD len vals (i + 1 + j) (by omega)]

/-- The inner loop, for one fixed outer index `i`: `negPair` clauses for every
`j < len - i - 1`. -/
lemma clauseWriter_atMostOneRange_inner
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (baseE shiftE : Expr) (len i : ℕ) (av bv : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      baseE.eval σ' = baseE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalB : ∀ (τ : Store), PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      baseE.eval τ = av i)
    (hvalS : ∀ (τ : Store) (j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = bv j) :
    ClauseWriter (loopProg iInner (.sub (.sub (.const len) (ctlCell iOuter)) (.const 1))
        (leafProg wpJ iInner (negPairLits baseE shiftE)))
      M Jmax wpJ (PinsHold M ((iOuter, i) :: pins))
      ((List.range (len - i - 1)).flatMap fun j => [negPair (av i) (bv j)]) := by
  have hpin' : ∀ p ∈ (iOuter, i) :: pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨hiOuter, hiOutermax, Ne.symm hneOI, hneOw⟩
    · exact ⟨(hpin p hp').1, (hpin p hp').2.1, (hpin p hp').2.2.2.1, (hpin p hp').2.2.2.2⟩
  have hleaf : ClauseLoopBody (leafProg wpJ iInner (negPairLits baseE shiftE)) M Jmax wpJ iInner
      (PinsHold M ((iOuter, i) :: pins)) (fun j => [negPair (av i) (bv j)]) :=
    clauseLoopBody_negPair M Jmax wpJ iInner baseE shiftE ((iOuter, i) :: pins)
      (fun _ => av i) bv
      hwpJ hwpJmax hiInner hiInnermax hneIw hpin' hdepB hdepS
      (fun τ _ hF h0 _ => hvalB τ hF h0)
      (fun τ j hF h0 hj => hvalS τ j hF h0 hj)
  refine clauseWriter_forN _ M Jmax wpJ iInner ((iOuter, i) :: pins) _
    (.sub (.sub (.const len) (ctlCell iOuter)) (.const 1)) (len - i - 1)
    hiInner hiInnermax hneIw hpin' hleaf ?_
  intro τ h0 hF hz
  simp only [Expr.eval]
  rw [ctlCell_eval, h0, hF (iOuter, i) (by simp)]

/-- The `atMostOneRange` family, over `(List.range len).map vals`, as a whole
`ClauseWriter`: an outer loop over `i` of trip count `len`, running
`clauseWriter_atMostOneRange_inner`'s shrinking inner loop at every iteration. -/
lemma clauseWriter_atMostOneRange
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (baseE shiftE : Expr) (len : ℕ) (vals : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      baseE.eval σ' = baseE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalB : ∀ (τ : Store) (i : ℕ), PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      baseE.eval τ = vals i)
    (hvalS : ∀ (τ : Store) (i j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = vals (i + 1 + j)) :
    ClauseWriter (loopProg iOuter (.const len)
        (.seq (loopProg iInner (.sub (.sub (.const len) (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits baseE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1)))))
      M Jmax wpJ (PinsHold M pins)
      (atMostOneRange ((List.range len).map vals)) := by
  rw [atMostOneRange_range_map_flatMap]
  have hpinOuter : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ wpJ :=
    fun p hp => ⟨(hpin p hp).1, (hpin p hp).2.1, (hpin p hp).2.2.1, (hpin p hp).2.2.2.2⟩
  refine clauseWriter_forN _ M Jmax wpJ iOuter pins _ (.const len) len
    hiOuter hiOutermax hneOw hpinOuter ?_ (fun _ _ _ _ => rfl)
  refine clauseLoopBody_of_writer _ M Jmax wpJ iOuter pins _
    hiOuter hiOutermax hneOw hpinOuter (fun i => ?_)
  exact clauseWriter_atMostOneRange_inner M Jmax wpJ iOuter iInner pins baseE shiftE len i
    vals (fun j => vals (i + 1 + j))
    hwpJ hwpJmax hiOuter hiOutermax hiInner hiInnermax hneOI hneOw hneIw hpin
    hdepB hdepS (hvalB · i) (hvalS · i)

/-! ## One `exactlyOne` block, as a reusable `ClauseWriter`

The generic combinator every `exactlyOne` call in the uniqueness family
specializes: a single index expression plays double duty as the `atLeastOne`
variable reader and as the `atMostOneRange` base reader, since both name the
same value at the same iteration. -/

/-- One `exactlyOne` clause block over `(List.range len).map vals`: the
run-time-width `atLeastOne` clause (sharing `iOuter` as its own loop counter)
followed by the `atMostOneRange` double loop over `iOuter`/`iInner`. -/
lemma clauseWriter_exactlyOne_range
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (indexE shiftE : Expr) (len : ℕ) (vals : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hdepI : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      indexE.eval σ' = indexE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalI : ∀ (τ : Store) (i : ℕ), PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      indexE.eval τ = vals i)
    (hvalS : ∀ (τ : Store) (i j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = vals (i + 1 + j)) :
    ClauseWriter (.seq (writeAtLeastOneProg wpJ iOuter (.const len) indexE)
        (loopProg iOuter (.const len)
        (.seq (loopProg iInner (.sub (.sub (.const len) (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits indexE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1))))))
      M Jmax wpJ (PinsHold M pins) (exactlyOne ((List.range len).map vals)) := by
  rw [exactlyOne_eq_atLeastOne_append]
  have hpin1 : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ ∧ p.1 ≠ iOuter :=
    fun p hp => ⟨(hpin p hp).1, (hpin p hp).2.1, (hpin p hp).2.2.2.2, (hpin p hp).2.2.1⟩
  refine clauseWriter_seq _ _ M Jmax wpJ (PinsHold M pins) _ _ ?_ ?_
  · refine clauseWriter_atLeastOne M Jmax wpJ iOuter (.const len) indexE pins
      ((List.range len).map vals) hwpJ hwpJmax hiOuter hiOutermax hneOw hpin1
      (fun τ _ _ => by simp [Expr.eval]) (fun σ1 σ2 _ _ _ => rfl)
      (hdep_pins_to_bound M Jmax wpJ indexE hdepI) ?_
    intro τ k hF h0 hk hklt
    rw [range_map_length] at hklt
    rw [range_map_getD len vals k hklt]
    exact hvalI τ k (pinsHold_cons M (iOuter, k) pins τ hk hF) h0
  · exact clauseWriter_atMostOneRange M Jmax wpJ iOuter iInner pins indexE shiftE len vals
      hwpJ hwpJmax hiOuter hiOutermax hiInner hiInnermax hneOI hneOw hneIw hpin hdepI hdepS
      hvalI hvalS

/-! ## Variable expressions

The three numbers a uniqueness clause needs, each in two forms: the "base" form
`vals i` that both the `atLeastOne` reader and the `atMostOneRange` outer index
read, and the "shift" form `vals (i + 1 + j)` the `atMostOneRange` inner index
reads. -/

/-- `state t i`, base form: `i` is the level's own counter. -/
def uniqStateBaseE (n W m : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- `state t (i + 1 + j)`, shift form. -/
def uniqStateShiftE (n W m : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2))

/-- `head t i`, base form. -/
def uniqHeadBaseE (n W m : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- `head t (i + 1 + j)`, shift form. -/
def uniqHeadShiftE (n W m : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2))

/-- `cell t p i`, base form (the third counter is the level's own). -/
def uniqCellBaseE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ2)

/-- `cell t p (i + 1 + j)`, shift form. -/
def uniqCellShiftE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)
    (.add (.add (ctlCell lvJ2) (.const 1)) (ctlCell lvJ3))

/-! ### Frame and value obligations

Each expression owes the two facts `clauseWriter_exactlyOne_range` asks for.
They follow by rewriting the dense-expression evaluation, replacing each
`ctlCell` read, and closing by `simp`. -/

lemma uniqStateBaseE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqStateBaseE n W m).eval σ' = (uniqStateBaseE n W m).eval σ := by
  unfold uniqStateBaseE
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)

lemma uniqStateBaseE_value (M n W m t i : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins2 t i) τ) (h0 : τ 0 = M) :
    (uniqStateBaseE n W m).eval τ = (denseLayout n W m).state t i := by
  unfold uniqStateBaseE
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m t i rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ0 t τ (by simp [ctlPins2]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ1 i τ (by simp [ctlPins2]) hF h0)

lemma uniqStateShiftE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqStateShiftE n W m).eval σ' = (uniqStateShiftE n W m).eval σ := by
  unfold uniqStateShiftE
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
      (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))

lemma uniqStateShiftE_value (M n W m t i j : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins2 t i) τ) (h0 : τ 0 = M) (hj : τ (M + lvJ2) = j) :
    (uniqStateShiftE n W m).eval τ = (denseLayout n W m).state t (i + 1 + j) := by
  unfold uniqStateShiftE
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m t (i + 1 + j) rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ0 t τ (by simp [ctlPins2]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ1 i τ (by simp [ctlPins2]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

lemma uniqHeadBaseE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqHeadBaseE n W m).eval σ' = (uniqHeadBaseE n W m).eval σ := by
  unfold uniqHeadBaseE
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)

lemma uniqHeadBaseE_value (M n W m t i : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins2 t i) τ) (h0 : τ 0 = M) :
    (uniqHeadBaseE n W m).eval τ = (denseLayout n W m).head t i := by
  unfold uniqHeadBaseE
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t i rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ0 t τ (by simp [ctlPins2]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ1 i τ (by simp [ctlPins2]) hF h0)

lemma uniqHeadShiftE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqHeadShiftE n W m).eval σ' = (uniqHeadShiftE n W m).eval σ := by
  unfold uniqHeadShiftE
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
      (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))

lemma uniqHeadShiftE_value (M n W m t i j : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins2 t i) τ) (h0 : τ 0 = M) (hj : τ (M + lvJ2) = j) :
    (uniqHeadShiftE n W m).eval τ = (denseLayout n W m).head t (i + 1 + j) := by
  unfold uniqHeadShiftE
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t (i + 1 + j) rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ0 t τ (by simp [ctlPins2]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M (ctlPins2 t i) lvJ1 i τ (by simp [ctlPins2]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

lemma uniqCellBaseE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqCellBaseE n W m).eval σ' = (uniqCellBaseE n W m).eval σ := by
  unfold uniqCellBaseE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)

lemma uniqCellBaseE_value (M n W m t p i : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p i) τ) (h0 : τ 0 = M) :
    (uniqCellBaseE n W m).eval τ = (denseLayout n W m).cell t p i := by
  unfold uniqCellBaseE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p i rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ1 p τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ2 i τ (by simp [ctlPins3]) hF h0)

lemma uniqCellShiftE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqCellShiftE n W m).eval σ' = (uniqCellShiftE n W m).eval σ := by
  unfold uniqCellShiftE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)
      (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree))

lemma uniqCellShiftE_value (M n W m t p i j : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p i) τ) (h0 : τ 0 = M) (hj : τ (M + lvJ3) = j) :
    (uniqCellShiftE n W m).eval τ = (denseLayout n W m).cell t p (i + 1 + j) := by
  unfold uniqCellShiftE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p (i + 1 + j) rfl rfl rfl
    (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ1 p τ (by simp [ctlPins3]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M (ctlPins3 t p i) lvJ2 i τ (by simp [ctlPins3]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

/-! ## The three `exactlyOne` calls, at one fixed row

Each call is `clauseWriter_exactlyOne_range` instantiated at one pair of
expressions; the state and head calls share `lvJ1`/`lvJ2` (safe, since
`loopProg` resets its own counter on entry), and the cell call — one nesting
level deeper, under a fixed `p` — uses `lvJ2`/`lvJ3`. -/

/-- `exactlyOne` over the head positions at one fixed `t`. -/
lemma uniq_head_writer (M n W m t : ℕ) :
    ClauseWriter (.seq (writeAtLeastOneProg wpJ lvJ1 (.const W) (uniqHeadBaseE n W m))
        (loopProg lvJ1 (.const W)
        (.seq (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2 (negPairLits (uniqHeadBaseE n W m) (uniqHeadShiftE n W m))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      (exactlyOne ((List.range W).map fun p => (denseLayout n W m).head t p)) := by
  have hpin1 : ∀ p ∈ ctlPins1 t,
      1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ lvJ2 ∧ p.1 ≠ wpJ := by
    intro p hp
    simp only [ctlPins1, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega,
      by unfold lvJ0 lvJ1; omega, by unfold lvJ0 lvJ2; omega, by unfold lvJ0 wpJ; omega⟩
  refine clauseWriter_exactlyOne_range M ctlJmax wpJ lvJ1 lvJ2 (ctlPins1 t)
    (uniqHeadBaseE n W m) (uniqHeadShiftE n W m) W
    (fun p => (denseLayout n W m).head t p)
    (by unfold wpJ; omega) (by unfold wpJ ctlJmax; omega)
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega)
    (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega) (by unfold lvJ2 wpJ; omega)
    hpin1
    (fun σ σ' hσ hσ' hagree => uniqHeadBaseE_frame M n W m σ σ' hσ hσ' hagree)
    (fun σ σ' hσ hσ' hagree => uniqHeadShiftE_frame M n W m σ σ' hσ hσ' hagree)
    (fun τ i hF h0 => uniqHeadBaseE_value M n W m t i τ hF h0)
    (fun τ i j hF h0 hj => uniqHeadShiftE_value M n W m t i j τ hF h0 hj)

/-! ## Layout-stride/count-separated writers -/

/-- `exactlyOne` over a state count independent of the dense-layout stride. -/
lemma uniq_state_writer_gen (M nS W mS nC t : ℕ) :
    ClauseWriter (.seq (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseE nS W mS))
        (loopProg lvJ1 (.const nC)
        (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqStateBaseE nS W mS) (uniqStateShiftE nS W mS))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)) := by
  have hpin1 : ∀ p ∈ ctlPins1 t,
      1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ lvJ2 ∧ p.1 ≠ wpJ := by
    intro p hp
    simp only [ctlPins1, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega,
      by unfold lvJ0 lvJ1; omega, by unfold lvJ0 lvJ2; omega, by unfold lvJ0 wpJ; omega⟩
  refine clauseWriter_exactlyOne_range M ctlJmax wpJ lvJ1 lvJ2 (ctlPins1 t)
    (uniqStateBaseE nS W mS) (uniqStateShiftE nS W mS) nC
    (fun q => (denseLayout nS W mS).state t q)
    (by unfold wpJ; omega) (by unfold wpJ ctlJmax; omega)
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega)
    (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega) (by unfold lvJ2 wpJ; omega)
    hpin1
    (fun σ σ' hσ hσ' hagree => uniqStateBaseE_frame M nS W mS σ σ' hσ hσ' hagree)
    (fun σ σ' hσ hσ' hagree => uniqStateShiftE_frame M nS W mS σ σ' hσ hσ' hagree)
    (fun τ i hF h0 => uniqStateBaseE_value M nS W mS t i τ hF h0)
    (fun τ i j hF h0 hj => uniqStateShiftE_value M nS W mS t i j τ hF h0 hj)

/-- `exactlyOne` over a letter count independent of the dense-layout stride. -/
lemma uniq_cell_writer_gen (M nS W mS mC t p : ℕ) :
    ClauseWriter (.seq (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseE nS W mS))
        (loopProg lvJ2 (.const mC)
        (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
            (leafProg wpJ lvJ3
              (negPairLits (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
      M ctlJmax wpJ (PinsHold M (ctlPins2 t p))
      (exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) := by
  have hpin2 : ∀ q ∈ ctlPins2 t p,
      1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ lvJ2 ∧ q.1 ≠ lvJ3 ∧ q.1 ≠ wpJ := by
    intro q hq
    simp only [ctlPins2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨by unfold lvJ1; omega, by unfold lvJ1 ctlJmax; omega,
        by unfold lvJ1 lvJ2; omega, by unfold lvJ1 lvJ3; omega, by unfold lvJ1 wpJ; omega⟩
    · exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega,
        by unfold lvJ0 lvJ2; omega, by unfold lvJ0 lvJ3; omega, by unfold lvJ0 wpJ; omega⟩
  refine clauseWriter_exactlyOne_range M ctlJmax wpJ lvJ2 lvJ3 (ctlPins2 t p)
    (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS) mC
    (fun a => (denseLayout nS W mS).cell t p a)
    (by unfold wpJ; omega) (by unfold wpJ ctlJmax; omega)
    (by unfold lvJ2; omega) (by unfold lvJ2 ctlJmax; omega)
    (by unfold lvJ3; omega) (by unfold lvJ3 ctlJmax; omega)
    (by unfold lvJ2 lvJ3; omega) (by unfold lvJ2 wpJ; omega) (by unfold lvJ3 wpJ; omega)
    hpin2
    (fun σ σ' hσ hσ' hagree => uniqCellBaseE_frame M nS W mS σ σ' hσ hσ' hagree)
    (fun σ σ' hσ hσ' hagree => uniqCellShiftE_frame M nS W mS σ σ' hσ hσ' hagree)
    (fun τ i hF h0 => uniqCellBaseE_value M nS W mS t p i τ hF h0)
    (fun τ i j hF h0 hj => uniqCellShiftE_value M nS W mS t p i j τ hF h0 hj)

/-- The cell-position loop with an independent letter count. -/
lemma uniq_cell_p_loop_writer_gen (M nS W mS mC t : ℕ) :
    ClauseWriter (loopProg lvJ1 (.const W)
        (.seq (.seq (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseE nS W mS))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      ((List.range W).flatMap fun p =>
        exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) := by
  have hpin1 : ∀ p ∈ ctlPins1 t, 1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ wpJ := by
    intro p hp
    simp only [ctlPins1, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega,
      by unfold lvJ0 lvJ1; omega, by unfold lvJ0 wpJ; omega⟩
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ1 (ctlPins1 t) _ (.const W) W
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ1 wpJ; omega)
    hpin1 ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ1 (ctlPins1 t) _
    (by unfold lvJ1; omega) (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ1 wpJ; omega)
    hpin1 (fun p => uniq_cell_writer_gen M nS W mS mC t p)

/-- The uniqueness row with independent state and letter counts. -/
lemma uniq_t_fixed_writer_gen (M nS W mS nC mC t : ℕ) :
    ClauseWriter (.seq (.seq
        (.seq (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseE nS W mS))
          (loopProg lvJ1 (.const nC)
          (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqStateBaseE nS W mS) (uniqStateShiftE nS W mS))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
        (.seq (writeAtLeastOneProg wpJ lvJ1 (.const W) (uniqHeadBaseE nS W mS))
          (loopProg lvJ1 (.const W)
          (.seq (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqHeadBaseE nS W mS) (uniqHeadShiftE nS W mS))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
        (loopProg lvJ1 (.const W)
        (.seq (.seq (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseE nS W mS))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M ctlJmax wpJ (PinsHold M (ctlPins1 t))
      (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
        ++ exactlyOne ((List.range W).map fun p => (denseLayout nS W mS).head t p)
        ++ (List.range W).flatMap fun p =>
          exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) :=
  clauseWriter_seq _ _ M ctlJmax wpJ (PinsHold M (ctlPins1 t)) _ _
    (clauseWriter_seq _ _ M ctlJmax wpJ (PinsHold M (ctlPins1 t)) _ _
      (uniq_state_writer_gen M nS W mS nC t) (uniq_head_writer M nS W mS t))
    (uniq_cell_p_loop_writer_gen M nS W mS mC t)

/-- The uniqueness program with independent layout strides and iteration counts. -/
def uniquenessFamilyProgGen (nS W mS nC mC T : ℕ) : Program :=
  loopProg lvJ0 (.const (T + 1))
    (.seq (.seq (.seq
      (.seq (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseE nS W mS))
        (loopProg lvJ1 (.const nC)
          (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqStateBaseE nS W mS) (uniqStateShiftE nS W mS))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      (.seq (writeAtLeastOneProg wpJ lvJ1 (.const W) (uniqHeadBaseE nS W mS))
        (loopProg lvJ1 (.const W)
          (.seq (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqHeadBaseE nS W mS) (uniqHeadShiftE nS W mS))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
      (loopProg lvJ1 (.const W)
        (.seq (.seq (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseE nS W mS))
          (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
              (leafProg wpJ lvJ3
                (negPairLits (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

/-- The uniqueness family's program, as in `uniquenessFamilyProg_writer`. -/
def uniquenessFamilyProg (n W m T : ℕ) : Program :=
  uniquenessFamilyProgGen n W m n m T

/-- The full uniqueness family with independent layout strides and iteration counts. -/
lemma uniquenessFamilyProgGen_writer_gen (M nS W mS nC mC T : ℕ) :
    ClauseWriter (loopProg lvJ0 (.const (T + 1))
        (.seq (.seq (.seq
            (.seq (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseE nS W mS))
              (loopProg lvJ1 (.const nC)
              (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
                  (leafProg wpJ lvJ2
                    (negPairLits (uniqStateBaseE nS W mS) (uniqStateShiftE nS W mS))))
                (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
            (.seq (writeAtLeastOneProg wpJ lvJ1 (.const W) (uniqHeadBaseE nS W mS))
              (loopProg lvJ1 (.const W)
              (.seq (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
                  (leafProg wpJ lvJ2
                    (negPairLits (uniqHeadBaseE nS W mS) (uniqHeadShiftE nS W mS))))
                (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
            (loopProg lvJ1 (.const W)
            (.seq (.seq (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseE nS W mS))
                (loopProg lvJ2 (.const mC)
                (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                    (leafProg wpJ lvJ3
                      (negPairLits (uniqCellBaseE nS W mS) (uniqCellShiftE nS W mS))))
                  (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
              (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M ctlJmax wpJ (PinsHold M ctlPins0)
      (execUniquenessClausesAt (denseLayout nS W mS)
        (List.range nC) (List.range mC) W T) := by
  refine clauseWriter_forN _ M ctlJmax wpJ lvJ0 ctlPins0 _ (.const (T + 1)) (T + 1)
    (by unfold lvJ0; omega) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega)
    (ctlPins0_ok lvJ0)
    ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer _ M ctlJmax wpJ lvJ0 ctlPins0 _
    (by unfold lvJ0; omega) (by unfold lvJ0 ctlJmax; omega) (by unfold lvJ0 wpJ; omega)
    (ctlPins0_ok lvJ0)
    (fun t => uniq_t_fixed_writer_gen M nS W mS nC mC t)

/-! ## The `t` loop, closing the whole family -/

/-- The full uniqueness family, as a `ClauseWriter`.  Its clause list is
`execUniquenessClausesAt (denseLayout n W m) (List.range n) (List.range m) W T`
by `rfl`, so the right-hand side is exactly the family's own definition, with
`S`/`A` specialized to `List.range n`/`List.range m` as `descUniquenessClauses`
does. -/
lemma uniquenessFamilyProg_writer (M n W m T : ℕ) :
    ClauseWriter (loopProg lvJ0 (.const (T + 1))
        (.seq (.seq (.seq
            (.seq (writeAtLeastOneProg wpJ lvJ1 (.const n) (uniqStateBaseE n W m))
              (loopProg lvJ1 (.const n)
              (.seq (loopProg lvJ2 (.sub (.sub (.const n) (ctlCell lvJ1)) (.const 1))
                  (leafProg wpJ lvJ2
                    (negPairLits (uniqStateBaseE n W m) (uniqStateShiftE n W m))))
                (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
            (.seq (writeAtLeastOneProg wpJ lvJ1 (.const W) (uniqHeadBaseE n W m))
              (loopProg lvJ1 (.const W)
              (.seq (loopProg lvJ2 (.sub (.sub (.const W) (ctlCell lvJ1)) (.const 1))
                  (leafProg wpJ lvJ2
                    (negPairLits (uniqHeadBaseE n W m) (uniqHeadShiftE n W m))))
                (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
            (loopProg lvJ1 (.const W)
            (.seq (.seq (writeAtLeastOneProg wpJ lvJ2 (.const m) (uniqCellBaseE n W m))
                (loopProg lvJ2 (.const m)
                (.seq (loopProg lvJ3 (.sub (.sub (.const m) (ctlCell lvJ2)) (.const 1))
                    (leafProg wpJ lvJ3
                      (negPairLits (uniqCellBaseE n W m) (uniqCellShiftE n W m))))
                  (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
              (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M ctlJmax wpJ (PinsHold M ctlPins0)
      (execUniquenessClausesAt (denseLayout n W m) (List.range n) (List.range m) W T) :=
  uniquenessFamilyProgGen_writer_gen M n W m n m T

/-! ## Run-time width and time parameters -/

/-- Placement requirements for the run-time width and time cells. -/
structure UniquenessParamPlacement (Jmax wReg tReg : ℕ) : Prop where
  ctl_le : ctlJmax ≤ Jmax
  w_min : 15 ≤ wReg
  w_le : wReg ≤ Jmax
  t_min : 15 ≤ tReg
  t_le : tReg ≤ Jmax
  regs_ne : wReg ≠ tReg

/-- The uniqueness width parameter cell. -/
def uniquenessWReg : ℕ := 15

/-- The uniqueness time parameter cell. -/
def uniquenessTReg : ℕ := 16

/-- The control extent containing the uniqueness parameter cells. -/
def uniquenessParamJmax : ℕ := 16

lemma uniqueness_param_fixed_placement :
    UniquenessParamPlacement uniquenessParamJmax uniquenessWReg uniquenessTReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [uniquenessParamJmax, uniquenessWReg, uniquenessTReg, ctlJmax]

lemma uniqueness_param_placement_satisfiable :
    ∃ Jmax wReg tReg, UniquenessParamPlacement Jmax wReg tReg :=
  ⟨uniquenessParamJmax, uniquenessWReg, uniquenessTReg,
    uniqueness_param_fixed_placement⟩

/-- Run-time parameters at the outermost uniqueness level. -/
def uniquenessParamPins0 (wReg tReg W T : ℕ) : List (ℕ × ℕ) :=
  [(wReg, W), (tReg, T)]

/-- Run-time parameters together with the time counter. -/
def uniquenessParamPins1 (wReg tReg W T t : ℕ) : List (ℕ × ℕ) :=
  (lvJ0, t) :: uniquenessParamPins0 wReg tReg W T

/-- Run-time parameters together with the first two counters. -/
def uniquenessParamPins2 (wReg tReg W T t i : ℕ) : List (ℕ × ℕ) :=
  (lvJ1, i) :: uniquenessParamPins1 wReg tReg W T t

/-- Run-time parameters together with the first three counters. -/
def uniquenessParamPins3 (wReg tReg W T t i j : ℕ) : List (ℕ × ℕ) :=
  (lvJ2, j) :: uniquenessParamPins2 wReg tReg W T t i

lemma uniqueness_param_pins0_ok (Jmax wReg tReg W T iJ : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax) :
    ∀ p ∈ uniquenessParamPins0 wReg tReg W T,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  simp only [uniquenessParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by have := hplace.w_min; omega, hplace.w_le,
      by have hw := hplace.w_min; unfold ctlJmax at hiJctl; omega,
      by have := hplace.w_min; unfold wpJ; omega⟩
  · exact ⟨by have := hplace.t_min; omega, hplace.t_le,
      by have ht := hplace.t_min; unfold ctlJmax at hiJctl; omega,
      by have := hplace.t_min; unfold wpJ; omega⟩

lemma uniqueness_param_pins1_ok (Jmax wReg tReg W T t iJ : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) :
    ∀ p ∈ uniquenessParamPins1 wReg tReg W T t,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by unfold lvJ0; omega,
      Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le, h0,
      by unfold lvJ0 wpJ; omega⟩
  · exact uniqueness_param_pins0_ok Jmax wReg tReg W T iJ hplace hiJctl p hp

lemma uniqueness_param_pins2_ok (Jmax wReg tReg W T t i iJ : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (hiJctl : iJ ≤ ctlJmax)
    (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) :
    ∀ p ∈ uniquenessParamPins2 wReg tReg W T t i,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by unfold lvJ1; omega,
      Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le, h1,
      by unfold lvJ1 wpJ; omega⟩
  · exact uniqueness_param_pins1_ok Jmax wReg tReg W T t iJ hplace hiJctl h0 p hp

/-- `state t i` with the dense-layout width read from a parameter cell. -/
def uniqStateBaseEParam (n m wReg : ℕ) : Expr :=
  denseStateE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- Shifted state expression with a run-time dense-layout width. -/
def uniqStateShiftEParam (n m wReg : ℕ) : Expr :=
  denseStateE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2))

/-- `head t i` with the dense-layout width read from a parameter cell. -/
def uniqHeadBaseEParam (n m wReg : ℕ) : Expr :=
  denseHeadE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- Shifted head expression with a run-time dense-layout width. -/
def uniqHeadShiftEParam (n m wReg : ℕ) : Expr :=
  denseHeadE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0)
    (.add (.add (ctlCell lvJ1) (.const 1)) (ctlCell lvJ2))

/-- `cell t p i` with the dense-layout width read from a parameter cell. -/
def uniqCellBaseEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m)
    (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ2)

/-- Shifted cell expression with a run-time dense-layout width. -/
def uniqCellShiftEParam (n m wReg : ℕ) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)
    (.add (.add (ctlCell lvJ2) (.const 1)) (ctlCell lvJ3))

lemma uniqueness_param_ctl_frame (M Jmax wReg tReg j : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (hj : j = lvJ0 ∨ j = lvJ1 ∨ j = lvJ2 ∨ j = lvJ3)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  exact ctlCell_frame_lv M j hj σ σ' hσ hσ'
    (fun k hk1 hk2 hkw => hagree k hk1 (Nat.le_trans hk2 hplace.ctl_le) hkw)

lemma uniqueness_param_width_frame (M Jmax wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell wReg).eval σ' = (ctlCell wReg).eval σ := by
  exact ctlCell_frame M Jmax wReg (by have := hplace.w_min; omega) hplace.w_le
    (by have := hplace.w_min; unfold wpJ; omega)
    σ σ' hσ hσ' hagree

lemma uniqueness_param_state_base_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqStateBaseEParam n m wReg).eval σ' = (uniqStateBaseEParam n m wReg).eval σ := by
  unfold uniqStateBaseEParam
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)

lemma uniqueness_param_state_shift_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqStateShiftEParam n m wReg).eval σ' = (uniqStateShiftEParam n m wReg).eval σ := by
  unfold uniqStateShiftEParam
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
        σ σ' hσ hσ' hagree)
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ2 hplace
        (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))

lemma uniqueness_param_head_base_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqHeadBaseEParam n m wReg).eval σ' = (uniqHeadBaseEParam n m wReg).eval σ := by
  unfold uniqHeadBaseEParam
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)

lemma uniqueness_param_head_shift_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqHeadShiftEParam n m wReg).eval σ' = (uniqHeadShiftEParam n m wReg).eval σ := by
  unfold uniqHeadShiftEParam
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
        σ σ' hσ hσ' hagree)
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ2 hplace
        (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree))

lemma uniqueness_param_cell_base_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqCellBaseEParam n m wReg).eval σ' = (uniqCellBaseEParam n m wReg).eval σ := by
  unfold uniqCellBaseEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ2 hplace
      (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)

lemma uniqueness_param_cell_shift_frame (M Jmax n m wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (uniqCellShiftEParam n m wReg).eval σ' = (uniqCellShiftEParam n m wReg).eval σ := by
  unfold uniqCellShiftEParam
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl
    (uniqueness_param_width_frame M Jmax wReg tReg hplace σ σ' hσ hσ' hagree) rfl
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ0 hplace (Or.inl rfl)
      σ σ' hσ hσ' hagree)
    (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ1 hplace (Or.inr (Or.inl rfl))
      σ σ' hσ hσ' hagree)
    (expr_add_one_add_eval_congr _ _ σ σ'
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ2 hplace
        (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)
      (uniqueness_param_ctl_frame M Jmax wReg tReg lvJ3 hplace
        (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree))

lemma uniqueness_param_state_base_value (M n W m T wReg tReg t i : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins2 wReg tReg W T t i) τ) (h0 : τ 0 = M) :
    (uniqStateBaseEParam n m wReg).eval τ = (denseLayout n W m).state t i := by
  unfold uniqStateBaseEParam
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m t i rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 i τ (by simp [uniquenessParamPins2]) hF h0)

lemma uniqueness_param_state_shift_value (M n W m T wReg tReg t i j : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins2 wReg tReg W T t i) τ)
    (h0 : τ 0 = M) (hj : τ (M + lvJ2) = j) :
    (uniqStateShiftEParam n m wReg).eval τ = (denseLayout n W m).state t (i + 1 + j) := by
  unfold uniqStateShiftEParam
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m t (i + 1 + j) rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M _ lvJ1 i τ (by simp [uniquenessParamPins2]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

lemma uniqueness_param_head_base_value (M n W m T wReg tReg t i : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins2 wReg tReg W T t i) τ) (h0 : τ 0 = M) :
    (uniqHeadBaseEParam n m wReg).eval τ = (denseLayout n W m).head t i := by
  unfold uniqHeadBaseEParam
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t i rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 i τ (by simp [uniquenessParamPins2]) hF h0)

lemma uniqueness_param_head_shift_value (M n W m T wReg tReg t i j : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins2 wReg tReg W T t i) τ)
    (h0 : τ 0 = M) (hj : τ (M + lvJ2) = j) :
    (uniqHeadShiftEParam n m wReg).eval τ = (denseLayout n W m).head t (i + 1 + j) := by
  unfold uniqHeadShiftEParam
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t (i + 1 + j) rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins2,
      uniquenessParamPins1]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M _ lvJ1 i τ (by simp [uniquenessParamPins2]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

lemma uniqueness_param_cell_base_value (M n W m T wReg tReg t p i : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins3 wReg tReg W T t p i) τ) (h0 : τ 0 = M) :
    (uniqCellBaseEParam n m wReg).eval τ = (denseLayout n W m).cell t p i := by
  unfold uniqCellBaseEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p i rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2, uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2, uniquenessParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ2 i τ (by simp [uniquenessParamPins3]) hF h0)

lemma uniqueness_param_cell_shift_value (M n W m T wReg tReg t p i j : ℕ) (τ : Store)
    (hF : PinsHold M (uniquenessParamPins3 wReg tReg W T t p i) τ)
    (h0 : τ 0 = M) (hj : τ (M + lvJ3) = j) :
    (uniqCellShiftEParam n m wReg).eval τ =
      (denseLayout n W m).cell t p (i + 1 + j) := by
  unfold uniqCellShiftEParam
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p (i + 1 + j) rfl
    (ctlCell_eval_of_pin M _ wReg W τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2, uniquenessParamPins1, uniquenessParamPins0]) hF h0) rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2, uniquenessParamPins1]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [uniquenessParamPins3,
      uniquenessParamPins2]) hF h0)
    (expr_add_one_add_eval _ _ τ i j
      (ctlCell_eval_of_pin M _ lvJ2 i τ (by simp [uniquenessParamPins3]) hF h0)
      (by rw [ctlCell_eval, h0]; exact hj))

/-! ### Run-time-count `exactlyOne` combinators -/

lemma clause_writer_at_most_one_range_inner_count
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (cntE baseE shiftE : Expr) (len i : ℕ) (av bv : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hcnt : ∀ τ : Store, PinsHold M pins τ → τ 0 = M → cntE.eval τ = len)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      baseE.eval σ' = baseE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalB : ∀ τ : Store, PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      baseE.eval τ = av i)
    (hvalS : ∀ (τ : Store) (j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = bv j) :
    ClauseWriter (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
        (leafProg wpJ iInner (negPairLits baseE shiftE)))
      M Jmax wpJ (PinsHold M ((iOuter, i) :: pins))
      ((List.range (len - i - 1)).flatMap fun j => [negPair (av i) (bv j)]) := by
  have hpin' : ∀ p ∈ (iOuter, i) :: pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨hiOuter, hiOutermax, Ne.symm hneOI, hneOw⟩
    · exact ⟨(hpin p hp').1, (hpin p hp').2.1,
        (hpin p hp').2.2.2.1, (hpin p hp').2.2.2.2⟩
  have hleaf : ClauseLoopBody (leafProg wpJ iInner (negPairLits baseE shiftE))
      M Jmax wpJ iInner (PinsHold M ((iOuter, i) :: pins))
      (fun j => [negPair (av i) (bv j)]) :=
    clauseLoopBody_negPair M Jmax wpJ iInner baseE shiftE ((iOuter, i) :: pins)
      (fun _ => av i) bv hwpJ hwpJmax hiInner hiInnermax hneIw hpin' hdepB hdepS
      (fun τ _ hF h0 _ => hvalB τ hF h0)
      (fun τ j hF h0 hj => hvalS τ j hF h0 hj)
  refine clauseWriter_forN _ M Jmax wpJ iInner ((iOuter, i) :: pins) _
    (.sub (.sub cntE (ctlCell iOuter)) (.const 1)) (len - i - 1)
    hiInner hiInnermax hneIw hpin' hleaf ?_
  intro τ h0 hF _
  have hcnt' : cntE.eval τ = len := hcnt τ (pinsHold_tail M (iOuter, i) pins τ hF) h0
  simp only [Expr.eval, hcnt']
  rw [ctlCell_eval, h0, hF (iOuter, i) (by simp)]

lemma clause_writer_at_most_one_range_count
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (cntE baseE shiftE : Expr) (len : ℕ) (vals : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hcnt : ∀ τ : Store, PinsHold M pins τ → τ 0 = M → cntE.eval τ = len)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      baseE.eval σ' = baseE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalB : ∀ (τ : Store) (i : ℕ), PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      baseE.eval τ = vals i)
    (hvalS : ∀ (τ : Store) (i j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = vals (i + 1 + j)) :
    ClauseWriter (loopProg iOuter cntE
        (.seq (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits baseE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1)))))
      M Jmax wpJ (PinsHold M pins) (atMostOneRange ((List.range len).map vals)) := by
  rw [atMostOneRange_range_map_flatMap]
  have hpinOuter : ∀ p ∈ pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ wpJ :=
    fun p hp => ⟨(hpin p hp).1, (hpin p hp).2.1,
      (hpin p hp).2.2.1, (hpin p hp).2.2.2.2⟩
  refine clauseWriter_forN _ M Jmax wpJ iOuter pins _ cntE len
    hiOuter hiOutermax hneOw hpinOuter ?_ ?_
  · refine clauseLoopBody_of_writer _ M Jmax wpJ iOuter pins _
      hiOuter hiOutermax hneOw hpinOuter (fun i => ?_)
    exact clause_writer_at_most_one_range_inner_count M Jmax wpJ iOuter iInner pins
      cntE baseE shiftE len i vals (fun j => vals (i + 1 + j))
      hwpJ hwpJmax hiOuter hiOutermax hiInner hiInnermax hneOI hneOw hneIw hpin hcnt
      hdepB hdepS (hvalB · i) (hvalS · i)
  · intro τ h0 hF _
    exact hcnt τ hF h0

lemma clause_writer_exactly_one_range_count
    (M Jmax wpJ iOuter iInner : ℕ) (pins : List (ℕ × ℕ))
    (cntE indexE shiftE : Expr) (len : ℕ) (vals : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiOuter : 1 ≤ iOuter) (hiOutermax : iOuter ≤ Jmax)
    (hiInner : 1 ≤ iInner) (hiInnermax : iInner ≤ Jmax)
    (hneOI : iInner ≠ iOuter) (hneOw : iOuter ≠ wpJ) (hneIw : iInner ≠ wpJ)
    (hpin : ∀ p ∈ pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iOuter ∧ p.1 ≠ iInner ∧ p.1 ≠ wpJ)
    (hcnt : ∀ τ : Store, PinsHold M pins τ → τ 0 = M → cntE.eval τ = len)
    (hcntE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → r ≠ M + iOuter →
        σ1 r = σ2 r) → cntE.eval σ1 = cntE.eval σ2)
    (hdepI : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      indexE.eval σ' = indexE.eval σ)
    (hdepS : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) →
      shiftE.eval σ' = shiftE.eval σ)
    (hvalI : ∀ (τ : Store) (i : ℕ), PinsHold M ((iOuter, i) :: pins) τ → τ 0 = M →
      indexE.eval τ = vals i)
    (hvalS : ∀ (τ : Store) (i j : ℕ), PinsHold M ((iOuter, i) :: pins) τ →
      τ 0 = M → τ (M + iInner) = j → shiftE.eval τ = vals (i + 1 + j)) :
    ClauseWriter (.seq (writeAtLeastOneProg wpJ iOuter cntE indexE)
        (loopProg iOuter cntE
        (.seq (loopProg iInner (.sub (.sub cntE (ctlCell iOuter)) (.const 1))
            (leafProg wpJ iInner (negPairLits indexE shiftE)))
          (ctlAssign iOuter (.add (ctlCell iOuter) (.const 1))))))
      M Jmax wpJ (PinsHold M pins) (exactlyOne ((List.range len).map vals)) := by
  rw [exactlyOne_eq_atLeastOne_append]
  have hpin1 : ∀ p ∈ pins,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ ∧ p.1 ≠ iOuter :=
    fun p hp => ⟨(hpin p hp).1, (hpin p hp).2.1,
      (hpin p hp).2.2.2.2, (hpin p hp).2.2.1⟩
  refine clauseWriter_seq _ _ M Jmax wpJ (PinsHold M pins) _ _ ?_ ?_
  · refine clauseWriter_atLeastOne M Jmax wpJ iOuter cntE indexE pins
      ((List.range len).map vals) hwpJ hwpJmax hiOuter hiOutermax hneOw hpin1
      (fun τ hF h0 => by rw [hcnt τ hF h0, range_map_length]) hcntE
      (hdep_pins_to_bound M Jmax wpJ indexE hdepI) ?_
    intro τ k hF h0 hk hklt
    rw [range_map_length] at hklt
    rw [range_map_getD len vals k hklt]
    exact hvalI τ k (pinsHold_cons M (iOuter, k) pins τ hk hF) h0
  · exact clause_writer_at_most_one_range_count M Jmax wpJ iOuter iInner pins
      cntE indexE shiftE len vals hwpJ hwpJmax hiOuter hiOutermax hiInner hiInnermax
      hneOI hneOw hneIw hpin hcnt hdepI hdepS hvalI hvalS

/-! ### Run-time-parameter uniqueness writers -/

lemma uniq_state_writer_param
    (M Jmax nS W mS nC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (.seq
        (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
        (loopProg lvJ1 (.const nC)
        (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqStateBaseEParam nS mS wReg)
                (uniqStateShiftEParam nS mS wReg))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)) := by
  have hpin1 : ∀ p ∈ uniquenessParamPins1 wReg tReg W T t,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ lvJ2 ∧ p.1 ≠ wpJ := by
    intro p hp
    have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
      (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
    have h2 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ2 hplace
      (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega) p hp
    exact ⟨h1.1, h1.2.1, h1.2.2.1, h2.2.2.1, h1.2.2.2⟩
  refine clauseWriter_exactlyOne_range M Jmax wpJ lvJ1 lvJ2
    (uniquenessParamPins1 wReg tReg W T t)
    (uniqStateBaseEParam nS mS wReg) (uniqStateShiftEParam nS mS wReg) nC
    (fun q => (denseLayout nS W mS).state t q)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega)
    (by unfold lvJ2 wpJ; omega) hpin1
    (fun σ σ' hσ hσ' h => uniqueness_param_state_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_state_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ i hF h0 => uniqueness_param_state_base_value M nS W mS T wReg tReg t i
      τ hF h0)
    (fun τ i j hF h0 hj => uniqueness_param_state_shift_value M nS W mS T wReg tReg
      t i j τ hF h0 hj)

lemma uniq_head_writer_param
    (M Jmax nS W mS T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (.seq
        (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
        (loopProg lvJ1 (ctlCell wReg)
        (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
            (leafProg wpJ lvJ2
              (negPairLits (uniqHeadBaseEParam nS mS wReg)
                (uniqHeadShiftEParam nS mS wReg))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      (exactlyOne ((List.range W).map fun p => (denseLayout nS W mS).head t p)) := by
  have hpin1 : ∀ p ∈ uniquenessParamPins1 wReg tReg W T t,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ lvJ1 ∧ p.1 ≠ lvJ2 ∧ p.1 ≠ wpJ := by
    intro p hp
    have h1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
      (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) p hp
    have h2 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ2 hplace
      (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega) p hp
    exact ⟨h1.1, h1.2.1, h1.2.2.1, h2.2.2.1, h1.2.2.2⟩
  refine clause_writer_exactly_one_range_count M Jmax wpJ lvJ1 lvJ2
    (uniquenessParamPins1 wReg tReg W T t) (ctlCell wReg)
    (uniqHeadBaseEParam nS mS wReg) (uniqHeadShiftEParam nS mS wReg) W
    (fun p => (denseLayout nS W mS).head t p)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 lvJ2; omega) (by unfold lvJ1 wpJ; omega)
    (by unfold lvJ2 wpJ; omega) hpin1 ?_ ?_
    (fun σ σ' hσ hσ' h => uniqueness_param_head_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_head_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ i hF h0 => uniqueness_param_head_base_value M nS W mS T wReg tReg t i
      τ hF h0)
    (fun τ i j hF h0 hj => uniqueness_param_head_shift_value M nS W mS T wReg tReg
      t i j τ hF h0 hj)
  · intro τ hF h0
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [uniquenessParamPins1, uniquenessParamPins0]) hF h0
  · intro σ1 σ2 h1 h2 hagree
    rw [ctlCell_eval, h1, ctlCell_eval, h2]
    exact hagree (M + wReg) (by have := hplace.w_le; omega)
      (by have := hplace.w_min; unfold wpJ; omega)
      (by have := hplace.w_min; unfold lvJ1; omega)

lemma uniq_cell_writer_param
    (M Jmax nS W mS mC T wReg tReg t p : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (.seq
        (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
        (loopProg lvJ2 (.const mC)
        (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
            (leafProg wpJ lvJ3
              (negPairLits (uniqCellBaseEParam nS mS wReg)
                (uniqCellShiftEParam nS mS wReg))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
      M Jmax wpJ (PinsHold M (uniquenessParamPins2 wReg tReg W T t p))
      (exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) := by
  have hpin2 : ∀ q ∈ uniquenessParamPins2 wReg tReg W T t p,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ2 ∧ q.1 ≠ lvJ3 ∧ q.1 ≠ wpJ := by
    intro q hq
    have h2 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ2 hplace
      (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
      (by unfold lvJ1 lvJ2; omega) q hq
    have h3 := uniqueness_param_pins2_ok Jmax wReg tReg W T t p lvJ3 hplace
      (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) q hq
    exact ⟨h2.1, h2.2.1, h2.2.2.1, h3.2.2.1, h2.2.2.2⟩
  refine clauseWriter_exactlyOne_range M Jmax wpJ lvJ2 lvJ3
    (uniquenessParamPins2 wReg tReg W T t p)
    (uniqCellBaseEParam nS mS wReg) (uniqCellShiftEParam nS mS wReg) mC
    (fun a => (denseLayout nS W mS).cell t p a)
    (by unfold wpJ; omega) (Nat.le_trans wpJ_le hplace.ctl_le)
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ3; omega) (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ2 lvJ3; omega) (by unfold lvJ2 wpJ; omega)
    (by unfold lvJ3 wpJ; omega) hpin2
    (fun σ σ' hσ hσ' h => uniqueness_param_cell_base_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun σ σ' hσ hσ' h => uniqueness_param_cell_shift_frame M Jmax nS mS wReg tReg
      hplace σ σ' hσ hσ' h)
    (fun τ i hF h0 => uniqueness_param_cell_base_value M nS W mS T wReg tReg t p i
      τ hF h0)
    (fun τ i j hF h0 hj => uniqueness_param_cell_shift_value M nS W mS T wReg tReg
      t p i j τ hF h0 hj)

lemma uniq_cell_p_loop_writer_param
    (M Jmax nS W mS mC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
            (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseEParam nS mS wReg)
                    (uniqCellShiftEParam nS mS wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      ((List.range W).flatMap fun p =>
        exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) := by
  have hpin1 := uniqueness_param_pins1_ok Jmax wReg tReg W T t lvJ1 hplace
    (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega)
  refine clauseWriter_forN _ M Jmax wpJ lvJ1
    (uniquenessParamPins1 wReg tReg W T t) _ (ctlCell wReg) W
    (by unfold lvJ1; omega)
    (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ1 wpJ; omega) hpin1 ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ1
      (uniquenessParamPins1 wReg tReg W T t) _ (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega) hpin1
      (fun p => uniq_cell_writer_param M Jmax nS W mS mC T wReg tReg t p hplace)
  · intro τ h0 hF _
    exact ctlCell_eval_of_pin M _ wReg W τ
      (by simp [uniquenessParamPins1, uniquenessParamPins0]) hF h0

lemma uniq_t_fixed_writer_param
    (M Jmax nS W mS nC mC T wReg tReg t : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (.seq (.seq
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
          (loopProg lvJ1 (.const nC)
          (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqStateBaseEParam nS mS wReg)
                  (uniqStateShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
          (loopProg lvJ1 (ctlCell wReg)
          (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqHeadBaseEParam nS mS wReg)
                  (uniqHeadShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
        (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
            (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseEParam nS mS wReg)
                    (uniqCellShiftEParam nS mS wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      M Jmax wpJ (PinsHold M (uniquenessParamPins1 wReg tReg W T t))
      (exactlyOne ((List.range nC).map fun q => (denseLayout nS W mS).state t q)
        ++ exactlyOne ((List.range W).map fun p => (denseLayout nS W mS).head t p)
        ++ (List.range W).flatMap fun p =>
          exactlyOne ((List.range mC).map fun a => (denseLayout nS W mS).cell t p a)) :=
  clauseWriter_seq _ _ M Jmax wpJ
    (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) _ _
    (clauseWriter_seq _ _ M Jmax wpJ
      (PinsHold M (uniquenessParamPins1 wReg tReg W T t)) _ _
      (uniq_state_writer_param M Jmax nS W mS nC T wReg tReg t hplace)
      (uniq_head_writer_param M Jmax nS W mS T wReg tReg t hplace))
    (uniq_cell_p_loop_writer_param M Jmax nS W mS mC T wReg tReg t hplace)

/-- The uniqueness program whose syntax contains parameter addresses but not their values. -/
def uniquenessFamilyProgParam (nS mS nC mC wReg tReg : ℕ) : Program :=
  loopProg lvJ0 (.add (ctlCell tReg) (.const 1))
    (.seq (.seq (.seq
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (.const nC) (uniqStateBaseEParam nS mS wReg))
          (loopProg lvJ1 (.const nC)
          (.seq (loopProg lvJ2 (.sub (.sub (.const nC) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqStateBaseEParam nS mS wReg)
                  (uniqStateShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
        (.seq
          (writeAtLeastOneProg wpJ lvJ1 (ctlCell wReg) (uniqHeadBaseEParam nS mS wReg))
          (loopProg lvJ1 (ctlCell wReg)
          (.seq (loopProg lvJ2 (.sub (.sub (ctlCell wReg) (ctlCell lvJ1)) (.const 1))
              (leafProg wpJ lvJ2
                (negPairLits (uniqHeadBaseEParam nS mS wReg)
                  (uniqHeadShiftEParam nS mS wReg))))
            (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))))
        (loopProg lvJ1 (ctlCell wReg)
        (.seq (.seq
            (writeAtLeastOneProg wpJ lvJ2 (.const mC) (uniqCellBaseEParam nS mS wReg))
            (loopProg lvJ2 (.const mC)
            (.seq (loopProg lvJ3 (.sub (.sub (.const mC) (ctlCell lvJ2)) (.const 1))
                (leafProg wpJ lvJ3
                  (negPairLits (uniqCellBaseEParam nS mS wReg)
                    (uniqCellShiftEParam nS mS wReg))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1))))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma uniquenessFamilyProgParam_writer_param
    (M Jmax nS W mS nC mC T wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) :
    ClauseWriter (uniquenessFamilyProgParam nS mS nC mC wReg tReg)
      M Jmax wpJ (PinsHold M [(wReg, W), (tReg, T)])
      (execUniquenessClausesAt (denseLayout nS W mS)
        (List.range nC) (List.range mC) W T) := by
  unfold uniquenessFamilyProgParam
  refine clauseWriter_forN _ M Jmax wpJ lvJ0
    (uniquenessParamPins0 wReg tReg W T) _ (.add (ctlCell tReg) (.const 1)) (T + 1)
    (by unfold lvJ0; omega)
    (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
    (by unfold lvJ0 wpJ; omega)
    (uniqueness_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace
      (by unfold lvJ0 ctlJmax; omega)) ?_ ?_
  · exact clauseLoopBody_of_writer _ M Jmax wpJ lvJ0
      (uniquenessParamPins0 wReg tReg W T) _ (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega)
      (uniqueness_param_pins0_ok Jmax wReg tReg W T lvJ0 hplace
        (by unfold lvJ0 ctlJmax; omega))
      (fun t => uniq_t_fixed_writer_param M Jmax nS W mS nC mC T wReg tReg t hplace)
  · intro τ h0 hF _
    have eT : (ctlCell tReg).eval τ = T :=
      ctlCell_eval_of_pin M _ tReg T τ (by simp [uniquenessParamPins0]) hF h0
    simp only [Expr.eval, eT]

end NPComplete.CookLevin

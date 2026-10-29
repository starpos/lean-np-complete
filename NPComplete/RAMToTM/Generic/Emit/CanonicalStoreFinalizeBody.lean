module

public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalize
public import NPComplete.RAMToTM.Generic.Emit.WriteFootprint

/-!
# The finalize phase's cleanup half, assembled

Joining a reduction program with an assumed decider via `Program.seq` is only sound if the
reduction leaves the store *exactly* `bitInputStore outputBits` as a function `ℕ → ℕ`
(`CanonicalStoreFinalize.lean`'s module comment), not merely on the output cells. Once the
output bits are emitted, `finalizePivotProg` stages the cleanup control cells at their
post-pivot addresses, then changes cell `0` from the emit bound `S` to the true output length `M`.
`finalizeProg` then runs `finalizeCleanupProg`, which applies `zeroRangeProg` to the scratch region
and `zeroCtlCellsProg` to the finalize phase's control cells. The combined result agrees with
`bitInputStore` above the output region, closing the `funext` obligation `store_eq_bitInputStore`
demands.

It also proves the resource facts the producer's cost analysis needs: `ScanFree` and cost bounds
for cleanup, and `ProgramBoundedIn` for cleanup and for every emitter (bit, natural number, list,
table, tuple table, tagged-entry list, and row table).
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store eval_seq)
open NPComplete.BitEncoding (Bits)

/-- Finalize's cleanup pass: zero the scratch region `[base, base + len)` (read off control
    cells `baseJ`/`lenJ`, cursor `curJ`), then zero the control cells `M + 1 .. M + k`
    themselves. Run in this order since `zeroRangeProg` still needs its own control cells
    (`baseJ`/`lenJ`/`curJ`) intact while it runs. -/
def finalizeCleanupProg (baseJ lenJ curJ k : ℕ) : Program :=
  .seq (zeroRangeProg baseJ lenJ curJ) (zeroCtlCellsProg k)

/-- Running `finalizeCleanupProg` from a store that already holds the correct output length
    (`hM`/`hMlen`) and output bits (`hbitsAt`) at `[0, M]`, with the scratch region
    `[M + k + 1, B]` about to be cleared (`hbase`/`hlenCell`/`hlenEq`) and everything above `B`
    already zero (`hAbove`, e.g. from `WriteFootprint.eval_eq_zero_of_gt`), produces exactly
    `bitInputStore bits` as a function `ℕ → ℕ`: every address above `M` falls into one of three
    disjoint, exhaustively-covered ranges — `[M + 1, M + k]` (control cells, zeroed by
    `zeroCtlCellsProg`), `[M + k + 1, B]` (scratch, zeroed by `zeroRangeProg`), or `(B, ∞)`
    (already zero, `hAbove`) — and neither zeroing pass disturbs the output region `[1, M]`. -/
lemma finalizeCleanupProg_eq_bitInputStore (baseJ lenJ curJ k M B len : ℕ) (bits : Bits) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hbJk : baseJ ≤ k) (hcJk : curJ ≤ k)
    (hM : σ 0 = M) (hMlen : M = bits.length)
    (hbitsAt : ∀ i, i < bits.length → σ (i + 1) = if bits.getD i false then 1 else 0)
    (hbase : σ (M + baseJ) = M + k + 1) (hlenCell : σ (M + lenJ) = len)
    (hlenEq : M + k + 1 + len = B + 1)
    (hAbove : ∀ r, B < r → σ r = 0) :
    (finalizeCleanupProg baseJ lenJ curJ k).eval σ = bitInputStore bits := by
  have hsepB : M + baseJ < M + k + 1 := by omega
  have hsepC : M + curJ < M + k + 1 := by omega
  set σ1 := (zeroRangeProg baseJ lenJ curJ).eval σ with hσ1def
  have hσ1ctl : σ1 0 = M :=
    zeroRangeProg_ctl baseJ lenJ curJ M (M + k + 1) len σ hc1 hbc hlc hM hbase hlenCell hsepB hsepC
  have hσ1zeroed : ∀ q, q < len → σ1 (M + k + 1 + q) = 0 :=
    zeroRangeProg_zeroed baseJ lenJ curJ M (M + k + 1) len σ hc1 hbc hlc hM hbase hlenCell hsepB
      hsepC
  have hσ1frame : ∀ r, (r < M + k + 1 ∨ M + k + 1 + len ≤ r) → r ≠ M + curJ → σ1 r = σ r :=
    zeroRangeProg_frame baseJ lenJ curJ M (M + k + 1) len σ hc1 hbc hlc hM hbase hlenCell hsepB
      hsepC
  set σ2 := (zeroCtlCellsProg k).eval σ1 with hσ2def
  have hσ2ctl : σ2 0 = M := zeroCtlCellsProg_ctl k σ1 M hσ1ctl
  have hσ2zeroed : ∀ j, 1 ≤ j → j ≤ k → σ2 (M + j) = 0 := zeroCtlCellsProg_zeroed k σ1 M hσ1ctl
  have hσ2frame : ∀ r, (r < M + 1 ∨ M + k < r) → σ2 r = σ1 r :=
    zeroCtlCellsProg_frame k σ1 M hσ1ctl
  have heval : (finalizeCleanupProg baseJ lenJ curJ k).eval σ = σ2 := by
    unfold finalizeCleanupProg
    rw [eval_seq, ← hσ1def, ← hσ2def]
  rw [heval]
  apply store_eq_bitInputStore
  · rw [hσ2ctl, hMlen]
  · intro i hi
    have hi1 : i + 1 < M + 1 ∨ M + k < i + 1 := Or.inl (by omega)
    have step1 : σ2 (i + 1) = σ1 (i + 1) := hσ2frame (i + 1) hi1
    have hi2 : i + 1 < M + k + 1 ∨ M + k + 1 + len ≤ i + 1 := Or.inl (by omega)
    have hne2 : i + 1 ≠ M + curJ := by omega
    have step2 : σ1 (i + 1) = σ (i + 1) := hσ1frame (i + 1) hi2 hne2
    rw [step1, step2]
    exact hbitsAt i (by omega)
  · intro r hr
    by_cases hrk : r ≤ M + k
    · have hj1 : 1 ≤ r - M := by omega
      have hj2 : r - M ≤ k := by omega
      have heq : M + (r - M) = r := by omega
      have hz := hσ2zeroed (r - M) hj1 hj2
      rwa [heq] at hz
    · by_cases hrB : r ≤ B
      · have step1 : σ2 r = σ1 r := hσ2frame r (Or.inr (by omega))
        have hq : r - (M + k + 1) < len := by omega
        have heq : M + k + 1 + (r - (M + k + 1)) = r := by omega
        have hz := hσ1zeroed (r - (M + k + 1)) hq
        rw [heq] at hz
        rw [step1, hz]
      · have step1 : σ2 r = σ1 r := hσ2frame r (Or.inr (by omega))
        have hne : r ≠ M + curJ := by omega
        have step2 : σ1 r = σ r := hσ1frame r (Or.inr (by omega)) hne
        rw [step1, step2]
        exact hAbove r (by omega)

open NPComplete.BoundedWhile (Expr eval_assign eval_assignInd writeReg
  writeReg_same writeReg_diff)

/-! ## The finalize phase's pivot half

The emit phase leaves cell `0` holding a proven-but-oversized bound `S ≥ M + k` (chosen so the
reduction never has to compute the exact output length `M` at run time — the emit cursor's final
value already carries it) rather than `M` itself. Every finalize control cell is addressed
relative to cell `0` (`ctlCell j` reads `σ (σ 0 + j)`), so `finalizeCleanupProg` cannot start
until cell `0` is corrected to `M`. `finalizePivotProg` does that correction, but must first
stage `finalizeCleanupProg`'s own control cells (`baseJ`, `lenJ`) at their *post-pivot* addresses
`M + baseJ`/`M + lenJ` — which is only possible *before* the pivot, computed relative to the
*current* cursor cell (`ctlCell curJ`, still holding `M + 1`) rather than the not-yet-corrected
`ctlAddr`. Writing cell `0` last (after both stages) is what makes this order sound: staging
reads `ctlCell curJ`/`ctlCell topJ`, whose addresses `S + curJ`/`S + topJ` are always safely above
every staged target `M + baseJ`/`M + lenJ` (`M + k ≤ S`, `baseJ, lenJ ≤ k`). -/

/-- Correct cell `0` from the emit phase's oversized bound `S` down to the true output length
    `M`, first staging `finalizeCleanupProg`'s own control cells (`M + baseJ` := the scratch
    region's base `M + k + 1`, `M + lenJ` := its length `len`) at cursor-relative addresses
    while cell `0` still reads `S`. Order matters: both staging writes must run before the cell-0
    correction, since they compute their target addresses from `ctlCell curJ`
    (`= σ (σ 0 + curJ)`), which only equals `M + 1` while `σ 0 = S`. -/
def finalizePivotProg (curJ topJ baseJ lenJ k : ℕ) : Program :=
  .seq (.assignInd (.add (ctlCell curJ) (.const (baseJ - 1))) (.add (ctlCell curJ) (.const k)))
  <| .seq (.assignInd (.add (ctlCell curJ) (.const (lenJ - 1)))
      (.sub (ctlCell topJ) (.add (ctlCell curJ) (.const k))))
    (.assign 0 (.sub (ctlCell curJ) (.const 1)))

/-! ## The finalize phase, whole -/

/-- The complete finalize phase: pivot cell `0` from the emit bound `S` down to `M` (staging
    `finalizeCleanupProg`'s control cells in the process), then run `finalizeCleanupProg` itself.
    `zeroCurJ` is `finalizeCleanupProg`'s own cursor and may reuse `curJ` (the emit cursor's
    value is dead after the pivot) or be a fresh cell — both are sound. -/
def finalizeProg (curJ topJ baseJ lenJ zeroCurJ k : ℕ) : Program :=
  .seq (finalizePivotProg curJ topJ baseJ lenJ k) (finalizeCleanupProg baseJ lenJ zeroCurJ k)

/-! ## `ScanFree` facts for every program built in this file and in `CanonicalStoreFinalize.lean`

`eval_eq_of_gt_of_programBoundedIn`/`eval_eq_zero_of_gt` (`WriteFootprint.lean`) need `ScanFree` on
whatever program is actually run, since `scanList`/`lookup` leave `ProgramBoundedIn` unconstrained.
None of the reduction's own programs ever use those two constructs — every one of them is built
from `seq`/`assign`/`assignInd`/`forN`/`ifNZ` alone — so `ScanFree` holds throughout; this section
collects that fact bottom-up, one constructor at a time, so later callers never have to unfold a
whole program's definition to get it. -/

lemma scanFree_ctlAssign (j : ℕ) (e : Expr) : ScanFree (ctlAssign j e) := by
  unfold ctlAssign ScanFree; trivial

lemma scanFree_zeroRangeBody (baseJ curJ : ℕ) : ScanFree (zeroRangeBody baseJ curJ) := by
  unfold zeroRangeBody ScanFree
  exact ⟨trivial, scanFree_ctlAssign curJ _⟩

lemma scanFree_zeroRangeProg (baseJ lenJ curJ : ℕ) : ScanFree (zeroRangeProg baseJ lenJ curJ) := by
  unfold zeroRangeProg ScanFree
  exact ⟨scanFree_ctlAssign curJ _, scanFree_zeroRangeBody baseJ curJ⟩

/-- `zeroCtlCellsProg`'s recursion is on `k`, so `ScanFree` needs its own induction rather than
    following from a fixed unfold. -/
lemma scanFree_zeroCtlCellsProg : ∀ k, ScanFree (zeroCtlCellsProg k)
  | 0 => by unfold zeroCtlCellsProg ScanFree; trivial
  | k + 1 => by
    unfold zeroCtlCellsProg ScanFree
    exact ⟨scanFree_zeroCtlCellsProg k, scanFree_ctlAssign (k + 1) _⟩

lemma scanFree_finalizePivotProg (curJ topJ baseJ lenJ k : ℕ) :
    ScanFree (finalizePivotProg curJ topJ baseJ lenJ k) := by
  unfold finalizePivotProg ScanFree
  exact ⟨trivial, trivial, trivial⟩

lemma scanFree_finalizeCleanupProg (baseJ lenJ curJ k : ℕ) :
    ScanFree (finalizeCleanupProg baseJ lenJ curJ k) := by
  unfold finalizeCleanupProg ScanFree
  exact ⟨scanFree_zeroRangeProg baseJ lenJ curJ, scanFree_zeroCtlCellsProg k⟩

open NPComplete.BoundedWhile (cost_seq cost_forN loopCost_le_of_body_le)

/-! ## Cost bounds for the finalize phase

`BoundedWhileDecider.cost_le` ultimately needs the whole reduction's `Program.cost` bounded by a
polynomial in the input length. `Program.cost` is store-dependent only through `.forN`'s iteration
count (`loopCost body (n.eval σ) σ`) — `Expr.cost` is purely syntactic and every other `Program`
constructor's cost is a fixed function of its immediate sub-costs — so a straight-line program
(no `forN`/`ifNZ`/`scanList`/`lookup`) has store-*independent* cost, and a program built from
`forN` loops over straight-line bodies has cost bounded by `iterations × body_cost`.
`BoundedWhile.lean`'s `loopCost_le_of_body_le` already supplies exactly that bound; this section
only computes the concrete per-instruction/per-body constants for this file's own finalize
programs (and, bonus, the emit primitives) and chains them. -/

lemma zeroRangeBody_cost (baseJ curJ : ℕ) (σ : Store) : (zeroRangeBody baseJ curJ).cost σ = 21 := by
  simp [zeroRangeBody, ctlAssign, ctlAddr, ctlCell, Expr.cost]

/-- `zeroCtlCellsProg`'s cost is store-independent and exact (not just bounded): every step is a
    fixed-cost `ctlAssign`, so induction on `k` gives `1 + 5 * k` on the nose. -/
lemma zeroCtlCellsProg_cost (k : ℕ) (σ : Store) : (zeroCtlCellsProg k).cost σ = 1 + 5 * k := by
  induction k generalizing σ with
  | zero => unfold zeroCtlCellsProg; simp
  | succ k ih =>
    unfold zeroCtlCellsProg
    rw [cost_seq, ih]
    have : (ctlAssign (k + 1) (Expr.const 0)).cost ((zeroCtlCellsProg k).eval σ) = 5 := by
      simp [ctlAssign, ctlAddr, Expr.cost]
    rw [this]; ring

/-- `zeroRangeProg`'s cost: a fixed prologue (resetting the cursor) plus `loopCost_le_of_body_le`
    applied to `zeroRangeBody_cost`'s uniform per-iteration bound, at the iteration count `len`
    the length cell holds right after the prologue (`ctlAssign_eval_diff`/`_same` place that value
    without needing `zeroRangeProg_eval_eq`'s full store reasoning). -/
lemma zeroRangeProg_cost_le (baseJ lenJ curJ M len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hlc : lenJ ≠ curJ) (hM : σ 0 = M) (hlen : σ (M + lenJ) = len) :
    (zeroRangeProg baseJ lenJ curJ).cost σ ≤ 21 * len + 10 := by
  unfold zeroRangeProg
  rw [cost_seq, cost_forN]
  have hstep : (ctlAssign curJ (Expr.const 0)).cost σ = 5 := by
    simp [ctlAssign, ctlAddr, Expr.cost]
  set σ' := (ctlAssign curJ (Expr.const 0)).eval σ with hσ'def
  have hσ'0 : σ' 0 = M := by
    rw [hσ'def, ctlAssign_eval_diff curJ (Expr.const 0) σ 0 (by rw [hM]; omega), hM]
  have hσ'len : σ' (M + lenJ) = len := by
    rw [hσ'def, ctlAssign_eval_diff curJ (Expr.const 0) σ (M + lenJ) (by rw [hM]; omega), hlen]
  have hbound : (ctlCell lenJ).eval σ' = len := by rw [ctlCell_eval, hσ'0, hσ'len]
  have hbodyle : ∀ τ, (zeroRangeBody baseJ curJ).cost τ ≤ 21 :=
    fun τ => (zeroRangeBody_cost baseJ curJ τ).le
  have hloop := loopCost_le_of_body_le (zeroRangeBody baseJ curJ) 21 hbodyle len σ'
  have hcc : (ctlCell lenJ).cost = 4 := by simp [ctlCell, ctlAddr, Expr.cost]
  rw [hstep, hcc, hbound]
  omega

lemma finalizeCleanupProg_cost_le (baseJ lenJ curJ k M len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hlc : lenJ ≠ curJ) (hM : σ 0 = M) (hlen : σ (M + lenJ) = len) :
    (finalizeCleanupProg baseJ lenJ curJ k).cost σ ≤ 21 * len + 5 * k + 11 := by
  unfold finalizeCleanupProg
  rw [cost_seq]
  have h1 := zeroRangeProg_cost_le baseJ lenJ curJ M len σ hc1 hlc hM hlen
  have h2 := zeroCtlCellsProg_cost k ((zeroRangeProg baseJ lenJ curJ).eval σ)
  omega

lemma finalizePivotProg_cost (curJ topJ baseJ lenJ k : ℕ) (σ : Store) :
    (finalizePivotProg curJ topJ baseJ lenJ k).cost σ = 38 := by
  simp [finalizePivotProg, ctlAddr, ctlCell, Expr.cost]

open NPComplete.BoundedWhile (loopEval)

/-! ## `ProgramBoundedIn` for the finalize phase

`BoundedWhileDecider.compiled_operands_le` needs `ProgramBoundedIn` (`CompileExecBounded.lean`) for
whatever program is actually run — every address a `Program` assigns to and every intermediate
value it computes must stay `≤ B` — and `WriteFootprint.lean`'s bounded-execution lemmas share the
same prerequisite. `ScanFree` is already established for every finalize program above; this section
adds `ProgramBoundedIn`, reusing this file's own store-tracking facts
(`zeroRangeBody_loop_invariant`, `zeroRangeProg_ctl`) rather than
re-deriving how the store evolves. Two bounds are genuinely distinct here: `Bp` (this section's
own bound, tracking every address/value the finalize programs touch) is *not* the same `B` used
elsewhere for "everything above the scratch region is zero" — `finalizePivotProg`'s pivot
register holds `B + 1` (one past the scratch region), which exceeds `B` itself, so
`ProgramBoundedIn` for the pivot needs `Bp ≥ B + 1`. Callers instantiate `Bp` to whatever bound
actually covers the compiled RAM's cells; the lemmas below are stated generically in terms of
`Bp` and whatever raw values (`Btop`, etc.) the relevant control cells hold, without assuming a
fixed relationship to any particular `B`. -/

/-- `ExprBoundedIn` for `ctlAddr j`: the register index `0` and `j` both stay `≤ Bp`, and the
    combined value `σ 0 + j` (the address `ctlCell j` will read from) stays `≤ Bp`. -/
lemma exprBoundedIn_ctlAddr (Bp j : ℕ) (σ : Store) (hj : j ≤ Bp) (hsum : σ 0 + j ≤ Bp) :
    ExprBoundedIn Bp σ (ctlAddr j) := by
  simp only [ctlAddr, ExprBoundedIn, Expr.eval]
  omega

/-- `ExprBoundedIn` for `ctlCell j`: `ctlAddr j`'s own bound, plus its value `σ 0 + j` (the
    address `.regInd` dereferences) staying `≤ Bp`. -/
lemma exprBoundedIn_ctlCell (Bp j : ℕ) (σ : Store) (hj : j ≤ Bp) (hsum : σ 0 + j ≤ Bp) :
    ExprBoundedIn Bp σ (ctlCell j) := by
  simp only [ctlCell, ExprBoundedIn]
  refine ⟨exprBoundedIn_ctlAddr Bp j σ hj hsum, ?_⟩
  rw [ctlAddr_eval]; exact hsum

/-- `ProgramBoundedIn` for one `zeroRangeBody` step at cursor value `c`: both instructions'
    addresses/values (`base + c` for the write, `c + 1` for the cursor advance) stay `≤ Bp`,
    reusing the same one-step `writeReg` tracking `zeroRangeBody_loop_invariant`'s own proof
    establishes for its `t = 1` case, inlined here since only the intermediate store (not the
    bundled zeroed/frame facts) is needed. `baseJ ≠ curJ` turns out unnecessary: only cell
    *values*, never the two indices' relative identity, are used. -/
lemma programBoundedIn_zeroRangeBody (Bp baseJ curJ M base c : ℕ) (σ : Store)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hcur : σ (M + curJ) = c)
    (hbaseJBp : baseJ ≤ Bp) (hcurJBp : curJ ≤ Bp) (hMcurJBp : M + curJ ≤ Bp)
    (haddr : base + c ≤ Bp) :
    ProgramBoundedIn Bp σ (zeroRangeBody baseJ curJ) := by
  unfold zeroRangeBody ProgramBoundedIn
  have hcc1 : (ctlCell baseJ).eval σ = base := by rw [ctlCell_eval, hM, hbase]
  have hcc2 : (ctlCell curJ).eval σ = c := by rw [ctlCell_eval, hM, hcur]
  refine ⟨⟨⟨exprBoundedIn_ctlCell Bp baseJ σ hbaseJBp (by rw [hM]; omega),
    exprBoundedIn_ctlCell Bp curJ σ hcurJBp (by rw [hM]; omega),
    by simp [hcc1, hcc2, haddr]⟩,
    by simp [ExprBoundedIn], by simp [Expr.eval, hcc1, hcc2, haddr]⟩, ?_⟩
  set σ1 := (Program.assignInd (Expr.add (ctlCell baseJ) (ctlCell curJ)) (Expr.const 0)).eval σ
    with hσ1def
  have hσ1eq : σ1 = writeReg σ (base + c) 0 := by
    rw [hσ1def, eval_assignInd]
    congr 1
    simp [Expr.eval, hcc1, hcc2]
  have hσ10 : σ1 0 = M := by rw [hσ1eq, writeReg_diff σ (base + c) 0 0 (by omega), hM]
  have hσ1cur : σ1 (M + curJ) = c := by
    rw [hσ1eq, writeReg_diff σ (base + c) 0 (M + curJ) (by omega), hcur]
  unfold ctlAssign ProgramBoundedIn
  have hσ1cc : (ctlCell curJ).eval σ1 = c := by rw [ctlCell_eval, hσ10, hσ1cur]
  refine ⟨exprBoundedIn_ctlAddr Bp curJ σ1 hcurJBp (by rw [hσ10]; omega),
    ⟨exprBoundedIn_ctlCell Bp curJ σ1 hcurJBp (by rw [hσ10]; omega),
      by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hσ1cc]; omega⟩, ?_⟩
  rw [ctlAddr_eval, hσ10]; omega

/-- `ProgramBoundedIn` for `zeroRangeProg`: the cursor-reset prologue, then every one of `len`
    loop iterations, each supplied by `programBoundedIn_zeroRangeBody` at that iteration's own
    cursor value (`0 + m'`, from `zeroRangeBody_loop_invariant`) — the same store-tracking
    dependency `zeroRangeProg_cost_le` and `finalizeCleanupProg_eq_bitInputStore` both rely on. -/
lemma programBoundedIn_zeroRangeProg (Bp baseJ lenJ curJ M base len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hlen : σ (M + lenJ) = len)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base)
    (hbaseJBp : baseJ ≤ Bp) (hlenJBp : lenJ ≤ Bp) (hcurJBp : curJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMlenJBp : M + lenJ ≤ Bp) (haddr : base + len ≤ Bp) :
    ProgramBoundedIn Bp σ (zeroRangeProg baseJ lenJ curJ) := by
  unfold zeroRangeProg ProgramBoundedIn
  refine ⟨⟨exprBoundedIn_ctlAddr Bp curJ σ hcurJBp (by rw [hM]; omega),
    by simp [ExprBoundedIn], by rw [ctlAddr_eval, hM]; omega⟩, ?_⟩
  set σ' := (ctlAssign curJ (Expr.const 0)).eval σ with hσ'def
  have hσ'0 : σ' 0 = M := by
    rw [hσ'def, ctlAssign_eval_diff curJ (Expr.const 0) σ 0 (by rw [hM]; omega), hM]
  have hσ'base : σ' (M + baseJ) = base := by
    rw [hσ'def, ctlAssign_eval_diff curJ (Expr.const 0) σ (M + baseJ) (by rw [hM]; omega), hbase]
  have hσ'len : σ' (M + lenJ) = len := by
    rw [hσ'def, ctlAssign_eval_diff curJ (Expr.const 0) σ (M + lenJ) (by rw [hM]; omega), hlen]
  have hσ'cur0 : σ' (M + curJ) = 0 := by
    rw [hσ'def]
    have h := ctlAssign_eval_same curJ (Expr.const 0) σ
    rwa [hM] at h
  have hbound : (ctlCell lenJ).eval σ' = len := by rw [ctlCell_eval, hσ'0, hσ'len]
  refine ⟨exprBoundedIn_ctlCell Bp lenJ σ' hlenJBp (by rw [hσ'0]; omega), ?_⟩
  rw [hbound]
  intro m' hm'
  obtain ⟨hi0, hib, hic, _, _⟩ :=
    zeroRangeBody_loop_invariant baseJ curJ M base hc1 hbc hsepB hsepC m' 0 σ' hσ'0 hσ'base hσ'cur0
  refine programBoundedIn_zeroRangeBody Bp baseJ curJ M base m'
    (loopEval (zeroRangeBody baseJ curJ) m' σ') hsepB hsepC hi0 hib (by rw [hic]; omega)
    hbaseJBp hcurJBp hMcurJBp (by omega)

/-- `ProgramBoundedIn` for `zeroCtlCellsProg`: induction on `k`, each step contributing one
    `ctlAssign` whose address `M + (k + 1)` stays `≤ Bp` (via `zeroCtlCellsProg_ctl`'s
    preservation of cell `0`). -/
lemma programBoundedIn_zeroCtlCellsProg (Bp k M : ℕ) (σ : Store) (hM : σ 0 = M)
    (hkBp : k ≤ Bp) (hMkBp : M + k ≤ Bp) :
    ProgramBoundedIn Bp σ (zeroCtlCellsProg k) := by
  induction k generalizing σ with
  | zero => unfold zeroCtlCellsProg ProgramBoundedIn; trivial
  | succ k ih =>
    unfold zeroCtlCellsProg ProgramBoundedIn
    refine ⟨ih σ hM (by omega) (by omega), ?_⟩
    have hctl : (zeroCtlCellsProg k).eval σ 0 = M := zeroCtlCellsProg_ctl k σ M hM
    unfold ctlAssign ProgramBoundedIn
    refine ⟨exprBoundedIn_ctlAddr Bp (k + 1) ((zeroCtlCellsProg k).eval σ) (by omega)
      (by rw [hctl]; omega), by simp [ExprBoundedIn], by rw [ctlAddr_eval, hctl]; omega⟩

/-- `ProgramBoundedIn` for `finalizeCleanupProg`: chains `programBoundedIn_zeroRangeProg` with
    `programBoundedIn_zeroCtlCellsProg`, using `zeroRangeProg_ctl` to carry cell `0`'s value
    across the two stages without re-deriving it. -/
lemma programBoundedIn_finalizeCleanupProg (Bp baseJ lenJ curJ k M base len : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hbc : baseJ ≠ curJ) (hlc : lenJ ≠ curJ)
    (hM : σ 0 = M) (hbase : σ (M + baseJ) = base) (hlen : σ (M + lenJ) = len)
    (hsepB : M + baseJ < base) (hsepC : M + curJ < base)
    (hbaseJBp : baseJ ≤ Bp) (hlenJBp : lenJ ≤ Bp) (hcurJBp : curJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMlenJBp : M + lenJ ≤ Bp) (haddrBp : base + len ≤ Bp)
    (hkBp : k ≤ Bp) (hMkBp : M + k ≤ Bp) :
    ProgramBoundedIn Bp σ (finalizeCleanupProg baseJ lenJ curJ k) := by
  unfold finalizeCleanupProg ProgramBoundedIn
  refine ⟨programBoundedIn_zeroRangeProg Bp baseJ lenJ curJ M base len σ hc1 hbc hlc hM hbase hlen
    hsepB hsepC hbaseJBp hlenJBp hcurJBp hMcurJBp hMlenJBp haddrBp, ?_⟩
  have hctl : (zeroRangeProg baseJ lenJ curJ).eval σ 0 = M :=
    zeroRangeProg_ctl baseJ lenJ curJ M base len σ hc1 hbc hlc hM hbase hlen hsepB hsepC
  exact programBoundedIn_zeroCtlCellsProg Bp k M ((zeroRangeProg baseJ lenJ curJ).eval σ) hctl
    hkBp hMkBp

/-- The shared pivot's boundedness proof stays generic in the control-register offsets, so callers
    can reuse it without duplicating the pivot's address calculations. -/
lemma programBoundedIn_finalizePivotProg
    (Bp curJ topJ baseJ lenJ k S L B : ℕ) (τ : Store)
    (hcurJ1 : 1 ≤ curJ) (htopJ1 : 1 ≤ topJ)
    (hbaseJ1 : 1 ≤ baseJ) (hlenJ1 : 1 ≤ lenJ)
    (hbaseSep : L + baseJ ≤ S) (hlenSep : L + lenJ ≤ S)
    (h0 : τ 0 = S) (hcur : τ (S + curJ) = L + 1)
    (htop : τ (S + topJ) = B + 1)
    (hS_curBp : S + curJ ≤ Bp) (hS_topBp : S + topJ ≤ Bp)
    (hLkBp : L + 1 + k ≤ Bp) (hB1Bp : B + 1 ≤ Bp) :
    ProgramBoundedIn Bp τ (finalizePivotProg curJ topJ baseJ lenJ k) := by
  have hcc : (ctlCell curJ).eval τ = L + 1 := by
    rw [ctlCell_eval, h0]
    exact hcur
  have htc : (ctlCell topJ).eval τ = B + 1 := by
    rw [ctlCell_eval, h0]
    exact htop
  let first := Program.assignInd (.add (ctlCell curJ) (.const (baseJ - 1)))
    (.add (ctlCell curJ) (.const k))
  let second := Program.assignInd (.add (ctlCell curJ) (.const (lenJ - 1)))
    (.sub (ctlCell topJ) (.add (ctlCell curJ) (.const k)))
  let third := Program.assign 0 (.sub (ctlCell curJ) (.const 1))
  let τ1 := first.eval τ
  have hτ1eq : τ1 = writeReg τ (L + baseJ) (L + 1 + k) := by
    dsimp [τ1, first]
    rw [eval_assignInd]
    have ha : (Expr.add (ctlCell curJ) (.const (baseJ - 1))).eval τ = L + baseJ := by
      simp only [Expr.eval, hcc]
      omega
    have hv : (Expr.add (ctlCell curJ) (.const k)).eval τ = L + 1 + k := by
      simp only [Expr.eval, hcc]
    rw [ha, hv]
  have hτ10 : τ1 0 = S := by
    rw [hτ1eq, writeReg_diff _ _ _ _ (by omega), h0]
  have hτ1cur : τ1 (S + curJ) = L + 1 := by
    rw [hτ1eq, writeReg_diff _ _ _ _ (by omega), hcur]
  have hτ1top : τ1 (S + topJ) = B + 1 := by
    rw [hτ1eq, writeReg_diff _ _ _ _ (by omega), htop]
  have hcc1 : (ctlCell curJ).eval τ1 = L + 1 := by
    rw [ctlCell_eval, hτ10]
    exact hτ1cur
  have htc1 : (ctlCell topJ).eval τ1 = B + 1 := by
    rw [ctlCell_eval, hτ10]
    exact hτ1top
  have hfirst : ProgramBoundedIn Bp τ first := by
    simp [first, ProgramBoundedIn, ExprBoundedIn, ctlCell, ctlAddr, Expr.eval, h0, hcur]
    omega
  have hsecond : ProgramBoundedIn Bp τ1 second := by
    simp [second, ProgramBoundedIn, ExprBoundedIn, ctlCell, ctlAddr, Expr.eval,
      hτ10, hτ1cur, hτ1top]
    omega
  let τ2 := second.eval τ1
  have hτ2eq : τ2 = writeReg τ1 (L + lenJ) (B + 1 - (L + 1 + k)) := by
    dsimp [τ2, second]
    rw [eval_assignInd]
    have ha : (Expr.add (ctlCell curJ) (.const (lenJ - 1))).eval τ1 = L + lenJ := by
      simp only [Expr.eval, hcc1]
      omega
    have hv : (Expr.sub (ctlCell topJ) (.add (ctlCell curJ) (.const k))).eval τ1 =
        B + 1 - (L + 1 + k) := by
      simp only [Expr.eval, hcc1, htc1]
    rw [ha, hv]
  have hτ20 : τ2 0 = S := by
    rw [hτ2eq, writeReg_diff _ _ _ _ (by omega), hτ10]
  have hτ2cur : τ2 (S + curJ) = L + 1 := by
    rw [hτ2eq, writeReg_diff _ _ _ _ (by omega), hτ1cur]
  have hcc2 : (ctlCell curJ).eval τ2 = L + 1 := by
    rw [ctlCell_eval, hτ20]
    exact hτ2cur
  have hthird : ProgramBoundedIn Bp τ2 third := by
    simp [third, ProgramBoundedIn, ExprBoundedIn, ctlCell, ctlAddr, Expr.eval, hτ20, hτ2cur]
    omega
  change ProgramBoundedIn Bp τ first ∧
    (ProgramBoundedIn Bp (first.eval τ) second ∧
      ProgramBoundedIn Bp (second.eval (first.eval τ)) third)
  exact ⟨hfirst, ⟨hsecond, hthird⟩⟩

open NPComplete.BoundedWhile (loopCost loopCost_succ)
open NPComplete.BitEncoding (encodeNat)

/-! ## `ProgramBoundedIn` for the `encodeList`-shaped emit programs

`ProgramBoundedIn` for the finalize phase is established above;
`BoundedWhileDecider.compiled_operands_le` and `WriteFootprint.lean`'s bounded-execution lemmas
need it for the emit programs too, since the whole reduction (emit, then finalize) is one
compiled `Program`. The same
two-bound distinction the finalize section's module comment calls out applies here: `Bp` (every
address/value the emit programs touch) is *not* fixed to equal the ordinary control-cell wall
`M + curJ`/`M + tmpJ` etc. — `emitBitProg`'s cursor advance forces `ExprBoundedIn`'s `.add` case to
bound the *summed* result `cur + 1`, not just `cur` itself, so the write window's own upper edge
must be supplied as a bound on `Bp` independently of the wall. The `.forN` loops this section's
programs build (`emitNatProg`'s zero-bit loop, `emitListProg`'s element loop) need `ProgramBoundedIn`
at *every* store `loopEval body m' σ` visits, exactly where the corresponding correctness lemmas
(`emitNatProg_eval_state`, `emitListProg_eval_state`) already needed the store at each iteration —
the same per-iteration facts (`emit_zero_loop_invariant`, `emitNatTableProg_hbody`) are reused here
rather than re-derived. -/

open NPComplete.BoundedWhile (eval_forN loopEval_zero loopEval_succ)
open NPComplete.BitEncoding (encodeNat_length)

/-- `ProgramBoundedIn` for `emitBitProg`: both instructions' addresses/values (the write target
    `cur` and the cursor advance `cur + 1`) stay `≤ Bp`. Mirrors `programBoundedIn_zeroRangeBody`'s
    shape, except the write target here *is* the cursor value itself (`emitBitProg` writes
    directly at the cursor, unlike `zeroRangeBody`'s `base + c`), so `hcur0`/`hne` (cursor is
    nonzero and distinct from its own control cell) are needed up front rather than derived. -/
lemma programBoundedIn_emitBitProg (Bp curJ M cur : ℕ) (v : Expr) (σ : Store)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur0 : cur ≠ 0) (hne : cur ≠ M + curJ)
    (hv : ExprBoundedIn Bp σ v)
    (hcurJBp : curJ ≤ Bp) (hMcurJBp : M + curJ ≤ Bp) (hcurBp : cur ≤ Bp)
    (hcur1Bp : cur + 1 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitBitProg curJ v) := by
  unfold emitBitProg ProgramBoundedIn
  have hcc : (ctlCell curJ).eval σ = cur := by rw [ctlCell_eval, hM, hcur]
  refine ⟨⟨exprBoundedIn_ctlCell Bp curJ σ hcurJBp (by rw [hM]; omega), hv,
    by rw [hcc]; exact hcurBp⟩, ?_⟩
  set σ1 := (Program.assignInd (ctlCell curJ) v).eval σ with hσ1def
  clear_value σ1
  have hσ1eq : σ1 = writeReg σ cur (v.eval σ) := by rw [hσ1def, eval_assignInd, hcc]
  have hσ10 : σ1 0 = M := by rw [hσ1eq, writeReg_diff σ cur (v.eval σ) 0 (Ne.symm hcur0), hM]
  have hσ1cur : σ1 (M + curJ) = cur := by
    rw [hσ1eq, writeReg_diff σ cur (v.eval σ) (M + curJ) (Ne.symm hne), hcur]
  clear hσ1eq hσ1def
  unfold ctlAssign ProgramBoundedIn
  have hσ1cc : (ctlCell curJ).eval σ1 = cur := by rw [ctlCell_eval, hσ10, hσ1cur]
  refine ⟨exprBoundedIn_ctlAddr Bp curJ σ1 hcurJBp (by rw [hσ10]; omega),
    ⟨exprBoundedIn_ctlCell Bp curJ σ1 hcurJBp (by rw [hσ10]; omega),
     by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hσ1cc]; omega⟩, ?_⟩
  rw [ctlAddr_eval, hσ10]; omega

/-- `ProgramBoundedIn` for `emitNatProg`: the length-staging prologue, `n` iterations of the
    zero-bit loop (each supplied by `programBoundedIn_emitBitProg` at that iteration's own cursor
    value, from `emit_zero_loop_invariant`), then the terminating `1`-bit. The whole write window
    `[cur, cur + n + 1]` must stay `≤ Bp` (`hcurEBp`), distinct from the ordinary control-cell wall
    `M + curJ` (`hsep`): the two bounds are unrelated a priori. -/
lemma programBoundedIn_emitNatProg (Bp curJ tmpJ M cur : ℕ) (e : Expr) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hsep : cur + e.eval σ < M + curJ)
    (he : ExprBoundedIn Bp σ e)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hcurEBp : cur + e.eval σ + 1 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitNatProg curJ tmpJ e) := by
  set n := e.eval σ with hndef
  unfold emitNatProg ProgramBoundedIn
  refine ⟨⟨exprBoundedIn_ctlAddr Bp tmpJ σ htmpJBp (by rw [hM]; omega), he,
    by rw [ctlAddr_eval, hM]; omega⟩, ?_⟩
  have hσ1val : (ctlAssign tmpJ e).eval σ (M + tmpJ) = n := by
    have h := ctlAssign_eval_same tmpJ e σ
    rw [hM] at h
    rw [h, ← hndef]
  have hσ10 : (ctlAssign tmpJ e).eval σ 0 = M := by
    rw [ctlAssign_zero tmpJ e σ hc2, hM]
  have hσ1cur : (ctlAssign tmpJ e).eval σ (M + curJ) = cur := by
    have hne : M + curJ ≠ σ 0 + tmpJ := by rw [hM]; omega
    rw [ctlAssign_eval_diff tmpJ e σ (M + curJ) hne, hcur]
  set σ1 := (ctlAssign tmpJ e).eval σ with hσ1def
  clear_value σ1
  unfold ProgramBoundedIn
  have hbound : (ctlCell tmpJ).eval σ1 = n := by rw [ctlCell_eval, hσ10, hσ1val]
  refine ⟨⟨exprBoundedIn_ctlCell Bp tmpJ σ1 htmpJBp (by rw [hσ10]; omega), ?_⟩, ?_⟩
  · rw [hbound]
    intro m' hm'
    obtain ⟨hi0, hic, _, _⟩ :=
      emit_zero_loop_invariant curJ M hc1 m' cur σ1 hσ10 hσ1cur hcur1 (by omega)
    exact programBoundedIn_emitBitProg Bp curJ M (cur + m') (Expr.const 0) (loopEval
      (emitBitProg curJ (Expr.const 0)) m' σ1) hi0 hic (by omega) (by omega)
      (by simp only [ExprBoundedIn]; omega) hcurJBp hMcurJBp (by omega) (by omega)
  · have hforNeval : (Program.forN (ctlCell tmpJ) (emitBitProg curJ (Expr.const 0))).eval σ1
        = loopEval (emitBitProg curJ (Expr.const 0)) n σ1 := by rw [eval_forN, hbound]
    rw [hforNeval]
    obtain ⟨hi0, hic, _, _⟩ :=
      emit_zero_loop_invariant curJ M hc1 n cur σ1 hσ10 hσ1cur hcur1 (by omega)
    exact programBoundedIn_emitBitProg Bp curJ M (cur + n) (Expr.const 1) (loopEval
      (emitBitProg curJ (Expr.const 0)) n σ1) hi0 hic (by omega) (by omega)
      (by simp only [ExprBoundedIn]; omega) hcurJBp hMcurJBp (by omega) (by omega)

/-- Propagates `ProgramBoundedIn` to the store `loopEval body m' τ` visits at every position
    `m' < t`, given a per-step invariant transition supplying that fact at each step's own entry
    store. -/
lemma programBoundedIn_loopEval_of_indexed_inv (M : ℕ) (body : Program) (Inv : ℕ → Store → Prop)
    (Bp n : ℕ)
    (hbody : ∀ m, m < n → ∀ τ, Inv m τ → τ 0 = M →
      Inv (m + 1) (body.eval τ) ∧ (body.eval τ) 0 = M ∧ ProgramBoundedIn Bp τ body) :
    ∀ (t k : ℕ), k + t ≤ n → ∀ (τ : Store), Inv k τ → τ 0 = M →
      ∀ m', m' < t → ProgramBoundedIn Bp (loopEval body m' τ) body := by
  intro t
  induction t with
  | zero => intro k _ τ _ _ m' hm'; omega
  | succ t ih =>
    intro k hk τ hInv h0 m' hm'
    have hkn : k < n := by omega
    obtain ⟨hInv', hctl', hpb⟩ := hbody k hkn τ hInv h0
    rcases Nat.eq_zero_or_pos m' with hm0 | hmpos
    · subst hm0; rw [loopEval_zero]; exact hpb
    · have hm'1 : m' - 1 < t := by omega
      have hrec := ih (k + 1) (by omega) (body.eval τ) hInv' hctl' (m' - 1) hm'1
      have hm'eq : m' = (m' - 1) + 1 := by omega
      rw [hm'eq, loopEval_succ]
      exact hrec

/-- `ProgramBoundedIn` for `emitListProg`, generic in `body`/`Inv` like `emitListProg_eval_state`:
    the length prefix (`programBoundedIn_emitNatProg`), then the element loop, whose per-iteration
    bound is supplied by the caller's own `hbody` and propagated by
    `programBoundedIn_loopEval_of_indexed_inv`. -/
lemma programBoundedIn_emitListProg (Bp curJ tmpJ cntJ M cur n : ℕ) (body : Program)
    (Inv : ℕ → Store → Prop) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcc : cntJ ≠ curJ) (hcnt2 : cntJ ≠ tmpJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur) (hcnt : σ (M + cntJ) = n)
    (hsepCnt : cur + n + 1 ≤ M + cntJ) (hsepFull : cur + n + 1 ≤ M + curJ)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hcurNBp : cur + n + 1 ≤ Bp)
    (hbody : ∀ m, m < n → ∀ τ, Inv m τ → τ 0 = M →
      Inv (m + 1) (body.eval τ) ∧ (body.eval τ) 0 = M ∧ ProgramBoundedIn Bp τ body)
    (hInv0 : Inv 0 ((emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ)) :
    ProgramBoundedIn Bp σ (emitListProg curJ tmpJ cntJ body) := by
  unfold emitListProg ProgramBoundedIn
  have hcntEval : (ctlCell cntJ).eval σ = n := by rw [ctlCell_eval, hM, hcnt]
  refine ⟨?_, ?_⟩
  · apply programBoundedIn_emitNatProg Bp curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1
      (by rw [hcntEval]; omega) (exprBoundedIn_ctlCell Bp cntJ σ hcntJBp (by rw [hM]; omega))
      hcurJBp htmpJBp hMcurJBp hMtmpJBp (by rw [hcntEval]; omega)
  · have hsep' : cur + (ctlCell cntJ).eval σ < M + curJ := by rw [hcntEval]; omega
    obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
      emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1 hsep'
    rw [hcntEval] at hbits1 hcursor1 hframe1
    set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ with hσ1def
    have hInv0' : Inv 0 σ1 := hInv0
    have hσ1cnt : σ1 (M + cntJ) = n := by
      rw [hframe1 (M + cntJ) (by omega) (by omega) (Or.inr (by omega)), hcnt]
    have hbound : (ctlCell cntJ).eval σ1 = n := by rw [ctlCell_eval, hctl1, hσ1cnt]
    unfold ProgramBoundedIn
    refine ⟨exprBoundedIn_ctlCell Bp cntJ σ1 hcntJBp (by rw [hctl1]; omega), ?_⟩
    rw [hbound]
    exact programBoundedIn_loopEval_of_indexed_inv M body Inv Bp n hbody n 0 (by omega) σ1 hInv0'
      hctl1

/-- Per-iteration `ProgramBoundedIn` fact for `emitNatTableBody`. Reuses `emitNatTableProg_hbody`
    for the invariant-advance/cell-0 facts (not re-derived); boundedness itself needs no bound on
    `g`'s own values, only that the write window stays inside the control-cell wall `M + curJ`
    (already `≤ Bp` via `hMcurJBp`) and the table address `tbl + m` stays `≤ Bp` (`htblNBp`). -/
lemma programBoundedIn_emitNatTableBody (Bp curJ tmpJ tblJ idxJ M cur0 tbl n : ℕ) (g : ℕ → ℕ)
    (τ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ) (hbi : tblJ ≠ idxJ)
    (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + curJ)
    (hsepTmpAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + tmpJ)
    (hsepIdxAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + idxJ)
    (hsepTblAll : cur0 + ((List.range n).flatMap (fun k => encodeNat (g k))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblNBp : tbl + n ≤ Bp)
    (m : ℕ) (hmn : m < n) (hInv : EmitNatTableInv curJ tblJ idxJ M cur0 tbl n g m τ) (hM : τ 0 = M) :
    EmitNatTableInv curJ tblJ idxJ M cur0 tbl n g (m + 1)
      ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) ∧
    (emitNatTableBody curJ tmpJ tblJ idxJ).eval τ 0 = M ∧
    ProgramBoundedIn Bp τ (emitNatTableBody curJ tmpJ tblJ idxJ) := by
  obtain ⟨hidxCell, htblCell, htable, hcurpin⟩ := hInv
  obtain ⟨_, _, hctl0, _, hInv'⟩ :=
    emitNatTableProg_hbody curJ tmpJ tblJ idxJ M cur0 tbl n g
      hc1 hc2 hct hcb hci htb hti hbi hcur01 hsepFull hsepTmpAll hsepIdxAll hsepTblAll
      hloCur hloTmp hloIdx m hmn τ (τ (M + curJ)) ⟨hidxCell, htblCell, htable, hcurpin⟩ hM rfl
  refine ⟨hInv', hctl0, ?_⟩
  have he : (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))).eval τ = g m := by
    simp only [Expr.eval, ctlCell_eval, hM, htblCell, hidxCell]
    exact htable m hmn
  have hstep : ((List.range m).flatMap (fun k => encodeNat (g k))).length + (encodeNat (g m)).length
      = ((List.range (m + 1)).flatMap (fun k => encodeNat (g k))).length := by
    have hsplit2 := flatMap_range_length_split (fun k => encodeNat (g k)) (m + 1) m (by omega)
    have h1 : (m + 1) - m = 1 := by omega
    rw [h1, List.range'_one] at hsplit2
    simpa using hsplit2
  have hle : ((List.range (m + 1)).flatMap (fun k => encodeNat (g k))).length
      ≤ ((List.range n).flatMap (fun k => encodeNat (g k))).length := by
    have hsplit := flatMap_range_length_split (fun k => encodeNat (g k)) n (m + 1) (by omega)
    omega
  rw [encodeNat_length] at hstep
  have hkey : τ (M + curJ) + g m + 1
      = cur0 + ((List.range (m + 1)).flatMap (fun k => encodeNat (g k))).length := by
    rw [hcurpin]; omega
  have htblmBp : tbl + m ≤ Bp := by omega
  have hAddr : (ctlCell tblJ).eval τ + (ctlCell idxJ).eval τ ≤ Bp := by
    rw [ctlCell_eval, ctlCell_eval, hM, htblCell, hidxCell]; omega
  have he_ebi : ExprBoundedIn Bp τ (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))) := by
    refine ⟨⟨exprBoundedIn_ctlCell Bp tblJ τ htblJBp (by rw [hM]; omega),
      exprBoundedIn_ctlCell Bp idxJ τ hidxJBp (by rw [hM]; omega), hAddr⟩, ?_⟩
    simpa [Expr.eval] using hAddr
  unfold emitNatTableBody ProgramBoundedIn
  refine ⟨programBoundedIn_emitNatProg Bp curJ tmpJ M (τ (M + curJ))
    (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))) τ hc1 hc2 hct hM rfl (by omega)
    (by rw [he]; omega) he_ebi hcurJBp htmpJBp hMcurJBp hMtmpJBp (by rw [he]; omega), ?_⟩
  have hsep' : τ (M + curJ) + (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))).eval τ
      < M + curJ := by rw [he]; omega
  obtain ⟨hbits, hcursor, hframe, hctl⟩ := emitNatProg_eval_state curJ tmpJ M (τ (M + curJ))
    (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ))) τ hc1 hc2 hct hM rfl (by omega) hsep'
  rw [he] at hbits hcursor hframe
  set σ1 := (emitNatProg curJ tmpJ
    (Expr.regInd (Expr.add (ctlCell tblJ) (ctlCell idxJ)))).eval τ with hσ1def
  have hσ1idx : σ1 (M + idxJ) = m := by
    rw [hframe (M + idxJ) (by omega) (by omega) (Or.inr (by omega)), hidxCell]
  clear_value σ1
  unfold ctlAssign ProgramBoundedIn
  have hcc : (ctlCell idxJ).eval σ1 = m := by rw [ctlCell_eval, hctl, hσ1idx]
  refine ⟨exprBoundedIn_ctlAddr Bp idxJ σ1 hidxJBp (by rw [hctl]; omega),
    ⟨exprBoundedIn_ctlCell Bp idxJ σ1 hidxJBp (by rw [hctl]; omega),
     by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hcc]; omega⟩, ?_⟩
  rw [ctlAddr_eval, hctl]; omega

/-- `ProgramBoundedIn` for `emitNatTableProg`: the `idxJ := 0` prologue, then
    `programBoundedIn_emitListProg` at `Inv := EmitNatTableInv ... (cur + n + 1) tbl n g`, with
    the per-iteration obligation supplied by `programBoundedIn_emitNatTableBody`. `EmitNatTableInv
    ... 0` at loop entry is established the same way `emitNatTableProg_eval_state` does (via
    `emitNatProg_eval_state`'s frame fact), not by a fresh induction. -/
lemma programBoundedIn_emitNatTableProg (Bp curJ tmpJ cntJ tblJ idxJ M cur tbl n : ℕ) (g : ℕ → ℕ)
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
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblNBp : tbl + n ≤ Bp) :
    ProgramBoundedIn Bp σ (emitNatTableProg curJ tmpJ cntJ tblJ idxJ) := by
  unfold emitNatTableProg ProgramBoundedIn
  refine ⟨⟨exprBoundedIn_ctlAddr Bp idxJ σ hidxJBp (by rw [hM]; omega), by simp [ExprBoundedIn],
    by rw [ctlAddr_eval, hM]; omega⟩, ?_⟩
  have hσ'0 : (ctlAssign idxJ (Expr.const 0)).eval σ 0 = M := by
    rw [ctlAssign_zero idxJ (Expr.const 0) σ hc4, hM]
  have hσ'cur : (ctlAssign idxJ (Expr.const 0)).eval σ (M + curJ) = cur := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + curJ) (by rw [hM]; omega), hcur]
  have hσ'cnt : (ctlAssign idxJ (Expr.const 0)).eval σ (M + cntJ) = n := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + cntJ) (by rw [hM]; omega), hcnt]
  have hσ'tbl : (ctlAssign idxJ (Expr.const 0)).eval σ (M + tblJ) = tbl := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + tblJ) (by rw [hM]; omega), htbl]
  have hσ'idx : (ctlAssign idxJ (Expr.const 0)).eval σ (M + idxJ) = 0 := by
    have h := ctlAssign_eval_same idxJ (Expr.const 0) σ
    rw [hM] at h
    simpa [Expr.eval] using h
  have hσ'table : ∀ q, q < n → (ctlAssign idxJ (Expr.const 0)).eval σ (tbl + q) = g q := by
    intro q hq
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (tbl + q) (by rw [hM]; omega), htable q hq]
  set σ' := (ctlAssign idxJ (Expr.const 0)).eval σ with hσ'def
  clear_value σ'
  have hsepFull' : cur + n + 1 ≤ M + curJ := by
    have := Nat.zero_le ((List.range n).flatMap (fun k => encodeNat (g k))).length
    omega
  have hcntEval : (ctlCell cntJ).eval σ' = n := by rw [ctlCell_eval, hσ'0, hσ'cnt]
  have hsep' : cur + (ctlCell cntJ).eval σ' < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ' hc1 hc2 hct hσ'0 hσ'cur hcur1 hsep'
  rw [hcntEval] at hbits1 hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell cntJ)).eval σ' with hσ1def
  have hσ1idx : σ1 (M + idxJ) = 0 := by
    rw [hframe1 (M + idxJ) (by omega) (by omega) (Or.inr (by omega)), hσ'idx]
  have hσ1tbl : σ1 (M + tblJ) = tbl := by
    rw [hframe1 (M + tblJ) (by omega) (by omega) (Or.inr (by omega)), hσ'tbl]
  have hσ1table : ∀ q, q < n → σ1 (tbl + q) = g q := by
    intro q hq
    have hrange : cur + n + 1 ≤ tbl + q := by omega
    rw [hframe1 (tbl + q) (by omega) (by omega) (Or.inr hrange), hσ'table q hq]
  have hInv0 : EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g 0 σ1 :=
    ⟨hσ1idx, hσ1tbl, hσ1table, by rw [hcursor1]; simp⟩
  have hbody : ∀ m, m < n → ∀ τ, EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g m τ →
      τ 0 = M →
      EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g (m + 1)
        ((emitNatTableBody curJ tmpJ tblJ idxJ).eval τ) ∧
      (emitNatTableBody curJ tmpJ tblJ idxJ).eval τ 0 = M ∧
      ProgramBoundedIn Bp τ (emitNatTableBody curJ tmpJ tblJ idxJ) := by
    intro m hmn τ hInv hMτ
    exact programBoundedIn_emitNatTableBody Bp curJ tmpJ tblJ idxJ M (cur + n + 1) tbl n g τ
      hc1 hc2 hct hcb hci htb hti hbi (by omega) hsepFull hsepTmpAll hsepIdxAll hsepTblAll
      hloCur hloTmp hloIdx hcurJBp htmpJBp htblJBp hidxJBp hMcurJBp hMtmpJBp hMtblJBp hMidxJBp
      htblNBp m hmn hInv hMτ
  exact programBoundedIn_emitListProg Bp curJ tmpJ cntJ M cur n
    (emitNatTableBody curJ tmpJ tblJ idxJ) (EmitNatTableInv curJ tblJ idxJ M (cur + n + 1) tbl n g)
    σ' hc1 hc2 hct hcc hcnt2 hσ'0 hσ'cur hcur1 hσ'cnt hsepCnt hsepFull' hcurJBp htmpJBp hcntJBp
    hMcurJBp hMtmpJBp hMcntJBp (by omega) hbody hInv0

/-! ## `ProgramBoundedIn` for `emitNatTupleTableProg` (fixed-width tuple tables)

`emitNatTupleFieldsFrom`'s recursion is on the field count `k` alone, structurally shaped like
`zeroCtlCellsProg` rather than a `Program.forN` loop, so `programBoundedIn_loopEval_of_indexed_inv`
does not apply to it directly: this section's per-field lemmas below redo that induction on `k`,
then the remaining layers (`emitNatTupleFields`, `emitNatTupleBody`, `emitNatTupleTableProg`)
reuse the generic `emitListProg`-level lemmas exactly as `emitNatTableProg`'s own bounded lemmas
do. -/

/-- `ProgramBoundedIn` for `emitNatTupleFieldsFrom`'s first `k` fields: induction on `k`, reusing
    `emitNatTupleFieldsFrom_eval_state` at the smaller index `k` for the intermediate store, then
    bounding the field-`k` address expression's own intermediate values (`tbl`, `w * q`,
    `tbl + w * q`, `tbl + w * q + k`) against `Bp` via `htblQWBp`. No value bound on `g` itself
    (no `V`) is needed: the write-window bound `cur + (prefix length) + 1 ≤ Bp` for the emitted
    field comes straight from the exact cursor tracking `hcursorK` plus the top-level length bound
    (`hsep`), per `programBoundedIn_emitNatTableBody`'s own `hkey`-free reliance on that
    mechanism. -/
lemma programBoundedIn_emitNatTupleFieldsFrom (Bp curJ tmpJ tblJ idxJ M tbl w q : ℕ)
    (g : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ) (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblQWBp : tbl + w * q + w ≤ Bp) :
    ∀ k cur (σ : Store), k ≤ w → σ 0 = M → σ (M + curJ) = cur → 1 ≤ cur →
      σ (M + tblJ) = tbl → σ (M + idxJ) = q →
      (∀ t, t < k → σ (tbl + w * q + t) = g q t) →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length < M + curJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + tmpJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + idxJ →
      cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length ≤ M + tblJ →
      ProgramBoundedIn Bp σ (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k) := by
  intro k
  induction k with
  | zero =>
    intro cur σ _ _ _ _ _ _ _ _ _ _ _
    rw [emitNatTupleFieldsFrom_zero]; unfold ProgramBoundedIn; trivial
  | succ k ih =>
    intro cur σ hkw h0 hcur hcur1 htblCell hidxCell htable hsep hsepTmp hsepIdx hsepTbl
    have hkwK : k ≤ w := by omega
    have htableK : ∀ t, t < k → σ (tbl + w * q + t) = g q t := fun t ht => htable t (by omega)
    have hlenStep : ((List.range (k + 1)).flatMap (fun t => encodeNat (g q t))).length
        = ((List.range k).flatMap (fun t => encodeNat (g q t))).length + g q k + 1 := by
      have hstepList : (List.range (k + 1)).flatMap (fun t => encodeNat (g q t))
          = (List.range k).flatMap (fun t => encodeNat (g q t)) ++ encodeNat (g q k) := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hstepList, List.length_append, encodeNat_length]
      omega
    have hsepK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        < M + curJ := by omega
    have hsepTmpK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + tmpJ := by omega
    have hsepIdxK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + idxJ := by omega
    have hsepTblK : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ M + tblJ := by omega
    have hihpb := ih cur σ hkwK h0 hcur hcur1 htblCell hidxCell htableK hsepK hsepTmpK hsepIdxK
      hsepTblK
    obtain ⟨_, hcursorK, h0K, hidxK, htblK, hframeK⟩ :=
      emitNatTupleFieldsFrom_eval_state curJ tmpJ tblJ idxJ M tbl w q g
        hc1 hc2 hct hcb hci htb hti hloCur hloTmp k cur σ
        h0 hcur hcur1 htblCell hidxCell htableK hsepK hsepTmpK hsepIdxK hsepTblK
    set σK := (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w k).eval σ with hσKdef
    have hkAddr_ge : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        ≤ tbl + w * q + k := by omega
    have hfieldCurNe : tbl + w * q + k ≠ M + curJ := by omega
    have hfieldTmpNe : tbl + w * q + k ≠ M + tmpJ := by omega
    have hfieldVal : σK (tbl + w * q + k) = g q k := by
      rw [hframeK (tbl + w * q + k) hfieldCurNe hfieldTmpNe (Or.inr hkAddr_ge)]
      exact htable k (by omega)
    have htblEval : (ctlCell tblJ).eval σK = tbl := by rw [ctlCell_eval, h0K, htblK]
    have hidxEval : (ctlCell idxJ).eval σK = q := by rw [ctlCell_eval, h0K, hidxK]
    have hEeval : (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k)).eval σK = tbl + w * q + k := by
      simp [Expr.eval, htblEval, hidxEval]
    have haddrEval : (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK = g q k := by
      have h1 : (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
          (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK
          = σK ((Expr.add (Expr.add (ctlCell tblJ)
            (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k)).eval σK) := rfl
      rw [h1, hEeval]; exact hfieldVal
    have hkBp : k ≤ Bp := by omega
    have hwBp : w ≤ Bp := by omega
    have haddrBp : tbl + w * q + k ≤ Bp := by omega
    have hmulBp : w * q ≤ Bp := by omega
    have haddBp : tbl + w * q ≤ Bp := by omega
    have hA : ExprBoundedIn Bp σK (ctlCell tblJ) :=
      exprBoundedIn_ctlCell Bp tblJ σK htblJBp (by rw [h0K]; omega)
    have hidxAddr : ExprBoundedIn Bp σK (ctlCell idxJ) :=
      exprBoundedIn_ctlCell Bp idxJ σK hidxJBp (by rw [h0K]; omega)
    have hB : ExprBoundedIn Bp σK (Expr.mul (Expr.const w) (ctlCell idxJ)) := by
      refine ⟨hwBp, hidxAddr, ?_⟩
      simp only [Expr.eval]; rw [hidxEval]; exact hmulBp
    have hC : ExprBoundedIn Bp σK (Expr.add (ctlCell tblJ) (Expr.mul (Expr.const w)
        (ctlCell idxJ))) := by
      refine ⟨hA, hB, ?_⟩
      simp only [Expr.eval]; rw [htblEval, hidxEval]; exact haddBp
    have he_ebi : ExprBoundedIn Bp σK (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))) := by
      refine ⟨⟨hC, hkBp, ?_⟩, ?_⟩
      · simp only [Expr.eval]; rw [htblEval, hidxEval]; omega
      · rw [hEeval]; exact haddrBp
    have hcur_running1 : 1 ≤ cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length := by
      omega
    have hsep_field : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        + (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
          (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK < M + curJ := by
      rw [haddrEval]; omega
    have hcurEBp : cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length
        + (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
          (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))).eval σK + 1 ≤ Bp := by
      rw [haddrEval]; omega
    have hfieldpb := programBoundedIn_emitNatProg Bp curJ tmpJ M
      (cur + ((List.range k).flatMap (fun t => encodeNat (g q t))).length)
      (Expr.regInd (Expr.add (Expr.add (ctlCell tblJ)
        (Expr.mul (Expr.const w) (ctlCell idxJ))) (Expr.const k))) σK
      hc1 hc2 hct h0K hcursorK hcur_running1 hsep_field he_ebi hcurJBp htmpJBp hMcurJBp hMtmpJBp
      hcurEBp
    clear_value σK
    rw [emitNatTupleFieldsFrom_succ]
    unfold ProgramBoundedIn
    rw [← hσKdef]
    exact ⟨hihpb, hfieldpb⟩

/-- `ProgramBoundedIn` for `emitNatTupleFields`: `programBoundedIn_emitNatTupleFieldsFrom` at
    `k := w`. -/
lemma programBoundedIn_emitNatTupleFields (Bp curJ tmpJ tblJ idxJ M tbl w q : ℕ) (g : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ)
    (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ) (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblQWBp : tbl + w * q + w ≤ Bp)
    (cur : ℕ) (σ : Store) (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (htblCell : σ (M + tblJ) = tbl) (hidxCell : σ (M + idxJ) = q)
    (hentry : ∀ t, t < w → σ (tbl + w * q + t) = g q t)
    (hsep : cur + ((List.range w).flatMap (fun t => encodeNat (g q t))).length < M + curJ)
    (hsepTmp : cur + ((List.range w).flatMap (fun t => encodeNat (g q t))).length ≤ M + tmpJ)
    (hsepIdx : cur + ((List.range w).flatMap (fun t => encodeNat (g q t))).length ≤ M + idxJ)
    (hsepTbl : cur + ((List.range w).flatMap (fun t => encodeNat (g q t))).length ≤ M + tblJ) :
    ProgramBoundedIn Bp σ (emitNatTupleFields curJ tmpJ tblJ idxJ w) := by
  have hfields : emitNatTupleFields curJ tmpJ tblJ idxJ w
      = emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w := rfl
  rw [hfields]
  exact programBoundedIn_emitNatTupleFieldsFrom Bp curJ tmpJ tblJ idxJ M tbl w q g
    hc1 hc2 hct hcb hci htb hti hloCur hloTmp hcurJBp htmpJBp htblJBp hidxJBp hMcurJBp
    hMtmpJBp hMtblJBp hMidxJBp htblQWBp w cur σ (le_refl w) hM hcur hcur1 htblCell hidxCell hentry
    hsep hsepTmp hsepIdx hsepTbl

/-- `ProgramBoundedIn` for `emitNatTupleBody`: `programBoundedIn_emitNatTupleFields` for the field
    emission, then the trailing index-advance `ctlAssign`, whose written value `idx + 1` needs its
    own explicit bound `hidx1Bp` (unlike the field addresses, `idx`'s own magnitude is not pinned
    down by any address-style separation hypothesis here). Mirrors
    `programBoundedIn_emitNatTableBody`'s trailing-`ctlAssign` half exactly, reusing
    `emitNatTupleFieldsFrom_eval_state` (at `k := w`, discarding the bits/cursor/frame components
    this half does not need) for the post-fields store facts. -/
lemma programBoundedIn_emitNatTupleBody (Bp curJ tmpJ tblJ idxJ M cur tbl w idx : ℕ)
    (g : ℕ → ℕ → ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hct : curJ ≠ tmpJ) (hcb : curJ ≠ tblJ) (hci : curJ ≠ idxJ)
    (htb : tmpJ ≠ tblJ) (hti : tmpJ ≠ idxJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (htblCell : σ (M + tblJ) = tbl) (hidxCell : σ (M + idxJ) = idx)
    (hentry : ∀ t, t < w → σ (tbl + w * idx + t) = g idx t)
    (hsep : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length < M + curJ)
    (hsepTmp : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + tmpJ)
    (hsepIdx : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + idxJ)
    (hsepTbl : cur + ((List.range w).flatMap (fun t => encodeNat (g idx t))).length ≤ M + tblJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblQWBp : tbl + w * idx + w ≤ Bp) (hidx1Bp : idx + 1 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitNatTupleBody curJ tmpJ tblJ idxJ w) := by
  unfold emitNatTupleBody ProgramBoundedIn
  have hfieldspb := programBoundedIn_emitNatTupleFields Bp curJ tmpJ tblJ idxJ M tbl w idx g
    hc1 hc2 hct hcb hci htb hti hloCur hloTmp hcurJBp htmpJBp htblJBp hidxJBp hMcurJBp
    hMtmpJBp hMtblJBp hMidxJBp htblQWBp cur σ hM hcur hcur1 htblCell hidxCell hentry
    hsep hsepTmp hsepIdx hsepTbl
  refine ⟨hfieldspb, ?_⟩
  obtain ⟨_, _, hctl, hσ1idx, _, _⟩ :=
    emitNatTupleFieldsFrom_eval_state curJ tmpJ tblJ idxJ M tbl w idx g
      hc1 hc2 hct hcb hci htb hti hloCur hloTmp w cur σ
      hM hcur hcur1 htblCell hidxCell hentry hsep hsepTmp hsepIdx hsepTbl
  set σ1 := (emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w).eval σ with hσ1def
  have hfields : emitNatTupleFields curJ tmpJ tblJ idxJ w
      = emitNatTupleFieldsFrom curJ tmpJ tblJ idxJ w w := rfl
  rw [hfields, ← hσ1def]
  clear_value σ1
  unfold ctlAssign ProgramBoundedIn
  have hcc : (ctlCell idxJ).eval σ1 = idx := by rw [ctlCell_eval, hctl, hσ1idx]
  refine ⟨exprBoundedIn_ctlAddr Bp idxJ σ1 hidxJBp (by rw [hctl]; omega),
    ⟨exprBoundedIn_ctlCell Bp idxJ σ1 hidxJBp (by rw [hctl]; omega),
     by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hcc]; omega⟩, ?_⟩
  rw [ctlAddr_eval, hctl]; omega

/-- Per-iteration `ProgramBoundedIn` fact for `emitNatTupleBody` under `EmitNatTupleTableInv`.
    Reuses `emitNatTupleTableProg_hbody` for the invariant-advance/cell-`0` facts, and the same
    `flatMap_range_length_split` computation to place entry `m`'s write window inside the global
    length wall. The two address-magnitude
    bounds `programBoundedIn_emitNatTupleBody` needs beyond that wall (`tbl + w * m + w ≤ Bp` and
    `m + 1 ≤ Bp`) come from the table-wide `htblNWBp`/`hnBp` via `Nat.mul_le_mul_left` (turning
    `w * (m + 1) ≤ w * n` into the additive shape `tbl + w * m + w ≤ Bp` needs, per the module's
    `ring`-then-`omega` convention for such nonlinear steps) and `hmn` respectively. -/
lemma programBoundedIn_emitNatTupleBody_of_inv (Bp curJ tmpJ tblJ idxJ M cur0 tbl n w : ℕ)
    (g : ℕ → ℕ → ℕ) (τ : Store)
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
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblNWBp : tbl + w * n ≤ Bp) (hnBp : n ≤ Bp)
    (m : ℕ) (hmn : m < n) (hInv : EmitNatTupleTableInv curJ tblJ idxJ M cur0 tbl n w g m τ)
    (hM : τ 0 = M) :
    EmitNatTupleTableInv curJ tblJ idxJ M cur0 tbl n w g (m + 1)
      ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) ∧
    (emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ 0 = M ∧
    ProgramBoundedIn Bp τ (emitNatTupleBody curJ tmpJ tblJ idxJ w) := by
  obtain ⟨hidxCell, htblCell, htable, hcurpin⟩ := hInv
  obtain ⟨_, _, hctl0, _, hInv'⟩ :=
    emitNatTupleTableProg_hbody curJ tmpJ tblJ idxJ M cur0 tbl n w g
      hc1 hc2 hct hcb hci htb hti hbi hcur01 hsepFull hsepTmpAll hsepIdxAll hsepTblAll
      hloCur hloTmp hloIdx m hmn τ (τ (M + curJ)) ⟨hidxCell, htblCell, htable, hcurpin⟩ hM rfl
  refine ⟨hInv', hctl0, ?_⟩
  have hkey : τ (M + curJ) + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
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
    rw [hcurpin]; omega
  have hsep_v : τ (M + curJ) + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      < M + curJ := by omega
  have hsepTmp_v : τ (M + curJ) + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + tmpJ := by omega
  have hsepIdx_v : τ (M + curJ) + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + idxJ := by omega
  have hsepTbl_v : τ (M + curJ) + ((List.range w).flatMap (fun t => encodeNat (g m t))).length
      ≤ M + tblJ := by omega
  have hcur'1 : 1 ≤ τ (M + curJ) := by omega
  have hentry : ∀ t, t < w → τ (tbl + w * m + t) = g m t := fun t ht => htable m t hmn ht
  have hmono : w * (m + 1) ≤ w * n := Nat.mul_le_mul_left w (by omega)
  have heq : w * (m + 1) = w * m + w := by ring
  have htblQWBp : tbl + w * m + w ≤ Bp := by omega
  have hidx1Bp : m + 1 ≤ Bp := by omega
  exact programBoundedIn_emitNatTupleBody Bp curJ tmpJ tblJ idxJ M (τ (M + curJ)) tbl w m g τ
    hc1 hc2 hct hcb hci htb hti hM rfl hcur'1 htblCell hidxCell hentry
    hsep_v hsepTmp_v hsepIdx_v hsepTbl_v hloCur hloTmp
    hcurJBp htmpJBp htblJBp hidxJBp hMcurJBp hMtmpJBp hMtblJBp hMidxJBp htblQWBp hidx1Bp

/-- `ProgramBoundedIn` for `emitNatTupleTableProg`: the `idxJ := 0` prologue, then
    `programBoundedIn_emitListProg` at `Inv := EmitNatTupleTableInv ... (cur + n + 1) tbl n w g`,
    with the per-iteration obligation supplied by `programBoundedIn_emitNatTupleBody_of_inv`.
    `EmitNatTupleTableInv ... 0` at loop entry is established the same way
    `emitNatTupleTableProg_eval_state` does (via `emitNatProg_eval_state`'s frame fact), not by a
    fresh induction — exactly as `programBoundedIn_emitNatTableProg` does for the one-`Nat`-per-
    entry table. -/
lemma programBoundedIn_emitNatTupleTableProg (Bp curJ tmpJ cntJ tblJ idxJ M cur tbl n w : ℕ)
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
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl) (hloIdx : M + idxJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (htblJBp : tblJ ≤ Bp) (hidxJBp : idxJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp) (hMidxJBp : M + idxJ ≤ Bp)
    (htblNWBp : tbl + w * n ≤ Bp) (hnBp : n ≤ Bp) :
    ProgramBoundedIn Bp σ (emitNatTupleTableProg curJ tmpJ cntJ tblJ idxJ w) := by
  unfold emitNatTupleTableProg ProgramBoundedIn
  refine ⟨⟨exprBoundedIn_ctlAddr Bp idxJ σ hidxJBp (by rw [hM]; omega), by simp [ExprBoundedIn],
    by rw [ctlAddr_eval, hM]; omega⟩, ?_⟩
  have hσ'0 : (ctlAssign idxJ (Expr.const 0)).eval σ 0 = M := by
    rw [ctlAssign_zero idxJ (Expr.const 0) σ hc4, hM]
  have hσ'cur : (ctlAssign idxJ (Expr.const 0)).eval σ (M + curJ) = cur := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + curJ) (by rw [hM]; omega), hcur]
  have hσ'cnt : (ctlAssign idxJ (Expr.const 0)).eval σ (M + cntJ) = n := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + cntJ) (by rw [hM]; omega), hcnt]
  have hσ'tbl : (ctlAssign idxJ (Expr.const 0)).eval σ (M + tblJ) = tbl := by
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (M + tblJ) (by rw [hM]; omega), htbl]
  have hσ'idx : (ctlAssign idxJ (Expr.const 0)).eval σ (M + idxJ) = 0 := by
    have h := ctlAssign_eval_same idxJ (Expr.const 0) σ
    rw [hM] at h
    simpa [Expr.eval] using h
  have hσ'table : ∀ q t, q < n → t < w →
      (ctlAssign idxJ (Expr.const 0)).eval σ (tbl + w * q + t) = g q t := by
    intro q t hq ht
    rw [ctlAssign_eval_diff idxJ (Expr.const 0) σ (tbl + w * q + t) (by omega), htable q t hq ht]
  set σ' := (ctlAssign idxJ (Expr.const 0)).eval σ with hσ'def
  clear_value σ'
  have hsepFull' : cur + n + 1 ≤ M + curJ := by
    have hlen0 : (0 : ℕ) ≤ ((List.range n).flatMap
      (fun i => (List.range w).flatMap (fun t => encodeNat (g i t)))).length := Nat.zero_le _
    omega
  have hcntEval : (ctlCell cntJ).eval σ' = n := by rw [ctlCell_eval, hσ'0, hσ'cnt]
  have hsep' : cur + (ctlCell cntJ).eval σ' < M + curJ := by rw [hcntEval]; omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ' hc1 hc2 hct hσ'0 hσ'cur hcur1 hsep'
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
  have hbody : ∀ m, m < n → ∀ τ,
      EmitNatTupleTableInv curJ tblJ idxJ M (cur + n + 1) tbl n w g m τ → τ 0 = M →
      EmitNatTupleTableInv curJ tblJ idxJ M (cur + n + 1) tbl n w g (m + 1)
        ((emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ) ∧
      (emitNatTupleBody curJ tmpJ tblJ idxJ w).eval τ 0 = M ∧
      ProgramBoundedIn Bp τ (emitNatTupleBody curJ tmpJ tblJ idxJ w) := by
    intro m hmn τ hInv hMτ
    exact programBoundedIn_emitNatTupleBody_of_inv Bp curJ tmpJ tblJ idxJ M (cur + n + 1) tbl n w g
      τ hc1 hc2 hct hcb hci htb hti hbi (by omega) hsepFull hsepTmpAll hsepIdxAll hsepTblAll
      hloCur hloTmp hloIdx hcurJBp htmpJBp htblJBp hidxJBp hMcurJBp hMtmpJBp hMtblJBp hMidxJBp
      htblNWBp hnBp m hmn hInv hMτ
  exact programBoundedIn_emitListProg Bp curJ tmpJ cntJ M cur n
    (emitNatTupleBody curJ tmpJ tblJ idxJ w)
    (EmitNatTupleTableInv curJ tblJ idxJ M (cur + n + 1) tbl n w g)
    σ' hc1 hc2 hct hcc hcnt2 hσ'0 hσ'cur hcur1 hσ'cnt hsepCnt hsepFull' hcurJBp htmpJBp hcntJBp
    hMcurJBp hMtmpJBp hMcntJBp (by omega) hbody hInv0

/-! ## `ProgramBoundedIn` for the variable-length row table (`emitRowTableProg`)

`emitNatTupleTableProg`'s toolkit assumes a fixed per-entry width; `emitRowTableProg`
(`CanonicalStoreFinalize.lean`) is variable-length at both levels: each row's tagged entry list has
a data-dependent length, and rows themselves are looped by `emitListProg`, just as
`emitOpsListProg` loops `emitRawOpBody` once per entry. The bound is built through four layers
already defined in `CanonicalStoreFinalize.lean`: `emitRawOpBody` (one entry), `emitOpsListProg`
(a row's entry list, `emitListProg` over `emitRawOpBody`), `emitRowBody` (one whole row), and
`emitRowTableProg` (the whole table, `emitListProg` over `emitRowBody`). Each layer's own
`_hbody`/`_eval_state`/`_state_upto_ptr` correctness lemma tracks the state; this file adds the
`ProgramBoundedIn` computation at each layer. -/

/-- `ProgramBoundedIn` for `emitRawOpBody`: this needs no ceiling on the value `d` itself
    (`.assignInd`'s `ExprBoundedIn` checks dereferenced addresses, not the value being written —
    see the `ExprBoundedIn` docstring in `CompileExecBounded.lean`), but it does need
    `ptr + 2 ≤ Bp` (the entry's address family, `ptr`, `ptr + 1`, and `ptr + 2`, stays in the
    tracked region), `cur + d + 2 ≤ Bp` (the write window of `emitNatProg`'s loop), and
    `tmpJ ≠ ptrJ`, since `programBoundedIn_emitNatProg` reads the pointer's control cell through
    that separation argument. -/
lemma programBoundedIn_emitRawOpBody (Bp curJ tmpJ ptrJ M cur ptr d : ℕ) (σ : Store)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ) (hct : curJ ≠ tmpJ) (hcp : curJ ≠ ptrJ) (htp : tmpJ ≠ ptrJ)
    (hM : σ 0 = M) (hcur : σ (M + curJ) = cur) (hcur1 : 1 ≤ cur)
    (hptrCell : σ (M + ptrJ) = ptr) (hdata : σ (ptr + 1) = d)
    (hloCur : M + curJ < ptr)
    (hsep : cur + 1 + d < M + curJ) (hsepPtr : cur + 1 + d + 1 ≤ M + ptrJ)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hptrJBp : ptrJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMptrJBp : M + ptrJ ≤ Bp)
    (hptr2Bp : ptr + 2 ≤ Bp) (hworkBp : cur + d + 2 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitRawOpBody curJ tmpJ ptrJ) := by
  have hcur0 : cur ≠ 0 := by omega
  have hcurNe : cur ≠ M + curJ := by omega
  have hv : ExprBoundedIn Bp σ (Expr.regInd (ctlCell ptrJ)) := by
    refine ⟨exprBoundedIn_ctlCell Bp ptrJ σ hptrJBp (by rw [hM]; omega), ?_⟩
    rw [ctlCell_eval, hM, hptrCell]; omega
  have hPB_A : ProgramBoundedIn Bp σ (emitBitProg curJ (Expr.regInd (ctlCell ptrJ))) :=
    programBoundedIn_emitBitProg Bp curJ M cur (Expr.regInd (ctlCell ptrJ)) σ
      hM hcur hcur0 hcurNe hv hcurJBp hMcurJBp (by omega) (by omega)
  have hσ1ctl : ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) 0 = M :=
    emitBitProg_ctl curJ M cur _ σ hc1 hM hcur hcur0 hcurNe
  have hσ1cursor : ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) (M + curJ) = cur + 1 :=
    emitBitProg_cursor curJ M cur _ σ hM hcur hcur0 hcurNe
  have hσ1frame := emitBitProg_frame curJ M cur (Expr.regInd (ctlCell ptrJ)) σ hM hcur hcur0 hcurNe
  have hσ1ptr : ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) (M + ptrJ) = ptr := by
    rw [hσ1frame (M + ptrJ) (by omega) (by omega)]; exact hptrCell
  have hσ1ptr1 : ((emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ) (ptr + 1) = d := by
    rw [hσ1frame (ptr + 1) (by omega) (by omega)]; exact hdata
  set σ1 := (emitBitProg curJ (Expr.regInd (ctlCell ptrJ))).eval σ with hσ1def
  have heval2 : (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1 = d := by
    have h1 : (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1
        = σ1 (σ1 (σ1 0 + ptrJ) + 1) := by simp [Expr.eval, ctlCell_eval]
    rw [h1, hσ1ctl, hσ1ptr]; exact hσ1ptr1
  have hval1 : (ctlCell ptrJ).eval σ1 = ptr := by rw [ctlCell_eval, hσ1ctl, hσ1ptr]
  have he : ExprBoundedIn Bp σ1 (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))) := by
    refine ⟨⟨exprBoundedIn_ctlCell Bp ptrJ σ1 hptrJBp (by rw [hσ1ctl]; omega),
      by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hval1]; omega⟩, ?_⟩
    simp [Expr.eval, hval1]; omega
  have hsep' : cur + 1 + (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))).eval σ1
      < M + curJ := by rw [heval2]; omega
  have hPB_B : ProgramBoundedIn Bp σ1 (emitNatProg curJ tmpJ
      (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1)))) :=
    programBoundedIn_emitNatProg Bp curJ tmpJ M (cur + 1)
      (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))) σ1
      hc1 hc2 hct hσ1ctl hσ1cursor (by omega) hsep' he
      hcurJBp htmpJBp hMcurJBp hMtmpJBp (by rw [heval2]; omega)
  obtain ⟨-, hcursor2, hframe2, hctl2⟩ :=
    emitNatProg_eval_state curJ tmpJ M (cur + 1)
      (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1))) σ1
      hc1 hc2 hct hσ1ctl hσ1cursor (by omega) hsep'
  rw [heval2] at hcursor2 hframe2
  set σ2 := (emitNatProg curJ tmpJ
    (Expr.regInd (Expr.add (ctlCell ptrJ) (Expr.const 1)))).eval σ1 with hσ2def
  have hσ2ptr : σ2 (M + ptrJ) = ptr := by
    rw [hframe2 (M + ptrJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσ1ptr
  have hPB_C :
      ProgramBoundedIn Bp σ2 (ctlAssign ptrJ (Expr.add (ctlCell ptrJ) (Expr.const 2))) := by
    unfold ctlAssign ProgramBoundedIn
    have hval2 : (ctlCell ptrJ).eval σ2 = ptr := by rw [ctlCell_eval, hctl2, hσ2ptr]
    refine ⟨exprBoundedIn_ctlAddr Bp ptrJ σ2 hptrJBp (by rw [hctl2]; omega),
      ⟨exprBoundedIn_ctlCell Bp ptrJ σ2 hptrJBp (by rw [hctl2]; omega),
        by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hval2]; omega⟩, ?_⟩
    rw [ctlAddr_eval, hctl2]; omega
  unfold emitRawOpBody ProgramBoundedIn
  refine ⟨⟨hPB_A, ?_⟩, ?_⟩
  · rw [← hσ1def]; exact hPB_B
  · rw [eval_seq, ← hσ1def, ← hσ2def]; exact hPB_C

/-- Per-iteration `ProgramBoundedIn` fact for `emitRawOpBody`. Reuses `emitOpsListProg_hbody` for
    the invariant-advance/cell-`0` facts, the same `hkey` peeling technique for the positional
    separation facts (`hloCurPtr`/`hsep'`/`hsepPtr'`), and needs no ceiling on any data
    value: `hrowWidthBp` (the whole row's own physical width `≤ Bp`) supplies the address bound
    `emitRawOpBody`'s own address family (`ptr`, `ptr + 1`, `ptr + 2`) needs, and `hMcurJBp`
    combined with `hsep'` already forces the write window `≤ Bp` (`programBoundedIn_emitRawOpBody`'s
    own `hworkBp`), matching `programBoundedIn_emitRawOpBody`'s docstring. -/
lemma programBoundedIn_emitRawOpBody_of_inv (Bp curJ tmpJ ptrJ M cur0 rowBase cnt : ℕ)
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
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hptrJBp : ptrJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMptrJBp : M + ptrJ ≤ Bp)
    (hrowWidthBp : rowBase + 2 * cnt + 2 ≤ Bp)
    (m : ℕ) (hmcnt : m < cnt) (τ : Store)
    (hInv : EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d m τ) (hM : τ 0 = M) :
    EmitOpsListInv curJ ptrJ M cur0 rowBase cnt tag d (m + 1)
      ((emitRawOpBody curJ tmpJ ptrJ).eval τ) ∧
    (emitRawOpBody curJ tmpJ ptrJ).eval τ 0 = M ∧
    ProgramBoundedIn Bp τ (emitRawOpBody curJ tmpJ ptrJ) := by
  obtain ⟨hptrCell, htagAll, hdataAll, hcurpin⟩ := hInv
  obtain ⟨_, _, hctl0, _, hInv'⟩ :=
    emitOpsListProg_hbody curJ tmpJ ptrJ M cur0 rowBase cnt tag d
      hc1 hc2 hct hcp htp hcur01 hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
      m hmcnt τ (τ (M + curJ)) ⟨hptrCell, htagAll, hdataAll, hcurpin⟩ hM rfl
  refine ⟨hInv', hctl0, ?_⟩
  have hloCurPtr : M + curJ < rowBase + 2 + 2 * m := by omega
  have hkey : τ (M + curJ) + (d m + 2)
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
    have hlenM : ([tag m] ++ encodeNat (d m)).length = d m + 2 := by simp [encodeNat_length]
    rw [hlenM] at hlen_remaining
    rw [hcurpin]
    omega
  have hcur1' : 1 ≤ τ (M + curJ) := by omega
  have hsep' : τ (M + curJ) + 1 + d m < M + curJ := by omega
  have hsepPtr' : τ (M + curJ) + 1 + d m + 1 ≤ M + ptrJ := by omega
  have hptr2Bp' : rowBase + 2 + 2 * m + 2 ≤ Bp := by omega
  have hworkBp' : τ (M + curJ) + d m + 2 ≤ Bp := by omega
  exact programBoundedIn_emitRawOpBody Bp curJ tmpJ ptrJ M (τ (M + curJ)) (rowBase + 2 + 2 * m)
    (d m) τ hc1 hc2 hct hcp htp hM rfl hcur1' hptrCell (hdataAll m hmcnt) hloCurPtr hsep'
    hsepPtr' hcurJBp htmpJBp hptrJBp hMcurJBp hMtmpJBp hMptrJBp hptr2Bp' hworkBp'

/-- `ProgramBoundedIn` for `emitOpsListProg`: a direct `programBoundedIn_emitListProg`
    instantiation, needing no value ceiling but an explicit bound `hrowWidthBp` on the row's own
    physical width (every entry's address family stays inside it) and `hcurNBp` on the
    length-prefix's own write window, mirroring `programBoundedIn_emitNatTableProg`'s two-bound
    convention. -/
lemma programBoundedIn_emitOpsListProg (Bp curJ tmpJ cntJ ptrJ M cur rowBase cnt : ℕ)
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
    (hloCur : M + curJ < rowBase) (hloTmp : M + tmpJ < rowBase) (hloPtr : M + ptrJ < rowBase)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp) (hptrJBp : ptrJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMptrJBp : M + ptrJ ≤ Bp)
    (hcurNBp : cur + cnt + 1 ≤ Bp) (hrowWidthBp : rowBase + 2 * cnt + 2 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitOpsListProg curJ tmpJ cntJ ptrJ) := by
  have hcntEval : (ctlCell cntJ).eval σ = cnt := by rw [ctlCell_eval, hM, hcnt]
  have hsep' : cur + (ctlCell cntJ).eval σ < M + curJ := by
    rw [hcntEval]
    have : (0 : ℕ) ≤ ((List.range cnt).flatMap
      (fun i => [tag i] ++ encodeNat (d i))).length := Nat.zero_le _
    omega
  obtain ⟨hbits1, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell cntJ) σ hc1 hc2 hct hM hcur hcur1 hsep'
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
  have hbody : ∀ m, m < cnt → ∀ τ,
      EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d m τ → τ 0 = M →
      EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d (m + 1)
        ((emitRawOpBody curJ tmpJ ptrJ).eval τ) ∧
      (emitRawOpBody curJ tmpJ ptrJ).eval τ 0 = M ∧
      ProgramBoundedIn Bp τ (emitRawOpBody curJ tmpJ ptrJ) := by
    intro m hmcnt τ hInv hMτ
    exact programBoundedIn_emitRawOpBody_of_inv Bp curJ tmpJ ptrJ M (cur + cnt + 1) rowBase cnt
      tag d hc1 hc2 hct hcp htp (by omega) hsepFull hsepTmpAll hsepPtrAll hloCur hloTmp hloPtr
      hcurJBp htmpJBp hptrJBp hMcurJBp hMtmpJBp hMptrJBp hrowWidthBp m hmcnt τ hInv hMτ
  have hsepFull' : cur + cnt + 1 ≤ M + curJ := by
    have : (0 : ℕ) ≤ ((List.range cnt).flatMap
      (fun i => [tag i] ++ encodeNat (d i))).length := Nat.zero_le _
    omega
  exact programBoundedIn_emitListProg Bp curJ tmpJ cntJ M cur cnt (emitRawOpBody curJ tmpJ ptrJ)
    (EmitOpsListInv curJ ptrJ M (cur + cnt + 1) rowBase cnt tag d) σ
    hc1 hc2 hct hcc hcnt2 hM hcur hcur1 hcnt hsepCnt hsepFull'
    hcurJBp htmpJBp hcntJBp hMcurJBp hMtmpJBp hMcntJBp hcurNBp hbody hInv0

/-! ## `ProgramBoundedIn` for `emitRowBody` (one whole variable-length row)

`emitRowBody` chains five pieces (`ctlAssign cntJ ...`, `emitNatProg` for the row key,
`ctlAssign ptrJ ...`, `emitOpsListProg` for the tagged payload list, `ctlAssign rowJ ...`), three
of which (`ctlAssign`) have store-independent structural shape — only the row-key emission and
the payload-list emission genuinely depend on the store. `emitRowBody_state_upto_ptr` already
bridges the first three pieces to a named store `σC`; the lemma below reuses it for that bridging
rather than re-deriving it, adding only the row key's own value (`e2.eval σA = rowKey`, not
exposed by that lemma, so redone here the same small way `emitRowBody_eval_state` itself does)
and the bound computation. -/

/-- `ProgramBoundedIn` for `emitRowBody`. This needs no value ceiling on `rowKey` or on any
    entry value — `.assignInd`'s `ExprBoundedIn` never inspects the value it writes
    (`programBoundedIn_emitRawOpBody`'s docstring) — only address bounds: `hrowJBp` supplies the
    `ctlAssign`-piece addresses (`M + rowJ`, `M + cntJ`, `M + ptrJ`), and `hrowWidthBp` (the row's
    physical width `≤ Bp`) supplies the sums `row + 1 ≤ Bp` / `row + 2 ≤ Bp` checked by those
    pieces' `Expr.add` nodes. The final `ctlAssign rowJ (ctlCell ptrJ)` piece needs neither: its
    written value (the next row's head) is never inspected, only the read address `M + ptrJ`
    (already `≤ Bp`). -/
lemma programBoundedIn_emitRowBody (Bp curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt : ℕ)
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
      + ((List.range cnt).flatMap (fun i => [tag i] ++ encodeNat (d i))).length ≤ M + rowJ)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMptrJBp : M + ptrJ ≤ Bp) (hMrowJBp : M + rowJ ≤ Bp)
    (hrowWidthBp : row + 2 * cnt + 2 ≤ Bp) :
    ProgramBoundedIn Bp σ (emitRowBody curJ tmpJ cntJ ptrJ rowJ) := by
  obtain ⟨σC, hCcur, hC0, hCcnt, hCptr, hCtag, hCdata, hCeq, -⟩ :=
    emitRowBody_state_upto_ptr curJ tmpJ cntJ ptrJ rowJ M cur row rowKey cnt tag d σ
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hM hcur hcur1 hrowCell hrowKey hcntCell htagAll hdataAll
      hloCur hloTmp hloCnt hloPtr hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
  have hσA0 : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ 0
      = M := by
    rw [ctlAssign_eval_diff cntJ _ σ 0 (by omega)]; exact hM
  have hσArow : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + rowJ) = row := by
    rw [ctlAssign_eval_diff cntJ _ σ (M + rowJ) (by omega)]; exact hrowCell
  have hσAcur : (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
      (M + curJ) = cur := by
    rw [ctlAssign_eval_diff cntJ _ σ (M + curJ) (by omega)]; exact hcur
  have hval1 : (ctlCell rowJ).eval σ = row := by rw [ctlCell_eval, hM, hrowCell]
  have he1 : ExprBoundedIn Bp σ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))) := by
    refine ⟨⟨exprBoundedIn_ctlCell Bp rowJ σ hrowJBp (by rw [hM]; omega),
      by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hval1]; omega⟩, ?_⟩
    simp [Expr.eval, hval1]; omega
  have hPB1 :
      ProgramBoundedIn Bp σ (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1))))
      := by
    unfold ProgramBoundedIn ctlAssign
    refine ⟨exprBoundedIn_ctlAddr Bp cntJ σ hcntJBp (by rw [hM]; omega), he1, ?_⟩
    rw [ctlAddr_eval, hM]; omega
  set σA := (ctlAssign cntJ (Expr.regInd (Expr.add (ctlCell rowJ) (Expr.const 1)))).eval σ
    with hσAdef
  have hexprB : (Expr.regInd (ctlCell rowJ)).eval σA = rowKey := by
    have h1 : (Expr.regInd (ctlCell rowJ)).eval σA = σA (σA (σA 0 + rowJ)) := by
      simp [Expr.eval, ctlCell_eval]
    rw [h1, hσA0, hσArow]
    rw [hσAdef, ctlAssign_eval_diff cntJ _ σ row (by omega)]; exact hrowKey
  have he2 : ExprBoundedIn Bp σA (Expr.regInd (ctlCell rowJ)) := by
    refine ⟨exprBoundedIn_ctlCell Bp rowJ σA hrowJBp (by rw [hσA0]; omega), ?_⟩
    rw [ctlCell_eval, hσA0, hσArow]; omega
  have hsepB : cur + (Expr.regInd (ctlCell rowJ)).eval σA < M + curJ := by rw [hexprB]; omega
  have hPB2 : ProgramBoundedIn Bp σA (emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))) :=
    programBoundedIn_emitNatProg Bp curJ tmpJ M cur (Expr.regInd (ctlCell rowJ)) σA
      hc1 hc2 hCurTmp hσA0 hσAcur hcur1 hsepB he2
      hcurJBp htmpJBp hMcurJBp hMtmpJBp (by rw [hexprB]; omega)
  obtain ⟨-, hcursorB, hframeB, hctlB⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (Expr.regInd (ctlCell rowJ)) σA
      hc1 hc2 hCurTmp hσA0 hσAcur hcur1 hsepB
  rw [hexprB] at hcursorB hframeB
  have hσBrow : ((emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval σA) (M + rowJ)
      = row := by
    rw [hframeB (M + rowJ) (by omega) (by omega) (Or.inr (by omega))]; exact hσArow
  set σB := (emitNatProg curJ tmpJ (Expr.regInd (ctlCell rowJ))).eval σA with hσBdef
  have hval3 : (ctlCell rowJ).eval σB = row := by rw [ctlCell_eval, hctlB, hσBrow]
  have he3 : ExprBoundedIn Bp σB (Expr.add (ctlCell rowJ) (Expr.const 2)) := by
    refine ⟨exprBoundedIn_ctlCell Bp rowJ σB hrowJBp (by rw [hctlB]; omega),
      by simp only [ExprBoundedIn]; omega, by simp [Expr.eval, hval3]; omega⟩
  have hPB3 : ProgramBoundedIn Bp σB (ctlAssign ptrJ (Expr.add (ctlCell rowJ) (Expr.const 2))) := by
    unfold ProgramBoundedIn ctlAssign
    refine ⟨exprBoundedIn_ctlAddr Bp ptrJ σB hptrJBp (by rw [hctlB]; omega), he3, ?_⟩
    rw [ctlAddr_eval, hctlB]; omega
  have hPB4 : ProgramBoundedIn Bp σC (emitOpsListProg curJ tmpJ cntJ ptrJ) :=
    programBoundedIn_emitOpsListProg Bp curJ tmpJ cntJ ptrJ M (cur + rowKey + 1) row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hC0 hCcur (by omega) hCcnt hCptr hCtag hCdata
      (by omega) (by omega) (by omega) (by omega) hloCur hloTmp hloPtr
      hcurJBp htmpJBp hcntJBp hptrJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp
      (by omega) hrowWidthBp
  obtain ⟨-, -, hctlD, -, -⟩ :=
    emitOpsListProg_eval_state curJ tmpJ cntJ ptrJ M (cur + rowKey + 1) row cnt tag d σC
      hc1 hc2 hCurTmp hCurCnt.symm hTmpCnt.symm hCurPtr hTmpPtr
      hC0 hCcur (by omega) hCcnt hCptr hCtag hCdata
      (by omega) (by omega) (by omega) (by omega) hloCur hloTmp hloPtr
  have hPB5 : ProgramBoundedIn Bp ((emitOpsListProg curJ tmpJ cntJ ptrJ).eval σC)
      (ctlAssign rowJ (ctlCell ptrJ)) := by
    unfold ProgramBoundedIn ctlAssign
    refine ⟨exprBoundedIn_ctlAddr Bp rowJ _ hrowJBp (by rw [hctlD]; omega),
      exprBoundedIn_ctlCell Bp ptrJ _ hptrJBp (by rw [hctlD]; omega), ?_⟩
    rw [ctlAddr_eval, hctlD]; omega
  unfold emitRowBody ProgramBoundedIn
  refine ⟨⟨⟨⟨hPB1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← hσAdef]; exact hPB2
  · rw [eval_seq, ← hσAdef, ← hσBdef]; exact hPB3
  · rw [eval_seq, eval_seq, ← hσAdef, ← hσBdef, hCeq]; exact hPB4
  · rw [eval_seq, eval_seq, eval_seq, ← hσAdef, ← hσBdef, hCeq]; exact hPB5

/-! ## `ProgramBoundedIn` for `emitRowTableProg` (the whole variable-length table)

`emitRowTableProg` stages `rowJ` at the table's base then loops `emitRowBody` once per row via
`emitListProg`, exactly as `emitOpsListProg` loops `emitRawOpBody` once per entry. Both use the
`emitListProg`-wrapping shape already seen in `emitNatTableProg`; this section instantiates the
generic `programBoundedIn_emitListProg`, using `emitRowTableProg_hbody` and
`rowTableBitsLen_row_le` for per-row invariant and separation facts. -/

/-- Per-iteration `ProgramBoundedIn` fact for `emitRowBody` under `EmitRowTableInv`. Reuses
    `emitRowTableProg_hbody` for the invariant-advance/cell-`0` facts and `rowTableBitsLen_row_le`
    peeling for the per-row separation bounds; needs no ceiling on any row's `rowKey`/`cnt`/data
    values (`programBoundedIn_emitRowBody`'s own docstring), only the table's own physical extent
    `tbl + rowTableWidth cntG rowCnt ≤ Bp`
    (`hTableWidthBp`), from which `rowTableWidth_succ` plus monotonicity of `rowTableWidth`
    (`flatMap_range_length_split` applied to `rowTableWidth`'s own `flatMap`) derives the current
    row's own width bound `programBoundedIn_emitRowBody` needs. -/
lemma programBoundedIn_emitRowBody_of_inv (Bp curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt : ℕ)
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
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMptrJBp : M + ptrJ ≤ Bp) (hMrowJBp : M + rowJ ≤ Bp)
    (hTableWidthBp : tbl + rowTableWidth cntG rowCnt ≤ Bp)
    (m : ℕ) (hmrowCnt : m < rowCnt) (τ : Store)
    (hInv : EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG m τ) (hM : τ 0 = M) :
    EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG (m + 1)
      ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) ∧
    (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ 0 = M ∧
    ProgramBoundedIn Bp τ (emitRowBody curJ tmpJ cntJ ptrJ rowJ) := by
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
  have hcur'eq : τ (M + curJ) = cur0 + rowTableBitsLen rowKeyG cntG tagG dG m := hcurPos
  have hkey := rowTableBitsLen_row_le rowKeyG cntG tagG dG rowCnt m hmrowCnt
  have hsepFullRow : τ (M + curJ) + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + curJ := by omega
  have hsepTmpRow : τ (M + curJ) + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + tmpJ := by omega
  have hsepCntRow : τ (M + curJ) + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + cntJ := by omega
  have hsepPtrRow : τ (M + curJ) + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + ptrJ := by omega
  have hsepRowRow : τ (M + curJ) + (rowKeyG m + 1) + (cntG m + 1)
      + ((List.range (cntG m)).flatMap (fun i => [tagG m i] ++ encodeNat (dG m i))).length
      ≤ M + rowJ := by omega
  obtain ⟨_, _, hctl0, _, hInv'⟩ :=
    emitRowTableProg_hbody curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG
      hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
      hcur01 hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
      hloCur hloTmp hloCnt hloPtr hloRow
      m hmrowCnt τ (τ (M + curJ)) ⟨hrowPos, hcurPos, hrowKeyAll, hcntAll, htagAll2, hdataAll2⟩ hM rfl
  refine ⟨hInv', hctl0, ?_⟩
  have hWidthMono : rowTableWidth cntG (m + 1) ≤ rowTableWidth cntG rowCnt := by
    unfold rowTableWidth
    have hsplit := flatMap_range_length_split (fun q => List.replicate (2 + 2 * cntG q) false)
      rowCnt (m + 1) (by omega)
    omega
  have hrowWidthBp' : row + 2 * cntG m + 2 ≤ Bp := by
    have hsucc := rowTableWidth_succ cntG m
    omega
  exact programBoundedIn_emitRowBody Bp curJ tmpJ cntJ ptrJ rowJ M (τ (M + curJ)) row (rowKeyG m)
    (cntG m) (tagG m) (dG m) τ
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
    hM rfl (by omega) hrowCell hrowKey hcntCell htagAllRow hdataAllRow
    hloCurRow hloTmpRow hloCntRow hloPtrRow hsepFullRow hsepTmpRow hsepCntRow hsepPtrRow hsepRowRow
    hcurJBp htmpJBp hcntJBp hptrJBp hrowJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp hMrowJBp
    hrowWidthBp'

/-- Build the initial row invariant from the emitted-count frame. -/
lemma programBoundedIn_emitRowTableProg_inv0 (curJ tmpJ rowJ M cur tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ)
    (σ0 σ1 : Store) (hCurRow : curJ ≠ rowJ) (hTmpRow : tmpJ ≠ rowJ)
    (hsepFull : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepRowAll : cur + rowCnt + 1 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hcursor1 : σ1 (M + curJ) = cur + rowCnt + 1)
    (hframe1 : ∀ r, r ≠ M + curJ → r ≠ M + tmpJ →
      r < cur ∨ cur + rowCnt + 1 ≤ r → σ1 r = σ0 r)
    (hσ0row : σ0 (M + rowJ) = tbl)
    (hσ0rowKeyAll : ∀ q, q < rowCnt → σ0 (tbl + rowTableWidth cntG q) = rowKeyG q)
    (hσ0cntAll : ∀ q, q < rowCnt → σ0 (tbl + rowTableWidth cntG q + 1) = cntG q)
    (hσ0tagAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ0 (tbl + rowTableWidth cntG q + 2 + 2 * i) = if tagG q i then 1 else 0)
    (hσ0dataAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ0 (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) = dG q i) :
    EmitRowTableInv curJ rowJ M (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG 0 σ1 := by
  have hneRowCur : M + rowJ ≠ M + curJ := fun h => hCurRow (Nat.add_left_cancel h).symm
  have hneRowTmp : M + rowJ ≠ M + tmpJ := fun h => hTmpRow (Nat.add_left_cancel h).symm
  have hgeRow : cur + rowCnt + 1 ≤ M + rowJ :=
    le_trans (Nat.le_add_right (cur + rowCnt + 1)
      (rowTableBitsLen rowKeyG cntG tagG dG rowCnt)) hsepRowAll
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe1 (M + rowJ) hneRowCur hneRowTmp (Or.inr hgeRow), hσ0row]
    simp [rowTableWidth]
  · rw [hcursor1]
    simp [rowTableBitsLen]
  · intro q hq
    have hne1 : tbl + rowTableWidth cntG q ≠ M + curJ := by omega
    have hne2 : tbl + rowTableWidth cntG q ≠ M + tmpJ := by omega
    have hge : cur + rowCnt + 1 ≤ tbl + rowTableWidth cntG q := by omega
    rw [hframe1 (tbl + rowTableWidth cntG q) hne1 hne2 (Or.inr hge)]
    exact hσ0rowKeyAll q hq
  · intro q hq
    have hne1 : tbl + rowTableWidth cntG q + 1 ≠ M + curJ := by omega
    have hne2 : tbl + rowTableWidth cntG q + 1 ≠ M + tmpJ := by omega
    have hge : cur + rowCnt + 1 ≤ tbl + rowTableWidth cntG q + 1 := by omega
    rw [hframe1 (tbl + rowTableWidth cntG q + 1) hne1 hne2 (Or.inr hge)]
    exact hσ0cntAll q hq
  · intro q hq i hi
    have hne1 : tbl + rowTableWidth cntG q + 2 + 2 * i ≠ M + curJ := by omega
    have hne2 : tbl + rowTableWidth cntG q + 2 + 2 * i ≠ M + tmpJ := by omega
    have hge : cur + rowCnt + 1 ≤ tbl + rowTableWidth cntG q + 2 + 2 * i := by omega
    rw [hframe1 (tbl + rowTableWidth cntG q + 2 + 2 * i) hne1 hne2 (Or.inr hge)]
    exact hσ0tagAll q hq i hi
  · intro q hq i hi
    have hne1 : tbl + rowTableWidth cntG q + 2 + 2 * i + 1 ≠ M + curJ := by omega
    have hne2 : tbl + rowTableWidth cntG q + 2 + 2 * i + 1 ≠ M + tmpJ := by omega
    have hge : cur + rowCnt + 1 ≤ tbl + rowTableWidth cntG q + 2 + 2 * i + 1 := by omega
    rw [hframe1 (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) hne1 hne2 (Or.inr hge)]
    exact hσ0dataAll q hq i hi

/-- Package the bounded per-row obligation expected by the outer list program. -/
lemma programBoundedIn_emitRowTableProg_hbody_len (Bp curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt : ℕ)
    (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ)
    (hc1 : 1 ≤ curJ) (hc2 : 1 ≤ tmpJ)
    (hCurTmp : curJ ≠ tmpJ) (hCurCnt : curJ ≠ cntJ) (hCurPtr : curJ ≠ ptrJ)
    (hCurRow : curJ ≠ rowJ) (hTmpCnt : tmpJ ≠ cntJ) (hTmpPtr : tmpJ ≠ ptrJ)
    (hTmpRow : tmpJ ≠ rowJ) (hCntPtr : cntJ ≠ ptrJ) (hCntRow : cntJ ≠ rowJ)
    (hPtrRow : ptrJ ≠ rowJ) (hcur01 : 1 ≤ cur0)
    (hsepFull : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + curJ)
    (hsepTmpAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + tmpJ)
    (hsepCntAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + cntJ)
    (hsepPtrAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + ptrJ)
    (hsepRowAll : cur0 + rowTableBitsLen rowKeyG cntG tagG dG rowCnt ≤ M + rowJ)
    (hloCur : M + curJ < tbl) (hloTmp : M + tmpJ < tbl)
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp)
    (hptrJBp : ptrJ ≤ Bp) (hrowJBp : rowJ ≤ Bp) (hMcurJBp : M + curJ ≤ Bp)
    (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMptrJBp : M + ptrJ ≤ Bp) (hMrowJBp : M + rowJ ≤ Bp)
    (hTableWidthBp : tbl + rowTableWidth cntG rowCnt ≤ Bp) :
    ∀ m, m < rowCnt → ∀ τ,
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG m τ →
      τ 0 = M →
      EmitRowTableInv curJ rowJ M cur0 tbl rowCnt rowKeyG cntG tagG dG (m + 1)
        ((emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ) ∧
      (emitRowBody curJ tmpJ cntJ ptrJ rowJ).eval τ 0 = M ∧
      ProgramBoundedIn Bp τ (emitRowBody curJ tmpJ cntJ ptrJ rowJ) := by
  intro m hm τ hInv hMτ
  exact programBoundedIn_emitRowBody_of_inv Bp curJ tmpJ cntJ ptrJ rowJ M cur0 tbl rowCnt
    rowKeyG cntG tagG dG hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow
    hCntPtr hCntRow hPtrRow hcur01 hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow
    hcurJBp htmpJBp hcntJBp hptrJBp hrowJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp hMrowJBp
    hTableWidthBp m hm τ hInv hMτ

/-- `ProgramBoundedIn` for `emitRowTableProg`: the `rowJ := tbl` staging prologue, then
    `programBoundedIn_emitListProg` at `Inv := EmitRowTableInv ... (cur + rowCnt + 1) tbl rowCnt
    rowKeyG cntG tagG dG`, with the per-iteration obligation supplied by
    `programBoundedIn_emitRowBody_of_inv`. `EmitRowTableInv ... 0` at loop entry is established the
    same way `emitRowTableProg_eval_state` does (via `emitNatProg_eval_state`'s frame fact), not by
    a fresh induction. -/
lemma programBoundedIn_emitRowTableProg (Bp curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ M cur tbl
    rowCnt : ℕ) (rowKeyG cntG : ℕ → ℕ) (tagG : ℕ → ℕ → Bool) (dG : ℕ → ℕ → ℕ) (σ : Store)
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
    (hloCnt : M + cntJ < tbl) (hloPtr : M + ptrJ < tbl) (hloRow : M + rowJ < tbl)
    (hcurJBp : curJ ≤ Bp) (htmpJBp : tmpJ ≤ Bp) (hcntJBp : cntJ ≤ Bp) (hptrJBp : ptrJ ≤ Bp)
    (hrowJBp : rowJ ≤ Bp) (hrowCntJBp : rowCntJ ≤ Bp) (htblJBp : tblJ ≤ Bp)
    (hMcurJBp : M + curJ ≤ Bp) (hMtmpJBp : M + tmpJ ≤ Bp) (hMcntJBp : M + cntJ ≤ Bp)
    (hMptrJBp : M + ptrJ ≤ Bp) (hMrowJBp : M + rowJ ≤ Bp) (hMrowCntJBp : M + rowCntJ ≤ Bp)
    (hMtblJBp : M + tblJ ≤ Bp)
    (hcurNBp : cur + rowCnt + 1 ≤ Bp) (hTableWidthBp : tbl + rowTableWidth cntG rowCnt ≤ Bp) :
    ProgramBoundedIn Bp σ (emitRowTableProg curJ tmpJ cntJ ptrJ rowJ rowCntJ tblJ) := by
  unfold emitRowTableProg ProgramBoundedIn
  have hexprTbl : (ctlCell tblJ).eval σ = tbl := by rw [ctlCell_eval, hM, htbl]
  have hσ0row : (ctlAssign rowJ (ctlCell tblJ)).eval σ (M + rowJ) = tbl := by
    have h := ctlAssign_eval_same rowJ (ctlCell tblJ) σ
    rw [hM] at h
    rw [h]; exact hexprTbl
  have hPB0 : ProgramBoundedIn Bp σ (ctlAssign rowJ (ctlCell tblJ)) := by
    unfold ProgramBoundedIn ctlAssign
    refine ⟨exprBoundedIn_ctlAddr Bp rowJ σ hrowJBp (by rw [hM]; omega),
      exprBoundedIn_ctlCell Bp tblJ σ htblJBp (by rw [hM]; omega), ?_⟩
    rw [ctlAddr_eval, hM]; omega
  refine ⟨hPB0, ?_⟩
  set σ0 := (ctlAssign rowJ (ctlCell tblJ)).eval σ with hσ0def
  have hσ0cur : σ0 (M + curJ) = cur := by
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (M + curJ) (by omega)]; exact hcur
  have hσ00 : σ0 0 = M := by
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ 0 (by omega)]; exact hM
  have hσ0rowCnt : σ0 (M + rowCntJ) = rowCnt := by
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (M + rowCntJ) (by omega)]; exact hrowCnt
  have hσ0rowKeyAll : ∀ q, q < rowCnt → σ0 (tbl + rowTableWidth cntG q) = rowKeyG q := by
    intro q hq
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (tbl + rowTableWidth cntG q) (by omega)]
    exact hrowKeyAll q hq
  have hσ0cntAll : ∀ q, q < rowCnt → σ0 (tbl + rowTableWidth cntG q + 1) = cntG q := by
    intro q hq
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (tbl + rowTableWidth cntG q + 1) (by omega)]
    exact hcntAll q hq
  have hσ0tagAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ0 (tbl + rowTableWidth cntG q + 2 + 2 * i) = if tagG q i then 1 else 0 := by
    intro q hq i hi
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (tbl + rowTableWidth cntG q + 2 + 2 * i) (by omega)]
    exact htagAll q hq i hi
  have hσ0dataAll : ∀ q, q < rowCnt → ∀ i, i < cntG q →
      σ0 (tbl + rowTableWidth cntG q + 2 + 2 * i + 1) = dG q i := by
    intro q hq i hi
    rw [hσ0def, ctlAssign_eval_diff rowJ _ σ (tbl + rowTableWidth cntG q + 2 + 2 * i + 1)
      (by omega)]
    exact hdataAll q hq i hi
  have hσ0rowCntEval : (ctlCell rowCntJ).eval σ0 = rowCnt := by
    rw [ctlCell_eval, hσ00, hσ0rowCnt]
  have hsep1 : cur + (ctlCell rowCntJ).eval σ0 < M + curJ := by rw [hσ0rowCntEval]; omega
  obtain ⟨-, hcursor1, hframe1, hctl1⟩ :=
    emitNatProg_eval_state curJ tmpJ M cur (ctlCell rowCntJ) σ0 hc1 hc2 hCurTmp hσ00 hσ0cur
      hcur1 hsep1
  rw [hσ0rowCntEval] at hcursor1 hframe1
  set σ1 := (emitNatProg curJ tmpJ (ctlCell rowCntJ)).eval σ0 with hσ1def
  have hInv0 := programBoundedIn_emitRowTableProg_inv0 curJ tmpJ rowJ M cur tbl rowCnt
    rowKeyG cntG tagG dG σ0 σ1 hCurRow hTmpRow hsepFull hsepRowAll hloCur hloTmp hcursor1 hframe1
    hσ0row hσ0rowKeyAll hσ0cntAll hσ0tagAll hσ0dataAll
  have hbody := programBoundedIn_emitRowTableProg_hbody_len Bp curJ tmpJ cntJ ptrJ rowJ M
    (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG
    hc1 hc2 hCurTmp hCurCnt hCurPtr hCurRow hTmpCnt hTmpPtr hTmpRow hCntPtr hCntRow hPtrRow
    (by omega) hsepFull hsepTmpAll hsepCntAll hsepPtrAll hsepRowAll
    hloCur hloTmp hloCnt hloPtr hloRow
    hcurJBp htmpJBp hcntJBp hptrJBp hrowJBp hMcurJBp hMtmpJBp hMcntJBp hMptrJBp hMrowJBp
    hTableWidthBp
  have hsepFull' : cur + rowCnt + 1 ≤ M + curJ := by
    have h0 : (0 : ℕ) ≤ rowTableBitsLen rowKeyG cntG tagG dG rowCnt := Nat.zero_le _
    omega
  exact programBoundedIn_emitListProg Bp curJ tmpJ rowCntJ M cur rowCnt
    (emitRowBody curJ tmpJ cntJ ptrJ rowJ)
    (EmitRowTableInv curJ rowJ M (cur + rowCnt + 1) tbl rowCnt rowKeyG cntG tagG dG) σ0
    hc1 hc2 hCurTmp hCurRowCnt.symm hTmpRowCnt.symm hσ00 hσ0cur hcur1 hσ0rowCnt
    hsepCnt hsepFull' hcurJBp htmpJBp hrowCntJBp hMcurJBp hMtmpJBp hMrowCntJBp hcurNBp
    hbody hInv0

end NPComplete.RAMToTM

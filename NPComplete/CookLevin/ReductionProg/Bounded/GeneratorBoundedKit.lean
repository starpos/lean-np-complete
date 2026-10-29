module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAtLeastOne

/-!
Every clause family is loops inside loops, four deep for persist and trans,
shallower for the others.  This file gives the shape that recurs across
families: an outer trip count threaded explicitly as an `i < n` premise rather
than pulled out of `Frozen`, since a level's own pins never expose its own counter.

None of what follows names a family.  The persist, uniqueness, and accept families
use the same assembly pattern.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The table width `n` blocks of arbitrary clause lists consume, each
bounded by `wid`, via induction on `List.range n`'s own flatMap. -/
lemma rowTableWidth_flatMap_range_le (g : ℕ → List Clause) (wid : ℕ) (n : ℕ)
    (hg : ∀ i, i < n → rowTableWidth (rowW (g i)) (g i).length ≤ wid) :
    rowTableWidth (rowW ((List.range n).flatMap g)) ((List.range n).flatMap g).length
      ≤ n * wid := by
  induction n with
  | zero => simp [rowTableWidth_zero]
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, rowTableWidth_append_total]
      have h1 := ih (fun i hi => hg i (by omega))
      have h2 := hg k (by omega)
      have h3 : (k + 1) * wid = k * wid + wid := by ring
      omega

/-! ## Closing a family level into `ClauseWriterBounded`

A bounded loop body in the `Frozen`-indexed form needs a fixed counter bound
from `Frozen`.  Here `Frozen` is `PinsHold M pins`, and `pins` omits the loop's
own counter, so it places no bound on that counter.  The bounded induction therefore carries
the trip-count premise `i < n` directly, matching
`programBoundedIn_loopEval_of_indexed_inv` and specialized to
`ClauseLoopBody`/`ClauseWriterBounded`. -/

/-- Bounded companion to `ClauseLoopBody`, indexed by an explicit trip count
`n` instead of a `Frozen`-derived counter cap.  `wid` bounds one iteration's
own table width. -/
def ClauseLoopBodyBoundedUpTo (body : Program) (M Jmax wpJ iJ K S B n wid : ℕ)
    (Frozen : Store → Prop) : Prop :=
  ∀ (τ : Store) (i wp : ℕ), Frozen τ → τ 0 = M → τ (M + iJ) = i → i < n → τ (M + wpJ) = wp →
    M + Jmax < wp → wp + wid ≤ S → StoreValuesLe S τ → TightCells K M τ →
    ProgramBoundedIn B τ body ∧ StoreValuesLe S (body.eval τ) ∧ TightCells K M (body.eval τ)

/-- Boundedness at every store the loop visits, from the per-iteration
statements, threading the trip count as `i0 + k ≤ n` rather than deriving it
from `Frozen`.  The slack `k * wid` scales the per-iteration width by the
remaining trip count. -/
lemma clauseLoopBodyBoundedUpTo_loopEval (body : Program) (M Jmax wpJ iJ K S B n wid : ℕ)
    (Frozen : Store → Prop) (g : ℕ → List Clause)
    (hgwid : ∀ i, i < n → rowTableWidth (rowW (g i)) (g i).length ≤ wid)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g)
    (hbd : ClauseLoopBodyBoundedUpTo body M Jmax wpJ iJ K S B n wid Frozen) :
    ∀ (k i0 : ℕ) (τ : Store) (wp0 : ℕ), i0 + k ≤ n → Frozen τ → τ 0 = M → τ (M + iJ) = i0 →
      τ (M + wpJ) = wp0 → M + Jmax < wp0 → wp0 + k * wid ≤ S →
      StoreValuesLe S τ → TightCells K M τ →
      (∀ m' < k, ProgramBoundedIn B (loopEval body m' τ) body) ∧
        StoreValuesLe S (loopEval body k τ) ∧ TightCells K M (loopEval body k τ) := by
  intro k
  induction k with
  | zero =>
      intro i0 τ wp0 _ _ _ _ _ _ _ hst ht
      exact ⟨fun m' hm' => absurd hm' (by omega), by rwa [loopEval_zero], by rwa [loopEval_zero]⟩
  | succ k ih =>
      intro i0 τ wp0 hikn hF h0 hi hw hsep hslack hst ht
      have hi0n : i0 < n := by omega
      have hslack0 : wp0 + wid ≤ S := by
        have hsm : (k + 1) * wid = wid + k * wid := by ring
        omega
      obtain ⟨hF', h0', hi', hw', _, _⟩ := hbody τ i0 wp0 hF h0 hi hw hsep
      obtain ⟨hpb, hst', ht'⟩ := hbd τ i0 wp0 hF h0 hi hi0n hw hsep hslack0 hst ht
      have hsep' : M + Jmax < wp0 + rowTableWidth (rowW (g i0)) (g i0).length := by omega
      have hslack' : (wp0 + rowTableWidth (rowW (g i0)) (g i0).length) + k * wid ≤ S := by
        have hgi := hgwid i0 hi0n
        have hsm : (k + 1) * wid = wid + k * wid := by ring
        omega
      obtain ⟨hrec, hstk, htk⟩ :=
        ih (i0 + 1) (body.eval τ) _ (by omega) hF' h0' hi' hw' hsep' hslack' hst' ht'
      refine ⟨fun m' hm' => ?_, by rw [loopEval_succ]; exact hstk,
        by rw [loopEval_succ]; exact htk⟩
      rcases Nat.eq_zero_or_pos m' with rfl | hpos
      · rw [loopEval_zero]; exact hpb
      · have hm'eq : m' = (m' - 1) + 1 := by omega
        rw [hm'eq, loopEval_succ]
        exact hrec (m' - 1) (by omega)

/-- A leaf whose literals are bounded is an UpTo-bounded loop body: `i < n`
combined with `n ≤ K` gives the bump room that a `Frozen`-indexed counter
bound cannot supply here.  The width is the row's own
`2 + 2 * lits.length`. -/
lemma clauseLoopBodyBoundedUpTo_leafProg (K S B M Jmax iJ n : ℕ)
    (lits : List (Expr × Expr)) (Frozen : Store → Prop)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hJ : 24 ≤ Jmax) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hnK : n ≤ K)
    (hcnt : lits.length ≤ S)
    (hlits : LitsBounded K S B M lits) :
    ClauseLoopBodyBoundedUpTo (leafProg wpJ iJ lits) M Jmax wpJ iJ K S B n
      (2 + 2 * lits.length) Frozen := by
  intro τ i wp hF h0 hi hin hw hsep hslack hst ht
  have hsep24 : M + 24 < wp := by omega
  have hb : τ (M + iJ) + 1 ≤ K := by omega
  have hrow : wp + 2 + 2 * lits.length ≤ S := by omega
  have hex := leafProg_exit K S B M wp iJ τ lits h0 hw hsep24 hMB hrow hSB hcnt
    hlits ht hst hiJ hiJ2 hb hKS
  exact ⟨programBoundedIn_leafProg K S B M wp iJ τ lits h0 hw hsep24 hMB
    hrow hSB hcnt hlits ht hst hiJ hiJ2 hKB, hex.2.2.2, hex.2.2.1⟩

/-- A whole `loopProg`'s program bound, from an UpTo body bound whose trip
count matches the count expression's own value.  `n * wid` is the total width
`n` iterations of `wid`-bounded steps still consume. -/
lemma programBoundedIn_loopProg_up_to (K S B M Jmax iJ wp n wid : ℕ) (σ : Store) (cntE : Expr)
    (body : Program) (Frozen : Store → Prop) (g : ℕ → List Clause)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + Jmax < wp)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B)
    (hFreset : Frozen ((ctlAssign iJ (.const 0)).eval σ))
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hgwid : ∀ i, i < n → rowTableWidth (rowW (g i)) (g i).length ≤ wid)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g)
    (hbd : ClauseLoopBodyBoundedUpTo body M Jmax wpJ iJ K S B n wid Frozen)
    (hcnt : ExprBoundedIn B ((ctlAssign iJ (.const 0)).eval σ) cntE)
    (hn : cntE.eval ((ctlAssign iJ (.const 0)).eval σ) = n)
    (hslack : wp + n * wid ≤ S) :
    ProgramBoundedIn B σ (loopProg iJ cntE body) := by
  obtain ⟨g0, gi, gt, gs⟩ := ctlAssign_zero_preserves K S M iJ σ h0 hiJ hiJ2 ht hst
  have hgw : (ctlAssign iJ (.const 0)).eval σ (M + wpJ) = wp := by
    rw [ctlAssign_eval_diff iJ (.const 0) σ (M + wpJ)
      (by rw [h0]; simp only [wpJ]; omega), hwp]
  refine ⟨programBoundedIn_ctlAssign_const B M iJ 0 σ h0 (by omega) (by omega), hcnt, ?_⟩
  rw [hn]
  exact (clauseLoopBodyBoundedUpTo_loopEval body M Jmax wpJ iJ K S B n wid Frozen g hgwid hbody
    hbd n 0 _ wp (by omega) hFreset g0 gi hgw hsep hslack gs gt).1

/-- The envelopes at an UpTo-bounded loop's exit, for whatever runs after it. -/
lemma loopProg_up_to_exit (K S B M Jmax iJ wp n wid : ℕ) (σ : Store) (cntE : Expr)
    (body : Program) (Frozen : Store → Prop) (g : ℕ → List Clause)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + Jmax < wp)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (hFreset : Frozen ((ctlAssign iJ (.const 0)).eval σ))
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hgwid : ∀ i, i < n → rowTableWidth (rowW (g i)) (g i).length ≤ wid)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g)
    (hbd : ClauseLoopBodyBoundedUpTo body M Jmax wpJ iJ K S B n wid Frozen)
    (hn : cntE.eval ((ctlAssign iJ (.const 0)).eval σ) = n)
    (hslack : wp + n * wid ≤ S) :
    TightCells K M ((loopProg iJ cntE body).eval σ) ∧
      StoreValuesLe S ((loopProg iJ cntE body).eval σ) := by
  obtain ⟨g0, gi, gt, gs⟩ := ctlAssign_zero_preserves K S M iJ σ h0 hiJ hiJ2 ht hst
  have hgw : (ctlAssign iJ (.const 0)).eval σ (M + wpJ) = wp := by
    rw [ctlAssign_eval_diff iJ (.const 0) σ (M + wpJ)
      (by rw [h0]; simp only [wpJ]; omega), hwp]
  obtain ⟨_, hs, htc⟩ := clauseLoopBodyBoundedUpTo_loopEval body M Jmax wpJ iJ K S B n wid Frozen
    g hgwid hbody hbd n 0 _ wp (by omega) hFreset g0 gi hgw hsep hslack gs gt
  unfold loopProg
  rw [eval_seq, eval_forN, hn]
  exact ⟨htc, hs⟩

/-- A whole `loopProg`, packaged as `ClauseWriterBounded`, from an UpTo body
bound and the loop's own trip count.  `n * wid` is the outer width from `n`
iterations of `wid`-bounded steps. -/
lemma clauseWriterBounded_loopProg_up_to (K S B M Jmax iJ n wid : ℕ) (cntE : Expr) (body : Program)
    (Frozen : Store → Prop) (g : ℕ → List Clause)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B)
    (hFreset : ∀ τ : Store, Frozen τ → τ 0 = M →
      Frozen ((ctlAssign iJ (.const 0)).eval τ))
    (hgwid : ∀ i, i < n → rowTableWidth (rowW (g i)) (g i).length ≤ wid)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ Frozen g)
    (hbd : ClauseLoopBodyBoundedUpTo body M Jmax wpJ iJ K S B n wid Frozen)
    (hcntB : ∀ τ : Store, Frozen τ → τ 0 = M →
      ExprBoundedIn B ((ctlAssign iJ (.const 0)).eval τ) cntE)
    (hn : ∀ τ : Store, Frozen τ → τ 0 = M →
      cntE.eval ((ctlAssign iJ (.const 0)).eval τ) = n) :
    ClauseWriterBounded (loopProg iJ cntE body) M Jmax wpJ K S B (n * wid) Frozen := by
  intro τ wp hF h0 hwp hsep hslack hst ht
  refine ⟨programBoundedIn_loopProg_up_to K S B M Jmax iJ wp n wid τ cntE body Frozen g
    h0 hwp hsep hiJ hiJ2 hMB (hFreset τ hF h0) ht hst hgwid hbody hbd (hcntB τ hF h0)
    (hn τ hF h0) hslack, ?_, ?_⟩
  · exact (loopProg_up_to_exit K S B M Jmax iJ wp n wid τ cntE body Frozen g
      h0 hwp hsep hiJ hiJ2 (hFreset τ hF h0) ht hst hgwid hbody hbd (hn τ hF h0) hslack).2
  · exact (loopProg_up_to_exit K S B M Jmax iJ wp n wid τ cntE body Frozen g
      h0 hwp hsep hiJ hiJ2 (hFreset τ hF h0) ht hst hgwid hbody hbd (hn τ hF h0) hslack).1

/-- Bounded companion to `clauseLoopBody_of_writer`: a writer bounded for
every counter value below the trip count, followed by that counter's own
bump, is an UpTo-bounded loop body over the outer pins alone. -/
lemma clauseLoopBodyBoundedUpTo_of_clauseWriterBounded (prog : Program)
    (M Jmax wpJ iJ K S B n wid : ℕ) (pins : List (ℕ × ℕ)) (cs : ℕ → List Clause)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B) (hKS : K ≤ S) (hKB : K ≤ B)
    (hnK : n ≤ K)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ (PinsHold M ((iJ, i) :: pins)) (cs i))
    (hb : ∀ i, ClauseWriterBounded prog M Jmax wpJ K S B wid (PinsHold M ((iJ, i) :: pins))) :
    ClauseLoopBodyBoundedUpTo (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ K S B n wid (PinsHold M pins) := by
  intro τ i wp hF h0 hi hin hwp hsep hslack hst ht
  have hpins : PinsHold M ((iJ, i) :: pins) τ := pinsHold_cons M (iJ, i) pins τ hi hF
  obtain ⟨hpb1, hst1, ht1⟩ := hb i τ wp hpins h0 hwp hsep hslack hst ht
  obtain ⟨hF1, h01, _, _, _⟩ := hw i τ wp hpins h0 hwp hsep
  have hi' : prog.eval τ (M + iJ) = i := pinsHold_head M (iJ, i) pins (prog.eval τ) hF1
  have hb1 : prog.eval τ (M + iJ) + 1 ≤ K := by omega
  obtain ⟨_, gt, gs⟩ := ctlAssign_bump_preserves K S M iJ 1 _ h01 hiJ hiJ2 ht1 hst1 hb1 hKS
  rw [eval_seq]
  exact ⟨⟨hpb1, programBoundedIn_ctlAssign_bump B M _ iJ 1 _ h01 (by omega) rfl (by omega)⟩,
    gs, gt⟩

/-- A `ClauseWriterBounded` fact needed only when the pinned counter is
inside the tight envelope extends to every counter value for free: outside
it, `TightCells` contradicts the pin, so the case is vacuous.  Discharges the
`hb` argument of `clauseLoopBodyBoundedUpTo_of_clauseWriterBounded` at a level
whose per-iteration `ClauseWriterBounded` is only proved for counters
under `K` (a `pHead ≤ K`-style hypothesis a caller supplies from its own trip
count). -/
lemma clauseWriterBounded_of_le_or_vacuous (prog : Program) (M Jmax wpJ K S B wid iJ i : ℕ)
    (pins : List (ℕ × ℕ))
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (hreal : i ≤ K →
      ClauseWriterBounded prog M Jmax wpJ K S B wid (PinsHold M ((iJ, i) :: pins))) :
    ClauseWriterBounded prog M Jmax wpJ K S B wid (PinsHold M ((iJ, i) :: pins)) := by
  by_cases hik : i ≤ K
  · exact hreal hik
  · intro τ wp hF h0 hw hsep hslack hst ht
    have hi' : τ (M + iJ) = i := pinsHold_head M (iJ, i) pins τ hF
    have := ht iJ hiJ hiJ2
    omega

/-- Resetting a counter not among a pins list's addresses leaves the pins
intact — the `hFreset` obligation every loop-bounded call needs. -/
lemma pinsHold_reset (M j : ℕ) (pins : List (ℕ × ℕ)) (τ : Store)
    (h0 : τ 0 = M) (hne : ∀ p ∈ pins, p.1 ≠ j) (hF : PinsHold M pins τ) :
    PinsHold M pins ((ctlAssign j (.const 0)).eval τ) := by
  intro p hp
  have hev : ((ctlAssign j (.const 0)).eval τ) (M + p.1) = τ (M + p.1) := by
    unfold ctlAssign
    rw [eval_assignInd]
    simp only [Expr.eval, ctlAddr, h0]
    exact writeReg_diff τ (M + j) 0 (M + p.1) (by have := hne p hp; omega)
  rw [hev]
  exact hF p hp

/-! ## Wrapping `writeAtLeastOneProg` into `ClauseWriterBounded`

`writeAtLeastOneProg` is a single row of run-time width, not a loop-over-rows
combinator, so it does not fit `clauseWriterBounded_loopProg_up_to`.  Uniqueness
and accept both use it as one block inside a larger nest, so it needs its own
`ClauseWriterBounded` wrapper — built from `programBoundedIn_writeAtLeastOneProg`
and `writeAtLeastOneProg_exit`, the two bounded facts `GeneratorBoundedAtLeastOne`
already proves for it. -/

/-- `writeAtLeastOneProg`, packaged as `ClauseWriterBounded`.  The two count
expression obligations (`hcntE'`/`hn'`) are stated at the header's own exit
store, matching what `.forN` actually evaluates the count against; `hcntE0`/
`hn0` are the same at entry, since a caller typically only has the entry fact
in hand. `2 + 2 * n` is the row's own width: a tag/pointer header plus two
cells per literal. -/
lemma clauseWriterBounded_writeAtLeastOneProg (K S B M Jmax iJ n : ℕ) (cntE varE : Expr)
    (Frozen : Store → Prop)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hJ : 24 ≤ Jmax) (hMB : M + 24 ≤ B)
    (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hSB : S ≤ B) (hnK : n ≤ K)
    (hcntE0 : ∀ τ : Store, Frozen τ → τ 0 = M → ExprBoundedIn B τ cntE)
    (hn0 : ∀ τ : Store, Frozen τ → τ 0 = M → cntE.eval τ = n)
    (hcntE' : ∀ (τ : Store) (wp : ℕ), Frozen τ → τ 0 = M → τ (M + wpJ) = wp →
      M + Jmax < wp →
      ExprBoundedIn B (writeReg (writeReg (writeReg τ (wp + 1) n) (M + wpJ) (wp + 2))
        (M + iJ) 0) cntE)
    (hn' : ∀ (τ : Store) (wp : ℕ), Frozen τ → τ 0 = M → τ (M + wpJ) = wp →
      M + Jmax < wp →
      cntE.eval (writeReg (writeReg (writeReg τ (wp + 1) n) (M + wpJ) (wp + 2))
        (M + iJ) 0) = n)
    (hvarE : ∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ varE ∧ varE.eval τ ≤ S) :
    ClauseWriterBounded (writeAtLeastOneProg wpJ iJ cntE varE) M Jmax wpJ K S B (2 + 2 * n)
      Frozen := by
  intro τ wp hF h0 hwp hsep hslack hst ht
  have hsep24 : M + 24 < wp := by omega
  refine ⟨programBoundedIn_writeAtLeastOneProg K S B M wp iJ n τ cntE varE h0 hwp hsep24 hMB
    hiJ hiJ2 hKB hKS hSB hnK (by omega) (hcntE0 τ hF h0) (hn0 τ hF h0)
    (hcntE' τ wp hF h0 hwp hsep) (hn' τ wp hF h0 hwp hsep) hvarE ht hst, ?_, ?_⟩
  · exact (writeAtLeastOneProg_exit K S M wp iJ n τ cntE varE h0 hwp hsep24 hiJ hiJ2 hKS hnK
      (by omega) (hn0 τ hF h0) (hn' τ wp hF h0 hwp hsep)
      (fun σ h0' ht' hst' => (hvarE σ h0' ht' hst').2) ht hst).2.2.2
  · exact (writeAtLeastOneProg_exit K S M wp iJ n τ cntE varE h0 hwp hsep24 hiJ hiJ2 hKS hnK
      (by omega) (hn0 τ hF h0) (hn' τ wp hF h0 hwp hsep)
      (fun σ h0' ht' hst' => (hvarE σ h0' ht' hst').2) ht hst).2.2.1

end NPComplete.CookLevin

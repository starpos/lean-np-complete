module

public import NPComplete.CookLevin.ReductionProg.GeneratorScanFree

/-!
`ProgramBoundedIn` asks a different question than the writer contracts do.  A
writer says which clauses land where; boundedness says every intermediate an
expression forms stays under an envelope, on *both* arms of every conditional and
at *every* store a loop visits.  The two are proved against the same programs, so
the bounded statements are shaped to sit alongside the writer ones — same
argument order, same `Frozen` predicate — and composed by the same seq/loop
lemmas.

Three envelopes are needed, not one, and they are nested.  A dense variable
number is a product of a time index, a window width and a block size, so a single
bound would have to satisfy `B * B ≤ B`.

* `K` bounds the *control and parameter cells* — the counters, the window width,
  the time bound.  These are the only cells a dense expression multiplies, so
  this is the envelope the expression bounds are stated against.
* `S` bounds the *whole store*.  It must dominate `K`'s polynomials, because the
  variable numbers the generator computes are written into the clause table and
  then have to stay under a store-wide bound.
* `B` bounds the *expressions*, covering the intermediate products as well.

`K` and `S` differ precisely because a variable number is quadratic in `K`:
collapsing them would ask `K` to dominate its own square.  Keeping them apart
costs nothing, since the writes that push values past `K` all land above the
control block, which is what leaves the counters at `K` while the table grows.

Both `K` and `S` have to be preserved by execution, which is why the bounded
statements carry them forward as part of their conclusion: a `.seq` cannot hand
the second program a store it knows nothing about.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The cells the expressions multiply

The control block runs to `ctlJmax = 7`, the emitter registers to `M + 14`, and
the run-time parameters to `M + 24`.  A dense variable expression reads its
counters and its window width from that range, so bounding it is what makes the
arithmetic bounds available; cells above it are the clause table, which the
generator writes but never multiplies. -/

/-- The control and parameter cells all hold values under `K`. -/
def TightCells (K M : ℕ) (τ : Store) : Prop := ∀ j, 2 ≤ j → j ≤ 24 → τ (M + j) ≤ K

/-- Cells the writers leave alone keep their bound, which is how a clause write
    above the pointer preserves the tight envelope. -/
lemma tightCells_of_frame {K M : ℕ} {τ τ' : Store} (h : TightCells K M τ)
    (hfr : ∀ j, 2 ≤ j → j ≤ 24 → τ' (M + j) = τ (M + j)) : TightCells K M τ' := by
  intro j h2 h24
  rw [hfr j h2 h24]
  exact h j h2 h24

/-! ## The bounded companions

Each mirrors a writer contract argument for argument, so a family's boundedness
proof can follow its correctness proof line by line.  The conclusion carries the
tight envelope and the tight cells forward because composition needs them: the
second half of a `.seq` is bounded at the store the first half produced, and
nothing else in the development says what that store holds. -/

/-- Bounded companion to `ClauseWriter`.  `wid` is an upper bound on the table
    width `prog` still writes, so `wp + wid ≤ S` is a real constraint on the
    entry pointer `wp` already bound by the outer `∀` — unlike a hypothesis
    quantified separately over every `wp`, which no finite `S` could satisfy. -/
def ClauseWriterBounded (prog : Program) (M Jmax wpJ K S B wid : ℕ)
    (Frozen : Store → Prop) : Prop :=
  ∀ (τ : Store) (wp : ℕ), Frozen τ → τ 0 = M → τ (M + wpJ) = wp → M + Jmax < wp →
    wp + wid ≤ S →
    StoreValuesLe S τ → TightCells K M τ →
    ProgramBoundedIn B τ prog ∧ StoreValuesLe S (prog.eval τ) ∧
      TightCells K M (prog.eval τ)

/-! ## Widening

A width bound stays a bound at any larger width, since the slack hypothesis
`wp + wid ≤ S` only gets easier to satisfy as `wid` grows. -/

lemma clauseWriterBounded_of_wid_le (prog : Program) (M Jmax wpJ K S B wid wid' : ℕ)
    (Frozen : Store → Prop) (hwid : wid ≤ wid')
    (h : ClauseWriterBounded prog M Jmax wpJ K S B wid Frozen) :
    ClauseWriterBounded prog M Jmax wpJ K S B wid' Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  exact h τ wp hF h0 hw hsep (by omega) hst ht

/-! ## Composition -/

/-- Two bounded writers compose, using the first's *writer* contract to know
    where the second starts.  This is why the bounded statements take the same
    `Frozen` and `Jmax` as the writer ones: the entry conditions the second half
    needs are exactly what the first half's correctness already established.
    The combined width `wid1 + wid2` is what lets the caller's single slack
    hypothesis at entry cover both halves in turn. -/
lemma clauseWriterBounded_seq (p1 p2 : Program) (M Jmax wpJ K S B wid1 wid2 : ℕ)
    (Frozen : Store → Prop) (cs1 : List Clause)
    (hw1 : ClauseWriter p1 M Jmax wpJ Frozen cs1)
    (hwid1 : rowTableWidth (rowW cs1) cs1.length ≤ wid1)
    (hb1 : ClauseWriterBounded p1 M Jmax wpJ K S B wid1 Frozen)
    (hb2 : ClauseWriterBounded p2 M Jmax wpJ K S B wid2 Frozen) :
    ClauseWriterBounded (.seq p1 p2) M Jmax wpJ K S B (wid1 + wid2) Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  obtain ⟨hF', h0', hw', _, _⟩ := hw1 τ wp hF h0 hw hsep
  obtain ⟨hpb1, hst1, ht1⟩ := hb1 τ wp hF h0 hw hsep (by omega) hst ht
  have hsep' : M + Jmax < wp + rowTableWidth (rowW cs1) cs1.length := by omega
  have hslack' : (wp + rowTableWidth (rowW cs1) cs1.length) + wid2 ≤ S := by omega
  obtain ⟨hpb2, hst2, ht2⟩ := hb2 (p1.eval τ) _ hF' h0' hw' hsep' hslack' hst1 ht1
  rw [eval_seq]
  exact ⟨⟨hpb1, hpb2⟩, hst2, ht2⟩

end NPComplete.CookLevin

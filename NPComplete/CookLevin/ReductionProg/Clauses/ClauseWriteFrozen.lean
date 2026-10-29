module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableFrame

/-!
`clauseWriter_seq` composes two writers only when they carry the *same* `Frozen`
predicate, and the five families do not: the arithmetic ones freeze nothing but
the control block, the initial and accept ones each freeze a staged word, and the
transition one freezes three.

A writer's frame promise preserves cells outside its control block, so a word
staged above its extent remains available to later families.  A word read by a
family must lie below that family's entry pointer.  Since different families
read different words, one predicate cannot keep every word on the required side
of every writer's extent.

`ClauseWriterIO` gives each family distinct entry and exit predicates.  Each
family consumes its own staged word, and `.seq` composes consecutive families
through their shared intermediate predicate.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A clause writer with distinct entry and exit predicates.  `ClauseWriter` is
    the diagonal case; the extra freedom is what lets a concatenation shed a
    staged word after the family that reads it has run. -/
def ClauseWriterIO (prog : Program) (M Jmax wpJ : ℕ)
    (Entry Exit : Store → Prop) (cs : List Clause) : Prop :=
  ∀ (τ : Store) (wp : ℕ), Entry τ → τ 0 = M → τ (M + wpJ) = wp → M + Jmax < wp →
    Exit (prog.eval τ) ∧
    (prog.eval τ) 0 = M ∧
    (prog.eval τ) (M + wpJ) = wp + rowTableWidth (rowW cs) cs.length ∧
    RowsWritten (prog.eval τ) wp cs ∧
    (∀ r, r < wp → CtlFree M Jmax r → (prog.eval τ) r = τ r)

/-- Every family's own theorem is already of this shape, with entry and exit the
    same predicate. -/
lemma clauseWriterIO_of_writer (prog : Program) (M Jmax wpJ : ℕ) (F : Store → Prop)
    (cs : List Clause) (h : ClauseWriter prog M Jmax wpJ F cs) :
    ClauseWriterIO prog M Jmax wpJ F F cs := h

/-- Dropping what the rest of the concatenation no longer needs. -/
lemma clauseWriterIO_weaken_exit (prog : Program) (M Jmax wpJ : ℕ)
    (Entry Exit Exit' : Store → Prop) (cs : List Clause)
    (hw : ∀ τ, Exit τ → Exit' τ)
    (h : ClauseWriterIO prog M Jmax wpJ Entry Exit cs) :
    ClauseWriterIO prog M Jmax wpJ Entry Exit' cs := by
  intro τ wp hF h0 hwp hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h τ wp hF h0 hwp hsep
  exact ⟨hw _ a1, a2, a3, a4, a5⟩

/-- Requiring more on entry than the writer needs. -/
lemma clauseWriterIO_strengthen_entry (prog : Program) (M Jmax wpJ : ℕ)
    (Entry Entry' Exit : Store → Prop) (cs : List Clause)
    (hs : ∀ τ, Entry' τ → Entry τ)
    (h : ClauseWriterIO prog M Jmax wpJ Entry Exit cs) :
    ClauseWriterIO prog M Jmax wpJ Entry' Exit cs :=
  fun τ wp hF h0 hwp hsep => h τ wp (hs τ hF) h0 hwp hsep

/-- Running two writers in sequence writes the concatenation, threading the
    middle predicate.  The proof is `clauseWriter_seq`'s, with the second
    writer's entry supplied by the first writer's exit. -/
lemma clauseWriterIO_seq (p1 p2 : Program) (M Jmax wpJ : ℕ)
    (Entry Mid Exit : Store → Prop) (cs ds : List Clause)
    (h1 : ClauseWriterIO p1 M Jmax wpJ Entry Mid cs)
    (h2 : ClauseWriterIO p2 M Jmax wpJ Mid Exit ds) :
    ClauseWriterIO (.seq p1 p2) M Jmax wpJ Entry Exit (cs ++ ds) := by
  intro τ wp hF h0 hw hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 τ wp hF h0 hw hsep
  set σ1 := p1.eval τ with hσ1def
  set d1 := rowTableWidth (rowW cs) cs.length with hd1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 σ1 (wp + d1) a1 a2 a3 (by omega)
  have hgoal : (Program.seq p1 p2).eval τ = p2.eval σ1 := by rw [eval_seq, hσ1def]
  rw [hgoal]
  have hkeep : RowsWritten (p2.eval σ1) wp cs :=
    rowsWritten_of_agree σ1 (p2.eval σ1) wp cs a4
      (fun r _ hlt => b5 r (by omega) (Or.inr (by omega)))
  refine ⟨b1, b2, ?_, ?_, ?_⟩
  · rw [b3, rowTableWidth_append_total cs ds, ← hd1]; omega
  · exact rowsWritten_append _ wp cs ds hkeep b4
  · intro r hr1 hr2
    rw [b5 r (by omega) hr2]
    exact a5 r hr1 hr2

/-! ## Carrying a word past the families that do not read it

A word staged above a writer's control extent and inside the wider extent of the surrounding
contract is covered by that writer's frame promise, so it survives unread.  Stating the fit against
the wider extent keeps this compatible with the family that *does* read the word, which needs the
word inside its own extent. -/

/-- The placement hypotheses of `clauseWriterIO_carry_widen` at `J1 = ctlJmax` are jointly
    satisfiable, so the lemma is not vacuous there. -/
lemma clauseWriterIO_carry_satisfiable :
    ∃ M Jmax base : ℕ, ∃ xs : List ℕ,
      M + ctlJmax + 1 < base ∧ base + xs.length ≤ M + Jmax :=
  ⟨0, 20, 10, [0], by unfold ctlJmax; omega, by simp⟩

end NPComplete.CookLevin

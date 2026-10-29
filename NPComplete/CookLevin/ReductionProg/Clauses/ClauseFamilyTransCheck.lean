module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTrans

/-!
`transFamilyProg_writer`'s three table columns travel inside `Frozen` (as
`TransFrozen`, itself `PinsAndWords3`), not as a bare `∀ σ, WordAt σ base xs`
hypothesis. The latter shape is unsatisfiable by any nonempty word — a store
holding something else at those cells refutes it — so a lemma stated that way
would prove nothing no matter how strong its conclusion looks.

This file rules that failure mode out for `transFamilyProg_writer` by applying it
directly, at a concrete one-state one-letter `halt` descriptor, and exhibiting
a `Program` that satisfies the resulting `ClauseWriter`.  Producing that term
at all is only possible because every hypothesis `transFamilyProg_writer` asks for
is dischargeable — the check that matters.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A one-state, one-letter descriptor whose single table entry is `halt`. -/
def transCheckDesc : TableauDescriptor where
  numStates := 1
  startState := 0
  numLetters := 1
  blankIdx := 0
  falseIdx := 0
  trueIdx := 0
  table := [NatTrans.halt]

/-- `transFamilyProg_writer`, applied at `transCheckDesc` and three bases past the
control block.  The witness program is exactly the one `transFamilyProg_writer`
already builds; what this checks is that every hypothesis it asks for —
`d.numStates = n`, `d.numLetters = m`, and the three `M + ctlJmax < base`
separations — can be discharged at once, so the resulting `ClauseWriter` is a
real (non-vacuous) obligation on a real program. -/
lemma descTransClauses_writer_nonvacuous (W T : ℕ) :
    ∃ prog : Program, ClauseWriter prog 0
      (transJM 0 8 (transCheckDesc.table.map transKind) 8
        (transCheckDesc.table.map transArg1) 8 (transCheckDesc.table.map transArg2))
      wpJ
      (TransFrozen 0 ctlPins0 8 (transCheckDesc.table.map transKind) 8
        (transCheckDesc.table.map transArg1) 8 (transCheckDesc.table.map transArg2))
      (descTransClauses (denseLayout 1 W 1) transCheckDesc W T) :=
  ⟨_, transFamilyProg_writer 0 1 W 1 T 8 8 8 transCheckDesc rfl rfl
    (by unfold ctlJmax; omega) (by unfold ctlJmax; omega) (by unfold ctlJmax; omega)⟩

/-- The generalized writer works when both layout strides exceed their loop counts. -/
lemma trans_writer_gen_at_target_stride (M W T kindBase arg1Base arg2Base : ℕ)
    (d : TableauDescriptor) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ∃ prog : Program, ClauseWriter prog M
      (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2)) wpJ
      (TransFrozen M ctlPins0 kindBase (d.table.map transKind) arg1Base
        (d.table.map transArg1) arg2Base (d.table.map transArg2))
      (descTransClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T) :=
  ⟨_, by
    simpa only [trans_clauses_triple_family_eq_desc] using
      transFamilyProgGen_writer_gen M (d.numStates + 1) W (d.numLetters + 1)
        d.numStates d.numLetters T kindBase arg1Base arg2Base d
        hbasek hw1below hw2below⟩

end NPComplete.CookLevin

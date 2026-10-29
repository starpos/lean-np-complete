module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInit

/-!
A writer term exists as soon as its hypotheses typecheck, whether or not any
store can satisfy the `Frozen` predicate it carries.  If none can, every use of
the writer is vacuous at the point of use — the failure mode a
`∀ σ, WordAt σ base xs` hypothesis produces.

So this file checks the two things that decide it: that the initial family's
`Frozen` has a witness, and that the writer's contract yields the `RowsWritten` a
caller needs at a store meeting its entry conditions.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A one-state, one-letter descriptor whose single entry halts. -/
def initCheckDesc : TableauDescriptor where
  numStates := 1
  startState := 0
  numLetters := 1
  blankIdx := 0
  falseIdx := 0
  trueIdx := 0
  table := [NatTrans.halt]

/-- A store holding the one-symbol prefix word at base 8, with its length in the
cell below.  Everything else is zero, which is what the word's own entry is. -/
def initCheckStore : Store := fun r => if r = 7 then 1 else 0

lemma initCheckStore_word : WordAt initCheckStore 8 [0] := by
  refine ⟨by norm_num [initCheckStore], fun k hk => ?_⟩
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  norm_num [initCheckStore]

/-- The initial family's `Frozen` is satisfiable, so the writer states a real
obligation rather than one no store can trigger. -/
lemma init_frozen_satisfiable :
    ∃ τ : Store, PinsAndWord 0 ctlPins0 8 [0] τ :=
  ⟨initCheckStore, fun _ hp => absurd hp (List.not_mem_nil), initCheckStore_word⟩

/-- `initFamilyProg_writer` applied at concrete values: every hypothesis it asks for
can be discharged at once. -/
lemma descBoundedPrefixInitClauses_writer_nonvacuous (n W m T freeLen : ℕ) (allowedIdx : List ℕ) :
    ∃ prog : Program, ClauseWriter prog 0 9 wpJ (PinsAndWord 0 ctlPins0 8 [0])
      (descBoundedPrefixInitClauses (denseLayout n W m) initCheckDesc [0] freeLen
        allowedIdx W T) :=
  ⟨_, initFamilyProg_writer 0 9 n W m T 8 freeLen initCheckDesc [0] allowedIdx
    (by unfold ctlJmax; omega) (by unfold ctlJmax; omega) (by simp)⟩

/-- The contract is usable downstream: at a store meeting the entry conditions it
delivers `RowsWritten` for the family's own clause list. -/
lemma init_writer_gives_rows (n W m T freeLen : ℕ) (allowedIdx : List ℕ)
    (τ : Store) (wp : ℕ)
    (hF : PinsAndWord 0 ctlPins0 8 [0] τ) (h0 : τ 0 = 0) (hw : τ (0 + wpJ) = wp)
    (hsep : 0 + 9 < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descBoundedPrefixInitClauses (denseLayout n W m) initCheckDesc [0] freeLen
        allowedIdx W T) := by
  obtain ⟨prog, hprog⟩ := descBoundedPrefixInitClauses_writer_nonvacuous n W m T freeLen allowedIdx
  exact ⟨prog, (hprog τ wp hF h0 hw hsep).2.2.2.1⟩

end NPComplete.CookLevin

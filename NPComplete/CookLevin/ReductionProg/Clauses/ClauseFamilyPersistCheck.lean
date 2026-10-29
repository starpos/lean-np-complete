module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyPersist
public import NPComplete.CookLevin.Tableau.DenseLayout

/-!
A family writer's clause list is a large expression, and one that merely *looks*
like the family would typecheck just as well as one that *is* the family.  The
same goes for the contract around it: `ClauseWriter` bundles five conclusions,
and reading the right one out is what a caller will actually do.

Both are checked here rather than left implicit — the clause list against the
descriptor family's own definition, and the contract by extracting the
`RowsWritten` a caller needs.
-/

@[expose] public section

open NPComplete.CookLevin
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

namespace NPComplete.CookLevin

/-- The program `persistFamilyProg_writer` is about, named so the usability check
below can state its conclusion without repeating it. -/
def persistProgCheck (n W m T : ℕ) : Program :=
  persistFamilyProg n W m T

/-- The writer's clause list is the descriptor family's own definition, so the
statement is about the reduction's persistence clauses and not a lookalike. -/
lemma persist_writer_is_desc_family (n W m T : ℕ) (d : TableauDescriptor)
    (hm : d.numLetters = m) :
    execPersistClausesAt (denseLayout n W m) (List.range m) W T
      = descPersistClauses (denseLayout n W m) d W T := by
  unfold descPersistClauses
  rw [hm]

/-- The writer's conclusion is usable downstream: at any store meeting the
entry conditions it delivers `RowsWritten` for the family. -/
lemma persist_writer_gives_rows (M n W m T : ℕ) (τ : Store) (wp : ℕ)
    (hF : PinsHold M ctlPins0 τ) (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp)
    (hsep : M + ctlJmax < wp) :
    RowsWritten ((persistProgCheck n W m T).eval τ) wp
      (execPersistClausesAt (denseLayout n W m) (List.range m) W T) :=
  (persistFamilyProg_writer M n W m T τ wp hF h0 hw hsep).2.2.2.1

/-- The generalized writer reaches the descriptor family at the target strides. -/
lemma persist_writer_gen_at_target_stride (M W T : ℕ) (d : TableauDescriptor) :
    ∃ prog : Program, ClauseWriter prog M ctlJmax wpJ (PinsHold M ctlPins0)
      (descPersistClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T) :=
  ⟨_, persistFamilyProgGen_writer_gen M (d.numStates + 1) W (d.numLetters + 1)
    d.numLetters T⟩

/-- The run-time-parameter writer has a concrete program witness whose syntax
contains only the parameter-cell addresses, not the values stored there. -/
lemma persist_writer_param_nonvacuous
    (M Jmax n m mC W T wReg tReg : ℕ) (τ : Store) (wp : ℕ)
    (hplace : PersistParamPlacement Jmax wReg tReg)
    (hF : PinsHold M [(wReg, W), (tReg, T)] τ)
    (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (execPersistClausesAt (denseLayout n W m) (List.range mC) W T) :=
  ⟨persistFamilyProgParam n m mC wReg tReg,
    (persistFamilyProgParam_writer_param M Jmax n W m mC T wReg tReg hplace
      τ wp hF h0 hw hsep).2.2.2.1⟩

/-- The same parameterized program satisfies its writer contract at two
unrelated parameter pairs. -/
lemma persistFamilyProgParam_serves_any_parameters
    (M Jmax n m mC wReg tReg : ℕ) (hplace : PersistParamPlacement Jmax wReg tReg)
    (W₁ T₁ W₂ T₂ : ℕ) :
    ClauseWriter (persistFamilyProgParam n m mC wReg tReg) M Jmax wpJ
        (PinsHold M [(wReg, W₁), (tReg, T₁)])
        (execPersistClausesAt (denseLayout n W₁ m) (List.range mC) W₁ T₁) ∧
    ClauseWriter (persistFamilyProgParam n m mC wReg tReg) M Jmax wpJ
        (PinsHold M [(wReg, W₂), (tReg, T₂)])
        (execPersistClausesAt (denseLayout n W₂ m) (List.range mC) W₂ T₂) :=
  ⟨persistFamilyProgParam_writer_param M Jmax n W₁ m mC T₁ wReg tReg hplace,
    persistFamilyProgParam_writer_param M Jmax n W₂ m mC T₂ wReg tReg hplace⟩

end NPComplete.CookLevin

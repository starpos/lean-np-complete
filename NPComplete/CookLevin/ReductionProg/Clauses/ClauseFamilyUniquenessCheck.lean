module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyUniqueness
public import NPComplete.CookLevin.Tableau.DenseLayout

/-!
The uniqueness writer reuses the same two counters across the state and head
blocks, relying on each loop resetting its counter on entry.  A clause list that
merely resembles the family would typecheck just as well as the family itself,
and so would a contract whose conclusions are never read — so both are checked
here: the list against the descriptor family's own definition, and the contract
by extracting the `RowsWritten` a caller needs.
-/

@[expose] public section

open NPComplete.CookLevin
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

namespace NPComplete.CookLevin

/-- The writer's clause list is the descriptor family's own definition, so the
statement is about the reduction's uniqueness clauses. -/
lemma uniqueness_writer_is_desc_family (n W m T : ℕ) (d : TableauDescriptor)
    (hn : d.numStates = n) (hm : d.numLetters = m) :
    execUniquenessClausesAt (denseLayout n W m) (List.range n) (List.range m) W T
      = descUniquenessClauses (denseLayout n W m) d W T := by
  unfold descUniquenessClauses
  rw [hn, hm]

/-- The writer's conclusion is usable downstream: at any store meeting the entry
conditions it delivers `RowsWritten` for the family. -/
lemma uniqueness_writer_gives_rows (M n W m T : ℕ) (τ : Store) (wp : ℕ)
    (hF : PinsHold M ctlPins0 τ) (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp)
    (hsep : M + ctlJmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (execUniquenessClausesAt (denseLayout n W m) (List.range n) (List.range m) W T) :=
  ⟨_, (uniquenessFamilyProg_writer M n W m T τ wp hF h0 hw hsep).2.2.2.1⟩

/-! ## The target stride

The reduction's variable numbering uses one more state and one more letter than
the descriptor enumerates, because the range certificate requires
`stateList.length + 1`.  The separated writer handles this stride; an equal-stride
writer would require `d.numStates = d.numStates + 1`, which is impossible. -/

/-- The separated writer reaches the descriptor family at the reduction's own
stride, which is one past the descriptor's state and letter counts. -/
lemma uniqueness_writer_gen_at_target_stride (M W T : ℕ) (d : TableauDescriptor) :
    ∃ prog : Program, ClauseWriter prog M ctlJmax wpJ (PinsHold M ctlPins0)
      (descUniquenessClauses (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T) :=
  ⟨_, uniquenessFamilyProgGen_writer_gen M (d.numStates + 1) W (d.numLetters + 1)
    d.numStates d.numLetters T⟩

/-- The run-time-parameter writer executes at the reduction's target stride
when its parameter cells and the standard writer entry conditions hold. -/
lemma uniqueness_writer_param_nonvacuous
    (M Jmax W T wReg tReg : ℕ) (d : TableauDescriptor) (τ : Store) (wp : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg)
    (hF : PinsHold M [(wReg, W), (tReg, T)] τ)
    (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descUniquenessClauses
        (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d W T) :=
  ⟨uniquenessFamilyProgParam (d.numStates + 1) (d.numLetters + 1)
      d.numStates d.numLetters wReg tReg,
    (uniquenessFamilyProgParam_writer_param M Jmax (d.numStates + 1) W
      (d.numLetters + 1) d.numStates d.numLetters T wReg tReg hplace
      τ wp hF h0 hw hsep).2.2.2.1⟩

/-- One program term serves two unrelated width and time parameter pairs. -/
lemma uniquenessFamilyProgParam_serves_any_parameters
    (M Jmax nS mS nC mC wReg tReg : ℕ)
    (hplace : UniquenessParamPlacement Jmax wReg tReg) (W₁ T₁ W₂ T₂ : ℕ) :
    ClauseWriter (uniquenessFamilyProgParam nS mS nC mC wReg tReg) M Jmax wpJ
        (PinsHold M [(wReg, W₁), (tReg, T₁)])
        (execUniquenessClausesAt (denseLayout nS W₁ mS)
          (List.range nC) (List.range mC) W₁ T₁) ∧
    ClauseWriter (uniquenessFamilyProgParam nS mS nC mC wReg tReg) M Jmax wpJ
        (PinsHold M [(wReg, W₂), (tReg, T₂)])
        (execUniquenessClausesAt (denseLayout nS W₂ mS)
          (List.range nC) (List.range mC) W₂ T₂) :=
  ⟨uniquenessFamilyProgParam_writer_param M Jmax nS W₁ mS nC mC T₁ wReg tReg hplace,
    uniquenessFamilyProgParam_writer_param M Jmax nS W₂ mS nC mC T₂ wReg tReg hplace⟩

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransCheck

/-!
A non-vacuity check that only exhibits the writer term proves less than it looks:
the term exists as soon as the hypotheses typecheck, whether or not any store can
satisfy the `Frozen` predicate it carries.  If none can, every use of the writer
is still vacuous at the point of use.

So this file checks the two things that actually matter: that `TransFrozen` has a
witness, and that the writer's contract yields the `RowsWritten` a caller needs
at a store meeting its entry conditions.
-/

@[expose] public section

open NPComplete.CookLevin
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

namespace NPComplete.CookLevin

-- `TransFrozen` is satisfiable, so the writer's `Frozen` premise is not vacuous.
lemma transFrozen_satisfiable :
    ∃ τ : Store, TransFrozen 0 ctlPins0 8 (transCheckDesc.table.map transKind) 8
      (transCheckDesc.table.map transArg1) 8 (transCheckDesc.table.map transArg2) τ := by
  refine ⟨fun r => if r = 7 then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact absurd hp (List.not_mem_nil)
  · exact ⟨by norm_num [transCheckDesc], by
      intro k hk
      simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil] at hk
      have : k = 0 := by omega
      subst this
      norm_num [transCheckDesc, transKind]⟩
  · exact ⟨by norm_num [transCheckDesc], by
      intro k hk
      simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil] at hk
      have : k = 0 := by omega
      subst this
      norm_num [transCheckDesc, transArg1]⟩
  · exact ⟨by norm_num [transCheckDesc], by
      intro k hk
      simp only [transCheckDesc, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil] at hk
      have : k = 0 := by omega
      subst this
      norm_num [transCheckDesc, transArg2]⟩


-- At a store meeting the entry conditions, the writer delivers `RowsWritten` for the family's
-- own clause list.
lemma trans_writer_gives_rows (W T : ℕ) (τ : Store) (wp : ℕ)
    (hF : TransFrozen 0 ctlPins0 8 (transCheckDesc.table.map transKind) 8
      (transCheckDesc.table.map transArg1) 8 (transCheckDesc.table.map transArg2) τ)
    (h0 : τ 0 = 0) (hw : τ (0 + wpJ) = wp)
    (hsep : 0 + transJM 0 8 (transCheckDesc.table.map transKind) 8
      (transCheckDesc.table.map transArg1) 8 (transCheckDesc.table.map transArg2) < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descTransClauses (denseLayout 1 W 1) transCheckDesc W T) := by
  obtain ⟨prog, hprog⟩ := descTransClauses_writer_nonvacuous W T
  exact ⟨prog, (hprog τ wp hF h0 hw hsep).2.2.2.1⟩

end NPComplete.CookLevin

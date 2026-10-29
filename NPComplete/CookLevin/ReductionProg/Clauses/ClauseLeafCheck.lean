module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq

/-!
The leaf combinators carry enough hypotheses that a signature can typecheck while
being unusable — either because the hypotheses cannot all hold at once, or
because discharging them at a real call site is impossible.  This file rules both
out by instantiating the chain the family assembly actually walks: a leaf feeding
`clauseWriter_forN`, at a configuration whose variable expression is genuine
control-cell arithmetic rather than a constant, since a constant would satisfy
the frame and value obligations vacuously and prove nothing about the real use.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A loop whose body writes `imply3` clauses with a counter-dependent last
    variable is a `ClauseWriter` for the clause list it should be. -/
lemma clauseWriter_imply3_counter_example :
    ClauseWriter
      (loopProg 2 (.const 3)
        (leafProg 1 2 (imply3Lits (.const 5) (.const 6) (.const 7) (ctlCell 2))))
      100 4 1 (PinsHold 100 [])
      ((List.range 3).flatMap (fun i => [imply3 5 6 7 i])) := by
  refine clauseWriter_forN _ 100 4 1 2 [] _ (.const 3) 3
    (by omega) (by omega) (by omega) (by intro p hp; exact absurd hp (List.not_mem_nil)) ?_
    (fun τ _ _ _ => rfl)
  refine clauseLoopBody_imply3 100 4 1 2 (.const 5) (.const 6) (.const 7) (ctlCell 2) []
    (fun _ => 5) (fun _ => 6) (fun _ => 7) (fun i => i)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro p hp; exact absurd hp (List.not_mem_nil))
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) ?_
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) ?_
  · intro σ σ' hσ hσ' hagree
    simp only [ctlCell_eval, hσ, hσ']
    exact hagree 2 (by omega) (by omega) (by omega)
  · intro τ i hF h0 hi
    simp only [ctlCell_eval, h0]
    exact hi

end NPComplete.CookLevin

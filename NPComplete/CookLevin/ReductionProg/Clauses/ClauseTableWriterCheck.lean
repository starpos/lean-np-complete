module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableWriter

/-!
The placement calculation proves only that the words fit; the entry predicate
could still be unsatisfiable. This module exhibits a store satisfying it, verifies
the combined writer at the reduction's target strides, and derives the rows
contract for any qualifying entry store. The example establishes nonvacuity; the
downstream guarantee applies to every store meeting its hypotheses.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- A store staging five one-symbol words at the bases the placement lemma
chooses, each with its length in the cell below it. -/
def tableCheckStore : Store :=
  fun r => if r = 8 ∨ r = 11 ∨ r = 14 ∨ r = 17 ∨ r = 20 then 1 else 0

lemma tableCheckStore_word (base : ℕ)
    (h : base = 9 ∨ base = 12 ∨ base = 15 ∨ base = 18 ∨ base = 21) :
    WordAt tableCheckStore base [0] := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num [tableCheckStore],
      fun k hk => by
        have hk0 : k = 0 := by simpa using hk
        subst hk0; norm_num [tableCheckStore]⟩

/-- The concatenation's entry predicate is satisfiable, so `tableWriterProg_io`
states an obligation some store actually triggers. -/
lemma tableFrozen_satisfiable :
    TableFrozen 0 ctlPins0 9 [0] 12 [0] 15 [0] 18 [0] 21 [0] tableCheckStore := by
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro p hp; exact absurd hp (List.not_mem_nil)
  · exact tableCheckStore_word 9 (Or.inl rfl)
  · exact tableCheckStore_word 12 (Or.inr (Or.inl rfl))
  · exact tableCheckStore_word 15 (Or.inr (Or.inr (Or.inl rfl)))
  · exact tableCheckStore_word 18 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact tableCheckStore_word 21 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The combined writer reaches the reduction's layout strides while iterating
only over the descriptor's actual state and letter counts. -/
lemma tableWriterProgGen_io_at_target_stride (M Jmax W T freeLen : ℕ) (d : TableauDescriptor)
    (prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (prefIdx allowedIdx outIdx : List ℕ)
    (hPrefBase : M + ctlJmax + 1 < prefBase)
    (hPrefK : prefBase + prefIdx.length + 1 < kindBase)
    (hKA1 : kindBase + (d.table.map transKind).length + 1 < arg1Base)
    (hA1A2 : arg1Base + (d.table.map transArg1).length + 1 < arg2Base)
    (hA2Out : arg2Base + (d.table.map transArg2).length + 1 < outBase)
    (hOutFit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriterIO
      (tableWriterProgGen (d.numStates + 1) W (d.numLetters + 1)
        d.numStates d.numLetters T d prefBase prefIdx.length freeLen allowedIdx
        kindBase arg1Base arg2Base outBase outIdx)
      M Jmax wpJ
      (TableFrozen M ctlPins0 prefBase prefIdx kindBase (d.table.map transKind)
        arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2) outBase outIdx)
      (PinsHold M ctlPins0)
      (descTableauCNF (denseLayout (d.numStates + 1) W (d.numLetters + 1)) d
        prefIdx freeLen allowedIdx outIdx W T).clauses := by
  have h := tableWriterProgGen_io_gen M Jmax (d.numStates + 1) W (d.numLetters + 1)
    d.numStates d.numLetters T d prefBase freeLen prefIdx allowedIdx
    kindBase arg1Base arg2Base outBase outIdx
    hPrefBase hPrefK hKA1 hA1A2 hA2Out hOutFit
  rw [table_writer_clauses_gen_eq_desc] at h
  exact h

/-- The contract is usable downstream: at a store meeting the entry conditions it
delivers `RowsWritten` for the generator's own clause list — the five families
concatenated, not a restatement of them. -/
lemma descTableauCNF_gives_rows (W T freeLen : ℕ) (allowedIdx : List ℕ)
    (τ : Store) (wp : ℕ)
    (hF : TableFrozen 0 ctlPins0 9 [0] 12 (initCheckDesc.table.map transKind)
      15 (initCheckDesc.table.map transArg1) 18 (initCheckDesc.table.map transArg2) 21 [0] τ)
    (h0 : τ 0 = 0) (hw : τ (0 + wpJ) = wp) (hsep : 0 + 22 < wp) :
    ∃ prog : Program, RowsWritten (prog.eval τ) wp
      (descTableauCNF (denseLayout 1 W 1) initCheckDesc [0] freeLen allowedIdx [0] W T).clauses :=
  ⟨_, (tableWriterProg_io 0 22 1 W 1 T initCheckDesc 9 freeLen [0] allowedIdx 12 15 18 21 [0]
    rfl rfl (by unfold ctlJmax; omega) (by norm_num)
    (by norm_num [initCheckDesc]) (by norm_num [initCheckDesc])
    (by norm_num [initCheckDesc]) (by norm_num)
    τ wp hF h0 hw hsep).2.2.2.1⟩

end NPComplete.CookLevin

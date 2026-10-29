module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowsWritten
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableWriterCheck

/-!
The two halves of the producer were built against different vocabularies: the
materializing half states what it wrote as `RowsWritten` at the write pointer,
the emitting half states what it reads as `ClauseTableAt` at a table base held
in a register.  The two predicates are the same statement — the emitter's
precondition was defined to be the writer's postcondition — so the seam needs no
reasoning, only to be stated.

Stating it is still worth doing separately.  The writer's clause list is the
generator's own five-family concatenation rather than a `CNF`'s field, so the
handoff is where a `CNF` with that clause list gets chosen, and where the write
pointer becomes the table base the emitter's register has to hold.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Whatever a clause writer leaves in the store is exactly the table the
emitter's precondition asks for, at the pointer the writer started from. -/
lemma clauseTableAt_of_clauseWriterIO (prog : Program) (M Jmax : ℕ)
    (Entry Exit : Store → Prop) (φ : CNF) (τ : Store) (wp : ℕ)
    (h : ClauseWriterIO prog M Jmax wpJ Entry Exit φ.clauses)
    (hF : Entry τ) (h0 : τ 0 = M) (hw : τ (M + wpJ) = wp) (hsep : M + Jmax < wp) :
    ClauseTableAt (prog.eval τ) wp φ :=
  (clauseTableAt_iff_rowsWritten _ wp φ).mpr (h τ wp hF h0 hw hsep).2.2.2.1

/-! ## The emitter's registers

The emitter takes its seven control cells as parameters and asks only that they
be distinct.  Leaving them abstract through the packaging would mean carrying
twenty-two inequalities as hypotheses everywhere; fixing six of them here (the
seventh is the generator's own row-count cell) turns each into an `omega` fact
about literals, discharged once.

They sit *above* the writer's control block on purpose.  A writer's frame
promise covers exactly the cells outside its own block, so a register placed
there survives the materializing half — which is what lets the producer set up
the emitter's registers before running the writer, rather than between the two
halves where the table would already be in the way. -/

def emCurJ : ℕ := 8
def emTmpJ : ℕ := 9
def emCntJ : ℕ := 10
def emPtrJ : ℕ := 11
def emRowJ : ℕ := 12
def emTblJ : ℕ := 14

/-! ## The two halves' placements do not collide

The emitter's registers have to sit above the writer's control block, its table
above the staged words, and the output cursor below both.  That the demands
have a common solution is arithmetic, and worth exhibiting: a layout meeting
the writer's conditions but not the emitter's would make the composed producer
unbuildable with no failing proof to point at. -/

/-- A layout meeting both halves' conditions at once. -/
lemma handoff_placement_satisfiable :
    ∃ M prefBase outBase tbl cur : ℕ,
      M + ctlJmax + 1 < prefBase ∧ prefBase < outBase ∧
      M + emTblJ < tbl ∧ M + emRowJ < tbl ∧ M + emCurJ < tbl ∧
      outBase < tbl ∧ cur + 1 < M + emCurJ := by
  have hc : ctlJmax = 7 := rfl
  have h1 : emCurJ = 8 := rfl
  have h2 : emRowJ = 12 := rfl
  have h3 : emTblJ = 14 := rfl
  exact ⟨100, 120, 130, 200, 1,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end NPComplete.CookLevin

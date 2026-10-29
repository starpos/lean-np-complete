module

public import NPComplete.CookLevin.SAT
public import NPComplete.CookLevin.ToThreeCNF.Basic

/-!
`ClauseEval.lean`'s literal/clause evaluator programs and `SATVerifier.lean`'s NP-membership
proof both need the Boolean CNF check `cnfSatBool`. `ClauseEval.lean` sits upstream of
`SATVerifier.lean` in the `CNFEvalTop.lean` import chain (`ClauseEval` → `ClauseLengthEval` →
`CNFEval` → `CNFEvalAt` → `CNFEvalOuterBounded` → `CNFEvalTop`), which supplies the evaluator
used by the SAT verifier's machine-side wiring. Defining `cnfSatBool` in `SATVerifier.lean`
would make the evaluation chain depend on that module, while its machine wiring already
depends on `CNFEvalTop.lean`, creating a cycle. This module isolates the definitions at the
lowest layer that can see both `SAT.lean` (`Clause`/`CNF`) and `ToThreeCNF/Basic.lean`
(`cnfVarBound`), so the evaluator and verifier can import them without depending on each
other. `cnfVarBound_gt` also belongs here because `SATVerifierWiring.lean`'s machine half
uses it to bound the certificate variable read by a decoded literal. Keeping it in this
shared low-level module lets both import chains use it without a cycle.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT (Literal)

/-- Cell `v` of `w` gives the value of variable `v`; unset cells read `false`. -/
def decodeAssignment (w : List Bool) : Literal.Assignment :=
  fun v => w.getD v false

/-- Boolean clause check: OR over the evaluated literals. -/
def clauseSatBool (w : List Bool) (c : Clause) : Bool :=
  c.lits.any (fun l => l.eval (decodeAssignment w))

/-- Boolean CNF check: AND over the clause checks. -/
def cnfSatBool (w : List Bool) (φ : CNF) : Bool :=
  φ.clauses.all (clauseSatBool w)

lemma clauseSatBool_eq (w : List Bool) (c : Clause) :
    clauseSatBool w c = true ↔ ∃ l ∈ c.lits, l.eval (decodeAssignment w) = true := by
  simp [clauseSatBool]

lemma cnfSatBool_iff (w : List Bool) (φ : CNF) :
    cnfSatBool w φ = true ↔ ∀ c ∈ φ.clauses, c.Satisfied (decodeAssignment w) := by
  simp [cnfSatBool, Clause.Satisfied, clauseSatBool_eq]

lemma litsVarBound_ge (ls : List Literal) :
    ∀ l ∈ ls, l.var < litsVarBound ls := by
  induction ls with
  | nil => intro l hl; cases hl
  | cons l' ls ih =>
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hmem
      · simp only [litsVarBound]; omega
      · simp only [litsVarBound]
        have := ih l hmem
        omega

lemma clauseVarBound_ge (c : Clause) : ∀ l ∈ c.lits, l.var < clauseVarBound c :=
  litsVarBound_ge c.lits

lemma clausesVarBound_ge (cs : List Clause) (c : Clause) (hc : c ∈ cs) :
    clauseVarBound c ≤ clausesVarBound cs := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
      rcases List.mem_cons.mp hc with rfl | hmem
      · simp only [clausesVarBound]; omega
      · simp only [clausesVarBound]
        have := ih hmem
        omega

/-- Every literal of every clause of `φ` has variable below `cnfVarBound φ`. -/
lemma cnfVarBound_gt (φ : CNF) :
    ∀ c ∈ φ.clauses, ∀ l ∈ c.lits, l.var < cnfVarBound φ := by
  intro c hc l hl
  have h1 := clauseVarBound_ge c l hl
  have h2 := clausesVarBound_ge φ.clauses c hc
  have h3 : cnfVarBound φ = clausesVarBound φ.clauses := rfl
  omega

end NPComplete.CookLevin

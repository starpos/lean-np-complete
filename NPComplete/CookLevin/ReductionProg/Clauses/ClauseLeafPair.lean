module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.Tableau.TableauRamLoops

/-!
The uniqueness family's `atMostOne` emits a clause shape none of the reduction's
named constructors covers: two negative literals, written as an anonymous
`Clause` in `atMostOne`'s own definition.  Since `atMostOneRange` states that
family as a range nest whose innermost step produces exactly that shape, the leaf
for it belongs with the other constructors' leaves rather than inside the family
proof.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-- The two-negative-literal clause `atMostOne` pairs its arguments into. -/
def negPair (a b : ℕ) : Clause := ⟨[Literal.neg a, Literal.neg b]⟩

lemma negPair_var0 (a b : ℕ) : litVar ((negPair a b).lits.getD 0 default) = a := rfl
lemma negPair_var1 (a b : ℕ) : litVar ((negPair a b).lits.getD 1 default) = b := rfl

/-- The all-pairs family as the loop nest the producer runs: an outer range over
the first element and an inner range over the strictly later ones, each iteration
writing one `negPair`. -/
lemma atMostOneRange_eq_negPair (vs : List ℕ) :
    atMostOneRange vs
      = (List.range vs.length).flatMap fun i =>
          (List.range (vs.length - i - 1)).map fun j =>
            negPair (vs.getD i 0) (vs.getD (i + 1 + j) 0) := rfl

/-- One uniqueness iteration writes a run-time-width `atLeastOne` followed by the
all-pairs nest — the two leaf shapes, in the order the writer emits them. -/
lemma exactlyOne_eq_atLeastOne_cons (vs : List ℕ) :
    exactlyOne vs = atLeastOne vs :: atMostOneRange vs := by
  unfold exactlyOne
  rw [atMostOne_eq_atMostOneRange]

/-- The two literal expressions of a `negPair` clause. -/
def negPairLits (aE bE : Expr) : List (Expr × Expr) :=
  [(.const 1, aE), (.const 1, bE)]

lemma negPairLits_length (aE bE : Expr) : (negPairLits aE bE).length = 2 := rfl

lemma negPairLits_get0 (aE bE : Expr) :
    (negPairLits aE bE).getD 0 defLit = (.const 1, aE) := rfl
lemma negPairLits_get1 (aE bE : Expr) :
    (negPairLits aE bE).getD 1 defLit = (.const 1, bE) := rfl

/-- Specializes the leaf combinator to `negPair`. -/
lemma clauseLoopBody_negPair (M Jmax wpJ iJ : ℕ) (aE bE : Expr)
    (pins : List (ℕ × ℕ)) (av bv : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hdepA : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → aE.eval σ' = aE.eval σ)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → bE.eval σ' = bE.eval σ)
    (hvalA : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      aE.eval τ = av i)
    (hvalB : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      bE.eval τ = bv i) :
    ClauseLoopBody (leafProg wpJ iJ (negPairLits aE bE)) M Jmax wpJ iJ (PinsHold M pins)
      (fun i => [negPair (av i) (bv i)]) := by
  refine clauseLoopBody_leaf M Jmax wpJ iJ (negPairLits aE bE) pins
    (fun i => negPair (av i) (bv i)) hwpJ hwpJmax hiJ hiJmax hne hpin ?_ ?_ ?_
  · intro p hp σ σ' hσ hσ' hagree
    simp only [negPairLits, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, hdepA σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepB σ σ' hσ hσ' hagree⟩
  · intro i; rfl
  · intro τ i k hF h0 hi hk
    rw [negPairLits_length] at hk
    interval_cases k
    · rw [negPairLits_get0]
      exact ⟨rfl, by rw [negPair_var0]; exact hvalA τ i hF h0 hi⟩
    · rw [negPairLits_get1]
      exact ⟨rfl, by rw [negPair_var1]; exact hvalB τ i hF h0 hi⟩

end NPComplete.CookLevin

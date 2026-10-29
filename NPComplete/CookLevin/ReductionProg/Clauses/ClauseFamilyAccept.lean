module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteLoop

/-!
The accept family's fixed-width clauses are `implyPos` clauses, so the family
needs a leaf that writes one such clause per counter value.  `implyPosLits`
pairs constant tag expressions with two caller-supplied variable expressions.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The fixed-width part

`implyPos a b` is two literals, `(true, a)` and `(false, b)`, so the leaf's
literal list is two expression pairs and the clause's width is `2` at every
index — exactly the `hlen` the leaf combinator asks for. -/

lemma implyPos_len (a b : ℕ) : (implyPos a b).lits.length = 2 := rfl

lemma implyPos_var0 (a b : ℕ) : litVar ((implyPos a b).lits.getD 0 default) = a := rfl
lemma implyPos_var1 (a b : ℕ) : litVar ((implyPos a b).lits.getD 1 default) = b := rfl

/-- The two literal expressions of an `implyPos` clause, given expressions for
    its two variable numbers. -/
def implyPosLits (aE bE : Expr) : List (Expr × Expr) :=
  [(.const 1, aE), (.const 0, bE)]

lemma implyPosLits_length (aE bE : Expr) : (implyPosLits aE bE).length = 2 := rfl

lemma implyPosLits_get0 (aE bE : Expr) : (implyPosLits aE bE).getD 0 defLit = (.const 1, aE) := rfl
lemma implyPosLits_get1 (aE bE : Expr) : (implyPosLits aE bE).getD 1 defLit = (.const 0, bE) := rfl

end NPComplete.CookLevin

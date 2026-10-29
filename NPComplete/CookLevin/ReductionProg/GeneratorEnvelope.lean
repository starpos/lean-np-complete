module

public import NPComplete.CookLevin.ReductionProg.GeneratorProg
public import NPComplete.CookLevin.ReductionProg.GeneratorSizePoly
public import NPComplete.CookLevin.Tableau.TableauVarBound
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowsWritten

/-!
`ProgramBoundedIn B σ p` asks that every intermediate an expression evaluates —
not just the values a program finally stores — stay under `B`, and the packaging
asks in turn that `B` be polynomial in the input length.  So the envelope has to
dominate three separate quantities, and each needs its own majorant before they
can be added:

* the addresses the generator touches, whose top is the end of the clause table;
* the values it writes, which are dense-layout variable numbers;
* the intermediates of the two size computations, which Horner's rule produces.

The three are gathered here rather than inside the boundedness proof, because
each is a statement about the *specification* — how large the tableau is — and
holds whether or not any program is involved.  Keeping them separate is also what
lets the boundedness proof cite one inequality per obligation instead of
re-deriving the tableau's dimensions at every leaf.

Two gaps between these majorants and what the boundedness proof will need are
worth stating before they are papered over.

`ExprBoundedIn` bounds a `.const` by its own value, so Horner's evaluation is not
covered by a bound on what it evaluates *to*: the polynomial's coefficients are
themselves subterms.  With `p = 100 * X` at input length `0`, the cubic part
`setupSpan p 0 ^ 3 + 30` of `setupM` is `57` while the coefficient `100` sits
inside the expression.  The envelope therefore needs a majorant of the
coefficients, not only of the value — a shift such as `q.comp (X + 1)` is the
shape that covers both.

And `ProgramBoundedIn` on `.ifNZ` demands *both* branches be bounded, while the
specification's variable bound speaks only of clauses the generator actually
emits.  The transition leaf is a branch tree whose unselected arms still carry
dense-layout expressions, so those need a bound of their own, from the
descriptor's columns rather than from the emitted clause list.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM

/-! ## The workspace base

`setupM` is a cube of the input span plus the output-length majorant
`emitLenPoly`; naming its polynomial form is what lets the envelope be stated
as a polynomial rather than as an evaluation. -/

/-- `setupM` as a polynomial in the input length. -/
noncomputable def setupMPoly (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Polynomial ℕ :=
  (2 * X + 3 + p) * ((2 * X + 3 + p) * (2 * X + 3 + p)) + C 30 +
    emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length

lemma setupMPoly_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) :
    (setupMPoly p time d allowedIdx).eval N = setupM p time d allowedIdx N := by
  simp [setupMPoly, setupM, setupSpan]

/-! ## Horner's own constants

The constants a Horner expression carries are the polynomial's coefficients, and
`ExprBoundedIn` bounds a constant by its own value rather than by what the
expression evaluates to.  Over `ℕ` the coefficients sum to the evaluation at `1`,
so that single number dominates all of them at once — and being a constant, it is
trivially polynomial in the input length. -/

/-- A coefficient is at most the polynomial's value at `1`, which over `ℕ` is the
sum of the coefficients. -/
lemma coeff_le_eval_one (q : Polynomial ℕ) (i : ℕ) : q.coeff i ≤ q.eval 1 := by
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  by_cases h : i ∈ q.support
  · have := Finset.single_le_sum (f := fun j => q.coeff j * 1 ^ j)
      (fun j _ => Nat.zero_le _) h
    simpa using this
  · rw [Polynomial.notMem_support_iff.mp h]; exact Nat.zero_le _

/-! ## The table's extent

A row is two header cells plus two per literal, so the table is at most the row
count times the widest row.  Both factors already have majorants — the clause
count from the closed formula, the width from the family-by-family bound — and
this lemma is what turns the pair into an extent. -/

/-- The table occupies at most `q * (2 + 2 * L)` cells when no row is wider than
`L`. -/
lemma rowTableWidth_le_count_mul (f : ℕ → ℕ) (q L : ℕ) (hf : ∀ i, i < q → f i ≤ L) :
    rowTableWidth f q ≤ q * (2 + 2 * L) := by
  induction q with
  | zero => simp [rowTableWidth_zero]
  | succ k ih =>
      rw [rowTableWidth_succ]
      have h1 : rowTableWidth f k ≤ k * (2 + 2 * L) := ih (fun i hi => hf i (by omega))
      have h2 : f k ≤ L := hf k (by omega)
      have h3 : (k + 1) * (2 + 2 * L) = k * (2 + 2 * L) + (2 + 2 * L) := by ring
      omega

end NPComplete.CookLevin

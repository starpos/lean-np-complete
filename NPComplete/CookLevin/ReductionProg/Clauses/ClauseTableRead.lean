module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.Tableau.NatTableau

/-!
Four of the five families compute every variable number arithmetically, but the
accept and initial families read a tape symbol out of a list — `natInitSymbol`
indexes the output or prefix word, falling back to the blank outside it.  A list
is not something an expression can hold, so the producer keeps it in the store
and reads it with `regInd`.

Two things have to be pinned down for that to work.  First, the signed index:
`natInitSymbol` tests `0 ≤ p` on a difference of two window positions, which on
naturals is the comparison `pHead ≤ p`, and the index is then the truncated
subtraction — so the expression language's `lt` and `sub` suffice, with no
integers anywhere.  Second, the out-of-range fallback: `getD` returns the blank
past the end, which the expression reproduces by comparing against the stored
length rather than by relying on whatever happens to sit above the list.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The signed index is a natural comparison

`natInitSymbol`'s argument is always a difference of two window positions, and
the only thing its sign test can see is whether the subtrahend is the larger. -/

lemma natInitSymbol_sub (blank : ℕ) (xs : List ℕ) (p q : ℕ) :
    natInitSymbol blank xs ((p : ℤ) - (q : ℤ))
      = if q ≤ p then xs.getD (p - q) blank else blank := by
  unfold natInitSymbol
  by_cases h : q ≤ p
  · rw [ite_eq_left (by omega), ite_eq_left h]
    congr 1
    omega
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-! ## A word in the store

`WordAt σ base blank xs` says the list `xs` occupies cells `base .. base+len-1`
with its length in the cell below the data, which is the layout an expression can
index without knowing the length at compile time. -/

/-- The list `xs` sits at `base`, with its length one cell below it. -/
def WordAt (σ : Store) (base : ℕ) (xs : List ℕ) : Prop :=
  σ (base - 1) = xs.length ∧ ∀ k, k < xs.length → σ (base + k) = xs.getD k 0

/-- Reading index `kE` of the word at `base`, with the blank supplied for
    out-of-range indices.

    The length is a compile-time constant, not a store-cell read.  The producer
    fixes it when selected for its word.  Keeping it fixed bounds the read
    address statically: a length supplied by an arbitrary store could permit a
    read above the write pointer, outside the scope of the frame condition. -/
def wordReadE (base blank len : ℕ) (kE : Expr) : Expr :=
  .add
    (.mul (.lt kE (.const len)) (.regInd (.add (.const base) (.mul (.lt kE (.const len)) kE))))
    (.mul (.sub (.const 1) (.lt kE (.const len))) (.const blank))

/-- The read returns the list's element inside the list and the blank outside,
    which is exactly `getD` at the blank. -/
lemma wordReadE_eval (σ : Store) (base blank : ℕ) (xs : List ℕ) (kE : Expr)
    (hw : WordAt σ base xs) :
    (wordReadE base blank xs.length kE).eval σ = xs.getD (kE.eval σ) blank := by
  obtain ⟨hlen, hdata⟩ := hw
  unfold wordReadE
  simp only [Expr.eval]
  by_cases h : kE.eval σ < xs.length
  · simp [h]
    rw [hdata (kE.eval σ) h]
    rw [List.getD_eq_getElem xs 0 h]
  · simp [h]

/-- A word read whose base and length are supplied by expressions. -/
def wordReadEExpr (baseE lenE : Expr) (blank : ℕ) (kE : Expr) : Expr :=
  .add
    (.mul (.lt kE lenE) (.regInd (.add baseE (.mul (.lt kE lenE) kE))))
    (.mul (.sub (.const 1) (.lt kE lenE)) (.const blank))

lemma wordReadEExpr_eval (σ : Store) (base blank : ℕ) (xs : List ℕ)
    (baseE lenE kE : Expr)
    (hbase : baseE.eval σ = base) (hlen : lenE.eval σ = xs.length)
    (hw : WordAt σ base xs) :
    (wordReadEExpr baseE lenE blank kE).eval σ = xs.getD (kE.eval σ) blank := by
  obtain ⟨_, hdata⟩ := hw
  unfold wordReadEExpr
  simp only [Expr.eval, hbase, hlen]
  by_cases h : kE.eval σ < xs.length
  · simp [h]
    rw [hdata (kE.eval σ) h]
    rw [List.getD_eq_getElem xs 0 h]
  · simp [h]

/-! ## Guarding the read

The two families wrap the read in a sign test, so the expression that computes a
symbol is the read multiplied by the guard plus the blank multiplied by its
negation — the same shape as the length test, one level out. -/

/-- The symbol at signed offset `p - q`, as an expression: blank when `q > p`,
    otherwise the word's entry at `p - q`. -/
def symbolAtE (base blank len : ℕ) (pE qE : Expr) : Expr :=
  .add
    (.mul (.sub (.const 1) (.lt pE qE)) (wordReadE base blank len (.sub pE qE)))
    (.mul (.lt pE qE) (.const blank))

lemma symbolAtE_eval (σ : Store) (base blank : ℕ) (xs : List ℕ) (pE qE : Expr)
    (hw : WordAt σ base xs) :
    (symbolAtE base blank xs.length pE qE).eval σ
      = natInitSymbol blank xs ((pE.eval σ : ℤ) - (qE.eval σ : ℤ)) := by
  rw [natInitSymbol_sub]
  unfold symbolAtE
  simp only [Expr.eval]
  by_cases h : pE.eval σ < qE.eval σ
  · rw [ite_eq_left h, ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right h, ite_eq_left (by omega)]
    have hread := wordReadE_eval σ base blank xs (.sub pE qE) hw
    simp only [Expr.eval] at hread
    rw [hread]
    omega

end NPComplete.CookLevin

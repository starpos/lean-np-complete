module

public import NPComplete.CookLevin.Tableau.DenseLayout
public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalize

/-!
The clause families are written with list recursion and `if`-guarded skips, but
the RAM language has no list recursion, and a guarded skip would make the number
of emitted clauses depend on the data. A `forN` has a fixed trip count, so
staging the clause count requires each iteration's contribution to be independent
of the data.

Rewriting the two offending families into plain nested ranges is what closes the
gap.  `atMostOne`'s all-pairs recursion becomes an outer range over the first
index and an inner range whose *trip count* shrinks with it — expressible because
`Expr` has truncated subtraction — and the persistence family's "every cell but
the head one" becomes two consecutive ranges instead of a skipped iteration.
Neither needs padding, and every iteration emits exactly one clause, which is
what the unary length prefix in the output encoding demands.

The triangular-number accumulator serves the same encoding constraint from the
other side: the clause count must be staged before any clause bit is written,
and the closed form for this count uses division by `2`.
Computing it by summation avoids needing division in `Expr` at all.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## Splitting a range around one excluded index -/

lemma range_split_at (W pHead : ℕ) (hp : pHead < W) :
    List.range W = List.range pHead ++ List.range' pHead (W - pHead) := by
  rw [List.range_eq_range',
    show (List.range pHead) = List.range' 0 pHead from List.range_eq_range']
  have h := @List.range'_append 0 pHead (W - pHead) 1
  simp only [Nat.one_mul, Nat.zero_add] at h
  rw [h, show pHead + (W - pHead) = W by omega]

/-- A shifted range is the base range under an offset map, the form a RAM loop
over `j` with body index `a + j` produces. -/
lemma range'_eq_map_range (a n : ℕ) :
    List.range' a n = (List.range n).map (fun j => a + j) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [List.range'_succ, List.range_succ_eq_map, List.map_cons, ih (a + 1), List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro j _
      simp
      omega

/-- The persistence family's guarded skip, rewritten as two unguarded loops.
A RAM `forN` cannot skip an iteration without making its emission count depend
on the index, so the excluded index is removed from the iteration space instead. -/
lemma persist_range_split (W pHead : ℕ) (hp : pHead < W) (g : ℕ → List Clause) :
    ((List.range W).flatMap fun pCell => if pHead = pCell then [] else g pCell) =
      (List.range pHead).flatMap g
        ++ (List.range (W - pHead - 1)).flatMap (fun j => g (pHead + 1 + j)) := by
  rw [range_split_at W pHead hp, List.flatMap_append]
  congr 1
  · apply List.flatMap_congr
    intro i hi
    rw [ite_eq_right (by have := List.mem_range.mp hi; omega)]
  · rw [show W - pHead = (W - pHead - 1) + 1 by omega, List.range'_succ,
      List.flatMap_cons, ite_eq_left rfl, List.nil_append,
      range'_eq_map_range, List.flatMap_map]
    apply List.flatMap_congr
    intro j _
    rw [ite_eq_right (by omega)]

/-! ## The all-pairs family as nested ranges -/

lemma getD_cons_succ (v : ℕ) (vs : List ℕ) (k : ℕ) :
    (v :: vs).getD (k + 1) 0 = vs.getD k 0 := by
  simp [List.getD_eq_getElem?_getD]

/-- A list-driven map, re-indexed through the list's own range.  The bridge
between a family written over a support list and the same family written over
`List.range`, which is all a RAM loop can iterate. -/
lemma map_eq_map_range_getD (vs : List ℕ) (g : ℕ → Clause) :
    vs.map (fun w => g w) = (List.range vs.length).map (fun j => g (vs.getD j 0)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    have hi : i < vs.length := by simpa using h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `atMostOne` as a RAM loop nest: the outer index picks the first element, the
inner *trip count* `n - i - 1` covers exactly the strictly later ones.  Every
iteration emits exactly one clause, so the total is a closed formula and no
padding is needed to make the count uniform. -/
def atMostOneRange (vs : List ℕ) : List Clause :=
  (List.range vs.length).flatMap fun i =>
    (List.range (vs.length - i - 1)).map fun j =>
      ⟨[Literal.neg (vs.getD i 0), Literal.neg (vs.getD (i + 1 + j) 0)]⟩

lemma atMostOne_eq_atMostOneRange (vs : List ℕ) : atMostOne vs = atMostOneRange vs := by
  induction vs with
  | nil => simp [atMostOne, atMostOneRange]
  | cons v vs ih =>
      rw [atMostOne_cons, ih]
      unfold atMostOneRange
      simp only [List.length_cons]
      rw [List.range_succ_eq_map, List.flatMap_cons]
      have hhead : (v :: vs).getD 0 0 = v := rfl
      congr 1
      · rw [map_eq_map_range_getD vs (fun w => ⟨[Literal.neg v, Literal.neg w]⟩)]
        simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.zero_add, hhead]
        apply List.map_congr_left
        intro j _
        rw [show (1 : ℕ) + j = j + 1 by omega, getD_cons_succ]
      · rw [List.flatMap_map]
        apply List.flatMap_congr
        intro i _
        simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right]
        apply List.map_congr_left
        intro j _
        rw [show i + 1 + 1 + j = (i + 1 + j) + 1 by omega, getD_cons_succ, getD_cons_succ]

/-! ## Triangular numbers without division

The clause count has to reach a control cell before the first clause bit is
written, and its closed form carries a `/2` that `Expr` cannot express.  Summing
the indices produces the same value, and the doubled identity below lets the
count be related to the closed form without ever dividing. -/

def triAcc : ℕ → ℕ
  | 0 => 0
  | n + 1 => triAcc n + n

lemma two_mul_triAcc (n : ℕ) : 2 * triAcc n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [triAcc, Nat.mul_add, ih]
      cases n with
      | zero => rfl
      | succ k => simp; ring

/-- The generator's clause count with every division replaced by a triangular
number.  This is the value the producer stages before writing any clause bit;
`clauseCount_eq` ties it to the generator so no division-carrying form of the
count is ever needed. -/
def clauseCount (n m T W freeLen : ℕ) : ℕ :=
  (T + 1) * (triAcc n + 1 + (triAcc W + 1) + W * (triAcc m + 1))
  + (2 + W + freeLen)
  + T * W * n * m * 3
  + T * W * (W - 1) * m
  + (W * W + 1)

lemma clauseCount_eq (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) (W T : ℕ) :
    clauseCount d.numStates d.numLetters T W freeLen =
      (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses.length := by
  have h2 := descTableauCNF_length v d prefIdx freeLen allowedIdx outIdx W T
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by omega)
  rw [h2]
  unfold clauseCount
  rw [← two_mul_triAcc d.numStates, ← two_mul_triAcc d.numLetters, ← two_mul_triAcc W]
  ring

/-! ## The transition table as flat numeric columns

A RAM store holds numbers, not `NatTrans` values, and the bit-cost bound rules
out the DSL's own table-lookup constructor.  Splitting the table into three
numeric columns avoids both problems at once: the transition at a state/letter
pair is read by the same row-major index from each column, so the lookup is
arithmetic — no per-entry branch tree over the table's size. -/

def transKind : NatTrans → ℕ
  | .halt => 0
  | .write _ _ => 1
  | .move _ _ => 2

def transArg1 : NatTrans → ℕ
  | .halt => 0
  | .write q' _ => q'
  | .move q' _ => q'

def transArg2 : NatTrans → ℕ
  | .halt => 0
  | .write _ b => b
  | .move _ d => match d with | .left => 0 | .right => 1

/-! ## Evaluating a fixed polynomial at run time

The tableau's time bound and certificate bound are polynomial evaluations at the
input length, so the producer has to compute them while running.  The polynomial
is fixed once the implementation is chosen, so its coefficients are constants and
Horner's rule turns the evaluation into the `add`/`mul`/`const` fragment the RAM
expression language provides.

The degree is read off `support` rather than `natDegree`, which keeps the whole
argument inside the polynomial API this development already depends on. -/

def hornerExpr (coeffs : List ℕ) (e : Expr) : Expr :=
  coeffs.foldr (fun c acc => Expr.add (Expr.const c) (Expr.mul e acc)) (Expr.const 0)

def hornerVal (coeffs : List ℕ) (x : ℕ) : ℕ :=
  coeffs.foldr (fun c acc => c + x * acc) 0

lemma hornerExpr_eval (coeffs : List ℕ) (e : Expr) (σ : Store) :
    (hornerExpr coeffs e).eval σ = hornerVal coeffs (e.eval σ) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      simp only [hornerExpr, hornerVal, List.foldr_cons, Expr.eval] at ih ⊢
      rw [ih]

lemma hornerVal_eq_sum (coeffs : List ℕ) (x : ℕ) :
    hornerVal coeffs x = ∑ i ∈ Finset.range coeffs.length, coeffs.getD i 0 * x ^ i := by
  induction coeffs with
  | nil => simp [hornerVal]
  | cons c cs ih =>
      rw [hornerVal, List.foldr_cons, ← hornerVal, ih]
      simp only [List.length_cons, Finset.sum_range_succ']
      simp [Finset.mul_sum]
      ring_nf

/-- One past the largest exponent carried by the polynomial. -/
noncomputable def polyLen (p : Polynomial ℕ) : ℕ := p.support.sup id + 1

noncomputable def coeffList (p : Polynomial ℕ) : List ℕ :=
  (List.range (polyLen p)).map (fun i => p.coeff i)

lemma coeffList_length (p : Polynomial ℕ) : (coeffList p).length = polyLen p := by
  simp [coeffList]

lemma coeffList_getD (p : Polynomial ℕ) (i : ℕ) (hi : i < polyLen p) :
    (coeffList p).getD i 0 = p.coeff i := by
  unfold coeffList
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

lemma eval_eq_sum_polyLen (p : Polynomial ℕ) (x : ℕ) :
    p.eval x = ∑ i ∈ Finset.range (polyLen p), p.coeff i * x ^ i := by
  conv_lhs => rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum]
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range, polyLen]
    exact Nat.lt_succ_of_le (by simpa using Finset.le_sup (f := id) hi)
  · intro i _ hni
    rw [Polynomial.notMem_support_iff.mp hni]
    ring

lemma hornerVal_coeffList (p : Polynomial ℕ) (x : ℕ) :
    hornerVal (coeffList p) x = p.eval x := by
  rw [hornerVal_eq_sum, coeffList_length, eval_eq_sum_polyLen]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeffList_getD p i (Finset.mem_range.mp hi)]

/-- The producer's run-time evaluation of a fixed polynomial agrees with the
polynomial's own evaluation, so a specification stated with `Polynomial.eval`
can be met by a program built from constants. -/
lemma hornerExpr_coeffList_eval (p : Polynomial ℕ) (e : Expr) (σ : Store) :
    (hornerExpr (coeffList p) e).eval σ = p.eval (e.eval σ) := by
  rw [hornerExpr_eval, hornerVal_coeffList]

end NPComplete.CookLevin

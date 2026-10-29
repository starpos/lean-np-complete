module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# 3-SAT Definition

This module provides a common fixed-arity 3-CNF syntax and satisfaction predicate for reductions
and verifiers, together with predicates for bounded instances and clauses with distinct variables.
-/

@[expose] public section

namespace NPComplete.SAT

/-- A literal is either a positive variable xᵢ or a negative variable ¬xᵢ. -/
@[stable_api] inductive Literal where
  | pos : Nat → Literal  -- xᵢ
  | neg : Nat → Literal  -- ¬xᵢ
  deriving DecidableEq, Repr

namespace Literal

/-- Get the variable index of a literal. -/
@[stable_api] def var : Literal → Nat
  | pos i => i
  | neg i => i

/-- Check if a literal is positive. -/
@[stable_api] def is_pos : Literal → Bool
  | pos _ => true
  | neg _ => false

/-- Check if a literal is negative. -/
def is_neg : Literal → Bool
  | pos _ => false
  | neg _ => true

/-- A truth assignment maps variables to boolean values. -/
@[stable_api] def Assignment := Nat → Bool

/-- Evaluate a literal under an assignment. -/
@[stable_api] def eval (a : Assignment) : Literal → Bool
  | pos i => a i
  | neg i => !(a i)

/-- The negation of a literal. -/
@[stable_api] def negate : Literal → Literal
  | pos i => neg i
  | neg i => pos i

@[stable_api] lemma var_negate (l : Literal) : l.negate.var = l.var := by
  cases l <;> rfl

@[stable_api] lemma is_pos_negate (l : Literal) : l.negate.is_pos = !l.is_pos := by
  cases l <;> rfl

lemma eval_negate (a : Assignment) (l : Literal) : l.negate.eval a = !(l.eval a) := by
  cases l <;> simp [eval, negate, Bool.not_not]

end Literal

/-- A 3-clause is a disjunction of exactly 3 literals. -/
@[stable_api] structure ThreeClause where
  l1 : Literal
  l2 : Literal
  l3 : Literal
  deriving DecidableEq, Repr

namespace ThreeClause

/-- Get all literals in a clause as a list. -/
@[stable_api] def literals (c : ThreeClause) : List Literal := [c.l1, c.l2, c.l3]

/-- Get literal at position k (0, 1, or 2). -/
def literal_at (c : ThreeClause) (k : Nat) : Option Literal :=
  match k with
  | 0 => some c.l1
  | 1 => some c.l2
  | 2 => some c.l3
  | _ => none

/-- literal_at returns the same as indexing literals list. -/
lemma literal_at_eq_literals_get (c : ThreeClause) (k : Nat) (hk : k < 3) :
    c.literal_at k = some (c.literals[k]'(by simp [literals]; omega)) := by
  interval_cases k <;> rfl

/-- If `literal_at k = some lit` and the clause is bounded by `n`, then `lit.var < n`. -/
lemma literal_at_var_lt_of_bounded (c : ThreeClause) (n : Nat)
    (hb : c.l1.var < n ∧ c.l2.var < n ∧ c.l3.var < n)
    (k : Nat) (hk : k < 3) (lit : Literal)
    (hlit : c.literal_at k = some lit) : lit.var < n := by
  have heq := literal_at_eq_literals_get c k hk
  rw [hlit] at heq
  have hl_eq : lit = c.literals[k] := Option.some_inj.mp heq
  rw [congrArg Literal.var hl_eq]; simp only [literals]
  interval_cases k <;> simp_all

/-- Check if a clause contains a specific variable. -/
def contains_var (c : ThreeClause) (v : Nat) : Bool :=
  c.l1.var == v || c.l2.var == v || c.l3.var == v

/-- If `literal_at k = some l` (with `k < 3`), then `contains_var l.var = true`. -/
lemma contains_var_of_literal_at {c : ThreeClause} {k : Nat} {l : Literal}
    (hk : k < 3) (h : c.literal_at k = some l) :
    c.contains_var l.var = true := by
  interval_cases k <;> simp [literal_at] at h <;> cases h <;> simp [contains_var]

/-- A clause is satisfied if at least one literal evaluates to true. -/
@[stable_api] def Satisfied (a : Literal.Assignment) (c : ThreeClause) : Prop :=
  c.l1.eval a = true ∨ c.l2.eval a = true ∨ c.l3.eval a = true

/-- Decidable satisfaction check. -/
def is_satisfied (a : Literal.Assignment) (c : ThreeClause) : Bool :=
  c.l1.eval a || c.l2.eval a || c.l3.eval a

lemma is_satisfied_iff_satisfied (a : Literal.Assignment) (c : ThreeClause) :
    c.is_satisfied a = true ↔ c.Satisfied a := by
  simp only [is_satisfied, Satisfied, Bool.or_eq_true, or_assoc]

/-- Check if a clause has both positive and negative literals (mixed clause). -/
def is_mixed (c : ThreeClause) : Bool :=
  (c.l1.is_pos || c.l2.is_pos || c.l3.is_pos) &&
  (c.l1.is_neg || c.l2.is_neg || c.l3.is_neg)

/-- If a clause has a positive literal at some position and a negative literal at some (possibly
    other) position, then `is_mixed = true`. -/
lemma is_mixed_of_literal_at_pos_of_literal_at_neg {c : ThreeClause} {kpos kneg jpos jneg : Nat}
    (hkpos : kpos < 3) (hkneg : kneg < 3)
    (hpos : c.literal_at kpos = some (Literal.pos jpos))
    (hneg : c.literal_at kneg = some (Literal.neg jneg)) :
    c.is_mixed = true := by
  interval_cases kpos <;> interval_cases kneg <;>
    simp [literal_at] at hpos hneg <;>
    first
    | rw [hpos] at hneg; contradiction
    | simp [is_mixed, Literal.is_pos, Literal.is_neg, hpos, hneg]

/-- A clause has no repeated variables when its three literals refer to pairwise
    distinct variables. -/
def NoRepeatedVars (c : ThreeClause) : Prop :=
  c.l1.var ≠ c.l2.var ∧ c.l2.var ≠ c.l3.var ∧ c.l1.var ≠ c.l3.var

/-- Decidable check for no repeated variables. -/
def check_no_repeated_vars (c : ThreeClause) : Bool :=
  c.l1.var != c.l2.var && c.l2.var != c.l3.var && c.l1.var != c.l3.var

lemma check_no_repeated_vars_iff (c : ThreeClause) :
    c.check_no_repeated_vars = true ↔ c.NoRepeatedVars := by
  simp only [check_no_repeated_vars, NoRepeatedVars, Bool.and_eq_true, bne_iff_ne, and_assoc]

/-- Get all variables in a clause as a list. -/
def vars (c : ThreeClause) : List Nat := [c.l1.var, c.l2.var, c.l3.var]

/-- If a literal is in the clause literals, its variable is in the clause vars. -/
lemma var_mem_of_mem_literals (c : ThreeClause) (l : Literal) (hl : l ∈ c.literals) :
    l.var ∈ c.vars := by
  unfold literals at hl; unfold vars
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl ⊢
  rcases hl with rfl | rfl | rfl <;> tauto

/-- A variable is in vars iff contains_var is true. -/
lemma contains_var_iff_mem_vars (c : ThreeClause) (v : Nat) :
    c.contains_var v = true ↔ v ∈ c.vars := by
  unfold contains_var vars
  simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.mem_nil_iff, or_false]
  tauto

end ThreeClause

/-- A 3-CNF formula is a conjunction of 3-clauses over a fixed number of variables. -/
@[stable_api] structure ThreeCNF where
  numVars : Nat
  clauses : List ThreeClause
  deriving Repr

namespace ThreeCNF

/-- A formula is satisfied if all clauses are satisfied. -/
@[stable_api] def Satisfied (a : Literal.Assignment) (f : ThreeCNF) : Prop :=
  ∀ c ∈ f.clauses, c.Satisfied a

/-- Decidable satisfaction check. -/
def is_satisfied (a : Literal.Assignment) (f : ThreeCNF) : Bool :=
  f.clauses.all (·.is_satisfied a)

lemma is_satisfied_iff_satisfied (a : Literal.Assignment) (f : ThreeCNF) :
    f.is_satisfied a = true ↔ f.Satisfied a := by
  simp only [is_satisfied, Satisfied, List.all_eq_true]
  constructor
  · intro h c hc
    exact (ThreeClause.is_satisfied_iff_satisfied a c).mp (h c hc)
  · intro h c hc
    exact (ThreeClause.is_satisfied_iff_satisfied a c).mpr (h c hc)

end ThreeCNF

/-- The 3-SAT problem: is a 3-CNF formula satisfiable? -/
@[stable_api] def ThreeSAT (f : ThreeCNF) : Prop := ∃ a, f.Satisfied a

/-- Alternative characterization using decidable check. -/
lemma threeSAT_iff_exists_is_satisfied (f : ThreeCNF) :
    ThreeSAT f ↔ ∃ a, f.is_satisfied a = true := by
  simp only [ThreeSAT, ThreeCNF.is_satisfied_iff_satisfied]

/-- Every literal variable index is below the formula's declared `numVars`, allowing reductions
    and verifiers to use that value as a bound on the variables in the formula. -/
@[stable_api] def ThreeCNF.Bounded (f : ThreeCNF) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c.literals, l.var < f.numVars

/-- The valid input domain for reductions and verifiers: the subtype proof ensures every literal
    variable index is below the formula's declared `numVars`. -/
@[stable_api] abbrev ValidThreeCNF := {f : ThreeCNF // f.Bounded}

end NPComplete.SAT

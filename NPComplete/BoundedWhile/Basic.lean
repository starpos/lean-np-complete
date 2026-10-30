module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Data.Nat.Basic

/-!
Bounded WHILE provides a total, syntax-directed language for constructions whose runtime and cost
must be proved within Lean. Evaluating each loop bound once at entry keeps iteration finite and its
cost compositional, while an infinite register file lets each construction choose its own layout
without changing the language.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

/-! ## Register file -/

/-- A register file: an infinitely-indexed bank of `Nat` cells.  Unwritten cells
    default to `0` when read (below via `emptyStore`). -/
@[stable_api] def Store : Type := ℕ → ℕ

/-- The all-zero initial store. -/
@[stable_api] def emptyStore : Store := fun _ => 0

/-- Point-update: `writeReg σ r v` yields the store that maps `r` to `v` and every
    other register `r'` to `σ r'`. -/
@[stable_api] def writeReg (σ : Store) (r v : ℕ) : Store :=
  fun r' => if r' = r then v else σ r'

@[stable_api, simp] lemma writeReg_same (σ : Store) (r v : ℕ) : writeReg σ r v r = v := by
  simp [writeReg]

@[stable_api] lemma writeReg_diff (σ : Store) (r v r' : ℕ) (h : r' ≠ r) :
    writeReg σ r v r' = σ r' := by simp [writeReg, h]

/-! ## Expressions: arithmetic and comparison over the register file -/

/-- Arithmetic / comparison expressions over the register file.  `lt` and `eq` return
    `1` (true) or `0` (false), matching the `ifNZ` convention.  `regInd` performs an
    *indirect* register read: the inner `Expr` computes an address, and the outer node
    reads the register at that address. Both computations use the store passed to `eval`. -/
@[stable_api] inductive Expr : Type where
  | const : ℕ → Expr
  | reg : ℕ → Expr
  | regInd : Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  deriving Repr

attribute [stable_api] instReprExpr

/-- Denotational value of an expression against a store. -/
@[stable_api] def Expr.eval : Expr → Store → ℕ
  | .const n, _ => n
  | .reg r, σ => σ r
  | .regInd e, σ => σ (e.eval σ)
  | .add e1 e2, σ => e1.eval σ + e2.eval σ
  | .sub e1 e2, σ => e1.eval σ - e2.eval σ
  | .mul e1 e2, σ => e1.eval σ * e2.eval σ
  | .lt e1 e2, σ => if e1.eval σ < e2.eval σ then 1 else 0
  | .eq e1 e2, σ => if e1.eval σ = e2.eval σ then 1 else 0

/-! The unfolding equations of `Expr.eval` state its meaning, which `brecOn` does not expose. -/

@[stable_api] lemma Expr.eval_const (n : ℕ) (σ : Store) : (Expr.const n).eval σ = n := rfl

@[stable_api] lemma Expr.eval_reg (r : ℕ) (σ : Store) : (Expr.reg r).eval σ = σ r := rfl

@[stable_api] lemma Expr.eval_regInd (e : Expr) (σ : Store) :
    (Expr.regInd e).eval σ = σ (e.eval σ) := rfl

@[stable_api] lemma Expr.eval_add (e₁ e₂ : Expr) (σ : Store) :
    (Expr.add e₁ e₂).eval σ = e₁.eval σ + e₂.eval σ := rfl

@[stable_api] lemma Expr.eval_sub (e₁ e₂ : Expr) (σ : Store) :
    (Expr.sub e₁ e₂).eval σ = e₁.eval σ - e₂.eval σ := rfl

@[stable_api] lemma Expr.eval_mul (e₁ e₂ : Expr) (σ : Store) :
    (Expr.mul e₁ e₂).eval σ = e₁.eval σ * e₂.eval σ := rfl

@[stable_api] lemma Expr.eval_lt (e₁ e₂ : Expr) (σ : Store) :
    (Expr.lt e₁ e₂).eval σ = if e₁.eval σ < e₂.eval σ then 1 else 0 := rfl

@[stable_api] lemma Expr.eval_eq (e₁ e₂ : Expr) (σ : Store) :
    (Expr.eq e₁ e₂).eval σ = if e₁.eval σ = e₂.eval σ then 1 else 0 := rfl

/-- Per-node operation count of an expression.  Each internal node contributes one
    unit; leaves contribute one for the read/const.  `regInd` charges one extra unit
    for the indirection on top of its inner address computation. -/
@[stable_api] def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .reg _ => 1
  | .regInd e => e.cost + 1
  | .add e1 e2 => e1.cost + e2.cost + 1
  | .sub e1 e2 => e1.cost + e2.cost + 1
  | .mul e1 e2 => e1.cost + e2.cost + 1
  | .lt e1 e2 => e1.cost + e2.cost + 1
  | .eq e1 e2 => e1.cost + e2.cost + 1

/-! The unfolding equations of `Expr.cost` state its meaning, which `brecOn` does not expose. -/

@[stable_api] lemma Expr.cost_const (n : ℕ) : (Expr.const n).cost = 1 := rfl

@[stable_api] lemma Expr.cost_reg (r : ℕ) : (Expr.reg r).cost = 1 := rfl

@[stable_api] lemma Expr.cost_regInd (e : Expr) : (Expr.regInd e).cost = e.cost + 1 := rfl

@[stable_api] lemma Expr.cost_add (e₁ e₂ : Expr) :
    (Expr.add e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

@[stable_api] lemma Expr.cost_sub (e₁ e₂ : Expr) :
    (Expr.sub e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

@[stable_api] lemma Expr.cost_mul (e₁ e₂ : Expr) :
    (Expr.mul e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

@[stable_api] lemma Expr.cost_lt (e₁ e₂ : Expr) :
    (Expr.lt e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

@[stable_api] lemma Expr.cost_eq (e₁ e₂ : Expr) :
    (Expr.eq e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

/-! ## Association-list lookup helper

`findVal pairs key` returns the value paired with the first `key`-matching entry,
or `0` if no entry matches. `Program.lookup` uses this finite association-list
lookup with first-match priority and a zero default. -/

/-- Association-list lookup: return the value of the first pair whose key matches,
    defaulting to `0`. -/
@[stable_api] def findVal : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (k, v) :: rest, key => if k = key then v else findVal rest key

@[stable_api, simp] lemma findVal_nil (key : ℕ) : findVal [] key = 0 := rfl

@[stable_api, simp] lemma findVal_cons (k v key : ℕ) (rest : List (ℕ × ℕ)) :
    findVal ((k, v) :: rest) key =
      (if k = key then v else findVal rest key) := rfl

/-! ## Programs: structured commands with bounded iteration -/

/-- A structured command in the bounded-WHILE surface.

  * `forN n body` iterates `body` exactly `n.eval σ` times.
  * `scanList xs r body` iterates `body` once per element `x ∈ xs`, with register
    `r` set to `x` before each iteration.  Models scanning a finite table (a
    `Finset`, `.toList`-ified at the meta level) inside the DSL.
  * `lookup pairs kReg vReg` writes to register `vReg` the value paired with the
    key found at register `kReg` in the association list `pairs` (or `0` if
    absent). Lookup returns the first matching entry.

  Every loop has a fixed bound (an `Expr` for `forN`, the list length for
  `scanList`, the association-list length for `lookup`) so evaluation is
  structurally recursive with no `while`. -/
@[stable_api] inductive Program : Type where
  | skip : Program
  | assign : ℕ → Expr → Program
  | assignInd : Expr → Expr → Program
  | seq : Program → Program → Program
  | ifNZ : Expr → Program → Program → Program
  | forN : Expr → Program → Program
  | scanList : List ℕ → ℕ → Program → Program
  | lookup : List (ℕ × ℕ) → ℕ → ℕ → Program
  deriving Repr

attribute [stable_api] instReprProgram

/-! ## Evaluation

Mutual recursion pairs `Program.eval` with `loopEval`: `Program.eval` handles all eight
constructors; `loopEval body k σ` applies `body` to `σ` exactly `k` times, threading
the store through each iteration. Structural termination comes from `k` in `loopEval`
and from the subterm relation in `Program.eval`. -/

mutual
  /-- Evaluate a program against a store. -/
  @[stable_api] def Program.eval : Program → Store → Store
    | .skip, σ => σ
    | .assign r e, σ => writeReg σ r (e.eval σ)
    | .assignInd eA eV, σ => writeReg σ (eA.eval σ) (eV.eval σ)
    | .seq p1 p2, σ => p2.eval (p1.eval σ)
    | .ifNZ e t f, σ => if e.eval σ ≠ 0 then t.eval σ else f.eval σ
    | .forN n body, σ => loopEval body (n.eval σ) σ
    | .scanList xs r body, σ => scanListEval body xs r σ
    | .lookup pairs kReg vReg, σ => writeReg σ vReg (findVal pairs (σ kReg))

  /-- Iterate `body` on the store `k` times, threading updates. -/
  @[stable_api] def loopEval : Program → ℕ → Store → Store
    | _, 0, σ => σ
    | body, k+1, σ => loopEval body k (Program.eval body σ)

  /-- Iterate `body` once per element of `xs`, threading updates and binding the
      current element to register `r` before each iteration. -/
  @[stable_api] def scanListEval : Program → List ℕ → ℕ → Store → Store
    | _, [], _, σ => σ
    | body, x :: xs, r, σ =>
        scanListEval body xs r (Program.eval body (writeReg σ r x))
end

/-! ## Cost

`Program.cost p σ` is the total operation count of evaluating `p` starting from
store `σ`.  Sequence adds; conditional charges the branch actually taken; loop cost
sums the body cost across iterations at each visited store — closed-form
determinable exactly because the loop bound is known at entry. -/

mutual
  /-- Total operation count of evaluating a program from a store. -/
  @[stable_api] def Program.cost : Program → Store → ℕ
    | .skip, _ => 1
    | .assign _ e, _ => e.cost + 1
    | .assignInd eA eV, _ => eA.cost + eV.cost + 1
    | .seq p1 p2, σ => p1.cost σ + p2.cost (p1.eval σ)
    | .ifNZ e t f, σ => e.cost + 1 + (if e.eval σ ≠ 0 then t.cost σ else f.cost σ)
    | .forN n body, σ => n.cost + 1 + loopCost body (n.eval σ) σ
    | .scanList xs r body, σ => 1 + scanListCost body xs r σ
    | .lookup pairs _ _, _ => pairs.length + 1

  /-- Sum of `body.cost` across `k` iterations, threading the store. -/
  @[stable_api] def loopCost : Program → ℕ → Store → ℕ
    | _, 0, _ => 0
    | body, k+1, σ => Program.cost body σ + loopCost body k (Program.eval body σ)

  /-- Sum of `body.cost` across a `scanList` traversal, threading the register-bound
      store through each iteration.  Each iteration charges `body.cost` at the
      store that already reflects the write to register `r`. -/
  @[stable_api] def scanListCost : Program → List ℕ → ℕ → Store → ℕ
    | _, [], _, _ => 0
    | body, x :: xs, r, σ =>
        Program.cost body (writeReg σ r x)
          + scanListCost body xs r (Program.eval body (writeReg σ r x))
end

/-! ## Compositional lemmas -/

@[stable_api, simp] lemma eval_skip (σ : Store) : Program.skip.eval σ = σ := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_assign (r : ℕ) (e : Expr) (σ : Store) :
    (Program.assign r e).eval σ = writeReg σ r (e.eval σ) := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_assignInd (eA eV : Expr) (σ : Store) :
    (Program.assignInd eA eV).eval σ = writeReg σ (eA.eval σ) (eV.eval σ) := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_seq (p1 p2 : Program) (σ : Store) :
    (Program.seq p1 p2).eval σ = p2.eval (p1.eval σ) := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_ifNZ (e : Expr) (t f : Program) (σ : Store) :
    (Program.ifNZ e t f).eval σ =
      (if e.eval σ ≠ 0 then t.eval σ else f.eval σ) := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_forN (n : Expr) (body : Program) (σ : Store) :
    (Program.forN n body).eval σ = loopEval body (n.eval σ) σ := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_scanList (xs : List ℕ) (r : ℕ) (body : Program) (σ : Store) :
    (Program.scanList xs r body).eval σ = scanListEval body xs r σ := by
  simp [Program.eval]

@[stable_api, simp] lemma eval_lookup (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ) (σ : Store) :
    (Program.lookup pairs kReg vReg).eval σ =
      writeReg σ vReg (findVal pairs (σ kReg)) := by
  simp [Program.eval]

@[stable_api, simp] lemma loopEval_zero (body : Program) (σ : Store) :
    loopEval body 0 σ = σ := by
  simp [loopEval]

@[stable_api, simp] lemma loopEval_succ (body : Program) (k : ℕ) (σ : Store) :
    loopEval body (k + 1) σ = loopEval body k (body.eval σ) := by
  simp [loopEval]

/-- The snoc form aligns runtime iteration with syntax trees that append their final
    command, so their evaluations can be compared without reversing either recursion. -/
@[stable_api] lemma loopEval_succ_snoc (body : Program) (k : ℕ) (σ : Store) :
    loopEval body (k + 1) σ = body.eval (loopEval body k σ) := by
  induction k generalizing σ with
  | zero => simp
  | succ n ih => rw [loopEval_succ, ih, loopEval_succ]

@[stable_api] lemma loopEval_one (body : Program) (σ : Store) :
    loopEval body 1 σ = body.eval σ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, loopEval_succ, loopEval_zero]

@[stable_api] lemma loopEval_add (body : Program) (a b : ℕ) (σ : Store) :
    loopEval body (a + b) σ = loopEval body b (loopEval body a σ) := by
  induction a generalizing σ with
  | zero => simp
  | succ a ih =>
    have e1 : a + 1 + b = (a + b) + 1 := by omega
    rw [e1, loopEval_succ, ih, loopEval_succ]

@[stable_api, simp] lemma scanListEval_nil (body : Program) (r : ℕ) (σ : Store) :
    scanListEval body [] r σ = σ := by simp [scanListEval]

@[stable_api, simp] lemma scanListEval_cons (body : Program) (x : ℕ) (xs : List ℕ)
    (r : ℕ) (σ : Store) :
    scanListEval body (x :: xs) r σ =
      scanListEval body xs r (body.eval (writeReg σ r x)) := by
  simp [scanListEval]

@[stable_api, simp] lemma cost_skip (σ : Store) : Program.skip.cost σ = 1 := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_assign (r : ℕ) (e : Expr) (σ : Store) :
    (Program.assign r e).cost σ = e.cost + 1 := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_assignInd (eA eV : Expr) (σ : Store) :
    (Program.assignInd eA eV).cost σ = eA.cost + eV.cost + 1 := by
  simp [Program.cost]

/-- **Sequencing distributes cost.**  The total cost of `p1 ; p2` at `σ` is the cost
    of `p1` at `σ` plus the cost of `p2` at the store after `p1`. -/
@[stable_api, simp] lemma cost_seq (p1 p2 : Program) (σ : Store) :
    (Program.seq p1 p2).cost σ = p1.cost σ + p2.cost (p1.eval σ) := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_ifNZ (e : Expr) (t f : Program) (σ : Store) :
    (Program.ifNZ e t f).cost σ =
      e.cost + 1 + (if e.eval σ ≠ 0 then t.cost σ else f.cost σ) := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_forN (n : Expr) (body : Program) (σ : Store) :
    (Program.forN n body).cost σ = n.cost + 1 + loopCost body (n.eval σ) σ := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_scanList (xs : List ℕ) (r : ℕ) (body : Program) (σ : Store) :
    (Program.scanList xs r body).cost σ = 1 + scanListCost body xs r σ := by
  simp [Program.cost]

@[stable_api, simp] lemma cost_lookup (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ) (σ : Store) :
    (Program.lookup pairs kReg vReg).cost σ = pairs.length + 1 := by
  simp [Program.cost]

@[stable_api, simp] lemma loopCost_zero (body : Program) (σ : Store) :
    loopCost body 0 σ = 0 := by simp [loopCost]

@[stable_api, simp] lemma loopCost_succ (body : Program) (k : ℕ) (σ : Store) :
    loopCost body (k + 1) σ = body.cost σ + loopCost body k (body.eval σ) := by
  simp [loopCost]

@[stable_api, simp] lemma scanListCost_nil (body : Program) (r : ℕ) (σ : Store) :
    scanListCost body [] r σ = 0 := by simp [scanListCost]

@[stable_api, simp] lemma scanListCost_cons (body : Program) (x : ℕ) (xs : List ℕ)
    (r : ℕ) (σ : Store) :
    scanListCost body (x :: xs) r σ =
      body.cost (writeReg σ r x)
        + scanListCost body xs r (body.eval (writeReg σ r x)) := by
  simp [scanListCost]

/-! ## Loop cost bound: `n` iterations charge at most `n × max_body_cost`

A structural bound on loop cost that is *not* tight — it does not attempt to track
the per-iteration cost variation — but is enough to conclude polynomial cost from a
polynomial per-iteration cost.  Concretely: if some `B` bounds `body.cost` at every
visited store, then `loopCost body k σ ≤ k * B`. -/

/-- If `body.cost` is uniformly bounded by `B` across the stores visited during a
    `loopEval body k σ`, then the total `loopCost body k σ` is at most `k * B`.
    The unconditional premise avoids requiring callers to describe which stores
    the loop visits. -/
@[stable_api] lemma loopCost_le_of_body_le
    (body : Program) (B : ℕ) (hbody : ∀ σ, body.cost σ ≤ B) :
    ∀ k σ, loopCost body k σ ≤ k * B := by
  intro k
  induction k with
  | zero => intro σ; simp
  | succ k ih =>
      intro σ
      simp only [loopCost_succ]
      have h1 := hbody σ
      have h2 := ih (body.eval σ)
      have h3 : (k + 1) * B = B + k * B := by rw [Nat.succ_mul]; omega
      omega

/-- Invariant-conditional analogue of `loopCost_le_of_body_le`: a uniform
    `∀ σ` body bound is unavailable when the body contains nested scans whose
    iteration counts are register values, but those registers are preserved
    by the body on the stores the loop actually visits.  If `P` is preserved
    by the body and bounds the body cost, the loop cost is `k * B` from any
    `P`-store. -/
@[stable_api] lemma loopCost_le_of_body_le_inv
    (body : Program) (P : Store → Prop) (B : ℕ)
    (hpres : ∀ σ, P σ → P (body.eval σ))
    (hbody : ∀ σ, P σ → body.cost σ ≤ B) :
    ∀ k σ, P σ → loopCost body k σ ≤ k * B := by
  intro k
  induction k with
  | zero => intro σ _; simp
  | succ k ih =>
      intro σ hP
      simp only [loopCost_succ]
      have h1 := hbody σ hP
      have h2 := ih (body.eval σ) (hpres σ hP)
      have h3 : (k + 1) * B = B + k * B := by rw [Nat.succ_mul]; omega
      omega

/-- Uniform-bound analogue of `loopCost_le_of_body_le` for `scanList`: if some `B`
    bounds `body.cost` at every store, then `scanListCost body xs r σ ≤ xs.length * B`.
    The bound depends only on the list length, decoupling the scan cost from the
    element values written to register `r`. -/
@[stable_api] lemma scanListCost_le_of_body_le
    (body : Program) (B : ℕ) (hbody : ∀ σ, body.cost σ ≤ B) :
    ∀ xs r σ, scanListCost body xs r σ ≤ xs.length * B := by
  intro xs
  induction xs with
  | nil => intro r σ; simp
  | cons x tail ih =>
      intro r σ
      simp only [scanListCost_cons, List.length_cons]
      have h1 := hbody (writeReg σ r x)
      have h2 := ih r (body.eval (writeReg σ r x))
      have h3 : (tail.length + 1) * B = B + tail.length * B := by
        rw [Nat.succ_mul]; omega
      omega

/-- Invariant-conditional analogue of `scanListCost_le_of_body_le`: companion
    of `loopCost_le_of_body_le_inv` for `scanList`, threading the per-iteration
    `writeReg σ r x` element binding through the invariant. -/
@[stable_api] lemma scanListCost_le_of_body_le_inv
    (body : Program) (r : ℕ) (P : Store → Prop) (B : ℕ)
    (hpres : ∀ σ x, P σ → P (body.eval (writeReg σ r x)))
    (hbody : ∀ σ x, P σ → body.cost (writeReg σ r x) ≤ B) :
    ∀ xs σ, P σ → scanListCost body xs r σ ≤ xs.length * B := by
  intro xs
  induction xs with
  | nil => intro σ _; simp
  | cons x tail ih =>
      intro σ hP
      simp only [scanListCost_cons, List.length_cons]
      have h1 := hbody σ x hP
      have h2 := ih (body.eval (writeReg σ r x)) (hpres σ x hP)
      have h3 : (tail.length + 1) * B = B + tail.length * B := by
        rw [Nat.succ_mul]; omega
      omega

/-- Chained bound: cost of `Program.scanList xs r body` at `σ` in terms of a length
    bound `L ≥ xs.length` and a body-cost bound `B`. Instantiating `L` with any
    upper bound on the encoded list length yields a cost bound in terms of that input size. -/
@[stable_api] lemma cost_scanList_le_of_bounds
    (body : Program) (xs : List ℕ) (r : ℕ) (σ : Store)
    (B L : ℕ) (hbody : ∀ σ, body.cost σ ≤ B) (hlen : xs.length ≤ L) :
    (Program.scanList xs r body).cost σ ≤ 1 + L * B := by
  have hscan : scanListCost body xs r σ ≤ xs.length * B :=
    scanListCost_le_of_body_le body B hbody xs r σ
  have hmul : xs.length * B ≤ L * B := Nat.mul_le_mul_right B hlen
  simp only [cost_scanList]
  omega

/-- Chained bound: cost of `Program.forN n body` at `σ` in terms of an iteration
    bound `L ≥ n.eval σ` and a body-cost bound `B`.  Companion of
    `cost_scanList_le_of_bounds`. -/
@[stable_api] lemma cost_forN_le_of_bounds
    (n : Expr) (body : Program) (σ : Store)
    (B L : ℕ) (hbody : ∀ σ, body.cost σ ≤ B) (hn : n.eval σ ≤ L) :
    (Program.forN n body).cost σ ≤ n.cost + 1 + L * B := by
  have hloop : loopCost body (n.eval σ) σ ≤ (n.eval σ) * B :=
    loopCost_le_of_body_le body B hbody (n.eval σ) σ
  have hmul : (n.eval σ) * B ≤ L * B := Nat.mul_le_mul_right B hn
  simp only [cost_forN]
  omega

/-- Invariant-conditional analogue of `cost_forN_le_of_bounds`: the body cost
    may depend on a preserved store invariant rather than a uniform `∀ σ` bound. -/
@[stable_api] lemma cost_forN_le_of_inv
    (n : Expr) (body : Program) (σ : Store) (P : Store → Prop)
    (B L : ℕ) (hP : P σ)
    (hpres : ∀ τ, P τ → P (body.eval τ))
    (hbody : ∀ τ, P τ → body.cost τ ≤ B) (hn : n.eval σ ≤ L) :
    (Program.forN n body).cost σ ≤ n.cost + 1 + L * B := by
  have hloop := loopCost_le_of_body_le_inv body P B hpres hbody (n.eval σ) σ hP
  have hmul : n.eval σ * B ≤ L * B := Nat.mul_le_mul_right B hn
  simp only [cost_forN]
  omega

/-- Constant-cost bound for a single `Program.lookup pairs kReg vReg`: pairs.length + 1
    at every store.  A cost-bound wrapper analogous to `cost_scanList_le_of_bounds`. -/
@[stable_api] lemma cost_lookup_le_of_len
    (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ) (σ : Store)
    (L : ℕ) (hlen : pairs.length ≤ L) :
    (Program.lookup pairs kReg vReg).cost σ ≤ L + 1 := by
  simp only [cost_lookup]; omega

end NPComplete.BoundedWhile

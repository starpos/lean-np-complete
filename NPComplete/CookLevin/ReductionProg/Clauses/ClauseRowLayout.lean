module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseEmitProg

/-!
The five family writers run in sequence, so row offsets in concatenated clause
lists must match the pointer advances of each writer. The row-width lemmas show
that appending lists preserves earlier offsets and shifts later rows by the first
list's total width.

Dense-layout state, head, and cell numbers are mixed-radix expressions. This
module defines those expressions and proves evaluation and congruence lemmas,
which callers use to discharge value and frame obligations.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT

lemma rowTableWidth_zero (f : ℕ → ℕ) : rowTableWidth f 0 = 0 := rfl

lemma getD_append_shift (cs ds : List Clause) (j : ℕ) :
    (cs ++ ds).getD (cs.length + j) default = ds.getD j default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-! ## Variable numbers as expressions

The dense layout was chosen so that a variable's number is a mixed-radix
combination of its indices — sums and products only.  That is exactly the
fragment the expression language provides, so the producer computes variable
numbers directly, with no division and no table of precomputed numbers. -/

open NPComplete.BoundedWhile (Expr Store)

def denseBlockE (nE WE mE : Expr) : Expr := .add (.add nE WE) (.mul WE mE)

def denseStateE (nE WE mE tE qE : Expr) : Expr :=
  .add (.mul tE (denseBlockE nE WE mE)) qE

def denseHeadE (nE WE mE tE pE : Expr) : Expr :=
  .add (.add (.mul tE (denseBlockE nE WE mE)) nE) pE

def denseCellE (nE WE mE tE pE aE : Expr) : Expr :=
  .add (.add (.add (.mul tE (denseBlockE nE WE mE)) nE) WE) (.add (.mul pE mE) aE)

lemma denseBlockE_eval (nE WE mE : Expr) (σ : Store) :
    (denseBlockE nE WE mE).eval σ = denseBlock (nE.eval σ) (WE.eval σ) (mE.eval σ) := by
  simp [denseBlockE, denseBlock, Expr.eval]

lemma denseStateE_eval (nE WE mE tE qE : Expr) (σ : Store) :
    (denseStateE nE WE mE tE qE).eval σ
      = (denseLayout (nE.eval σ) (WE.eval σ) (mE.eval σ)).state (tE.eval σ) (qE.eval σ) := by
  simp [denseStateE, denseLayout, Expr.eval, denseBlockE_eval]

lemma denseHeadE_eval (nE WE mE tE pE : Expr) (σ : Store) :
    (denseHeadE nE WE mE tE pE).eval σ
      = (denseLayout (nE.eval σ) (WE.eval σ) (mE.eval σ)).head (tE.eval σ) (pE.eval σ) := by
  simp [denseHeadE, denseLayout, Expr.eval, denseBlockE_eval]

lemma denseCellE_eval (nE WE mE tE pE aE : Expr) (σ : Store) :
    (denseCellE nE WE mE tE pE aE).eval σ
      = (denseLayout (nE.eval σ) (WE.eval σ) (mE.eval σ)).cell
          (tE.eval σ) (pE.eval σ) (aE.eval σ) := by
  simp [denseCellE, denseLayout, Expr.eval, denseBlockE_eval]

/-! ## Congruence of dense-layout expressions

A family's variable expression is a `dense*E` applied to counters and sizes.
Frame and value obligations then reduce to the same facts about those
arguments, so they are discharged here rather than restated at each family. -/

lemma expr_add_one_eval_congr (e : Expr) (σ σ' : Store)
    (h : e.eval σ' = e.eval σ) :
    (Expr.add e (.const 1)).eval σ' = (Expr.add e (.const 1)).eval σ := by
  simp [Expr.eval, h]

lemma expr_add_one_eval (e : Expr) (σ : Store) (v : ℕ) (hv : e.eval σ = v) :
    (Expr.add e (.const 1)).eval σ = v + 1 := by
  simp [Expr.eval, hv]

lemma expr_add_one_add_eval_congr (eBase eJ : Expr) (σ σ' : Store)
    (hB : eBase.eval σ' = eBase.eval σ) (hJ : eJ.eval σ' = eJ.eval σ) :
    (Expr.add (Expr.add eBase (.const 1)) eJ).eval σ'
      = (Expr.add (Expr.add eBase (.const 1)) eJ).eval σ := by
  simp [Expr.eval, hB, hJ]

lemma expr_add_one_add_eval (eBase eJ : Expr) (σ : Store) (b j : ℕ)
    (hb : eBase.eval σ = b) (hj : eJ.eval σ = j) :
    (Expr.add (Expr.add eBase (.const 1)) eJ).eval σ = b + 1 + j := by
  simp [Expr.eval, hb, hj]

lemma denseStateE_eval_congr (nE WE mE tE qE : Expr) (σ σ' : Store)
    (hn : nE.eval σ' = nE.eval σ) (hW : WE.eval σ' = WE.eval σ)
    (hm : mE.eval σ' = mE.eval σ) (ht : tE.eval σ' = tE.eval σ)
    (hq : qE.eval σ' = qE.eval σ) :
    (denseStateE nE WE mE tE qE).eval σ' = (denseStateE nE WE mE tE qE).eval σ := by
  rw [denseStateE_eval, denseStateE_eval, hn, hW, hm, ht, hq]

lemma denseHeadE_eval_congr (nE WE mE tE pE : Expr) (σ σ' : Store)
    (hn : nE.eval σ' = nE.eval σ) (hW : WE.eval σ' = WE.eval σ)
    (hm : mE.eval σ' = mE.eval σ) (ht : tE.eval σ' = tE.eval σ)
    (hp : pE.eval σ' = pE.eval σ) :
    (denseHeadE nE WE mE tE pE).eval σ' = (denseHeadE nE WE mE tE pE).eval σ := by
  rw [denseHeadE_eval, denseHeadE_eval, hn, hW, hm, ht, hp]

lemma denseCellE_eval_congr (nE WE mE tE pE aE : Expr) (σ σ' : Store)
    (hn : nE.eval σ' = nE.eval σ) (hW : WE.eval σ' = WE.eval σ)
    (hm : mE.eval σ' = mE.eval σ) (ht : tE.eval σ' = tE.eval σ)
    (hp : pE.eval σ' = pE.eval σ) (ha : aE.eval σ' = aE.eval σ) :
    (denseCellE nE WE mE tE pE aE).eval σ' = (denseCellE nE WE mE tE pE aE).eval σ := by
  rw [denseCellE_eval, denseCellE_eval, hn, hW, hm, ht, hp, ha]

lemma denseStateE_eval_eq (nE WE mE tE qE : Expr) (σ : Store) (n W m t q : ℕ)
    (hn : nE.eval σ = n) (hW : WE.eval σ = W) (hm : mE.eval σ = m)
    (ht : tE.eval σ = t) (hq : qE.eval σ = q) :
    (denseStateE nE WE mE tE qE).eval σ = (denseLayout n W m).state t q := by
  rw [denseStateE_eval, hn, hW, hm, ht, hq]

lemma denseHeadE_eval_eq (nE WE mE tE pE : Expr) (σ : Store) (n W m t p : ℕ)
    (hn : nE.eval σ = n) (hW : WE.eval σ = W) (hm : mE.eval σ = m)
    (ht : tE.eval σ = t) (hp : pE.eval σ = p) :
    (denseHeadE nE WE mE tE pE).eval σ = (denseLayout n W m).head t p := by
  rw [denseHeadE_eval, hn, hW, hm, ht, hp]

lemma denseCellE_eval_eq (nE WE mE tE pE aE : Expr) (σ : Store) (n W m t p a : ℕ)
    (hn : nE.eval σ = n) (hW : WE.eval σ = W) (hm : mE.eval σ = m)
    (ht : tE.eval σ = t) (hp : pE.eval σ = p) (ha : aE.eval σ = a) :
    (denseCellE nE WE mE tE pE aE).eval σ = (denseLayout n W m).cell t p a := by
  rw [denseCellE_eval, hn, hW, hm, ht, hp, ha]

end NPComplete.CookLevin

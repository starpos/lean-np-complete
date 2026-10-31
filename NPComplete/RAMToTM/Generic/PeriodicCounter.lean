module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.BoundedWhile.Frame

/-! Periodic counters support flattening structured traversals without division at runtime. -/

@[expose] public section

namespace NPComplete.RAMToTM
open NPComplete.BoundedWhile

@[construction_api] def periodicCounterProg (d cr pr : ℕ) : Program :=
  (Program.assign cr (.add (.reg cr) (.eq (.reg pr) (.const (d - 1))))).seq
    (.assign pr (.mul (.add (.reg pr) (.const 1))
      (.sub (.const 1) (.eq (.reg pr) (.const (d - 1))))))

@[construction_api] lemma periodicCounterProg_correct {d cr pr : ℕ} {σ : Store}
    (hne : cr ≠ pr) (hp : σ pr < d) :
    let τ := (periodicCounterProg d cr pr).eval σ
    τ cr = σ cr + (if σ pr = d - 1 then 1 else 0) ∧
    τ pr = (if σ pr = d - 1 then 0 else σ pr + 1) ∧
    d * τ cr + τ pr = d * σ cr + σ pr + 1 ∧ τ pr < d := by
  have hd : d - 1 + 1 = d := by omega
  simp only [periodicCounterProg, eval_seq, eval_assign, Expr.eval, writeReg]
  simp only [hne, Ne.symm hne, ↓reduceIte]
  by_cases h : σ pr = d - 1
  · simp only [h, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.add_zero, true_and,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc, hd]
    omega
  · have hlt : σ pr + 1 < d := by omega
    simp only [h, ↓reduceIte, Nat.reduceSub, Nat.mul_one, Nat.add_zero, true_and,
      Nat.add_assoc, hlt]

@[construction_api] lemma periodicCounterProg_bounded {d cr pr B : ℕ} {σ : Store}
    (hne : cr ≠ pr) (hp : σ pr < d) (hcr : cr ≤ B) (hpr : pr ≤ B) (hd : d ≤ B)
    (hc : σ cr + 1 ≤ B) : ProgramBoundedIn B σ (periodicCounterProg d cr pr) := by
  simp only [periodicCounterProg, programBoundedIn_seq_iff, programBoundedIn_assign_iff,
    ExprBoundedIn, Expr.eval, eval_assign, writeReg, Ne.symm hne, ↓reduceIte]
  by_cases h : σ pr = d - 1 <;> simp only [h, ↓reduceIte, Nat.reduceSub,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega

@[construction_api] lemma periodicCounterProg_avoids (d cr pr : ℕ) :
    (periodicCounterProg d cr pr).Avoids (fun r => r ≠ cr ∧ r ≠ pr) := by
  simp only [periodicCounterProg, Program.avoids_seq, Program.avoids_assign, not_and, not_not,
    implies_true, and_true]
  intro h; exact (h rfl).elim

@[construction_api] lemma periodicCounterProg_scanFree (d cr pr : ℕ) :
    ScanFree (periodicCounterProg d cr pr) := by
  simp only [periodicCounterProg, ScanFree, and_self]

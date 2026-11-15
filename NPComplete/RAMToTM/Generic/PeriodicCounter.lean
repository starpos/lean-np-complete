module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.BoundedWhile.Frame
public import NPComplete.BoundedWhile.RegLayout

/-! Periodic counters support flattening structured traversals without division at runtime. -/

@[expose] public section

namespace NPComplete.RAMToTM
open NPComplete.BoundedWhile

@[construction_api, stage_raw_ctor] def periodicCounterProg (d cr pr : ℕ) : Program :=
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

/-! ### Layout wrapper

`periodicCounterProgL` is the layout-role version of `periodicCounterProg`: the counter and period
position registers are roles of a layout, the period `d` stays data.  The lemmas restate the
contract of the raw constructor in those roles. -/

/-- The layout-role version of `periodicCounterProg`: `cr` and `pr` are roles of `R`. -/
@[construction_api, stage_boundary] def periodicCounterProgL {Role : Type} (R : RegLayout Role)
    (d : ℕ) (cr pr : Role) : Program :=
  periodicCounterProg d (R.reg cr) (R.reg pr)

variable {Role : Type} {R : RegLayout Role}

@[construction_api, stage_contract] lemma periodicCounterProgL_correct {d : ℕ} {cr pr : Role}
    {σ : Store} (hne : cr ≠ pr) (hp : σ (R.reg pr) < d) :
    let τ := (periodicCounterProgL R d cr pr).eval σ
    τ (R.reg cr) = σ (R.reg cr) + (if σ (R.reg pr) = d - 1 then 1 else 0) ∧
    τ (R.reg pr) = (if σ (R.reg pr) = d - 1 then 0 else σ (R.reg pr) + 1) ∧
    d * τ (R.reg cr) + τ (R.reg pr) = d * σ (R.reg cr) + σ (R.reg pr) + 1 ∧
    τ (R.reg pr) < d :=
  periodicCounterProg_correct (R.reg_ne hne) hp

@[construction_api, stage_contract] lemma periodicCounterProgL_bounded {d : ℕ} {cr pr : Role}
    {B : ℕ} {σ : Store} (hne : cr ≠ pr) (hp : σ (R.reg pr) < d) (hcr : R.reg cr ≤ B)
    (hpr : R.reg pr ≤ B) (hd : d ≤ B) (hc : σ (R.reg cr) + 1 ≤ B) :
    ProgramBoundedIn B σ (periodicCounterProgL R d cr pr) :=
  periodicCounterProg_bounded (R.reg_ne hne) hp hcr hpr hd hc

@[construction_api, stage_contract] lemma periodicCounterProgL_avoids (d : ℕ) (cr pr : Role) :
    (periodicCounterProgL R d cr pr).Avoids (fun r => r ≠ R.reg cr ∧ r ≠ R.reg pr) :=
  periodicCounterProg_avoids d (R.reg cr) (R.reg pr)

@[construction_api, stage_contract] lemma periodicCounterProgL_scanFree (d : ℕ) (cr pr : Role) :
    ScanFree (periodicCounterProgL R d cr pr) :=
  periodicCounterProg_scanFree d (R.reg cr) (R.reg pr)

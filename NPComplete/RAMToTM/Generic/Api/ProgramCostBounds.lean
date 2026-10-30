module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.BoundedWhile.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Structural cost and value bounds for bounded RAM programs

These contracts depend only on the bounded-while language and its operand bounds, allowing distinct
reduction pipelines to reuse them without specializing the results to a particular problem.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

/-- A structural operation-count envelope.  For a fixed AST this is a polynomial in `L`: every
    `forN` or `scanList` contributes one multiplication by the common loop ceiling. -/
def CostEnvelope : Program → ℕ → ℕ
  | .skip, _ => 1
  | .assign _ e, _ => e.cost + 1
  | .assignInd e₁ e₂, _ => e₁.cost + e₂.cost + 1
  | .seq p q, L => CostEnvelope p L + CostEnvelope q L
  | .ifNZ e p q, L => e.cost + 1 + CostEnvelope p L + CostEnvelope q L
  | .forN e body, L => e.cost + 1 + L * CostEnvelope body L
  | .scanList _xs _ body, L => 1 + L * CostEnvelope body L
  | .lookup xs _ _, _ => xs.length + 1

/-- The loop-bound part of the cost contract.  The `forN` clause quantifies exactly over the
    executed prefix stores, which is what `loopCost` needs; no address or value-range assertion is
    hidden in this predicate. -/
def LoopBounded : Program → ℕ → Store → Prop
  | .skip, _, _ | .assign _ _, _, _ | .assignInd _ _, _, _ | .lookup _ _ _, _, _ => True
  | .seq p q, L, σ => LoopBounded p L σ ∧ LoopBounded q L (p.eval σ)
  | .ifNZ _ p q, L, σ => LoopBounded p L σ ∧ LoopBounded q L σ
  | .forN e body, L, σ =>
      e.eval σ ≤ L ∧ ∀ k, k < e.eval σ → LoopBounded body L (loopEval body k σ)
  | .scanList xs _ body, L, _ =>
      xs.length ≤ L ∧ ∀ τ, body.cost τ ≤ CostEnvelope body L

lemma g6_loopCost_le (body : Program) (B k : ℕ) (σ : Store)
    (hbody : ∀ i, i < k → body.cost (loopEval body i σ) ≤ B) :
    loopCost body k σ ≤ k * B := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    rw [loopCost_succ]
    have h0 : body.cost σ ≤ B := by simpa using hbody 0 (by omega)
    have htail : ∀ i, i < k → body.cost (loopEval body i (body.eval σ)) ≤ B := by
      intro i hi
      simpa [loopEval_succ] using hbody (i + 1) (by omega)
    have hi := ih (body.eval σ) htail
    rw [Nat.succ_mul]
    omega

lemma g6_cost_le_envelope : ∀ (p : Program) (L : ℕ) (σ : Store),
    LoopBounded p L σ → p.cost σ ≤ CostEnvelope p L := by
  intro p
  induction p with
  | skip => simp [CostEnvelope]
  | assign r e => simp [CostEnvelope]
  | assignInd e₁ e₂ => simp [CostEnvelope]
  | seq p q ihp ihq =>
    intro L σ h
    rw [cost_seq]
    have hp := ihp L σ h.1
    have hq := ihq L (p.eval σ) h.2
    simp only [CostEnvelope]
    omega
  | ifNZ e p q ihp ihq =>
    intro L σ h
    rw [cost_ifNZ]
    simp only [CostEnvelope]
    split <;> rename_i hb
    · have hp := ihp L σ h.1
      omega
    · have hq := ihq L σ h.2
      omega
  | forN e body ih =>
    intro L σ h
    rw [cost_forN]
    simp only [CostEnvelope]
    have hbody : ∀ i, i < e.eval σ → body.cost (loopEval body i σ) ≤
        CostEnvelope body L := by
      intro i hi
      exact ih L (loopEval body i σ) (h.2 i (by omega))
    have hloop := g6_loopCost_le body (CostEnvelope body L) (e.eval σ) σ hbody
    have hmul := Nat.mul_le_mul_right (CostEnvelope body L) h.1
    omega
  | scanList xs r body ih =>
    intro L σ h
    rw [cost_scanList]
    simp only [CostEnvelope]
    have hscan := scanListCost_le_of_body_le body (CostEnvelope body L)
      (fun τ => h.2 τ) xs r σ
    have hmul := Nat.mul_le_mul_right (CostEnvelope body L) h.1
    omega
  | lookup xs k v => simp [CostEnvelope]

lemma CostEnvelope_mono (p : Program) {L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    CostEnvelope p L₁ ≤ CostEnvelope p L₂ := by
  induction p with
  | skip | assign | assignInd | lookup => simp [CostEnvelope]
  | seq p q ihp ihq =>
    simp only [CostEnvelope]
    exact Nat.add_le_add ihp ihq
  | ifNZ e p q ihp ihq =>
    simp only [CostEnvelope]
    omega
  | forN e body ih =>
    simp only [CostEnvelope]
    have hb := ih
    exact Nat.add_le_add_left (Nat.mul_le_mul hL hb) _
  | scanList xs r body ih =>
    simp only [CostEnvelope]
    exact Nat.add_le_add_left (Nat.mul_le_mul hL ih) _

def StoreBounded (B : ℕ) (σ : Store) : Prop := ∀ i, σ i ≤ B

/-- A structural guard for the part of the DSL covered by `ProgramBoundedIn`. -/
def NoCompileTimeTables : Program → Prop
  | .skip | .assign _ _ | .assignInd _ _ => True
  | .lookup _ _ _ | .scanList _ _ _ => False
  | .seq p q => NoCompileTimeTables p ∧ NoCompileTimeTables q
  | .ifNZ _ p q => NoCompileTimeTables p ∧ NoCompileTimeTables q
  | .forN _ body => NoCompileTimeTables body

lemma g6_loopEval_store_bounded (body : Program) (B k : ℕ) (σ : Store)
    (hstep : ∀ τ, StoreBounded B τ → ProgramBoundedIn B τ body →
      StoreBounded B (body.eval τ))
    (hσ : StoreBounded B σ)
    (hp : ∀ m' < k, ProgramBoundedIn B (loopEval body m' σ) body) :
    StoreBounded B (loopEval body k σ) := by
  induction k generalizing σ with
  | zero => simpa [StoreBounded] using hσ
  | succ k ih =>
      have hp0 : ProgramBoundedIn B σ body := by simpa [loopEval] using hp 0 (by omega)
      have hnext := hstep σ hσ hp0
      rw [loopEval_succ]
      apply ih (body.eval σ) hnext
      intro m hm
      simpa [loopEval_succ] using hp (m + 1) (by omega)

lemma g6_program_eval_store_bounded : ∀ (p : Program) (B : ℕ) (_ : 1 ≤ B)
    (σ : Store), StoreBounded B σ → ProgramBoundedIn B σ p →
      NoCompileTimeTables p → StoreBounded B (p.eval σ) := by
  intro p
  induction p with
  | skip => intro B _ σ hσ _ _; simpa [StoreBounded] using hσ
  | assign r e =>
      intro B hB1 σ hσ hp _ i
      obtain ⟨hr, he⟩ := hp
      by_cases hi : i = r
      · subst i
        simp [writeReg_same]
        exact expr_eval_le_of_bounded_in hσ hB1 e he
      · rw [show (Program.assign r e).eval σ i = σ i by simp [writeReg, hi]]
        exact hσ i
  | assignInd eA eV =>
      intro B hB1 σ hσ hp _ i
      obtain ⟨heA, heV, haddr⟩ := hp
      by_cases hi : i = eA.eval σ
      · subst i
        simp [writeReg_same]
        exact expr_eval_le_of_bounded_in hσ hB1 eV heV
      · rw [show (Program.assignInd eA eV).eval σ i = σ i by simp [writeReg, hi]]
        exact hσ i
  | seq p q ihp ihq =>
      intro B hB1 σ hσ hp hnt
      simpa only [eval_seq] using
        ihq B hB1 (p.eval σ) (ihp B hB1 σ hσ hp.1 hnt.1) hp.2 hnt.2
  | ifNZ e p q ihp ihq =>
      intro B hB1 σ hσ hp hnt
      simp only [Program.eval]
      split
      · exact ihp B hB1 σ hσ hp.2.1 hnt.1
      · exact ihq B hB1 σ hσ hp.2.2 hnt.2
  | forN e body ih =>
      intro B hB1 σ hσ hp hnt
      obtain ⟨he, hbody⟩ := hp
      have hloop : StoreBounded B (loopEval body (e.eval σ) σ) :=
        g6_loopEval_store_bounded body B (e.eval σ) σ
          (fun τ hτ hpτ => ih B hB1 τ hτ hpτ hnt) hσ hbody
      simpa only [Program.eval] using hloop
  | scanList xs r body ih => intro B _ σ hσ hp hnt; exact False.elim hnt
  | lookup pairs k v => intro B _ σ hσ hp hnt; exact False.elim hnt

/-- `ProgramBoundedIn` supplies the executed-prefix obligations for the cost contract.  The
    store-bound hypothesis is necessary because `ExprBoundedIn` permits register reads. -/
lemma programBoundedIn_to_g6_loopBounded : ∀ (p : Program) (B L : ℕ) (_ : 1 ≤ B)
    (σ : Store), StoreBounded B σ → ProgramBoundedIn B σ p →
      NoCompileTimeTables p → B ≤ L → LoopBounded p L σ := by
  intro p
  induction p with
  | skip => simp [LoopBounded]
  | assign => simp [LoopBounded]
  | assignInd => simp [LoopBounded]
  | seq p q ihp ihq =>
      intro B L hB1 σ hσ hp hnt hBL
      exact ⟨ihp B L hB1 σ hσ hp.1 hnt.1 hBL,
        ihq B L hB1 (p.eval σ)
          (g6_program_eval_store_bounded p B hB1 σ hσ hp.1 hnt.1)
          hp.2 hnt.2 hBL⟩
  | ifNZ e p q ihp ihq =>
      intro B L hB1 σ hσ hp hnt hBL
      exact ⟨ihp B L hB1 σ hσ hp.2.1 hnt.1 hBL,
        ihq B L hB1 σ hσ hp.2.2 hnt.2 hBL⟩
  | forN e body ih =>
      intro B L hB1 σ hσ hp hnt hBL
      obtain ⟨he, hbody⟩ := hp
      refine ⟨le_trans (expr_eval_le_of_bounded_in hσ hB1 e he) hBL, ?_⟩
      intro k hk
      apply ih B L hB1 (loopEval body k σ)
        (g6_loopEval_store_bounded body B k σ
          (fun τ hτ hpτ => g6_program_eval_store_bounded body B hB1 τ hτ hpτ hnt)
          hσ (fun m hm => hbody m (by omega)))
        (hbody k (by omega)) hnt
      omega
  | scanList xs r body ih => intro B L _ σ hσ hp hnt hBL; exact False.elim hnt
  | lookup pairs k v => intro B L _ σ hσ hp hnt hBL; exact False.elim hnt

lemma polynomial_nat_eval_le_power (p : Polynomial ℕ) (N : ℕ) :
    p.eval N ≤
      (p.support.card + 1) * (p.support.sup (fun n => p.coeff n) + 1) *
        (p.support.sup id + 1) * (N + 1) ^
          ((p.support.card + 1) * (p.support.sup (fun n => p.coeff n) + 1) *
            (p.support.sup id + 1)) := by
  let A := p.support.card
  let C := p.support.sup (fun n => p.coeff n)
  let D := p.support.sup id
  let c := (A + 1) * (C + 1) * (D + 1)
  have hA0 : A ≤ A + 1 := by omega
  have hC0 : C ≤ C + 1 := by omega
  have hD0 : D ≤ D + 1 := by omega
  have hqpos : 0 < (A + 1) * (C + 1) := Nat.mul_pos (by omega) (by omega)
  have hq : (A + 1) * (C + 1) ≤ c := by
    dsimp [c]
    apply Nat.le_mul_of_pos_right
    omega
  have hA : A ≤ c := by
    exact le_trans hA0 (le_trans (by apply Nat.le_mul_of_pos_right; omega) hq)
  have hC : C ≤ c := by
    exact le_trans hC0 (le_trans (by apply Nat.le_mul_of_pos_left; omega) hq)
  have hD : D ≤ c := by
    exact le_trans hD0 (by
      dsimp [c]
      apply Nat.le_mul_of_pos_left
      exact hqpos)
  have hAC : A * C ≤ c := by
    exact le_trans (Nat.mul_le_mul hA0 hC0) hq
  have hterm : ∀ n ∈ p.support, p.coeff n * N ^ n ≤ C * (N + 1) ^ c := by
    intro n hn
    have hcn : p.coeff n ≤ C := Finset.le_sup (f := fun n => p.coeff n) hn
    have hdn : n ≤ D := Finset.le_sup (f := fun n => n) hn
    have hp1 : N ^ n ≤ (N + 1) ^ n := Nat.pow_le_pow_left (by omega) _
    have hdc : n ≤ c := le_trans hdn hD
    have hp2 : (N + 1) ^ n ≤ (N + 1) ^ c := Nat.pow_le_pow_right (by omega) hdc
    exact Nat.mul_le_mul hcn (hp1.trans hp2)
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    (∑ n ∈ p.support, p.coeff n * N ^ n) ≤
        ∑ n ∈ p.support, C * (N + 1) ^ c := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ ≤ p.support.card • (C * (N + 1) ^ c) := by
      exact Finset.sum_le_card_nsmul _ _ _ (by intro n hn; rfl)
    _ = A * (C * (N + 1) ^ c) := by simp [A]
    _ = (A * C) * (N + 1) ^ c := by ring
    _ ≤ c * (N + 1) ^ c := Nat.mul_le_mul_right _ hAC

@[construction_api] lemma programBoundedIn_assign (B r : ℕ) (σ : Store) (e : Expr)
    (hr : r ≤ B) (he : ExprBoundedIn B σ e) :
    ProgramBoundedIn B σ (.assign r e) :=
  ⟨hr, he⟩

@[construction_api] lemma programBoundedIn_seq (p q : Program) (B : ℕ) (σ : Store)
    (hp : ProgramBoundedIn B σ p)
    (hq : ProgramBoundedIn B (p.eval σ) q) :
    ProgramBoundedIn B σ (.seq p q) :=
  ⟨hp, hq⟩

end NPComplete.RAMToTM

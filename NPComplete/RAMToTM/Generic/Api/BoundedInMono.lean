module

public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
# Monotonicity of `ProgramBoundedIn` / `ExprBoundedIn` in the operand bound

Callers lift independently derived operand bounds of sibling programs to a shared bound before
composing them under `.seq`.  This leaf module holds the two structural lemmas for that lifting so
that it does not pull in the cost-bound API.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

lemma exprBoundedIn_mono : ∀ (e : Expr) {B B' : ℕ} {σ : Store}, B ≤ B' →
    ExprBoundedIn B σ e → ExprBoundedIn B' σ e := by
  intro e
  induction e with
  | const n => intro B B' σ hB h; simp only [ExprBoundedIn] at h ⊢; omega
  | reg r => intro B B' σ hB h; simp only [ExprBoundedIn] at h ⊢; omega
  | regInd e ih =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih hB h.1, by omega⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih₁ hB h.1, ih₂ hB h.2.1, by omega⟩
  | sub e₁ e₂ ih₁ ih₂ =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih₁ hB h.1, ih₂ hB h.2.1, by omega⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih₁ hB h.1, ih₂ hB h.2.1, by omega⟩
  | lt e₁ e₂ ih₁ ih₂ =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih₁ hB h.1, ih₂ hB h.2⟩
  | eq e₁ e₂ ih₁ ih₂ =>
      intro B B' σ hB h
      simp only [ExprBoundedIn] at h ⊢
      exact ⟨ih₁ hB h.1, ih₂ hB h.2⟩

lemma programBoundedIn_mono : ∀ (p : Program) {B B' : ℕ} {σ : Store}, B ≤ B' →
    ProgramBoundedIn B σ p → ProgramBoundedIn B' σ p := by
  intro p
  induction p with
  | skip => intro B B' σ hB h; trivial
  | assign r e =>
      intro B B' σ hB h
      simp only [ProgramBoundedIn] at h ⊢
      exact ⟨by omega, exprBoundedIn_mono e hB h.2⟩
  | assignInd eA eV =>
      intro B B' σ hB h
      simp only [ProgramBoundedIn] at h ⊢
      exact ⟨exprBoundedIn_mono eA hB h.1, exprBoundedIn_mono eV hB h.2.1, by omega⟩
  | seq p q ihp ihq =>
      intro B B' σ hB h
      simp only [ProgramBoundedIn] at h ⊢
      exact ⟨ihp hB h.1, ihq hB h.2⟩
  | ifNZ e p q ihp ihq =>
      intro B B' σ hB h
      simp only [ProgramBoundedIn] at h ⊢
      exact ⟨exprBoundedIn_mono e hB h.1, ihp hB h.2.1, ihq hB h.2.2⟩
  | forN e body ihbody =>
      intro B B' σ hB h
      simp only [ProgramBoundedIn] at h ⊢
      refine ⟨exprBoundedIn_mono e hB h.1, ?_⟩
      intro m hm
      exact ihbody hB (h.2 m hm)
  | scanList xs r body ih => intro B B' σ hB h; trivial
  | lookup pairs k v => intro B B' σ hB h; trivial

end NPComplete.RAMToTM

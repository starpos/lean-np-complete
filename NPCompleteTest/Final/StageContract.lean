module

import NPComplete

/-!
# Stage contract API, plain `import NPComplete` from a module

Expected: a client builds `StoreFact` values, projects `holds`/`supp`, unfolds `bigAnd`, and proves
and composes `StageSpec` without touching a program body, with no `public import`.
-/

open NPComplete.BoundedWhile NPComplete.RAMToTM

example (σ : Store) (h : (StoreFact.cell 1 5).holds σ) : σ 1 = 5 := h

example : (StoreFact.cell 1 5).supp = {1} := rfl

example : ((StoreFact.cell 1 5).and (StoreFact.cell 2 6)).supp = {1} ∪ {2} := rfl

example (σ : Store) : (StoreFact.bigAnd [.cell 1 1, .cell 2 2, .cell 3 3]).holds σ ↔
    σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 := by
  simp [StoreFact.bigAnd, StoreFact.and, StoreFact.cell]

example (σ : Store) (h : (StoreFact.bigAnd [.cell 1 1, .cell 2 2, .cell 3 3]).holds σ) :
    σ 2 = 2 := by
  rw [StoreFact.holds_bigAnd] at h
  exact h (.cell 2 2) (by simp)

example : Disjoint (StoreFact.bigAnd [.cell 1 1, .cell 2 2]).supp ({10} : Set ℕ) := by
  apply StoreFact.disjoint_bigAnd
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> exact StoreFact.disjoint_cell (by simp)

example {B : ℕ} (hB : 5 ≤ B) :
    StageSpec B (fun _ => True) (.assign 5 (.const 1)) {5} (fun σ => σ 5 = 1) :=
  StageSpec.assign hB (fun _ _ => by simp [ExprBoundedIn]; omega) (by simp [Expr.eval])

example {B : ℕ} {P Q : Store → Prop} {p q : Program} {W₁ W₂ : Set ℕ}
    (h₁ : StageSpec B P p W₁ Q) (h₂ : StageSpec B Q q W₂ Q) :
    StageSpec B P (p.seq q) (W₁ ∪ W₂) Q := h₁.seq h₂

example {B : ℕ} {P Q : Store → Prop} {p : Program} {W : Set ℕ}
    (h : StageSpec B P p W Q) (hd : Disjoint (StoreFact.cell 9 1).supp W) :
    StageSpec B (fun σ => P σ ∧ (StoreFact.cell 9 1).holds σ) p W
      (fun σ => Q σ ∧ (StoreFact.cell 9 1).holds σ) := h.frame_fact _ hd

example {B : ℕ} {Q : Store → Prop} {p : Program} {Wr : ℕ → Prop} {res : List (ℕ × Bool)}
    (h : Comp B Q p Wr res) :
    StageSpec B (fun σ => Q σ ∧ StoreValuesLe B σ) p {r | Wr r} (BoolResults res) :=
  comp_iff_stageSpec.mp h

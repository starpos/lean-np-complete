module

public import NPComplete
public import NPComplete.Test.LayoutContractExample

/-!
# Examples for the layout combinators

Each combinator is used once where a client would otherwise hand-build the obligation: a memory
fact over an interval built by `LayoutFact.ofMem`, separation and inclusion of a conjunction reduced
to its members by `simp only` with the `bigAnd` lemmas, a loop whose footprint grows with the
counter by `LayoutSpec.forN`, and a write to a cell above the layout top by `LayoutSpec.assignCell`.
No tagged declaration lives here, so the file is built by `NPComplete.Extra` only.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout NPComplete.RAMToTM
open NPComplete.Test.LayoutContract

namespace NPComplete.Test.LayoutCombinator

def sevens (n : ℕ) : LayoutFact exL :=
  LayoutFact.ofMem (Set.Ico 600 (600 + n)) (fun _ ha => Nat.le_trans (by decide : exL.top ≤ 600) ha.1)
    (fun σ => ∀ k, k < n → σ (600 + k) = 7)
    (fun _ _ he hσ k hk => (he _ ⟨by omega, by omega⟩).trans (hσ k hk))

lemma sevens_holds (n : ℕ) (σ : Store) : (sevens n).holds σ ↔ ∀ k, k < n → σ (600 + k) = 7 :=
  LayoutFact.holds_ofMem _ _ _ _ σ

lemma sevens_sep_iff {n : ℕ} {H : exL.Foot} :
    (sevens n).foot.Sep H ↔ Disjoint (Set.Ico 600 (600 + n)) H.mem :=
  LayoutFact.ofMem_foot_sep_iff

lemma sevens_le_iff {n : ℕ} {H : exL.Foot} : (sevens n).foot.Le H ↔ Set.Ico 600 (600 + n) ⊆ H.mem :=
  LayoutFact.ofMem_foot_le_iff

def FD : LayoutFact exL := LayoutFact.bigAnd [LayoutFact.reg .ctr 5, sevens 3, sevens 2]

def bound : exL.Foot :=
  ⟨{.ctr, .flag}, Set.Ico 600 603, fun _ ha => Nat.le_trans (by decide : exL.top ≤ 600) ha.1⟩

lemma FD_holds (σ : Store) :
    FD.holds σ ↔ σ (exL.reg .ctr) = 5 ∧ (∀ k, k < 3 → σ (600 + k) = 7) ∧
      ∀ k, k < 2 → σ (600 + k) = 7 := by
  simp only [FD, LayoutFact.bigAnd_cons_cons, LayoutFact.bigAnd_singleton, LayoutFact.holds_and,
    LayoutFact.holds_reg, sevens_holds]

lemma FD_sep : FD.foot.Sep footB := by
  simp only [FD, LayoutFact.foot_bigAnd_sep_iff, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, LayoutFact.reg_foot_sep_iff, sevens_sep_iff]
  refine ⟨by decide, ?_, ?_⟩ <;> simp [footB, Set.disjoint_left] <;> omega

lemma FD_le : FD.foot.Le bound := by
  simp only [FD, LayoutFact.foot_bigAnd_le_iff, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, LayoutFact.reg_foot_le_iff, sevens_le_iff]
  refine ⟨by simp [bound], ?_, ?_⟩ <;> intro a ha <;> simp only [bound, Set.mem_Ico] at ha ⊢ <;>
    omega

lemma FD_sep_of_le : FD.foot.Sep (Foot.regsOnly {.tmp} : exL.Foot) :=
  Foot.Sep.of_le FD_le ⟨by decide, Set.disjoint_empty _⟩

def progD : Program :=
  .seq (.assignInd (.add (.const 600) (.reg (exL.reg .tmp))) (.const 7))
    (.assign (exL.reg .tmp) (.add (.reg (exL.reg .tmp)) (.const 1)))

def winD (j : ℕ) : exL.Foot :=
  ⟨{.tmp}, {600 + j}, fun _ ha => by
    rw [Set.mem_singleton_iff.1 ha]
    exact Nat.le_trans (by decide : exL.top ≤ 600) (Nat.le_add_right _ _)⟩

def allD (n : ℕ) : exL.Foot :=
  ⟨{.tmp}, Set.Ico 600 (600 + n), fun _ ha => Nat.le_trans (by decide : exL.top ≤ 600) ha.1⟩

lemma progD_step {B j : ℕ} (hB : 700 ≤ B) (hj : j ≤ 100) :
    LayoutSpec exL B (fun σ => σ (exL.reg .tmp) = j) progD (winD j)
      (fun σ => σ (exL.reg .tmp) = j + 1 ∧ σ (600 + j) = 7) := by
  have hne : ¬ 2 = 600 + j := by omega
  refine StageSpec.of_writesIn ?_ ?_ ?_
  · intro σ h
    rw [exL_reg_tmp] at h
    simp [progD, winD, Foot.denote, WritesIn, Expr.eval, h, exL_reg_tmp]
  · intro σ h
    rw [exL_reg_tmp] at h
    simp [progD, eval_seq, eval_assignInd, eval_assign, Expr.eval, writeReg, h, exL_reg_tmp]
    omega
  · intro σ h
    rw [exL_reg_tmp] at h
    simp [progD, ProgramBoundedIn, ExprBoundedIn, Expr.eval, exL_reg_tmp, h, eval_assignInd,
      writeReg, hne]
    omega

lemma progD_loop {B : ℕ} (hB : 700 ≤ B) :
    LayoutSpec exL B (fun σ => σ (exL.reg .tmp) = 0) (.forN (.const 3) progD) (allD 3)
      (fun σ => σ (exL.reg .tmp) = 3) := by
  refine LayoutSpec.forN (I := fun j σ => σ (exL.reg .tmp) = j) (Wj := winD) (N := 3)
    (fun _ _ => rfl) (fun _ _ => by simp [ExprBoundedIn]; omega) (fun σ h => h) ?_ ?_
  · intro j hj
    exact (progD_step hB (by omega)).weaken (fun _ h => h) ⟨subset_rfl, subset_rfl⟩
      (fun _ h => h.1)
  · intro j hj
    refine ⟨subset_rfl, fun a ha => ?_⟩
    simp only [winD, allD, Set.mem_singleton_iff, Set.mem_Ico] at ha ⊢
    omega

def cellFoot : exL.Foot := Foot.cell 650 (by simp [exL])

lemma copy_spec {B : ℕ} (hB : 700 ≤ B) :
    LayoutSpec exL B (fun _ => True) (.assign 650 (.reg (exL.reg .ctr))) cellFoot
      (fun σ => σ 650 = σ (exL.reg .ctr)) :=
  LayoutSpec.assignCell (by simp [exL]) (by omega)
    (fun _ _ => by simp [ExprBoundedIn, exL_reg_ctr])
    (fun σ _ => by simp [Expr.eval, writeReg])

lemma copy_frame {B : ℕ} (hB : 700 ≤ B) :
    LayoutSpec exL B (fun σ => True ∧ FB.holds σ) (.assign 650 (.reg (exL.reg .ctr))) cellFoot
      (fun σ => σ 650 = σ (exL.reg .ctr) ∧ FB.holds σ) :=
  (copy_spec hB).frame_fact FB (by
    refine ⟨by simp [cellFoot, Foot.cell], ?_⟩
    simp [FB, LayoutFact.and, LayoutFact.reg, LayoutFact.block, Foot.union, Foot.regsOnly,
      cellFoot, Foot.cell])

end NPComplete.Test.LayoutCombinator

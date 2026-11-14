module

public import NPComplete

/-!
# Acceptance examples for the layout layer of the stage contract

The stage-contract pipeline is rewritten over a role type and a layout: two stages write a
register and, through `assignInd`, a memory cell, and a fact about another register and another
memory block is carried across both and the stages are sequenced.  Register separation is a
`decide` on role sets and memory separation is a `simp` on intervals; the footprint and fact
combinators `Foot.Sep` and `LayoutFact.toStoreFact` connect them to `StageSpec.frame_fact`.
No program body and no `writeReg` is unfolded in the pipeline lemma.  The negative examples show
that role overlap and memory overlap both falsify `Sep`.  No tagged declaration lives here, so the
file is built by `NPComplete.Extra` only.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.BoundedWhile.RegLayout NPComplete.RAMToTM

namespace NPComplete.Test.LayoutContract

inductive Role | ctr | flag | tmp
  deriving DecidableEq

def Role.list : List Role := [.ctr, .flag, .tmp]

lemma Role.mem_list (r : Role) : r ∈ Role.list := by
  cases r <;> simp [Role.list]

def exL : RegLayout Role :=
  ⟨8, ⟨fun | .ctr => 0 | .flag => 1 | .tmp => 2,
    pairwise_ne_injective Role.mem_list (by decide)⟩⟩

lemma exL_reg_ctr : exL.reg .ctr = 0 := rfl

lemma exL_reg_flag : exL.reg .flag = 1 := rfl

lemma exL_reg_tmp : exL.reg .tmp = 2 := rfl

def progA : Program :=
  .seq (.assign (exL.reg .flag) (.const 1)) (.assignInd (.const 100) (.const 1))

def progB : Program :=
  .seq (.assign (exL.reg .tmp) (.const 2)) (.assignInd (.const 200) (.const 2))

def footA : exL.Foot := ⟨{.flag}, {100}, by simp [exL]⟩

def footB : exL.Foot := ⟨{.tmp}, {200}, by simp [exL]⟩

def FA : LayoutFact exL :=
  (LayoutFact.reg .flag 1).and (LayoutFact.block 100 1 (fun _ => 1) (by simp [exL]))

def FB : LayoutFact exL :=
  (LayoutFact.reg .tmp 2).and (LayoutFact.block 200 1 (fun _ => 2) (by simp [exL]))

def FC : LayoutFact exL :=
  (LayoutFact.reg .ctr 5).and (LayoutFact.block 300 2 (fun k => k) (by simp [exL]))

lemma progA_spec {B : ℕ} (hB : 200 ≤ B) :
    LayoutSpec exL B (fun _ => True) progA footA FA.holds := by
  refine StageSpec.of_writesIn ?_ ?_ ?_
  · intro σ _
    simp [progA, footA, Foot.denote, WritesIn, Expr.eval]
  · intro σ _
    simp [progA, FA, LayoutFact.and, LayoutFact.reg, LayoutFact.block, writeReg, Expr.eval]
  · intro σ _
    simp [progA, ProgramBoundedIn, ExprBoundedIn, Expr.eval, exL_reg_flag]
    omega

lemma progB_spec {B : ℕ} (hB : 200 ≤ B) :
    LayoutSpec exL B (fun _ => True) progB footB FB.holds := by
  refine StageSpec.of_writesIn ?_ ?_ ?_
  · intro σ _
    simp [progB, footB, Foot.denote, WritesIn, Expr.eval]
  · intro σ _
    simp [progB, FB, LayoutFact.and, LayoutFact.reg, LayoutFact.block, writeReg, Expr.eval]
  · intro σ _
    simp [progB, ProgramBoundedIn, ExprBoundedIn, Expr.eval, exL_reg_tmp]
    omega

lemma FC_sep_footA : FC.foot.Sep footA := by
  refine ⟨by decide, ?_⟩
  simp [FC, LayoutFact.and, LayoutFact.reg, LayoutFact.block, Foot.union, Foot.regsOnly, footA]

lemma FC_sep_footB : FC.foot.Sep footB := by
  refine ⟨by decide, ?_⟩
  simp [FC, LayoutFact.and, LayoutFact.reg, LayoutFact.block, Foot.union, Foot.regsOnly, footB]

lemma FA_sep_footB : FA.foot.Sep footB := by
  refine ⟨by decide, ?_⟩
  simp [FA, LayoutFact.and, LayoutFact.reg, LayoutFact.block, Foot.union, Foot.regsOnly, footB]

lemma pipeline_spec {B : ℕ} (hB : 200 ≤ B) :
    LayoutSpec exL B FC.holds (progA.seq progB) (footA.union footB)
      (fun σ => FA.holds σ ∧ FB.holds σ ∧ FC.holds σ) := by
  have h₁ : LayoutSpec exL B FC.holds progA footA (fun σ => FA.holds σ ∧ FC.holds σ) :=
    ((progA_spec hB).frame_fact FC FC_sep_footA).weaken
      (fun σ h => ⟨trivial, h⟩) ⟨subset_rfl, subset_rfl⟩ (fun σ h => h)
  have h₂ : LayoutSpec exL B (fun σ => FA.holds σ ∧ FC.holds σ) progB footB
      (fun σ => FA.holds σ ∧ FB.holds σ ∧ FC.holds σ) :=
    (((progB_spec hB).frame_fact FA FA_sep_footB).frame_fact FC FC_sep_footB).weaken
      (fun σ h => ⟨⟨trivial, h.1⟩, h.2⟩) ⟨subset_rfl, subset_rfl⟩
      (fun σ h => ⟨h.1.2, h.1.1, h.2⟩)
  exact h₁.seq h₂

lemma FC_satisfiable : ∃ σ, FC.holds σ :=
  ⟨fun a => if a = 0 then 5 else if a = 301 then 1 else 0, by
    simp only [FC, LayoutFact.and, LayoutFact.reg, LayoutFact.block, exL_reg_ctr]
    refine ⟨by simp, fun k hk => ?_⟩
    interval_cases k <;> simp⟩

lemma pipeline_not_vacuous {B : ℕ} (hB : 200 ≤ B) :
    ∃ σ, FC.holds σ ∧ FA.holds ((progA.seq progB).eval σ) := by
  obtain ⟨σ, hσ⟩ := FC_satisfiable
  exact ⟨σ, hσ, ((pipeline_spec hB) σ hσ).1.1⟩

lemma footprint_not_vacuous :
    ¬ LayoutSpec exL 200 (fun _ => True) progA (Foot.regsOnly {.flag}) (fun _ => True) := by
  intro h
  have := (h emptyStore trivial).2.1 100 (by
    simp [Foot.denote, Foot.regsOnly, exL_reg_flag])
  simp [progA, emptyStore, writeReg, Expr.eval] at this

lemma role_overlap_not_sep : ¬ FA.foot.Sep footA := by
  intro ⟨h, _⟩
  exact absurd h (by decide)

lemma mem_overlap_not_sep :
    ¬ (LayoutFact.block 100 1 (fun _ => 7) (by simp [exL]) : LayoutFact exL).foot.Sep footA := by
  intro ⟨_, h⟩
  exact Set.disjoint_left.1 h (show (100 : ℕ) ∈ Set.Ico 100 (100 + 1) by simp)
    (show (100 : ℕ) ∈ ({100} : Set ℕ) by simp)

lemma regs_only_sep : (LayoutFact.reg .ctr 5 : LayoutFact exL).foot.Sep (Foot.regsOnly {.flag}) :=
  ⟨by decide, Set.disjoint_empty _⟩

def progC : Program := .assign (exL.reg .ctr) (.const 5)

lemma progC_spec {B : ℕ} (hB : 8 ≤ B) :
    LayoutSpec exL B (fun _ => True) progC (Foot.regsOnly {.ctr}) (fun σ => σ (exL.reg .ctr) = 5) :=
  LayoutSpec.assign (by rw [exL_reg_ctr]; omega) (fun _ _ => by simp [ExprBoundedIn]; omega)
    (fun σ _ => by simp [Expr.eval, writeReg])

lemma progC_frame {B : ℕ} (hB : 8 ≤ B) :
    LayoutSpec exL B (fun σ => True ∧ FA.holds σ) progC (Foot.regsOnly {.ctr})
      (fun σ => σ (exL.reg .ctr) = 5 ∧ FA.holds σ) :=
  LayoutSpec.frame_fact_regs (progC_spec hB) FA (by decide)

lemma progC_direct {B : ℕ} (hB : 8 ≤ B) :
    LayoutSpec exL B (fun _ => True) progC (Foot.regsOnly {.ctr}) (fun σ => σ (exL.reg .ctr) = 5) :=
  LayoutSpec.of_direct (by
    simp [Program.Avoids, progC, Foot.denote, Foot.regsOnly])
    (fun σ _ => by simp [progC, Expr.eval, writeReg])
    (fun σ _ => by simp [progC, ProgramBoundedIn, ExprBoundedIn, exL_reg_ctr]; omega)

lemma forN_counter {B : ℕ} (hB : 8 ≤ B) :
    LayoutSpec exL B (fun σ => σ (exL.reg .tmp) = 0)
      (.forN (.const 3) (.assign (exL.reg .tmp) (.add (.reg (exL.reg .tmp)) (.const 1))))
      (Foot.regsOnly {.tmp}) (fun σ => σ (exL.reg .tmp) = 3) := by
  refine LayoutSpec.forN_fixed (I := fun j σ => σ (exL.reg .tmp) = j) (N := 3)
    (fun _ _ => rfl) (fun _ _ => by simp [ExprBoundedIn]; omega) (fun σ h => h) ?_
  intro j hj
  refine LayoutSpec.assign (by rw [exL_reg_tmp]; omega) (fun σ hσ => ?_) (fun σ hσ => ?_)
  · simp only [ExprBoundedIn, Expr.eval, exL_reg_tmp] at hσ ⊢
    omega
  · simp [Expr.eval, hσ]

end NPComplete.Test.LayoutContract

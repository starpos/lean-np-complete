module

public import NPComplete

/-!
# Acceptance examples for the stage contract

Two stages write a register and, through `assignInd`, a memory cell.  A third fact about another
register and another memory block is carried across both stages and the stages are sequenced, using
only `frame_fact`, `seq` and `weaken`; no program body and no `writeReg` is unfolded in the
pipeline lemma.  The negative examples show that the contract and the disjointness side condition
are not vacuous.  The last examples cover the bridge to `Comp`, `keep_values` and `forN`.
No tagged declaration lives here, so the file is built by `NPComplete.Extra` only.
-/

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM

namespace NPComplete.Test.StageContract

def progA : Program :=
  .seq (.assign 1 (.const 1)) (.assignInd (.const 100) (.const 1))

def progB : Program :=
  .seq (.assign 2 (.const 2)) (.assignInd (.const 200) (.const 2))

def footA : Set ℕ := {1, 100}

def footB : Set ℕ := {2, 200}

def FA : StoreFact := (StoreFact.cell 1 1).and (StoreFact.cell 100 1)

def FB : StoreFact := (StoreFact.cell 2 2).and (StoreFact.cell 200 2)

def FC : StoreFact := (StoreFact.cell 3 5).and (StoreFact.block 300 2 (fun k => k))

lemma progA_spec {B : ℕ} (hB : 200 ≤ B) :
    StageSpec B (fun _ => True) progA footA FA.holds := by
  refine StageSpec.of_writesIn ?_ ?_ ?_
  · intro σ _
    simp [progA, footA, WritesIn, Expr.eval]
  · intro σ _
    simp [progA, FA, StoreFact.and, StoreFact.cell, writeReg, Expr.eval]
  · intro σ _
    simp [progA, ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    omega

lemma progB_spec {B : ℕ} (hB : 200 ≤ B) :
    StageSpec B (fun _ => True) progB footB FB.holds := by
  refine StageSpec.of_writesIn ?_ ?_ ?_
  · intro σ _
    simp [progB, footB, WritesIn, Expr.eval]
  · intro σ _
    simp [progB, FB, StoreFact.and, StoreFact.cell, writeReg, Expr.eval]
  · intro σ _
    simp [progB, ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    omega

lemma FC_disjoint {W : Set ℕ} (h3 : 3 ∉ W) (h300 : 300 ∉ W) (h301 : 301 ∉ W) :
    Disjoint FC.supp W := by
  refine Set.disjoint_union_left.mpr ⟨StoreFact.disjoint_cell h3, StoreFact.disjoint_block ?_⟩
  intro k hk
  interval_cases k <;> simpa

lemma FA_disjoint_footB : Disjoint FA.supp footB := by
  refine Set.disjoint_union_left.mpr ⟨StoreFact.disjoint_cell ?_, StoreFact.disjoint_cell ?_⟩ <;>
    simp [footB]

lemma pipeline_spec {B : ℕ} (hB : 200 ≤ B) :
    StageSpec B FC.holds (progA.seq progB) (footA ∪ footB)
      (fun σ => FA.holds σ ∧ FB.holds σ ∧ FC.holds σ) := by
  have h₁ : StageSpec B FC.holds progA footA (fun σ => FA.holds σ ∧ FC.holds σ) :=
    ((progA_spec hB).frame_fact FC
      (FC_disjoint (by simp [footA]) (by simp [footA]) (by simp [footA]))).weaken
      (fun σ h => ⟨trivial, h⟩) subset_rfl (fun σ h => h)
  have h₂ : StageSpec B (fun σ => FA.holds σ ∧ FC.holds σ) progB footB
      (fun σ => FA.holds σ ∧ FB.holds σ ∧ FC.holds σ) :=
    (((progB_spec hB).frame_fact FA FA_disjoint_footB).frame_fact FC
      (FC_disjoint (by simp [footB]) (by simp [footB]) (by simp [footB]))).weaken
      (fun σ h => ⟨⟨trivial, h.1⟩, h.2⟩) subset_rfl (fun σ h => ⟨h.1.2, h.1.1, h.2⟩)
  exact h₁.seq h₂

lemma stage_footprint_not_vacuous : ¬ StageSpec 200 (fun _ => True) progA {1} (fun _ => True) := by
  intro h
  have := (h emptyStore trivial).2.1 100 (by simp)
  simp [progA, emptyStore, writeReg, Expr.eval] at this

lemma fact_not_trivial : ¬ FA.holds emptyStore := by
  simp [FA, StoreFact.and, StoreFact.cell, emptyStore]

lemma overlap_not_disjoint : ¬ Disjoint (StoreFact.cell 100 7).supp footA :=
  StoreFact.not_disjoint_cell (by simp [footA])

lemma bigAnd_holds (σ : Store)
    (h : (StoreFact.bigAnd [.cell 1 1, .cell 2 2, .cell 3 3]).holds σ) :
    σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 := by
  rw [StoreFact.holds_bigAnd] at h
  exact ⟨h (.cell 1 1) (by simp), h (.cell 2 2) (by simp), h (.cell 3 3) (by simp)⟩

lemma bigAnd_disjoint :
    Disjoint (StoreFact.bigAnd [.cell 1 1, .cell 2 2, .cell 3 3]).supp ({10} : Set ℕ) := by
  apply StoreFact.disjoint_bigAnd
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl <;> exact StoreFact.disjoint_cell (by simp)

def assign5 : Program := .assign 5 (.const 1)

def assign6 : Program := .assign 6 (.const 2)

lemma assign5_comp {B : ℕ} (hB : 5 ≤ B) (hB1 : 1 ≤ B) :
    Comp B (fun _ => True) assign5 (fun r => r = 5) [(5, true)] :=
  Comp.assign (b := true) hB (fun _ _ _ => ⟨hB1, by simp [Expr.eval]⟩)

lemma assign5_spec {B : ℕ} (hB : 5 ≤ B) (hB1 : 1 ≤ B) :
    StageSpec B (fun σ => True ∧ StoreValuesLe B σ) assign5 {r | r = 5}
      (BoolResults [(5, true)]) :=
  comp_iff_stageSpec.mp (assign5_comp hB hB1)

lemma assign5_comp' {B : ℕ} (hB : 5 ≤ B) (hB1 : 1 ≤ B) :
    Comp B (fun _ => True) assign5 (fun r => r = 5) [(5, true)] :=
  comp_iff_stageSpec.mpr
    ((StageSpec.assign (P := fun σ => True ∧ StoreValuesLe B σ) (r := 5) (e := .const 1) hB
      (fun _ _ => hB1)
      (fun σ _ => by
        intro q hq
        simp [Expr.eval, writeReg] at hq ⊢
        subst hq
        simp)).weaken (fun _ h => h) (by intro r hr; simpa using hr) (fun _ h => h))

lemma keep_values_pipeline {B : ℕ} (hB : 6 ≤ B) :
    StageSpec B (fun σ => StoreValuesLe B σ) (assign5.seq assign6) ({r | r = 5} ∪ {6})
      (fun σ => BoolResults [(5, true)] σ ∧ StoreValuesLe B σ) := by
  have h₁ := (comp_iff_stageSpec.mp (assign5_comp (B := B) (by omega) (by omega))).keep_values
    (by omega) (by simp [assign5, ScanFree])
  have h₂ : StageSpec B (fun σ => BoolResults [(5, true)] σ) assign6 {6}
      (fun σ => BoolResults [(5, true)] σ) :=
    StageSpec.assign (e := .const 2) (by omega) (fun _ _ => by simp [ExprBoundedIn]; omega)
      (fun σ hσ q hq => by
        simp only [List.mem_singleton] at hq
        subst hq
        simpa [writeReg] using hσ (5, true) (by simp))
  have h₃ := h₂.keep_values (by omega) (by simp [assign6, ScanFree])
  exact (h₁.weaken (fun σ h => ⟨⟨trivial, h⟩, h⟩) subset_rfl (fun σ h => h)).seq h₃

lemma forN_counter {B : ℕ} (hB : 7 ≤ B) :
    StageSpec B (fun σ => σ 7 = 0) (.forN (.const 3) (.assign 7 (.add (.reg 7) (.const 1))))
      {7} (fun σ => σ 7 = 3) := by
  refine StageSpec.forN (I := fun j σ => σ 7 = j) (Wj := fun _ => {7}) (N := 3)
    (fun _ _ => rfl) (fun _ _ => by simp [ExprBoundedIn]; omega) (fun σ h => h) ?_
    (fun _ _ => subset_rfl)
  intro j hj
  refine StageSpec.assign (by omega) (fun σ hσ => ?_) (fun σ hσ => ?_)
  · simp only [ExprBoundedIn, Expr.eval]
    omega
  · simp [Expr.eval, hσ]

lemma of_avoids_assign {B : ℕ} (hB : 5 ≤ B) :
    StageSpec B (fun _ => True) assign5 {5} (fun σ => σ 5 = 1) :=
  StageSpec.of_avoids (by decide +kernel) (fun σ _ => by simp [assign5, Expr.eval])
    (fun σ _ => by simp [assign5, ProgramBoundedIn, ExprBoundedIn]; omega)

lemma mono_bound_example {B : ℕ} (hB : 200 ≤ B) :
    StageSpec (B + 1) (fun _ => True) progA footA FA.holds :=
  (progA_spec hB).mono_bound (Nat.le_succ B)

end NPComplete.Test.StageContract

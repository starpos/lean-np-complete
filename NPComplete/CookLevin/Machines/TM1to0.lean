module

public import NPComplete.CookLevin.Machines.TM1to0.Package
public import NPComplete.CookLevin.Machines.TM2to1
public import Mathlib.Data.Finset.Lattice.Fold

/-!
Mathlib `TM1to0.tr_respects` is a semantic refinement: one TM1 step becomes
at least one TM0 step. Complexity needs the missing upper bound. `trAux`
already emits one micro-step per `move`/`write`/`goto`/`halt` and compiles
`load`/`branch` away, so the bound is a count of those constructors and
does not depend on the tape.
-/

@[expose] public section

namespace NPComplete.CookLevin.TM1to0

open Turing TM0 TM1 Turing.TM1to0
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)
open Function (iterate_succ iterate_succ_apply' iterate_zero_apply)

variable {Γ Λ σ : Type*}

lemma stepsTo_succ_iff {α : Type*} {f : α → Option α} {a c : α} {t : ℕ} :
    StepsTo f a c (t + 1) ↔ ∃ b, StepsTo f a b t ∧ f b = some c := by
  simp [StepsTo, iterate_succ_apply', Option.bind_eq_some_iff]

lemma stepsTo_of_step_eq {α : Type*} {f : α → Option α} {a b c : α} {t : ℕ}
    (heq : f a = f b) (h : StepsTo f b c t) (ht : 0 < t) :
    StepsTo f a c t := by
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simp only [StepsTo, iterate_succ, Function.comp_apply, Option.bind_some] at h ⊢
  rw [heq, h]

/-- An upper bound on the TM0 micro-steps `trAux` emits along any path;
    `branch` takes the maximum and `load` adds nothing. -/
def stmtSize : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => stmtSize q + 1
  | .write _ q => stmtSize q + 1
  | .load _ q => stmtSize q
  | .branch _ q₁ q₂ => max (stmtSize q₁) (stmtSize q₂)
  | .goto _ => 1
  | .halt => 1

def stmtSimBound (q : TM1.Stmt Γ Λ σ) : ℕ := stmtSize q

lemma stmtSize_pos (q : TM1.Stmt Γ Λ σ) : 1 ≤ stmtSize q := by
  induction q <;> simp [stmtSize] <;> omega

def machineStmtBound [Fintype Λ] (M : Λ → TM1.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup fun l => stmtSimBound (M l)

def supportStmtBound (S : Finset Λ) (M : Λ → TM1.Stmt Γ Λ σ) : ℕ :=
  S.sup fun l => stmtSimBound (M l)

variable (M : Λ → TM1.Stmt Γ Λ σ)

lemma stmtSimBound_le_machine [Fintype Λ] (l : Λ) :
    stmtSimBound (M l) ≤ machineStmtBound M :=
  Finset.le_sup (f := fun l => stmtSimBound (M l)) (Finset.mem_univ l)

lemma stmtSimBound_le_support {S : Finset Λ} {l : Λ} (hl : l ∈ S) :
    stmtSimBound (M l) ≤ supportStmtBound S M :=
  Finset.le_sup (f := fun l => stmtSimBound (M l)) hl

lemma tm1_step_eq_some [Inhabited Γ] {c c' : TM1.Cfg Γ Λ σ}
    (h : TM1.step M c = some c') :
    ∃ l v T, c = ⟨some l, v, T⟩ ∧ c' = TM1.stepAux (M l) v T := by
  rcases c with ⟨_ | l, v, T⟩
  · simp [TM1.step] at h
  · refine ⟨l, v, T, rfl, ?_⟩
    simp [TM1.step] at h
    exact h.symm

variable [Inhabited Λ] [Inhabited σ]

lemma tr_move_one [Inhabited Γ] (d : Turing.Dir) (q : TM1.Stmt Γ Λ σ) (v : σ)
    (T : Tape Γ) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.move d q), v), T⟩ =
      some ⟨(some q, v), T.move d⟩ := by
  simp [TM0.step, tr, trAux]

lemma tr_write_one [Inhabited Γ] (a : Γ → σ → Γ) (q : TM1.Stmt Γ Λ σ) (v : σ)
    (T : Tape Γ) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.write a q), v), T⟩ =
      some ⟨(some q, v), T.write (a T.1 v)⟩ := by
  simp [TM0.step, tr, trAux]

lemma tr_load_step_eq [Inhabited Γ] (a : Γ → σ → σ) (q : TM1.Stmt Γ Λ σ) (v : σ)
    (T : Tape Γ) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.load a q), v), T⟩ =
      TM0.step (tr M) ⟨(some q, a T.1 v), T⟩ := by
  simp [TM0.step, tr, trAux]

lemma tr_branch_false [Inhabited Γ] (p : Γ → σ → Bool) (q₁ q₂ : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) (hp : p T.1 v = false) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.branch p q₁ q₂), v), T⟩ =
      TM0.step (tr M) ⟨(some q₂, v), T⟩ := by
  simp [TM0.step, tr, trAux, hp]

lemma tr_branch_true [Inhabited Γ] (p : Γ → σ → Bool) (q₁ q₂ : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) (hp : p T.1 v = true) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.branch p q₁ q₂), v), T⟩ =
      TM0.step (tr M) ⟨(some q₁, v), T⟩ := by
  simp [TM0.step, tr, trAux, hp]

lemma tr_goto_one [Inhabited Γ] (l : Γ → σ → Λ) (v : σ) (T : Tape Γ) :
    TM0.step (tr M) ⟨(some (TM1.Stmt.goto l), v), T⟩ =
      some (trCfg M (TM1.stepAux (TM1.Stmt.goto l) v T)) := by
  simp [TM0.step, tr, trAux, trCfg, TM1.stepAux, Tape.write_self]

lemma tr_halt_one [Inhabited Γ] (v : σ) (T : Tape Γ) :
    TM0.step (tr M) ⟨(some TM1.Stmt.halt, v), T⟩ =
      some (trCfg M (TM1.stepAux TM1.Stmt.halt v T)) := by
  simp [TM0.step, tr, trAux, trCfg, TM1.stepAux, Tape.write_self]

lemma trAux_stepsTo [Inhabited Γ] (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ t, 0 < t ∧
      StepsTo (TM0.step (tr M)) ⟨(some q, v), T⟩
        (trCfg M (TM1.stepAux q v T)) t ∧
      t ≤ stmtSimBound q := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨t, ht0, ht, hle⟩ := ih v (T.move d)
    refine ⟨t + 1, Nat.succ_pos _, ?_, ?_⟩
    · exact stepsTo_cons _ (tr_move_one M d q v T) (by simpa [TM1.stepAux] using ht)
    · simpa [stmtSimBound, stmtSize] using Nat.add_le_add_right hle 1
  | write a q ih =>
    obtain ⟨t, ht0, ht, hle⟩ := ih v (T.write (a T.1 v))
    refine ⟨t + 1, Nat.succ_pos _, ?_, ?_⟩
    · exact stepsTo_cons _ (tr_write_one M a q v T) (by simpa [TM1.stepAux] using ht)
    · simpa [stmtSimBound, stmtSize] using Nat.add_le_add_right hle 1
  | load a q ih =>
    obtain ⟨t, ht0, ht, hle⟩ := ih (a T.1 v) T
    refine ⟨t, ht0, ?_, ?_⟩
    · exact stepsTo_of_step_eq (tr_load_step_eq M a q v T)
        (by simpa [TM1.stepAux] using ht) ht0
    · simpa [stmtSimBound, stmtSize] using hle
  | branch p q₁ q₂ ih₁ ih₂ =>
    cases hp : p T.1 v
    · obtain ⟨t, ht0, ht, hle⟩ := ih₂ v T
      refine ⟨t, ht0, ?_, ?_⟩
      · exact stepsTo_of_step_eq (tr_branch_false M p q₁ q₂ v T hp)
          (by simpa [TM1.stepAux, hp] using ht) ht0
      · exact hle.trans (by simp [stmtSimBound, stmtSize])
    · obtain ⟨t, ht0, ht, hle⟩ := ih₁ v T
      refine ⟨t, ht0, ?_, ?_⟩
      · exact stepsTo_of_step_eq (tr_branch_true M p q₁ q₂ v T hp)
          (by simpa [TM1.stepAux, hp] using ht) ht0
      · exact hle.trans (by simp [stmtSimBound, stmtSize])
  | goto l =>
    refine ⟨1, Nat.one_pos, ?_, by simp [stmtSimBound, stmtSize]⟩
    exact stepsTo_cons _ (tr_goto_one M l v T) (stepsTo_zero _ _)
  | halt =>
    refine ⟨1, Nat.one_pos, ?_, by simp [stmtSimBound, stmtSize]⟩
    exact stepsTo_cons _ (tr_halt_one M v T) (stepsTo_zero _ _)

/-- One TM1 step uses at most `stmtSimBound (M l)` TM0 steps; the bound depends only
    on `M l`. -/
lemma tr_one_step [Inhabited Γ] {l : Λ} {v : σ} {T : Tape Γ} :
    ∃ t, 0 < t ∧
      StepsTo (TM0.step (tr M)) (trCfg M ⟨some l, v, T⟩)
        (trCfg M (TM1.stepAux (M l) v T)) t ∧
      t ≤ stmtSimBound (M l) := by
  simpa [trCfg] using trAux_stepsTo M (M l) v T

lemma trCfg_init [Inhabited Γ] (input : List Γ) :
    trCfg M (TM1.init input) = TM0.init input :=
  rfl

/-- If TM1 runs `T` steps, the TM0 simulation runs in at most `T * machineStmtBound M` steps. -/
lemma tr_total_steps [Inhabited Γ] [Fintype Λ]
    (input : List Γ) {c : TM1.Cfg Γ Λ σ} {T : ℕ}
    (h : StepsTo (TM1.step M) (TM1.init input) c T) :
    ∃ t, StepsTo (TM0.step (tr M)) (trCfg M (TM1.init input)) (trCfg M c) t ∧
      t ≤ T * machineStmtBound M := by
  induction T generalizing c with
  | zero =>
    simp only [StepsTo, iterate_zero_apply, Option.some.injEq] at h
    subst c
    exact ⟨0, stepsTo_zero _ _, Nat.zero_le _⟩
  | succ T ih =>
    obtain ⟨c₀, h₀, hstep⟩ := stepsTo_succ_iff.1 h
    obtain ⟨t₀, ht₀, hle₀⟩ := ih h₀
    obtain ⟨l, v, tape, rfl, rfl⟩ := tm1_step_eq_some M hstep
    obtain ⟨t₁, _, ht₁, hle₁⟩ := tr_one_step M (l := l) (v := v) (T := tape)
    refine ⟨t₁ + t₀, stepsTo_trans _ ht₀ ht₁, ?_⟩
    have hC : stmtSimBound (M l) ≤ machineStmtBound M :=
      stmtSimBound_le_machine M l
    calc
      t₁ + t₀ ≤ stmtSimBound (M l) + T * machineStmtBound M :=
        Nat.add_le_add hle₁ hle₀
      _ ≤ machineStmtBound M + T * machineStmtBound M :=
        Nat.add_le_add_right hC _
      _ = (T + 1) * machineStmtBound M := by
        rw [Nat.add_comm, Nat.succ_mul]

lemma stepsTo_label_mem [Inhabited Γ] {S : Finset Λ} (ss : TM1.Supports M S)
    (input : List Γ) {c : TM1.Cfg Γ Λ σ} {T : ℕ}
    (h : StepsTo (TM1.step M) (TM1.init input) c T) :
    c.l ∈ Finset.insertNone S := by
  induction T generalizing c with
  | zero =>
    simp only [StepsTo, iterate_zero_apply, Option.some.injEq] at h
    subst c
    exact Finset.some_mem_insertNone.2 ss.1
  | succ T ih =>
    obtain ⟨c₀, h₀, hstep⟩ := stepsTo_succ_iff.1 h
    exact TM1.step_supports M ss hstep (ih h₀)

/-- Same total bound, using `supportStmtBound S M` for a given finite support `S`. -/
lemma tr_total_steps_of_support [Inhabited Γ] {S : Finset Λ} (ss : TM1.Supports M S)
    (input : List Γ) {c : TM1.Cfg Γ Λ σ} {T : ℕ}
    (h : StepsTo (TM1.step M) (TM1.init input) c T) :
    ∃ t, StepsTo (TM0.step (tr M)) (trCfg M (TM1.init input)) (trCfg M c) t ∧
      t ≤ T * supportStmtBound S M := by
  induction T generalizing c with
  | zero =>
    simp only [StepsTo, iterate_zero_apply, Option.some.injEq] at h
    subst c
    exact ⟨0, stepsTo_zero _ _, Nat.zero_le _⟩
  | succ T ih =>
    obtain ⟨c₀, h₀, hstep⟩ := stepsTo_succ_iff.1 h
    obtain ⟨t₀, ht₀, hle₀⟩ := ih h₀
    obtain ⟨l, v, tape, rfl, rfl⟩ := tm1_step_eq_some M hstep
    obtain ⟨t₁, _, ht₁, hle₁⟩ := tr_one_step M (l := l) (v := v) (T := tape)
    have hlS : l ∈ S :=
      Finset.some_mem_insertNone.1 (stepsTo_label_mem M ss input h₀)
    refine ⟨t₁ + t₀, stepsTo_trans _ ht₀ ht₁, ?_⟩
    have hC : stmtSimBound (M l) ≤ supportStmtBound S M :=
      stmtSimBound_le_support M hlS
    calc
      t₁ + t₀ ≤ stmtSimBound (M l) + T * supportStmtBound S M :=
        Nat.add_le_add hle₁ hle₀
      _ ≤ supportStmtBound S M + T * supportStmtBound S M :=
        Nat.add_le_add_right hC _
      _ = (T + 1) * supportStmtBound S M := by
        rw [Nat.add_comm, Nat.succ_mul]

end NPComplete.CookLevin.TM1to0

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Machines.TM2to1.Package
public import Mathlib.Computability.StateTransition
public import Mathlib.Tactic.Ring

/-!
Mathlib `TM2to1.tr_respects` is a semantic refinement: one source step becomes
at least one target step. Complexity needs the missing upper bound. The
existing go / act / ret auxiliaries already iterate once per current stack
cell, so the bound is a count of those iterates, not a new shuttle. Stacking
then uses that each TM2 statement grows stacks by at most its `push` count.
-/

@[expose] public section

namespace NPComplete.CookLevin.TM2to1

open Turing TM2to1 StateTransition
open Function (iterate_succ_apply' update)

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- Exact `t`-step reachability, as a proposition. -/
@[stable_api] def StepsTo {α : Type*} (f : α → Option α) (a b : α) (t : ℕ) : Prop :=
  (fun s : Option α => s.bind f)^[t] (some a) = some b

lemma stepsTo_zero {α : Type*} (f : α → Option α) (a : α) : StepsTo f a a 0 :=
  rfl

lemma stepsTo_succ {α : Type*} (f : α → Option α) {a b c : α} {t : ℕ}
    (h : StepsTo f a b t) (hstep : f b = some c) : StepsTo f a c (t + 1) := by
  simp only [StepsTo, iterate_succ_apply']
  rw [h, Option.bind_some, hstep]

lemma stepsTo_cons {α : Type*} (f : α → Option α) {a b c : α} {t : ℕ}
    (hstep : f a = some b) (h : StepsTo f b c t) : StepsTo f a c (t + 1) := by
  simp only [StepsTo, Function.iterate_succ, Function.comp_apply, Option.bind_some, hstep]
  exact h

lemma stepsTo_trans {α : Type*} (f : α → Option α) {a b c : α} {t₁ t₂ : ℕ}
    (h₁ : StepsTo f a b t₁) (h₂ : StepsTo f b c t₂) : StepsTo f a c (t₂ + t₁) := by
  simp only [StepsTo, Function.iterate_add_apply] at *
  rw [h₁, h₂]

lemma stepsTo_of_none {α : Type*} (f : α → Option α) (t : ℕ) :
    (fun s : Option α => s.bind f)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Invert one step off the front of a `StepsTo` chain. -/
lemma stepsTo_cons_inv {α : Type*} (f : α → Option α) {a b : α} {t : ℕ}
    (h : StepsTo f a b (t + 1)) :
    ∃ a', f a = some a' ∧ StepsTo f a' b t := by
  simp only [StepsTo, Function.iterate_succ, Function.comp_apply, Option.bind_some] at h
  rcases hfa : f a with _ | a'
  · rw [hfa, stepsTo_of_none] at h
    exact absurd h (by simp)
  · rw [hfa] at h
    exact ⟨a', rfl, h⟩

/-- Statement size counts the maximum number of constructors along a path; a
    `branch` contributes one plus the larger child size. Bounds shuttle count. -/
def stmtSize : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtSize q + 1
  | .peek _ _ q => stmtSize q + 1
  | .pop _ _ q => stmtSize q + 1
  | .load _ q => stmtSize q + 1
  | .branch _ q₁ q₂ => max (stmtSize q₁) (stmtSize q₂) + 1
  | .goto _ => 1
  | .halt => 1

lemma stmtSize_pos (q : TM2.Stmt Γ Λ σ) : 1 ≤ stmtSize q := by
  induction q <;> simp [stmtSize]

lemma stmtSize_stRun (k : K) (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    stmtSize (stRun s q) = stmtSize q + 1 := by
  cases s <;> rfl

/-- Number of `push` nodes on the heaviest branch. -/
def stmtPushCount : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtPushCount q + 1
  | .peek _ _ q => stmtPushCount q
  | .pop _ _ q => stmtPushCount q
  | .load _ q => stmtPushCount q
  | .branch _ q₁ q₂ => max (stmtPushCount q₁) (stmtPushCount q₂)
  | .goto _ => 0
  | .halt => 0

lemma stmtPushCount_le_stmtSize (q : TM2.Stmt Γ Λ σ) :
    stmtPushCount q ≤ stmtSize q := by
  induction q <;> simp [stmtPushCount, stmtSize] <;> omega

/-- One TM2 statement costs at most this many TM1 steps, given current max stack.
    The extra `stmtSize` in the stack argument pays for `push` growth inside the
    statement, so later shuttles still fit. -/
def stmtSimBound (q : TM2.Stmt Γ Λ σ) (maxStack : ℕ) : ℕ :=
  stmtSize q * (2 * (maxStack + stmtSize q) + 4)

def machineStmtBound [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup fun l => stmtSize (M l)

variable [DecidableEq K]
variable (M : Λ → TM2.Stmt Γ Λ σ)

lemma tr_go_one (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    {n : ℕ} (hn : n < S.length) :
    TM1.step (tr M)
      ⟨some (Λ'.go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
    some ⟨some (Λ'.go k o q), v,
      (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ := by
  rw [iterate_succ_apply']
  simp only [TM1.step, tr, TM1.stepAux]
  simp only [Tape.mk'_nth_nat, Tape.move_right_n_head, addBottom_nth_snd]
  rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
  · simp only [Option.isNone, Bool.cond_false]
  · rwa [List.length_reverse]

lemma tr_go_stepsTo (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    StepsTo (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (Λ'.go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      n := by
  induction n with
  | zero => exact stepsTo_zero _ _
  | succ n ih =>
    exact stepsTo_succ (TM1.step (tr M)) (ih (Nat.le_of_lt hn)) (tr_go_one M k o q v hL hn)

lemma tr_ret_one (q : TM2.Stmt Γ Λ σ) (v : σ)
    {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    TM1.step (tr M)
      ⟨some (Λ'.ret q), v, (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ =
    some ⟨some (Λ'.ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  simp only [TM1.step, tr, TM1.stepAux]
  rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]
  simp only [Bool.cond_false]
  rw [iterate_succ_apply', Tape.move_right_left]

lemma tr_ret_stepsTo (q : TM2.Stmt Γ Λ σ) (v : σ)
    {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    StepsTo (TM1.step (tr M))
      ⟨some (Λ'.ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩
      n := by
  induction n with
  | zero => exact stepsTo_zero _ _
  | succ n ih =>
    exact stepsTo_cons (TM1.step (tr M)) (tr_ret_one M q v n) ih

lemma tr_act_one (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : ∀ k, List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k', L'.map (proj k') =
        ListBlank.mk (((update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      TM1.step (tr M)
        ⟨some (Λ'.go k o q), v,
          (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (Λ'.ret q), stVar v (S k) o,
        (Tape.move Dir.right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
  obtain ⟨L', hL', hrun⟩ :=
    tr_respects_aux₂ (Λ := Λ) (q := TM1.Stmt.goto fun _ _ => Λ'.ret q) hL o
  refine ⟨L', hL', ?_⟩
  simp only [TM1.step, tr, TM1.stepAux]
  rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
    stk_nth_val _ (hL k), List.getElem?_eq_none (le_of_eq List.length_reverse)]
  simp only [Option.isNone, Bool.cond_true]
  rw [hrun, Function.update_self]
  rfl

omit [DecidableEq K] in
lemma stWrite_length_le (k : K) (v : σ) (l : List (Γ k)) (o : StAct K Γ σ k) :
    (stWrite v l o).length ≤ l.length + 1 := by
  cases o with
  | push f => simp [stWrite]
  | peek f => simp [stWrite]
  | pop f =>
    simp [stWrite, List.length_tail]
    omega

/-- One stack action: go `n` + act `1` + ret `n'`, with `n' ≤ n + 1`. -/
lemma tr_shuttle_stepsTo (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : ∀ k, List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ L' t, (∀ k', L'.map (proj k') =
        ListBlank.mk (((update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      StepsTo (TM1.step (tr M))
        ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
        ⟨some (Λ'.ret q), stVar v (S k) o, Tape.mk' ∅ (addBottom L')⟩ t ∧
      t ≤ 2 * (S k).length + 2 := by
  obtain ⟨L', hL', hact⟩ := tr_act_one M k o q v hL
  let n := (S k).length
  let n' := (stWrite v (S k) o).length
  have hgo := tr_go_stepsTo M k o q v (hL k) n le_rfl
  have hret := tr_ret_stepsTo M q (stVar v (S k) o) (L := L') n'
  have hmid : StepsTo (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (Λ'.ret q), stVar v (S k) o,
        (Tape.move Dir.right)^[n'] (Tape.mk' ∅ (addBottom L'))⟩ (n + 1) :=
    stepsTo_succ (TM1.step (tr M)) hgo hact
  refine ⟨L', n' + (n + 1), hL', stepsTo_trans _ hmid hret, ?_⟩
  have hn' : n' ≤ n + 1 := stWrite_length_le k v (S k) o
  omega

lemma tr_ret_bottom (q : TM2.Stmt Γ Λ σ) (v : σ)
    {L : ListBlank (∀ k, Option (Γ k))} :
    TM1.step (tr M) ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩ =
      some (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) := by
  simp only [TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst, Bool.cond_true]

lemma update_length_le_add_one (S : ∀ k, List (Γ k)) (k' k : K) (l : List (Γ k'))
    (hl : l.length ≤ (S k').length + 1) :
    (update S k' l k).length ≤ (S k).length + 1 := by
  rcases eq_or_ne k k' with rfl | hk
  · simpa [Function.update_self] using hl
  · simp [Function.update_of_ne hk]

lemma stepAux_stk_len_le (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtPushCount q := by
  induction q generalizing v S with
  | push k' f q ih =>
    refine (ih v (update S k' (f v :: S k'))).trans ?_
    simp only [stmtPushCount]
    have hlen : (f v :: S k').length ≤ (S k').length + 1 := by simp
    have := update_length_le_add_one S k' k (f v :: S k') hlen
    omega
  | peek k' f q ih =>
    simpa [TM2.stepAux, stmtPushCount] using ih (f v (S k').head?) S
  | pop k' f q ih =>
    refine (ih (f v (S k').head?) (update S k' (S k').tail)).trans ?_
    simp only [stmtPushCount]
    have hle : (update S k' (S k').tail k).length ≤ (S k).length := by
      rcases eq_or_ne k k' with rfl | hk
      · simp [Function.update_self, List.length_tail]
      · simp [Function.update_of_ne hk]
    omega
  | load a q ih =>
    simpa [TM2.stepAux, stmtPushCount] using ih (a v) S
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtPushCount]
    cases p v
    · exact (ih₂ v S).trans (by gcongr; exact Nat.le_max_right _ _)
    · exact (ih₁ v S).trans (by gcongr; exact Nat.le_max_left _ _)
  | goto f => simp [TM2.stepAux, stmtPushCount]
  | halt => simp [TM2.stepAux, stmtPushCount]

omit [DecidableEq K] in
lemma stmtSimBound_mono {q q' : TM2.Stmt Γ Λ σ} {n : ℕ} (h : stmtSize q ≤ stmtSize q') :
    stmtSimBound q n ≤ stmtSimBound q' n := by
  unfold stmtSimBound
  exact Nat.mul_le_mul h (by omega)

/-- `TM2.stepAux q` reached from the pure TM1 unfolding of `trNormal q`, with a step bound.
    The `+ 1` on the bound reserves the single TM1 step that produced this pure state (either
    the initial `normal l` step or a `ret`-state step after a stack shuttle), so callers can add
    that step back without breaking the bound. -/
lemma tr_stmt_stepsTo (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (T : ListBlank (∀ k, Option (Γ k)))
    (hT : ∀ k, T.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (n : ℕ) (hn : ∀ k, (S k).length ≤ n) :
    ∃ c' t, TrCfg (TM2.stepAux q v S) c' ∧
      StepsTo (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) c' t ∧
      t + 1 ≤ stmtSimBound q n := by
  induction q using stmtStRec generalizing v S T n with
  | run k s q' IH =>
    have hc0 : TM1.stepAux (trNormal (stRun s q')) v (Tape.mk' ∅ (addBottom T)) =
        ⟨some (Λ'.go k s q'), v, Tape.mk' ∅ (addBottom T)⟩ := by
      simp [trNormal_run, TM1.stepAux]
    obtain ⟨L', t₁, hL', hshuttle, ht₁⟩ := tr_shuttle_stepsTo M k s q' v hT
    have hstep2 : StepsTo (TM1.step (tr M))
        ⟨some (Λ'.go k s q'), v, Tape.mk' ∅ (addBottom T)⟩
        (TM1.stepAux (trNormal q') (stVar v (S k) s) (Tape.mk' ∅ (addBottom L'))) (t₁ + 1) :=
      stepsTo_succ (TM1.step (tr M)) hshuttle (tr_ret_bottom M q' (stVar v (S k) s))
    have hn' : ∀ j, ((update S k (stWrite v (S k) s)) j).length ≤ n + 1 := fun j => by
      have h1 := update_length_le_add_one S k j (stWrite v (S k) s) (stWrite_length_le k v (S k) s)
      have h2 := hn j
      omega
    obtain ⟨c', t₂, hc', hsteps2, hbound2⟩ :=
      IH (stVar v (S k) s) (update S k (stWrite v (S k) s)) L' hL' (n + 1) hn'
    refine ⟨c', t₂ + (t₁ + 1), ?_, ?_, ?_⟩
    · rw [step_run q' v S s]; exact hc'
    · rw [hc0]; exact stepsTo_trans (TM1.step (tr M)) hstep2 hsteps2
    · have hSize : stmtSize (stRun s q') = stmtSize q' + 1 := stmtSize_stRun k s q'
      have hnk := hn k
      have ht1 : t₁ + 1 ≤ 2 * (n + stmtSize q' + 1) + 4 := by omega
      have hEq1 : stmtSimBound q' (n + 1) = stmtSize q' * (2 * (n + stmtSize q' + 1) + 4) := by
        simp only [stmtSimBound]; ring
      have hEq2 : stmtSimBound (stRun s q') n =
          stmtSize q' * (2 * (n + stmtSize q' + 1) + 4) + (2 * (n + stmtSize q' + 1) + 4) := by
        simp only [stmtSimBound, hSize]; ring
      rw [hEq1] at hbound2
      rw [hEq2]
      omega
  | load a q' IH =>
    obtain ⟨c', t, hc', hsteps, hbound⟩ := IH (a v) S T hT n hn
    refine ⟨c', t, hc', ?_, hbound.trans (stmtSimBound_mono (by simp [stmtSize]))⟩
    simpa [trNormal, TM1.stepAux] using hsteps
  | branch p q₁ q₂ IH₁ IH₂ =>
    rcases hp : p v with - | -
    · obtain ⟨c', t, hc', hsteps, hbound⟩ := IH₂ v S T hT n hn
      refine ⟨c', t, ?_, ?_, hbound.trans (stmtSimBound_mono (by simp [stmtSize]; omega))⟩
      · simpa [hp] using hc'
      · simpa [trNormal, TM1.stepAux, hp] using hsteps
    · obtain ⟨c', t, hc', hsteps, hbound⟩ := IH₁ v S T hT n hn
      refine ⟨c', t, ?_, ?_, hbound.trans (stmtSimBound_mono (by simp [stmtSize]; omega))⟩
      · simpa [hp] using hc'
      · simpa [trNormal, TM1.stepAux, hp] using hsteps
  | goto f =>
    refine ⟨_, 0, TrCfg.mk T hT, stepsTo_zero _ _, ?_⟩
    simp only [stmtSimBound]
    have h1 := stmtSize_pos (Γ := Γ) (Λ := Λ) (TM2.Stmt.goto f)
    generalize stmtSize (TM2.Stmt.goto f) = m at h1 ⊢
    have h2 : 1 ≤ 2 * (n + m) + 4 := by omega
    have h3 := Nat.mul_le_mul h1 h2
    omega
  | halt =>
    refine ⟨_, 0, TrCfg.mk T hT, stepsTo_zero _ _, ?_⟩
    simp only [stmtSimBound]
    have h1 := stmtSize_pos (Γ := Γ) (Λ := Λ) (TM2.Stmt.halt (σ := σ))
    generalize stmtSize (TM2.Stmt.halt (σ := σ)) = m at h1 ⊢
    have h2 : 1 ≤ 2 * (n + m) + 4 := by omega
    have h3 := Nat.mul_le_mul h1 h2
    omega

/-- One TM2 step uses at most `stmtSimBound (M l) n` TM1 steps, linear in the current
    max stack. -/
lemma tr_one_step {l : Λ} {v : σ} {S : ∀ k, List (Γ k)}
    {c₂ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (htr : TrCfg ⟨some l, v, S⟩ c₂) (n : ℕ) (hn : ∀ k, (S k).length ≤ n) :
    ∃ c₂' t, TrCfg (TM2.stepAux (M l) v S) c₂' ∧
      StepsTo (TM1.step (tr M)) c₂ c₂' t ∧
      t ≤ stmtSimBound (M l) n := by
  obtain ⟨T, hT⟩ := htr
  obtain ⟨c', t, hc', hsteps, hbound⟩ := tr_stmt_stepsTo M (M l) v S T hT n hn
  refine ⟨c', t + 1, hc', ?_, by omega⟩
  have hentry : TM1.step (tr M) ⟨some (Λ'.normal l), v, Tape.mk' ∅ (addBottom T)⟩ =
      some (TM1.stepAux (trNormal (M l)) v (Tape.mk' ∅ (addBottom T))) := by
    simp [TM1.step, tr]
  exact stepsTo_cons (TM1.step (tr M)) hentry hsteps

/-- Iterating `tr_one_step` for `T` steps, keeping the running max stack bound at
    `n₀ + i * machineStmtBound M` after `i` steps (`stepAux_stk_len_le` pays for the
    growth each step). -/
lemma tr_total_steps_aux [Fintype Λ] (T : ℕ) :
    ∀ (c₀ : TM2.Cfg Γ Λ σ) (c₀' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (n₀ : ℕ),
      TrCfg c₀ c₀' → (∀ k, (c₀.stk k).length ≤ n₀) →
      ∀ c, StepsTo (TM2.step M) c₀ c T →
        ∃ c' t, TrCfg c c' ∧ StepsTo (TM1.step (tr M)) c₀' c' t ∧
          t ≤ T * machineStmtBound M * (2 * (n₀ + T * machineStmtBound M) + 4) := by
  induction T with
  | zero =>
    intro c₀ c₀' n₀ hc₀ hn₀ c hstep
    have hcc : c₀ = c := by
      simp only [StepsTo, Function.iterate_zero, id] at hstep
      exact Option.some.inj hstep
    subst hcc
    exact ⟨c₀', 0, hc₀, stepsTo_zero _ _, by simp⟩
  | succ T ih =>
    intro c₀ c₀' n₀ hc₀ hn₀ c hstep
    obtain ⟨cmid, hstep1, hstepRest⟩ := stepsTo_cons_inv (TM2.step M) hstep
    obtain ⟨lo, v₀, S₀⟩ := c₀
    cases lo with
    | none => simp [TM2.step] at hstep1
    | some l₀ =>
      have hcmid : cmid = TM2.stepAux (M l₀) v₀ S₀ := by
        simpa [TM2.step] using hstep1.symm
      subst hcmid
      obtain ⟨cmid', t₁, hcmid', hstepA, hbound1⟩ := tr_one_step M hc₀ n₀ hn₀
      simp only [stmtSimBound] at hbound1
      have hCle : stmtSize (M l₀) ≤ machineStmtBound M :=
        Finset.le_sup (f := fun l => stmtSize (M l)) (Finset.mem_univ l₀)
      have hn1 : ∀ k, ((TM2.stepAux (M l₀) v₀ S₀).stk k).length ≤ n₀ + machineStmtBound M := by
        intro k
        have h1 := stepAux_stk_len_le (M l₀) v₀ S₀ k
        have h2 := stmtPushCount_le_stmtSize (M l₀)
        have h3 : (S₀ k).length ≤ n₀ := hn₀ k
        omega
      obtain ⟨c', t₂, hc', hstepB, hbound2⟩ :=
        ih (TM2.stepAux (M l₀) v₀ S₀) cmid' (n₀ + machineStmtBound M) hcmid' hn1 c hstepRest
      refine ⟨c', t₂ + t₁, hc', stepsTo_trans (TM1.step (tr M)) hstepA hstepB, ?_⟩
      have hCC : n₀ + machineStmtBound M + T * machineStmtBound M =
          n₀ + (T + 1) * machineStmtBound M := by ring
      rw [hCC] at hbound2
      have hCTC : machineStmtBound M ≤ (T + 1) * machineStmtBound M := by
        have := Nat.mul_le_mul (show 1 ≤ T + 1 by omega) (le_refl (machineStmtBound M))
        simpa using this
      have hSle : stmtSize (M l₀) ≤ (T + 1) * machineStmtBound M := hCle.trans hCTC
      have ht1 : t₁ ≤ machineStmtBound M * (2 * (n₀ + (T + 1) * machineStmtBound M) + 4) :=
        hbound1.trans (Nat.mul_le_mul hCle (by omega))
      have hEq : (T + 1) * machineStmtBound M * (2 * (n₀ + (T + 1) * machineStmtBound M) + 4) =
          T * machineStmtBound M * (2 * (n₀ + (T + 1) * machineStmtBound M) + 4) +
            machineStmtBound M * (2 * (n₀ + (T + 1) * machineStmtBound M) + 4) := by ring
      rw [hEq]
      omega

/-- If TM2 runs `T` steps from an input of length `n`, the TM1 simulation
    runs in at most `T * machineStmtBound M *
    (2 * (input.length + T * machineStmtBound M) + 4)` steps. -/
lemma tr_total_steps [Fintype K] [Fintype Λ] [Inhabited Λ] [Inhabited σ]
    (k₀ : K) (input : List (Γ k₀)) {c : TM2.Cfg Γ Λ σ} {T : ℕ}
    (h : StepsTo (TM2.step M) (TM2.init k₀ input) c T) :
    ∃ c' t, TrCfg c c' ∧
      StepsTo (TM1.step (tr M))
        (TM1.init (trInit k₀ input) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) c' t ∧
      t ≤ T * machineStmtBound M * (2 * (input.length + T * machineStmtBound M) + 4) := by
  have hlen : ∀ k : K, ((TM2.init k₀ input : TM2.Cfg Γ Λ σ).stk k).length ≤ input.length := by
    intro k
    rcases eq_or_ne k k₀ with rfl | hne
    · simp [TM2.init, Function.update_self]
    · simp [TM2.init, Function.update_of_ne hne]
  exact tr_total_steps_aux M T (TM2.init k₀ input) _ input.length (trCfg_init k₀ input) hlen c h

end NPComplete.CookLevin.TM2to1

module

public import NPComplete.CookLevin.Tableau

/-!
# Explicit tableau window

Some reductions need a window chosen independently of input and output lengths while retaining the
same local tableau clauses. This module provides that explicit-window variant so callers can enlarge
the rectangular encoding without changing its semantics.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-- The tableau core with an explicitly supplied window.  Keeping the window
independent from the input and output lengths lets callers use a larger
rectangular layout while retaining the same local semantic clauses. -/
noncomputable def tableauMachineWithInitAtWindow [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset Λ) (_input output : List Γ)
    (T W : ℕ) (initial : List Clause) : CNF :=
  ⟨uniquenessClauses (Γ := Γ) S W T ++
      initial ++
        transClauses M S W T ++
          persistClauses (Γ := Γ) W T ++
            acceptClauses M S output W T⟩

/-- Semantic Cook-Levin tableau at an explicitly supplied window. -/
noncomputable def tableauMachineAtWindow [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset Λ) (input output : List Γ)
    (T W : ℕ) : CNF :=
  tableauMachineWithInitAtWindow M S input output T W
    (initClauses S input W T)

/-- Assignment used for the converse direction at an explicitly supplied
window.  Unlike `runAssign`, this definition records every cell and head in
that supplied window. -/
noncomputable def runAssignAtWindow [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset Λ) (input _output : List Γ)
    (T W : ℕ) : Literal.Assignment :=
  fun v =>
    (List.range (T + 1)).any fun t =>
      let c := runCfg M input t
      let hd := runHead M input t
      S.toList.any (fun q => decide (v = stateVar t (stateIdx S q) ∧ c.q = q)) ||
        (List.range W).any fun p =>
          decide (v = headVar t p ∧ hd = idxToPos T p) ||
            (letters Γ).any fun a =>
              decide (v = cellVar t p (letterIdx a) ∧
                absNth c hd (idxToPos T p) = a)

lemma runAssignAtWindow_state [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t : ℕ} (ht : t ≤ T) (hq : (runCfg M input t).q ∈ S) :
    runAssignAtWindow M S input output T W
        (stateVar t (stateIdx S (runCfg M input t).q)) = true := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inl ⟨(runCfg M input t).q, ?_, ?_⟩⟩
  · exact Finset.mem_toList.mpr hq
  · exact ⟨rfl, rfl⟩

lemma runAssignAtWindow_head [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t p : ℕ} (ht : t ≤ T) (hp : p < W)
    (hhd : runHead M input t = idxToPos T p) :
    runAssignAtWindow M S input output T W (headVar t p) = true := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inr ⟨p, List.mem_range.mpr hp, Or.inl ⟨rfl, hhd⟩⟩⟩

lemma runAssignAtWindow_cell [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t p : ℕ} {a : Γ} (ht : t ≤ T) (hp : p < W)
    (ha : absNth (runCfg M input t) (runHead M input t) (idxToPos T p) = a) :
    runAssignAtWindow M S input output T W
        (cellVar t p (letterIdx a)) = true := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inr ⟨p, List.mem_range.mpr hp, Or.inr ?_⟩⟩
  exact ⟨a, mem_letters a, ⟨rfl, ha⟩⟩

lemma runAssignAtWindow_state_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t : ℕ} {q : Λ}
    (h : runAssignAtWindow M S input output T W
      (stateVar t (stateIdx S q)) = true) :
    t ≤ T ∧ q ∈ S ∧ (runCfg M input t).q = q := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨t', ht', hcase⟩ := h
  have ht'le : t' ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht')
  rcases hcase with hst | hrest
  · obtain ⟨q', hq', hv, hqeq⟩ := hst
    obtain ⟨rfl, hidx⟩ := stateVar_eq_iff.mp hv
    have hq : q ∈ S := Finset.mem_toList.mp (mem_of_idxOf_eq hq' hidx)
    exact ⟨ht'le, hq,
      hqeq.trans (stateIdx_inj (Finset.mem_toList.mp hq') hq hidx.symm)⟩
  · rcases hrest with ⟨p, _, hhp | hcell⟩
    · exact (stateVar_ne_headVar _ _ _ _ hhp.1).elim
    · obtain ⟨_, _, hv, _⟩ := hcell
      exact (cellVar_ne_stateVar _ _ _ _ _ hv.symm).elim

lemma runAssignAtWindow_head_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t p : ℕ}
    (h : runAssignAtWindow M S input output T W (headVar t p) = true) :
    t ≤ T ∧ runHead M input t = idxToPos T p := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨t', ht', hcase⟩ := h
  have ht'le : t' ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht')
  rcases hcase with hst | hrest
  · obtain ⟨q', _, hv, _⟩ := hst
    exact (stateVar_ne_headVar _ _ _ _ hv.symm).elim
  · obtain ⟨p', _, hhp | hcell⟩ := hrest
    · obtain ⟨hv, hhd⟩ := hhp
      obtain ⟨rfl, rfl⟩ := headVar_eq_iff.mp hv
      exact ⟨ht'le, hhd⟩
    · obtain ⟨a, _, hv, _⟩ := hcell
      exact (cellVar_ne_headVar _ _ _ _ _ hv.symm).elim

lemma runAssignAtWindow_cell_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W t p : ℕ} {a : Γ}
    (h : runAssignAtWindow M S input output T W
      (cellVar t p (letterIdx a)) = true) :
    t ≤ T ∧ absNth (runCfg M input t) (runHead M input t)
      (idxToPos T p) = a := by
  simp only [runAssignAtWindow, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨t', ht', hcase⟩ := h
  have ht'le : t' ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht')
  rcases hcase with hst | hrest
  · obtain ⟨q', _, hv, _⟩ := hst
    exact (cellVar_ne_stateVar _ _ _ _ _ hv).elim
  · obtain ⟨p', _, hhp | hcell⟩ := hrest
    · obtain ⟨hv, _⟩ := hhp
      exact (cellVar_ne_headVar _ _ _ _ _ hv).elim
    · obtain ⟨a', _, hv, habs⟩ := hcell
      obtain ⟨rfl, rfl, haidx⟩ := cellVar_eq_iff.mp hv
      rw [← letterIdx_inj haidx] at habs
      exact ⟨ht'le, habs⟩

lemma sat_run_step_at_window [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T t W : ℕ} {τ : Literal.Assignment}
    (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W)
    (htrans : ∀ c ∈ transClauses M S W T, c.Satisfied τ)
    (ht : t < T)
    (hst : τ (stateVar t (stateIdx S (runCfg M input t).q)) = true)
    (hhd : τ (headVar t (posToIdx T (runHead M input t))) = true)
    (hcl : τ (cellVar t (posToIdx T (runHead M input t))
      (letterIdx (runCfg M input t).Tape.head)) = true) :
    τ (stateVar (t + 1) (stateIdx S (runCfg M input (t + 1)).q)) = true ∧
    τ (headVar (t + 1) (posToIdx T (runHead M input (t + 1)))) = true ∧
    τ (cellVar (t + 1) (posToIdx T (runHead M input t))
      (letterIdx (absNth (runCfg M input (t + 1)) (runHead M input (t + 1))
        (runHead M input t)))) = true := by
  have hqS : (runCfg M input t).q ∈ S := runCfg_state_mem hS input t
  have haL : (runCfg M input t).Tape.head ∈ letters Γ := mem_letters _
  have hpW : posToIdx T (runHead M input t) < W := by
    exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input ht.le) hW
  have hInst : ∀ x ∈ transOne M S W t (posToIdx T (runHead M input t))
      (runCfg M input t).q (runCfg M input t).Tape.head, x.Satisfied τ := by
    intro x hx
    apply htrans
    simp only [transClauses, List.mem_flatMap]
    exact ⟨t, List.mem_range.mpr ht, posToIdx T (runHead M input t),
      List.mem_range.mpr hpW, (runCfg M input t).q, Finset.mem_toList.mpr hqS,
      (runCfg M input t).Tape.head, haL, hx⟩
  have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  rcases hM : M (runCfg M input t).q (runCfg M input t).Tape.head with _ | ⟨q', stmt⟩
  · simp only [transOne, hM] at hInst
    set st := stateVar t (stateIdx S (runCfg M input t).q)
    set hd := headVar t (posToIdx T (runHead M input t))
    set cl := cellVar t (posToIdx T (runHead M input t))
      (letterIdx (runCfg M input t).Tape.head)
    have h1 : (imply3 st hd cl
        (stateVar (t + 1) (stateIdx S (runCfg M input t).q))).Satisfied τ :=
      hInst _ (by simp)
    have h2 : (imply3 st hd cl
        (headVar (t + 1) (posToIdx T (runHead M input t)))).Satisfied τ :=
      hInst _ (by simp)
    have h3 : (imply3 st hd cl (cellVar (t + 1)
        (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head))).Satisfied τ := hInst _ (by simp)
    replace h1 := eval_imply3 h1 hst hhd hcl
    replace h2 := eval_imply3 h2 hst hhd hcl
    replace h3 := eval_imply3 h3 hst hhd hcl
    refine ⟨?_, ?_, ?_⟩
    · rw [hstepc]; simp only [stepOrStay, step, hM]; exact h1
    · rw [hheadc]; simp only [stepHead, hM]; exact h2
    · rw [hstepc, hheadc]
      simp only [stepOrStay, step, stepHead, hM, absNth, Tape.nth_zero, sub_self]
      exact h3
  · have hq'S : q' ∈ S := hS.2 (Option.mem_def.mpr hM) hqS
    rcases stmt with d | b
    · exact sat_run_step_move hM ht (by
        exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input ht) hW)
        hInst hq'S hst hhd hcl
    · simp only [transOne, hM, ite_eq_left hq'S] at hInst
      set st := stateVar t (stateIdx S (runCfg M input t).q)
      set hd := headVar t (posToIdx T (runHead M input t))
      set cl := cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)
      have h1 : (imply3 st hd cl
          (stateVar (t + 1) (stateIdx S q'))).Satisfied τ := hInst _ (by simp)
      have h2 : (imply3 st hd cl
          (headVar (t + 1) (posToIdx T (runHead M input t)))).Satisfied τ :=
        hInst _ (by simp)
      have h3 : (imply3 st hd cl (cellVar (t + 1)
          (posToIdx T (runHead M input t)) (letterIdx b))).Satisfied τ :=
        hInst _ (by simp)
      replace h1 := eval_imply3 h1 hst hhd hcl
      replace h2 := eval_imply3 h2 hst hhd hcl
      replace h3 := eval_imply3 h3 hst hhd hcl
      refine ⟨?_, ?_, ?_⟩
      · rw [hstepc]; simp only [stepOrStay, step, hM]; exact h1
      · rw [hheadc]; simp only [stepHead, hM]; exact h2
      · rw [hstepc, hheadc, absNth_stepOrStay_write hM]; exact h3

lemma sat_run_cell_succ_at_window [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {input output : List Γ}
    {T t W : ℕ} {τ : Literal.Assignment}
    (hW : windowSize input.length output.length T ≤ W)
    (hpersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ)
    (ht : t < T)
    (hhd : τ (headVar t (posToIdx T (runHead M input t))) = true)
    (hclAll : ∀ p, p < W →
      τ (cellVar t p (letterIdx (absNth (runCfg M input t) (runHead M input t)
        (idxToPos T p)))) = true)
    (hclHead : τ (cellVar (t + 1) (posToIdx T (runHead M input t))
      (letterIdx (absNth (runCfg M input (t + 1)) (runHead M input (t + 1))
        (runHead M input t)))) = true) :
    ∀ p, p < W →
      τ (cellVar (t + 1) p (letterIdx (absNth (runCfg M input (t + 1))
        (runHead M input (t + 1)) (idxToPos T p)))) = true := by
  intro p hp
  have hboundT : -(T : ℤ) ≤ runHead M input t := by
    have := (runHead_abs_le M input t).1
    omega
  have hpHeadEq : idxToPos T (posToIdx T (runHead M input t)) = runHead M input t :=
    idxToPos_posToIdx hboundT
  by_cases hpeq : p = posToIdx T (runHead M input t)
  · subst hpeq
    rwa [hpHeadEq]
  · have hcl_t := hclAll p hp
    have hres := sat_run_persist hpersist ht
      (by exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input ht.le) hW)
      hp (fun he => hpeq he.symm) hhd hcl_t
    have hne : idxToPos T p ≠ runHead M input t := by
      rw [← hpHeadEq]
      intro he
      apply hpeq
      simp only [idxToPos] at he
      omega
    have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
    have hheadc : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rw [hstepc, hheadc, absNth_stepOrStay_of_ne hne]
    exact hres

/-- Forward induction over the run: the base case reads the initial
configuration off `initClauses`, and the step case derives the state, head and
touched cell at `t+1` from those at `t` via `sat_run_step_at_window`, then
propagates the untouched cells with `sat_run_cell_succ_at_window`. -/
lemma sat_run_at_window [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} {τ : Literal.Assignment} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W)
    (hinit : ∀ c ∈ initClauses S input W T, c.Satisfied τ)
    (htrans : ∀ c ∈ transClauses M S W T, c.Satisfied τ)
    (hpersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ) :
    ∀ t, t ≤ T →
      τ (stateVar t (stateIdx S (runCfg M input t).q)) = true ∧
      τ (headVar t (posToIdx T (runHead M input t))) = true ∧
      ∀ p, p < W →
        τ (cellVar t p (letterIdx (absNth (runCfg M input t)
          (runHead M input t) (idxToPos T p)))) = true := by
  intro t
  induction t with
  | zero =>
    intro _
    have hdef : (default : Λ) ∈ S := Finset.mem_coe.mp hS.1
    refine ⟨?_, ?_, ?_⟩
    · simpa [runCfg_zero, init] using state_of_initClauses hdef hinit
    · simpa [runHead_zero, posToIdx, originIdx] using head_of_initClauses hinit
    · intro p hp
      simpa [runCfg_zero, runHead_zero, absNth, init, tape_mk₁_nth] using
        initSymbol_of_initClauses hinit hp
  | succ t ih =>
    intro ht1
    have ht : t < T := by omega
    obtain ⟨hst, hhd, hclAll⟩ := ih ht.le
    have hcellhead : τ (cellVar t (posToIdx T (runHead M input t))
        (letterIdx (runCfg M input t).Tape.head)) = true := by
      have hb := hclAll (posToIdx T (runHead M input t))
        (lt_of_lt_of_le (runHead_posToIdx_lt_window M input ht.le) hW)
      have heq : idxToPos T (posToIdx T (runHead M input t)) = runHead M input t :=
        idxToPos_posToIdx (by have := (runHead_abs_le M input t).1; omega)
      rw [heq] at hb
      simpa [absNth] using hb
    obtain ⟨hst', hhd', hclhead'⟩ :=
      sat_run_step_at_window hS hW htrans ht hst hhd hcellhead
    exact ⟨hst', hhd', sat_run_cell_succ_at_window hW hpersist ht hhd hclAll hclhead'⟩

/-- `nextIdx_move_isSome_of_real` generalized past the tight window: at any
`W ≥ windowSize ...`, a genuinely-reached head position still always has room
to move, since enlarging `W` only weakens the right-edge side condition. -/
lemma nextIdx_move_isSome_of_real_at_window [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (input : List Γ)
    {T t p W inputLen outputLen : ℕ} (d : Dir) (ht : t < T)
    (hW : windowSize inputLen outputLen T ≤ W)
    (hpeq : runHead M input t = idxToPos T p) :
    ∃ p', nextIdx W p d = some p' ∧
      idxToPos T p' = runHead M input t + dirDelta d := by
  have hb := runHead_abs_le M input t
  have hpreal : p = posToIdx T (runHead M input t) := by
    rw [hpeq]; exact (posToIdx_idxToPos T p).symm
  subst hpreal
  rcases d with _ | _
  · have hlo : -(T : ℤ) ≤ runHead M input t - 1 := by omega
    exact ⟨posToIdx T (runHead M input t - 1), nextIdx_left_eq hlo, by
      rw [idxToPos_posToIdx hlo]; simp only [dirDelta]; ring⟩
  · have hlo : -(T : ℤ) ≤ runHead M input t := by omega
    have hhi : posToIdx T (runHead M input t + 1) < W :=
      lt_of_lt_of_le (posToIdx_lt_window (by omega)) hW
    exact ⟨posToIdx T (runHead M input t + 1), nextIdx_right_eq hlo hhi, by
      rw [idxToPos_posToIdx (by omega : -(T : ℤ) ≤ runHead M input t + 1)]
      simp [dirDelta]⟩

/-- `transOne_of_run_none` generalized to an enlarged window and
`runAssignAtWindow`: the stuttering clauses at a halted step are witnessed
regardless of `p`, so the window-size change never enters this branch. -/
lemma transOne_at_window_of_run_none [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T W t p : ℕ} {q : Λ} {a : Γ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = none) (ht : t < T) :
    ∀ c ∈ transOne M S W t p q a,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  set τ := runAssignAtWindow M S input output T W with hτdef
  intro c hc
  simp only [transOne, hM, List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
      τ (cellVar t p (letterIdx a)) = true →
      τ (stateVar (t + 1) (stateIdx S q)) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx a)) = true := by
    intro hst hhd hcl
    obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
      (τ := τ)
      (fun h => (runAssignAtWindow_state_inv h).2.2)
      (fun h => (runAssignAtWindow_head_inv h).2)
      (fun h => (runAssignAtWindow_cell_inv h).2)
      hst hhd hcl
    exact transOne_of_run_none_successor hS hW hM ht
      hqreal hpreal hareal
      (fun hu hq => runAssignAtWindow_state hu hq)
      (fun hu hp hhead => runAssignAtWindow_head hu hp hhead)
      (fun hu hp hcell => runAssignAtWindow_cell hu hp hcell)
  rcases hc with rfl | rfl | rfl
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- `transOne_of_run_write` generalized to an enlarged window and
`runAssignAtWindow`: a write never relocates the head, so `p` stays inside
whichever window contains the real head position at time `t`. -/
lemma transOne_at_window_of_run_write [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T W t p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {b : Γ}
    (hS : Supports M ↑S) (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = some (q', Stmt.write b)) (ht : t < T) (hq'S : q' ∈ S) :
    ∀ c ∈ transOne M S W t p q a,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  set τ := runAssignAtWindow M S input output T W with hτdef
  intro c hc
  simp only [transOne, hM, ite_eq_left hq'S, List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
      τ (cellVar t p (letterIdx a)) = true →
      τ (stateVar (t + 1) (stateIdx S q')) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx b)) = true := by
    intro hst hhd hcl
    obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
      (τ := τ)
      (fun h => (runAssignAtWindow_state_inv h).2.2)
      (fun h => (runAssignAtWindow_head_inv h).2)
      (fun h => (runAssignAtWindow_cell_inv h).2)
      hst hhd hcl
    exact transOne_of_run_write_successor hS hW hM ht
      hqreal hpreal hareal
      (fun hu hq => runAssignAtWindow_state hu hq)
      (fun hu hp hhead => runAssignAtWindow_head hu hp hhead)
      (fun hu hp hcell => runAssignAtWindow_cell hu hp hcell)
  rcases hc with rfl | rfl | rfl
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- `transOne_of_run_move` generalized to an enlarged window and
`runAssignAtWindow`.  The `forbid3` (window-edge) branch is still shown
impossible via `nextIdx_move_isSome_of_real_at_window`, which only needs
`W ≥ windowSize ...`, not equality. -/
lemma transOne_at_window_of_run_move [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T W t p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {d : Dir}
    (hS : Supports M ↑S) (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = some (q', Stmt.move d)) (ht : t < T) (hq'S : q' ∈ S) :
    ∀ c ∈ transOne M S W t p q a,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  set τ := runAssignAtWindow M S input output T W with hτdef
  rcases hnextval : nextIdx W p d with _ | p'
  · intro c hc
    simp only [transOne, hM, ite_eq_left hq'S, hnextval, List.mem_singleton] at hc
    subst hc
    refine satisfied_forbid3 (fun _ hhd => ?_)
    obtain ⟨p'', hp'eq, _⟩ := nextIdx_move_isSome_of_real_at_window M input
      (inputLen := input.length) (outputLen := output.length) d ht hW
      (runAssignAtWindow_head_inv hhd).2
    rw [hnextval] at hp'eq
    exact absurd hp'eq (by simp)
  · intro c hc
    simp only [transOne, hM, ite_eq_left hq'S, hnextval, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
        τ (cellVar t p (letterIdx a)) = true →
        τ (stateVar (t + 1) (stateIdx S q')) = true ∧
        τ (headVar (t + 1) p') = true ∧
        τ (cellVar (t + 1) p (letterIdx a)) = true := by
      intro hst hhd hcl
      obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
        (τ := τ)
        (fun h => (runAssignAtWindow_state_inv h).2.2)
        (fun h => (runAssignAtWindow_head_inv h).2)
        (fun h => (runAssignAtWindow_cell_inv h).2)
        hst hhd hcl
      exact transOne_of_run_move_successor hS hW hM ht
        hqreal hpreal hareal hnextval
        (fun hu hq => runAssignAtWindow_state hu hq)
        (fun hu hp hhead => runAssignAtWindow_head hu hp hhead)
        (fun hu hp hcell => runAssignAtWindow_cell hu hp hcell)
    rcases hc with rfl | rfl | rfl
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- `transOne_of_run` generalized to an enlarged window: dispatches on the
machine's transition function, delegating the three shapes above. -/
lemma transOne_at_window_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T W t p : ℕ} {q : Λ} {a : Γ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W) (hq : q ∈ S) (ht : t < T) :
    ∀ c ∈ transOne M S W t p q a,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  rcases hM : M q a with _ | ⟨q', stmt⟩
  · exact transOne_at_window_of_run_none hS hW hM ht
  · have hq'S : q' ∈ S := hS.2 (Option.mem_def.mpr hM) hq
    rcases stmt with d | b
    · exact transOne_at_window_of_run_move hS hW hM ht hq'S
    · exact transOne_at_window_of_run_write hS hW hM ht hq'S

/-- The transition family at an enlarged window is witnessed by the real run;
the `nextIdx` boundary bookkeeping generalizes past the tight window since
the real head position always has room to move in the enlarged window too
(`nextIdx_move_isSome_of_real_at_window`). -/
lemma transClauses_at_window_of_run [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W) :
    ∀ c ∈ transClauses M S W T,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  intro c hc
  simp only [transClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, p, hp, q, hq, a, ha, hc⟩ := hc
  exact transOne_at_window_of_run hS hW (Finset.mem_toList.mp hq) (List.mem_range.mp ht) c hc

lemma uniquenessClauses_at_window_of_run [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W) :
    ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  intro c hc
  simp only [uniquenessClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, hc⟩ := hc
  have htT : t ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht)
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · have hnodup : (S.toList.map fun q => stateVar t (stateIdx S q)).Nodup :=
        List.Nodup.map_on
          (fun q1 hq1 q2 hq2 heq => stateIdx_inj (Finset.mem_toList.mp hq1)
            (Finset.mem_toList.mp hq2) (stateVar_eq_iff.mp heq).2)
          S.nodup_toList
      refine satisfied_exactlyOne_of_unique hnodup
        (List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (runCfg_state_mem hS input t), rfl⟩)
        (runAssignAtWindow_state htT (runCfg_state_mem hS input t)) ?_ c hc
      intro v hv htv
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
      exact congrArg (fun q' => stateVar t (stateIdx S q'))
        (runAssignAtWindow_state_inv htv).2.2.symm
    · have hb0 : -(T : ℤ) ≤ runHead M input t := by
        have h := (runHead_abs_le M input t).1
        have hcast : (t : ℤ) ≤ T := by exact_mod_cast htT
        omega
      have hp0W : posToIdx T (runHead M input t) < W := by
        exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input htT) hW
      have hhd0 : runHead M input t = idxToPos T (posToIdx T (runHead M input t)) :=
        (idxToPos_posToIdx hb0).symm
      have hnodup : ((List.range W).map fun p => headVar t p).Nodup :=
        List.Nodup.map (fun p1 p2 heq => (headVar_eq_iff.mp heq).2) List.nodup_range
      refine satisfied_exactlyOne_of_unique hnodup
        (List.mem_map.mpr ⟨_, List.mem_range.mpr hp0W, rfl⟩)
        (runAssignAtWindow_head htT hp0W hhd0) ?_ c hc
      intro v hv htv
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
      have hp : runHead M input t = idxToPos T p :=
        (runAssignAtWindow_head_inv htv).2
      have hpeq : posToIdx T (runHead M input t) = p := by
        have heq := congrArg (posToIdx T) (hhd0.symm.trans hp)
        simpa [posToIdx_idxToPos] using heq
      exact congrArg (headVar t) hpeq.symm
  · simp only [List.mem_flatMap] at hc
    obtain ⟨p, hp, hc⟩ := hc
    have hpW : p < W := List.mem_range.mp hp
    have hnodup : ((letters Γ).map fun a => cellVar t p (letterIdx a)).Nodup :=
      List.Nodup.map_on
        (fun a1 _ a2 _ heq => letterIdx_inj (cellVar_eq_iff.mp heq).2.2)
        letters_nodup
    refine satisfied_exactlyOne_of_unique hnodup
      (List.mem_map.mpr ⟨_, mem_letters _, rfl⟩)
      (runAssignAtWindow_cell htT hpW rfl) ?_ c hc
    intro v hv htv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact congrArg (fun x => cellVar t p (letterIdx x))
      (runAssignAtWindow_cell_inv htv).2.symm

lemma initClauses_at_window_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W) :
    ∀ c ∈ initClauses S input W T,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  intro c hc
  have hst : (initStateClause (Λ := Λ) S).Satisfied
      (runAssignAtWindow M S input output T W) := by
    have hdef : (default : Λ) ∈ S := hS.1
    simp only [initStateClause, hdef, ↓reduceIte]
    refine satisfied_unitPos ?_
    simpa [runCfg, init] using
      (runAssignAtWindow_state (M := M) (S := S) (input := input)
        (output := output) (T := T) (W := W) (t := 0) (Nat.zero_le _)
        (by simpa [runCfg, init] using hdef))
  have hhd : (unitPos (headVar 0 (originIdx T))).Satisfied
      (runAssignAtWindow M S input output T W) := by
    refine satisfied_unitPos ?_
    refine runAssignAtWindow_head (ht := Nat.zero_le _)
      (hp := lt_of_lt_of_le (originIdx_lt_window input.length output.length T) hW) ?_
    simp [runHead, originIdx, idxToPos]
  have hcell : ∀ p, p < W →
      (unitPos (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p))))).Satisfied
        (runAssignAtWindow M S input output T W) := by
    intro p hp
    refine satisfied_unitPos ?_
    refine runAssignAtWindow_cell (ht := Nat.zero_le _) (hp := hp) ?_
    simp [absNth, runCfg, runHead, init, tape_mk₁_nth]
  simp [initClauses, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | rfl | ⟨p, hp, rfl⟩
  · exact hst
  · exact hhd
  · exact hcell p hp

lemma persistClauses_at_window_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} :
    ∀ c ∈ persistClauses (Γ := Γ) W T,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  intro c hc
  simp only [persistClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, pHead, hpHead, pCell, hpCell, hc⟩ := hc
  have htT : t < T := List.mem_range.mp ht
  have hpHeadW : pHead < W := List.mem_range.mp hpHead
  have hpCellW : pCell < W := List.mem_range.mp hpCell
  by_cases hne : pHead = pCell
  · simp [hne] at hc
  · rw [ite_eq_right hne] at hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    refine satisfied_imply2 (fun hhd hcl => ?_)
    have hpeq : runHead M input t = idxToPos T pHead :=
      (runAssignAtWindow_head_inv hhd).2
    have haeq : absNth (runCfg M input t) (runHead M input t) (idxToPos T pCell) = a :=
      (runAssignAtWindow_cell_inv hcl).2
    have hne' : idxToPos T pCell ≠ runHead M input t := by
      rw [hpeq]
      intro he
      have hp : posToIdx T (idxToPos T pCell) = posToIdx T (idxToPos T pHead) :=
        congrArg (posToIdx T) he
      simp only [posToIdx_idxToPos] at hp
      exact hne hp.symm
    refine runAssignAtWindow_cell (M := M) (S := S) (input := input)
      (output := output) (T := T) (W := W) (t := t + 1) (p := pCell)
      (by omega) hpCellW ?_
    have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
    have hheadc : runHead M input (t + 1) =
        stepHead M (runCfg M input t) (runHead M input t) := rfl
    rw [hstepc, hheadc, absNth_stepOrStay_of_ne hne']
    exact haeq

lemma acceptClauses_at_window_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} (hS : Supports M ↑S)
    (hRun : MachineOutputsInTime M input output T) :
    ∀ c ∈ acceptClauses M S output W T,
      c.Satisfied (runAssignAtWindow M S input output T W) := by
  obtain ⟨hshape, hhalt⟩ := runCfg_of_machineOutputsInTime hRun
  intro c hc
  simp only [acceptClauses, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_singleton] at hc
  rcases hc with ⟨pHead, _, p, hpmem, rfl⟩ | rfl
  · have hpW : p < W := List.mem_range.mp hpmem
    refine satisfied_implyPos (fun hhd => ?_)
    have hpeq : runHead M input T = idxToPos T pHead :=
      (runAssignAtWindow_head_inv hhd).2
    refine runAssignAtWindow_cell (M := M) (S := S) (input := input)
      (output := output) (T := T) (W := W) (t := T) (le_refl T) hpW ?_
    show absNth (runCfg M input T) (runHead M input T) (idxToPos T p) =
      initSymbol output ((p : ℤ) - (pHead : ℤ))
    simp only [absNth, hshape, tape_mk₁_nth]
    congr 1
    rw [hpeq]
    simp only [idxToPos]
    ring
  · have hheadeq : (runCfg M input T).Tape.head = initSymbol output 0 := by
      rw [hshape, ← Tape.nth_zero, tape_mk₁_nth]
    have hMhalt : M (runCfg M input T).q (initSymbol output 0) = none := by
      rw [← hheadeq]
      exact step_eq_none_iff.mp hhalt
    have hqinS : (runCfg M input T).q ∈ S := runCfg_state_mem hS input T
    have hqinHalt : (runCfg M input T).q ∈ haltStates M S (initSymbol output 0) := by
      simp only [haltStates, List.mem_filter, Finset.mem_toList]
      exact ⟨hqinS, by rw [hMhalt]⟩
    exact satisfied_atLeastOne
      (List.mem_map.mpr ⟨(runCfg M input T).q, hqinHalt, rfl⟩)
      (runAssignAtWindow_state (M := M) (S := S) (input := input)
        (output := output) (T := T) (W := W) (t := T) (le_refl T) hqinS)

/-- Cells outside the rectangular window still hold the initial blank, so they
agree with the output tape's default symbol. -/
lemma tableauMachineAtWindow_sat_imp_machineOutputsInTime_outside_window
    [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (input output : List Γ) (T : ℕ) (p : ℤ)
    (hlo : -(T : ℤ) ≤ runHead M input T) (hhi : runHead M input T ≤ T)
    (hout : ¬ (-(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1)) :
    absNth (runCfg M input T) (runHead M input T) (runHead M input T + p) =
      initSymbol output p := by
  have huntouched : runHead M input T + p < -(T : ℤ) ∨ (T : ℤ) < runHead M input T + p := by
    omega
  rw [absNth_eq_initSymbol_of_untouched M input T _ huntouched]
  rcases (by omega : runHead M input T + p < -(T : ℤ) ∨
      (max input.length output.length + T : ℤ) + 1 ≤ runHead M input T + p) with hneg | hpos
  · rw [initSymbol_eq_default_of_neg (by omega), initSymbol_eq_default_of_neg (by omega)]
  · have hm1 := le_max_left input.length output.length
    have hm2 := le_max_right input.length output.length
    rw [initSymbol_eq_default_of_ge (by omega), initSymbol_eq_default_of_ge (by omega)]

/-- Inside the window, the satisfying assignment's cell variables at time `T`
are pinned to the output tape by the accept clauses and uniqueness. -/
lemma tableauMachineAtWindow_sat_imp_machineOutputsInTime_inside_window
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment}
    (hW : windowSize input.length output.length T ≤ W)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hhdT : τ (headVar T (posToIdx T (runHead M input T))) = true)
    (hWpos : posToIdx T (runHead M input T) < W)
    (hclT : ∀ p, p < W → τ (cellVar T p (letterIdx (absNth (runCfg M input T)
      (runHead M input T) (idxToPos T p)))) = true)
    (hlo : -(T : ℤ) ≤ runHead M input T) (p : ℤ)
    (hin : -(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1) :
    absNth (runCfg M input T) (runHead M input T) (runHead M input T + p) =
      initSymbol output p := by
  have hpW : posToIdx T (runHead M input T + p) < W :=
    lt_of_lt_of_le (posToIdx_lt_window hin.2) hW
  have hcellT := hclT _ hpW
  rw [idxToPos_posToIdx hin.1] at hcellT
  have hmem : implyPos (headVar T (posToIdx T (runHead M input T)))
      (cellVar T (posToIdx T (runHead M input T + p))
        (letterIdx (initSymbol output ((posToIdx T (runHead M input T + p) : ℤ) -
          (posToIdx T (runHead M input T) : ℤ))))) ∈ acceptClauses M S output W T := by
    simp only [acceptClauses, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inl ⟨_, List.mem_range.mpr hWpos, _, List.mem_range.mpr hpW, rfl⟩
  rw [atMostOne_cell_of_sat (le_refl T) hUniq hpW hcellT
    (eval_implyPos (hAccept _ hmem) hhdT)]
  have hlo' : -(T : ℤ) ≤ runHead M input T + p := hin.1
  have hc1 : (posToIdx T (runHead M input T + p) : ℤ) = runHead M input T + p + T :=
    Int.toNat_of_nonneg (by omega)
  have hc2 : (posToIdx T (runHead M input T) : ℤ) = runHead M input T + T :=
    Int.toNat_of_nonneg (by omega)
  congr 1
  rw [hc1, hc2]
  ring

/-- The tape at time `T` equals the output tape. -/
lemma tableauMachineAtWindow_sat_imp_machineOutputsInTime_tape
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment}
    (hW : windowSize input.length output.length T ≤ W)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hhdT : τ (headVar T (posToIdx T (runHead M input T))) = true)
    (hclT : ∀ p, p < W → τ (cellVar T p (letterIdx (absNth (runCfg M input T)
      (runHead M input T) (idxToPos T p)))) = true) :
    (runCfg M input T).Tape = Tape.mk₁ output := by
  have hlo : -(T : ℤ) ≤ runHead M input T := by
    have := (runHead_abs_le M input T).1
    omega
  have hhi : runHead M input T ≤ (T : ℤ) := by
    have := (runHead_abs_le M input T).2
    omega
  have hWpos : posToIdx T (runHead M input T) < W :=
    lt_of_lt_of_le (runHead_posToIdx_lt_window M input (le_refl T)) hW
  apply tape_ext_of_nth
  intro p
  rw [tape_mk₁_nth, ← show absNth (runCfg M input T) (runHead M input T)
      (runHead M input T + p) = (runCfg M input T).Tape.nth p by simp [absNth]]
  by_cases hpw : -(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1
  · exact tableauMachineAtWindow_sat_imp_machineOutputsInTime_inside_window hW hUniq
      hAccept hhdT hWpos hclT hlo p hpw
  · exact tableauMachineAtWindow_sat_imp_machineOutputsInTime_outside_window M input output
      T p hlo hhi hpw

/-- A satisfied accept clause on the halting state forces the machine to halt on
the output head symbol. -/
lemma tableauMachineAtWindow_sat_imp_machineOutputsInTime_halt
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment} (hS : Supports M ↑S)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hstT : τ (stateVar T (stateIdx S (runCfg M input T).q)) = true)
    (hshape : (runCfg M input T).Tape = Tape.mk₁ output) :
    step M (runCfg M input T) = none := by
  have hhaltClause : atLeastOne
      ((haltStates M S (initSymbol output 0)).map
        fun q => stateVar T (stateIdx S q)) ∈ acceptClauses M S output W T := by
    simp [acceptClauses]
  obtain ⟨qv, hqvmem, hqvtrue⟩ := atLeastOne_exists (hAccept _ hhaltClause)
  simp only [List.mem_map] at hqvmem
  obtain ⟨q, hqmem, hqeq⟩ := hqvmem
  rw [← hqeq] at hqvtrue
  have hqeqReal : q = (runCfg M input T).q :=
    atMostOne_state_of_sat (S := S) (le_refl T) hUniq
      (Finset.mem_toList.mp (List.mem_of_mem_filter hqmem))
      (runCfg_state_mem hS input T) hqvtrue hstT
  have hmatch := (List.mem_filter.mp (hqeqReal ▸ hqmem)).2
  have hMeq : M (runCfg M input T).q (initSymbol output 0) = none := by
    rcases hMM : M (runCfg M input T).q (initSymbol output 0) with _ | _
    · rfl
    · simp [hMM] at hmatch
  rw [step_eq_none_iff, show (runCfg M input T).Tape.head = initSymbol output 0 by
    rw [hshape, ← Tape.nth_zero, tape_mk₁_nth]]
  exact hMeq

lemma tableauMachineAtWindow_sat_imp_machineOutputsInTime
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T W : ℕ} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W)
    (hSAT : SAT (tableauMachineAtWindow M S input output T W)) :
    MachineOutputsInTime M input output T := by
  obtain ⟨τ, hτ⟩ := hSAT
  have hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append]
    aesop
  have hInit : ∀ c ∈ initClauses S input W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append]
    aesop
  have hTrans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append]
    aesop
  have hPersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append]
    aesop
  have hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append]
    aesop
  obtain ⟨hstT, hhdT, hclAllT⟩ :=
    sat_run_at_window hS hW hInit hTrans hPersist T (le_refl T)
  have hshape := tableauMachineAtWindow_sat_imp_machineOutputsInTime_tape hW hUniq
    hAccept hhdT hclAllT
  exact machineOutputsInTime_of_halted hshape
    (tableauMachineAtWindow_sat_imp_machineOutputsInTime_halt hS hUniq hAccept hstT hshape)

lemma tableauMachineAtWindow_sat_iff [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (input output : List Γ) (T W : ℕ) (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W) :
    SAT (tableauMachineAtWindow M S input output T W) ↔
      MachineOutputsInTime M input output T := by
  constructor
  · exact tableauMachineAtWindow_sat_imp_machineOutputsInTime hS hW
  · intro hRun
    have hUniq := uniquenessClauses_at_window_of_run (M := M) (S := S)
      (input := input) (output := output) hS hW
    have hInit := initClauses_at_window_of_run (M := M) (S := S)
      (input := input) (output := output) hS hW
    have hTrans := transClauses_at_window_of_run (M := M) (S := S)
      (input := input) (output := output) hS hW
    have hPersist := persistClauses_at_window_of_run (M := M) (S := S)
      (input := input) (output := output) (T := T) (W := W)
    have hAccept := acceptClauses_at_window_of_run (M := M) (S := S)
      (input := input) (output := output) (T := T) (W := W) hS hRun
    refine ⟨runAssignAtWindow M S input output T W, ?_⟩
    intro c hc
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append] at hc
    aesop

/-- `tableauMachineWithInit_sat_of_run_of_initial` generalized to an
explicitly supplied window: any initial-clause list whose satisfaction
follows from the standard `tableauMachineAtWindow` clauses is witnessed by
the same satisfying assignment. -/
lemma tableauMachineWithInitAtWindow_sat_of_run_of_initial
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {initial : List Clause} (hS : Supports M ↑S)
    (hW : windowSize input.length output.length T ≤ W)
    (hRun : MachineOutputsInTime M input output T)
    (hInit : ∀ τ : Literal.Assignment,
      (∀ c ∈ (tableauMachineAtWindow M S input output T W).clauses,
        c.Satisfied τ) →
      ∀ c ∈ initial, c.Satisfied τ) :
    SAT (tableauMachineWithInitAtWindow M S input output T W initial) := by
  obtain ⟨τ, hτ⟩ := (tableauMachineAtWindow_sat_iff M S input output T W hS hW).mpr hRun
  have hinitial := hInit τ hτ
  have huniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  have htrans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  have hpersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  have haccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  refine ⟨τ, ?_⟩
  intro c hc
  simp only [tableauMachineWithInitAtWindow, List.mem_append] at hc
  aesop

/-- `boundedPrefixInitClauses_of_standard_sat` extends the result beyond the
    tight window: under `hspan`, `hprefix`, `hfree`, and `htail`, any assignment
    `τ` satisfying all `tableauMachineAtWindow` clauses satisfies every
    `boundedPrefixInitClauses` clause. -/
lemma boundedPrefixInitClauses_of_at_window_sat
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ}
    {input pref output : List Γ} {freeLen W T k : ℕ}
    {allowed : List Γ} {blank : Γ} {τ : Literal.Assignment}
    (hspan : T + pref.length + freeLen + 1 ≤ W)
    (hstd : ∀ c ∈ (tableauMachineAtWindow M S input output T W).clauses,
      c.Satisfied τ)
    (hprefix : ∀ p, p < T + pref.length →
      initSymbol input (idxToPos T p) = initSymbol pref (idxToPos T p))
    (hfree : ∀ i, i < freeLen →
      ∃ a ∈ blank :: allowed, initSymbol input
          (idxToPos T (T + pref.length + i)) = a ∧
        ((i < k ∧ a ≠ blank) ∨ (k ≤ i ∧ a = blank)))
    (htail : ∀ p, T + pref.length + freeLen ≤ p →
      initSymbol input (idxToPos T p) = blank) :
    ∀ c ∈ boundedPrefixInitClauses S pref freeLen allowed blank W T,
      c.Satisfied τ := by
  have huniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied τ := by
    intro c hc
    apply hstd
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  have hstdInit : ∀ c ∈ initClauses S input W T,
      c.Satisfied τ := by
    intro c hc
    apply hstd
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow, List.mem_append]
    aesop
  have hstdCell : ∀ p, p < W →
      τ (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p)))) = true := by
    intro p hp
    apply eval_unitPos
    apply hstdInit
    simp only [initClauses, List.mem_cons, List.mem_map]
    exact Or.inr (Or.inr ⟨p, List.mem_range.mpr hp, rfl⟩)
  intro c hc
  unfold boundedPrefixInitClauses at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
    have hpW : p < W := List.mem_range.mp hp
    by_cases hfix : p < T + pref.length
    · rw [ite_eq_left hfix]
      refine satisfied_unitPos ?_
      simpa [hprefix p hfix] using hstdCell p hpW
    · by_cases hfree' : p < T + pref.length + freeLen
      · rw [ite_eq_right hfix, ite_eq_left hfree']
        let i := p - (T + pref.length)
        have hi : i < freeLen := by
          dsimp [i]
          omega
        have hpEq : p = T + pref.length + i := by
          dsimp [i]
          omega
        obtain ⟨a, ha, hEq, hcase⟩ := hfree i hi
        refine satisfied_atLeastOne
          (List.mem_map.mpr ⟨a, ha, rfl⟩) ?_
        have hcell := hstdCell p hpW
        rw [hpEq] at hcell
        rw [hEq] at hcell
        rw [hpEq]
        exact hcell
      · rw [ite_eq_right hfix, ite_eq_right hfree']
        refine satisfied_unitPos ?_
        simpa [htail p (by omega)] using hstdCell p hpW
  · rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
    have hi' : i < freeLen := List.mem_range.mp hi
    have hp : T + pref.length + i < W := by omega
    have hpNext : T + pref.length + i + 1 < W := by omega
    obtain ⟨a, ha, hEq, hcase⟩ := hfree i hi'
    by_cases hik : i < k
    · have hne : a ≠ blank := by
        rcases hcase with ⟨_, hne⟩ | hblank
        · exact hne
        · omega
      have hcell := hstdCell (T + pref.length + i) hp
      have hcell' : τ (cellVar 0 (T + pref.length + i)
          (letterIdx a)) = true := by
        simpa [hEq] using hcell
      have hfalse := cell_value_false_of_uniqueness huniq hp hcell' hne
      refine ⟨Literal.neg
        (cellVar 0 (T + pref.length + i) (letterIdx blank)), by
          simp [implyPos], ?_⟩
      simp [Literal.eval, hfalse]
    · have hblank : a = blank := by
        rcases hcase with htrue | ⟨hge, hblank⟩
        · omega
        · exact hblank
      by_cases hinext : i + 1 < freeLen
      · obtain ⟨a', ha', hEq', hcase'⟩ := hfree (i + 1) hinext
        have hblank' : a' = blank := by
          rcases hcase' with htrue | ⟨hge, hblank'⟩
          · omega
          · exact hblank'
        refine ⟨Literal.pos
          (cellVar 0 (T + pref.length + i + 1) (letterIdx blank)), by
            simp [implyPos], ?_⟩
        have hnext := hstdCell (T + pref.length + i + 1) hpNext
        have hEq'' : initSymbol input
            (idxToPos T (T + pref.length + i + 1)) = a' := by
          simpa only [Nat.add_assoc] using hEq'
        rw [hEq'', hblank'] at hnext
        simpa [Literal.eval] using hnext
      · refine ⟨Literal.pos
          (cellVar 0 (T + pref.length + i + 1) (letterIdx blank)), by
            simp [implyPos], ?_⟩
        have hnext := hstdCell (T + pref.length + i + 1) hpNext
        rw [htail (T + pref.length + i + 1) (by omega)] at hnext
        simpa [Literal.eval] using hnext

/-- `machineOutputs_of_prefixInitClauses_sat` generalized past the tight window: any
`W ≥ windowSize ...` still lets a satisfying assignment of the custom
prefix/free-suffix initial clauses be reassembled into a real run. -/
lemma machineOutputs_of_prefixInitClauses_at_window_sat
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ}
    {pref suffix output : List Γ} {freeLen W T : ℕ} {allowed : List Γ}
    {τ : Literal.Assignment}
    (hS : Supports M ↑S)
    (hW : windowSize (pref ++ suffix).length output.length T ≤ W)
    (hsuffixLen : suffix.length = freeLen)
    (hτ : ∀ c ∈ (tableauMachineWithInitAtWindow M S (pref ++ suffix) output T W
      (prefixInitClauses S pref freeLen allowed W T)).clauses,
      c.Satisfied τ)
    (hfree : ∀ i, i < freeLen →
        τ (cellVar 0 (T + pref.length + i)
          (letterIdx (suffix.getI i))) = true) :
    MachineOutputsInTime M (pref ++ suffix) output T := by
  have hcustom : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    tauto
  have hstdInit :=
    prefixInitClauses_satisfied_implies_initClauses hsuffixLen hcustom hfree
  have hτ_unique : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    tauto
  have hτ_trans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    tauto
  have hτ_persist : ∀ c ∈ persistClauses (Γ := Γ) W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    tauto
  have hτ_accept : ∀ c ∈ acceptClauses M S output W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInitAtWindow, List.mem_append]
    tauto
  have hstdSat : SAT (tableauMachineAtWindow M S (pref ++ suffix) output T W) := by
    refine ⟨τ, ?_⟩
    intro c hc
    simp only [tableauMachineAtWindow, tableauMachineWithInitAtWindow,
      List.mem_append] at hc
    aesop
  exact (tableauMachineAtWindow_sat_iff M S (pref ++ suffix) output T W hS hW).mp hstdSat

end NPComplete.CookLevin

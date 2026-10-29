module

public import NPComplete.CookLevin.Machines.TM2to1.Package
public import Mathlib.Computability.StateTransition

/-!
The packaged machine must compute the same function as the source `FinTM2`.
Every reachable stack symbol is in `usedSymbols`, so wrapping through the
subtype does not change the transition.
-/

@[expose] public section

namespace NPComplete.CookLevin.TM2to1

open Turing TM2 StateTransition
open Function (update update_self update_of_ne)

lemma usedSymbols_k₀ (tm : FinTM2) : usedSymbols tm tm.k₀ = Set.univ := by
  ext x
  simp [usedSymbols]

lemma mem_usedSymbols_k₀ (tm : FinTM2) (x : tm.Γ tm.k₀) :
    x ∈ usedSymbols tm tm.k₀ := by
  simp [usedSymbols_k₀]

def packList (tm : FinTM2) (k : tm.K) :
    (l : List (tm.Γ k)) → (∀ x ∈ l, x ∈ usedSymbols tm k) → List (PackΓ tm k)
  | [], _ => []
  | x :: xs, h =>
      ⟨x, h x List.mem_cons_self⟩ ::
        packList tm k xs fun y hy => h y (List.mem_cons_of_mem x hy)

def unpackList {tm : FinTM2} {k : tm.K} : List (PackΓ tm k) → List (tm.Γ k)
  | [] => []
  | x :: xs => x.val :: unpackList xs

def StacksUsed (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) : Prop :=
  ∀ k, ∀ x ∈ S k, x ∈ usedSymbols tm k

def packStacks (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) (h : StacksUsed tm S) :
    ∀ k, List (PackΓ tm k) :=
  fun k => packList tm k (S k) (h k)

lemma packStacks_congr (tm : FinTM2) {S₁ S₂ : ∀ k, List (tm.Γ k)} (e : S₁ = S₂)
    (h₁ : StacksUsed tm S₁) (h₂ : StacksUsed tm S₂) :
    packStacks tm S₁ h₁ = packStacks tm S₂ h₂ := by
  subst e
  rfl

lemma stacksUsed_update_push (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (hS : StacksUsed tm S) (k : tm.K) (x : tm.Γ k)
    (hx : x ∈ usedSymbols tm k) :
    StacksUsed tm (update S k (x :: S k)) := by
  intro k' y hy
  by_cases hk : k' = k
  · subst hk
    have hy' : y = x ∨ y ∈ S k' := by
      have : y ∈ x :: S k' := by simpa [update_self] using hy
      simpa [List.mem_cons] using this
    rcases hy' with rfl | hy'
    · exact hx
    · exact hS k' y hy'
  · have : y ∈ S k' := by simpa [update_of_ne hk] using hy
    exact hS k' y this

lemma stacksUsed_update_tail (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (hS : StacksUsed tm S) (k : tm.K) :
    StacksUsed tm (update S k (S k).tail) := by
  intro k' y hy
  by_cases hk : k' = k
  · subst hk
    have : y ∈ (S k').tail := by simpa [update_self] using hy
    exact hS k' y (List.mem_of_mem_tail this)
  · have : y ∈ S k' := by simpa [update_of_ne hk] using hy
    exact hS k' y this

lemma packList_head (tm : FinTM2) (k : tm.K)
    (l : List (tm.Γ k)) (h : ∀ x ∈ l, x ∈ usedSymbols tm k) :
    (packList tm k l h).head?.map Subtype.val = l.head? := by
  cases l <;> rfl

lemma packList_tail (tm : FinTM2) (k : tm.K)
    (l : List (tm.Γ k)) (h : ∀ x ∈ l, x ∈ usedSymbols tm k)
    (ht : ∀ x ∈ l.tail, x ∈ usedSymbols tm k) :
    packList tm k l.tail ht = (packList tm k l h).tail := by
  cases l <;> rfl

lemma packStacks_update_push (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (hS : StacksUsed tm S) (k : tm.K) (x : tm.Γ k)
    (hx : x ∈ usedSymbols tm k) :
    packStacks tm (update S k (x :: S k)) (stacksUsed_update_push tm S hS k x hx) =
      update (packStacks tm S hS) k (⟨x, hx⟩ :: packStacks tm S hS k) := by
  funext k'
  by_cases hk : k' = k
  · subst hk
    simp only [packStacks, update_self, packList]
  · simp only [packStacks, update_of_ne hk]

lemma packStacks_update_tail (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (hS : StacksUsed tm S) (k : tm.K) :
    packStacks tm (update S k (S k).tail) (stacksUsed_update_tail tm S hS k) =
      update (packStacks tm S hS) k (packStacks tm S hS k).tail := by
  funext k'
  by_cases hk : k' = k
  · subst hk
    simp only [packStacks, update_self]
    exact packList_tail tm k' (S k') (hS k') _
  · simp only [packStacks, update_of_ne hk]

lemma packStacks_head (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (hS : StacksUsed tm S) (k : tm.K) :
    (packStacks tm S hS k).head?.map Subtype.val = (S k).head? :=
  packList_head tm k (S k) (hS k)

lemma stacksUsed_stepAux (tm : FinTM2)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : ∀ k, stmtPushRange k q ⊆ usedSymbols tm k)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (hS : StacksUsed tm S) :
    StacksUsed tm (stepAux q v S).stk := by
  induction q generalizing v S hS with
  | push k f q ih =>
    exact ih (fun k' => (stmtPushRange_push_subset k' k f q).trans (hq k'))
      v _ (stacksUsed_update_push tm S hS k (f v) (hq k (push_mem_stmtPushRange k f q v)))
  | peek k f q ih =>
    exact ih (fun k' => (stmtPushRange_peek_eq k' k f q).symm ▸ hq k') (f v (S k).head?) S hS
  | pop k f q ih =>
    exact ih (fun k' => (stmtPushRange_pop_eq k' k f q).symm ▸ hq k')
      (f v (S k).head?) _ (stacksUsed_update_tail tm S hS k)
  | load a q ih =>
    exact ih (fun k' => (stmtPushRange_load_eq k' a q).symm ▸ hq k') (a v) S hS
  | branch p q₁ q₂ ih₁ ih₂ =>
    cases hp : p v
    · simpa [stepAux, hp] using
        ih₂ (fun k' => (stmtPushRange_branch_right k' p q₁ q₂).trans (hq k')) v S hS
    · simpa [stepAux, hp] using
        ih₁ (fun k' => (stmtPushRange_branch_left k' p q₁ q₂).trans (hq k')) v S hS
  | goto f => simpa [stepAux] using hS
  | halt => simpa [stepAux] using hS


lemma packStmt_stepAux (tm : FinTM2)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : ∀ k, stmtPushRange k q ⊆ usedSymbols tm k)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (hS : StacksUsed tm S) :
    stepAux (packStmt tm q hq) v (packStacks tm S hS) =
      { l := (stepAux q v S).l
        var := (stepAux q v S).var
        stk := packStacks tm (stepAux q v S).stk (stacksUsed_stepAux tm q hq v S hS) } := by
  induction q generalizing v S hS with
  | push k f q ih =>
    have hx : f v ∈ usedSymbols tm k := hq k (push_mem_stmtPushRange k f q v)
    have hq' : ∀ k', stmtPushRange k' q ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_push_subset k' k f q).trans (hq k')
    have hS' := stacksUsed_update_push tm S hS k (f v) hx
    simp only [packStmt, stepAux]
    convert ih hq' v (update S k (f v :: S k)) hS'
    exact (packStacks_update_push tm S hS k (f v) hx).symm
  | peek k f q ih =>
    have hq' : ∀ k', stmtPushRange k' q ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_peek_eq k' k f q).symm ▸ hq k'
    simp only [packStmt, stepAux]
    convert ih hq' (f v (S k).head?) S hS
    exact packStacks_head tm S hS k
  | pop k f q ih =>
    have hq' : ∀ k', stmtPushRange k' q ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_pop_eq k' k f q).symm ▸ hq k'
    have hS' := stacksUsed_update_tail tm S hS k
    simp only [packStmt, stepAux]
    convert ih hq' (f v (S k).head?) (update S k (S k).tail) hS' using 2
    · exact congrArg (f v) (packStacks_head tm S hS k)
    · exact (packStacks_update_tail tm S hS k).symm
  | load a q ih =>
    have hq' : ∀ k', stmtPushRange k' q ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_load_eq k' a q).symm ▸ hq k'
    simp only [packStmt, stepAux]
    exact ih hq' (a v) S hS
  | branch p q₁ q₂ ih₁ ih₂ =>
    have hq₁ : ∀ k', stmtPushRange k' q₁ ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_branch_left k' p q₁ q₂).trans (hq k')
    have hq₂ : ∀ k', stmtPushRange k' q₂ ⊆ usedSymbols tm k' :=
      fun k' => (stmtPushRange_branch_right k' p q₁ q₂).trans (hq k')
    cases hp : p v
    · simp only [packStmt, stepAux, hp, Bool.cond_false]
      convert ih₂ hq₂ v S hS
      exact packStacks_congr tm (by simp [hp]) _ _
    · simp only [packStmt, stepAux, hp, Bool.cond_true]
      convert ih₁ hq₁ v S hS
      exact packStacks_congr tm (by simp [hp]) _ _
  | goto f =>
    simp [packStmt, stepAux]
  | halt =>
    simp [packStmt, stepAux]

lemma packFinTM2_k₀ (tm : FinTM2) : (packFinTM2 tm).k₀ = tm.k₀ :=
  rfl

lemma packFinTM2_k₁ (tm : FinTM2) : (packFinTM2 tm).k₁ = tm.k₁ :=
  rfl

lemma stacksUsed_initList (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    StacksUsed tm (initList tm l).stk := by
  intro k x hx
  by_cases hk : k = tm.k₀
  · subst hk
    simp [initList] at hx
    exact mem_usedSymbols_k₀ tm x
  · simp [initList, hk] at hx

lemma stacksUsed_haltList (tm : FinTM2) (l : List (tm.Γ tm.k₁))
    (hl : ∀ x ∈ l, x ∈ usedSymbols tm tm.k₁) :
    StacksUsed tm (haltList tm l).stk := by
  intro k x hx
  by_cases hk : k = tm.k₁
  · subst hk
    simp [haltList] at hx
    exact hl x hx
  · simp [haltList, hk] at hx

lemma flip_bind_none {α : Type*} (f : α → Option α) :
    flip bind f none = none :=
  rfl

lemma flip_bind_iterate_none {α : Type*} (f : α → Option α) (t : ℕ) :
    (flip bind f)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ, Function.comp_apply, flip_bind_none, ih]

lemma flip_bind_step (tm : FinTM2) (c : tm.Cfg) :
    flip bind tm.step (some c) = tm.step c :=
  rfl

lemma stacksUsed_of_bind_iterate (tm : FinTM2) (c c' : tm.Cfg) (t : ℕ)
    (hS : StacksUsed tm c.stk)
    (h : (flip bind tm.step)^[t] (some c) = some c') :
    StacksUsed tm c'.stk := by
  induction t generalizing c hS with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst c'
    exact hS
  | succ t ih =>
    rw [Function.iterate_succ, Function.comp_apply, flip_bind_step] at h
    cases hc : tm.step c with
    | none =>
      rw [hc] at h
      rw [flip_bind_iterate_none] at h
      cases h
    | some c₁ =>
      rw [hc] at h
      refine ih c₁ ?_ h
      rcases c with ⟨l?, v, S⟩
      cases l? with
      | none =>
        simp [FinTM2.step, TM2.step] at hc
      | some l =>
        simp [FinTM2.step, TM2.step] at hc
        cases hc
        exact stacksUsed_stepAux tm (tm.m l) (usedSymbols_covers tm l) v S hS

lemma mem_usedSymbols_of_haltList (tm : FinTM2)
    {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm l (some l') m) :
    ∀ x ∈ l', x ∈ usedSymbols tm tm.k₁ := by
  intro x hx
  have hreach : (flip bind tm.step)^[h.steps] (some (initList tm l)) =
      some (haltList tm l') := h.evals_in_steps
  have hS := stacksUsed_of_bind_iterate tm (initList tm l) (haltList tm l')
    h.steps (stacksUsed_initList tm l) hreach
  have : x ∈ (haltList tm l').stk tm.k₁ := by
    simpa [haltList] using hx
  exact hS tm.k₁ x this

lemma mem_usedSymbols_of_list_k₀ (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    ∀ x ∈ l, x ∈ usedSymbols tm tm.k₀ :=
  fun x _ => mem_usedSymbols_k₀ tm x

def packCfg (tm : FinTM2) (c : tm.Cfg) (hS : StacksUsed tm c.stk) :
    (packFinTM2 tm).Cfg :=
  ⟨c.l, c.var, packStacks tm c.stk hS⟩

lemma packList_nil (tm : FinTM2) (k : tm.K)
    (h : ∀ x ∈ ([] : List (tm.Γ k)), x ∈ usedSymbols tm k) :
    packList tm k [] h = [] :=
  rfl

lemma packed_cfg_eq (tm : FinTM2) {c₁ c₂ : (packFinTM2 tm).Cfg}
    (h1 : c₁.l = c₂.l) (h2 : c₁.var = c₂.var) (h3 : c₁.stk = c₂.stk) :
    c₁ = c₂ := by
  cases c₁; cases c₂
  simp at *
  subst h1; subst h2; subst h3
  rfl

lemma pack_initList_stk (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (k : tm.K) :
    packStacks tm (initList tm l).stk (stacksUsed_initList tm l) k =
      (initList (packFinTM2 tm)
        (packList tm tm.k₀ l (mem_usedSymbols_of_list_k₀ tm l))).stk k := by
  simp only [packStacks]
  by_cases hk : k = tm.k₀
  · subst hk
    simp only [initList, dite_true]
    split
    · rfl
    · exact absurd rfl ‹_›
  · have hk' : k ≠ (packFinTM2 tm).k₀ := by simpa [packFinTM2_k₀] using hk
    have hL : packList tm k ((initList tm l).stk k) (stacksUsed_initList tm l k) = [] := by
      convert packList_nil tm k (fun x hx => nomatch hx)
      simp [initList, dite_eq_right hk]
    have hR :
        (initList (packFinTM2 tm)
          (packList tm tm.k₀ l (mem_usedSymbols_of_list_k₀ tm l))).stk k = [] := by
      have : (initList (packFinTM2 tm)
          (packList tm tm.k₀ l (mem_usedSymbols_of_list_k₀ tm l))).stk k = [] := by
        unfold initList
        exact dite_eq_right hk'
      exact this
    exact hL.trans hR.symm

lemma pack_haltList_stk (tm : FinTM2) (l : List (tm.Γ tm.k₁))
    (hl : ∀ x ∈ l, x ∈ usedSymbols tm tm.k₁) (k : tm.K) :
    packStacks tm (haltList tm l).stk (stacksUsed_haltList tm l hl) k =
      (haltList (packFinTM2 tm) (packList tm tm.k₁ l hl)).stk k := by
  simp only [packStacks]
  by_cases hk : k = tm.k₁
  · subst hk
    simp only [haltList, dite_true]
    split
    · rfl
    · exact absurd rfl ‹_›
  · have hk' : k ≠ (packFinTM2 tm).k₁ := by simpa [packFinTM2_k₁] using hk
    have hL : packList tm k ((haltList tm l).stk k) (stacksUsed_haltList tm l hl k) = [] := by
      convert packList_nil tm k (fun x hx => nomatch hx)
      simp [haltList, dite_eq_right hk]
    have hR : (haltList (packFinTM2 tm) (packList tm tm.k₁ l hl)).stk k = [] := by
      have : (haltList (packFinTM2 tm) (packList tm tm.k₁ l hl)).stk k = [] := by
        unfold haltList
        exact dite_eq_right hk'
      exact this
    exact hL.trans hR.symm

lemma pack_initList (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    packCfg tm (initList tm l) (stacksUsed_initList tm l) =
      initList (packFinTM2 tm)
        (packList tm tm.k₀ l (mem_usedSymbols_of_list_k₀ tm l)) := by
  refine packed_cfg_eq tm ?_ ?_ ?_
  · simp [packCfg, initList, packFinTM2]
  · simp [packCfg, initList, packFinTM2]
  · funext k; exact pack_initList_stk tm l k

lemma pack_haltList (tm : FinTM2) (l : List (tm.Γ tm.k₁))
    (hl : ∀ x ∈ l, x ∈ usedSymbols tm tm.k₁) :
    packCfg tm (haltList tm l) (stacksUsed_haltList tm l hl) =
      haltList (packFinTM2 tm) (packList tm tm.k₁ l hl) := by
  refine packed_cfg_eq tm ?_ ?_ ?_
  · rfl
  · simp [packCfg, haltList, packFinTM2]
  · funext k; exact pack_haltList_stk tm l hl k

lemma pack_step_some (tm : FinTM2) (c c' : tm.Cfg) (hS : StacksUsed tm c.stk)
    (h : tm.step c = some c') :
    (packFinTM2 tm).step (packCfg tm c hS) =
      some (packCfg tm c' (by
        rcases c with ⟨l?, v, S⟩
        cases l? with
        | none => simp [FinTM2.step, TM2.step] at h
        | some l =>
          simp [FinTM2.step, TM2.step] at h
          cases h
          exact stacksUsed_stepAux tm (tm.m l) (usedSymbols_covers tm l) v S hS)) := by
  rcases c with ⟨l?, v, S⟩
  cases l? with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    simp [FinTM2.step, TM2.step] at h
    cases h
    simp [packCfg, FinTM2.step, TM2.step, packFinTM2]
    congr 1
    exact packStmt_stepAux tm (tm.m l) (usedSymbols_covers tm l) v S hS

lemma pack_bind_iterate (tm : FinTM2) (c c' : tm.Cfg) (t : ℕ)
    (hS : StacksUsed tm c.stk)
    (h : (flip bind tm.step)^[t] (some c) = some c') :
    (flip bind (packFinTM2 tm).step)^[t] (some (packCfg tm c hS)) =
      some (packCfg tm c' (stacksUsed_of_bind_iterate tm c c' t hS h)) := by
  induction t generalizing c hS with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst c'
    rfl
  | succ t ih =>
    rw [Function.iterate_succ, Function.comp_apply, flip_bind_step] at h
    cases hc : tm.step c with
    | none =>
      rw [hc, flip_bind_iterate_none] at h
      cases h
    | some c₁ =>
      rw [hc] at h
      have hstep := pack_step_some tm c c₁ hS hc
      rw [Function.iterate_succ, Function.comp_apply]
      change (flip bind (packFinTM2 tm).step)^[t]
          ((packFinTM2 tm).step (packCfg tm c hS)) = _
      rw [hstep]
      exact ih c₁ _ h

noncomputable def packFinTM2_outputsInTime (tm : FinTM2)
    {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm l (some l') m) :
    TM2OutputsInTime (packFinTM2 tm)
      (packList tm tm.k₀ l (mem_usedSymbols_of_list_k₀ tm l))
      (some (packList tm tm.k₁ l' (mem_usedSymbols_of_haltList tm h))) m where
  steps := h.steps
  evals_in_steps := by
    have hreach := h.evals_in_steps
    have hp := pack_bind_iterate tm (initList tm l) (haltList tm l') h.steps
      (stacksUsed_initList tm l) hreach
    rw [pack_initList] at hp
    convert hp
    exact congrArg some (pack_haltList tm l' (mem_usedSymbols_of_haltList tm h)).symm
  steps_le_m := h.steps_le_m

end NPComplete.CookLevin.TM2to1

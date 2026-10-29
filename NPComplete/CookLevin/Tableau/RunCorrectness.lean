module

public import NPComplete.CookLevin.Tableau.RunSnapshot

/-!
# Run assignment correctness

Each concrete configuration must yield a well-formed row of Boolean selectors, and satisfied
clauses must recover those selectors' meanings. This module establishes the per-time assignment
facts that the global SAT-run argument composes.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Local correctness -/

lemma runCfg_zero [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) : runCfg M input 0 = init input :=
  rfl

lemma runHead_zero [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) : runHead M input 0 = 0 :=
  rfl

lemma runCfg_state_mem [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {S : Finset Λ} (hS : Supports M ↑S) (input : List Γ) :
    ∀ t, (runCfg M input t).q ∈ S
  | 0 => by
      simpa [runCfg, init] using hS.1
  | t + 1 => by
      have hq := runCfg_state_mem hS input t
      simp only [runCfg, stepOrStay]
      cases hstep : step M (runCfg M input t) with
      | none => exact hq
      | some c' =>
          have hmem : c' ∈ step M (runCfg M input t) := by simp [hstep]
          exact step_supports M hS hmem hq

lemma mem_range_succ {n T : ℕ} (h : n ≤ T) : n ∈ List.range (T + 1) :=
  List.mem_range.mpr (Nat.lt_succ_of_le h)

lemma runAssign_state [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t : ℕ} (ht : t ≤ T) (hq : (runCfg M input t).q ∈ S) :
    runAssign M S input output T
        (stateVar t (stateIdx S (runCfg M input t).q)) = true := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inl ⟨(runCfg M input t).q, ?_, ?_⟩⟩
  · exact Finset.mem_toList.mpr hq
  · exact ⟨rfl, rfl⟩

lemma runAssign_head [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} (ht : t ≤ T)
    (hp : p < windowSize input.length output.length T)
    (hhd : runHead M input t = idxToPos T p) :
    runAssign M S input output T (headVar t p) = true := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inr ⟨p, List.mem_range.mpr hp, Or.inl ⟨rfl, hhd⟩⟩⟩

lemma runAssign_cell [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} {a : Γ} (ht : t ≤ T)
    (hp : p < windowSize input.length output.length T)
    (ha : absNth (runCfg M input t) (runHead M input t) (idxToPos T p) = a) :
    runAssign M S input output T (cellVar t p (letterIdx a)) = true := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨t, mem_range_succ ht, Or.inr ⟨p, List.mem_range.mpr hp, Or.inr ?_⟩⟩
  exact ⟨a, mem_letters a, ⟨rfl, ha⟩⟩

lemma mem_of_idxOf_eq [DecidableEq α] {l : List α} {x y : α}
    (hy : y ∈ l) (h : l.idxOf x = l.idxOf y) : x ∈ l := by
  by_contra hx
  have hxlen : l.idxOf x = l.length := List.idxOf_of_notMem hx
  have hylt : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
  omega

lemma runAssign_state_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T t : ℕ} {q : Λ}
    (h : runAssign M S input output T (stateVar t (stateIdx S q)) = true) :
    t ≤ T ∧ q ∈ S ∧ (runCfg M input t).q = q := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨t', ht', hcase⟩ := h
  have ht'le : t' ≤ T := Nat.lt_succ_iff.mp (List.mem_range.mp ht')
  rcases hcase with hst | hrest
  · obtain ⟨q', hq', hv, hqeq⟩ := hst
    obtain ⟨rfl, hidx⟩ := stateVar_eq_iff.mp hv
    have hq : q ∈ S :=
      Finset.mem_toList.mp (mem_of_idxOf_eq hq' hidx)
    exact ⟨ht'le, hq,
      hqeq.trans (stateIdx_inj (Finset.mem_toList.mp hq') hq hidx.symm)⟩
  · rcases hrest with ⟨p, _, hhp | hcell⟩
    · exact (stateVar_ne_headVar _ _ _ _ hhp.1).elim
    · obtain ⟨_, _, hv, _⟩ := hcell
      exact (cellVar_ne_stateVar _ _ _ _ _ hv.symm).elim

lemma runAssign_head_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T t p : ℕ}
    (h : runAssign M S input output T (headVar t p) = true) :
    t ≤ T ∧ runHead M input t = idxToPos T p := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
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

lemma runAssign_cell_inv [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T t p : ℕ} {a : Γ}
    (h : runAssign M S input output T (cellVar t p (letterIdx a)) = true) :
    t ≤ T ∧ absNth (runCfg M input t) (runHead M input t) (idxToPos T p) = a := by
  simp only [runAssign, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
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

lemma initClauses_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T : ℕ} (hS : Supports M ↑S) :
    ∀ c ∈ initClauses S input (windowSize input.length output.length T) T,
      c.Satisfied (runAssign M S input output T) := by
  intro c hc
  set W := windowSize input.length output.length T
  have hst : (initStateClause (Λ := Λ) S).Satisfied
      (runAssign M S input output T) := by
    have hdef : default ∈ S := hS.1
    simp only [initStateClause, hdef, ↓reduceIte]
    refine satisfied_unitPos ?_
    simpa [runCfg, init] using
      (runAssign_state (M := M) (S := S) (input := input) (output := output)
        (T := T) (t := 0) (Nat.zero_le _) (by simpa [runCfg, init] using hdef))
  have hhd : (unitPos (headVar 0 (originIdx T))).Satisfied
      (runAssign M S input output T) := by
    refine satisfied_unitPos ?_
    refine runAssign_head (ht := Nat.zero_le _) (hp := originIdx_lt_window _ _ _) ?_
    simp [runHead, originIdx, idxToPos]
  have hcell : ∀ p, p < W →
      (unitPos (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p))))).Satisfied
        (runAssign M S input output T) := by
    intro p hp
    refine satisfied_unitPos ?_
    refine runAssign_cell (ht := Nat.zero_le _) (hp := hp) ?_
    simp [absNth, runCfg, runHead, init, tape_mk₁_nth]
  simp [initClauses, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | rfl | ⟨p, hp, rfl⟩
  · exact hst
  · exact hhd
  · exact hcell p hp

lemma fixed_cell_of_prefixInitClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {S : Finset Λ} {pref : List Γ}
    {freeLen W T p : ℕ} {allowed : List Γ} {τ : Literal.Assignment}
    (h : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ)
    (hp : p < W) (hfix : p < T + pref.length) :
    τ (cellVar 0 p (letterIdx (initSymbol pref (idxToPos T p)))) = true := by
  apply eval_unitPos
  apply h
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
  exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp, by simp [hfix]⟩

lemma blank_cell_of_prefixInitClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {S : Finset Λ} {pref : List Γ}
    {freeLen W T p : ℕ} {allowed : List Γ} {τ : Literal.Assignment}
    (h : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ)
    (hp : p < W) (hblank : T + pref.length + freeLen ≤ p) :
    τ (cellVar 0 p (letterIdx (default : Γ))) = true := by
  apply eval_unitPos
  apply h
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
  refine List.mem_map.mpr ⟨p, List.mem_range.mpr hp, ?_⟩
  have hfix : ¬ p < T + pref.length := by omega
  have hfree : ¬ p < T + pref.length + freeLen := by omega
  simp [hfix, hfree]

lemma initSymbol_of_initClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {S : Finset Λ} {input : List Γ} {W T : ℕ}
    {τ : Literal.Assignment}
    (h : ∀ c ∈ initClauses S input W T, c.Satisfied τ)
    {p : ℕ} (hp : p < W) :
    τ (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p)))) = true := by
  apply eval_unitPos
  apply h
  simp [initClauses, List.mem_map, List.mem_range]
  exact Or.inr (Or.inr ⟨p, hp, rfl⟩)

lemma head_of_initClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {S : Finset Λ} {input : List Γ} {W T : ℕ}
    {τ : Literal.Assignment}
    (h : ∀ c ∈ initClauses S input W T, c.Satisfied τ) :
    τ (headVar 0 (originIdx T)) = true := by
  apply eval_unitPos
  apply h
  simp [initClauses]

lemma state_of_initClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] {S : Finset Λ} {input : List Γ} {W T : ℕ}
    {τ : Literal.Assignment} (hdef : default ∈ S)
    (h : ∀ c ∈ initClauses S input W T, c.Satisfied τ) :
    τ (stateVar 0 (stateIdx S default)) = true := by
  apply eval_unitPos
  have hc := h (initStateClause S) (by simp [initClauses])
  simpa [initStateClause, hdef] using hc

lemma atMostOne_state_of_sat [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ]
    {S : Finset Λ} {W T t : ℕ} {τ : Literal.Assignment} {q₁ q₂ : Λ}
    (ht : t ≤ T)
    (hsat : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (h₁ : q₁ ∈ S) (h₂ : q₂ ∈ S)
    (hτ₁ : τ (stateVar t (stateIdx S q₁)) = true)
    (hτ₂ : τ (stateVar t (stateIdx S q₂)) = true) :
    q₁ = q₂ := by
  have hexact :
      ∀ c ∈ exactlyOne (S.toList.map fun q => stateVar t (stateIdx S q)),
        c.Satisfied τ := by
    intro c hc
    apply hsat
    refine List.mem_flatMap.mpr ⟨t, mem_range_succ ht, ?_⟩
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl hc)))
  have hv₁ : stateVar t (stateIdx S q₁) ∈
      S.toList.map fun q => stateVar t (stateIdx S q) :=
    List.mem_map.mpr ⟨q₁, Finset.mem_toList.mpr h₁, rfl⟩
  have hv₂ : stateVar t (stateIdx S q₂) ∈
      S.toList.map fun q => stateVar t (stateIdx S q) :=
    List.mem_map.mpr ⟨q₂, Finset.mem_toList.mpr h₂, rfl⟩
  have hv :=
    atMostOne_unique τ (S.toList.map fun q => stateVar t (stateIdx S q))
      (fun c hc => hexact c (List.mem_cons.mpr (Or.inr hc)))
      _ _ hv₁ hv₂ hτ₁ hτ₂
  have hidx : stateIdx S q₁ = stateIdx S q₂ := (stateVar_eq_iff.mp hv).2
  exact stateIdx_inj h₁ h₂ hidx

lemma atMostOne_cell_of_sat [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ]
    {S : Finset Λ} {W T t p : ℕ} {τ : Literal.Assignment} {a₁ a₂ : Γ}
    (ht : t ≤ T)
    (hsat : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hp : p < W)
    (hτ₁ : τ (cellVar t p (letterIdx a₁)) = true)
    (hτ₂ : τ (cellVar t p (letterIdx a₂)) = true) :
    a₁ = a₂ := by
  have hexact :
      ∀ c ∈ exactlyOne ((letters Γ).map fun a => cellVar t p (letterIdx a)),
        c.Satisfied τ := by
    intro c hc
    apply hsat
    simp only [uniquenessClauses, List.mem_flatMap]
    refine ⟨t, mem_range_succ ht, List.mem_append.mpr (Or.inr ?_)⟩
    exact List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, hc⟩
  have hv₁ : cellVar t p (letterIdx a₁) ∈
      (letters Γ).map fun a => cellVar t p (letterIdx a) :=
    List.mem_map.mpr ⟨a₁, mem_letters a₁, rfl⟩
  have hv₂ : cellVar t p (letterIdx a₂) ∈
      (letters Γ).map fun a => cellVar t p (letterIdx a) :=
    List.mem_map.mpr ⟨a₂, mem_letters a₂, rfl⟩
  have hv := atMostOne_unique τ ((letters Γ).map fun a => cellVar t p (letterIdx a))
    (fun c hc => hexact c (List.mem_cons.mpr (Or.inr hc))) _ _ hv₁ hv₂ hτ₁ hτ₂
  exact letterIdx_inj (cellVar_eq_iff.mp hv).2.2

end NPComplete.CookLevin

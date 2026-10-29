module

public import NPComplete.CookLevin.Generate.VarMapBridge

/-!
# SAT under executable variable maps

An executable compiler's compact indices need not match the generic tableau
indices. This module proves injectivity on used variables and transports
assignments, so satisfiability can be compared without conflating the encodings.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

def ExecEncodableVar (v : ℕ) : Prop :=
  (∃ t q, v = stateVar t q) ∨
    (∃ t p, v = headVar t p) ∨
      ∃ t p a, v = cellVar t p a

lemma execVarMap_injective_encodable {u v : ℕ}
    (hu : ExecEncodableVar u) (hv : ExecEncodableVar v)
    (h : execVarMap u = execVarMap v) : u = v := by
  rcases hu with hu | hu
  · rcases hu with ⟨t, q, rfl⟩
    rcases hv with hv | hv
    · rcases hv with ⟨t', q', rfl⟩
      apply stateVar_eq_iff.mpr
      have h' : execCompactLayout.state t q =
          execCompactLayout.state t' q' := by
        simpa only [execVarMap_state] using h
      have hp : (t, q) = (t', q') := by
        apply execCompactLayout_state_injective
        change execCompactLayout.state t q = execCompactLayout.state t' q'
        exact h'
      exact Prod.ext_iff.mp hp
    · rcases hv with hv | hv
      · rcases hv with ⟨t', p', rfl⟩
        have h' : execCompactLayout.state t q =
            execCompactLayout.head t' p' := by
          simpa only [execVarMap_state, execVarMap_head] using h
        exact (execCompactLayout_state_ne_head t q t' p' h').elim
      · rcases hv with ⟨t', p', a', rfl⟩
        have h' : execCompactLayout.state t q =
            execCompactLayout.cell t' p' a' := by
          simpa only [execVarMap_state, execVarMap_cell] using h
        exact (execCompactLayout_cell_ne_state t' p' a' t q h'.symm).elim
  · rcases hu with hu | hu
    · rcases hu with ⟨t, p, rfl⟩
      rcases hv with hv | hv
      · rcases hv with ⟨t', q', rfl⟩
        have h' : execCompactLayout.head t p =
            execCompactLayout.state t' q' := by
          simpa only [execVarMap_head, execVarMap_state] using h
        exact (execCompactLayout_state_ne_head t' q' t p h'.symm).elim
      · rcases hv with hv | hv
        · rcases hv with ⟨t', p', rfl⟩
          apply headVar_eq_iff.mpr
          have h' : execCompactLayout.head t p =
              execCompactLayout.head t' p' := by
            simpa only [execVarMap_head] using h
          have hp : (t, p) = (t', p') := by
            apply execCompactLayout_head_injective
            change execCompactLayout.head t p = execCompactLayout.head t' p'
            exact h'
          exact Prod.ext_iff.mp hp
        · rcases hv with ⟨t', p', a', rfl⟩
          have h' : execCompactLayout.head t p =
              execCompactLayout.cell t' p' a' := by
            simpa only [execVarMap_head, execVarMap_cell] using h
          exact (execCompactLayout_cell_ne_head t' p' a' t p h'.symm).elim
    · rcases hu with ⟨t, p, a, rfl⟩
      rcases hv with hv | hv
      · rcases hv with ⟨t', q', rfl⟩
        have h' : execCompactLayout.cell t p a =
            execCompactLayout.state t' q' := by
          simpa only [execVarMap_cell, execVarMap_state] using h
        exact (execCompactLayout_cell_ne_state t p a t' q' h').elim
      · rcases hv with hv | hv
        · rcases hv with ⟨t', p', rfl⟩
          have h' : execCompactLayout.cell t p a =
              execCompactLayout.head t' p' := by
            simpa only [execVarMap_cell, execVarMap_head] using h
          exact (execCompactLayout_cell_ne_head t p a t' p' h').elim
        · rcases hv with ⟨t', p', a', rfl⟩
          apply cellVar_eq_iff.mpr
          have h' : execCompactLayout.cell t p a =
              execCompactLayout.cell t' p' a' := by
            simpa only [execVarMap_cell] using h
          have hp : (t, p, a) = (t', p', a') := by
            apply execCompactLayout_cell_injective
            change execCompactLayout.cell t p a =
              execCompactLayout.cell t' p' a'
            exact h'
          rcases Prod.ext_iff.mp hp with ⟨ht, hpa⟩
          exact ⟨ht, Prod.ext_iff.mp hpa⟩

def execMapCNF (m : ℕ → ℕ) (φ : CNF) : CNF :=
  ⟨execMapClauses m φ.clauses⟩

noncomputable def execPushAssignment (φ : CNF) (m : ℕ → ℕ)
    (τ : Literal.Assignment) : Literal.Assignment := fun n =>
  if h : ∃ v, v ∈ cnfUsedVars φ ∧ m v = n then
    τ (Classical.choose h)
  else false

lemma execPushAssignment_map (φ : CNF) (m : ℕ → ℕ)
    (τ : Literal.Assignment)
    (hinj : ∀ {u v}, u ∈ cnfUsedVars φ → v ∈ cnfUsedVars φ →
      m u = m v → u = v)
    {v : ℕ} (hv : v ∈ cnfUsedVars φ) :
    execPushAssignment φ m τ (m v) = τ v := by
  unfold execPushAssignment
  split
  · rename_i h
    have hc := Classical.choose_spec h
    have heq : Classical.choose h = v := hinj hc.1 hv hc.2
    simp [heq]
  · rename_i h
    exact False.elim (h ⟨v, hv, rfl⟩)

lemma execMapLiteral_eval_forward
    {φ : CNF} {c : Clause} {l : Literal} (m : ℕ → ℕ)
    (hc : c ∈ φ.clauses) (hl : l ∈ c.lits)
    (τ : Literal.Assignment)
    (hinj : ∀ {u v}, u ∈ cnfUsedVars φ → v ∈ cnfUsedVars φ →
      m u = m v → u = v) :
    (execMapLiteral m l).eval (execPushAssignment φ m τ) = l.eval τ := by
  have hv := cnfUsedVars_mem hc hl
  cases l with
  | pos v =>
      change v ∈ cnfUsedVars φ at hv
      simpa [execMapLiteral, Literal.eval] using
        (execPushAssignment_map φ m τ hinj hv)
  | neg v =>
      change v ∈ cnfUsedVars φ at hv
      have he := execPushAssignment_map φ m τ hinj hv
      simp only [execMapLiteral, Literal.eval]
      rw [he]

lemma execMapClause_sat_forward
    {φ : CNF} {c : Clause} (m : ℕ → ℕ)
    (hc : c ∈ φ.clauses) {τ : Literal.Assignment}
    (hτ : c.Satisfied τ)
    (hinj : ∀ {u v}, u ∈ cnfUsedVars φ → v ∈ cnfUsedVars φ →
      m u = m v → u = v) :
    (execMapClause m c).Satisfied (execPushAssignment φ m τ) := by
  obtain ⟨l, hl, hev⟩ := hτ
  refine ⟨execMapLiteral m l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  exact (execMapLiteral_eval_forward m hc hl τ hinj).trans hev

lemma execMapClause_sat_backward
    {c : Clause} (m : ℕ → ℕ)
    {τ : Literal.Assignment}
    (hτ : (execMapClause m c).Satisfied τ) :
    c.Satisfied (fun v => τ (m v)) := by
  obtain ⟨l, hl, hev⟩ := hτ
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp (by
    simpa [execMapClause] using hl)
  refine ⟨l', hl', ?_⟩
  cases l' <;> simpa [execMapLiteral, Literal.eval] using hev

lemma execMapCNF_sat_iff (φ : CNF) (m : ℕ → ℕ)
    (hinj : ∀ {u v}, u ∈ cnfUsedVars φ → v ∈ cnfUsedVars φ →
      m u = m v → u = v) :
    SAT (execMapCNF m φ) ↔ SAT φ := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => τ (m v), ?_⟩
    intro c hc
    have hc' : execMapClause m c ∈ (execMapCNF m φ).clauses := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact execMapClause_sat_backward m (hτ _ hc')
  · rintro ⟨τ, hτ⟩
    refine ⟨execPushAssignment φ m τ, ?_⟩
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact execMapClause_sat_forward m hd (hτ d hd) hinj

end NPComplete.CookLevin

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.SAT.ThreeSAT

/-!
A Cook-Levin tableau produces an unbounded-width CNF: local TM constraints
are not 3-clauses. The existing `ThreeCNF` type would force a SAT→3SAT
translation into this layer, which is a later reduction, not the tableau.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT (Literal)

/-- A disjunctive clause of unrestricted width. -/
@[stable_api] structure Clause where
  lits : List Literal
  deriving DecidableEq, Repr

attribute [stable_api] instDecidableEqClause instReprClause

@[stable_api] instance : Inhabited Clause := ⟨⟨[]⟩⟩

/-- A CNF formula is a list of clauses. -/
@[stable_api] structure CNF where
  clauses : List Clause
  deriving DecidableEq, Repr

attribute [stable_api] instDecidableEqCNF instReprCNF

namespace Clause

/-- The clause is true if some literal evaluates to `true`. -/
@[stable_api] def Satisfied (τ : Literal.Assignment) (c : Clause) : Prop :=
  ∃ l ∈ c.lits, l.eval τ = true

lemma satisfied_pos {τ : Literal.Assignment} {v : ℕ} (h : τ v = true) :
    Satisfied τ ⟨[Literal.pos v]⟩ :=
  ⟨Literal.pos v, List.mem_singleton.mpr rfl, h⟩

lemma satisfied_neg {τ : Literal.Assignment} {v : ℕ} (h : τ v = false) :
    Satisfied τ ⟨[Literal.neg v]⟩ :=
  ⟨Literal.neg v, List.mem_singleton.mpr rfl, by simp [Literal.eval, h]⟩

lemma not_satisfied_nil (τ : Literal.Assignment) : ¬ Satisfied τ ⟨[]⟩ := by
  rintro ⟨_, hmem, _⟩
  cases hmem

lemma satisfied_cons_of_left {τ : Literal.Assignment} {l : Literal} {ls : List Literal}
    (h : l.eval τ = true) : Satisfied τ ⟨l :: ls⟩ :=
  ⟨l, List.mem_cons.mpr (Or.inl rfl), h⟩

lemma satisfied_cons_of_right {τ : Literal.Assignment} {l : Literal} {ls : List Literal}
    (h : Satisfied τ ⟨ls⟩) : Satisfied τ ⟨l :: ls⟩ := by
  obtain ⟨l', hmem, he⟩ := h
  exact ⟨l', List.mem_cons.mpr (Or.inr hmem), he⟩

end Clause

/-- Concatenate two formulas. -/
@[stable_api] def CNF.append (φ ψ : CNF) : CNF :=
  ⟨φ.clauses ++ ψ.clauses⟩

/-- The formula is satisfiable. -/
@[stable_api] def SAT (φ : CNF) : Prop :=
  ∃ τ : Literal.Assignment, ∀ c ∈ φ.clauses, c.Satisfied τ

@[stable_api] lemma sat_nil : SAT ⟨[]⟩ :=
  ⟨fun _ => false, fun _ h => by cases h⟩

lemma sat_append {φ ψ : CNF} (h : SAT (φ.append ψ)) :
    SAT φ ∧ SAT ψ := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨⟨τ, fun c hc => hτ c (List.mem_append.mpr (Or.inl hc))⟩,
    ⟨τ, fun c hc => hτ c (List.mem_append.mpr (Or.inr hc))⟩⟩

@[stable_api] lemma sat_append_of {φ ψ : CNF} {τ : Literal.Assignment}
    (hφ : ∀ c ∈ φ.clauses, c.Satisfied τ)
    (hψ : ∀ c ∈ ψ.clauses, c.Satisfied τ) :
    SAT (φ.append ψ) :=
  ⟨τ, fun c hc =>
    match List.mem_append.mp hc with
    | Or.inl h => hφ c h
    | Or.inr h => hψ c h⟩

@[stable_api] lemma sat_of_append_left {φ ψ : CNF} (h : SAT (φ.append ψ)) : SAT φ :=
  (sat_append h).1

@[stable_api] lemma sat_of_append_right {φ ψ : CNF} (h : SAT (φ.append ψ)) : SAT ψ :=
  (sat_append h).2

end NPComplete.CookLevin

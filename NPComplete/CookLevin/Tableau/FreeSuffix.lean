module

public import NPComplete.CookLevin.Tableau.ClauseFamilies

/-!
# Free initial suffix

A finite initial prefix must not constrain tape cells beyond the chosen input when a tableau is
embedded in a bounded window. This module isolates the initial-clause form with a free suffix, so
the bounded tableau preserves the input while leaving the rest of the tape unconstrained.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Initial clauses with a free suffix -/

/-- Initial clauses with a fixed prefix and a bounded free suffix.

The cells before the prefix are blank, cells in the prefix are fixed, cells in
the suffix are restricted to `allowed`, and all remaining cells are blank. -/
noncomputable def prefixInitClauses [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (S : Finset Λ) (pref : List Γ)
    (freeLen : ℕ) (allowed : List Γ) (W T : ℕ) : List Clause :=
  initStateClause S ::
    unitPos (headVar 0 (originIdx T)) ::
      (List.range W).map fun p =>
        if p < T + pref.length then
          unitPos (cellVar 0 p (letterIdx (initSymbol pref (idxToPos T p))))
        else if p < T + pref.length + freeLen then
          atLeastOne (allowed.map fun a => cellVar 0 p (letterIdx a))
        else
          unitPos (cellVar 0 p (letterIdx (default : Γ)))

/-- Initial clauses with a bounded, blank-terminated free suffix.

The free cells may contain `blank` or one of the symbols in `allowed`.  The
implication clauses force the first blank to terminate the suffix. -/
noncomputable def boundedPrefixInitClauses [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ] (S : Finset Λ) (pref : List Γ)
    (freeLen : ℕ) (allowed : List Γ) (blank : Γ) (W T : ℕ) : List Clause :=
  (initStateClause S ::
      unitPos (headVar 0 (originIdx T)) ::
        (List.range W).map fun p =>
          if p < T + pref.length then
            unitPos (cellVar 0 p (letterIdx (initSymbol pref (idxToPos T p))))
          else if p < T + pref.length + freeLen then
            atLeastOne ((blank :: allowed).map fun a =>
              cellVar 0 p (letterIdx a))
          else
            unitPos (cellVar 0 p (letterIdx blank))) ++
    (List.range freeLen).map fun i =>
      implyPos
        (cellVar 0 (T + pref.length + i) (letterIdx blank))
        (cellVar 0 (T + pref.length + i + 1) (letterIdx blank))

lemma prefixInitClauses_mem_boundedPrefixInitClauses
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ]
    {S : Finset Λ} {pref : List Γ} {freeLen W T : ℕ}
    {allowed : List Γ} {blank : Γ} {c : Clause}
    (hblank : (default : Γ) = blank)
    (hc : c ∈ prefixInitClauses S pref freeLen (blank :: allowed) W T) :
    c ∈ boundedPrefixInitClauses S pref freeLen allowed blank W T := by
  simp only [prefixInitClauses, List.mem_cons] at hc
  rcases hc with rfl | hc
  · unfold boundedPrefixInitClauses
    exact List.mem_append.mpr (Or.inl List.mem_cons_self)
  rcases hc with rfl | hc
  · unfold boundedPrefixInitClauses
    exact List.mem_append.mpr
      (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self))
  rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
  have hpW : p < W := List.mem_range.mp hp
  unfold boundedPrefixInitClauses
  apply List.mem_append.mpr
  left
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨p, List.mem_range.mpr hpW, by
      by_cases hfix : p < T + pref.length
      · simp [hfix]
      · by_cases hfree : p < T + pref.length + freeLen
        · simp [hfix, hfree]
        · simp [hfix, hfree, hblank]⟩))

lemma eval_implyPos {τ : Literal.Assignment} {a b : ℕ}
    (h : (implyPos a b).Satisfied τ) (ha : τ a = true) : τ b = true := by
  obtain ⟨l, hl, hev⟩ := h
  simp [implyPos] at hl
  rcases hl with rfl | rfl
  · simp [Literal.eval, ha] at hev
  · exact hev

lemma eval_imply3 {τ : Literal.Assignment} {a b c d : ℕ}
    (h : (imply3 a b c d).Satisfied τ)
    (ha : τ a = true) (hb : τ b = true) (hc : τ c = true) : τ d = true := by
  obtain ⟨l, hl, hev⟩ := h
  simp [imply3] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · simp [Literal.eval, ha] at hev
  · simp [Literal.eval, hb] at hev
  · simp [Literal.eval, hc] at hev
  · exact hev

lemma eval_imply2 {τ : Literal.Assignment} {a b d : ℕ}
    (h : (imply2 a b d).Satisfied τ)
    (ha : τ a = true) (hb : τ b = true) : τ d = true := by
  obtain ⟨l, hl, hev⟩ := h
  simp [imply2] at hl
  rcases hl with rfl | rfl | rfl
  · simp [Literal.eval, ha] at hev
  · simp [Literal.eval, hb] at hev
  · exact hev

end NPComplete.CookLevin

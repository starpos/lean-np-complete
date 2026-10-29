module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableEmit
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowLayout

/-!
The generated CNF is the concatenation of five clause families, and the emitter
consumes a single table covering all of them.  Rather than teach the table
writer about the concatenation, this file fixes a contract for writing *one*
clause list into rows, and shows the contract composes: writing the second list
at the address where the first list's rows end yields the contract for the
concatenation.

That is what lets the producer run one routine per family, in sequence, with
each family's own loop nest, and still arrive at the single table the emitter
expects.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile (Store)
open NPComplete.SAT

def rowW (cs : List Clause) : ℕ → ℕ := fun k => (cs.getD k default).lits.length

def RowsWritten (σ : Store) (base : ℕ) (cs : List Clause) : Prop :=
  (∀ q, q < cs.length → σ (base + rowTableWidth (rowW cs) q + 1) = rowW cs q) ∧
  (∀ q, q < cs.length → ∀ i, i < rowW cs q →
      σ (base + rowTableWidth (rowW cs) q + 2 + 2 * i)
        = if litTag ((cs.getD q default).lits.getD i default) then 1 else 0) ∧
  (∀ q, q < cs.length → ∀ i, i < rowW cs q →
      σ (base + rowTableWidth (rowW cs) q + 2 + 2 * i + 1)
        = litVar ((cs.getD q default).lits.getD i default))

lemma rowW_append_left (cs ds : List Clause) (q : ℕ) (hq : q < cs.length) :
    rowW (cs ++ ds) q = rowW cs q := by
  unfold rowW; rw [List.getD_append cs ds default q hq]

lemma rowW_append_right (cs ds : List Clause) (j : ℕ) :
    rowW (cs ++ ds) (cs.length + j) = rowW ds j := by
  unfold rowW; rw [getD_append_shift]

lemma rowTableWidth_congr (f g : ℕ → ℕ) (q : ℕ) (h : ∀ i, i < q → f i = g i) :
    rowTableWidth f q = rowTableWidth g q := by
  unfold rowTableWidth; congr 1
  apply List.flatMap_congr; intro i hi; rw [h i (List.mem_range.mp hi)]

lemma rowTableWidth_app_left (cs ds : List Clause) (q : ℕ) (hq : q ≤ cs.length) :
    rowTableWidth (rowW (cs ++ ds)) q = rowTableWidth (rowW cs) q :=
  rowTableWidth_congr _ _ q (fun i hi => rowW_append_left cs ds i (by omega))

lemma rowTableWidth_app_shift (cs ds : List Clause) (j : ℕ) :
    rowTableWidth (rowW (cs ++ ds)) (cs.length + j)
      = rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j := by
  induction j with
  | zero => rw [Nat.add_zero, rowTableWidth_zero, Nat.add_zero]
            exact rowTableWidth_app_left cs ds cs.length le_rfl
  | succ j ih =>
      rw [show cs.length + (j+1) = (cs.length + j) + 1 by omega,
        rowTableWidth_succ, ih, rowTableWidth_succ, rowW_append_right]
      omega

lemma rowsWritten_append (σ : Store) (base : ℕ) (cs ds : List Clause)
    (hcs : RowsWritten σ base cs)
    (hds : RowsWritten σ (base + rowTableWidth (rowW cs) cs.length) ds) :
    RowsWritten σ base (cs ++ ds) := by
  obtain ⟨h1, h2, h3⟩ := hcs
  obtain ⟨g1, g2, g3⟩ := hds
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq
  · rcases Nat.lt_or_ge q cs.length with hlt | hge
    · rw [rowTableWidth_app_left cs ds q (le_of_lt hlt), rowW_append_left cs ds q hlt]
      exact h1 q hlt
    · obtain ⟨j, rfl⟩ : ∃ j, q = cs.length + j := ⟨q - cs.length, by omega⟩
      have hj : j < ds.length := by simp at hq; omega
      rw [rowTableWidth_app_shift, rowW_append_right]
      have := g1 j hj
      rw [show base + (rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j) + 1
        = base + rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j + 1 by omega]
      exact this
  · rcases Nat.lt_or_ge q cs.length with hlt | hge
    · rw [rowTableWidth_app_left cs ds q (le_of_lt hlt), List.getD_append cs ds default q hlt]
      rw [rowW_append_left cs ds q hlt]
      exact h2 q hlt
    · obtain ⟨j, rfl⟩ : ∃ j, q = cs.length + j := ⟨q - cs.length, by omega⟩
      have hj : j < ds.length := by simp at hq; omega
      rw [rowTableWidth_app_shift, getD_append_shift]
      rw [rowW_append_right]
      intro i hi
      have := g2 j hj i hi
      rw [show base + (rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j) + 2 + 2 * i
        = base + rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j + 2 + 2 * i by omega]
      exact this
  · rcases Nat.lt_or_ge q cs.length with hlt | hge
    · rw [rowTableWidth_app_left cs ds q (le_of_lt hlt), List.getD_append cs ds default q hlt]
      rw [rowW_append_left cs ds q hlt]
      exact h3 q hlt
    · obtain ⟨j, rfl⟩ : ∃ j, q = cs.length + j := ⟨q - cs.length, by omega⟩
      have hj : j < ds.length := by simp at hq; omega
      rw [rowTableWidth_app_shift, getD_append_shift]
      rw [rowW_append_right]
      intro i hi
      have := g3 j hj i hi
      rw [show base + (rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j) + 2 + 2*i + 1
        = base + rowTableWidth (rowW cs) cs.length + rowTableWidth (rowW ds) j + 2 + 2*i + 1 by omega]
      exact this

/-- The emitter's precondition is exactly this contract at the CNF's own clause
list, so the table writer's goal and the emitter's assumption are one statement. -/
lemma clauseTableAt_iff_rowsWritten (σ : Store) (tbl : ℕ) (φ : CNF) :
    ClauseTableAt σ tbl φ ↔ RowsWritten σ tbl φ.clauses := by
  unfold ClauseTableAt RowsWritten rowW cnfCnt cnfTag cnfVar
  rfl

/-! ## Base cases

Writing nothing satisfies the contract vacuously, and writing a single clause
reduces it to three plain facts about that clause's own cells — the form a
row-writing routine's correctness lemma delivers. -/

lemma rowsWritten_nil (σ : Store) (base : ℕ) : RowsWritten σ base [] := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> simp at hq

lemma rowsWritten_singleton (σ : Store) (base : ℕ) (c : Clause)
    (h1 : σ (base + 1) = c.lits.length)
    (h2 : ∀ i, i < c.lits.length →
      σ (base + 2 + 2 * i) = if litTag (c.lits.getD i default) then 1 else 0)
    (h3 : ∀ i, i < c.lits.length →
      σ (base + 2 + 2 * i + 1) = litVar (c.lits.getD i default)) :
    RowsWritten σ base [c] := by
  have hw : rowTableWidth (rowW [c]) 0 = 0 := rowTableWidth_zero _
  have hr : rowW [c] 0 = c.lits.length := rfl
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq
  · have hq0 : q = 0 := by simp at hq; omega
    subst hq0; rw [hw, hr, Nat.add_zero]; exact h1
  · have hq0 : q = 0 := by simp at hq; omega
    subst hq0; rw [hw, hr, Nat.add_zero]; exact h2
  · have hq0 : q = 0 := by simp at hq; omega
    subst hq0; rw [hw, hr, Nat.add_zero]; exact h3

/-- A single clause's row occupies the two header cells plus two per literal —
the amount the write pointer advances, so the next family starts there. -/
lemma rowTableWidth_singleton (c : Clause) :
    rowTableWidth (rowW [c]) 1 = 2 + 2 * c.lits.length := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, rowTableWidth_succ, rowTableWidth_zero,
    show rowW [c] 0 = c.lits.length from rfl]
  omega

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowLayout

/-!
The loop combinators take the control-cell indices as parameters and demand only
that they be distinct and inside the block.  Every family then has to supply the
same side conditions at every level, so leaving the indices abstract would mean
re-discharging arithmetic that has one right answer.

This file fixes that answer: one index per role, in a single block whose size is
a compile-time constant, chosen so the deepest family (transitions, four nested
ranges plus an inner literal counter) fits.  The families share the block rather
than each carrying their own, since they run in sequence and only the write
pointer has to survive between them.

Naming the indices makes the `PinsDisjoint`-style obligations `omega` facts
about literals.  The lemmas `ctlPins0_ok` through `ctlPins3_ok` establish the
pin conditions for each loop depth, so family proofs can reuse those facts.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The roles

Cell `M + 0` is the store's own base pointer and is never a loop's; the block
runs from `M + 1`. -/

/-- Where the next clause row is written.  Threaded through every family, so it
is the one control cell a family may not reuse. -/
def wpJ : ℕ := 1

/-- Loop counters, outermost to innermost.  Four suffice for every family's range
nest: transitions iterate over `t`, `p`, `qi`, `ai`. -/
def lvJ0 : ℕ := 2
def lvJ1 : ℕ := 3
def lvJ2 : ℕ := 4
def lvJ3 : ℕ := 5

/-- The literal counter inside a run-time-width clause, which sits below the
innermost range counter and so needs an index of its own. -/
def litJ : ℕ := 6

/-- A scratch cell for a value staged before a clause is written — the symbol a
variable number is read from, when the number comes from a table rather than
arithmetic. -/
def tmpJ : ℕ := 7

/-- The block's extent.  A compile-time constant, so every separation condition
against the table base is an `omega` fact. -/
def ctlJmax : ℕ := 7

lemma wpJ_pos : 1 ≤ wpJ := by unfold wpJ; omega
lemma wpJ_le : wpJ ≤ ctlJmax := by unfold wpJ ctlJmax; omega

/-! ## Pin lists

A level's `pins` is the list of counters above it, paired with their values.
Building them in a fixed order lets each family name its pin list once. -/

/-- The pin list at nesting depth `k`, for counter values `a b c` of the levels
above.  Depth 0 has nothing pinned; each further level adds its own counter. -/
def ctlPins0 : List (ℕ × ℕ) := []
def ctlPins1 (a : ℕ) : List (ℕ × ℕ) := [(lvJ0, a)]
def ctlPins2 (a b : ℕ) : List (ℕ × ℕ) := [(lvJ1, b), (lvJ0, a)]
def ctlPins3 (a b c : ℕ) : List (ℕ × ℕ) := [(lvJ2, c), (lvJ1, b), (lvJ0, a)]

/-! ## The side conditions, once

Each family's `hpin` argument says the pinned cells are in the block and differ
from the level's own counter and the write pointer.  With literal indices those
are decidable facts, so they are proved here and applied rather than re-derived
at every level. -/

lemma ctlPins0_ok (iJ : ℕ) :
    ∀ p ∈ ctlPins0, 1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp; exact absurd hp (List.not_mem_nil)

lemma ctlPins1_ok (a : ℕ) (iJ : ℕ) (h : lvJ0 ≠ iJ) :
    ∀ p ∈ ctlPins1 a, 1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  simp only [ctlPins1, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega, h, by unfold lvJ0 wpJ; omega⟩

lemma ctlPins2_ok (a b : ℕ) (iJ : ℕ) (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) :
    ∀ p ∈ ctlPins2 a b, 1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  simp only [ctlPins2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by unfold lvJ1; omega, by unfold lvJ1 ctlJmax; omega, h1, by unfold lvJ1 wpJ; omega⟩
  · exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega, h0, by unfold lvJ0 wpJ; omega⟩

lemma ctlPins3_ok (a b c : ℕ) (iJ : ℕ)
    (h0 : lvJ0 ≠ iJ) (h1 : lvJ1 ≠ iJ) (h2 : lvJ2 ≠ iJ) :
    ∀ p ∈ ctlPins3 a b c, 1 ≤ p.1 ∧ p.1 ≤ ctlJmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ := by
  intro p hp
  simp only [ctlPins3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨by unfold lvJ2; omega, by unfold lvJ2 ctlJmax; omega, h2, by unfold lvJ2 wpJ; omega⟩
  · exact ⟨by unfold lvJ1; omega, by unfold lvJ1 ctlJmax; omega, h1, by unfold lvJ1 wpJ; omega⟩
  · exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega, h0, by unfold lvJ0 wpJ; omega⟩

/-! ## Reading a pinned counter

A family's variable expressions read the enclosing counters through `ctlCell`.
These two lemmas are what turn such a read into its pinned value and into the
frame condition the leaf combinators ask for, so an expression built from
`ctlCell` and arithmetic discharges both obligations structurally. -/

lemma ctlCell_eval_of_pin (M : ℕ) (pins : List (ℕ × ℕ)) (j v : ℕ) (τ : Store)
    (hmem : (j, v) ∈ pins) (hF : PinsHold M pins τ) (h0 : τ 0 = M) :
    (ctlCell j).eval τ = v := by
  rw [ctlCell_eval, h0]
  exact hF (j, v) hmem

lemma ctlCell_frame (M Jmax j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ Jmax) (hjw : j ≠ wpJ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  rw [ctlCell_eval, ctlCell_eval, hσ, hσ']
  exact hagree j hj1 hj2 hjw

/-- The frame lemma at the four counters a variable expression may read, so a
    family's `hdep` obligation is one rewrite rather than four lookups. -/
lemma ctlCell_frame_lv (M j : ℕ) (hj : j = lvJ0 ∨ j = lvJ1 ∨ j = lvJ2 ∨ j = lvJ3)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ ctlJmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  have hj4 : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    unfold lvJ0 lvJ1 lvJ2 lvJ3 at hj; exact hj
  have hmax : ctlJmax = 7 := rfl
  have hw : wpJ = 1 := rfl
  exact ctlCell_frame M ctlJmax j (by omega) (by omega) (by omega) σ σ' hσ hσ' hagree

end NPComplete.CookLevin

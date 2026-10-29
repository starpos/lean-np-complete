module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteLoop

/-!
`ClauseLoopBody` describes an iteration of a loop, which must end by bumping its
counter.  That makes it the wrong notion to compose two writes with: running two
iterations back to back would bump the counter twice.  The families need exactly
that composition, though — a uniqueness iteration writes an `exactlyOne` block
followed by another, and the initial family is a concatenation of two loops — so
this file separates the two jobs.

`ClauseWriter` is the counter-free half: a program that writes some clause list
at the write pointer and advances it.  It composes with `.seq` directly, since
concatenating what two programs write is exactly `rowsWritten_append`.  A loop
iteration is then a writer plus a bump, and a whole loop is again a writer — so a
family is built by alternating the two, with `.seq` available at every level.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Running `prog` writes `cs` at the write pointer, advances the pointer past
    it, preserves the caller's frozen data, and leaves everything outside the
    control block below the pointer alone.  Unlike `ClauseLoopBody` there is no
    counter to bump, which is what makes `.seq` composition available. -/
def ClauseWriter (prog : Program) (M Jmax wpJ : ℕ) (Frozen : Store → Prop)
    (cs : List Clause) : Prop :=
  ∀ (τ : Store) (wp : ℕ), Frozen τ → τ 0 = M → τ (M + wpJ) = wp → M + Jmax < wp →
    Frozen (prog.eval τ) ∧
    (prog.eval τ) 0 = M ∧
    (prog.eval τ) (M + wpJ) = wp + rowTableWidth (rowW cs) cs.length ∧
    RowsWritten (prog.eval τ) wp cs ∧
    (∀ r, r < wp → CtlFree M Jmax r → (prog.eval τ) r = τ r)

/-- Running two writers in sequence writes the concatenation: the second starts
    at the pointer the first left behind, which is precisely the address
    `rowsWritten_append` needs, and it preserves the first's rows because they
    lie below its own entry pointer and outside the control block. -/
lemma clauseWriter_seq (p1 p2 : Program) (M Jmax wpJ : ℕ) (Frozen : Store → Prop)
    (cs ds : List Clause)
    (h1 : ClauseWriter p1 M Jmax wpJ Frozen cs)
    (h2 : ClauseWriter p2 M Jmax wpJ Frozen ds) :
    ClauseWriter (.seq p1 p2) M Jmax wpJ Frozen (cs ++ ds) := by
  intro τ wp hF h0 hw hsep
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 τ wp hF h0 hw hsep
  set σ1 := p1.eval τ with hσ1def
  set d1 := rowTableWidth (rowW cs) cs.length with hd1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 σ1 (wp + d1) a1 a2 a3 (by omega)
  have hgoal : (Program.seq p1 p2).eval τ = p2.eval σ1 := by rw [eval_seq, hσ1def]
  rw [hgoal]
  have hkeep : RowsWritten (p2.eval σ1) wp cs :=
    rowsWritten_of_agree σ1 (p2.eval σ1) wp cs a4
      (fun r _ hlt => b5 r (by omega) (Or.inr (by omega)))
  refine ⟨b1, b2, ?_, ?_, ?_⟩
  · rw [b3, rowTableWidth_append_total cs ds, ← hd1]; omega
  · exact rowsWritten_append _ wp cs ds hkeep b4
  · intro r hr1 hr2
    rw [b5 r (by omega) hr2]
    exact a5 r hr1 hr2

/-! ## Crossing between the two notions

A loop iteration is a writer followed by a counter bump; a whole loop is a
counter reset followed by `forN`, which is again a writer.  Alternating these
two is how a family's nest is built. -/

/-- Adding a counter bump turns a writer into a loop iteration.  The writer sees
    the iteration's own index pinned, which is how its clause list may depend on
    it; the resulting iteration only pins the levels above. -/
lemma clauseLoopBody_of_writer (prog : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ (PinsHold M ((iJ, i) :: pins)) (g i)) :
    ClauseLoopBody (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ (PinsHold M pins) g := by
  intro τ i wp hF h0 hi hwp hsep
  have hpins : PinsHold M ((iJ, i) :: pins) τ := pinsHold_cons M (iJ, i) pins τ hi hF
  obtain ⟨a1, a2, a3, a4, a5⟩ := hw i τ wp hpins h0 hwp hsep
  set σ1 := prog.eval τ with hσ1def
  have hσ1i : σ1 (M + iJ) = i := pinsHold_head M (iJ, i) pins σ1 a1
  set σ2 := (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1))).eval σ1 with hσ2def
  have hσ2eq : σ2 = writeReg σ1 (M + iJ) (i + 1) := by
    rw [hσ2def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, a2]
    congr 1
    simp [Expr.eval, ctlCell_eval, a2, hσ1i]
  have hgoal : (Program.seq prog (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1)))).eval τ
      = σ2 := by rw [hσ2def, hσ1def, eval_seq]
  rw [hgoal]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨_, _, hpne, _⟩ := hpin p hp
    rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) (M + p.1) (by omega)]
    exact pinsHold_tail M (iJ, i) pins σ1 a1 p hp
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) 0 (by omega), a2]
  · rw [hσ2eq, writeReg_same]
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) (M + wpJ) (by omega), a3]
  · exact rowsWritten_of_agree σ1 σ2 wp (g i) a4
      (fun r h1 _ => by rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r (by omega)])
  · intro r hr1 hr2
    have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
    rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r hrne]
    exact a5 r hr1 hr2

/-- Program shape of a whole loop: zero the counter, then iterate. -/
def loopProg (iJ : ℕ) (cntE : Expr) (body : Program) : Program :=
  .seq (ctlAssign iJ (.const 0)) (.forN cntE body)

/-- A whole loop is a writer for the `flatMap` of its iterations' lists.  Its
    trip count is fixed by the frozen data, so `n` is a plain parameter the
    caller reads off `hcnt`. -/
lemma clauseWriter_forN (body : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause) (cntE : Expr) (n : ℕ)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ (PinsHold M pins) g)
    (hcnt : ∀ τ : Store, τ 0 = M → PinsHold M pins τ → τ (M + iJ) = 0 → cntE.eval τ = n) :
    ClauseWriter (loopProg iJ cntE body) M Jmax wpJ (PinsHold M pins)
      ((List.range n).flatMap g) := by
  intro τ wp hF h0 hw hsep
  set σ1 := (ctlAssign iJ (Expr.const 0)).eval τ with hσ1def
  have hσ1eq : σ1 = writeReg τ (M + iJ) 0 := by
    rw [hσ1def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0]; rfl
  have hσ10 : σ1 0 = M := by
    rw [hσ1eq, writeReg_diff τ (M + iJ) 0 0 (by omega), h0]
  have hσ1i : σ1 (M + iJ) = 0 := by rw [hσ1eq, writeReg_same]
  have hσ1w : σ1 (M + wpJ) = wp := by
    rw [hσ1eq, writeReg_diff τ (M + iJ) 0 (M + wpJ) (by omega), hw]
  have hσ1pins : PinsHold M pins σ1 := by
    intro p hp
    obtain ⟨_, _, hpne, _⟩ := hpin p hp
    rw [hσ1eq, writeReg_diff τ (M + iJ) 0 (M + p.1) (by omega)]
    exact hF p hp
  obtain ⟨s1, s2, _, s4, s5, s6⟩ :=
    rowsWritten_forN body M Jmax wpJ iJ (PinsHold M pins) g cntE n wp σ1 hbody
      hσ1pins hσ10 hσ1i hσ1w (hcnt σ1 hσ10 hσ1pins hσ1i) hsep
  have hgoal : (loopProg iJ cntE body).eval τ = (Program.forN cntE body).eval σ1 := by
    rw [hσ1def]; unfold loopProg; rw [eval_seq]
  rw [hgoal]
  refine ⟨s1, s2, s4, s5, ?_⟩
  intro r hr1 hr2
  have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
  rw [s6 r hr1 hr2, hσ1eq, writeReg_diff τ (M + iJ) 0 r hrne]

/-! ## Choosing between two writers

A family whose clause *shape* varies with the input — the initial family's three
cases, the transition family's accept/reject split — cannot express that as
different loops, since a `forN` body writes the same number of clauses at every
index.  The choice has to happen inside one body, as an `ifNZ`.

Both branches write the *same* clause list: the caller knows which case holds
from the frozen data, and supplies the writer for it.  That is what keeps the
enclosing loop's clause list a function of the index alone. -/

lemma clauseWriter_ifNZ_gen (condE : Expr) (p1 p2 : Program) (M Jmax wpJ : ℕ)
    (Frozen : Store → Prop) (cs : List Clause) (cond : Prop)
    (hcond : ∀ τ, Frozen τ → τ 0 = M → (condE.eval τ ≠ 0 ↔ cond))
    (hw1 : cond → ClauseWriter p1 M Jmax wpJ Frozen cs)
    (hw2 : ¬cond → ClauseWriter p2 M Jmax wpJ Frozen cs) :
    ClauseWriter (.ifNZ condE p1 p2) M Jmax wpJ Frozen cs := by
  intro τ wp hF h0 hw hsep
  rw [eval_ifNZ]
  by_cases hc : cond
  · rw [ite_eq_left ((hcond τ hF h0).mpr hc)]
    exact hw1 hc τ wp hF h0 hw hsep
  · rw [ite_eq_right (fun h => hc ((hcond τ hF h0).mp h))]
    exact hw2 hc τ wp hF h0 hw hsep

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransExpr
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTransMove
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq
public import NPComplete.CookLevin.Tableau.TableauRamLoops

/-!
The transition family is the reduction's deepest nest: four range counters
(`t`, `p`, `qi`, `ai`) close over a branch that reads the machine's transition
table.  The selected clause shape depends on the table values:
`natTransClausesPadded` picks between an accepting triple (`imply3` × 3) and a
rejecting one (`forbid3` × 3), and the accepting branch varies by kind
(halt, write, or move).

`ClauseFamilyTransExpr.lean` supplies the variable expressions that read the
table and the current/next row; `ClauseTransMove.lean` supplies the arithmetic
form of a move's boundary test.  This file's own contribution is the wiring:
a `Program`-level `ifNZ` combinator for `ClauseWriter` (`clauseWriter_ifNZ`),
the fixed-shape three-clause blocks it selects between
(`trans_imply3_block_writer`, `trans_forbid3_block_writer`), a restatement of
`natTransClausesPadded` purely in terms of the three numeric columns
(`natTransClausesTriple`, matching it by `natTransClausesTriple_transOf`), and
the case-by-case selection of the right block by the columns' own values,
closed by `forN`/`clauseLoopBody_of_writer` into the family as a whole.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.SAT

/-! ## The `ifNZ` combinator

A `ClauseWriter` is a program together with a *fixed* clause list it always
writes; `ifNZ` therefore only makes sense here when both branches write the
*same* list — the branch taken depends on run-time data, but a family's clause
value at one loop index is single-valued, so the two writers below always
agree at the index the branch was chosen for. -/

/-- Wiring a `Program.ifNZ` into `ClauseWriter`: whichever branch the guard
selects, the caller supplies a `ClauseWriter` proof for it, at the *same*
clause list `cs`.  `hcond` reads the guard against the frozen data and the
usual `τ 0 = M` obligation, matching what the clause-writing leaves
already have on hand. -/
lemma clauseWriter_ifNZ (condE : Expr) (p1 p2 : Program) (M Jmax wpJ : ℕ)
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

/-! ## Combinators under `PinsAndWords3`

The loop combinators `clauseWriter_forN` and `clauseLoopBody_of_writer` freeze only
`PinsHold`.  The transition family also freezes three staged columns, so the same three
jobs — a below-the-pointer clause write, a counter bump, a whole `forN` —
are restated here with `PinsAndWords3` as `Frozen`. -/

lemma clauseWriter_clause_below_words3 (M Jmax : ℕ) (lits : List (Expr × Expr))
    (pins : List (ℕ × ℕ)) (c : Clause)
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (hwpJmax : wpJ ≤ Jmax)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ)
    (hbasek : M + ctlJmax < basek) (hbase1 : M + ctlJmax < base1)
    (hbase2 : M + ctlJmax < base2)
    (hwk : WordBelow basek xsk.length (M + Jmax + 1))
    (hw1w : WordBelow base1 xs1.length (M + Jmax + 1))
    (hw2w : WordBelow base2 xs2.length (M + Jmax + 1))
    (hdep : ∀ p ∈ lits, ∀ (bound : ℕ), ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      M + Jmax < bound → (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ)
    (hlen : c.lits.length = lits.length)
    (hlit : ∀ (τ : Store) (k : ℕ),
      PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ → τ 0 = M → k < lits.length →
      (lits.getD k defLit).1.eval τ = (if litTag (c.lits.getD k default) then 1 else 0) ∧
      (lits.getD k defLit).2.eval τ = litVar (c.lits.getD k default)) :
    ClauseWriter (writeClauseProg wpJ lits) M Jmax wpJ
      (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2) [c] := by
  intro τ wp hF h0 hw hsep
  have hinv : ∀ p ∈ lits, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      p.1.eval σ' = p.1.eval σ ∧ p.2.eval σ' = p.2.eval σ :=
    fun p hp σ σ' hσ hσ' hagree => hdep p hp wp σ σ' hσ hσ' hsep hagree
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ lits M wp τ wpJ_pos h0 hw (by omega) hinv
  set σ2 := (writeClauseProg wpJ lits).eval τ with hσ2def
  have hwidth : rowTableWidth (rowW [c]) [c].length = 2 + 2 * lits.length := by
    rw [show [c].length = 1 from rfl, rowTableWidth_singleton, hlen]
  have hmono : M + Jmax + 1 ≤ wp := by omega
  refine ⟨?_, w4, ?_, ?_, ?_⟩
  · exact pinsAndWords3_preserve_below M Jmax pins basek xsk base1 xs1 base2 xs2 τ σ2 wp hF
      hbasek hbase1 hbase2
      (wordBelow_mono _ _ _ _ hwk hmono) (wordBelow_mono _ _ _ _ hw1w hmono)
      (wordBelow_mono _ _ _ _ hw2w hmono) hpin hsep w5
  · rw [w3, hwidth]; omega
  · refine rowsWritten_singleton σ2 wp c ?_ ?_ ?_
    · rw [w1, hlen]
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).1]
      exact (hlit τ k hF h0 hk).1
    · intro k hk
      rw [hlen] at hk
      rw [(w2 k hk).2]
      exact (hlit τ k hF h0 hk).2
  · intro r hr1 hr2
    exact w5 r hr1 (by have hwpJ1 : wpJ = 1 := rfl; rcases hr2 with h | h <;> omega)

lemma clauseLoopBody_of_writer_words3 (prog : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause)
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ) (hiJctl : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hbasek : M + ctlJmax < basek) (hbase1 : M + ctlJmax < base1)
    (hbase2 : M + ctlJmax < base2)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ
      (PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2) (g i)) :
    ClauseLoopBody (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2) g := by
  intro τ i wp hF h0 hi hwp hsep
  have hpins : PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2 τ :=
    pinsAndWords3_cons M (iJ, i) pins basek xsk base1 xs1 base2 xs2 τ hi hF
  obtain ⟨a1, a2, a3, a4, a5⟩ := hw i τ wp hpins h0 hwp hsep
  set σ1 := prog.eval τ with hσ1def
  have hσ1i : σ1 (M + iJ) = i := pinsHold_head M (iJ, i) pins σ1 a1.1
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
  · rw [hσ2eq]
    exact pinsAndWords3_writeReg_loop M pins basek xsk base1 xs1 base2 xs2 iJ (i + 1) σ1
      (pinsAndWords3_tail M (iJ, i) pins basek xsk base1 xs1 base2 xs2 σ1 a1) hiJctl
      (fun p hp => by obtain ⟨_, _, hpne, _⟩ := hpin p hp; omega)
      hbasek hbase1 hbase2
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) 0 (by omega), a2]
  · rw [hσ2eq, writeReg_same]
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) (M + wpJ) (by omega), a3]
  · exact rowsWritten_of_agree σ1 σ2 wp (g i) a4
      (fun r h1 _ => by rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r (by omega)])
  · intro r hr1 hr2
    have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
    rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r hrne]
    exact a5 r hr1 hr2

lemma clauseWriter_forN_words3 (body : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause) (cntE : Expr) (n : ℕ)
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ) (hiJctl : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hbasek : M + ctlJmax < basek) (hbase1 : M + ctlJmax < base1)
    (hbase2 : M + ctlJmax < base2)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ
      (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2) g)
    (hcnt : ∀ τ : Store, τ 0 = M →
      PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ → τ (M + iJ) = 0 →
      cntE.eval τ = n) :
    ClauseWriter (loopProg iJ cntE body) M Jmax wpJ
      (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2)
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
  have hσ1F : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 σ1 := by
    rw [hσ1eq]
    exact pinsAndWords3_writeReg_loop M pins basek xsk base1 xs1 base2 xs2 iJ 0 τ hF hiJctl
      (fun p hp => by obtain ⟨_, _, hpne, _⟩ := hpin p hp; omega)
      hbasek hbase1 hbase2
  obtain ⟨s1, s2, _, s4, s5, s6⟩ :=
    rowsWritten_forN body M Jmax wpJ iJ
      (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2) g cntE n wp σ1 hbody
      hσ1F hσ10 hσ1i hσ1w (hcnt σ1 hσ10 hσ1F hσ1i) hsep
  have hgoal : (loopProg iJ cntE body).eval τ = (Program.forN cntE body).eval σ1 := by
    rw [hσ1def]; unfold loopProg; rw [eval_seq]
  rw [hgoal]
  refine ⟨s1, s2, s4, s5, ?_⟩
  intro r hr1 hr2
  have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
  rw [s6 r hr1 hr2, hσ1eq, writeReg_diff τ (M + iJ) 0 r hrne]

/-! ## The fixed-width blocks

Every `natTransClausesPadded` branch writes exactly three clauses, of one of
two shapes.  `transStateE`/`transHeadE`/`transCellE` are the three antecedents
shared by every accepting clause; only the fourth argument to `imply3`
(the successor position) differs across the three clauses of a block and
across the three kinds of successor row.  Isolating the single-clause writer
`trans_imply3_d_writer` at an arbitrary fourth expression lets one `clauseWriter_seq`
chain build every accepting block, whatever the successor reads. -/

/-- The pin list a `natTransClausesPadded` leaf sees: the three enclosing
counters plus its own. -/
abbrev transLeafPins (t p qi ai : ℕ) : List (ℕ × ℕ) := (lvJ3, ai) :: ctlPins3 t p qi

lemma trans_pin4 (t p qi ai : ℕ) :
    ∀ q ∈ transLeafPins t p qi ai, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ := by
  intro q hq
  simp only [transLeafPins, ctlPins3, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by unfold lvJ3; omega, by unfold lvJ3 ctlJmax; omega, by unfold lvJ3 wpJ; omega⟩
  · exact ⟨by unfold lvJ2; omega, by unfold lvJ2 ctlJmax; omega, by unfold lvJ2 wpJ; omega⟩
  · exact ⟨by unfold lvJ1; omega, by unfold lvJ1 ctlJmax; omega, by unfold lvJ1 wpJ; omega⟩
  · exact ⟨by unfold lvJ0; omega, by unfold lvJ0 ctlJmax; omega, by unfold lvJ0 wpJ; omega⟩

lemma trans_pin4_le (t p qi ai Jmax : ℕ) (h : ctlJmax ≤ Jmax) :
    ∀ q ∈ transLeafPins t p qi ai, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ :=
  fun q hq =>
    let ⟨h1, h2, h3⟩ := trans_pin4 t p qi ai q hq
    ⟨h1, Nat.le_trans h2 h, h3⟩

/-- A generic frame condition, phrased against the control block, restated in
the "agrees below a bound" shape `clauseWriter_clause_below_words3` consumes. -/
lemma ctl_frame_below (M Jmax wpJV : ℕ) (e : Expr)
    (hctl : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJV → σ' (M + j) = σ (M + j)) → e.eval σ' = e.eval σ)
    (bound : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hbound : M + Jmax < bound)
    (hagree : ∀ r, r < bound → r ≠ M + wpJV → σ' r = σ r) :
    e.eval σ' = e.eval σ :=
  hctl σ σ' hσ hσ' (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))

/-- One accepting clause, `imply3 (state t qi) (head t p) (cell t p ai) d`, for
an arbitrary successor expression `dE` — the block every kind of accepting
branch instantiates three times, at different `dE`. -/
lemma trans_imply3_d_writer (M n W m t p qi ai : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) (dE : Expr) (dv : ℕ)
    (hbasek : M + ctlJmax < kindBase) (hbase1 : M + ctlJmax < arg1Base)
    (hbase2 : M + ctlJmax < arg2Base)
    (hdepD : ∀ (bound : ℕ), ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      M + transJM M kindBase colk arg1Base col1 arg2Base col2 < bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → dE.eval σ' = dE.eval σ)
    (hvalD : ∀ τ : Store,
      TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → dE.eval τ = dv) :
    ClauseWriter
      (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m) dE))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai) dv] := by
  have hJ : ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
    transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2
  have hbposk : 1 ≤ kindBase := by have : ctlJmax = 7 := rfl; omega
  have hbpos1 : 1 ≤ arg1Base := by have : ctlJmax = 7 := rfl; omega
  have hbpos2 : 1 ≤ arg2Base := by have : ctlJmax = 7 := rfl; omega
  refine clauseWriter_clause_below_words3 M
      (transJM M kindBase colk arg1Base col1 arg2Base col2) _ _ _
      kindBase colk arg1Base col1 arg2Base col2
      (Nat.le_trans wpJ_le hJ)
      (trans_pin4_le t p qi ai _ hJ) hbasek hbase1 hbase2
      (transJM_wordBelow_kind M kindBase colk arg1Base col1 arg2Base col2 hbposk)
      (transJM_wordBelow_arg1 M kindBase colk arg1Base col1 arg2Base col2 hbpos1)
      (transJM_wordBelow_arg2 M kindBase colk arg1Base col1 arg2Base col2 hbpos2)
      ?_ rfl ?_
  · intro l hl bound σ σ' hσ hσ' hbound hagree
    have hboundc : M + ctlJmax < bound :=
      transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound
    simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transStateE n W m)
        (fun σ σ' hσ hσ' h => transStateE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hboundc hagree⟩
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transHeadE n W m)
        (fun σ σ' hσ hσ' h => transHeadE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hboundc hagree⟩
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transCellE n W m)
        (fun σ σ' hσ hσ' h => transCellE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hboundc hagree⟩
    · exact ⟨rfl, hdepD bound σ σ' hσ hσ' hbound hagree⟩
  · intro τ k hF h0 hk
    rw [imply3Lits_length] at hk
    interval_cases k
    · rw [imply3Lits_get0]
      refine ⟨rfl, ?_⟩
      rw [imply3_var0]
      exact transStateE_value M n W m t p qi τ
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
    · rw [imply3Lits_get1]
      refine ⟨rfl, ?_⟩
      rw [imply3_var1]
      exact transHeadE_value M n W m t p qi τ
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
    · rw [imply3Lits_get2]
      refine ⟨rfl, ?_⟩
      rw [imply3_var2]
      exact transCellE_value M n W m t p qi τ ai
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
        (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1)
    · rw [imply3Lits_get3]
      refine ⟨rfl, ?_⟩
      rw [imply3_var3]
      exact hvalD τ hF h0

/-- Three `imply3` clauses back to back, with three successor expressions —
what an accepting `natTransClausesPadded` branch always writes, whichever kind
of row those three successor expressions come from. -/
lemma trans_imply3_block_writer (M n W m t p qi ai : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) (dE1 dE2 dE3 : Expr) (dv1 dv2 dv3 : ℕ)
    (hbasek : M + ctlJmax < kindBase) (hbase1 : M + ctlJmax < arg1Base)
    (hbase2 : M + ctlJmax < arg2Base)
    (hdep1 : ∀ (bound : ℕ), ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      M + transJM M kindBase colk arg1Base col1 arg2Base col2 < bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → dE1.eval σ' = dE1.eval σ)
    (hdep2 : ∀ (bound : ℕ), ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      M + transJM M kindBase colk arg1Base col1 arg2Base col2 < bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → dE2.eval σ' = dE2.eval σ)
    (hdep3 : ∀ (bound : ℕ), ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      M + transJM M kindBase colk arg1Base col1 arg2Base col2 < bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → dE3.eval σ' = dE3.eval σ)
    (hval1 : ∀ τ : Store,
      TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → dE1.eval τ = dv1)
    (hval2 : ∀ τ : Store,
      TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → dE2.eval τ = dv2)
    (hval3 : ∀ τ : Store,
      TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → dE3.eval τ = dv3) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ
          (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m) dE1))
        (writeClauseProg wpJ
          (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m) dE2)))
        (writeClauseProg wpJ
          (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m) dE3)))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai) dv1,
       imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai) dv2,
       imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai) dv3] :=
  clauseWriter_seq _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _ _
    (clauseWriter_seq _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
        (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _ _
      (trans_imply3_d_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
        dE1 dv1 hbasek hbase1 hbase2 hdep1 hval1)
      (trans_imply3_d_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
        dE2 dv2 hbasek hbase1 hbase2 hdep2 hval2))
    (trans_imply3_d_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
      dE3 dv3 hbasek hbase1 hbase2 hdep3 hval3)

/-- One `forbid3 (state t qi) (head t p) (cell t p ai)` clause — the rejecting
branch's single repeated shape. -/
lemma trans_forbid3_writer (M n W m t p qi ai : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ)
    (hbasek : M + ctlJmax < kindBase) (hbase1 : M + ctlJmax < arg1Base)
    (hbase2 : M + ctlJmax < arg2Base) :
    ClauseWriter
      (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai)] := by
  have hJ : ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
    transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2
  have hbposk : 1 ≤ kindBase := by have : ctlJmax = 7 := rfl; omega
  have hbpos1 : 1 ≤ arg1Base := by have : ctlJmax = 7 := rfl; omega
  have hbpos2 : 1 ≤ arg2Base := by have : ctlJmax = 7 := rfl; omega
  refine clauseWriter_clause_below_words3 M
      (transJM M kindBase colk arg1Base col1 arg2Base col2) _ _ _
      kindBase colk arg1Base col1 arg2Base col2
      (Nat.le_trans wpJ_le hJ)
      (trans_pin4_le t p qi ai _ hJ) hbasek hbase1 hbase2
      (transJM_wordBelow_kind M kindBase colk arg1Base col1 arg2Base col2 hbposk)
      (transJM_wordBelow_arg1 M kindBase colk arg1Base col1 arg2Base col2 hbpos1)
      (transJM_wordBelow_arg2 M kindBase colk arg1Base col1 arg2Base col2 hbpos2)
      ?_ rfl ?_
  · intro l hl bound σ σ' hσ hσ' hbound hagree
    have hctlB := transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound
    simp only [forbid3Lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transStateE n W m)
        (fun σ σ' hσ hσ' h => transStateE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hctlB hagree⟩
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transHeadE n W m)
        (fun σ σ' hσ hσ' h => transHeadE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hctlB hagree⟩
    · exact ⟨rfl, ctl_frame_below M ctlJmax wpJ (transCellE n W m)
        (fun σ σ' hσ hσ' h => transCellE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' hctlB hagree⟩
  · intro τ k hF h0 hk
    rw [forbid3Lits_length] at hk
    interval_cases k
    · rw [forbid3Lits_get0]
      refine ⟨rfl, ?_⟩
      rw [forbid3_var0]
      exact transStateE_value M n W m t p qi τ
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
    · rw [forbid3Lits_get1]
      refine ⟨rfl, ?_⟩
      rw [forbid3_var1]
      exact transHeadE_value M n W m t p qi τ
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
    · rw [forbid3Lits_get2]
      refine ⟨rfl, ?_⟩
      rw [forbid3_var2]
      exact transCellE_value M n W m t p qi τ ai
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
        (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1)

/-- Three identical `forbid3` clauses — what a rejecting `natTransClausesPadded`
branch always writes. -/
lemma trans_forbid3_block_writer (M n W m t p qi ai : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ)
    (hbasek : M + ctlJmax < kindBase) (hbase1 : M + ctlJmax < arg1Base)
    (hbase2 : M + ctlJmax < arg2Base) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))
        (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))
        (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai),
       forbid3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai),
       forbid3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai)] :=
  clauseWriter_seq _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _ _
    (clauseWriter_seq _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
        (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _ _
      (trans_forbid3_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
        hbasek hbase1 hbase2)
      (trans_forbid3_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
        hbasek hbase1 hbase2))
    (trans_forbid3_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
      hbasek hbase1 hbase2)

/-! ## The three accepting shapes

`natTransClausesPadded`'s three accepting branches (halt / write / move) differ
only in which three successor expressions `trans_imply3_block_writer` is given:
the halt branch reads no table row at all (the successor position is unchanged
throughout), the write branch reads the `arg1`/`arg2` columns for the successor
state and written symbol, and the move branch reads `arg1` for the successor
state and computes the successor head position from `arg2` via `transHeadMoveE`.  The halt
block is proved here; the write and move blocks are proved below in the
layout-stride/count-separated form (`trans_accept_write_writer_gen`,
`trans_accept_move_writer_gen`). -/

/-- `state (t+1) qi` at the level's own counters — no table read, since a halt
transition leaves state, head, and cell unchanged. -/
def transStateSameE (n W m : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ2)

lemma transStateSameE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transStateSameE n W m).eval σ' = (transStateSameE n W m).eval σ := by
  unfold transStateSameE
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (expr_add_one_eval_congr _ σ σ'
      (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)

lemma transStateSameE_value (M n W m t p qi : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) :
    (transStateSameE n W m).eval τ = (denseLayout n W m).state (t + 1) qi := by
  unfold transStateSameE
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m (t + 1) qi rfl rfl rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0))
    (ctlCell_eval_of_pin M _ lvJ2 qi τ (by simp [ctlPins3]) hF h0)

/-- The halt branch's block: state, head, and cell all carry over unchanged. -/
lemma trans_accept_halt_writer (M n W m t p qi ai : ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ)
    (hbasek : M + ctlJmax < kindBase) (hbase1 : M + ctlJmax < arg1Base)
    (hbase2 : M + ctlJmax < arg2Base) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
          (transStateSameE n W m)))
        (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
          (transHeadSameE n W m))))
        (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
          (transCellSameE n W m))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai)
        ((denseLayout n W m).state (t + 1) qi),
       imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai)
        ((denseLayout n W m).head (t + 1) p),
       imply3 ((denseLayout n W m).state t qi) ((denseLayout n W m).head t p)
        ((denseLayout n W m).cell t p ai)
        ((denseLayout n W m).cell (t + 1) p ai)] :=
  trans_imply3_block_writer M n W m t p qi ai kindBase colk arg1Base col1 arg2Base col2
    (transStateSameE n W m) (transHeadSameE n W m) (transCellSameE n W m)
    ((denseLayout n W m).state (t + 1) qi)
    ((denseLayout n W m).head (t + 1) p)
    ((denseLayout n W m).cell (t + 1) p ai)
    hbasek hbase1 hbase2
    (fun bound σ σ' hσ hσ' hbound hagree =>
      ctl_frame_below M ctlJmax wpJ (transStateSameE n W m)
        (fun σ σ' hσ hσ' h => transStateSameE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' (transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound)
        hagree)
    (fun bound σ σ' hσ hσ' hbound hagree =>
      ctl_frame_below M ctlJmax wpJ (transHeadSameE n W m)
        (fun σ σ' hσ hσ' h => transHeadSameE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' (transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound)
        hagree)
    (fun bound σ σ' hσ hσ' hbound hagree =>
      ctl_frame_below M ctlJmax wpJ (transCellSameE n W m)
        (fun σ σ' hσ hσ' h => transCellSameE_frame M n W m σ σ' hσ hσ' h)
        bound σ σ' hσ hσ' (transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound)
        hagree)
    (fun τ hF h0 => transStateSameE_value M n W m t p qi τ
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0)
    (fun τ hF h0 => transHeadSameE_value M n W m t p qi τ
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0)
    (fun τ hF h0 => transCellSameE_value M n W m t p qi τ ai
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1) h0
      (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ hF.1))

/-! ## `natTransClausesPadded`, restated over the three numeric columns

`natTransClausesPadded` branches on a `NatTrans`, which a RAM program cannot
hold; `natTransClausesTriple` restates the same case split directly over the
three numbers a transition is read from (`transKind`, `transArg1`, `transArg2`), so
a producer's branch tests (`k = 0`, `k = 1`, `a1 < n`, `moveOk`) line up with the
definition one for one.  `natTransClausesTriple_transOf` is the bridge back: applied at a
transition's own `(transKind, transArg1, transArg2)`, it reproduces
`natTransClausesPadded` exactly. -/

/-- `natTransClausesPadded`, with the `NatTrans` argument replaced by its three
numeric columns `(k, a1, a2)`. `k`'s three values (`0`/`1`/other) select
halt/write/move; the move case's boundary test is `moveOk` rather than
`nextIdx`, and its successor head is the additive form `p + a2 - (1 - a2)`
(`ClauseTransMove.lean`'s `moveTo_eq_add_sub`) rather than `moveTo p a2`,
matching the form `trans_head_move_e_gen_value` produces directly. -/
def natTransClausesTriple (v : ExecVarLayout) (n W t p qi ai k a1 a2 : ℕ) : List Clause :=
  if k = 0 then
    [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi),
      imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
      imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
  else if k = 1 then
    if a1 < n then
      [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) a1),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p a2)]
    else
      [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
        forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
        forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
  else
    if a1 < n then
      if moveOk W p a2 ≠ 0 then
        [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) a1),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai)
            (v.head (t + 1) (p + a2 - (1 - a2))),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
      else
        [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
    else
      [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
        forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
        forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]

/-- Past the first two `k` cases, the definition depends only on `k ≠ 0 ∧ k ≠ 1`,
not on `k`'s exact value — this is what lets a caller who only knows `colk` is
neither `0` nor `1` (rather than that it equals `2`) still match the move
branch. -/
lemma natTransClausesTriple_of_ge2 (v : ExecVarLayout) (n W t p qi ai k a1 a2 : ℕ)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    natTransClausesTriple v n W t p qi ai k a1 a2
      = natTransClausesTriple v n W t p qi ai 2 a1 a2 := by
  unfold natTransClausesTriple
  rw [ite_eq_right hk0, ite_eq_right hk1, ite_eq_right (by omega : ¬ (2 : ℕ) = 0), ite_eq_right (by omega : ¬ (2 : ℕ) = 1)]

/-- The restated case split matches `natTransClausesPadded` exactly, at a
transition's own numeric columns. -/
lemma natTransClausesTriple_transOf (v : ExecVarLayout) (n W t p qi ai : ℕ) (e : NatTrans) :
    natTransClausesTriple v n W t p qi ai (transKind e) (transArg1 e) (transArg2 e)
      = natTransClausesPadded v n W t p qi ai e := by
  cases e with
  | halt => rfl
  | write q' b => rfl
  | move q' dir =>
      change natTransClausesTriple v n W t p qi ai 2 q'
          (transArg2 (NatTrans.move q' dir)) =
        natTransClausesPadded v n W t p qi ai (NatTrans.move q' dir)
      simp [natTransClausesTriple, natTransClausesPadded]
      by_cases hq' : q' < n
      · simp [hq']
        have hdirnat : transArg2 (NatTrans.move q' dir) = 0 ∨ transArg2 (NatTrans.move q' dir) = 1 := by
          cases dir <;> simp [transArg2]
        have hdireq : dirOfNat (transArg2 (NatTrans.move q' dir)) = dir := by cases dir <;> rfl
        by_cases hok : moveOk W p (transArg2 (NatTrans.move q' dir)) ≠ 0
        · simp [hok]
          rw [← hdireq, nextIdx_eq_moveTo W p _ hdirnat hok, hdireq,
            ← moveTo_eq_add_sub p (transArg2 (NatTrans.move q' dir)) hdirnat]
        · have hzero : moveOk W p (transArg2 (NatTrans.move q' dir)) = 0 := by
            by_contra hne
            exact hok hne
          simp [hzero]
          rw [← hdireq, nextIdx_none_of_moveOk_zero W p _ hdirnat hzero]
      · simp [hq']

/-! ## Reading the descriptor's own columns

`TableauDescriptor.entry` looks a transition up in `d.table`; the three columns
`ClauseFamilyTransExpr.lean` reads are `d.table.map transKind` etc., so
`TableauDescriptor.entry`'s row-major `getD` and `List.getD_map` together give
each column's value at `d.entry qi ai` directly. -/

lemma transKind_col_getD_eq (d : TableauDescriptor) (qi ai : ℕ) :
    (d.table.map transKind).getD (qi * d.numLetters + ai) 0 = transKind (d.entry qi ai) := by
  unfold TableauDescriptor.entry
  exact List.getD_map d.table NatTrans.halt transKind

lemma transArg1_col_getD_eq (d : TableauDescriptor) (qi ai : ℕ) :
    (d.table.map transArg1).getD (qi * d.numLetters + ai) 0 = transArg1 (d.entry qi ai) := by
  unfold TableauDescriptor.entry
  exact List.getD_map d.table NatTrans.halt transArg1

lemma transArg2_col_getD_eq (d : TableauDescriptor) (qi ai : ℕ) :
    (d.table.map transArg2).getD (qi * d.numLetters + ai) 0 = transArg2 (d.entry qi ai) := by
  unfold TableauDescriptor.entry
  exact List.getD_map d.table NatTrans.halt transArg2

/-! ## The innermost `(qi, ai)` body, as a nested `ifNZ`

`transLeafProg` tests, in order, the kind column against `0` and `1`, and — for
`1` (write) and `2`/other (move) — the `arg1` column against `n`; the move case
additionally tests `moveOkE`.  Each leaf of the resulting decision tree is one
of the accepting or rejecting three-clause blocks.  The writer lemmas for the two branches
(`trans_leaf_write_branch_writer_gen`, `trans_leaf_move_branch_writer_gen`) are
stated below for the layout-stride/count-separated form of this program. -/

/-- The nested-`ifNZ` program one `(t, p, qi, ai)` cell runs, reading the
kind/arg1/arg2 columns at their own bases. -/
def transLeafProg (n W m kindBase arg1Base arg2Base lenk len1 len2 : ℕ) : Program :=
  .ifNZ (.eq (transKindE kindBase lenk m) (.const 0))
    (.seq (.seq
      (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
        (transStateSameE n W m)))
      (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
        (transHeadSameE n W m))))
      (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
        (transCellSameE n W m))))
    (.ifNZ (.eq (transKindE kindBase lenk m) (.const 1))
      (.ifNZ (.lt (transArg1E arg1Base len1 m) (.const n))
        (.seq (.seq
          (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
            (transStateNextE n W m arg1Base len1)))
          (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
            (transHeadSameE n W m))))
          (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
            (transCellWriteE n W m arg2Base len2))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))))
      (.ifNZ (.lt (transArg1E arg1Base len1 m) (.const n))
        (.ifNZ (moveOkE W (ctlCell lvJ1) (transArg2E arg2Base len2 m))
          (.seq (.seq
            (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
              (transStateNextE n W m arg1Base len1)))
            (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
              (transHeadMoveE n W m arg2Base len2))))
            (writeClauseProg wpJ (imply3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)
              (transCellSameE n W m))))
          (.seq (.seq
            (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))
            (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))
            (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m)))
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))
          (writeClauseProg wpJ (forbid3Lits (transStateE n W m) (transHeadE n W m) (transCellE n W m))))))

/-! ## Layout-stride/count-separated transition expressions -/

/-- Successor-state expression with independent layout and table-row strides. -/
def transStateNextEGen (nS W mS mC arg1Base len1 : ℕ) : Expr :=
  denseStateE (.const nS) (.const W) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (transArg1E arg1Base len1 mC)

lemma trans_state_next_e_gen_frame (M nS W mS mC arg1Base len bound : ℕ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hw : WordBelow arg1Base len bound) (hbase : M + ctlJmax < arg1Base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (transStateNextEGen nS W mS mC arg1Base len).eval σ'
      = (transStateNextEGen nS W mS mC arg1Base len).eval σ := by
  have hctl0 : M + ctlJmax < bound := by obtain ⟨_, hb2⟩ := hw; omega
  have hctl' : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  unfold transStateNextEGen
  rw [denseStateE_eval, denseStateE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl',
    transArg1E_frame M arg1Base len bound mC σ σ' hσ hσ' hw hbase hagree]

lemma trans_state_next_e_gen_value (M nS W mS mC arg1Base t p qi ai : ℕ)
    (τ : Store) (col1 : List ℕ) (hF : PinsHold M (ctlPins3 t p qi) τ)
    (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) (hw : WordAt τ arg1Base col1) :
    (transStateNextEGen nS W mS mC arg1Base col1.length).eval τ
      = (denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0) := by
  have e0 : (ctlCell lvJ0).eval τ = t :=
    ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0
  unfold transStateNextEGen
  rw [denseStateE_eval]
  simp only [Expr.eval, e0]
  rw [transArg1E_value M arg1Base mC t p qi ai τ col1 hF h0 hai hw]

/-- Written-cell expression with independent layout and table-row strides. -/
def transCellWriteEGen (nS W mS mC arg2Base len2 : ℕ) : Expr :=
  denseCellE (.const nS) (.const W) (.const mS)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1) (transArg2E arg2Base len2 mC)

lemma trans_cell_write_e_gen_frame (M nS W mS mC arg2Base len bound : ℕ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hw : WordBelow arg2Base len bound) (hbase : M + ctlJmax < arg2Base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (transCellWriteEGen nS W mS mC arg2Base len).eval σ'
      = (transCellWriteEGen nS W mS mC arg2Base len).eval σ := by
  have hctl0 : M + ctlJmax < bound := by obtain ⟨_, hb2⟩ := hw; omega
  have hctl' : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  unfold transCellWriteEGen
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl',
    ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hctl',
    transArg2E_frame M arg2Base len bound mC σ σ' hσ hσ' hw hbase hagree]

lemma trans_cell_write_e_gen_value (M nS W mS mC arg2Base t p qi ai : ℕ)
    (τ : Store) (col2 : List ℕ) (hF : PinsHold M (ctlPins3 t p qi) τ)
    (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) (hw : WordAt τ arg2Base col2) :
    (transCellWriteEGen nS W mS mC arg2Base col2.length).eval τ
      = (denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0) := by
  have e0 : (ctlCell lvJ0).eval τ = t :=
    ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0
  have e1 : (ctlCell lvJ1).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0
  unfold transCellWriteEGen
  rw [denseCellE_eval]
  simp only [Expr.eval, e0, e1]
  rw [transArg2E_value M arg2Base mC t p qi ai τ col2 hF h0 hai hw]

/-- Moved-head expression with independent layout and table-row strides. -/
def transHeadMoveEGen (nS W mS mC arg2Base len2 : ℕ) : Expr :=
  denseHeadE (.const nS) (.const W) (.const mS) (.add (ctlCell lvJ0) (.const 1))
    (.sub (.add (ctlCell lvJ1) (transArg2E arg2Base len2 mC))
      (.sub (.const 1) (transArg2E arg2Base len2 mC)))

lemma trans_head_move_e_gen_frame (M nS W mS mC arg2Base len bound : ℕ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hw : WordBelow arg2Base len bound) (hbase : M + ctlJmax < arg2Base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (transHeadMoveEGen nS W mS mC arg2Base len).eval σ'
      = (transHeadMoveEGen nS W mS mC arg2Base len).eval σ := by
  have hctl0 : M + ctlJmax < bound := by obtain ⟨_, hb2⟩ := hw; omega
  have hctl' : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  unfold transHeadMoveEGen
  rw [denseHeadE_eval, denseHeadE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl',
    ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hctl',
    transArg2E_frame M arg2Base len bound mC σ σ' hσ hσ' hw hbase hagree]

lemma trans_head_move_e_gen_value (M nS W mS mC arg2Base t p qi ai p' : ℕ)
    (τ : Store) (col2 : List ℕ) (hF : PinsHold M (ctlPins3 t p qi) τ)
    (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) (hw : WordAt τ arg2Base col2)
    (hp' : p' = p + col2.getD (qi * mC + ai) 0 - (1 - col2.getD (qi * mC + ai) 0)) :
    (transHeadMoveEGen nS W mS mC arg2Base col2.length).eval τ
      = (denseLayout nS W mS).head (t + 1) p' := by
  have e0 : (ctlCell lvJ0).eval τ = t :=
    ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0
  have e1 : (ctlCell lvJ1).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0
  have ea := transArg2E_value M arg2Base mC t p qi ai τ col2 hF h0 hai hw
  unfold transHeadMoveEGen
  rw [denseHeadE_eval]
  simp only [Expr.eval, e0, e1, ea]
  rw [hp']

/-! ## Layout-stride/count-separated leaf program -/

/-- One transition leaf with separate layout strides, state guard, and table-row stride. -/
def transLeafProgGen (nS W mS nC mC kindBase arg1Base arg2Base lenk len1 len2 : ℕ) : Program :=
  .ifNZ (.eq (transKindE kindBase lenk mC) (.const 0))
    (.seq (.seq
      (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
        (transCellE nS W mS) (transStateSameE nS W mS)))
      (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
        (transCellE nS W mS) (transHeadSameE nS W mS))))
      (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
        (transCellE nS W mS) (transCellSameE nS W mS))))
    (.ifNZ (.eq (transKindE kindBase lenk mC) (.const 1))
      (.ifNZ (.lt (transArg1E arg1Base len1 mC) (.const nC))
        (.seq (.seq
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base len1)))
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transHeadSameE nS W mS))))
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transCellWriteEGen nS W mS mC arg2Base len2))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS))))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))))
      (.ifNZ (.lt (transArg1E arg1Base len1 mC) (.const nC))
        (.ifNZ (moveOkE W (ctlCell lvJ1) (transArg2E arg2Base len2 mC))
          (.seq (.seq
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base len1)))
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transHeadMoveEGen nS W mS mC arg2Base len2))))
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transCellSameE nS W mS))))
          (.seq (.seq
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS)))
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS))))
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS)))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS))))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS))))))

lemma trans_leaf_prog_gen_self (n W m kindBase arg1Base arg2Base lenk len1 len2 : ℕ) :
    transLeafProgGen n W m n m kindBase arg1Base arg2Base lenk len1 len2
      = transLeafProg n W m kindBase arg1Base arg2Base lenk len1 len2 := by
  rfl

lemma trans_accept_write_writer_gen
    (M nS W mS mC t p qi ai kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base col1.length)))
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transHeadSameE nS W mS))))
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transCellWriteEGen nS W mS mC arg2Base col2.length))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0))] := by
  have hbpos1 : 1 ≤ arg1Base := by have : ctlJmax = 7 := rfl; omega
  have hbpos2 : 1 ≤ arg2Base := by have : ctlJmax = 7 := rfl; omega
  refine trans_imply3_block_writer M nS W mS t p qi ai kindBase colk arg1Base col1
    arg2Base col2 (transStateNextEGen nS W mS mC arg1Base col1.length)
    (transHeadSameE nS W mS) (transCellWriteEGen nS W mS mC arg2Base col2.length)
    ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0))
    ((denseLayout nS W mS).head (t + 1) p)
    ((denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0))
    hbasek hw1below hw2below ?_ ?_ ?_ ?_ ?_ ?_
  · intro bound σ σ' hσ hσ' hbound hagree
    exact trans_state_next_e_gen_frame M nS W mS mC arg1Base col1.length bound σ σ' hσ hσ'
      (wordBelow_transJmax_arg1 M kindBase colk.length arg1Base col1.length arg2Base col2.length
        bound hbpos1 hbound) hw1below hagree
  · intro bound σ σ' hσ hσ' hbound hagree
    exact ctl_frame_below M ctlJmax wpJ (transHeadSameE nS W mS)
      (fun σ σ' hσ hσ' h => transHeadSameE_frame M nS W mS σ σ' hσ hσ' h)
      bound σ σ' hσ hσ'
      (transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound) hagree
  · intro bound σ σ' hσ hσ' hbound hagree
    exact trans_cell_write_e_gen_frame M nS W mS mC arg2Base col2.length bound σ σ' hσ hσ'
      (wordBelow_transJmax_arg2 M kindBase colk.length arg1Base col1.length arg2Base col2.length
        bound hbpos2 hbound) hw2below hagree
  · intro τ hF h0
    exact trans_state_next_e_gen_value M nS W mS mC arg1Base t p qi ai τ col1
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg1 M _ _ _ _ _ _ _ τ hF)
  · intro τ hF h0
    exact transHeadSameE_value M nS W mS t p qi τ
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF)) h0
  · intro τ hF h0
    exact trans_cell_write_e_gen_value M nS W mS mC arg2Base t p qi ai τ col2
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg2 M _ _ _ _ _ _ _ τ hF)

lemma trans_accept_move_writer_gen
    (M nS W mS mC t p qi ai kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (p' : ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base)
    (hp' : p' = p + col2.getD (qi * mC + ai) 0 - (1 - col2.getD (qi * mC + ai) 0)) :
    ClauseWriter (.seq (.seq
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base col1.length)))
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transHeadMoveEGen nS W mS mC arg2Base col2.length))))
        (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
          (transCellE nS W mS) (transCellSameE nS W mS))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)
        ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p'),
       imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).cell (t + 1) p ai)] := by
  have hbpos1 : 1 ≤ arg1Base := by have : ctlJmax = 7 := rfl; omega
  have hbpos2 : 1 ≤ arg2Base := by have : ctlJmax = 7 := rfl; omega
  refine trans_imply3_block_writer M nS W mS t p qi ai kindBase colk arg1Base col1
    arg2Base col2 (transStateNextEGen nS W mS mC arg1Base col1.length)
    (transHeadMoveEGen nS W mS mC arg2Base col2.length) (transCellSameE nS W mS)
    ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0))
    ((denseLayout nS W mS).head (t + 1) p') ((denseLayout nS W mS).cell (t + 1) p ai)
    hbasek hw1below hw2below ?_ ?_ ?_ ?_ ?_ ?_
  · intro bound σ σ' hσ hσ' hbound hagree
    exact trans_state_next_e_gen_frame M nS W mS mC arg1Base col1.length bound σ σ' hσ hσ'
      (wordBelow_transJmax_arg1 M kindBase colk.length arg1Base col1.length arg2Base col2.length
        bound hbpos1 hbound) hw1below hagree
  · intro bound σ σ' hσ hσ' hbound hagree
    exact trans_head_move_e_gen_frame M nS W mS mC arg2Base col2.length bound σ σ' hσ hσ'
      (wordBelow_transJmax_arg2 M kindBase colk.length arg1Base col1.length arg2Base col2.length
        bound hbpos2 hbound) hw2below hagree
  · intro bound σ σ' hσ hσ' hbound hagree
    exact ctl_frame_below M ctlJmax wpJ (transCellSameE nS W mS)
      (fun σ σ' hσ hσ' h => transCellSameE_frame M nS W mS σ σ' hσ hσ' h)
      bound σ σ' hσ hσ'
      (transJM_bound_ctl M kindBase colk arg1Base col1 arg2Base col2 bound hbound) hagree
  · intro τ hF h0
    exact trans_state_next_e_gen_value M nS W mS mC arg1Base t p qi ai τ col1
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg1 M _ _ _ _ _ _ _ τ hF)
  · intro τ hF h0
    exact trans_head_move_e_gen_value M nS W mS mC arg2Base t p qi ai p' τ col2
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg2 M _ _ _ _ _ _ _ τ hF) hp'
  · intro τ hF h0
    exact transCellSameE_value M nS W mS t p qi τ ai
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))

lemma trans_leaf_write_branch_writer_gen
    (M nS W mS nC mC t p qi ai kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (.ifNZ (.lt (transArg1E arg1Base col1.length mC) (.const nC))
        (.seq (.seq
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base col1.length)))
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transHeadSameE nS W mS))))
          (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS) (transCellWriteEGen nS W mS mC arg2Base col2.length))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS))))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
        (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)) := by
  have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
      (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)
      = if col1.getD (qi * mC + ai) 0 < nC then
          [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)
            ((denseLayout nS W mS).state (t + 1) (col1.getD (qi * mC + ai) 0)),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)
            ((denseLayout nS W mS).cell (t + 1) p (col2.getD (qi * mC + ai) 0))]
        else
          [forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai),
           forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai),
           forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai)] := by
    unfold natTransClausesTriple
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  rw [heq]
  refine clauseWriter_ifNZ _ _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
    (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _
    (col1.getD (qi * mC + ai) 0 < nC) ?_ ?_ ?_
  · intro τ hF h0
    have hval := transArg1E_value M arg1Base mC t p qi ai τ col1
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg1 M _ _ _ _ _ _ _ τ hF)
    simp only [Expr.eval, hval]
    by_cases hlt : col1.getD (qi * mC + ai) 0 < nC <;> simp
  · intro hlt
    rw [ite_eq_left hlt]
    exact trans_accept_write_writer_gen M nS W mS mC t p qi ai kindBase arg1Base arg2Base
      colk col1 col2 hbasek hw1below hw2below
  · intro hnlt
    rw [ite_eq_right hnlt]
    exact trans_forbid3_block_writer M nS W mS t p qi ai kindBase colk arg1Base col1 arg2Base col2
      hbasek hw1below hw2below

lemma trans_leaf_move_branch_writer_gen
    (M nS W mS nC mC t p qi ai kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (.ifNZ (.lt (transArg1E arg1Base col1.length mC) (.const nC))
        (.ifNZ (moveOkE W (ctlCell lvJ1) (transArg2E arg2Base col2.length mC))
          (.seq (.seq
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transStateNextEGen nS W mS mC arg1Base col1.length)))
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transHeadMoveEGen nS W mS mC arg2Base col2.length))))
            (writeClauseProg wpJ (imply3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS) (transCellSameE nS W mS))))
          (.seq (.seq
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS)))
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS))))
            (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
              (transCellE nS W mS)))))
        (.seq (.seq
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS))))
          (writeClauseProg wpJ (forbid3Lits (transStateE nS W mS) (transHeadE nS W mS)
            (transCellE nS W mS)))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 2
        (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0)) := by
  unfold natTransClausesTriple
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine clauseWriter_ifNZ _ _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
    (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _
    (col1.getD (qi * mC + ai) 0 < nC) ?_ ?_ ?_
  · intro τ hF h0
    have hval := transArg1E_value M arg1Base mC t p qi ai τ col1
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_arg1 M _ _ _ _ _ _ _ τ hF)
    simp only [Expr.eval, hval]
    by_cases hlt : col1.getD (qi * mC + ai) 0 < nC <;> simp
  · intro hlt
    rw [ite_eq_left hlt]
    refine clauseWriter_ifNZ _ _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _
      (moveOk W p (col2.getD (qi * mC + ai) 0) ≠ 0) ?_ ?_ ?_
    · intro τ hF h0
      rw [moveOkE_eval]
      have ep : (ctlCell lvJ1).eval τ = p :=
        ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3])
          (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ
            (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF)) h0
      rw [ep, transArg2E_value M arg2Base mC t p qi ai τ col2
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ
          (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
        h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
          (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
        (pinsAndWords3_arg2 M _ _ _ _ _ _ _ τ hF)]
    · intro hok
      rw [ite_eq_left hok]
      exact trans_accept_move_writer_gen M nS W mS mC t p qi ai kindBase arg1Base arg2Base
        colk col1 col2 (p + col2.getD (qi * mC + ai) 0 - (1 - col2.getD (qi * mC + ai) 0))
        hbasek hw1below hw2below rfl
    · intro hnok
      rw [ite_eq_right hnok]
      exact trans_forbid3_block_writer M nS W mS t p qi ai kindBase colk arg1Base col1
        arg2Base col2 hbasek hw1below hw2below
  · intro hnlt
    rw [ite_eq_right hnlt]
    exact trans_forbid3_block_writer M nS W mS t p qi ai kindBase colk arg1Base col1
      arg2Base col2 hbasek hw1below hw2below

lemma trans_leaf_writer_gen
    (M nS W mS nC mC t p qi ai kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
        colk.length col1.length col2.length)
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2)
      (natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
        (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
        (col2.getD (qi * mC + ai) 0)) := by
  unfold transLeafProgGen
  refine clauseWriter_ifNZ _ _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
    (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _
    (colk.getD (qi * mC + ai) 0 = 0) ?_ ?_ ?_
  · intro τ hF h0
    have hval := transKindE_value M kindBase mC t p qi ai τ colk
      (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
        (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
      (pinsAndWords3_kind M _ _ _ _ _ _ _ τ hF)
    simp only [Expr.eval, hval]
    by_cases h : colk.getD (qi * mC + ai) 0 = 0 <;> simp
  · intro hk0
    have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
        (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
        (col2.getD (qi * mC + ai) 0)
        = [imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).state (t + 1) qi),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).head (t + 1) p),
           imply3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
            ((denseLayout nS W mS).cell t p ai) ((denseLayout nS W mS).cell (t + 1) p ai)] := by
      unfold natTransClausesTriple
      rw [ite_eq_left hk0]
    rw [heq]
    exact trans_accept_halt_writer M nS W mS t p qi ai kindBase colk arg1Base col1 arg2Base col2
      hbasek hw1below hw2below
  · intro hkn0
    refine clauseWriter_ifNZ _ _ _ M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (transLeafPins t p qi ai) kindBase colk arg1Base col1 arg2Base col2) _
      (colk.getD (qi * mC + ai) 0 = 1) ?_ ?_ ?_
    · intro τ hF h0
      have hval := transKindE_value M kindBase mC t p qi ai τ colk
        (pinsHold_tail M (lvJ3, ai) (ctlPins3 t p qi) τ
          (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
        h0 (pinsHold_head M (lvJ3, ai) (ctlPins3 t p qi) τ
          (pinsAndWords3_pins M _ _ _ _ _ _ _ τ hF))
        (pinsAndWords3_kind M _ _ _ _ _ _ _ τ hF)
      simp only [Expr.eval, hval]
      by_cases h : colk.getD (qi * mC + ai) 0 = 1 <;> simp
    · intro hk1
      have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)
          = natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 1
              (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) := by rw [hk1]
      rw [heq]
      exact trans_leaf_write_branch_writer_gen M nS W mS nC mC t p qi ai kindBase
        arg1Base arg2Base colk col1 col2 hbasek hw1below hw2below
    · intro hkn1
      have heq : natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)
          = natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai 2
              (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) :=
        natTransClausesTriple_of_ge2 (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0) hkn0 hkn1
      rw [heq]
      exact trans_leaf_move_branch_writer_gen M nS W mS nC mC t p qi ai kindBase
        arg1Base arg2Base colk col1 col2 hbasek hw1below hw2below

lemma trans_ai_loop_writer_gen
    (M nS W mS nC mC t p qi kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (loopProg lvJ3 (.const mC)
        (.seq (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
            colk.length col1.length col2.length)
          (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (ctlPins3 t p qi) kindBase colk arg1Base col1 arg2Base col2)
      ((List.range mC).flatMap fun ai =>
        natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)) := by
  have hJ : ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
    transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2
  have hpin : ∀ q ∈ ctlPins3 t p qi,
      1 ≤ q.1 ∧ q.1 ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 ∧
        q.1 ≠ lvJ3 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins3_ok t p qi lvJ3 (by unfold lvJ0 lvJ3; omega)
      (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega) q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  refine clauseWriter_forN_words3 _ M (transJM M kindBase colk arg1Base col1 arg2Base col2)
    wpJ lvJ3 (ctlPins3 t p qi) _ (.const mC) mC kindBase colk arg1Base col1 arg2Base col2
    (by unfold lvJ3; omega) (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hJ)
    (by unfold lvJ3 wpJ; omega) (le_refl lvJ3) hpin hbasek hw1below hw2below
    ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M
    (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ lvJ3 (ctlPins3 t p qi) _
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ3; omega)
    (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hJ) (by unfold lvJ3 wpJ; omega)
    (le_refl lvJ3) hpin hbasek hw1below hw2below
    (fun ai => trans_leaf_writer_gen M nS W mS nC mC t p qi ai kindBase arg1Base arg2Base
      colk col1 col2 hbasek hw1below hw2below)

lemma trans_qi_loop_writer_gen
    (M nS W mS nC mC t p kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (loopProg lvJ2 (.const nC)
        (.seq (loopProg lvJ3 (.const mC)
            (.seq (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
                colk.length col1.length col2.length)
              (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (ctlPins2 t p) kindBase colk arg1Base col1 arg2Base col2)
      ((List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)) := by
  have hJ : ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
    transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2
  have hpin : ∀ q ∈ ctlPins2 t p,
      1 ≤ q.1 ∧ q.1 ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 ∧
        q.1 ≠ lvJ2 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins2_ok t p lvJ2 (by unfold lvJ0 lvJ2; omega)
      (by unfold lvJ1 lvJ2; omega) q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  refine clauseWriter_forN_words3 _ M (transJM M kindBase colk arg1Base col1 arg2Base col2)
    wpJ lvJ2 (ctlPins2 t p) _ (.const nC) nC kindBase colk arg1Base col1 arg2Base col2
    (by unfold lvJ2; omega) (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hJ)
    (by unfold lvJ2 wpJ; omega) (by unfold lvJ2 lvJ3; omega) hpin
    hbasek hw1below hw2below ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M
    (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ lvJ2 (ctlPins2 t p) _
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ2; omega)
    (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hJ) (by unfold lvJ2 wpJ; omega)
    (by unfold lvJ2 lvJ3; omega) hpin hbasek hw1below hw2below
    (fun qi => trans_ai_loop_writer_gen M nS W mS nC mC t p qi kindBase arg1Base arg2Base
      colk col1 col2 hbasek hw1below hw2below)

lemma trans_p_loop_writer_gen
    (M nS W mS nC mC t kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (loopProg lvJ1 (.const W)
        (.seq (loopProg lvJ2 (.const nC)
            (.seq (loopProg lvJ3 (.const mC)
                (.seq (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
                    colk.length col1.length col2.length)
                  (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ
      (TransFrozen M (ctlPins1 t) kindBase colk arg1Base col1 arg2Base col2)
      ((List.range W).flatMap fun p =>
        (List.range nC).flatMap fun qi =>
          (List.range mC).flatMap fun ai =>
            natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0)) := by
  have hJ : ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
    transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2
  have hpin : ∀ q ∈ ctlPins1 t,
      1 ≤ q.1 ∧ q.1 ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 ∧
        q.1 ≠ lvJ1 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins1_ok t lvJ1 (by unfold lvJ0 lvJ1; omega) q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  refine clauseWriter_forN_words3 _ M (transJM M kindBase colk arg1Base col1 arg2Base col2)
    wpJ lvJ1 (ctlPins1 t) _ (.const W) W kindBase colk arg1Base col1 arg2Base col2
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hJ)
    (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega) hpin
    hbasek hw1below hw2below ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M
    (transJM M kindBase colk arg1Base col1 arg2Base col2) wpJ lvJ1 (ctlPins1 t) _
    kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ1; omega)
    (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hJ) (by unfold lvJ1 wpJ; omega)
    (by unfold lvJ1 lvJ3; omega) hpin hbasek hw1below hw2below
    (fun p => trans_qi_loop_writer_gen M nS W mS nC mC t p kindBase arg1Base arg2Base
      colk col1 col2 hbasek hw1below hw2below)

/-- Raw numeric-column form of the transition family with independent counts. -/
def transClausesTripleFamily (v : ExecVarLayout) (nC W mC T : ℕ)
    (colk col1 col2 : List ℕ) : List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun p =>
      (List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple v nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)

lemma trans_clauses_triple_family_eq_desc (nS W mS T : ℕ) (d : TableauDescriptor) :
    transClausesTripleFamily (denseLayout nS W mS) d.numStates W d.numLetters T
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
      = descTransClauses (denseLayout nS W mS) d W T := by
  unfold transClausesTripleFamily descTransClauses
  simp_rw [transKind_col_getD_eq, transArg1_col_getD_eq, transArg2_col_getD_eq,
    natTransClausesTriple_transOf]

/-- The transition program with independent layout strides and iteration counts. -/
def transFamilyProgGen (nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base : ℕ) : Program :=
  loopProg lvJ0 (.const T)
    (.seq (loopProg lvJ1 (.const W)
      (.seq (loopProg lvJ2 (.const nC)
        (.seq (loopProg lvJ3 (.const mC)
          (.seq (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
            (d.table.map transKind).length (d.table.map transArg1).length
            (d.table.map transArg2).length)
            (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
        (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

/-- The transition family's program, as in `transFamilyProg_writer`. -/
def transFamilyProg (n W m T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base : ℕ) : Program :=
  transFamilyProgGen n W m n m T d kindBase arg1Base arg2Base

/-- The transition family with independent layout strides and iteration counts. -/
lemma transFamilyProgGen_writer_gen (M nS W mS nC mC T : ℕ)
    (kindBase arg1Base arg2Base : ℕ) (d : TableauDescriptor)
    (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (loopProg lvJ0 (.const T)
        (.seq (loopProg lvJ1 (.const W)
            (.seq (loopProg lvJ2 (.const nC)
                (.seq (loopProg lvJ3 (.const mC)
                    (.seq (transLeafProgGen nS W mS nC mC kindBase arg1Base arg2Base
                        (d.table.map transKind).length (d.table.map transArg1).length
                        (d.table.map transArg2).length)
                      (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
                  (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
              (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
          arg2Base (d.table.map transArg2)) wpJ
      (TransFrozen M ctlPins0 kindBase (d.table.map transKind) arg1Base
        (d.table.map transArg1) arg2Base (d.table.map transArg2))
      (transClausesTripleFamily (denseLayout nS W mS) nC W mC T
        (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)) := by
  unfold transClausesTripleFamily
  have hJ : ctlJmax ≤ transJM M kindBase (d.table.map transKind) arg1Base
      (d.table.map transArg1) arg2Base (d.table.map transArg2) :=
    transJM_ge_ctl M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2)
  refine clauseWriter_forN_words3 _ M
    (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2)) wpJ lvJ0 ctlPins0 _ (.const T) T kindBase
    (d.table.map transKind) arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2)
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    (fun p hp => absurd hp List.not_mem_nil) hbasek hw1below hw2below
    ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_words3 _ M
    (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2)) wpJ lvJ0 ctlPins0 _ kindBase
    (d.table.map transKind) arg1Base (d.table.map transArg1) arg2Base (d.table.map transArg2)
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    (fun p hp => absurd hp List.not_mem_nil) hbasek hw1below hw2below
    (fun t => trans_p_loop_writer_gen M nS W mS nC mC t kindBase arg1Base arg2Base
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2)
      hbasek hw1below hw2below)

/-! ## The `t` loop, closing the whole family -/

/-- The full transition family, as a `ClauseWriter`.  Its clause list is
`descTransClauses (denseLayout n W m) d W T`, the family's own definition, once
`d.numStates = n` and `d.numLetters = m`.  The dense layout supplies the variable
numbering, while descriptor `d` supplies the transition table.  The three table
columns are carried in `Frozen` as `TransFrozen`, so the writer's own correctness
does not depend on any store holding them — only the stores it actually runs on
need to. -/
lemma transFamilyProg_writer (M n W m T : ℕ) (kindBase arg1Base arg2Base : ℕ)
    (d : TableauDescriptor) (hn : d.numStates = n) (hm : d.numLetters = m)
    (hbasek : M + ctlJmax < kindBase)
    (hw1below : M + ctlJmax < arg1Base) (hw2below : M + ctlJmax < arg2Base) :
    ClauseWriter (loopProg lvJ0 (.const T)
        (.seq (loopProg lvJ1 (.const W)
            (.seq (loopProg lvJ2 (.const n)
                (.seq (loopProg lvJ3 (.const m)
                    (.seq (transLeafProg n W m kindBase arg1Base arg2Base
                        (d.table.map transKind).length (d.table.map transArg1).length
                        (d.table.map transArg2).length)
                      (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
                  (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
              (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
          (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1)))))
      M (transJM M kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
          arg2Base (d.table.map transArg2)) wpJ
      (TransFrozen M ctlPins0 kindBase (d.table.map transKind) arg1Base
        (d.table.map transArg1) arg2Base (d.table.map transArg2))
      (descTransClauses (denseLayout n W m) d W T) := by
  subst n
  subst m
  simpa only [trans_leaf_prog_gen_self, trans_clauses_triple_family_eq_desc] using
    transFamilyProgGen_writer_gen M d.numStates W d.numLetters d.numStates d.numLetters T
      kindBase arg1Base arg2Base d hbasek hw1below hw2below

end NPComplete.CookLevin

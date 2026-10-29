module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedCore

/-!
The write primitives are where the two envelopes first meet.  A literal write
stores a tag and a variable number at the pointer and then advances the pointer,
so its boundedness needs the pointer's own value bounded — the syntax envelope
has to reach past the end of the clause table, not merely past the variable
numbers.  Its *effect* on the envelopes is the opposite direction: everything it
writes lands at or above the pointer, so the control cells the dense expressions
multiply come through untouched.

That asymmetry is why the statements here separate the two obligations.  The
`programBoundedIn_*` lemmas take an expression bound and give a program bound;
the `*_preserves` lemmas take the tight envelope and give it back.  Families
combine them through `ClauseWriterBounded`, whose conclusion is exactly that
pair.

The second literal expression is evaluated against the store the tag write
already changed, which `writeLitProg_eval_state` also has to account for.  Rather
than hide that behind a frame condition, the bound on the variable expression is
asked for at that store directly: every caller's variable numbers read control
cells, which the tag write leaves alone, so discharging it is a rewrite.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Control-cell addressing

`ctlAddr j` is `reg 0 + j`, so its bound is the workspace's own extent; `ctlCell`
additionally reads that address, which `ExprBoundedIn` charges as the address
value rather than the contents. -/

lemma exprBoundedIn_ctlAddr (B M j : ℕ) (σ : Store) (h0 : σ 0 = M)
    (hj : M + j ≤ B) : ExprBoundedIn B σ (ctlAddr j) := by
  unfold ctlAddr
  simp only [ExprBoundedIn, Expr.eval, h0]
  exact ⟨by omega, by omega, by omega⟩

lemma ctlAddr_eval_at (M j : ℕ) (σ : Store) (h0 : σ 0 = M) :
    (ctlAddr j).eval σ = M + j := by simp only [ctlAddr, Expr.eval, h0]

lemma exprBoundedIn_ctlCell (B M j : ℕ) (σ : Store) (h0 : σ 0 = M)
    (hj : M + j ≤ B) : ExprBoundedIn B σ (ctlCell j) :=
  ⟨exprBoundedIn_ctlAddr B M j σ h0 hj, by rw [ctlAddr_eval_at M j σ h0]; omega⟩

/-- A counter or pointer bump.  The value written is the cell's own contents plus
    a compile-time constant, so the bound is on where the cell will land. -/
lemma programBoundedIn_ctlAssign_bump (B M wp j c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj : M + j ≤ B) (hwp : σ (M + j) = wp) (hwpB : wp + c ≤ B) :
    ProgramBoundedIn B σ (ctlAssign j (.add (ctlCell j) (.const c))) := by
  unfold ctlAssign
  refine ⟨exprBoundedIn_ctlAddr B M j σ h0 hj, ?_, by rw [ctlAddr_eval_at M j σ h0]; omega⟩
  refine ⟨exprBoundedIn_ctlCell B M j σ h0 hj, by simp only [ExprBoundedIn]; omega, ?_⟩
  simp only [Expr.eval, ctlCell, ctlAddr, h0, hwp]
  omega

/-- A counter reset. -/
lemma programBoundedIn_ctlAssign_const (B M j c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj : M + j ≤ B) (hc : c ≤ B) :
    ProgramBoundedIn B σ (ctlAssign j (.const c)) := by
  unfold ctlAssign
  exact ⟨exprBoundedIn_ctlAddr B M j σ h0 hj, by simp only [ExprBoundedIn]; omega,
    by rw [ctlAddr_eval_at M j σ h0]; omega⟩

/-! ## One literal -/

/-- The tag write's store, named once so the variable expression's bound and the
    frame reasoning can both refer to it. -/
lemma writeLitProg_tag_store (M wp : ℕ) (σ : Store) (tagE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) :
    (Program.assignInd (ctlCell wpJ) tagE).eval σ = writeReg σ wp (tagE.eval σ) := by
  rw [eval_assignInd, ctlCell_eval, h0, hwp]

lemma programBoundedIn_writeLitProg (B M wp : ℕ) (σ : Store) (tagE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hwpB : wp + 2 ≤ B)
    (htag : ExprBoundedIn B σ tagE)
    (hvar : ExprBoundedIn B (writeReg σ wp (tagE.eval σ)) varE) :
    ProgramBoundedIn B σ (writeLitProg wpJ tagE varE) := by
  have hj : M + wpJ ≤ B := by simp only [wpJ]; omega
  have e1 := writeLitProg_tag_store M wp σ tagE h0 hwp
  have hσ10 : (writeReg σ wp (tagE.eval σ)) 0 = M := by
    rw [writeReg_diff σ wp _ 0 (by omega), h0]
  have hσ1w : (writeReg σ wp (tagE.eval σ)) (M + wpJ) = wp := by
    rw [writeReg_diff σ wp _ (M + wpJ) (by simp only [wpJ]; omega), hwp]
  have e2 : (Program.assignInd (.add (ctlCell wpJ) (.const 1)) varE).eval
        (writeReg σ wp (tagE.eval σ))
      = writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
          (varE.eval (writeReg σ wp (tagE.eval σ))) := by
    rw [eval_assignInd]; simp only [Expr.eval, ctlCell_eval, hσ10, hσ1w]
  have hσ20 : (writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
      (varE.eval (writeReg σ wp (tagE.eval σ)))) 0 = M := by
    rw [writeReg_diff _ (wp + 1) _ 0 (by omega), hσ10]
  have hσ2w : (writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
      (varE.eval (writeReg σ wp (tagE.eval σ)))) (M + wpJ) = wp := by
    rw [writeReg_diff _ (wp + 1) _ (M + wpJ) (by simp only [wpJ]; omega), hσ1w]
  unfold writeLitProg
  refine ⟨⟨⟨exprBoundedIn_ctlCell B M wpJ σ h0 hj, htag, ?_⟩, ?_⟩, ?_⟩
  · rw [ctlCell_eval, h0, hwp]; omega
  · rw [e1]
    refine ⟨⟨exprBoundedIn_ctlCell B M wpJ _ hσ10 hj,
      by simp only [ExprBoundedIn]; omega, ?_⟩, hvar, ?_⟩
    · simp only [Expr.eval, ctlCell_eval, hσ10, hσ1w]; omega
    · simp only [Expr.eval, ctlCell_eval, hσ10, hσ1w]; omega
  · rw [eval_seq, e1, e2]
    exact programBoundedIn_ctlAssign_bump B M wp wpJ 2 _ hσ20 hj hσ2w hwpB

/-! ## The store a literal write leaves

`writeLitProg_eval_state` describes the result cell by cell, but pays for it with
a side condition saying the variable expression does not see the tag write.  That
condition is semantic, and the bound side has no way to produce it: the whole
point of a syntax-wide bound is that it holds without knowing what the
expressions mean.  Computing the resulting store outright avoids the question —
the variable expression is simply evaluated where it is actually evaluated. -/

/-- The result of a literal write, with no side condition on the expressions. -/
lemma writeLitProg_eval_direct (M wp : ℕ) (σ : Store) (tagE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) :
    (writeLitProg wpJ tagE varE).eval σ
      = writeReg (writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
          (varE.eval (writeReg σ wp (tagE.eval σ)))) (M + wpJ) (wp + 2) := by
  have e1 := writeLitProg_tag_store M wp σ tagE h0 hwp
  have hσ10 : (writeReg σ wp (tagE.eval σ)) 0 = M := by
    rw [writeReg_diff σ wp _ 0 (by omega), h0]
  have hσ1w : (writeReg σ wp (tagE.eval σ)) (M + wpJ) = wp := by
    rw [writeReg_diff σ wp _ (M + wpJ) (by simp only [wpJ]; omega), hwp]
  have e2 : (Program.assignInd (.add (ctlCell wpJ) (.const 1)) varE).eval
        (writeReg σ wp (tagE.eval σ))
      = writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
          (varE.eval (writeReg σ wp (tagE.eval σ))) := by
    rw [eval_assignInd]; simp only [Expr.eval, ctlCell_eval, hσ10, hσ1w]
  have hσ20 : (writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
      (varE.eval (writeReg σ wp (tagE.eval σ)))) 0 = M := by
    rw [writeReg_diff _ (wp + 1) _ 0 (by omega), hσ10]
  have hσ2w : (writeReg (writeReg σ wp (tagE.eval σ)) (wp + 1)
      (varE.eval (writeReg σ wp (tagE.eval σ)))) (M + wpJ) = wp := by
    rw [writeReg_diff _ (wp + 1) _ (M + wpJ) (by simp only [wpJ]; omega), hσ1w]
  unfold writeLitProg ctlAssign
  rw [eval_seq, eval_seq, e1, e2, eval_assignInd]
  simp only [Expr.eval, ctlAddr, ctlCell, hσ20, hσ2w]

/-- Everything the next literal needs on entry: the marker, the advanced pointer,
    and both envelopes. -/
lemma writeLitProg_exit (K S M wp : ℕ) (σ : Store) (tagE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (htagK : tagE.eval σ ≤ S)
    (hvarK : varE.eval (writeReg σ wp (tagE.eval σ)) ≤ S) (hwpK : wp + 2 ≤ S) :
    (writeLitProg wpJ tagE varE).eval σ 0 = M ∧
      (writeLitProg wpJ tagE varE).eval σ (M + wpJ) = wp + 2 ∧
      TightCells K M ((writeLitProg wpJ tagE varE).eval σ) ∧
      StoreValuesLe S ((writeLitProg wpJ tagE varE).eval σ) := by
  rw [writeLitProg_eval_direct M wp σ tagE varE h0 hwp hsep]
  set σ1 := writeReg σ wp (tagE.eval σ) with hs1
  set σ2 := writeReg σ1 (wp + 1) (varE.eval σ1) with hs2
  have h20 : σ2 0 = M := by
    rw [hs2, writeReg_diff _ (wp + 1) _ 0 (by omega), hs1,
      writeReg_diff σ wp _ 0 (by omega), h0]
  refine ⟨?_, writeReg_same _ _ _, ?_, fun i => ?_⟩
  · rw [writeReg_diff σ2 (M + wpJ) (wp + 2) 0 (by simp only [wpJ]; omega), h20]
  · refine tightCells_of_frame ht (fun j h2 h24 => ?_)
    rw [writeReg_diff σ2 (M + wpJ) (wp + 2) (M + j) (by simp only [wpJ]; omega), hs2,
      writeReg_diff σ1 (wp + 1) _ (M + j) (by omega), hs1,
      writeReg_diff σ wp _ (M + j) (by omega)]
  · by_cases hi : i = M + wpJ
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ2 (M + wpJ) (wp + 2) i hi, hs2]
      by_cases hi1 : i = wp + 1
      · rw [hi1, writeReg_same]; exact hvarK
      · rw [writeReg_diff σ1 (wp + 1) _ i hi1, hs1]
        by_cases hi2 : i = wp
        · rw [hi2, writeReg_same]; exact htagK
        · rw [writeReg_diff σ wp _ i hi2]; exact hst i

/-- Cells below the pointer, other than the pointer itself, are untouched.  This
    is the same frame `writeLitProg_eval_state` reports, but derived from the
    computed store, so it comes without that lemma's semantic side condition. -/
lemma writeLitProg_frame_below (M wp : ℕ) (σ : Store) (tagE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (r : ℕ) (hr : r < wp) (hrne : r ≠ M + wpJ) :
    (writeLitProg wpJ tagE varE).eval σ r = σ r := by
  rw [writeLitProg_eval_direct M wp σ tagE varE h0 hwp hsep,
    writeReg_diff _ (M + wpJ) (wp + 2) r hrne,
    writeReg_diff _ (wp + 1) _ r (by omega),
    writeReg_diff σ wp _ r (by omega)]

/-! ## Writes above the control block

Every payload cell a clause row occupies sits above the write pointer, which the
writer contracts already place above the control block.  So a single lemma covers
the effect all of them have on the envelopes, and the literal-list induction can
use it between literals as well as the families between clauses. -/

/-- A write above the control block preserves the marker, the tight cells, and
    the tight envelope. -/
lemma writeReg_above_preserves (K S M wp v : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hsep : M + 24 < wp) (ht : TightCells K M σ)
    (hst : StoreValuesLe S σ) (hv : v ≤ S) :
    (writeReg σ wp v) 0 = M ∧ TightCells K M (writeReg σ wp v) ∧
      StoreValuesLe S (writeReg σ wp v) := by
  refine ⟨by rw [writeReg_diff σ wp v 0 (by omega), h0],
    tightCells_of_frame ht (fun j h2 h24 => writeReg_diff σ wp v (M + j) (by omega)),
    fun i => ?_⟩
  by_cases hi : i = wp
  · rw [hi, writeReg_same]; exact hv
  · rw [writeReg_diff σ wp v i hi]; exact hst i

/-! ## Literal lists

A clause's literal expressions are asked for at *any* store with the right
control cells rather than at one named store.  That is what lets the same
hypothesis serve both writes of a literal — the variable expression is evaluated
after the tag write — and every later literal in the list, without a separate
frame condition per position. -/

/-- Every literal expression of a clause is bounded, and evaluates under the tight
    envelope, at any store with the marker and the tight cells. -/
def LitsBounded (K S B M : ℕ) (lits : List (Expr × Expr)) : Prop :=
  ∀ q ∈ lits, ∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
    ExprBoundedIn B τ q.1 ∧ ExprBoundedIn B τ q.2 ∧
      q.1.eval τ ≤ S ∧ q.2.eval τ ≤ S

lemma litsBounded_tail {K S B M : ℕ} {q : Expr × Expr} {rest : List (Expr × Expr)}
    (h : LitsBounded K S B M (q :: rest)) : LitsBounded K S B M rest :=
  fun p hp => h p (List.mem_cons_of_mem _ hp)

end NPComplete.CookLevin

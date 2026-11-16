module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck
public import NPComplete.CookLevin.Verifier.ThreeCNFEvalTop
public import NPComplete.CookLevin.Verifier.ThreeCNFEvalOuterBounded
public import NPComplete.CookLevin.Verifier.CNFEvalStages
public import NPComplete.RAMToTM.Generic.Api.ResStages

/-!
# Resource-carrying stage composition for the ThreeCNF evaluator

The second client of the `ResStages` combinators: the same resource composition shape as
`CNFEvalStages.lean` — value-bounds facts carried across the prefix seeds and unary decoders,
the clause-count loop's per-visit budgets read off the loop invariant — written from
`StageSpec.assign_const_carry`, `StageSpec.decodeUnaryAt` and `StageSpec.forN_le` alone.  The
fixed-arity clause step (`remaining := 3`, constant-count literal loop) shares the literal
leaf (`programBoundedIn_decodeClauseEvalStepAt_of_local_bounds`) with `CNFEvalStages`; only
the budget arithmetic and the frame/growth lemmas are system-specific.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip ReadsOnly)
open NPComplete.BoundedWhile (RegLayout LayoutFact Separates RegsLe)

stage_default boundary

/-- The local resource facts of one ThreeCNF-evaluator store: the budget cells are bounded by
`B` (`ValuesLeOn`) and pinned to the entry store's `wBase`/`bound`/`cursor` values. -/
@[stage_impl] def decodeThreeCNFEvalResBounds (B cursorReg wBaseReg boundReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg
    ∧ τ boundReg = σ boundReg ∧ τ cursorReg = σ cursorReg

/-! ## The ThreeCNF evaluator's necessary-separation core

The same shape as `CNFEvalStages.lean`: one proof body per lemma against a role assignment,
the numbered statement a wrapper that assembles the evidence from its own hypotheses, and a
layout version that supplies it wholesale. -/

/-- The register roles the ThreeCNF evaluator's stages name. -/
inductive ThreeCNFEvalRole where
  | cursor | pol | var | done | outer | remaining | sat | bit | val | wBase | cnf | bound
  | numVarsSkip
  deriving DecidableEq

/-- The register pairs the ThreeCNF clause step's resource proof separates, in the order of
the numbered statement's distinctness hypotheses. -/
def threeStepPairs : List (ThreeCNFEvalRole × ThreeCNFEvalRole) :=
  [(.cursor, .pol), (.cursor, .var), (.cursor, .done), (.var, .done), (.bound, .cursor),
    (.bound, .pol), (.bound, .var), (.bound, .done), (.remaining, .cursor), (.cursor, .bit),
    (.cursor, .val), (.bound, .remaining), (.bound, .bit), (.bound, .val), (.cursor, .wBase),
    (.pol, .wBase), (.var, .wBase), (.done, .wBase), (.remaining, .wBase), (.bit, .wBase),
    (.val, .wBase), (.remaining, .var), (.remaining, .pol), (.remaining, .done),
    (.remaining, .bit), (.remaining, .val), (.sat, .cursor), (.sat, .done), (.sat, .remaining),
    (.sat, .bound), (.sat, .wBase)]

/-- The roles the ThreeCNF clause step's resource proof indexes. -/
def threeStepUsed : Set ThreeCNFEvalRole :=
  {.cursor, .pol, .var, .done, .remaining, .sat, .bit, .val, .wBase, .cnf, .bound}

/-- The clause-step budgets at one store: the fixed loop count fits, the `wBase` budget and
the inner-loop budget. -/
def threeStepBudgets (B c wBase bound : ℕ) : Prop :=
  (3:ℕ) ≤ B ∧ wBase + bound ≤ B ∧ c + 3 * (bound + 1) + 1 + bound ≤ B

lemma threeStepBudgets.three {B c wBase bound : ℕ} (h : threeStepBudgets B c wBase bound) :
    (3:ℕ) ≤ B :=
  h.1

lemma threeStepBudgets.wb {B c wBase bound : ℕ} (h : threeStepBudgets B c wBase bound) :
    wBase + bound ≤ B :=
  h.2.1

lemma threeStepBudgets.inner {B c wBase bound : ℕ} (h : threeStepBudgets B c wBase bound) :
    c + 3 * (bound + 1) + 1 + bound ≤ B :=
  h.2.2

/-- The program's budgets at one store. -/
def threeProgramBudgets (B c wBase bound : ℕ) : Prop :=
  wBase + bound ≤ B ∧ (3:ℕ) ≤ B ∧
    c + 2 * bound + bound * (3 * (bound + 1)) + 3 * (bound + 1) + 1 + bound ≤ B

lemma threeProgramBudgets.wb {B c wBase bound : ℕ} (h : threeProgramBudgets B c wBase bound) :
    wBase + bound ≤ B :=
  h.1

lemma threeProgramBudgets.three {B c wBase bound : ℕ} (h : threeProgramBudgets B c wBase bound) :
    (3:ℕ) ≤ B :=
  h.2.1

lemma threeProgramBudgets.outerCoarse {B c wBase bound : ℕ}
    (h : threeProgramBudgets B c wBase bound) :
    c + 2 * bound + bound * (3 * (bound + 1)) + 3 * (bound + 1) + 1 + bound ≤ B :=
  h.2.2

/-- The pairs of `threeStepPairs` are pairs of distinct roles. -/
lemma threeStepPairs_ne (a b : ThreeCNFEvalRole) (h : (a, b) ∈ threeStepPairs) : a ≠ b := by
  simp only [threeStepPairs, List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
  all_goals first | decide | nomatch hm

/-- The ThreeCNF clause step's resource body at a role assignment. -/
@[stage_impl] lemma programBoundedIn_decodeThreeCNFEvalClauseStepAt_core
    (B : ℕ) (reg : ThreeCNFEvalRole → ℕ) (σ : Store)
    (hsep : Separates reg threeStepPairs) (hidx : RegsLe reg threeStepUsed B)
    (hb : threeStepBudgets B (σ (reg .cursor)) (σ (reg .wBase)) (σ (reg .bound))) :
    ProgramBoundedIn B σ
      (decodeThreeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf)
        (reg .bound)) := by
  rcases hb with ⟨h3, hwbudget, hinner⟩
  rcases (⟨hidx .cursor (by simp [threeStepUsed]), hidx .pol (by simp [threeStepUsed]), hidx .var (by simp [threeStepUsed]), hidx .done (by simp [threeStepUsed]), hidx .remaining (by simp [threeStepUsed]), hidx .sat (by simp [threeStepUsed]), hidx .bit (by simp [threeStepUsed]), hidx .val (by simp [threeStepUsed]), hidx .wBase (by simp [threeStepUsed]), hidx .cnf (by simp [threeStepUsed]), hidx .bound (by simp [threeStepUsed])⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
  rcases (⟨hsep .cursor .pol (by decide : (.cursor, .pol) ∈ threeStepPairs), hsep .cursor .var (by decide : (.cursor, .var) ∈ threeStepPairs), hsep .cursor .done (by decide : (.cursor, .done) ∈ threeStepPairs), hsep .var .done (by decide : (.var, .done) ∈ threeStepPairs), hsep .bound .cursor (by decide : (.bound, .cursor) ∈ threeStepPairs), hsep .bound .pol (by decide : (.bound, .pol) ∈ threeStepPairs), hsep .bound .var (by decide : (.bound, .var) ∈ threeStepPairs), hsep .bound .done (by decide : (.bound, .done) ∈ threeStepPairs), hsep .remaining .cursor (by decide : (.remaining, .cursor) ∈ threeStepPairs), hsep .cursor .bit (by decide : (.cursor, .bit) ∈ threeStepPairs), hsep .cursor .val (by decide : (.cursor, .val) ∈ threeStepPairs), hsep .bound .remaining (by decide : (.bound, .remaining) ∈ threeStepPairs), hsep .bound .bit (by decide : (.bound, .bit) ∈ threeStepPairs), hsep .bound .val (by decide : (.bound, .val) ∈ threeStepPairs), hsep .cursor .wBase (by decide : (.cursor, .wBase) ∈ threeStepPairs), hsep .pol .wBase (by decide : (.pol, .wBase) ∈ threeStepPairs), hsep .var .wBase (by decide : (.var, .wBase) ∈ threeStepPairs), hsep .done .wBase (by decide : (.done, .wBase) ∈ threeStepPairs), hsep .remaining .wBase (by decide : (.remaining, .wBase) ∈ threeStepPairs), hsep .bit .wBase (by decide : (.bit, .wBase) ∈ threeStepPairs), hsep .val .wBase (by decide : (.val, .wBase) ∈ threeStepPairs), hsep .remaining .var (by decide : (.remaining, .var) ∈ threeStepPairs), hsep .remaining .pol (by decide : (.remaining, .pol) ∈ threeStepPairs), hsep .remaining .done (by decide : (.remaining, .done) ∈ threeStepPairs), hsep .remaining .bit (by decide : (.remaining, .bit) ∈ threeStepPairs), hsep .remaining .val (by decide : (.remaining, .val) ∈ threeStepPairs), hsep .sat .cursor (by decide : (.sat, .cursor) ∈ threeStepPairs), hsep .sat .done (by decide : (.sat, .done) ∈ threeStepPairs), hsep .sat .remaining (by decide : (.sat, .remaining) ∈ threeStepPairs), hsep .sat .bound (by decide : (.sat, .bound) ∈ threeStepPairs), hsep .sat .wBase (by decide : (.sat, .wBase) ∈ threeStepPairs)⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hrc, hcbit, hcval, hbr, hbb, hbval, hcw, hpw, hvw, hdw, hrw, hbw, hvalw, hrv, hrp, hrd, hrbit, hrval, hsc, hsd, hsr, hsb, hsw⟩
  have hstep : ProgramBoundedIn B σ
      (decodeThreeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat) (reg .bit)
        (reg .val) (reg .wBase) (reg .bound)) := by
    unfold decodeThreeClauseEvalStepAt
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    refine ⟨⟨hri, h3⟩, ⟨⟨hsi, Nat.zero_le B⟩, ?_⟩⟩
    set σ1 := (Program.assign (reg .sat) (.const 0)).eval
      ((Program.assign (reg .remaining) (.const 3)).eval σ) with hσ1def
    have hσ1rem : σ1 (reg .remaining) = 3 := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ (reg .sat) 0 (reg .remaining) hsr.symm,
        eval_assign, Expr.eval, writeReg_same]
    have hσ1cur : σ1 (reg .cursor) = σ (reg .cursor) := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ (reg .sat) 0 (reg .cursor) hsc.symm, eval_assign, Expr.eval,
        writeReg_diff _ (reg .remaining) 3 (reg .cursor) hrc.symm]
    have hσ1bnd : σ1 (reg .bound) = σ (reg .bound) := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ (reg .sat) 0 (reg .bound) hsb.symm, eval_assign, Expr.eval,
        writeReg_diff _ (reg .remaining) 3 (reg .bound) hbr]
    have hσ1w : σ1 (reg .wBase) = σ (reg .wBase) := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ (reg .sat) 0 (reg .wBase) hsw.symm, eval_assign, Expr.eval,
        writeReg_diff _ (reg .remaining) 3 (reg .wBase) hrw.symm]
    refine programBoundedIn_forN_of_invariant B 3 σ1 (Expr.const 3)
      (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat) (reg .bit)
        (reg .val) (reg .wBase) (reg .bound))
      (fun j τ => τ (reg .bound) = σ (reg .bound) ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .remaining) ≤ 3 ∧ τ (reg .cursor) ≤ σ (reg .cursor) + j * (σ (reg .bound) + 1))
      h3 (by simp only [Expr.eval]; omega) (fun j _ => ?_) (fun j _ τ hI => ?_)
    · have hboundτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
            (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)) j σ1) (reg .bound) = σ (reg .bound) :=
        (decodeClauseEvalStepAt_loopEval_bound_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound) j σ1
          hbc hbp hbv hbd hbr hsb.symm hbb hbval).trans hσ1bnd
      have hwτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining)
          (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)) j σ1) (reg .wBase) = σ (reg .wBase) :=
        (decodeClauseEvalStepAt_loopEval_wBase_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound) j σ1
          hcw hpw hvw hdw hrw hbw hvalw hsw).trans hσ1w
      have hremτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)) j σ1) (reg .remaining) ≤ 3 := by
        have h := decodeClauseEvalStepAt_loopEval_remaining_le (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound) j σ1
          hrc hrp hrv hrd hrbit hrval hsr.symm
        rw [hσ1rem] at h
        exact h
      have hcurτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)) j σ1) (reg .cursor) ≤
          σ (reg .cursor) + j * (σ (reg .bound) + 1) := by
        have hg := decodeClauseEvalStepAt_cursor_le (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining)
          (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound) j σ1
          hcp hcv hcd hrc hcbit hcval hsc.symm hbc hbp hbv hbd hbr hbb hbval hsb.symm
        rw [hσ1cur, hσ1bnd] at hg
        exact hg
      exact ⟨hboundτ, hwτ, hremτ, hcurτ⟩
    · obtain ⟨hbdτ, hwτ, hremτ, hcurτ⟩ := hI
      have hj3 : j ≤ 3 := by omega
      have hmb : j * (σ (reg .bound) + 1) ≤ 3 * (σ (reg .bound) + 1) :=
        Nat.mul_le_mul_right _ hj3
      have hcurm : τ (reg .cursor) ≤ B := by omega
      have hremm : ((decodeLiteralValueProgramAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .bound)).eval τ)
          (reg .remaining) ≤ B := by
        rw [decodeLiteralValueProgramAt_frame (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .bound) (reg .remaining)
          τ hrc hrp hrv hrd]
        omega
      have hbudm : τ (reg .cursor) + 1 + τ (reg .bound) ≤ B := by rw [hbdτ]; omega
      have hwbm : τ (reg .wBase) + τ (reg .bound) ≤ B := by rw [hwτ, hbdτ]; exact hwbudget
      exact programBoundedIn_decodeClauseEvalStepAt_of_local_bounds B (reg .cursor) (reg .pol) (reg .var)
        (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound) τ
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
        hcw hpw hvw hdw hrw hrv hcurm hremm hbudm hwbm
  change ProgramBoundedIn B σ
      ((decodeThreeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat) (reg .bit)
        (reg .val) (reg .wBase) (reg .bound)).seq (andIntoProg (reg .sat) (reg .cnf)))
  simp only [ProgramBoundedIn]
  exact ⟨hstep, programBoundedIn_andIntoProg B (reg .sat) (reg .cnf) _ hsi hki⟩
/-- `ProgramBoundedIn` for `decodeThreeCNFEvalClauseStepAt` from value budgets: the two seeds
(`remaining := 3`, `sat := 0`) and the constant-count literal loop of one clause step, with the
per-visit obligations of the literal loop from the local leaf. -/
@[stage_impl] lemma programBoundedIn_decodeThreeCNFEvalClauseStepAt_of_value_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg
      boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hbr : boundReg ≠ remainingReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ boundReg ∧ satReg ≠ wBaseReg)
    (h3 : (3:ℕ) ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (hinner : σ cursorReg + 3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  rcases hsatFrame with ⟨hsc, hsd, hsr, hsb, hsw⟩
  set reg : ThreeCNFEvalRole → ℕ := (fun
    | .cursor => cursorReg
    | .pol => polReg
    | .var => varReg
    | .done => doneReg
    | .remaining => remainingReg
    | .sat => satReg
    | .bit => bitReg
    | .val => valReg
    | .wBase => wBaseReg
    | .cnf => cnfReg
    | .bound => boundReg
    | _ => 0)
  refine programBoundedIn_decodeThreeCNFEvalClauseStepAt_core B reg σ ?_ ?_ ?_
  · intro a b h
    simp only [threeStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  · intro r hr
    simp only [threeStepUsed, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  · exact ⟨h3, hwbudget, hinner⟩

/-- Layout version of the ThreeCNF clause-step resource core: separation and index bounds
come wholesale from the layout. -/
@[stage_impl] lemma programBoundedIn_decodeThreeCNFEvalClauseStepAt_layout
    (R : RegLayout ThreeCNFEvalRole) (B : ℕ) (σ : Store) (hRB : R.top ≤ B + 1)
    (hb : threeStepBudgets B (σ (R.reg .cursor)) (σ (R.reg .wBase)) (σ (R.reg .bound))) :
    ProgramBoundedIn B σ
      (decodeThreeCNFEvalClauseStepAt (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
        (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase) (R.reg .cnf)
        (R.reg .bound)) :=
  programBoundedIn_decodeThreeCNFEvalClauseStepAt_core B R.reg σ
    (R.separates threeStepPairs threeStepPairs_ne) (R.regsLe threeStepUsed hRB) hb

/-- The register pairs the ThreeCNF program's resource proof separates: the clause step's
plus the prefix/loop pairs. -/
def threeProgPairs : List (ThreeCNFEvalRole × ThreeCNFEvalRole) :=
  threeStepPairs ++ [(.cursor, .numVarsSkip), (.numVarsSkip, .done), (.cursor, .outer),
    (.done, .outer), (.outer, .wBase), (.bound, .outer), (.numVarsSkip, .outer),
    (.bound, .numVarsSkip), (.numVarsSkip, .wBase), (.cursor, .cnf), (.bound, .cnf),
    (.cnf, .wBase)]

/-- The roles the ThreeCNF program's resource proof indexes. -/
def threeProgUsed : Set ThreeCNFEvalRole :=
  insert .numVarsSkip (insert .outer threeStepUsed)

lemma threeStepPairs_subset_threeProgPairs : threeStepPairs ⊆ threeProgPairs :=
  List.subset_append_left _ _

lemma threeStepUsed_subset_threeProgUsed : threeStepUsed ⊆ threeProgUsed :=
  (Set.subset_insert _ _).trans (Set.subset_insert _ _)

/-- The pairs of `threeProgPairs` are pairs of distinct roles. -/
lemma threeProgPairs_ne (a b : ThreeCNFEvalRole) (h : (a, b) ∈ threeProgPairs) : a ≠ b := by
  simp only [threeProgPairs, List.mem_append] at h
  rcases h with h | h
  · exact threeStepPairs_ne a b h
  · simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | decide | nomatch hm

/-- The ThreeCNF evaluator's resource composition at a role assignment. -/
@[stage_impl] lemma decodeThreeCNFEvalProgramAt_resource_stage_core
    (B : ℕ) (reg : ThreeCNFEvalRole → ℕ) (σ : Store)
    (hsep : Separates reg threeProgPairs) (hidx : RegsLe reg threeProgUsed B)
    (hb : threeProgramBudgets B (σ (reg .cursor)) (σ (reg .wBase)) (σ (reg .bound))) :
    StageSpec B (decodeThreeCNFEvalResBounds B (reg .cursor) (reg .wBase) (reg .bound) σ)
      (decodeThreeCNFEvalProgramAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .outer) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
        (reg .cnf) (reg .bound) (reg .numVarsSkip))
      (({reg .done} : Set ℕ) ∪ ({reg .numVarsSkip} ∪
        ((fun r => r = reg .cursor ∨ r = reg .numVarsSkip ∨ r = reg .done) ∪
          (({reg .done} : Set ℕ) ∪ ({reg .outer} ∪
            ((fun r => r = reg .cursor ∨ r = reg .outer ∨ r = reg .done) ∪
              (fun r => r = reg .cursor ∨ r = reg .pol ∨ r = reg .var ∨ r = reg .done ∨
                r = reg .remaining ∨ r = reg .sat ∨ r = reg .bit ∨ r = reg .val ∨
                r = reg .cnf)))))))
      (fun _ => True) := by
  rcases hb with ⟨hwbudget, h3, houterCoarse⟩
  rcases (⟨hidx .cursor (by simp [threeProgUsed, threeStepUsed]), hidx .pol (by simp [threeProgUsed, threeStepUsed]), hidx .var (by simp [threeProgUsed, threeStepUsed]), hidx .done (by simp [threeProgUsed, threeStepUsed]), hidx .outer (by simp [threeProgUsed, threeStepUsed]), hidx .remaining (by simp [threeProgUsed, threeStepUsed]), hidx .sat (by simp [threeProgUsed, threeStepUsed]), hidx .bit (by simp [threeProgUsed, threeStepUsed]), hidx .val (by simp [threeProgUsed, threeStepUsed]), hidx .wBase (by simp [threeProgUsed, threeStepUsed]), hidx .cnf (by simp [threeProgUsed, threeStepUsed]), hidx .bound (by simp [threeProgUsed, threeStepUsed]), hidx .numVarsSkip (by simp [threeProgUsed, threeStepUsed])⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hki, hbi, hnvi⟩
  rcases (⟨hsep .cursor .pol (by decide : (.cursor, .pol) ∈ threeProgPairs), hsep .cursor .var (by decide : (.cursor, .var) ∈ threeProgPairs), hsep .cursor .done (by decide : (.cursor, .done) ∈ threeProgPairs), hsep .var .done (by decide : (.var, .done) ∈ threeProgPairs), hsep .bound .cursor (by decide : (.bound, .cursor) ∈ threeProgPairs), hsep .bound .pol (by decide : (.bound, .pol) ∈ threeProgPairs), hsep .bound .var (by decide : (.bound, .var) ∈ threeProgPairs), hsep .bound .done (by decide : (.bound, .done) ∈ threeProgPairs), hsep .bound .remaining (by decide : (.bound, .remaining) ∈ threeProgPairs), hsep .cursor .numVarsSkip (by decide : (.cursor, .numVarsSkip) ∈ threeProgPairs), hsep .numVarsSkip .done (by decide : (.numVarsSkip, .done) ∈ threeProgPairs), hsep .cursor .outer (by decide : (.cursor, .outer) ∈ threeProgPairs), hsep .done .outer (by decide : (.done, .outer) ∈ threeProgPairs), hsep .outer .wBase (by decide : (.outer, .wBase) ∈ threeProgPairs), hsep .bound .outer (by decide : (.bound, .outer) ∈ threeProgPairs), hsep .numVarsSkip .outer (by decide : (.numVarsSkip, .outer) ∈ threeProgPairs), hsep .bound .numVarsSkip (by decide : (.bound, .numVarsSkip) ∈ threeProgPairs), hsep .numVarsSkip .wBase (by decide : (.numVarsSkip, .wBase) ∈ threeProgPairs), hsep .cursor .cnf (by decide : (.cursor, .cnf) ∈ threeProgPairs), hsep .bound .cnf (by decide : (.bound, .cnf) ∈ threeProgPairs), hsep .remaining .cursor (by decide : (.remaining, .cursor) ∈ threeProgPairs), hsep .cursor .bit (by decide : (.cursor, .bit) ∈ threeProgPairs), hsep .cursor .val (by decide : (.cursor, .val) ∈ threeProgPairs), (hsep .sat .cursor (by decide : (.sat, .cursor) ∈ threeProgPairs)).symm, hsep .bound .bit (by decide : (.bound, .bit) ∈ threeProgPairs), hsep .bound .val (by decide : (.bound, .val) ∈ threeProgPairs), (hsep .sat .bound (by decide : (.sat, .bound) ∈ threeProgPairs)).symm, (hsep .sat .remaining (by decide : (.sat, .remaining) ∈ threeProgPairs)).symm, hsep .sat .done (by decide : (.sat, .done) ∈ threeProgPairs), hsep .cursor .wBase (by decide : (.cursor, .wBase) ∈ threeProgPairs), hsep .pol .wBase (by decide : (.pol, .wBase) ∈ threeProgPairs), hsep .var .wBase (by decide : (.var, .wBase) ∈ threeProgPairs), hsep .done .wBase (by decide : (.done, .wBase) ∈ threeProgPairs), hsep .remaining .wBase (by decide : (.remaining, .wBase) ∈ threeProgPairs), hsep .bit .wBase (by decide : (.bit, .wBase) ∈ threeProgPairs), hsep .val .wBase (by decide : (.val, .wBase) ∈ threeProgPairs), hsep .sat .wBase (by decide : (.sat, .wBase) ∈ threeProgPairs), hsep .cnf .wBase (by decide : (.cnf, .wBase) ∈ threeProgPairs), hsep .remaining .pol (by decide : (.remaining, .pol) ∈ threeProgPairs), hsep .remaining .done (by decide : (.remaining, .done) ∈ threeProgPairs), hsep .remaining .bit (by decide : (.remaining, .bit) ∈ threeProgPairs), hsep .remaining .val (by decide : (.remaining, .val) ∈ threeProgPairs), hsep .remaining .var (by decide : (.remaining, .var) ∈ threeProgPairs)⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr, hcl, hld, hco, hdo, how, hbo, hno, hbl, hnw, hck, hbk, hrc, hcbit, hcval, hcsat, hbb, hbval, hbs, hrs, hsd, hcw, hpw, hvw, hdw, hrw, hbw, hvalw, hsw, hkw, hrp, hrd, hrbit, hrval, hrv⟩
  have hC1 : ReadsOnly (fun a => a ≠ (reg .done))
      (fun ρ => ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) = σ (reg .cursor)) := by
    intro τ τ' he hτ
    exact ⟨(he (reg .wBase) hdw.symm).trans hτ.1, (he (reg .bound) hbd).trans hτ.2.1,
      (he (reg .cursor) hcd).trans hτ.2.2⟩
  have s1 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧
        (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) = σ (reg .cursor)))
      (Program.assign (reg .done) (.const 0)) {(reg .done)}
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧
        (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) = σ (reg .cursor)) ∧
        ρ (reg .done) = 0) :=
    StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hdi (by omega) hC1
  have hC2 : ReadsOnly (fun a => a ≠ (reg .numVarsSkip))
      (fun ρ => (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) = σ (reg .cursor))
        ∧ ρ (reg .done) = 0) := by
    intro τ τ' he hτ
    exact ⟨⟨(he (reg .wBase) hnw.symm).trans hτ.1.1, (he (reg .bound) hbl).trans hτ.1.2.1,
      (he (reg .cursor) hcl).trans hτ.1.2.2⟩, (he (reg .done) hld.symm).trans hτ.2⟩
  have s2 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧
        (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) = σ (reg .cursor)) ∧
        ρ (reg .done) = 0)
      (Program.assign (reg .numVarsSkip) (.const 0)) {(reg .numVarsSkip)}
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧ ρ (reg .wBase) = σ (reg .wBase) ∧
        ρ (reg .cursor) ≤ σ (reg .cursor) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .numVarsSkip) = 0) :=
    (StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hnvi (by omega)
      hC2).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc⟩, hdone⟩ := hpins
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC3 : ReadsOnly (fun a => a ≠ (reg .cursor) ∧ a ≠ (reg .numVarsSkip) ∧ a ≠ (reg .done))
      (fun ρ => ρ (reg .wBase) = σ (reg .wBase)) := by
    intro τ τ' he hτ
    exact (he (reg .wBase) ⟨hcw.symm, hnw.symm, hdw.symm⟩).trans hτ
  have hdS : (reg .done) ∉ ({(reg .wBase), (reg .bound), (reg .cursor)} : Set ℕ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hdw h
    · exact hbd.symm h
    · exact hcd.symm h
  have s3 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧ ρ (reg .wBase) = σ (reg .wBase) ∧
        ρ (reg .cursor) ≤ σ (reg .cursor) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .numVarsSkip) = 0)
      (decodeNatProgramAt (reg .cursor) (reg .numVarsSkip) (reg .done) (reg .bound))
      (fun r => r = (reg .cursor) ∨ r = (reg .numVarsSkip) ∨ r = (reg .done))
      (fun τ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} τ ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .bound) = σ (reg .bound) ∧ τ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧
        τ (reg .numVarsSkip) ≤ 0 + σ (reg .bound)) :=
    StageSpec.decodeUnaryAt (cg := σ (reg .cursor)) (k0 := 0) (lrv := σ (reg .bound))
      (c := (reg .cursor)) (k := (reg .numVarsSkip)) (d := (reg .done)) (lr := (reg .bound))
      (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hcl hcd hld
      ⟨hbc, hbl, hbd⟩ ⟨hci, hnvi, hdi, hbi⟩ hC3 hdS (by omega) (by omega)
  have hC4 : ReadsOnly (fun a => a ≠ (reg .done))
      (fun ρ => ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧
        ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .numVarsSkip) ≤ 0 + σ (reg .bound)) := by
    intro τ τ' he hτ
    exact ⟨(he (reg .wBase) hdw.symm).trans hτ.1, (he (reg .bound) hbd).trans hτ.2.1,
      by have h1 := he (reg .cursor) hcd; omega,
      by have h1 := he (reg .numVarsSkip) hld; omega⟩
  have s4 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧ ρ (reg .wBase) = σ (reg .wBase) ∧
        ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧
        ρ (reg .numVarsSkip) ≤ 0 + σ (reg .bound))
      (Program.assign (reg .done) (.const 0)) {(reg .done)}
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧
        (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧
          ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .numVarsSkip) ≤ 0 + σ (reg .bound)) ∧
        ρ (reg .done) = 0) :=
    StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hdi (by omega) hC4
  have hC5 : ReadsOnly (fun a => a ≠ (reg .outer))
      (fun ρ => (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧
          ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .numVarsSkip) ≤ 0 + σ (reg .bound)) ∧
        ρ (reg .done) = 0) := by
    intro τ τ' he hτ
    refine ⟨⟨(he (reg .wBase) how.symm).trans hτ.1.1, (he (reg .bound) hbo).trans hτ.1.2.1,
      by have h1 := he (reg .cursor) hco; omega,
      by have h1 := he (reg .numVarsSkip) hno; omega⟩,
      (he (reg .done) hdo).trans hτ.2⟩
  have s5 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧
        (ρ (reg .wBase) = σ (reg .wBase) ∧ ρ (reg .bound) = σ (reg .bound) ∧
          ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .numVarsSkip) ≤ 0 + σ (reg .bound)) ∧
        ρ (reg .done) = 0)
      (Program.assign (reg .outer) (.const 0)) {(reg .outer)}
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧ ρ (reg .wBase) = σ (reg .wBase) ∧
        ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .outer) = 0) :=
    (StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hoi (by omega)
      hC5).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc, hn⟩, hdone⟩ := hpins
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC6 : ReadsOnly (fun a => a ≠ (reg .cursor) ∧ a ≠ (reg .outer) ∧ a ≠ (reg .done))
      (fun ρ => ρ (reg .wBase) = σ (reg .wBase)) := by
    intro τ τ' he hτ
    exact (he (reg .wBase) ⟨hcw.symm, how.symm, hdw.symm⟩).trans hτ
  have s6 : StageSpec B
      (fun ρ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} ρ ∧ ρ (reg .wBase) = σ (reg .wBase) ∧
        ρ (reg .cursor) ≤ σ (reg .cursor) + σ (reg .bound) ∧ ρ (reg .bound) = σ (reg .bound) ∧ ρ (reg .outer) = 0)
      (decodeNatProgramAt (reg .cursor) (reg .outer) (reg .done) (reg .bound))
      (fun r => r = (reg .cursor) ∨ r = (reg .outer) ∨ r = (reg .done))
      (fun τ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} τ ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .bound) = σ (reg .bound) ∧ τ (reg .cursor) ≤ (σ (reg .cursor) + σ (reg .bound)) + σ (reg .bound) ∧
        τ (reg .outer) ≤ 0 + σ (reg .bound)) :=
    StageSpec.decodeUnaryAt (cg := σ (reg .cursor) + σ (reg .bound)) (k0 := 0) (lrv := σ (reg .bound))
      (c := (reg .cursor)) (k := (reg .outer)) (d := (reg .done)) (lr := (reg .bound))
      (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hco hcd hdo.symm
      ⟨hbc, hbo, hbd⟩ ⟨hci, hoi, hdi, hbi⟩ hC6 hdS (by omega) (by omega)
  have s7 : StageSpec B
      (fun τ => ValuesLeOn B {(reg .wBase), (reg .bound), (reg .cursor)} τ ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .bound) = σ (reg .bound) ∧ τ (reg .cursor) ≤ (σ (reg .cursor) + σ (reg .bound)) + σ (reg .bound) ∧
        τ (reg .outer) ≤ 0 + σ (reg .bound))
      (Program.forN (.reg (reg .outer))
        (decodeThreeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat)
          (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound)))
      (fun r => r = (reg .cursor) ∨ r = (reg .pol) ∨ r = (reg .var) ∨ r = (reg .done) ∨ r = (reg .remaining) ∨
        r = (reg .sat) ∨ r = (reg .bit) ∨ r = (reg .val) ∨ r = (reg .cnf))
      (fun _ => True) := by
    refine StageSpec.forN_le (N := σ (reg .bound))
      (I := fun j τ => τ (reg .bound) = σ (reg .bound) ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .cursor) ≤ (σ (reg .cursor) + σ (reg .bound)) + σ (reg .bound) +
          j * (3 * (σ (reg .bound) + 1)))
      ?_ ?_ ?_ ?_ ?_
    · intro ρ _; show ExprBoundedIn B ρ (Expr.reg (reg .outer)); exact hoi
    · intro ρ hρ; show (Expr.reg (reg .outer)).eval ρ ≤ σ (reg .bound)
      simp only [Expr.eval]; omega
    · intro ρ hρ j _
      obtain ⟨_, hwρ, hbdρ, hcurρ, _⟩ := hρ
      have hboundτ : (loopEval (decodeThreeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound)) j ρ) (reg .bound) =
          σ (reg .bound) :=
        (decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound) j ρ
          hbr hbs hbc hbp hbv hbd hbb hbval hbk).trans hbdρ
      have hwτ : (loopEval (decodeThreeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound)) j ρ) (reg .wBase) =
          σ (reg .wBase) :=
        (decodeThreeCNFEvalClauseStepAt_loopEval_wBase_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound) j ρ
          hrw hsw hcw hpw hvw hdw hbw hvalw hkw).trans hwρ
      have hcurτ : (loopEval (decodeThreeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound)) j ρ) (reg .cursor) ≤
          (σ (reg .cursor) + σ (reg .bound)) + σ (reg .bound) + j * (3 * (σ (reg .bound) + 1)) := by
        have hg := decodeThreeCNFEvalClauseStepAt_cursor_le (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound) j ρ
          hcp hcv hcd hrc hcbit hcval hcsat hck hbc hbp hbv hbd hbr hbb hbval hbs hbk
        rw [hbdρ] at hg
        omega
      exact ⟨hboundτ, hwτ, hcurτ⟩
    · refine Program.Avoids.mono (P := fun r => r ≠ (reg .cursor) ∧ r ≠ (reg .pol) ∧ r ≠ (reg .var) ∧
          r ≠ (reg .done) ∧ r ≠ (reg .remaining) ∧ r ≠ (reg .sat) ∧ r ≠ (reg .bit) ∧ r ≠ (reg .val) ∧ r ≠ (reg .cnf)) ?_
        (fun r hr => ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr (Or.inl h)),
          fun h => hr (Or.inr (Or.inr (Or.inl h))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))⟩)
      exact decodeThreeCNFEvalClauseStepAt_avoids_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .cnf) (reg .bound)
    · intro j _ τ hI
      obtain ⟨hbdτ, hwτ, hcurτ⟩ := hI
      have hjB : j ≤ σ (reg .bound) := by omega
      have hmb : j * (3 * (σ (reg .bound) + 1)) ≤ σ (reg .bound) * (3 * (σ (reg .bound) + 1)) :=
        Nat.mul_le_mul_right _ hjB
      exact programBoundedIn_decodeThreeCNFEvalClauseStepAt_core B reg τ
        (Separates.of_subset hsep threeStepPairs_subset_threeProgPairs)
        (RegsLe.mono threeStepUsed_subset_threeProgUsed hidx)
        ⟨h3, by rw [hwτ, hbdτ]; exact hwbudget, by rw [hbdτ]; omega⟩
  exact StageSpec.seq s1 (StageSpec.seq s2 (StageSpec.seq s3
    (StageSpec.seq s4 (StageSpec.seq s5 (StageSpec.seq s6 s7)))))
/-- Resource-carrying stage for the ThreeCNF evaluator's prefix (the `numVars` header skip and
the clause-count decode) and outer clause loop: the prefix seeds and decoders carry the local
value bounds as facts via `StageSpec.assign_const_carry`/`StageSpec.decodeUnaryAt`, and the
loop is a `StageSpec.forN_le` whose per-visit budgets come from the loop invariant. -/
@[stage_impl] lemma decodeThreeCNFEvalProgramAt_resource_stage
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      cnfReg boundReg numVarsSkipReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B ∧ numVarsSkipReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ numVarsSkipReg) (hld : numVarsSkipReg ≠ doneReg)
    (hco : cursorReg ≠ outerReg) (hdo : doneReg ≠ outerReg) (how : outerReg ≠ wBaseReg)
    (hbo : boundReg ≠ outerReg) (hno : numVarsSkipReg ≠ outerReg)
    (hbl : boundReg ≠ numVarsSkipReg) (hnw : numVarsSkipReg ≠ wBaseReg)
    (hck : cursorReg ≠ cnfReg) (hbk : boundReg ≠ cnfReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg)
    (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hrv : remainingReg ≠ varReg)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B) (h3 : (3:ℕ) ≤ B)
    (houterCoarse : σ cursorReg + 2 * σ boundReg +
        σ boundReg * (3 * (σ boundReg + 1)) + 3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B) :
    StageSpec B (decodeThreeCNFEvalResBounds B cursorReg wBaseReg boundReg σ)
      (decodeThreeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
        bitReg valReg wBaseReg cnfReg boundReg numVarsSkipReg)
      (({doneReg} : Set ℕ) ∪ ({numVarsSkipReg} ∪
        ((fun r => r = cursorReg ∨ r = numVarsSkipReg ∨ r = doneReg) ∪
          (({doneReg} : Set ℕ) ∪ ({outerReg} ∪
            ((fun r => r = cursorReg ∨ r = outerReg ∨ r = doneReg) ∪
              (fun r => r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨ r = remainingReg ∨
                r = satReg ∨ r = bitReg ∨ r = valReg ∨ r = cnfReg)))))))
      (fun _ => True) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hki, hbi, hnvi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  set reg : ThreeCNFEvalRole → ℕ := (fun
    | .cursor => cursorReg
    | .pol => polReg
    | .var => varReg
    | .done => doneReg
    | .outer => outerReg
    | .remaining => remainingReg
    | .sat => satReg
    | .bit => bitReg
    | .val => valReg
    | .wBase => wBaseReg
    | .cnf => cnfReg
    | .bound => boundReg
    | .numVarsSkip => numVarsSkipReg)
  have hstep : Separates reg threeStepPairs := by
    intro a b h
    simp only [threeStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | (exact Ne.symm (by assumption)) | nomatch hm
  have hextra : Separates reg
      [(.cursor, .numVarsSkip), (.numVarsSkip, .done), (.cursor, .outer), (.done, .outer),
        (.outer, .wBase), (.bound, .outer), (.numVarsSkip, .outer), (.bound, .numVarsSkip),
        (.numVarsSkip, .wBase), (.cursor, .cnf), (.bound, .cnf), (.cnf, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  refine decodeThreeCNFEvalProgramAt_resource_stage_core B reg σ
    (Separates.append hstep hextra) ?_ ⟨hwbudget, h3, houterCoarse⟩
  · intro r hr
    simp only [threeProgUsed, threeStepUsed, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- Layout version of the ThreeCNF resource composition core: separation and index bounds
come wholesale from the layout. -/
@[stage_impl] lemma decodeThreeCNFEvalProgramAt_resource_stage_layout
    (R : RegLayout ThreeCNFEvalRole) (B : ℕ) (σ : Store) (hRB : R.top ≤ B + 1)
    (hb : threeProgramBudgets B (σ (R.reg .cursor)) (σ (R.reg .wBase)) (σ (R.reg .bound))) :
    StageSpec B (decodeThreeCNFEvalResBounds B (R.reg .cursor) (R.reg .wBase) (R.reg .bound) σ)
      (decodeThreeCNFEvalProgramAt (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done)
        (R.reg .outer) (R.reg .remaining) (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase)
        (R.reg .cnf) (R.reg .bound) (R.reg .numVarsSkip))
      (({R.reg .done} : Set ℕ) ∪ ({R.reg .numVarsSkip} ∪
        ((fun r => r = R.reg .cursor ∨ r = R.reg .numVarsSkip ∨ r = R.reg .done) ∪
          (({R.reg .done} : Set ℕ) ∪ ({R.reg .outer} ∪
            ((fun r => r = R.reg .cursor ∨ r = R.reg .outer ∨ r = R.reg .done) ∪
              (fun r => r = R.reg .cursor ∨ r = R.reg .pol ∨ r = R.reg .var ∨ r = R.reg .done ∨
                r = R.reg .remaining ∨ r = R.reg .sat ∨ r = R.reg .bit ∨ r = R.reg .val ∨
                r = R.reg .cnf)))))))
      (fun _ => True) :=
  decodeThreeCNFEvalProgramAt_resource_stage_core B R.reg σ
    (R.separates threeProgPairs threeProgPairs_ne) (R.regsLe threeProgUsed hRB) hb

#check_stage_discipline all

end NPComplete.CookLevin

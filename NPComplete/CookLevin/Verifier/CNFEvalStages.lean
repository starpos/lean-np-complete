module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck
public import NPComplete.CookLevin.Verifier.CNFEvalTop
public import NPComplete.RAMToTM.Generic.Api.ValuesLeOn
public import NPComplete.RAMToTM.Generic.Api.ResStages

/-!
# Resource-connected stage contracts for the CNF evaluator

The stage contracts of `CNFEvalAt.lean` take the resource component (`ProgramBoundedIn`)
as an explicit obligation `hbnd`, because the verifier's resource lemmas live downstream
of that module and are stated over `StoreValuesLe` — a hypothesis no `LayoutFact` can
supply (a fact reads only its footprint, while `StoreValuesLe` constrains every address).

This module closes the gap from the other side: a value-bounds resource chain that needs
no store hypothesis at all.  `ProgramBoundedIn` never constrains the value of a cell it
reads (only `regInd` addresses and arithmetic operands), and every register whose value
enters an operand is either pinned by the entry facts or written by the program before it
is read, so the store hypothesis of the downstream lemmas is dead weight.  The
`..._of_value_bounds` lemmas below restate those lemmas without it (same proof shapes),
and the `..._stage_of_bounds` contracts then discharge the resource component inside the
contract from role-level budgets alone.  A caller supplies numeric budgets over the fact
values and never reasons about the program's internals.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip ReadsOnly)
open NPComplete.BoundedWhile (RegLayout LayoutFact StoreFact Separates RegsLe)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

stage_default boundary

/-! ## The value-bounds resource chain -/

/-- `programBoundedIn_decodeClauseWithLengthPrefixAt_of_bounds` without `StoreValuesLe`:
the store hypothesis only propagated `StoreValuesLe` that no consumer needs. -/
@[stage_impl] lemma programBoundedIn_decodeClauseWithLengthPrefixAt_of_value_bounds
    (B cursorReg doneReg remainingReg lengthReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ doneReg ≤ B ∧ remainingReg ≤ B ∧ lengthReg ≤ B ∧
      boundReg ≤ B)
    (hdist : cursorReg ≠ doneReg ∧ cursorReg ≠ lengthReg ∧ lengthReg ≠ doneReg ∧
      boundReg ≠ cursorReg ∧ boundReg ≠ lengthReg ∧ boundReg ≠ doneReg)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg) := by
  rcases hidx with ⟨hcurI, hdoneI, hremI, hlenI, hboundI⟩
  rcases hdist with ⟨hcd, hcl, hld, hbc, hbl, hbd⟩
  let σ0 := (Program.assign doneReg (.const 0)).eval σ
  let σ1 := (Program.assign lengthReg (.const 0)).eval σ0
  have hσ0b : σ0 boundReg = σ boundReg := by
    simp [σ0, eval_assign, Expr.eval, writeReg_diff _ doneReg _ _ hbd]
  have hσ1b : σ1 boundReg = σ boundReg := by
    simp [σ1, eval_assign, Expr.eval, writeReg_diff _ lengthReg _ _ hbl, hσ0b]
  have hσ1c : σ1 cursorReg = σ cursorReg := by
    simp [σ1, σ0, eval_assign, Expr.eval,
      writeReg_diff _ lengthReg _ _ hcl, writeReg_diff _ doneReg _ _ hcd]
  have hσ1l : σ1 lengthReg = 0 := by
    simp [σ1, eval_assign, Expr.eval, writeReg_same]
  have hnat : ProgramBoundedIn B σ1
      (decodeNatProgramAt cursorReg lengthReg doneReg boundReg) := by
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg lengthReg doneReg boundReg B σ1
      hcl hcd hld ⟨hcurI, hlenI, hdoneI, hboundI⟩
    · rw [hσ1c, hσ1b]
      omega
    · rw [hσ1l, hσ1b]
      omega
  let σ2 := (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1
  unfold decodeClauseWithLengthPrefixAt
  simp only [ProgramBoundedIn]
  rw [show (Program.assign doneReg (.const 0)).eval σ = σ0 from rfl]
  rw [show (Program.assign lengthReg (.const 0)).eval σ0 = σ1 from rfl]
  rw [show (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1 = σ2 from rfl]
  refine ⟨⟨hdoneI, by simp [ExprBoundedIn]⟩, ?_⟩
  refine ⟨⟨hlenI, by simp [ExprBoundedIn]⟩, ?_⟩
  refine ⟨hnat, ?_⟩
  refine ⟨⟨hdoneI, by simp [ExprBoundedIn]⟩, ?_⟩
  exact ⟨hremI, hlenI⟩

/-- One `decodeClauseEvalStepAt` visit never raises `remainingReg`: the guarded step
decrements it and every other write target is distinct. -/
@[stage_impl] lemma decodeClauseEvalStepAt_eval_remaining_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg : ℕ)
    (σ : Store)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg) (hrv : remainingReg ≠ varReg)
    (hrd : remainingReg ≠ doneReg) (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hrs : remainingReg ≠ satReg) :
    (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg boundReg).eval σ remainingReg ≤ σ remainingReg := by
  have hstep : ∀ τ,
      ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).seq
        ((Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).seq
          ((readAssignBitProg wBaseReg varReg bitReg).seq
            ((literalValueProg polReg bitReg valReg).seq
              (orIntoProg valReg satReg))))).eval τ remainingReg ≤ τ remainingReg := by
    intro τ
    rw [eval_seq, eval_seq, eval_seq, eval_seq]
    rw [orIntoProg_frame valReg satReg remainingReg _ hrs,
      literalValueProg_frame polReg bitReg valReg remainingReg _ hrval,
      readAssignBitProg_frame wBaseReg varReg bitReg remainingReg _ hrbit]
    simp only [eval_assign, Expr.eval, writeReg_same]
    rw [decodeLiteralValueProgramAt_frame cursorReg polReg varReg doneReg boundReg remainingReg τ
      hrc hrp hrv hrd]
    exact Nat.sub_le _ _
  unfold decodeClauseEvalStepAt
  rw [eval_ifNZ]
  split_ifs
  · exact hstep _
  · simp [eval_skip]

/-- Iterating `decodeClauseEvalStepAt` never raises `remainingReg`. -/
@[stage_impl] lemma decodeClauseEvalStepAt_loopEval_remaining_le
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg boundReg k : ℕ)
    (σ : Store)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg) (hrv : remainingReg ≠ varReg)
    (hrd : remainingReg ≠ doneReg) (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hrs : remainingReg ≠ satReg) :
    loopEval
      (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg boundReg) k σ remainingReg ≤ σ remainingReg := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    rw [loopEval_succ]
    exact le_trans (ih _)
      (decodeClauseEvalStepAt_eval_remaining_le cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg boundReg _ hrc hrp hrv hrd hrbit hrval hrs)

/-! ## The clause step's necessary-separation core

The proof body of the clause step's resource bound is stated once against a role assignment
`reg`, taking only the pairs of distinct roles its proof reads (`clauseStepPairs`) and the
index bounds of the roles it names (`clauseStepUsed`).  The numbered statement below is a
wrapper that assembles that evidence from its own hypotheses, and the layout version
assembles it wholesale from the layout; placements where some registers coincide (allowed by
the numbered statement's partial pairs) go through the numbered wrapper only. -/

/-- The register pairs the clause-step resource proof separates, in the order of the numbered
statement's distinctness hypotheses. -/
def clauseStepPairs : List (CNFEvalRole × CNFEvalRole) :=
  [(.cursor, .pol), (.cursor, .var), (.cursor, .done), (.var, .done), (.bound, .cursor),
    (.bound, .pol), (.bound, .var), (.bound, .done), (.bound, .remaining), (.cursor, .length),
    (.length, .done), (.remaining, .cursor), (.remaining, .var), (.bound, .length),
    (.remaining, .pol), (.remaining, .done), (.remaining, .bit), (.remaining, .val),
    (.cursor, .wBase), (.pol, .wBase), (.var, .wBase), (.done, .wBase), (.remaining, .wBase),
    (.length, .wBase), (.cursor, .bit), (.cursor, .val), (.bound, .bit), (.bound, .val),
    (.bit, .wBase), (.val, .wBase), (.sat, .cursor), (.sat, .done), (.sat, .remaining),
    (.sat, .length), (.sat, .bound), (.sat, .wBase)]

/-- The roles the clause-step resource proof indexes. -/
def clauseStepUsed : Set CNFEvalRole :=
  {.cursor, .pol, .var, .done, .remaining, .sat, .bit, .val, .wBase, .length, .cnf, .bound}

/-- The pairs of `clauseStepPairs` are pairs of distinct roles. -/
lemma clauseStepPairs_ne (a b : CNFEvalRole) (h : (a, b) ∈ clauseStepPairs) : a ≠ b := by
  simp only [clauseStepPairs, List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
  all_goals first | decide | nomatch hm

/-- The clause-step budgets at one store: the length-prefix budget, the `wBase` budget and
the inner-loop budget. -/
def clauseStepBudgets (B c wBase bound : ℕ) : Prop :=
  c + 1 + bound ≤ B ∧ wBase + bound ≤ B ∧ c + 2 + 2 * bound + bound * (bound + 1) ≤ B

lemma clauseStepBudgets.prefix {B c wBase bound : ℕ} (h : clauseStepBudgets B c wBase bound) :
    c + 1 + bound ≤ B :=
  h.1

lemma clauseStepBudgets.wb {B c wBase bound : ℕ} (h : clauseStepBudgets B c wBase bound) :
    wBase + bound ≤ B :=
  h.2.1

lemma clauseStepBudgets.inner {B c wBase bound : ℕ} (h : clauseStepBudgets B c wBase bound) :
    c + 2 + 2 * bound + bound * (bound + 1) ≤ B :=
  h.2.2

/-- The clause-loop budgets at one store: the `wBase` budget and the coarse outer budget at
the loop-entry values. -/
def clauseLoopBudgets (B CUR WB BND : ℕ) : Prop :=
  WB + BND ≤ B ∧ CUR + BND * (1 + BND + BND * (BND + 1)) + 2 + 2 * BND + BND * (BND + 1) ≤ B

lemma clauseLoopBudgets.wb {B CUR WB BND : ℕ} (h : clauseLoopBudgets B CUR WB BND) :
    WB + BND ≤ B :=
  h.1

lemma clauseLoopBudgets.outerCoarse {B CUR WB BND : ℕ} (h : clauseLoopBudgets B CUR WB BND) :
    CUR + BND * (1 + BND + BND * (BND + 1)) + 2 + 2 * BND + BND * (BND + 1) ≤ B :=
  h.2

/-- The program's budgets at one store: the `wBase` budget and the coarse outer budget at the
entry values. -/
def decodeCNFEvalBudgets (B c wBase bound : ℕ) : Prop :=
  wBase + bound ≤ B ∧
    c + bound + bound * (1 + bound + bound * (bound + 1)) + 2 + 2 * bound +
      bound * (bound + 1) ≤ B

lemma decodeCNFEvalBudgets.wb {B c wBase bound : ℕ} (h : decodeCNFEvalBudgets B c wBase bound) :
    wBase + bound ≤ B :=
  h.1

lemma decodeCNFEvalBudgets.outerCoarse {B c wBase bound : ℕ}
    (h : decodeCNFEvalBudgets B c wBase bound) :
    c + bound + bound * (1 + bound + bound * (bound + 1)) + 2 + 2 * bound +
      bound * (bound + 1) ≤ B :=
  h.2

/-- The clause step's resource body at a role assignment: one proof against `reg`, from the
pairs it separates and the index bounds of the roles it names. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseStepAt_core
    (B : ℕ) (reg : CNFEvalRole → ℕ) (σ : Store)
    (hsep : Separates reg clauseStepPairs) (hidx : RegsLe reg clauseStepUsed B)
    (hb : clauseStepBudgets B (σ (reg .cursor)) (σ (reg .wBase)) (σ (reg .bound))) :
    ProgramBoundedIn B σ (decodeCNFEvalClauseStepAtL reg) := by
  rcases hb with ⟨hbudget, hwbudget, hinner⟩
  rcases (⟨hidx .cursor (by simp [clauseStepUsed]), hidx .pol (by simp [clauseStepUsed]),
      hidx .var (by simp [clauseStepUsed]), hidx .done (by simp [clauseStepUsed]),
      hidx .remaining (by simp [clauseStepUsed]), hidx .sat (by simp [clauseStepUsed]),
      hidx .bit (by simp [clauseStepUsed]), hidx .val (by simp [clauseStepUsed]),
      hidx .wBase (by simp [clauseStepUsed]), hidx .length (by simp [clauseStepUsed]),
      hidx .cnf (by simp [clauseStepUsed]), hidx .bound (by simp [clauseStepUsed])⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases (⟨hsep .cursor .pol (by decide), hsep .cursor .var (by decide),
      hsep .cursor .done (by decide), hsep .var .done (by decide),
      hsep .bound .cursor (by decide), hsep .bound .pol (by decide),
      hsep .bound .var (by decide), hsep .bound .done (by decide),
      hsep .bound .remaining (by decide), hsep .cursor .length (by decide),
      hsep .length .done (by decide), hsep .remaining .cursor (by decide),
      hsep .remaining .var (by decide), hsep .bound .length (by decide),
      hsep .remaining .pol (by decide), hsep .remaining .done (by decide),
      hsep .remaining .bit (by decide), hsep .remaining .val (by decide),
      hsep .cursor .wBase (by decide), hsep .pol .wBase (by decide),
      hsep .var .wBase (by decide), hsep .done .wBase (by decide),
      hsep .remaining .wBase (by decide), hsep .length .wBase (by decide),
      hsep .cursor .bit (by decide), hsep .cursor .val (by decide),
      hsep .bound .bit (by decide), hsep .bound .val (by decide),
      hsep .bit .wBase (by decide), hsep .val .wBase (by decide),
      hsep .sat .cursor (by decide), hsep .sat .done (by decide),
      hsep .sat .remaining (by decide), hsep .sat .length (by decide),
      hsep .sat .bound (by decide), hsep .sat .wBase (by decide)⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
        _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr, hcl, hld, hrc, hrv, hbl, hrp, hrd, hrbit,
      hrval, hcw, hpw, hvw, hdw, hrw, hlw, hcbit, hcval, hbb, hbval, hbitw, hvw2, hsc, hsd,
      hsr, hsl, hsb, hsw⟩
  have hprefix : ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining) (reg .length)
        (reg .bound)) :=
    programBoundedIn_decodeClauseWithLengthPrefixAt_of_value_bounds B (reg .cursor) (reg .done)
      (reg .remaining) (reg .length) (reg .bound) σ ⟨hci, hdi, hri, hli, hbi⟩
      ⟨hcd, hcl, hld, hbc, hbl, hbd⟩ hbudget
  have hprefixBound : (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound)).eval σ (reg .bound) = σ (reg .bound) :=
    decodeClauseWithLengthPrefixAt_bound_frame (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound) σ hbc hbd hbl hbr
  have hprefixRem : (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound)).eval σ (reg .remaining) ≤ σ (reg .bound) :=
    decodeClauseWithLengthPrefixAt_remaining_le (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound) σ hcl hld hbd hbl
  have hprefixCur : (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound)).eval σ (reg .cursor) ≤ σ (reg .cursor) + 1 + σ (reg .bound) :=
    decodeClauseWithLengthPrefixAt_cursor_le (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound) σ hcd hcl hrc hbl hbd
  have hprefixW : (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining)
      (reg .length) (reg .bound)).eval σ (reg .wBase) = σ (reg .wBase) :=
    decodeClauseWithLengthPrefixAt_frame (reg .cursor) (reg .done) (reg .remaining) (reg .length)
      (reg .bound) (reg .wBase) σ hcw.symm hdw.symm hrw.symm hlw.symm
  set σ0 := (decodeClauseWithLengthPrefixAt (reg .cursor) (reg .done) (reg .remaining)
    (reg .length) (reg .bound)).eval σ with hσ0def
  set σ1 := (Program.assign (reg .sat) (.const 0)).eval σ0 with hσ1def
  have hσ1rem : σ1 (reg .remaining) = σ0 (reg .remaining) := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 (reg .sat) 0 (reg .remaining) hsr.symm
  have hσ1bnd : σ1 (reg .bound) = σ0 (reg .bound) := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 (reg .sat) 0 (reg .bound) hsb.symm
  have hσ1w : σ1 (reg .wBase) = σ0 (reg .wBase) := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 (reg .sat) 0 (reg .wBase) hsw.symm
  have hBndEq : σ1 (reg .bound) = σ (reg .bound) := by rw [hσ1bnd, hprefixBound]
  have hRemLe1 : σ1 (reg .remaining) ≤ σ (reg .bound) := by rw [hσ1rem]; exact hprefixRem
  have hσ1wbase : σ1 (reg .wBase) = σ (reg .wBase) := by rw [hσ1w, hprefixW]
  have hσ1cur : σ1 (reg .cursor) ≤ σ (reg .cursor) + 1 + σ (reg .bound) := by
    have h1 : σ1 (reg .cursor) = σ0 (reg .cursor) := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 (reg .sat) 0 (reg .cursor) hsc.symm
    rw [h1]; exact hprefixCur
  have hloop : ProgramBoundedIn B σ1
      (Program.forN (.reg (reg .remaining))
        (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining)
          (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound))) := by
    refine programBoundedIn_forN_of_invariant B (σ (reg .bound)) σ1 (.reg (reg .remaining)) _
      (fun j τ => τ (reg .bound) = σ (reg .bound) ∧ τ (reg .wBase) = σ (reg .wBase) ∧
        τ (reg .remaining) ≤ σ1 (reg .remaining) ∧
        τ (reg .cursor) ≤ σ1 (reg .cursor) + j * (σ (reg .bound) + 1))
      (show ExprBoundedIn B σ1 (Expr.reg (reg .remaining)) from hri) ?_ (fun j _ => ?_)
      (fun j _ τ hI => ?_)
    · show (Expr.reg (reg .remaining)).eval σ1 ≤ σ (reg .bound)
      simp only [Expr.eval]
      exact hRemLe1
    · have hboundτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var)
            (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
            (reg .bound)) j σ1) (reg .bound) = σ (reg .bound) :=
        (decodeClauseEvalStepAt_loopEval_bound_frame (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)
          j σ1 hbc hbp hbv hbd hbr hsb.symm hbb hbval).trans hBndEq
      have hwτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
          (reg .bound)) j σ1) (reg .wBase) = σ (reg .wBase) :=
        (decodeClauseEvalStepAt_loopEval_wBase_frame (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)
          j σ1 hcw hpw hvw hdw hrw hbitw hvw2 hsw).trans hσ1wbase
      have hremτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
          (reg .bound)) j σ1) (reg .remaining) ≤ σ1 (reg .remaining) :=
        decodeClauseEvalStepAt_loopEval_remaining_le (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)
          j σ1 hrc hrp hrv hrd hrbit hrval hsr.symm
      have hcurτ : (loopEval (decodeClauseEvalStepAt (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
          (reg .bound)) j σ1) (reg .cursor) ≤
          σ1 (reg .cursor) + j * (σ (reg .bound) + 1) := by
        rw [← hBndEq]
        exact decodeClauseEvalStepAt_cursor_le (reg .cursor) (reg .pol) (reg .var)
          (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .bound)
          j σ1
          hcp hcv hcd hrc hcbit hcval hsc.symm hbc hbp hbv hbd hbr hbb hbval hsb.symm
      exact ⟨hboundτ, hwτ, hremτ, hcurτ⟩
    · obtain ⟨hbdτ, hwτ, hremτ, hcurτ⟩ := hI
      have hjB : j ≤ σ (reg .bound) := by omega
      have hmb : j * (σ (reg .bound) + 1) ≤ σ (reg .bound) * (σ (reg .bound) + 1) :=
        Nat.mul_le_mul_right _ hjB
      have hcurm : τ (reg .cursor) ≤ B := by omega
      have hremm : ((decodeLiteralValueProgramAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .bound)).eval τ) (reg .remaining) ≤ B := by
        rw [decodeLiteralValueProgramAt_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .bound) (reg .remaining) τ hrc hrp hrv hrd]
        omega
      have hbudm : τ (reg .cursor) + 1 + τ (reg .bound) ≤ B := by rw [hbdτ]; omega
      have hwbm : τ (reg .wBase) + τ (reg .bound) ≤ B := by rw [hwτ, hbdτ]; exact hwbudget
      exact programBoundedIn_decodeClauseEvalStepAt_of_local_bounds B (reg .cursor) (reg .pol)
        (reg .var) (reg .done) (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase)
        (reg .bound) τ
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
        hcw hpw hvw hdw hrw hrv hcurm hremm hbudm hwbm
  have hclause : ProgramBoundedIn B σ
      (decodeClauseEvalWithLengthProgramAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length)
        (reg .bound)) := by
    unfold decodeClauseEvalWithLengthProgramAt
    simp only [ProgramBoundedIn]
    exact ⟨hprefix, ⟨⟨hsi, Nat.zero_le B⟩, hloop⟩⟩
  change ProgramBoundedIn B σ
      ((decodeClauseEvalWithLengthProgramAt (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length)
        (reg .bound)).seq (andIntoProg (reg .sat) (reg .cnf)))
  simp only [ProgramBoundedIn]
  exact ⟨hclause, programBoundedIn_andIntoProg B (reg .sat) (reg .cnf) _ hsi hki⟩

/-- `programBoundedIn_decodeCNFEvalClauseStepAt_of_store_bounds` without `StoreValuesLe`:
the per-iteration store hypothesis of the inner literal loop becomes a per-iteration
remaining bound, derived from the length-prefix postcondition. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseStepAt_of_value_bounds
    (B cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hrv : remainingReg ≠ varReg) (hbl : boundReg ≠ lengthReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbitw : bitReg ≠ wBaseReg) (hvw2 : valReg ≠ wBaseReg)
    (hsatFrame : satReg ≠ cursorReg ∧ satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧
      satReg ≠ lengthReg ∧ satReg ≠ boundReg ∧ satReg ≠ wBaseReg)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (hinner : σ cursorReg + 2 + 2 * σ boundReg + σ boundReg * (σ boundReg + 1) ≤ B) :
    ProgramBoundedIn B σ
      (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg lengthReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  rcases hsatFrame with ⟨hsc, hsd, hsr, hsl, hsb, hsw⟩
  set reg : CNFEvalRole → ℕ := (fun
    | .cursor => cursorReg
    | .pol => polReg
    | .var => varReg
    | .done => doneReg
    | .remaining => remainingReg
    | .sat => satReg
    | .bit => bitReg
    | .val => valReg
    | .wBase => wBaseReg
    | .length => lengthReg
    | .cnf => cnfReg
    | .bound => boundReg
    | _ => 0)
  refine programBoundedIn_decodeCNFEvalClauseStepAt_core B reg σ ?_ ?_ ?_
  · intro a b h
    simp only [clauseStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  · intro r hr
    simp only [clauseStepUsed, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  · exact ⟨hbudget, hwbudget, hinner⟩

/-- Layout version of the clause-step resource core: separation and index bounds come
wholesale from the layout. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseStepAt_layout
    (R : RegLayout CNFEvalRole) (B : ℕ) (σ : Store) (hRB : R.top ≤ B + 1)
    (hb : clauseStepBudgets B (σ (R.reg .cursor)) (σ (R.reg .wBase)) (σ (R.reg .bound))) :
    ProgramBoundedIn B σ (decodeCNFEvalClauseStepAtL R.reg) :=
  programBoundedIn_decodeCNFEvalClauseStepAt_core B R.reg σ
    (R.separates clauseStepPairs clauseStepPairs_ne) (R.regsLe clauseStepUsed hRB) hb

/-- The old clause-step statement allows `bitReg = valReg`: every distinctness hypothesis
holds at the placement `1 2 3 4 5 6 12 12 7 8 9 10`, and the numbered wrapper still
applies there. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseStepAt_coinciding_example :
    ProgramBoundedIn 100 (fun _ => 0)
      (decodeCNFEvalClauseStepAt 1 2 3 4 5 6 12 12 7 8 9 10) := by
  apply programBoundedIn_decodeCNFEvalClauseStepAt_of_value_bounds
  all_goals decide

/-! ## The clause loop's necessary-separation core

The loop's proof body is stated once against `reg`; its pairs are the clause step's plus the
pairs the loop's own frame/growth lemmas read, and its used set adds the count role. -/

/-- The register pairs the clause-loop resource proof separates: the clause step's plus the
loop's own pairs. -/
def clauseLoopPairs : List (CNFEvalRole × CNFEvalRole) :=
  clauseStepPairs ++ [(.bound, .cnf), (.cursor, .cnf), (.cnf, .wBase)]

/-- The roles the clause-loop resource proof indexes. -/
def clauseLoopUsed : Set CNFEvalRole := insert .outer clauseStepUsed

lemma clauseStepPairs_subset_clauseLoopPairs : clauseStepPairs ⊆ clauseLoopPairs :=
  List.subset_append_left _ _

lemma clauseStepUsed_subset_clauseLoopUsed : clauseStepUsed ⊆ clauseLoopUsed :=
  Set.subset_insert _ _

/-- The pairs of `clauseLoopPairs` are pairs of distinct roles. -/
lemma clauseLoopPairs_ne (a b : CNFEvalRole) (h : (a, b) ∈ clauseLoopPairs) : a ≠ b := by
  simp only [clauseLoopPairs, List.mem_append] at h
  rcases h with h | h
  · exact clauseStepPairs_ne a b h
  · simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | decide | nomatch hm

/-- The clause loop's resource body at a role assignment: one proof against `reg`, from the
pairs it separates and the index bounds of the roles it names. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseLoop_core
    (B : ℕ) (reg : CNFEvalRole → ℕ) (CUR WB BND : ℕ) (ρ : Store)
    (hsep : Separates reg clauseLoopPairs) (hidx : RegsLe reg clauseLoopUsed B)
    (hcount : ρ (reg .outer) ≤ BND) (hcur : ρ (reg .cursor) ≤ CUR) (hwb : ρ (reg .wBase) = WB)
    (hbd : ρ (reg .bound) = BND) (hb : clauseLoopBudgets B CUR WB BND) :
    ProgramBoundedIn B ρ
      (Program.forN (.reg (reg .outer)) (decodeCNFEvalClauseStepAtL reg)) := by
  rcases hb with ⟨hwbudget, houterCoarse⟩
  rcases (⟨hidx .cursor (by simp [clauseLoopUsed, clauseStepUsed]), hidx .pol (by simp [clauseLoopUsed, clauseStepUsed]), hidx .var (by simp [clauseLoopUsed, clauseStepUsed]), hidx .done (by simp [clauseLoopUsed, clauseStepUsed]), hidx .outer (by simp [clauseLoopUsed, clauseStepUsed]), hidx .remaining (by simp [clauseLoopUsed, clauseStepUsed]), hidx .sat (by simp [clauseLoopUsed, clauseStepUsed]), hidx .bit (by simp [clauseLoopUsed, clauseStepUsed]), hidx .val (by simp [clauseLoopUsed, clauseStepUsed]), hidx .wBase (by simp [clauseLoopUsed, clauseStepUsed]), hidx .length (by simp [clauseLoopUsed, clauseStepUsed]), hidx .cnf (by simp [clauseLoopUsed, clauseStepUsed]), hidx .bound (by simp [clauseLoopUsed, clauseStepUsed])⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases (⟨hsep .cursor .pol (by decide : (.cursor, .pol) ∈ clauseLoopPairs), hsep .cursor .var (by decide : (.cursor, .var) ∈ clauseLoopPairs), hsep .cursor .done (by decide : (.cursor, .done) ∈ clauseLoopPairs), hsep .var .done (by decide : (.var, .done) ∈ clauseLoopPairs), hsep .bound .cursor (by decide : (.bound, .cursor) ∈ clauseLoopPairs), hsep .bound .pol (by decide : (.bound, .pol) ∈ clauseLoopPairs), hsep .bound .var (by decide : (.bound, .var) ∈ clauseLoopPairs), hsep .bound .done (by decide : (.bound, .done) ∈ clauseLoopPairs), hsep .bound .remaining (by decide : (.bound, .remaining) ∈ clauseLoopPairs), hsep .cursor .length (by decide : (.cursor, .length) ∈ clauseLoopPairs), hsep .length .done (by decide : (.length, .done) ∈ clauseLoopPairs), hsep .remaining .cursor (by decide : (.remaining, .cursor) ∈ clauseLoopPairs), hsep .cursor .bit (by decide : (.cursor, .bit) ∈ clauseLoopPairs), hsep .cursor .val (by decide : (.cursor, .val) ∈ clauseLoopPairs), (hsep .sat .cursor (by decide : (.sat, .cursor) ∈ clauseLoopPairs)).symm, hsep .bound .length (by decide : (.bound, .length) ∈ clauseLoopPairs), hsep .bound .bit (by decide : (.bound, .bit) ∈ clauseLoopPairs), hsep .bound .val (by decide : (.bound, .val) ∈ clauseLoopPairs), (hsep .sat .bound (by decide : (.sat, .bound) ∈ clauseLoopPairs)).symm, hsep .bound .cnf (by decide : (.bound, .cnf) ∈ clauseLoopPairs), hsep .cursor .cnf (by decide : (.cursor, .cnf) ∈ clauseLoopPairs), (hsep .sat .remaining (by decide : (.sat, .remaining) ∈ clauseLoopPairs)).symm, hsep .sat .done (by decide : (.sat, .done) ∈ clauseLoopPairs), hsep .sat .length (by decide : (.sat, .length) ∈ clauseLoopPairs), hsep .cursor .wBase (by decide : (.cursor, .wBase) ∈ clauseLoopPairs), hsep .pol .wBase (by decide : (.pol, .wBase) ∈ clauseLoopPairs), hsep .var .wBase (by decide : (.var, .wBase) ∈ clauseLoopPairs), hsep .done .wBase (by decide : (.done, .wBase) ∈ clauseLoopPairs), hsep .remaining .wBase (by decide : (.remaining, .wBase) ∈ clauseLoopPairs), hsep .bit .wBase (by decide : (.bit, .wBase) ∈ clauseLoopPairs), hsep .val .wBase (by decide : (.val, .wBase) ∈ clauseLoopPairs), hsep .sat .wBase (by decide : (.sat, .wBase) ∈ clauseLoopPairs), hsep .length .wBase (by decide : (.length, .wBase) ∈ clauseLoopPairs), hsep .cnf .wBase (by decide : (.cnf, .wBase) ∈ clauseLoopPairs), hsep .remaining .var (by decide : (.remaining, .var) ∈ clauseLoopPairs), hsep .remaining .pol (by decide : (.remaining, .pol) ∈ clauseLoopPairs), hsep .remaining .done (by decide : (.remaining, .done) ∈ clauseLoopPairs), hsep .remaining .bit (by decide : (.remaining, .bit) ∈ clauseLoopPairs), hsep .remaining .val (by decide : (.remaining, .val) ∈ clauseLoopPairs)⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hcp, hcv, hcdN, hvd, hbc, hbp, hbv, hbdN, hbr, hcl, hld, hrc, hcbit, hcval, hcsat, hbl, hbb, hbval, hbs, hbk, hck, hrs, hsd, hsl, hcw, hpw, hvw, hdw, hrw, hbw, hvalw, hsw, hlw, hkw, hrv, hrp, hrd, hrbit, hrval⟩
  set body := decodeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat)
    (reg .bit) (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound)
  refine programBoundedIn_forN_of_invariant B BND ρ (Expr.reg (reg .outer)) body
    (fun j τ => τ (reg .bound) = BND ∧ τ (reg .wBase) = WB ∧
      τ (reg .cursor) ≤ CUR + j * (1 + BND + BND * (BND + 1)))
    ?_ hcount (fun j _ => ?_) (fun j _ τ hI => ?_)
  · show ExprBoundedIn B ρ (Expr.reg (reg .outer))
    exact hoi
  · have hboundτ : (loopEval body j ρ) (reg .bound) = BND :=
      (decodeCNFEvalClauseStepAt_loopEval_bound_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound) j ρ
        hbc hbp hbv hbdN hbl hbr hbs hbb hbval hbk).trans hbd
    have hwτ : (loopEval body j ρ) (reg .wBase) = WB :=
      (decodeCNFEvalClauseStepAt_loopEval_wBase_frame (reg .cursor) (reg .pol) (reg .var) (reg .done)
        (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound) j ρ
        hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw).trans hwb
    have hcurτ : (loopEval body j ρ) (reg .cursor) ≤ CUR + j * (1 + BND + BND * (BND + 1)) := by
      have hg : (loopEval body j ρ) (reg .cursor) ≤
          ρ (reg .cursor) + j * (1 + ρ (reg .bound) + ρ (reg .bound) * (ρ (reg .bound) + 1)) :=
        decodeCNFEvalClauseStepAt_cursor_le (reg .cursor) (reg .pol) (reg .var) (reg .done)
          (reg .remaining) (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound) j ρ
          hcp hcv hcdN hcl hld hrc hcbit hcval hcsat hbc hbp hbv hbdN hbl hbr hbb hbval hbs hbk
          hck hrs
      rw [hbd] at hg
      omega
    exact ⟨hboundτ, hwτ, hcurτ⟩
  · obtain ⟨hbdτ, hwτ, hcurτ⟩ := hI
    have hjB : j ≤ BND := by omega
    have hmb : j * (1 + BND + BND * (BND + 1)) ≤ BND * (1 + BND + BND * (BND + 1)) :=
      Nat.mul_le_mul_right _ hjB
    refine programBoundedIn_decodeCNFEvalClauseStepAt_core B reg τ
      (Separates.of_subset hsep clauseStepPairs_subset_clauseLoopPairs)
      (RegsLe.mono clauseStepUsed_subset_clauseLoopUsed hidx) ⟨?_, ?_, ?_⟩
    · rw [hbdτ]; omega
    · rw [hwτ, hbdτ]; exact hwbudget
    · rw [hbdτ]; omega
/-- Resource of the outer clause loop from the loop-entry value bounds: with the count
register at most `BND`, the cursor at most `CUR`, and `bound`/`wBase` pinned to `BND`/`WB`,
every visit of the clause step fits the entry budgets.  The per-visit skeleton (bounded-count
`forN` under an invariant) is `programBoundedIn_forN_of_invariant`; this lemma supplies the
loop's frames/growth and the clause-step budgets. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseLoop_of_value_bounds
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg CUR WB BND : ℕ) (ρ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg) (hcsat : cursorReg ≠ satReg)
    (hbl : boundReg ≠ lengthReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg) (hck : cursorReg ≠ cnfReg)
    (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg) (hsl : satReg ≠ lengthReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hcount : ρ outerReg ≤ BND) (hcur : ρ cursorReg ≤ CUR) (hwb : ρ wBaseReg = WB)
    (hbd : ρ boundReg = BND)
    (hwbudget : WB + BND ≤ B)
    (houterCoarse : CUR + BND * (1 + BND + BND * (BND + 1)) + 2 + 2 * BND +
        BND * (BND + 1) ≤ B) :
    ProgramBoundedIn B ρ
      (Program.forN (.reg outerReg)
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg)) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcdN, hvd, hbc, hbp, hbv, hbdN, hbr⟩
  set reg : CNFEvalRole → ℕ := (fun
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
    | .length => lengthReg
    | .cnf => cnfReg
    | .bound => boundReg
    | _ => 0)
  have hstep : Separates reg clauseStepPairs := by
    intro a b h
    simp only [clauseStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | (exact Ne.symm (by assumption)) | nomatch hm
  have hextra : Separates reg [(.bound, .cnf), (.cursor, .cnf), (.cnf, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  refine programBoundedIn_decodeCNFEvalClauseLoop_core B reg CUR WB BND ρ
    (Separates.append hstep hextra) ?_ hcount hcur hwb hbd ⟨hwbudget, houterCoarse⟩
  · intro r hr
    simp only [clauseLoopUsed, clauseStepUsed, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption


/-- Layout version of the clause-loop resource core: separation and index bounds come
wholesale from the layout. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalClauseLoop_layout
    (R : RegLayout CNFEvalRole) (B CUR WB BND : ℕ) (ρ : Store) (hRB : R.top ≤ B + 1)
    (hcount : ρ (R.reg .outer) ≤ BND) (hcur : ρ (R.reg .cursor) ≤ CUR) (hwb : ρ (R.reg .wBase) = WB)
    (hbd : ρ (R.reg .bound) = BND) (hb : clauseLoopBudgets B CUR WB BND) :
    ProgramBoundedIn B ρ
      (Program.forN (.reg (R.reg .outer)) (decodeCNFEvalClauseStepAtL R.reg)) :=
  programBoundedIn_decodeCNFEvalClauseLoop_core B R.reg CUR WB BND ρ
    (R.separates clauseLoopPairs clauseLoopPairs_ne) (R.regsLe clauseLoopUsed hRB)
    hcount hcur hwb hbd hb

/-! ## Resource-carrying composition of the prefix and the outer loop

The evaluator's resource proof composed from stages that carry the local value bounds as
facts: `decodeCNFEvalResBounds` bounds the budget cells (`ValuesLeOn`) and pins them to the
entry store, the prefix stages transport the facts, and the loop's per-visit resource proof
reads its budgets off the loop invariant (the cursor growth and the pinned `wBase`/`bound`
values).  No stage assumes a global store bound; the composition replaces the manual
unfolding of the evaluator's `ProgramBoundedIn`. -/

/-- The local resource facts of one evaluator store: the budget cells are bounded by `B`
(`ValuesLeOn`) and pinned to the entry store's `wBase`/`bound`/`cursor` values. -/
@[stage_impl] def decodeCNFEvalResBounds (B cursorReg wBaseReg boundReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg
    ∧ τ boundReg = σ boundReg ∧ τ cursorReg = σ cursorReg

/-- The value-fixing pins of one evaluator store, assembled from cells. -/
def decodeCNFEvalPins (wBaseReg boundReg cursorReg : ℕ) (σ : Store) : StoreFact :=
  StoreFact.bigAnd [StoreFact.cell wBaseReg (σ wBaseReg), StoreFact.cell boundReg (σ boundReg),
    StoreFact.cell cursorReg (σ cursorReg)]

/-- The facts carried at the composition entry: the budget cells bounded and pinned. -/
def decodeCNFEvalEntryFacts (B cursorReg wBaseReg boundReg : ℕ) (σ : Store) : Store → Prop :=
  fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
    (decodeCNFEvalPins wBaseReg boundReg cursorReg σ).holds ρ

/-- The facts carried after the done seed. -/
def decodeCNFEvalDoneFacts (B cursorReg wBaseReg boundReg doneReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
    ((decodeCNFEvalPins wBaseReg boundReg cursorReg σ).holds ρ ∧ ρ doneReg = 0)

/-- The facts carried after the outer-count seed: the `wBase`/`bound` pins, the cursor
relaxed to a bound and the count role seeded. -/
def decodeCNFEvalSeededFacts (B cursorReg wBaseReg boundReg outerReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
    ((StoreFact.cell wBaseReg (σ wBaseReg)).holds ρ ∧
      (ρ cursorReg ≤ σ cursorReg ∧
        ((StoreFact.cell boundReg (σ boundReg)).holds ρ ∧ (StoreFact.cell outerReg 0).holds ρ)))

/-- The facts carried after the count decode: the `wBase`/`bound` pins and the cursor/counter
growth bounds. -/
def decodeCNFEvalDecodedFacts (B cursorReg wBaseReg boundReg outerReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
    ((StoreFact.cell wBaseReg (σ wBaseReg)).holds ρ ∧
      ((StoreFact.cell boundReg (σ boundReg)).holds ρ ∧
        (ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ outerReg ≤ 0 + σ boundReg)))

/-- The register pairs the program's resource proof separates: the clause loop's plus the
count-role pairs. -/
def progPairs : List (CNFEvalRole × CNFEvalRole) :=
  clauseLoopPairs ++ [(.cursor, .outer), (.done, .outer), (.outer, .bound), (.outer, .wBase)]

/-- The roles the program's resource proof indexes. -/
def progUsed : Set CNFEvalRole := clauseLoopUsed

lemma clauseLoopPairs_subset_progPairs : clauseLoopPairs ⊆ progPairs :=
  List.subset_append_left _ _

lemma clauseLoopUsed_subset_progUsed : clauseLoopUsed ⊆ progUsed :=
  fun _ hr => hr

lemma clauseStepPairs_subset_progPairs : clauseStepPairs ⊆ progPairs :=
  List.Subset.trans clauseStepPairs_subset_clauseLoopPairs clauseLoopPairs_subset_progPairs

/-- The pairs of `progPairs` are pairs of distinct roles. -/
lemma progPairs_ne (a b : CNFEvalRole) (h : (a, b) ∈ progPairs) : a ≠ b := by
  simp only [progPairs, List.mem_append] at h
  rcases h with h | h
  · exact clauseLoopPairs_ne a b h
  · simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | decide | nomatch hm

/-- The evaluator's resource composition at a role assignment: one proof against `reg`, from
the pairs it separates and the index bounds of the roles it names. -/
@[stage_impl] lemma decodeCNFEvalProgramAt_resource_stage_core
    (B : ℕ) (reg : CNFEvalRole → ℕ) (σ : Store)
    (hsep : Separates reg progPairs) (hidx : RegsLe reg progUsed B)
    (hb : decodeCNFEvalBudgets B (σ (reg .cursor)) (σ (reg .wBase)) (σ (reg .bound))) :
    StageSpec B (decodeCNFEvalResBounds B (reg .cursor) (reg .wBase) (reg .bound) σ)
      (decodeCNFEvalProgramAtL reg)
      (({reg .done} : Set ℕ) ∪ ({reg .outer} ∪
        ((fun r => r = reg .cursor ∨ r = reg .outer ∨ r = reg .done) ∪
          (fun r => r = reg .cursor ∨ r = reg .pol ∨ r = reg .var ∨ r = reg .done ∨
            r = reg .remaining ∨ r = reg .sat ∨ r = reg .bit ∨ r = reg .val ∨
            r = reg .length ∨ r = reg .cnf))))
      (fun _ => True) := by
  rcases hb with ⟨hwbudget, houterCoarse⟩
  rcases (⟨hidx .cursor (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .pol (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .var (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .done (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .outer (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .remaining (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .sat (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .bit (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .val (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .wBase (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .length (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .cnf (by simp [progUsed, clauseLoopUsed, clauseStepUsed]), hidx .bound (by simp [progUsed, clauseLoopUsed, clauseStepUsed])⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases (⟨hsep .cursor .pol (by decide : (.cursor, .pol) ∈ progPairs), hsep .cursor .var (by decide : (.cursor, .var) ∈ progPairs), hsep .cursor .done (by decide : (.cursor, .done) ∈ progPairs), hsep .var .done (by decide : (.var, .done) ∈ progPairs), hsep .bound .cursor (by decide : (.bound, .cursor) ∈ progPairs), hsep .bound .pol (by decide : (.bound, .pol) ∈ progPairs), hsep .bound .var (by decide : (.bound, .var) ∈ progPairs), hsep .bound .done (by decide : (.bound, .done) ∈ progPairs), hsep .bound .remaining (by decide : (.bound, .remaining) ∈ progPairs), hsep .cursor .length (by decide : (.cursor, .length) ∈ progPairs), hsep .length .done (by decide : (.length, .done) ∈ progPairs), hsep .remaining .cursor (by decide : (.remaining, .cursor) ∈ progPairs), hsep .cursor .bit (by decide : (.cursor, .bit) ∈ progPairs), hsep .cursor .val (by decide : (.cursor, .val) ∈ progPairs), (hsep .sat .cursor (by decide : (.sat, .cursor) ∈ progPairs)).symm, hsep .bound .length (by decide : (.bound, .length) ∈ progPairs), hsep .bound .bit (by decide : (.bound, .bit) ∈ progPairs), hsep .bound .val (by decide : (.bound, .val) ∈ progPairs), (hsep .sat .bound (by decide : (.sat, .bound) ∈ progPairs)).symm, hsep .bound .cnf (by decide : (.bound, .cnf) ∈ progPairs), hsep .cursor .cnf (by decide : (.cursor, .cnf) ∈ progPairs), (hsep .sat .remaining (by decide : (.sat, .remaining) ∈ progPairs)).symm, hsep .sat .done (by decide : (.sat, .done) ∈ progPairs), hsep .sat .length (by decide : (.sat, .length) ∈ progPairs), hsep .cursor .wBase (by decide : (.cursor, .wBase) ∈ progPairs), hsep .pol .wBase (by decide : (.pol, .wBase) ∈ progPairs), hsep .var .wBase (by decide : (.var, .wBase) ∈ progPairs), hsep .done .wBase (by decide : (.done, .wBase) ∈ progPairs), hsep .remaining .wBase (by decide : (.remaining, .wBase) ∈ progPairs), hsep .bit .wBase (by decide : (.bit, .wBase) ∈ progPairs), hsep .val .wBase (by decide : (.val, .wBase) ∈ progPairs), hsep .sat .wBase (by decide : (.sat, .wBase) ∈ progPairs), hsep .length .wBase (by decide : (.length, .wBase) ∈ progPairs), hsep .cnf .wBase (by decide : (.cnf, .wBase) ∈ progPairs), hsep .remaining .var (by decide : (.remaining, .var) ∈ progPairs), hsep .cursor .outer (by decide : (.cursor, .outer) ∈ progPairs), hsep .done .outer (by decide : (.done, .outer) ∈ progPairs), hsep .outer .bound (by decide : (.outer, .bound) ∈ progPairs), hsep .outer .wBase (by decide : (.outer, .wBase) ∈ progPairs), hsep .remaining .pol (by decide : (.remaining, .pol) ∈ progPairs), hsep .remaining .done (by decide : (.remaining, .done) ∈ progPairs), hsep .remaining .bit (by decide : (.remaining, .bit) ∈ progPairs), hsep .remaining .val (by decide : (.remaining, .val) ∈ progPairs)⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) with
    ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr, hcl, hld, hrc, hcbit, hcval, hcsat, hbl, hbb, hbval, hbs, hbk, hck, hrs, hsd, hsl, hcw, hpw, hvw, hdw, hrw, hbw, hvalw, hsw, hlw, hkw, hrv, hco, hdo, hoBnd, how, hrp, hrd, hrbit, hrval⟩
  have hC1 : ReadsOnly (fun a => a ≠ (reg .done))
      (decodeCNFEvalPins (reg .wBase) (reg .bound) (reg .cursor) σ).holds := by
    intro τ τ' he hτ
    exact ⟨(he (reg .wBase) hdw.symm).trans hτ.1, (he (reg .bound) hbd).trans hτ.2.1,
      (he (reg .cursor) hcd).trans hτ.2.2⟩
  have s1 : StageSpec B
      (decodeCNFEvalEntryFacts B (reg .cursor) (reg .wBase) (reg .bound) σ)
      (Program.assign (reg .done) (.const 0)) {(reg .done)}
      (decodeCNFEvalDoneFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .done) σ) :=
    StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hdi (by omega) hC1
  have hC2 : ReadsOnly (fun a => a ≠ (reg .outer))
      (fun ρ => (decodeCNFEvalPins (reg .wBase) (reg .bound) (reg .cursor) σ).holds ρ ∧
        ρ (reg .done) = 0) := by
    intro τ τ' he hτ
    exact ⟨⟨(he (reg .wBase) how.symm).trans hτ.1.1, (he (reg .bound) hoBnd.symm).trans hτ.1.2.1,
      (he (reg .cursor) hco).trans hτ.1.2.2⟩, (he (reg .done) hdo).trans hτ.2⟩
  have s2 : StageSpec B
      (decodeCNFEvalDoneFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .done) σ)
      (Program.assign (reg .outer) (.const 0)) {(reg .outer)}
      (decodeCNFEvalSeededFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .outer) σ) :=
    (StageSpec.assign_const_carry (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hoi (by omega)
      hC2).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc⟩, hdone⟩ := hpins
      have hc' : ρ (reg .cursor) = σ (reg .cursor) := hc
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC3 : ReadsOnly (fun a => a ≠ (reg .cursor) ∧ a ≠ (reg .outer) ∧ a ≠ (reg .done))
      (StoreFact.cell (reg .wBase) (σ (reg .wBase))).holds := by
    intro τ τ' he hτ
    exact (he (reg .wBase) ⟨hcw.symm, how.symm, hdw.symm⟩).trans hτ
  have hdS : (reg .done) ∉ ({(reg .wBase), (reg .bound), (reg .cursor)} : Set ℕ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hdw h
    · exact hbd.symm h
    · exact hcd.symm h
  have s3 : StageSpec B
      (decodeCNFEvalSeededFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .outer) σ)
      (decodeNatProgramAt (reg .cursor) (reg .outer) (reg .done) (reg .bound))
      (fun r => r = (reg .cursor) ∨ r = (reg .outer) ∨ r = (reg .done))
      (decodeCNFEvalDecodedFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .outer) σ) :=
    StageSpec.decodeUnaryAt (cg := σ (reg .cursor)) (k0 := 0) (lrv := σ (reg .bound))
      (c := (reg .cursor)) (k := (reg .outer)) (d := (reg .done)) (lr := (reg .bound))
      (S := {(reg .wBase), (reg .bound), (reg .cursor)}) hco hcd hdo.symm
      ⟨hbc, hoBnd.symm, hbd⟩ ⟨hci, hoi, hdi, hbi⟩ hC3 hdS (by omega) (by omega)
  have s4 : StageSpec B
      (decodeCNFEvalDecodedFacts B (reg .cursor) (reg .wBase) (reg .bound) (reg .outer) σ)
      (Program.forN (.reg (reg .outer))
        (decodeCNFEvalClauseStepAt (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining) (reg .sat) (reg .bit)
          (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound)))
      (fun r => r = (reg .cursor) ∨ r = (reg .pol) ∨ r = (reg .var) ∨ r = (reg .done) ∨ r = (reg .remaining) ∨
        r = (reg .sat) ∨ r = (reg .bit) ∨ r = (reg .val) ∨ r = (reg .length) ∨ r = (reg .cnf))
      (fun _ => True) := by
    refine StageSpec.of_avoids ?_ (fun _ _ => trivial) (fun ρ hρ => ?_)
    · refine Program.Avoids.mono (P := fun r => r ≠ (reg .cursor) ∧ r ≠ (reg .pol) ∧ r ≠ (reg .var) ∧
          r ≠ (reg .done) ∧ r ≠ (reg .remaining) ∧ r ≠ (reg .sat) ∧ r ≠ (reg .bit) ∧ r ≠ (reg .val) ∧
          r ≠ (reg .length) ∧ r ≠ (reg .cnf)) ?_
        (fun r hr => ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr (Or.inl h)),
          fun h => hr (Or.inr (Or.inr (Or.inl h))), fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))⟩)
      exact decodeCNFEvalClauseStepAt_avoids_frame (reg .cursor) (reg .pol) (reg .var) (reg .done) (reg .remaining)
        (reg .sat) (reg .bit) (reg .val) (reg .wBase) (reg .length) (reg .cnf) (reg .bound)
    · obtain ⟨hvals, hwρ, hbdρ, hcurρ, houtρ⟩ := hρ
      exact programBoundedIn_decodeCNFEvalClauseLoop_core B reg
        (σ (reg .cursor) + σ (reg .bound)) (σ (reg .wBase)) (σ (reg .bound)) ρ
        (Separates.of_subset hsep clauseLoopPairs_subset_progPairs)
        (RegsLe.mono clauseLoopUsed_subset_progUsed hidx)
        (by omega) hcurρ hwρ hbdρ ⟨hwbudget, houterCoarse⟩
  exact StageSpec.seq s1 (StageSpec.seq s2 (StageSpec.seq s3 s4))
/-- Resource-carrying stage for the evaluator's clause-count prefix and outer loop: the
prefix stages carry the local bounds as facts, and the loop's per-visit resource proof is
the clause-step bounds read off the loop invariant. -/
@[stage_impl] lemma decodeCNFEvalProgramAt_resource_stage
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg) (hcsat : cursorReg ≠ satReg)
    (hbl : boundReg ≠ lengthReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg) (hck : cursorReg ≠ cnfReg)
    (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg) (hsl : satReg ≠ lengthReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hco : cursorReg ≠ outerReg) (hdo : doneReg ≠ outerReg) (hoBnd : outerReg ≠ boundReg)
    (how : outerReg ≠ wBaseReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg +
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) +
        2 + 2 * σ boundReg + σ boundReg * (σ boundReg + 1) ≤ B) :
    StageSpec B (decodeCNFEvalResBounds B cursorReg wBaseReg boundReg σ)
      (decodeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg cnfReg boundReg)
      (({doneReg} : Set ℕ) ∪ ({outerReg} ∪
        ((fun r => r = cursorReg ∨ r = outerReg ∨ r = doneReg) ∪
          (fun r => r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨ r = remainingReg ∨
            r = satReg ∨ r = bitReg ∨ r = valReg ∨ r = lengthReg ∨ r = cnfReg))))
      (fun _ => True) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  set reg : CNFEvalRole → ℕ := (fun
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
    | .length => lengthReg
    | .cnf => cnfReg
    | .bound => boundReg
    | _ => 0)
  have hstep : Separates reg clauseStepPairs := by
    intro a b h
    simp only [clauseStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | (exact Ne.symm (by assumption)) | nomatch hm
  have hextra : Separates reg [(.bound, .cnf), (.cursor, .cnf), (.cnf, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  have houter : Separates reg
      [(.cursor, .outer), (.done, .outer), (.outer, .bound), (.outer, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  refine decodeCNFEvalProgramAt_resource_stage_core B reg σ
    (Separates.append (Separates.append hstep hextra) houter) ?_ ⟨hwbudget, houterCoarse⟩
  · intro r hr
    simp only [progUsed, clauseLoopUsed, clauseStepUsed, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- Layout version of the resource composition core: separation and index bounds come
wholesale from the layout. -/
@[stage_impl] lemma decodeCNFEvalProgramAt_resource_stage_layout
    (R : RegLayout CNFEvalRole) (B : ℕ) (σ : Store) (hRB : R.top ≤ B + 1)
    (hb : decodeCNFEvalBudgets B (σ (R.reg .cursor)) (σ (R.reg .wBase)) (σ (R.reg .bound))) :
    StageSpec B (decodeCNFEvalResBounds B (R.reg .cursor) (R.reg .wBase) (R.reg .bound) σ)
      (decodeCNFEvalProgramAtL R.reg)
      (({R.reg .done} : Set ℕ) ∪ ({R.reg .outer} ∪
        ((fun r => r = R.reg .cursor ∨ r = R.reg .outer ∨ r = R.reg .done) ∪
          (fun r => r = R.reg .cursor ∨ r = R.reg .pol ∨ r = R.reg .var ∨ r = R.reg .done ∨
            r = R.reg .remaining ∨ r = R.reg .sat ∨ r = R.reg .bit ∨ r = R.reg .val ∨
            r = R.reg .length ∨ r = R.reg .cnf))))
      (fun _ => True) :=
  decodeCNFEvalProgramAt_resource_stage_core B R.reg σ
    (R.separates progPairs progPairs_ne) (R.regsLe progUsed hRB) hb

/-- The program's resource body at a role assignment: the composed stage's resource
component read off at the entry store. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalProgramAt_core
    (B : ℕ) (reg : CNFEvalRole → ℕ) (σ : Store)
    (hsep : Separates reg progPairs) (hidx : RegsLe reg progUsed B)
    (hb : decodeCNFEvalBudgets B (σ (reg .cursor)) (σ (reg .wBase)) (σ (reg .bound))) :
    ProgramBoundedIn B σ (decodeCNFEvalProgramAtL reg) := by
  rcases hb with ⟨hwbudget, houterCoarse⟩
  exact ((decodeCNFEvalProgramAt_resource_stage_core B reg σ hsep hidx
    ⟨hwbudget, houterCoarse⟩) σ
    ⟨fun a ha => by
      rcases Set.mem_insert_iff.mp ha with h | h
      · subst h; omega
      · rcases Set.mem_insert_iff.mp h with h | h
        · subst h; omega
        · rw [Set.mem_singleton_iff] at h
          subst h
          omega,
      rfl, rfl, rfl⟩).2.2

/-- `programBoundedIn_decodeCNFEvalProgramAt_of_store_bounds` without `StoreValuesLe`: at
any store whose cursor/`wBase`/`bound` values fit the coarse budget, the evaluator's
operands stay within `B`.  This is the resource component of the composed stage
`decodeCNFEvalProgramAt_resource_stage` read off at the entry store. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalProgramAt_of_value_bounds
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      lengthReg ≤ B ∧ cnfReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hcl : cursorReg ≠ lengthReg) (hld : lengthReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg) (hcsat : cursorReg ≠ satReg)
    (hbl : boundReg ≠ lengthReg) (hbb : boundReg ≠ bitReg) (hbval : boundReg ≠ valReg)
    (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg) (hck : cursorReg ≠ cnfReg)
    (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg) (hsl : satReg ≠ lengthReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg) (hlw : lengthReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hco : cursorReg ≠ outerReg) (hdo : doneReg ≠ outerReg) (hoBnd : outerReg ≠ boundReg)
    (how : outerReg ≠ wBaseReg)
    (hrp : remainingReg ≠ polReg) (hrd : remainingReg ≠ doneReg)
    (hrbit : remainingReg ≠ bitReg) (hrval : remainingReg ≠ valReg)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg +
        σ boundReg * (1 + σ boundReg + σ boundReg * (σ boundReg + 1)) +
        2 + 2 * σ boundReg + σ boundReg * (σ boundReg + 1) ≤ B) :
    ProgramBoundedIn B σ
      (decodeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg cnfReg boundReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  set reg : CNFEvalRole → ℕ := (fun
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
    | .length => lengthReg
    | .cnf => cnfReg
    | .bound => boundReg
    | _ => 0)
  have hstep : Separates reg clauseStepPairs := by
    intro a b h
    simp only [clauseStepPairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | (exact Ne.symm (by assumption)) | nomatch hm
  have hextra : Separates reg [(.bound, .cnf), (.cursor, .cnf), (.cnf, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  have houter : Separates reg
      [(.cursor, .outer), (.done, .outer), (.outer, .bound), (.outer, .wBase)] := by
    intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
    all_goals first | assumption | nomatch hm
  exact programBoundedIn_decodeCNFEvalProgramAt_core B reg σ
    (Separates.append (Separates.append hstep hextra) houter)
    (fun r hr => by
      simp only [progUsed, clauseLoopUsed, clauseStepUsed, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals assumption)
    ⟨hwbudget, houterCoarse⟩

/-- Layout version of the program's resource core: separation and index bounds come
wholesale from the layout. -/
@[stage_impl] lemma programBoundedIn_decodeCNFEvalProgramAt_layout
    (R : RegLayout CNFEvalRole) (B : ℕ) (σ : Store) (hRB : R.top ≤ B + 1)
    (hb : decodeCNFEvalBudgets B (σ (R.reg .cursor)) (σ (R.reg .wBase)) (σ (R.reg .bound))) :
    ProgramBoundedIn B σ (decodeCNFEvalProgramAtL R.reg) :=
  programBoundedIn_decodeCNFEvalProgramAt_core B R.reg σ
    (R.separates progPairs progPairs_ne) (R.regsLe progUsed hRB) hb

/-! ## Resource-connected stage contracts

Each contract below is the `CNFEvalAt` stage contract with its resource component proved
inside, from role-level budgets over the fact values: `hwbudget`/`hinner`/`houterCoarse`
pin the arithmetic the program's operands perform, and the layout's injectivity supplies
every distinctness obligation.  A caller never proves `ProgramBoundedIn` of the program
and never sees a register number. -/

/-- The clause step as a bundled stage whose resource component follows from the entry
budgets. -/
@[stage_contract] lemma decodeCNFEvalClauseStepAt_stage_of_bounds (R : RegLayout CNFEvalRole)
    (B addr v wBase bound : ℕ) (c : Clause) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound_c : c.lits.length + 1 ≤ bound)
    (hvarbound_c : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hwbudget : wBase + bound ≤ B)
    (hinner : addr + 2 + 2 * bound + bound * (bound + 1) ≤ B) :
    LayoutStage R B (decodeCNFEvalClauseStepAtL R.reg)
      (clauseInvFact R addr v wBase bound (((c :: cs).map encodeClause).flatten ++ rest)
        (c :: cs) w haddr hb)
      (clauseInvFact R (addr + (encodeClause c).length) (if clauseSatBool w c then v else 0)
        wBase bound ((cs.map encodeClause).flatten ++ rest) cs w (by omega) hb)
      (stepFoot R) := by
  refine decodeCNFEvalClauseStepAt_stage R B addr v wBase bound c cs rest w haddr hb hWA
    hbound_c hvarbound_c (fun σ hσ => ?_)
  obtain ⟨hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
  have hRB : R.top ≤ B + 1 := by
    have h1 : addr ≤ B := by omega
    omega
  exact programBoundedIn_decodeCNFEvalClauseStepAt_layout R B σ hRB
    ⟨by rw [hcur, hbd]; omega, by rw [hwb, hbd]; exact hwbudget,
      by rw [hcur, hbd]; exact hinner⟩

/-- The clause loop as a bundled stage whose resource component follows from the entry
budgets and the loop count carried by the outer role. -/
@[stage_contract] lemma decodeCNFEvalClauseLoop_stage_of_bounds (R : RegLayout CNFEvalRole)
    (B addr v wBase bound : ℕ) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hs0 : v = 0 ∨ v = 1)
    (hbound : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hlen : cs.length + 1 ≤ bound)
    (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) :
    LayoutStage R B
      (Program.forN (.reg (R.reg .outer)) (decodeCNFEvalClauseStepAtL R.reg))
      (LayoutFact.bigAnd [LayoutFact.reg .outer cs.length,
        clauseInvFact R addr v wBase bound ((cs.map encodeClause).flatten ++ rest) cs w haddr
          hb])
      (LayoutFact.bigAnd [LayoutFact.reg .outer cs.length,
        clauseInvFact R (addr + (cs.map encodeClause).flatten.length)
          (if v = 1 ∧ ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) wBase bound rest [] w
          (by omega) hb])
      (stepFoot R) := by
  refine decodeCNFEvalClauseLoop_stage R B addr v wBase bound cs rest w haddr hb hWA hs0 hbound
    hvarbound (fun σ hσ => ?_)
  obtain ⟨hcount, hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
  have hRB : R.top ≤ B + 1 := by
    have h1 : addr ≤ B := by omega
    omega
  exact programBoundedIn_decodeCNFEvalClauseLoop_layout R B (addr + bound) wBase bound σ hRB
    (by rw [hcount]; omega) (by rw [hcur]; exact Nat.le_add_right _ _) hwb hbd
    ⟨hwbudget, houterCoarse⟩

/-- The whole evaluator as a bundled stage whose resource component follows from the entry
budgets. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_stage_of_bounds (R : RegLayout CNFEvalRole)
    (B addr wBase bound : ℕ) (cs : List Clause) (rest : Bits) (w : List Bool)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) :
    LayoutStage R B (decodeCNFEvalProgramAtL R.reg)
      (clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr hb)
      (LayoutFact.reg .cnf (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0))
      (progFoot R) := by
  refine decodeCNFEvalProgramAt_stage R B addr wBase bound cs rest w haddr hb hWA hbound
    hbound2 hvarbound (fun σ hσ => ?_)
  obtain ⟨hcur, hcnf, hwb, hbd, hbits, hwit⟩ := hσ
  have hRB : R.top ≤ B + 1 := by
    have h1 : addr ≤ B := by omega
    omega
  exact programBoundedIn_decodeCNFEvalProgramAt_layout R B σ hRB
    ⟨by rw [hwb, hbd]; exact hwbudget, by rw [hcur, hbd]; exact houterCoarse⟩

#check_stage_discipline all

end NPComplete.CookLevin

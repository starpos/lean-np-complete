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
open NPComplete.BoundedWhile (RegLayout LayoutFact)
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
  have hprefix : ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg) :=
    programBoundedIn_decodeClauseWithLengthPrefixAt_of_value_bounds B cursorReg doneReg
      remainingReg lengthReg boundReg σ ⟨hci, hdi, hri, hli, hbi⟩
      ⟨hcd, hcl, hld, hbc, hbl, hbd⟩ hbudget
  have hprefixBound : (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
      boundReg).eval σ boundReg = σ boundReg :=
    decodeClauseWithLengthPrefixAt_bound_frame cursorReg doneReg remainingReg lengthReg boundReg σ
      hbc hbd hbl hbr
  have hprefixRem : (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
      boundReg).eval σ remainingReg ≤ σ boundReg :=
    decodeClauseWithLengthPrefixAt_remaining_le cursorReg doneReg remainingReg lengthReg
      boundReg σ hcl hld hbd hbl
  have hprefixCur : (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
      boundReg).eval σ cursorReg ≤ σ cursorReg + 1 + σ boundReg :=
    decodeClauseWithLengthPrefixAt_cursor_le cursorReg doneReg remainingReg lengthReg boundReg σ
      hcd hcl hrc hbl hbd
  have hprefixW : (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
      boundReg).eval σ wBaseReg = σ wBaseReg :=
    decodeClauseWithLengthPrefixAt_frame cursorReg doneReg remainingReg lengthReg boundReg
      wBaseReg σ hcw.symm hdw.symm hrw.symm hlw.symm
  set σ0 := (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg
    boundReg).eval σ with hσ0def
  set σ1 := (Program.assign satReg (.const 0)).eval σ0 with hσ1def
  have hσ1rem : σ1 remainingReg = σ0 remainingReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 remainingReg hsr.symm
  have hσ1bnd : σ1 boundReg = σ0 boundReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 boundReg hsb.symm
  have hσ1w : σ1 wBaseReg = σ0 wBaseReg := by
    rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 wBaseReg hsw.symm
  have hBndEq : σ1 boundReg = σ boundReg := by rw [hσ1bnd, hprefixBound]
  have hRemLe1 : σ1 remainingReg ≤ σ boundReg := by rw [hσ1rem]; exact hprefixRem
  have hσ1wbase : σ1 wBaseReg = σ wBaseReg := by rw [hσ1w, hprefixW]
  have hσ1cur : σ1 cursorReg ≤ σ cursorReg + 1 + σ boundReg := by
    have h1 : σ1 cursorReg = σ0 cursorReg := by
      rw [hσ1def, eval_assign, Expr.eval]; exact writeReg_diff σ0 satReg 0 cursorReg hsc.symm
    rw [h1]; exact hprefixCur
  have hloop : ProgramBoundedIn B σ1
      (Program.forN (.reg remainingReg)
        (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg boundReg)) := by
    refine programBoundedIn_forN_of_invariant B (σ boundReg) σ1 (.reg remainingReg) _
      (fun j τ => τ boundReg = σ boundReg ∧ τ wBaseReg = σ wBaseReg ∧
        τ remainingReg ≤ σ1 remainingReg ∧
        τ cursorReg ≤ σ1 cursorReg + j * (σ boundReg + 1))
      (show ExprBoundedIn B σ1 (Expr.reg remainingReg) from hri) ?_ (fun j _ => ?_)
      (fun j _ τ hI => ?_)
    · show (Expr.reg remainingReg).eval σ1 ≤ σ boundReg
      simp only [Expr.eval]
      exact hRemLe1
    · have hboundτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg
            remainingReg satReg bitReg valReg wBaseReg boundReg) j σ1) boundReg = σ boundReg :=
        (decodeClauseEvalStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg j σ1 hbc hbp hbv hbd hbr hsb.symm hbb
          hbval).trans hBndEq
      have hwτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg) j σ1) wBaseReg = σ wBaseReg :=
        (decodeClauseEvalStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg j σ1 hcw hpw hvw hdw hrw hbitw hvw2
          hsw).trans hσ1wbase
      have hremτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg) j σ1) remainingReg ≤ σ1 remainingReg :=
        decodeClauseEvalStepAt_loopEval_remaining_le cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg j σ1 hrc hrp hrv hrd hrbit hrval hsr.symm
      have hcurτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg) j σ1) cursorReg ≤
          σ1 cursorReg + j * (σ boundReg + 1) := by
        rw [← hBndEq]
        exact decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg j σ1
          hcp hcv hcd hrc hcbit hcval hsc.symm hbc hbp hbv hbd hbr hbb hbval hsb.symm
      exact ⟨hboundτ, hwτ, hremτ, hcurτ⟩
    · obtain ⟨hbdτ, hwτ, hremτ, hcurτ⟩ := hI
      have hjB : j ≤ σ boundReg := by omega
      have hmb : j * (σ boundReg + 1) ≤ σ boundReg * (σ boundReg + 1) :=
        Nat.mul_le_mul_right _ hjB
      have hcurm : τ cursorReg ≤ B := by omega
      have hremm : ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval τ)
          remainingReg ≤ B := by
        rw [decodeLiteralValueProgramAt_frame cursorReg polReg varReg doneReg boundReg remainingReg
          τ hrc hrp hrv hrd]
        omega
      have hbudm : τ cursorReg + 1 + τ boundReg ≤ B := by rw [hbdτ]; omega
      have hwbm : τ wBaseReg + τ boundReg ≤ B := by rw [hwτ, hbdτ]; exact hwbudget
      exact programBoundedIn_decodeClauseEvalStepAt_of_local_bounds B cursorReg polReg varReg
        doneReg remainingReg satReg bitReg valReg wBaseReg boundReg τ
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
        hcw hpw hvw hdw hrw hrv hcurm hremm hbudm hwbm
  have hclause : ProgramBoundedIn B σ
      (decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg boundReg) := by
    unfold decodeClauseEvalWithLengthProgramAt
    simp only [ProgramBoundedIn]
    exact ⟨hprefix, ⟨⟨hsi, Nat.zero_le B⟩, hloop⟩⟩
  change ProgramBoundedIn B σ
      ((decodeClauseEvalWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg boundReg).seq (andIntoProg satReg cnfReg))
  simp only [ProgramBoundedIn]
  exact ⟨hclause, programBoundedIn_andIntoProg B satReg cnfReg _ hsi hki⟩

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
  set body := decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
    bitReg valReg wBaseReg lengthReg cnfReg boundReg
  refine programBoundedIn_forN_of_invariant B BND ρ (Expr.reg outerReg) body
    (fun j τ => τ boundReg = BND ∧ τ wBaseReg = WB ∧
      τ cursorReg ≤ CUR + j * (1 + BND + BND * (BND + 1)))
    ?_ hcount (fun j _ => ?_) (fun j _ τ hI => ?_)
  · show ExprBoundedIn B ρ (Expr.reg outerReg)
    exact hoi
  · have hboundτ : (loopEval body j ρ) boundReg = BND :=
      (decodeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg j ρ
        hbc hbp hbv hbdN hbl hbr hbs hbb hbval hbk).trans hbd
    have hwτ : (loopEval body j ρ) wBaseReg = WB :=
      (decodeCNFEvalClauseStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg j ρ
        hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw).trans hwb
    have hcurτ : (loopEval body j ρ) cursorReg ≤ CUR + j * (1 + BND + BND * (BND + 1)) := by
      have hg : (loopEval body j ρ) cursorReg ≤
          ρ cursorReg + j * (1 + ρ boundReg + ρ boundReg * (ρ boundReg + 1)) :=
        decodeCNFEvalClauseStepAt_cursor_le cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg j ρ
          hcp hcv hcdN hcl hld hrc hcbit hcval hcsat hbc hbp hbv hbdN hbl hbr hbb hbval hbs hbk
          hck hrs
      rw [hbd] at hg
      omega
    exact ⟨hboundτ, hwτ, hcurτ⟩
  · obtain ⟨hbdτ, hwτ, hcurτ⟩ := hI
    have hjB : j ≤ BND := by omega
    have hmb : j * (1 + BND + BND * (BND + 1)) ≤ BND * (1 + BND + BND * (BND + 1)) :=
      Nat.mul_le_mul_right _ hjB
    refine programBoundedIn_decodeCNFEvalClauseStepAt_of_value_bounds B cursorReg polReg
      varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg τ
      ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
      ⟨hcp, hcv, hcdN, hvd, hbc, hbp, hbv, hbdN, hbr⟩
      hcl hld hrc hrv hbl hrp hrd hrbit hrval hcw hpw hvw hdw hrw hlw hcbit hcval hbb hbval
      hbw hvalw ⟨hcsat.symm, hsd, hrs.symm, hsl, hbs.symm, hsw⟩ ?_ ?_ ?_
    · rw [hbdτ]; omega
    · rw [hwτ, hbdτ]; exact hwbudget
    · rw [hbdτ]; omega


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
  have hC1 : ReadsOnly (fun a => a ≠ doneReg)
      (fun ρ => ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg) := by
    intro τ τ' he hτ
    exact ⟨(he wBaseReg hdw.symm).trans hτ.1, (he boundReg hbd).trans hτ.2.1,
      (he cursorReg hcd).trans hτ.2.2⟩
  have s1 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg))
      (Program.assign doneReg (.const 0)) {doneReg}
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg) ∧
        ρ doneReg = 0) :=
    StageSpec.assign_const_carry (S := {wBaseReg, boundReg, cursorReg}) hdi (by omega) hC1
  have hC2 : ReadsOnly (fun a => a ≠ outerReg)
      (fun ρ => (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg)
        ∧ ρ doneReg = 0) := by
    intro τ τ' he hτ
    exact ⟨⟨(he wBaseReg how.symm).trans hτ.1.1, (he boundReg hoBnd.symm).trans hτ.1.2.1,
      (he cursorReg hco).trans hτ.1.2.2⟩, (he doneReg hdo).trans hτ.2⟩
  have s2 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg) ∧
        ρ doneReg = 0)
      (Program.assign outerReg (.const 0)) {outerReg}
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg ∧ ρ boundReg = σ boundReg ∧ ρ outerReg = 0) :=
    (StageSpec.assign_const_carry (S := {wBaseReg, boundReg, cursorReg}) hoi (by omega)
      hC2).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc⟩, hdone⟩ := hpins
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC3 : ReadsOnly (fun a => a ≠ cursorReg ∧ a ≠ outerReg ∧ a ≠ doneReg)
      (fun ρ => ρ wBaseReg = σ wBaseReg) := by
    intro τ τ' he hτ
    exact (he wBaseReg ⟨hcw.symm, how.symm, hdw.symm⟩).trans hτ
  have hdS : doneReg ∉ ({wBaseReg, boundReg, cursorReg} : Set ℕ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hdw h
    · exact hbd.symm h
    · exact hcd.symm h
  have s3 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg ∧ ρ boundReg = σ boundReg ∧ ρ outerReg = 0)
      (decodeNatProgramAt cursorReg outerReg doneReg boundReg)
      (fun r => r = cursorReg ∨ r = outerReg ∨ r = doneReg)
      (fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg ∧
        τ boundReg = σ boundReg ∧ τ cursorReg ≤ σ cursorReg + σ boundReg ∧
        τ outerReg ≤ 0 + σ boundReg) :=
    StageSpec.decodeUnaryAt (cg := σ cursorReg) (k0 := 0) (lrv := σ boundReg)
      (c := cursorReg) (k := outerReg) (d := doneReg) (lr := boundReg)
      (S := {wBaseReg, boundReg, cursorReg}) hco hcd hdo.symm
      ⟨hbc, hoBnd.symm, hbd⟩ ⟨hci, hoi, hdi, hbi⟩ hC3 hdS (by omega) (by omega)
  have s4 : StageSpec B
      (fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg ∧
        τ boundReg = σ boundReg ∧ τ cursorReg ≤ σ cursorReg + σ boundReg ∧
        τ outerReg ≤ 0 + σ boundReg)
      (Program.forN (.reg outerReg)
        (decodeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg lengthReg cnfReg boundReg))
      (fun r => r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨ r = remainingReg ∨
        r = satReg ∨ r = bitReg ∨ r = valReg ∨ r = lengthReg ∨ r = cnfReg)
      (fun _ => True) := by
    refine StageSpec.of_avoids ?_ (fun _ _ => trivial) (fun ρ hρ => ?_)
    · refine Program.Avoids.mono (P := fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧
          r ≠ doneReg ∧ r ≠ remainingReg ∧ r ≠ satReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧
          r ≠ lengthReg ∧ r ≠ cnfReg) ?_
        (fun r hr => ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr (Or.inl h)),
          fun h => hr (Or.inr (Or.inr (Or.inl h))), fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))⟩)
      exact decodeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg
    · obtain ⟨hvals, hwρ, hbdρ, hcurρ, houtρ⟩ := hρ
      exact programBoundedIn_decodeCNFEvalClauseLoop_of_value_bounds B cursorReg polReg varReg
        doneReg outerReg remainingReg satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg
        (σ cursorReg + σ boundReg) (σ wBaseReg) (σ boundReg) ρ
        ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hli, hki, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
        hcl hld hrc hcbit hcval hcsat hbl hbb hbval hbs hbk hck hrs hsd hsl
        hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw hrv hrp hrd hrbit hrval
        (by omega) hcurρ hwρ hbdρ hwbudget houterCoarse
  exact StageSpec.seq s1 (StageSpec.seq s2 (StageSpec.seq s3 s4))

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
        bitReg valReg wBaseReg lengthReg cnfReg boundReg) :=
  ((decodeCNFEvalProgramAt_resource_stage B cursorReg polReg varReg doneReg outerReg remainingReg
    satReg bitReg valReg wBaseReg lengthReg cnfReg boundReg σ hidx hdist hcl hld hrc hcbit hcval
    hcsat hbl hbb hbval hbs hbk hck hrs hsd hsl hcw hpw hvw hdw hrw hbw hvalw hsw hlw hkw hrv
    hco hdo hoBnd how hrp hrd hrbit hrval hwbudget houterCoarse) σ
    ⟨fun a ha => by
      rcases Set.mem_insert_iff.mp ha with h | h
      · subst h; omega
      · rcases Set.mem_insert_iff.mp h with h | h
        · subst h; omega
        · rw [Set.mem_singleton_iff] at h
          subst h
          omega,
      rfl, rfl, rfl⟩).2.2

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
  have hRB : R.top ≤ B := by
    have h1 : addr ≤ B := by omega
    omega
  have hreg : ∀ role : CNFEvalRole, R.reg role ≤ B := by
    intro role
    exact Nat.le_of_lt (R.reg_lt_of_top_le role hRB)
  exact programBoundedIn_decodeCNFEvalClauseStepAt_of_value_bounds B
    (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done) (R.reg .remaining) (R.reg .sat)
    (R.reg .bit) (R.reg .val) (R.reg .wBase) (R.reg .length) (R.reg .cnf) (R.reg .bound) σ
    (hidx := ⟨hreg .cursor, hreg .pol, hreg .var, hreg .done, hreg .remaining, hreg .sat,
      hreg .bit, hreg .val, hreg .wBase, hreg .length, hreg .cnf, hreg .bound⟩)
    (hdist := ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide)⟩)
    (hcl := R.reg_ne (by decide)) (hld := R.reg_ne (by decide))
    (hrc := R.reg_ne (by decide)) (hrv := R.reg_ne (by decide))
    (hbl := R.reg_ne (by decide)) (hrp := R.reg_ne (by decide))
    (hrd := R.reg_ne (by decide)) (hrbit := R.reg_ne (by decide))
    (hrval := R.reg_ne (by decide)) (hcw := R.reg_ne (by decide))
    (hpw := R.reg_ne (by decide)) (hvw := R.reg_ne (by decide))
    (hdw := R.reg_ne (by decide)) (hrw := R.reg_ne (by decide))
    (hlw := R.reg_ne (by decide)) (hcbit := R.reg_ne (by decide))
    (hcval := R.reg_ne (by decide)) (hbb := R.reg_ne (by decide))
    (hbval := R.reg_ne (by decide)) (hbitw := R.reg_ne (by decide))
    (hvw2 := R.reg_ne (by decide))
    (hsatFrame := ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide)⟩)
    (hbudget := by rw [hcur, hbd]; omega)
    (hwbudget := by rw [hwb, hbd]; exact hwbudget)
    (hinner := by rw [hcur, hbd]; exact hinner)

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
  have hRB : R.top ≤ B := by
    have h1 : addr ≤ B := by omega
    omega
  have hreg : ∀ role : CNFEvalRole, R.reg role ≤ B := by
    intro role
    exact Nat.le_of_lt (R.reg_lt_of_top_le role hRB)
  exact programBoundedIn_decodeCNFEvalClauseLoop_of_value_bounds B
    (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done) (R.reg .outer) (R.reg .remaining)
    (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase) (R.reg .length) (R.reg .cnf)
    (R.reg .bound) (addr + bound) wBase bound σ
    (hidx := ⟨hreg .cursor, hreg .pol, hreg .var, hreg .done, hreg .outer, hreg .remaining,
      hreg .sat, hreg .bit, hreg .val, hreg .wBase, hreg .length, hreg .cnf, hreg .bound⟩)
    (hdist := ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide)⟩)
    (hcl := R.reg_ne (by decide)) (hld := R.reg_ne (by decide))
    (hrc := R.reg_ne (by decide)) (hcbit := R.reg_ne (by decide))
    (hcval := R.reg_ne (by decide)) (hcsat := R.reg_ne (by decide))
    (hbl := R.reg_ne (by decide)) (hbb := R.reg_ne (by decide))
    (hbval := R.reg_ne (by decide)) (hbs := R.reg_ne (by decide))
    (hbk := R.reg_ne (by decide)) (hck := R.reg_ne (by decide))
    (hrs := R.reg_ne (by decide)) (hsd := R.reg_ne (by decide))
    (hsl := R.reg_ne (by decide)) (hcw := R.reg_ne (by decide))
    (hpw := R.reg_ne (by decide)) (hvw := R.reg_ne (by decide))
    (hdw := R.reg_ne (by decide)) (hrw := R.reg_ne (by decide))
    (hbw := R.reg_ne (by decide)) (hvalw := R.reg_ne (by decide))
    (hsw := R.reg_ne (by decide)) (hlw := R.reg_ne (by decide))
    (hkw := R.reg_ne (by decide)) (hrv := R.reg_ne (by decide))
    (hrp := R.reg_ne (by decide)) (hrd := R.reg_ne (by decide))
    (hrbit := R.reg_ne (by decide)) (hrval := R.reg_ne (by decide))
    (hcount := by rw [hcount]; omega) (hcur := by rw [hcur]; exact Nat.le_add_right _ _)
    (hwb := hwb) (hbd := hbd)
    (hwbudget := hwbudget) (houterCoarse := houterCoarse)

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
  have hRB : R.top ≤ B := by
    have h1 : addr ≤ B := by omega
    omega
  have hreg : ∀ role : CNFEvalRole, R.reg role ≤ B := by
    intro role
    exact Nat.le_of_lt (R.reg_lt_of_top_le role hRB)
  exact programBoundedIn_decodeCNFEvalProgramAt_of_value_bounds B
    (R.reg .cursor) (R.reg .pol) (R.reg .var) (R.reg .done) (R.reg .outer) (R.reg .remaining)
    (R.reg .sat) (R.reg .bit) (R.reg .val) (R.reg .wBase) (R.reg .length) (R.reg .cnf)
    (R.reg .bound) σ
    (hidx := ⟨hreg .cursor, hreg .pol, hreg .var, hreg .done, hreg .outer, hreg .remaining,
      hreg .sat, hreg .bit, hreg .val, hreg .wBase, hreg .length, hreg .cnf, hreg .bound⟩)
    (hdist := ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide)⟩)
    (hcl := R.reg_ne (by decide)) (hld := R.reg_ne (by decide))
    (hrc := R.reg_ne (by decide)) (hcbit := R.reg_ne (by decide))
    (hcval := R.reg_ne (by decide)) (hcsat := R.reg_ne (by decide))
    (hbl := R.reg_ne (by decide)) (hbb := R.reg_ne (by decide))
    (hbval := R.reg_ne (by decide)) (hbs := R.reg_ne (by decide))
    (hbk := R.reg_ne (by decide)) (hck := R.reg_ne (by decide))
    (hrs := R.reg_ne (by decide)) (hsd := R.reg_ne (by decide))
    (hsl := R.reg_ne (by decide)) (hcw := R.reg_ne (by decide))
    (hpw := R.reg_ne (by decide)) (hvw := R.reg_ne (by decide))
    (hdw := R.reg_ne (by decide)) (hrw := R.reg_ne (by decide))
    (hbw := R.reg_ne (by decide)) (hvalw := R.reg_ne (by decide))
    (hsw := R.reg_ne (by decide)) (hlw := R.reg_ne (by decide))
    (hkw := R.reg_ne (by decide)) (hrv := R.reg_ne (by decide))
    (hco := R.reg_ne (by decide)) (hdo := R.reg_ne (by decide))
    (hoBnd := R.reg_ne (by decide)) (how := R.reg_ne (by decide))
    (hrp := R.reg_ne (by decide)) (hrd := R.reg_ne (by decide))
    (hrbit := R.reg_ne (by decide)) (hrval := R.reg_ne (by decide))
    (hwbudget := by rw [hwb, hbd]; exact hwbudget)
    (houterCoarse := by rw [hcur, hbd]; exact houterCoarse)

#check_stage_discipline all

end NPComplete.CookLevin

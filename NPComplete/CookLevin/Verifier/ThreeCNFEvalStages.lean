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
open NPComplete.BoundedWhile (RegLayout LayoutFact)

stage_default boundary

/-- The local resource facts of one ThreeCNF-evaluator store: the budget cells are bounded by
`B` (`ValuesLeOn`) and pinned to the entry store's `wBase`/`bound`/`cursor` values. -/
@[stage_impl] def decodeThreeCNFEvalResBounds (B cursorReg wBaseReg boundReg : ℕ) (σ : Store) :
    Store → Prop :=
  fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg
    ∧ τ boundReg = σ boundReg ∧ τ cursorReg = σ cursorReg

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
  have hstep : ProgramBoundedIn B σ
      (decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg) := by
    unfold decodeThreeClauseEvalStepAt
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    refine ⟨⟨hri, h3⟩, ⟨⟨hsi, Nat.zero_le B⟩, ?_⟩⟩
    set σ1 := (Program.assign satReg (.const 0)).eval
      ((Program.assign remainingReg (.const 3)).eval σ) with hσ1def
    have hσ1rem : σ1 remainingReg = 3 := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ satReg 0 remainingReg hsr.symm,
        eval_assign, Expr.eval, writeReg_same]
    have hσ1cur : σ1 cursorReg = σ cursorReg := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ satReg 0 cursorReg hsc.symm, eval_assign, Expr.eval,
        writeReg_diff _ remainingReg 3 cursorReg hrc.symm]
    have hσ1bnd : σ1 boundReg = σ boundReg := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ satReg 0 boundReg hsb.symm, eval_assign, Expr.eval,
        writeReg_diff _ remainingReg 3 boundReg hbr]
    have hσ1w : σ1 wBaseReg = σ wBaseReg := by
      rw [hσ1def, eval_assign, Expr.eval,
        writeReg_diff _ satReg 0 wBaseReg hsw.symm, eval_assign, Expr.eval,
        writeReg_diff _ remainingReg 3 wBaseReg hrw.symm]
    refine programBoundedIn_forN_of_invariant B 3 σ1 (Expr.const 3)
      (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg)
      (fun j τ => τ boundReg = σ boundReg ∧ τ wBaseReg = σ wBaseReg ∧
        τ remainingReg ≤ 3 ∧ τ cursorReg ≤ σ cursorReg + j * (σ boundReg + 1))
      h3 (by simp only [Expr.eval]; omega) (fun j _ => ?_) (fun j _ τ hI => ?_)
    · have hboundτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg
            remainingReg satReg bitReg valReg wBaseReg boundReg) j σ1) boundReg = σ boundReg :=
        (decodeClauseEvalStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg boundReg j σ1
          hbc hbp hbv hbd hbr hsb.symm hbb hbval).trans hσ1bnd
      have hwτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg) j σ1) wBaseReg = σ wBaseReg :=
        (decodeClauseEvalStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg boundReg j σ1
          hcw hpw hvw hdw hrw hbw hvalw hsw).trans hσ1w
      have hremτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg boundReg) j σ1) remainingReg ≤ 3 := by
        have h := decodeClauseEvalStepAt_loopEval_remaining_le cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg boundReg j σ1
          hrc hrp hrv hrd hrbit hrval hsr.symm
        rw [hσ1rem] at h
        exact h
      have hcurτ : (loopEval (decodeClauseEvalStepAt cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg boundReg) j σ1) cursorReg ≤
          σ cursorReg + j * (σ boundReg + 1) := by
        have hg := decodeClauseEvalStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
          satReg bitReg valReg wBaseReg boundReg j σ1
          hcp hcv hcd hrc hcbit hcval hsc.symm hbc hbp hbv hbd hbr hbb hbval hsb.symm
        rw [hσ1cur, hσ1bnd] at hg
        exact hg
      exact ⟨hboundτ, hwτ, hremτ, hcurτ⟩
    · obtain ⟨hbdτ, hwτ, hremτ, hcurτ⟩ := hI
      have hj3 : j ≤ 3 := by omega
      have hmb : j * (σ boundReg + 1) ≤ 3 * (σ boundReg + 1) :=
        Nat.mul_le_mul_right _ hj3
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
  change ProgramBoundedIn B σ
      ((decodeThreeClauseEvalStepAt cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg boundReg).seq (andIntoProg satReg cnfReg))
  simp only [ProgramBoundedIn]
  exact ⟨hstep, programBoundedIn_andIntoProg B satReg cnfReg _ hsi hki⟩

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
  have hC2 : ReadsOnly (fun a => a ≠ numVarsSkipReg)
      (fun ρ => (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg)
        ∧ ρ doneReg = 0) := by
    intro τ τ' he hτ
    exact ⟨⟨(he wBaseReg hnw.symm).trans hτ.1.1, (he boundReg hbl).trans hτ.1.2.1,
      (he cursorReg hcl).trans hτ.1.2.2⟩, (he doneReg hld.symm).trans hτ.2⟩
  have s2 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧ ρ cursorReg = σ cursorReg) ∧
        ρ doneReg = 0)
      (Program.assign numVarsSkipReg (.const 0)) {numVarsSkipReg}
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg ∧ ρ boundReg = σ boundReg ∧ ρ numVarsSkipReg = 0) :=
    (StageSpec.assign_const_carry (S := {wBaseReg, boundReg, cursorReg}) hnvi (by omega)
      hC2).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc⟩, hdone⟩ := hpins
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC3 : ReadsOnly (fun a => a ≠ cursorReg ∧ a ≠ numVarsSkipReg ∧ a ≠ doneReg)
      (fun ρ => ρ wBaseReg = σ wBaseReg) := by
    intro τ τ' he hτ
    exact (he wBaseReg ⟨hcw.symm, hnw.symm, hdw.symm⟩).trans hτ
  have hdS : doneReg ∉ ({wBaseReg, boundReg, cursorReg} : Set ℕ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hdw h
    · exact hbd.symm h
    · exact hcd.symm h
  have s3 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg ∧ ρ boundReg = σ boundReg ∧ ρ numVarsSkipReg = 0)
      (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg)
      (fun r => r = cursorReg ∨ r = numVarsSkipReg ∨ r = doneReg)
      (fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg ∧
        τ boundReg = σ boundReg ∧ τ cursorReg ≤ σ cursorReg + σ boundReg ∧
        τ numVarsSkipReg ≤ 0 + σ boundReg) :=
    StageSpec.decodeUnaryAt (cg := σ cursorReg) (k0 := 0) (lrv := σ boundReg)
      (c := cursorReg) (k := numVarsSkipReg) (d := doneReg) (lr := boundReg)
      (S := {wBaseReg, boundReg, cursorReg}) hcl hcd hld
      ⟨hbc, hbl, hbd⟩ ⟨hci, hnvi, hdi, hbi⟩ hC3 hdS (by omega) (by omega)
  have hC4 : ReadsOnly (fun a => a ≠ doneReg)
      (fun ρ => ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧
        ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ numVarsSkipReg ≤ 0 + σ boundReg) := by
    intro τ τ' he hτ
    exact ⟨(he wBaseReg hdw.symm).trans hτ.1, (he boundReg hbd).trans hτ.2.1,
      by have h1 := he cursorReg hcd; omega,
      by have h1 := he numVarsSkipReg hld; omega⟩
  have s4 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ boundReg = σ boundReg ∧ ρ cursorReg ≤ σ cursorReg + σ boundReg ∧
        ρ numVarsSkipReg ≤ 0 + σ boundReg)
      (Program.assign doneReg (.const 0)) {doneReg}
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧
          ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ numVarsSkipReg ≤ 0 + σ boundReg) ∧
        ρ doneReg = 0) :=
    StageSpec.assign_const_carry (S := {wBaseReg, boundReg, cursorReg}) hdi (by omega) hC4
  have hC5 : ReadsOnly (fun a => a ≠ outerReg)
      (fun ρ => (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧
          ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ numVarsSkipReg ≤ 0 + σ boundReg) ∧
        ρ doneReg = 0) := by
    intro τ τ' he hτ
    refine ⟨⟨(he wBaseReg how.symm).trans hτ.1.1, (he boundReg hbo).trans hτ.1.2.1,
      by have h1 := he cursorReg hco; omega,
      by have h1 := he numVarsSkipReg hno; omega⟩,
      (he doneReg hdo).trans hτ.2⟩
  have s5 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧
        (ρ wBaseReg = σ wBaseReg ∧ ρ boundReg = σ boundReg ∧
          ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ numVarsSkipReg ≤ 0 + σ boundReg) ∧
        ρ doneReg = 0)
      (Program.assign outerReg (.const 0)) {outerReg}
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ boundReg = σ boundReg ∧ ρ outerReg = 0) :=
    (StageSpec.assign_const_carry (S := {wBaseReg, boundReg, cursorReg}) hoi (by omega)
      hC5).weaken (fun _ => id) (fun r => id) (fun ρ hρ => by
      obtain ⟨hvals, hpins, hout⟩ := hρ
      obtain ⟨⟨hw, hb, hc, hn⟩, hdone⟩ := hpins
      exact ⟨hvals, hw, by omega, hb, hout⟩)
  have hC6 : ReadsOnly (fun a => a ≠ cursorReg ∧ a ≠ outerReg ∧ a ≠ doneReg)
      (fun ρ => ρ wBaseReg = σ wBaseReg) := by
    intro τ τ' he hτ
    exact (he wBaseReg ⟨hcw.symm, how.symm, hdw.symm⟩).trans hτ
  have s6 : StageSpec B
      (fun ρ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} ρ ∧ ρ wBaseReg = σ wBaseReg ∧
        ρ cursorReg ≤ σ cursorReg + σ boundReg ∧ ρ boundReg = σ boundReg ∧ ρ outerReg = 0)
      (decodeNatProgramAt cursorReg outerReg doneReg boundReg)
      (fun r => r = cursorReg ∨ r = outerReg ∨ r = doneReg)
      (fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg ∧
        τ boundReg = σ boundReg ∧ τ cursorReg ≤ (σ cursorReg + σ boundReg) + σ boundReg ∧
        τ outerReg ≤ 0 + σ boundReg) :=
    StageSpec.decodeUnaryAt (cg := σ cursorReg + σ boundReg) (k0 := 0) (lrv := σ boundReg)
      (c := cursorReg) (k := outerReg) (d := doneReg) (lr := boundReg)
      (S := {wBaseReg, boundReg, cursorReg}) hco hcd hdo.symm
      ⟨hbc, hbo, hbd⟩ ⟨hci, hoi, hdi, hbi⟩ hC6 hdS (by omega) (by omega)
  have s7 : StageSpec B
      (fun τ => ValuesLeOn B {wBaseReg, boundReg, cursorReg} τ ∧ τ wBaseReg = σ wBaseReg ∧
        τ boundReg = σ boundReg ∧ τ cursorReg ≤ (σ cursorReg + σ boundReg) + σ boundReg ∧
        τ outerReg ≤ 0 + σ boundReg)
      (Program.forN (.reg outerReg)
        (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg remainingReg satReg
          bitReg valReg wBaseReg cnfReg boundReg))
      (fun r => r = cursorReg ∨ r = polReg ∨ r = varReg ∨ r = doneReg ∨ r = remainingReg ∨
        r = satReg ∨ r = bitReg ∨ r = valReg ∨ r = cnfReg)
      (fun _ => True) := by
    refine StageSpec.forN_le (N := σ boundReg)
      (I := fun j τ => τ boundReg = σ boundReg ∧ τ wBaseReg = σ wBaseReg ∧
        τ cursorReg ≤ (σ cursorReg + σ boundReg) + σ boundReg +
          j * (3 * (σ boundReg + 1)))
      ?_ ?_ ?_ ?_ ?_
    · intro ρ _; show ExprBoundedIn B ρ (Expr.reg outerReg); exact hoi
    · intro ρ hρ; show (Expr.reg outerReg).eval ρ ≤ σ boundReg
      simp only [Expr.eval]; omega
    · intro ρ hρ j _
      obtain ⟨_, hwρ, hbdρ, hcurρ, _⟩ := hρ
      have hboundτ : (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) j ρ) boundReg =
          σ boundReg :=
        (decodeThreeCNFEvalClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg j ρ
          hbr hbs hbc hbp hbv hbd hbb hbval hbk).trans hbdρ
      have hwτ : (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) j ρ) wBaseReg =
          σ wBaseReg :=
        (decodeThreeCNFEvalClauseStepAt_loopEval_wBase_frame cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg j ρ
          hrw hsw hcw hpw hvw hdw hbw hvalw hkw).trans hwρ
      have hcurτ : (loopEval (decodeThreeCNFEvalClauseStepAt cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg) j ρ) cursorReg ≤
          (σ cursorReg + σ boundReg) + σ boundReg + j * (3 * (σ boundReg + 1)) := by
        have hg := decodeThreeCNFEvalClauseStepAt_cursor_le cursorReg polReg varReg doneReg
          remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg j ρ
          hcp hcv hcd hrc hcbit hcval hcsat hck hbc hbp hbv hbd hbr hbb hbval hbs hbk
        rw [hbdρ] at hg
        omega
      exact ⟨hboundτ, hwτ, hcurτ⟩
    · refine Program.Avoids.mono (P := fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧
          r ≠ doneReg ∧ r ≠ remainingReg ∧ r ≠ satReg ∧ r ≠ bitReg ∧ r ≠ valReg ∧ r ≠ cnfReg) ?_
        (fun r hr => ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr (Or.inl h)),
          fun h => hr (Or.inr (Or.inr (Or.inl h))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))),
          fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))⟩)
      exact decodeThreeCNFEvalClauseStepAt_avoids_frame cursorReg polReg varReg doneReg
        remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg
    · intro j _ τ hI
      obtain ⟨hbdτ, hwτ, hcurτ⟩ := hI
      have hjB : j ≤ σ boundReg := by omega
      have hmb : j * (3 * (σ boundReg + 1)) ≤ σ boundReg * (3 * (σ boundReg + 1)) :=
        Nat.mul_le_mul_right _ hjB
      exact programBoundedIn_decodeThreeCNFEvalClauseStepAt_of_value_bounds B cursorReg polReg
        varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg τ
        ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
        hrc hcbit hcval hbr hbb hbval hcw hpw hvw hdw hrw hbw hvalw hrv hrp hrd hrbit hrval
        ⟨hcsat.symm, hsd, hrs.symm, hbs.symm, hsw⟩ h3
        (by rw [hwτ, hbdτ]; exact hwbudget) (by rw [hbdτ]; omega)
  exact StageSpec.seq s1 (StageSpec.seq s2 (StageSpec.seq s3
    (StageSpec.seq s4 (StageSpec.seq s5 (StageSpec.seq s6 s7)))))

#check_stage_discipline all

end NPComplete.CookLevin

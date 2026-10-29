module

public import NPComplete.CookLevin.Verifier.ThreeCNFEvalOuterBounded
public import NPComplete.CookLevin.Verifier.ThreeCNFEvalTop
public import NPComplete.CookLevin.UniformPackaging.DecoderBounds

/-!
`ProgramBoundedIn` for the top-level `decodeThreeCNFEvalProgramAt`: decode the `numVars`
header, then the clause-count prefix, then bound the per-clause `.forN` loop via
`programBoundedIn_decodeThreeCNFEvalClauseStepAt_at_loop_of_outer_bounds`
(`ThreeCNFEvalOuterBounded.lean`) at every prefix count. Mirrors `CNFEvalTop.lean`'s
`programBoundedIn_decodeCNFEvalProgramAt_of_store_bounds`, with the extra `numVars`-skip stage
threaded through as a distinguished cost-free prefix (its own coarse budget only needs a `+
σ boundReg` cursor allowance, reused as the base store for the clause-count decode and fold).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ loopEval_succ_snoc eval_assignInd eval_skip)

/-- Running two sequential zero-assignments (`doneReg` then `xReg`) leaves `boundReg`,
    `cursorReg`, `wBaseReg` frame-preserved, sets `xReg`/`doneReg` to `0`, and preserves
    `StoreValuesLe B`. Factors the boilerplate shared by the `numVarsSkipReg`- and
    `outerReg`-indexed reset stages of `decodeThreeCNFEvalProgramAt`. -/
lemma two_assign_bounded_prelude
    (doneReg xReg boundReg wBaseReg cursorReg B : ℕ) (σ : Store) (hσ : StoreValuesLe B σ)
    (hxd : xReg ≠ doneReg) (hbd : boundReg ≠ doneReg) (hxb : xReg ≠ boundReg)
    (hdw : doneReg ≠ wBaseReg) (hxw : xReg ≠ wBaseReg)
    (hdc : doneReg ≠ cursorReg) (hxc : xReg ≠ cursorReg) :
    ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) boundReg = σ boundReg ∧
    ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) cursorReg = σ cursorReg ∧
    ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) wBaseReg = σ wBaseReg ∧
    ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) xReg = 0 ∧
    ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) doneReg = 0 ∧
    StoreValuesLe B ((Program.assign xReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) := by
  set σ0 := (Program.assign doneReg (.const 0)).eval σ with hσ0def
  have hσ0b : σ0 boundReg = σ boundReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 boundReg hbd
  have hσ0cur : σ0 cursorReg = σ cursorReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 cursorReg hdc.symm
  have hσ0w : σ0 wBaseReg = σ wBaseReg := by
    rw [hσ0def, eval_assign, Expr.eval]; exact writeReg_diff σ doneReg 0 wBaseReg hdw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eval_assign, Expr.eval, writeReg_diff σ0 xReg 0 boundReg hxb.symm, hσ0b]
  · rw [eval_assign, Expr.eval, writeReg_diff σ0 xReg 0 cursorReg hxc.symm, hσ0cur]
  · rw [eval_assign, Expr.eval, writeReg_diff σ0 xReg 0 wBaseReg hxw.symm, hσ0w]
  · rw [eval_assign, Expr.eval, writeReg_same]
  · rw [eval_assign, Expr.eval, writeReg_diff σ0 xReg 0 doneReg hxd.symm]
    rw [hσ0def, eval_assign, Expr.eval, writeReg_same]
  · apply storeValuesLe_assign
    · apply storeValuesLe_assign hσ; simp only [Expr.eval]; omega
    · simp only [Expr.eval]; omega

/-- Bounded correctness and store transition of the `numVars`-skip stage: seeding
    `doneReg`/`numVarsSkipReg` and running `decodeNatProgramAt` (over `numVarsSkipReg`) is
    `ProgramBoundedIn`, and its result store `σ1'` is `StoreValuesLe`-bounded with
    `boundReg`/`wBaseReg` frame-preserved and `cursorReg` growing by at most `σ boundReg`. -/
lemma num_vars_stage_bounded
    (cursorReg doneReg wBaseReg boundReg numVarsSkipReg B : ℕ) (σ : Store)
    (hσ : StoreValuesLe B σ) (hB1 : 1 ≤ B)
    (hnc : numVarsSkipReg ≠ cursorReg) (hcd : cursorReg ≠ doneReg) (hnd : numVarsSkipReg ≠ doneReg)
    (hbd : boundReg ≠ doneReg) (hnBnd : numVarsSkipReg ≠ boundReg) (hbc : boundReg ≠ cursorReg)
    (hcw : cursorReg ≠ wBaseReg) (hnw : numVarsSkipReg ≠ wBaseReg) (hdw : doneReg ≠ wBaseReg)
    (hidx : cursorReg ≤ B ∧ numVarsSkipReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B)
    (hcur0 : σ cursorReg + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (Program.seq (.assign doneReg (.const 0))
        (Program.seq (.assign numVarsSkipReg (.const 0))
          (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg))) ∧
    ∃ σ1' : Store,
      (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg).eval
        ((Program.assign numVarsSkipReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ)) = σ1' ∧
      StoreValuesLe B σ1' ∧ σ1' boundReg = σ boundReg ∧ σ1' wBaseReg = σ wBaseReg ∧
      σ1' cursorReg ≤ σ cursorReg + σ boundReg := by
  obtain ⟨hci, hni, hdi, hbi⟩ := hidx
  obtain ⟨hb1, hcur1, hw1, hx1, hd1, hLe1⟩ :=
    two_assign_bounded_prelude doneReg numVarsSkipReg boundReg wBaseReg cursorReg B σ hσ
      hnd hbd hnBnd hdw hnw hcd.symm hnc
  have hprefix : ProgramBoundedIn B
      ((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ))
      (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg) := by
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg numVarsSkipReg doneReg boundReg
      B _ hnc.symm hcd (fun h => hnd h) ⟨hci, hni, hdi, hbi⟩
    · rw [hcur1, hb1]; exact hcur0
    · rw [hx1, hb1]; omega
  have hStore : StoreValuesLe B
      ((decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg).eval
        ((Program.assign numVarsSkipReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ))) :=
    program_eval_storeValuesLe _ _ hB1 hLe1 hprefix
      (scanFree_decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg)
  have hbF := decodeNatProgramAt_bound_frame cursorReg numVarsSkipReg doneReg boundReg
    ((Program.assign numVarsSkipReg (.const 0)).eval
      ((Program.assign doneReg (.const 0)).eval σ)) hbc hnBnd.symm hbd
  have hwF := decodeNatProgramAt_frame cursorReg numVarsSkipReg doneReg boundReg wBaseReg
    ((Program.assign numVarsSkipReg (.const 0)).eval
      ((Program.assign doneReg (.const 0)).eval σ)) hcw.symm hnw.symm hdw.symm
  have hcurLe : (decodeNatProgramAt cursorReg numVarsSkipReg doneReg boundReg).eval
      ((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) cursorReg ≤
      ((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) cursorReg +
      ((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) boundReg := by
    unfold decodeNatProgramAt decodeUnaryProgAt
    rw [eval_forN]
    simp only [Expr.eval]
    exact loopEval_decodeUnaryStep_cursor_le cursorReg numVarsSkipReg doneReg hnc.symm hcd
      (((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ)) boundReg)
      ((Program.assign numVarsSkipReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ))
  refine ⟨?_, _, rfl, hStore, ?_, ?_, ?_⟩
  · simp only [ProgramBoundedIn, ExprBoundedIn]
    exact ⟨⟨hdi, Nat.zero_le B⟩, ⟨hni, Nat.zero_le B⟩, hprefix⟩
  · rw [hbF, hb1]
  · rw [hwF, hw1]
  · rw [hcur1, hb1] at hcurLe; exact hcurLe

/-- Bounded correctness and store transition of the clause-count-decode stage: seeding
    `doneReg`/`outerReg` and running `decodeNatProgramAt` (over `outerReg`) at the
    post-`numVars`-stage store `σ1'` is `ProgramBoundedIn`, and its result store `σ4` is
    `StoreValuesLe`-bounded with `boundReg`/`wBaseReg` frame-preserved and `cursorReg` growing
    by at most `σ1' boundReg`. -/
lemma clause_count_stage_bounded
    (cursorReg doneReg wBaseReg boundReg outerReg B : ℕ) (σ1' : Store)
    (hσ1'Le : StoreValuesLe B σ1') (hB1 : 1 ≤ B)
    (hco : cursorReg ≠ outerReg) (hcd : cursorReg ≠ doneReg) (hdo : doneReg ≠ outerReg)
    (hbd : boundReg ≠ doneReg) (hoBnd : outerReg ≠ boundReg) (hbc : boundReg ≠ cursorReg)
    (hcw : cursorReg ≠ wBaseReg) (how : outerReg ≠ wBaseReg) (hdw : doneReg ≠ wBaseReg)
    (hidx : cursorReg ≤ B ∧ outerReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B)
    (hcur0 : σ1' cursorReg + σ1' boundReg ≤ B) :
    ProgramBoundedIn B
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1'))
      (decodeNatProgramAt cursorReg outerReg doneReg boundReg) ∧
    ∃ σ4 : Store,
      (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval
        ((Program.assign outerReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ1')) = σ4 ∧
      StoreValuesLe B σ4 ∧ σ4 boundReg = σ1' boundReg ∧ σ4 wBaseReg = σ1' wBaseReg ∧
      σ4 cursorReg ≤ σ1' cursorReg + σ1' boundReg := by
  obtain ⟨hci, hoi, hdi, hbi⟩ := hidx
  obtain ⟨hb2, hcur2, hw2, ho2, hd2, hLe2⟩ :=
    two_assign_bounded_prelude doneReg outerReg boundReg wBaseReg cursorReg B σ1' hσ1'Le
      hdo.symm hbd hoBnd hdw how hcd.symm hco.symm
  have hprefix : ProgramBoundedIn B
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1'))
      (decodeNatProgramAt cursorReg outerReg doneReg boundReg) := by
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg outerReg doneReg boundReg
      B _ hco hcd (fun h => hdo h.symm) ⟨hci, hoi, hdi, hbi⟩
    · rw [hcur2, hb2]; exact hcur0
    · rw [ho2, hb2]; omega
  have hStore : StoreValuesLe B
      ((decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval
        ((Program.assign outerReg (.const 0)).eval
          ((Program.assign doneReg (.const 0)).eval σ1'))) :=
    program_eval_storeValuesLe _ _ hB1 hLe2 hprefix
      (scanFree_decodeNatProgramAt cursorReg outerReg doneReg boundReg)
  have hbF := decodeNatProgramAt_bound_frame cursorReg outerReg doneReg boundReg
    ((Program.assign outerReg (.const 0)).eval
      ((Program.assign doneReg (.const 0)).eval σ1')) hbc hoBnd.symm hbd
  have hwF := decodeNatProgramAt_frame cursorReg outerReg doneReg boundReg wBaseReg
    ((Program.assign outerReg (.const 0)).eval
      ((Program.assign doneReg (.const 0)).eval σ1')) hcw.symm how.symm hdw.symm
  have hcurLe : (decodeNatProgramAt cursorReg outerReg doneReg boundReg).eval
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) cursorReg ≤
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) cursorReg +
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) boundReg := by
    unfold decodeNatProgramAt decodeUnaryProgAt
    rw [eval_forN]
    simp only [Expr.eval]
    exact loopEval_decodeUnaryStep_cursor_le cursorReg outerReg doneReg hco hcd
      (((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) boundReg)
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1'))
  refine ⟨hprefix, _, rfl, hStore, ?_, ?_, ?_⟩
  · rw [hbF, hb2]
  · rw [hwF, hw2]
  · rw [hcur2, hb2] at hcurLe; exact hcurLe

/-- `ProgramBoundedIn` for `decodeThreeCNFEvalProgramAt`: decode the `numVars` header
    (`σ1'`, the post-header store), then the clause-count prefix, then bound the per-clause
    `.forN` loop. `houterCoarse` is stated at `σ` scale (`num_vars_stage_bounded`/
    `clause_count_stage_bounded` transport it to `σ1'`, the store
    `programBoundedIn_decodeThreeCNFEvalClauseStepAt_at_loop_of_outer_bounds` expects), matching
    that lemma's own budget shape via the header's `+ σ boundReg` cursor growth. -/
lemma programBoundedIn_decodeThreeCNFEvalProgramAt_of_store_bounds
    (B cursorReg polReg varReg doneReg outerReg remainingReg satReg bitReg valReg wBaseReg
      cnfReg boundReg numVarsSkipReg : ℕ) (σ : Store) (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ outerReg ≤ B ∧
      remainingReg ≤ B ∧ satReg ≤ B ∧ bitReg ≤ B ∧ valReg ≤ B ∧ wBaseReg ≤ B ∧
      cnfReg ≤ B ∧ boundReg ≤ B ∧ numVarsSkipReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hrc : remainingReg ≠ cursorReg) (hcbit : cursorReg ≠ bitReg) (hcval : cursorReg ≠ valReg)
    (hcsat : cursorReg ≠ satReg) (hbb : boundReg ≠ bitReg)
    (hbval : boundReg ≠ valReg) (hbs : boundReg ≠ satReg) (hbk : boundReg ≠ cnfReg)
    (hck : cursorReg ≠ cnfReg) (hrs : remainingReg ≠ satReg) (hsd : satReg ≠ doneReg)
    (hcw : cursorReg ≠ wBaseReg) (hpw : polReg ≠ wBaseReg) (hvw : varReg ≠ wBaseReg)
    (hdw : doneReg ≠ wBaseReg) (hrw : remainingReg ≠ wBaseReg) (hbw : bitReg ≠ wBaseReg)
    (hvalw : valReg ≠ wBaseReg) (hsw : satReg ≠ wBaseReg)
    (hkw : cnfReg ≠ wBaseReg) (hrv : remainingReg ≠ varReg)
    (hco : cursorReg ≠ outerReg) (hdo : doneReg ≠ outerReg) (hoBnd : outerReg ≠ boundReg)
    (how : outerReg ≠ wBaseReg)
    (hnc : numVarsSkipReg ≠ cursorReg) (hnd : numVarsSkipReg ≠ doneReg)
    (hnBnd : numVarsSkipReg ≠ boundReg) (hnw : numVarsSkipReg ≠ wBaseReg)
    (hB1 : 1 ≤ B)
    (hwbudget : σ wBaseReg + σ boundReg ≤ B)
    (houterCoarse : σ cursorReg + σ boundReg + σ boundReg + σ boundReg * (3 * (σ boundReg + 1)) +
        3 * (σ boundReg + 1) + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeThreeCNFEvalProgramAt cursorReg polReg varReg doneReg outerReg remainingReg satReg
        bitReg valReg wBaseReg cnfReg boundReg numVarsSkipReg) := by
  rcases hidx with ⟨hci, hpi, hvi, hdi, hoi, hri, hsi, hbiti, hvali, hwi, hki, hbi, hni⟩
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
  obtain ⟨hstage1, σ1', hσ1'def, hσ1'Le, hσ1'b, hσ1'w, hσ1'cur⟩ :=
    num_vars_stage_bounded cursorReg doneReg wBaseReg boundReg numVarsSkipReg B σ hσ hB1
      hnc hcd hnd hbd hnBnd hbc hcw hnw hdw ⟨hci, hni, hdi, hbi⟩ (by omega)
  obtain ⟨hstage2, σ4, hσ4def, hσ4Le, hσ4b, hσ4w, hσ4cur⟩ :=
    clause_count_stage_bounded cursorReg doneReg wBaseReg boundReg outerReg B σ1' hσ1'Le hB1
      hco hcd hdo hbd hoBnd hbc hcw how hdw ⟨hci, hoi, hdi, hbi⟩ (by rw [hσ1'b]; omega)
  have houterCoarse' : σ1' cursorReg + σ1' boundReg + σ1' boundReg *
      (3 * (σ1' boundReg + 1)) + 3 * (σ1' boundReg + 1) + 1 + σ1' boundReg ≤ B := by
    rw [hσ1'b]; omega
  unfold decodeThreeCNFEvalProgramAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hstage1.1, hstage1.2.1, hstage1.2.2, ⟨hdi, Nat.zero_le B⟩,
    ⟨hoi, Nat.zero_le B⟩, ?_, hoi, ?_⟩
  · rw [hσ1'def]; exact hstage2
  · rw [hσ1'def, hσ4def]
    intro m hm
    simp only [Expr.eval] at hm
    have hcount := decodeNatProgramAt_count_le cursorReg outerReg doneReg boundReg
      ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) hco hdo.symm
    have ho1' : ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) outerReg = 0 := by
      simp [eval_assign, Expr.eval, writeReg_same]
    have hbEq : ((Program.assign outerReg (.const 0)).eval
        ((Program.assign doneReg (.const 0)).eval σ1')) boundReg = σ1' boundReg := by
      simp [eval_assign, Expr.eval, writeReg_diff _ outerReg _ boundReg hoBnd.symm,
        writeReg_diff _ doneReg _ boundReg hbd]
    rw [ho1', hbEq, hσ4def] at hcount
    have hmle : m ≤ σ1' boundReg := by omega
    have hwbudget' : σ1' wBaseReg + σ1' boundReg ≤ B := by rw [hσ1'w, hσ1'b]; exact hwbudget
    exact programBoundedIn_decodeThreeCNFEvalClauseStepAt_at_loop_of_outer_bounds B cursorReg
      polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg cnfReg boundReg m σ1' σ4
      ⟨hci, hpi, hvi, hdi, hri, hsi, hbiti, hvali, hwi, hki, hbi⟩
      ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd, hbr⟩
      hrc hcbit hcval hcsat hbb hbval hbs hbk hck hrs hsd hcw hpw hvw hdw hrw hbw hvalw hsw hkw
      hrv hB1 hwbudget' houterCoarse' hσ4Le hσ4b hσ4w hσ4cur hmle

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAcceptFamily
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAtLeastOne
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedInitFamily
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedLoad
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedPersist
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedSetup
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedStage
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedTop
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedTransFamily
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedUniqFamily

/-!
Each `ProgramBoundedIn` bound of the generator is stated over a long list of hypotheses, so a
contradictory hypothesis set would make it hold for no reason. These checks instantiate the bounds
at concrete values, with every hypothesis discharged, to show that the premises are satisfiable and
that the conclusions yield genuine facts. They also hold the content witnesses and the proof that
the table writer's entry premises are contradictory at the post-setup store. No main construction
uses them, so they stay outside the consumer-facing umbrella.
-/

@[expose] public section

namespace NPComplete.CookLevin

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Verification: non-vacuity and content extraction -/

/-- Non-vacuity witness: `clauseWriterBounded_acceptFamilyProgParam`'s
hypotheses hold simultaneously at concrete values with `T ≥ 1`, `W ≥ 1`, a
non-empty `outIdx`, and a non-empty halt-state list — the loops here
actually run and the halt row actually has width, unlike a degenerate
`W = 0`/`d.table = []` witness. -/
example :
    ∃ (M Jmax K S B n W m T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
      (wReg tReg obReg : ℕ),
      AcceptParamPlacement Jmax wReg tReg obReg ∧ 24 ≤ Jmax ∧
      M + obReg + 1 < outBase ∧ outBase + outIdx.length ≤ M + Jmax ∧
      1 ≤ K ∧ wReg ≤ 23 ∧ tReg ≤ 23 ∧ obReg ≤ 23 ∧
      M + 24 ≤ B ∧ K + 1 ≤ B ∧ K ≤ S ∧ S ≤ B ∧ W ≤ K ∧
      AcceptEnv K B n m ∧ AcceptEnv K S n m ∧ n ≤ B ∧ m ≤ B ∧
      d.blankIdx ≤ K ∧ (∀ v ∈ outIdx, v ≤ K) ∧ outIdx.length ≤ B ∧
      (∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0), v ≤ K) ∧
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ K ∧
      1 ≤ W ∧ 1 ≤ T ∧ outIdx ≠ [] ∧
      descHaltStates d (natInitSymbol d.blankIdx outIdx 0) ≠ [] := by
  refine ⟨0, 24, 2, 30, 30, 0, 2, 1, 1, 20,
    (⟨2, 0, 1, 0, 0, 0, [NatTrans.halt]⟩ : TableauDescriptor), [0], 15, 16, 17,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold ctlJmax; norm_num)
    | (unfold AcceptEnv; norm_num)
    | (intro v hv; simp at hv; omega)
    | decide

/-- Content-extraction witness: at concrete `M`, `wp`, and a store satisfying
all hypotheses (`W = 1`, `T = 1`, `outIdx = [0]`, a single halt state),
`clauseWriterBounded_acceptFamilyProgParam` actually yields a
`ProgramBoundedIn` fact for a run where both window loops iterate once and
the halt row is non-empty. -/
example : ProgramBoundedIn 1000
    (fun r => if r = 1 then (27 : ℕ) else if r = 15 then 1 else if r = 16 then 1
      else if r = 17 then 21 else if r = 20 then 1 else 0)
    (acceptFamilyProgParam 0 1 (⟨2, 0, 1, 0, 0, 0, [NatTrans.halt]⟩ : TableauDescriptor) [0]
      15 16 17) := by
  have hplace : AcceptParamPlacement 26 15 16 17 :=
    ⟨by unfold ctlJmax; norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hfam := clauseWriterBounded_acceptFamilyProgParam 0 26 21 1000 1000 0 1 1 1 21
    (⟨2, 0, 1, 0, 0, 0, [NatTrans.halt]⟩ : TableauDescriptor) [0] 15 16 17 hplace (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold AcceptEnv; norm_num) (by unfold AcceptEnv; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by intro v hv; simp at hv; omega) (by norm_num)
    (by unfold descHaltStates; decide) (by unfold descHaltStates; decide)
  refine (hfam _ 27 ?_ (by norm_num) (by simp only [wpJ]; norm_num) (by norm_num) (by decide)
    ?_ ?_).1
  · unfold AcceptParamFrozen PinsAndWord PinsHold WordAt acceptParamPins0
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> norm_num
    · norm_num
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      norm_num
  · intro i; simp only; split_ifs <;> omega
  · intro j hj2 hj24; simp only; split_ifs <;> omega

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Non-vacuity witness: `programBoundedIn_writeAtLeastOneProg`'s hypotheses are
    simultaneously satisfiable at a concrete instance, ruling out the lemma
    proving `False → …`. -/
example : ProgramBoundedIn 30 (fun r => if r = 1 then (25 : ℕ) else 0)
    (writeAtLeastOneProg wpJ 2 (Expr.const 1) (Expr.const 0)) := by
  apply programBoundedIn_writeAtLeastOneProg 5 29 30 0 25 2 1
  · rfl
  · rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp [ExprBoundedIn]
  · rfl
  · simp [ExprBoundedIn]
  · rfl
  · intro τ _ _ _
    exact ⟨by simp [ExprBoundedIn], by simp [Expr.eval]⟩
  · intro j hj hj24
    simp only
    split <;> omega
  · intro i
    simp only
    split <;> omega

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Verification: non-vacuity and content extraction -/

/-- Non-vacuity witness: `clauseWriterBounded_initFamilyProgParam`'s
hypotheses hold simultaneously at concrete values.  `allowedIdx = [0]` makes
the window's widest branch (`atLeastOne`) width `6`, matching the leaf
bound `2 + 2 * (allowedIdx.length + 1) = 6`. -/
example :
    ∃ (M Jmax K S B n W m _T wReg tReg fReg plReg pbReg : ℕ) (d : TableauDescriptor)
      (allowedIdx prefIdx : List ℕ) (prefLen freeLen prefBase : ℕ),
      InitParamPlacement Jmax wReg tReg fReg plReg pbReg ∧ 24 ≤ Jmax ∧
      prefLen = prefIdx.length ∧
      wReg ≤ 23 ∧ tReg ≤ 23 ∧ fReg ≤ 23 ∧ plReg ≤ 23 ∧ pbReg ≤ 23 ∧
      M + pbReg + 1 < prefBase ∧ prefBase + prefIdx.length ≤ M + Jmax ∧
      InitEnv K B n m ∧ InitEnv K S n m ∧ n ≤ B ∧ m ≤ B ∧
      M + 24 ≤ B ∧ S ≤ B ∧ K + 1 ≤ B ∧ K ≤ S ∧ 2 ≤ S ∧
      d.blankIdx ≤ K ∧ (∀ v ∈ allowedIdx, v ≤ K) ∧
      allowedIdx.length + 1 ≤ K ∧ (∀ v ∈ prefIdx, v ≤ K) ∧
      W ≤ K ∧ freeLen ≤ K ∧ d.startState ≤ K := by
  refine ⟨(0:ℕ), (24:ℕ), (2:ℕ), (30:ℕ), (30:ℕ), (0:ℕ), (1:ℕ), (0:ℕ), (0:ℕ), (15:ℕ), (16:ℕ),
    (17:ℕ), (18:ℕ), (19:ℕ), (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor),
    ([0] : List ℕ), ([0] : List ℕ), (1:ℕ), (1:ℕ), (21:ℕ), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold ctlJmax; norm_num)
    | (unfold InitEnv; norm_num)
    | (intro v hv; simp at hv; omega)
    | norm_num

/-- Content-extraction witness: at concrete `M`, `wp`, and a store satisfying
all hypotheses, `clauseWriterBounded_initFamilyProgParam` actually yields a
`ProgramBoundedIn` fact — not merely a proof from vacuous premises. -/
example : ProgramBoundedIn 300
    (fun r => if r = 1 then (25 : ℕ) else if r = 15 then 1 else if r = 16 then 0
      else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
      else if r = 20 then 1 else if r = 21 then 0 else 0)
    (initFamilyProgParam 0 1 (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0]
      15 16 17 18 19) := by
  have hplace : InitParamPlacement 24 15 16 17 18 19 :=
    ⟨by unfold ctlJmax; norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩
  have hfam := clauseWriterBounded_initFamilyProgParam 0 24 25 300 300 0 1 1 0 15 16 17 18 19
    (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0] [0] 1 1 21 hplace (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold InitEnv; norm_num) (by unfold InitEnv; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by intro v hv; simp at hv; omega) (by norm_num)
    (by intro v hv; simp at hv; omega) (by norm_num) (by norm_num) (by norm_num)
  refine (hfam _ 25 ?_ (by norm_num) (by simp only [wpJ]; norm_num) (by norm_num) (by norm_num)
    ?_ ?_).1
  · unfold InitParamFrozen PinsAndWord PinsHold WordAt initParamPins0
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    · norm_num
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      norm_num
  · intro i; simp only; split_ifs <;> omega
  · intro j hj2 hj24; simp only; split_ifs <;> omega

end

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## Non-vacuity

`loadWordsProg`'s `ProgramBoundedIn`, at concrete `p = time = 0`, `d = loadConstTestDescriptor`
(a genuinely non-constant table), `allowedIdx = []`, `outIdx = [5, 7, 9]`, and mixed-bit input
`[true, false, true]` (`N = 3`, so the loop actually runs and both `ifNZ` branches fire), with
`B := envB.eval 3` — every hypothesis discharged, not assumed. -/
example :
    ProgramBoundedIn
      (Polynomial.eval 3 (envB 0 0 loadConstTestDescriptor
        (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]))
      (bitInputStore [true, false, true])
      (loadWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9]) := by
  show ProgramBoundedIn
    (Polynomial.eval ([true, false, true] : List Bool).length
      (envB 0 0 loadConstTestDescriptor
        (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]))
    (bitInputStore [true, false, true])
    (loadWordsProg 0 0 loadConstTestDescriptor [] [5, 7, 9])
  apply programBoundedIn_loadWordsProg_envB
  · exact envK_ge_trueIdx 0 0 loadConstTestDescriptor true [false, true] [] [5, 7, 9] 3
  · exact envK_ge_falseIdx 0 0 loadConstTestDescriptor [true, false, true] [] [5, 7, 9] 3
  · intro k hk
    rw [envK_eval]
    have hmem : (loadConstTestDescriptor.table.map transKind).getD k 0 ∈
        loadConstTestDescriptor.table.map transKind := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_kind (d := loadConstTestDescriptor)
      (prefIdx := prefixWord loadConstTestDescriptor [true, false, true])
      (allowedIdx := ([] : List ℕ)) (outIdx := [5, 7, 9]) hmem
    have h2 := envIdxMax_le_envKConst loadConstTestDescriptor
      (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]
    omega
  · intro k hk
    rw [envK_eval]
    have hmem : (loadConstTestDescriptor.table.map transArg1).getD k 0 ∈
        loadConstTestDescriptor.table.map transArg1 := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_arg1 (d := loadConstTestDescriptor)
      (prefIdx := prefixWord loadConstTestDescriptor [true, false, true])
      (allowedIdx := ([] : List ℕ)) (outIdx := [5, 7, 9]) hmem
    have h2 := envIdxMax_le_envKConst loadConstTestDescriptor
      (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]
    omega
  · intro k hk
    rw [envK_eval]
    have hmem : (loadConstTestDescriptor.table.map transArg2).getD k 0 ∈
        loadConstTestDescriptor.table.map transArg2 := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_arg2 (d := loadConstTestDescriptor)
      (prefIdx := prefixWord loadConstTestDescriptor [true, false, true])
      (allowedIdx := ([] : List ℕ)) (outIdx := [5, 7, 9]) hmem
    have h2 := envIdxMax_le_envKConst loadConstTestDescriptor
      (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]
    omega
  · intro k hk
    rw [envK_eval]
    have hmem : ([5, 7, 9] : List ℕ).getD k 0 ∈ ([5, 7, 9] : List ℕ) := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_out (d := loadConstTestDescriptor)
      (prefIdx := prefixWord loadConstTestDescriptor [true, false, true])
      (allowedIdx := ([] : List ℕ)) (outIdx := [5, 7, 9]) hmem
    have h2 := envIdxMax_le_envKConst loadConstTestDescriptor
      (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]
    omega

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Non-vacuity witness for `clauseWriterBounded_persistFamilyProgParam`: all of its
hypotheses hold simultaneously at concrete values, so the contract is not
vacuous. -/
example :
    ∃ (K S B M Jmax n m mC W T wReg tReg : ℕ),
      PersistParamPlacement Jmax wReg tReg ∧ 24 ≤ Jmax ∧
      1 ≤ K ∧ 2 ≤ wReg ∧ wReg ≤ 23 ∧ tReg ≤ 23 ∧ M + 24 ≤ B ∧
      PersistEnv K B n m ∧ PersistEnv K S n m ∧ n ≤ B ∧ m ≤ B ∧
      S ≤ B ∧ K + 1 ≤ B ∧ K ≤ S ∧ mC ≤ K ∧
      3 ≤ S ∧ W ≤ K ∧ W ≤ B ∧ T + 1 ≤ K := by
  refine ⟨2, 24, 24, 0, 24, 0, 0, 1, 1, 1, 15, 16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num [ctlJmax], by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · unfold PersistEnv; norm_num
  · unfold PersistEnv; norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Non-vacuity

Each of the four `ProgramBoundedIn` lemmas above discharges its hypotheses at
one concrete instance — `p = time = X`, `N = 3`, `d = initCheckDesc`,
`outIdx = []` — to confirm none of the arithmetic obligations collapsed into
something unsatisfiable, and that the envelope built out of `V = q.eval (N+1)`
(kept apart from `B`) is exercised rather than trivialized. -/

example (σ : Store) (hσ0 : σ 0 = 3) :
    ProgramBoundedIn 21582843385 σ
      (setupProg Polynomial.X Polynomial.X initCheckDesc ([] : List ℕ)) := by
  apply programBoundedIn_setupProg 21582843385 3 Polynomial.X Polynomial.X initCheckDesc []
    σ hσ0
  · simp
  · simp
  · simp
  · simp [setupSpan]
  · rw [cookWindowPoly_eval]; simp
  · rw [cookWindowPoly_eval]; simp
  · rw [cookWindowPoly_eval]; simp
  · rw [NPComplete.CookLevin.timePoly_eval]; simp
  · rw [NPComplete.CookLevin.timePoly_eval]; simp
  · rw [NPComplete.CookLevin.timePoly_eval]; simp
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · omega
  · simp only [setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]

example (σ : Store) (hσ0 : σ 0 = 3) :
    ProgramBoundedIn 21582843385 σ
      (generatorLayoutProg Polynomial.X Polynomial.X initCheckDesc [] ([] : List ℕ)) := by
  apply programBoundedIn_generatorLayoutProg 21582843385 3 Polynomial.X Polynomial.X
    initCheckDesc [] [] σ hσ0
  · simp
  · simp
  · simp
  · simp [setupSpan]
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [setupM, setupSpan, generatorPrefOffset, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · omega
  · simp only [generatorPrefBase, generatorPrefOffset, generatorPrefLen, setupM, setupSpan,
      initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [generatorKindBase, generatorKindOffset, generatorPrefOffset,
      generatorPrefLen, setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [generatorArg1Base, generatorArg1Offset, generatorKindOffset,
      generatorPrefOffset, generatorPrefLen, setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [generatorArg2Base, generatorArg2Offset, generatorArg1Offset,
      generatorKindOffset, generatorPrefOffset,
      generatorPrefLen, setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  · simp only [generatorOutBase, generatorOutOffset, generatorArg2Offset,
      generatorArg1Offset, generatorKindOffset,
      generatorPrefOffset, generatorPrefLen, setupM, setupSpan, initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]

example (σ : Store) (hσ0 : σ 0 = 3) :
    ProgramBoundedIn 21582843385 σ
      (generatorSetupProg Polynomial.X Polynomial.X initCheckDesc [] ([] : List ℕ)) := by
  apply programBoundedIn_generatorSetupProg 21582843385 3 Polynomial.X Polynomial.X
    initCheckDesc [] [] σ hσ0
  · apply programBoundedIn_setupProg 21582843385 3 Polynomial.X Polynomial.X initCheckDesc []
      σ hσ0
    · simp
    · simp
    · simp
    · simp [setupSpan]
    · rw [cookWindowPoly_eval]; simp
    · rw [cookWindowPoly_eval]; simp
    · rw [cookWindowPoly_eval]; simp
    · rw [NPComplete.CookLevin.timePoly_eval]; simp
    · rw [NPComplete.CookLevin.timePoly_eval]; simp
    · rw [NPComplete.CookLevin.timePoly_eval]; simp
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · omega
    · simp only [setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
  · intro τ hτ
    apply programBoundedIn_generatorLayoutProg 21582843385 3 Polynomial.X Polynomial.X
      initCheckDesc [] [] τ hτ
    · simp
    · simp
    · simp
    · simp [setupSpan]
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [setupM, setupSpan, generatorPrefOffset, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · omega
    · simp only [generatorPrefBase, generatorPrefOffset, generatorPrefLen, setupM, setupSpan,
        initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [generatorKindBase, generatorKindOffset, generatorPrefOffset,
        generatorPrefLen, setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [generatorArg1Base, generatorArg1Offset, generatorKindOffset,
        generatorPrefOffset, generatorPrefLen, setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [generatorArg2Base, generatorArg2Offset, generatorArg1Offset,
        generatorKindOffset, generatorPrefOffset,
        generatorPrefLen, setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]
    · simp only [generatorOutBase, generatorOutOffset, generatorArg2Offset,
        generatorArg1Offset, generatorKindOffset,
        generatorPrefOffset, generatorPrefLen, setupM, setupSpan, initCheckDesc]
      unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
      simp [cookWindowPoly_eval, timePoly_eval]

example (σ : Store) (hσ0 : σ 0 = 3) :
    ProgramBoundedIn 21582843385 σ
      (Program.assign 0 (setupME Polynomial.X Polynomial.X initCheckDesc [])) := by
  apply programBoundedIn_setupME_assign
  refine exprBoundedIn_setupME 21582843385 3 Polynomial.X Polynomial.X initCheckDesc [] σ
    (exprBoundedIn_setupSpanE 21582843385 3 Polynomial.X σ hσ0 (by simp) (by simp) (by simp)
      (by simp [setupSpan]))
    (setupSpanE_eval Polynomial.X σ 3 hσ0) hσ0 ?_ ?_ ?_
    ?_
  all_goals
    first
    | (simp only [initCheckDesc]
       unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
       simp [cookWindowPoly_eval, timePoly_eval])
    | (simp only [setupM, setupSpan, initCheckDesc]
       unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
       simp [cookWindowPoly_eval, timePoly_eval])

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Verification: non-vacuity and content extraction -/

/-- Non-vacuity witness: `clauseWriterBounded_tableWriterProgParam`'s
hypotheses hold simultaneously at concrete values (`M = 0`, `K = 32`,
`S = B = 100000`, a one-state one-letter descriptor with an empty
transition table, `W = T = freeLen = 1`). -/
example :
    ∃ (M Jmax K S B W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
      (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ),
      GeneratorPlacement M Jmax prefLen prefBase kindBase arg1Base
        arg2Base outBase d prefIdx outIdx ∧
      24 ≤ Jmax ∧ 1 ≤ K ∧ M + 24 ≤ B ∧ K + 1 ≤ B ∧ K ≤ S ∧
      S ≤ B ∧ 2 ≤ S ∧ 3 ≤ S ∧ 4 ≤ S ∧
      UniqEnv K B (d.numStates + 1) (d.numLetters + 1) ∧
      UniqEnv K S (d.numStates + 1) (d.numLetters + 1) ∧
      InitEnv K B (d.numStates + 1) (d.numLetters + 1) ∧
      InitEnv K S (d.numStates + 1) (d.numLetters + 1) ∧
      TransEnv K B (d.numStates + 1) (d.numLetters + 1) ∧
      TransEnv K S (d.numStates + 1) (d.numLetters + 1) ∧
      PersistEnv K B (d.numStates + 1) (d.numLetters + 1) ∧
      PersistEnv K S (d.numStates + 1) (d.numLetters + 1) ∧
      AcceptEnv K B (d.numStates + 1) (d.numLetters + 1) ∧
      AcceptEnv K S (d.numStates + 1) (d.numLetters + 1) ∧
      d.numStates + 1 ≤ B ∧ d.numLetters + 1 ≤ B ∧
      d.numStates ≤ K ∧ d.numLetters ≤ K ∧ d.numLetters ≤ B ∧
      W ≤ K ∧ W ≤ B ∧ T + 1 ≤ K ∧
      d.blankIdx ≤ K ∧ (∀ v ∈ allowedIdx, v ≤ K) ∧
      allowedIdx.length + 1 ≤ K ∧ (∀ v ∈ prefIdx, v ≤ K) ∧
      freeLen ≤ K ∧ d.startState ≤ K ∧
      K * d.numLetters + K + K ≤ B ∧
      (d.table.map transKind).length ≤ B ∧ (d.table.map transArg1).length ≤ B ∧
      (d.table.map transArg2).length ≤ B ∧
      (∀ v ∈ d.table.map transKind, v ≤ K) ∧ (∀ v ∈ d.table.map transArg1, v ≤ K) ∧
      (∀ v ∈ d.table.map transArg2, v ≤ K) ∧
      kindBase ≤ K ∧ arg1Base ≤ K ∧ arg2Base ≤ K ∧ d.numStates ≤ B ∧
      (∀ v ∈ outIdx, v ≤ K) ∧ outIdx.length ≤ B ∧
      (∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0), v ≤ K) ∧
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ K ∧
      outBase ≤ K ∧ outBase + outIdx.length + 1 ≤ K := by
  refine ⟨0, 40, 32, 100000, 100000, 1, 1, 1, 1, 21, 24, 26, 28, 30,
    (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor), [0], [0], [0],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold initPrefBaseReg; norm_num)
    | (unfold UniqEnv; norm_num)
    | (unfold InitEnv; norm_num)
    | (unfold TransEnv; norm_num)
    | (unfold PersistEnv; norm_num)
    | (unfold AcceptEnv; norm_num)
    | (intro v hv; simp at hv; omega)
    | (unfold descHaltStates; decide)
    | norm_num

/-- The content-witness store satisfies the `GeneratorTableFrozen` premise
    of the table writer's bound, showing that the premise is realizable. -/
lemma clauseWriterBounded_tableWriterProgParam_contentWitness_frozen :
    GeneratorTableFrozen 0 1 1 1 1 21 [0] 24
      (List.map transKind (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor).table) 26
      (List.map transArg1 (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor).table) 28
      (List.map transArg2 (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor).table) 30 [0]
      (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
        else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
        else if r = 20 then 1 else if r = 21 then 0
        else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
        else if r = 29 then 1 else if r = 30 then 0 else 0) := by
  unfold GeneratorTableFrozen InitParamFrozen PinsAndWord PinsHold WordAt initParamPins0
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg]
  · norm_num
  · intro k hk; simp only [List.length_cons, List.length_nil] at hk; interval_cases k; norm_num
  · norm_num
  · intro k hk; simp at hk
  · norm_num
  · intro k hk; simp at hk
  · norm_num
  · intro k hk; simp at hk
  · norm_num
  · intro k hk; simp only [List.length_cons, List.length_nil] at hk; interval_cases k; norm_num

/-- The content-witness store's `StoreValuesLe` obligation, split out alongside
`clauseWriterBounded_tableWriterProgParam_contentWitness_frozen`. -/
lemma clauseWriterBounded_tableWriterProgParam_contentWitness_storeLe :
    StoreValuesLe 100000
      (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
        else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
        else if r = 20 then 1 else if r = 21 then 0
        else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
        else if r = 29 then 1 else if r = 30 then 0 else 0) := by
  intro i
  simp only []
  rcases eq_or_ne i 1 with h | h
  · subst h; norm_num
  rcases eq_or_ne i 15 with h1 | h1
  · subst h1; norm_num
  rcases eq_or_ne i 16 with h2 | h2
  · subst h2; norm_num
  rcases eq_or_ne i 17 with h3 | h3
  · subst h3; norm_num
  rcases eq_or_ne i 18 with h4 | h4
  · subst h4; norm_num
  rcases eq_or_ne i 19 with h5 | h5
  · subst h5; norm_num
  rcases eq_or_ne i 20 with h6 | h6
  · subst h6; norm_num
  rcases eq_or_ne i 21 with h7 | h7
  · subst h7; norm_num
  rcases eq_or_ne i 23 with h8 | h8
  · subst h8; norm_num
  rcases eq_or_ne i 25 with h9 | h9
  · subst h9; norm_num
  rcases eq_or_ne i 27 with h10 | h10
  · subst h10; norm_num
  rcases eq_or_ne i 29 with h11 | h11
  · subst h11; norm_num
  rcases eq_or_ne i 30 with h12 | h12
  · subst h12; norm_num
  simp [h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- The content-witness store's `TightCells` obligation, split out alongside
`clauseWriterBounded_tableWriterProgParam_contentWitness_frozen`. -/
lemma clauseWriterBounded_tableWriterProgParam_contentWitness_tightCells :
    TightCells 32 0
      (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
        else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
        else if r = 20 then 1 else if r = 21 then 0
        else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
        else if r = 29 then 1 else if r = 30 then 0 else 0) := by
  unfold TightCells
  intro j hj2 hj24; simp only []; interval_cases j <;> norm_num

/-- Concrete witness that `clauseWriterBounded_tableWriterProgParam` yields
`ProgramBoundedIn` for `tableWriterProgParam` at these parameters and this store.
The store obligations are proved by
`clauseWriterBounded_tableWriterProgParam_contentWitness_frozen`,
`clauseWriterBounded_tableWriterProgParam_contentWitness_storeLe`, and
`clauseWriterBounded_tableWriterProgParam_contentWitness_tightCells`. -/
lemma clauseWriterBounded_tableWriterProgParam_contentWitness : ProgramBoundedIn 100000
    (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
      else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
      else if r = 20 then 1 else if r = 21 then 0
      else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
      else if r = 29 then 1 else if r = 30 then 0 else 0)
    (tableWriterProgParam (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0] [0]) := by
  have hplace : GeneratorPlacement 0 40 1 21 24 26 28 30
      (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0] [0] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [initPrefBaseReg]
  have hfam := clauseWriterBounded_tableWriterProgParam 0 40 32 100000 100000 1 1 1 1 21 24
    26 28 30 (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0] [0] [0] hplace
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by unfold UniqEnv; norm_num) (by unfold UniqEnv; norm_num)
    (by unfold InitEnv; norm_num) (by unfold InitEnv; norm_num)
    (by unfold TransEnv; norm_num) (by unfold TransEnv; norm_num)
    (by unfold PersistEnv; norm_num) (by unfold PersistEnv; norm_num)
    (by unfold AcceptEnv; norm_num) (by unfold AcceptEnv; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by intro v hv; simp at hv; omega) (by norm_num)
    (by intro v hv; simp at hv; omega) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro v hv; simp at hv) (by intro v hv; simp at hv) (by intro v hv; simp at hv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro v hv; simp at hv; omega) (by norm_num)
    (by intro v hv; unfold descHaltStates at hv; simp at hv; omega)
    (by unfold descHaltStates; decide) (by norm_num) (by norm_num)
  exact (hfam
    (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
      else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
      else if r = 20 then 1 else if r = 21 then 0
      else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
      else if r = 29 then 1 else if r = 30 then 0 else 0)
    41 clauseWriterBounded_tableWriterProgParam_contentWitness_frozen
    (by norm_num) (by simp only [wpJ]; norm_num) (by norm_num)
    (by unfold descHaltStates; decide)
    clauseWriterBounded_tableWriterProgParam_contentWitness_storeLe
    clauseWriterBounded_tableWriterProgParam_contentWitness_tightCells).1

/-- Content-extraction witness: at concrete `M`, `wp`, and a store satisfying
all hypotheses, `clauseWriterBounded_tableWriterProgParam` actually yields a
`ProgramBoundedIn` fact for `tableWriterProgParam` — not merely a proof from
vacuous premises. -/
example : ProgramBoundedIn 100000
    (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 1
      else if r = 17 then 1 else if r = 18 then 1 else if r = 19 then 21
      else if r = 20 then 1 else if r = 21 then 0
      else if r = 23 then 0 else if r = 25 then 0 else if r = 27 then 0
      else if r = 29 then 1 else if r = 30 then 0 else 0)
    (tableWriterProgParam (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) [0] [0]) :=
  clauseWriterBounded_tableWriterProgParam_contentWitness

end

section
open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## Placement and frozen-prefix compatibility

At the post-setup store derived from `bitInputStore bits`, the prefix-length
cell `prefBase - 1` remains zero because the setup does not write it.
`GeneratorTableFrozen`'s `WordAt` premise then forces `prefIdx.length = 0`,
while `GeneratorPlacement` requires `prefLen = prefIdx.length ≥ 1`.  Thus these
two premises are incompatible at this store. -/

/-- `GeneratorPlacement` and `GeneratorTableFrozen` cannot both hold at the
    store produced by `generatorSetupProg` followed by `.assign 0 (setupME p)`
    from `bitInputStore bits`, for any polynomials, descriptor, or index lists.
    The frozen word premise forces a zero prefix length, contradicting the
    positive length required by the placement. -/
lemma tableWriterEntryUnreachable (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits)
    (Jmax W T freeLen prefLen prefBase kindBase arg1Base arg2Base outBase : ℕ)
    (prefIdx colk col1 col2 : List ℕ)
    (hplace : GeneratorPlacement (setupM p time d allowedIdx bits.length) Jmax prefLen prefBase
      kindBase arg1Base arg2Base outBase d prefIdx outIdx)
    (hF : GeneratorTableFrozen (setupM p time d allowedIdx bits.length) W T freeLen prefLen
      prefBase prefIdx kindBase colk arg1Base col1 arg2Base col2 outBase outIdx
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits)))) : False := by
  have hM1 : (1 : ℕ) ≤ setupM p time d allowedIdx bits.length := by
    have := setupM_gt p time d allowedIdx bits.length; omega
  have hprefBase_gt : bits.length < generatorPrefBase p time d allowedIdx bits.length - 1 := by
    unfold generatorPrefBase generatorPrefOffset setupM setupSpan
    have h1 : (0 : ℕ) ≤ p.eval bits.length := Nat.zero_le _
    have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval bits.length := Nat.zero_le _
    have h3 : bits.length ≤ 2 * bits.length + 3 + p.eval bits.length := by omega
    have h4 : (2 * bits.length + 3 + p.eval bits.length) ≤
        (2 * bits.length + 3 + p.eval bits.length) *
          ((2 * bits.length + 3 + p.eval bits.length) *
            (2 * bits.length + 3 + p.eval bits.length)) := by
      nlinarith [sq_nonneg (2 * bits.length + 3 + p.eval bits.length)]
    omega
  have hlayoutPins := generator_setup_prog_layout_pins p time d allowedIdx outIdx
    (bitInputStore bits) bits.length rfl
  have hρPins : PinsHold (setupM p time d allowedIdx bits.length)
      (generatorLayoutPins p time d allowedIdx outIdx bits.length)
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits))) :=
    generator_handoff_pins p time d allowedIdx _ (setupM p time d allowedIdx bits.length) _ hM1
      (fun q hq => by
        simp only [generatorLayoutPins, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg, transArg2BaseReg,
            acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]) hlayoutPins
  have hpin : (Program.assign 0 (setupME p time d allowedIdx)).eval
      ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits))
      (setupM p time d allowedIdx bits.length + initPrefBaseReg)
      = generatorPrefBase p time d allowedIdx bits.length :=
    hρPins (initPrefBaseReg, generatorPrefBase p time d allowedIdx bits.length)
      (by simp [generatorLayoutPins])
  have hFprefBase : (Program.assign 0 (setupME p time d allowedIdx)).eval
      ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits))
      (setupM p time d allowedIdx bits.length + initPrefBaseReg) = prefBase :=
    hF.1.1.1.1.1 (initPrefBaseReg, prefBase) (by simp [initParamPins0])
  have hprefBaseEq : prefBase = generatorPrefBase p time d allowedIdx bits.length := by
    rw [← hFprefBase, hpin]
  have hword : WordAt
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits)))
      prefBase prefIdx := hF.1.1.1.1.2
  have hb := (generator_staged_bases_above_setup p time d allowedIdx bits.length).1
  simp only [generatorTableBaseReg] at hb
  have hzero : (Program.assign 0 (setupME p time d allowedIdx)).eval
      ((generatorSetupProg p time d allowedIdx outIdx).eval (bitInputStore bits))
      (generatorPrefBase p time d allowedIdx bits.length - 1) = 0 := by
    rw [handoff_frame_ne p time d allowedIdx outIdx (bitInputStore bits) bits.length _ rfl
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact bitInputStore_eq_zero_of_ge_inputEnd bits _ (by omega)
  have hlen0 : prefIdx.length = 0 := by
    have hcell := hword.1
    rw [hprefBaseEq, hzero] at hcell
    omega
  have hlen := hplace.pref_len
  have hpos := hplace.pref_pos
  omega

/-- Non-vacuity: combined with the vertex, `CompiledOperandBound` follows at
    `B := envB.eval N` from just `1 ≤ B` and `StoreValuesLe B (bitInputStore
    bits)`.  The store bound follows from `bitInputStore_storeValuesLe`;
    the lower bounds on `envK` and `envB` below provide its hypotheses and `1 ≤ B`. -/
example (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (bits : Bits)
    (hB : 1 ≤ Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
    (hσ : StoreValuesLe (Polynomial.eval bits.length
      (envB p time d (prefixWord d bits) allowedIdx outIdx)) (bitInputStore bits)) :
    CompiledOperandBound (generatorProgFromBits p time d allowedIdx outIdx) bits
      (NPComplete.BitCostRAM.bitLen
        (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))) :=
  compiledOperandBound_generatorProgFromBits_of_programBoundedIn p time d allowedIdx outIdx bits _ hB hσ
    (programBoundedIn_generatorProgFromBits p time d allowedIdx outIdx bits)

/-! ## Non-vacuity

`post_setup_tightCells` / `post_setup_storeValuesLe` are not vacuous: at a concrete
instance (`p = time = X`, `d = initCheckDesc`, `bits = [true, false, true]`, so
`N = 3`, matching `GeneratorEnvelopeAgg.lean`'s `aggInstance*` witnesses) both
instantiate and yield genuine numeric facts, and `post_setup_pins` pins down an actual value
(`setupM X X initCheckDesc [0] 3 = 1847750595`) rather than an unconstrained
one.
`tableWriterEntryUnreachable` also fires concretely at this instance. -/

example :
    TightCells
      (Polynomial.eval (3 : ℕ) (envK Polynomial.X Polynomial.X initCheckDesc
        (List.replicate (generatorPrefLen 3) 0) [0] [0]))
      (setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0]
        ([true, false, true] : Bits).length)
      ((Program.assign 0 (setupME Polynomial.X Polynomial.X initCheckDesc [0])).eval
        ((generatorSetupProg Polynomial.X Polynomial.X initCheckDesc [0] [0]).eval
          (bitInputStore [true, false, true]))) := by
  have h := post_setup_tightCells Polynomial.X Polynomial.X initCheckDesc
    (List.replicate (generatorPrefLen 3) 0) [0] [0] (bitInputStore [true, false, true]) 3 rfl
    (by
      intro j hj2 hj13
      have hM := lt_setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0] 3
      rw [bitInputStore_eq_zero_of_ge_inputEnd [true, false, true] _ (by norm_num; omega)]
      exact Nat.zero_le _)
  simpa using h

example :
    StoreValuesLe
      (Polynomial.eval (3 : ℕ) (envB Polynomial.X Polynomial.X initCheckDesc
        (List.replicate (generatorPrefLen 3) 0) [0] [0]))
      ((Program.assign 0 (setupME Polynomial.X Polynomial.X initCheckDesc [0])).eval
        ((generatorSetupProg Polynomial.X Polynomial.X initCheckDesc [0] [0]).eval
          (bitInputStore [true, false, true]))) := by
  have hK1 := envK_ge_one Polynomial.X Polynomial.X initCheckDesc
    (List.replicate (generatorPrefLen 3) 0) [0] [0] 3
  have hKlen := envK_ge_two_n Polynomial.X Polynomial.X initCheckDesc
    (List.replicate (generatorPrefLen 3) 0) [0] [0] 3
  have hKB := envB_ge_envK Polynomial.X Polynomial.X initCheckDesc
    (List.replicate (generatorPrefLen 3) 0) [0] [0] 3
  have h := post_setup_storeValuesLe Polynomial.X Polynomial.X initCheckDesc
    (List.replicate (generatorPrefLen 3) 0) [0] [0] (bitInputStore [true, false, true]) 3 rfl
    (bitInputStore_storeValuesLe [true, false, true]
      (Polynomial.eval (3:ℕ) (envB Polynomial.X Polynomial.X initCheckDesc
        (List.replicate (generatorPrefLen 3) 0) [0] [0])) (by omega) (by norm_num; omega))
  simpa using h

/-- Cell `0` of the post-setup store is the concrete value
    `setupM X X initCheckDesc [0] 3 = 1847750595`, not merely `≤` some bound —
    `post_setup_pins` pins an actual number. -/
example :
    (Program.assign 0 (setupME Polynomial.X Polynomial.X initCheckDesc [0])).eval
      ((generatorSetupProg Polynomial.X Polynomial.X initCheckDesc [0] [0]).eval
        (bitInputStore [true, false, true])) 0 = 1847750595 := by
  have h := post_setup_pins Polynomial.X Polynomial.X initCheckDesc [0] [0]
    (bitInputStore [true, false, true]) 3 rfl
  simp only at h
  have h1 : (1847750595 : ℕ) = setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc
      [0] 3 := by
    unfold setupM setupSpan
    simp only [initCheckDesc]
    unfold emitLenPoly clauseCountPoly emitWidthPoly varBoundPoly
    simp [cookWindowPoly_eval, timePoly_eval]
  rw [h1]
  simpa using h.1

/-- `tableWriterEntryUnreachable` fires at this same concrete instance: the
    generator's own placement (`GeneratorPlacement` with `prefLen :=
    generatorPrefLen 3`, `prefBase := generatorPrefBase X 3`) together with
    `GeneratorTableFrozen` at the post-setup store is `False`, not an unused
    hypothesis. -/
example (Jmax W T freeLen kindBase arg1Base arg2Base outBase : ℕ)
    (prefIdx colk col1 col2 : List ℕ)
    (hplace : GeneratorPlacement
      (setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0]
        ([true, false, true] : Bits).length) Jmax
      (generatorPrefLen 3) (generatorPrefBase Polynomial.X Polynomial.X initCheckDesc [0] 3)
      kindBase arg1Base arg2Base
      outBase initCheckDesc prefIdx [0])
    (hF : GeneratorTableFrozen
      (setupM (Polynomial.X : Polynomial ℕ) Polynomial.X initCheckDesc [0]
        ([true, false, true] : Bits).length) W T freeLen
      (generatorPrefLen 3) (generatorPrefBase Polynomial.X Polynomial.X initCheckDesc [0] 3)
      prefIdx kindBase colk arg1Base
      col1 arg2Base col2 outBase [0]
      ((Program.assign 0 (setupME Polynomial.X Polynomial.X initCheckDesc [0])).eval
        ((generatorSetupProg Polynomial.X Polynomial.X initCheckDesc [0] [0]).eval
          (bitInputStore [true, false, true])))) : False :=
  tableWriterEntryUnreachable Polynomial.X Polynomial.X initCheckDesc [0] [0]
    [true, false, true] Jmax W T freeLen (generatorPrefLen 3)
    (generatorPrefBase Polynomial.X Polynomial.X initCheckDesc [0] 3) kindBase arg1Base arg2Base
    outBase prefIdx colk col1
    col2 hplace hF

/-- Non-vacuity check for the top-level vertex at `p = time = 0`,
    `d = loadConstTestDescriptor`, `allowedIdx = []`, `outIdx = [5, 7, 9]`, and
    mixed-bit input `[true, false, true]`.  The input length is `3`, so the load
    loop runs and both `ifNZ` branches are taken; with `B := envB.eval 3`,
    `programBoundedIn_generatorProgFromBits` establishes the required bound. -/
example :
    ProgramBoundedIn
      (Polynomial.eval 3 (envB 0 0 loadConstTestDescriptor
        (prefixWord loadConstTestDescriptor [true, false, true]) [] [5, 7, 9]))
      (bitInputStore [true, false, true])
      (generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]) :=
  programBoundedIn_generatorProgFromBits 0 0 loadConstTestDescriptor [] [5, 7, 9]
    [true, false, true]

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Verification: non-vacuity and content extraction -/

/-- Non-vacuity witness: `clauseWriterBounded_transFamilyProgParam`'s
hypotheses hold simultaneously at concrete values. -/
example :
    ∃ (M Jmax K S B nS W mS nC mC T wReg tReg kbReg a1Reg a2Reg
        kindBase arg1Base arg2Base : ℕ) (d : TableauDescriptor),
      TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg ∧
      TransParamTablePlacement M Jmax a2Reg kindBase (d.table.map transKind).length
        arg1Base (d.table.map transArg1).length arg2Base (d.table.map transArg2).length ∧
      24 ≤ Jmax ∧ 1 ≤ K ∧ 2 ≤ wReg ∧ wReg ≤ 23 ∧ tReg ≤ 23 ∧
      kbReg ≤ 23 ∧ a1Reg ≤ 23 ∧ a2Reg ≤ 23 ∧ M + 24 ≤ B ∧
      S ≤ B ∧ 4 ≤ S ∧ 3 ≤ S ∧ K + 1 ≤ B ∧ K ≤ S ∧
      TransEnv K B nS mS ∧ TransEnv K S nS mS ∧ nS ≤ B ∧ mS ≤ B ∧
      K * mC + K + K ≤ B ∧ mC ≤ B ∧ mC ≤ K ∧ nC ≤ K ∧
      (d.table.map transKind).length ≤ B ∧ (d.table.map transArg1).length ≤ B ∧
      (d.table.map transArg2).length ≤ B ∧
      (∀ v ∈ d.table.map transKind, v ≤ K) ∧ (∀ v ∈ d.table.map transArg1, v ≤ K) ∧
      (∀ v ∈ d.table.map transArg2, v ≤ K) ∧
      kindBase ≤ K ∧ arg1Base ≤ K ∧ arg2Base ≤ K ∧
      nC ≤ B ∧ W ≤ K ∧ T + 1 ≤ K := by
  refine ⟨0, 40, 100, 100000, 100000, 1, 1, 1, 1, 1, 0, 15, 16, 17, 18, 19, 24, 25, 26,
    (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_,
    ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  all_goals first
    | (unfold ctlJmax; norm_num)
    | (unfold TransEnv; norm_num)
    | (intro v hv; simp at hv)
    | norm_num

/-- Content-extraction witness: at concrete `M`, `wp`, and a store satisfying
all hypotheses, `clauseWriterBounded_transFamilyProgParam` actually yields a
`ProgramBoundedIn` fact — not merely a proof from vacuous premises.  This example uses an empty
transition table and separately sets the iteration bound `T` to `0`.  The family therefore evaluates zero outer iterations, and
`ProgramBoundedIn` checks the bound on the `.forN` node without running its body. -/
example : ProgramBoundedIn 100000
    (fun r => if r = 1 then (41 : ℕ) else if r = 15 then 1 else if r = 16 then 0
      else if r = 17 then 24 else if r = 18 then 25 else if r = 19 then 26
      else 0)
    (transFamilyProgParam 1 1 1 1 (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor)
      15 16 17 18 19) := by
  have hplace : TransParamPlacement 40 15 16 17 18 19 :=
    ⟨by unfold ctlJmax; norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩
  have htable : TransParamTablePlacement 0 40 19 24 0 25 0 26 0 :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hfam := clauseWriterBounded_transFamilyProgParam 0 40 100 100000 100000 1 1 1 1 1 0
    (⟨1, 0, 1, 0, 0, 0, []⟩ : TableauDescriptor) 24 25 26 15 16 17 18 19 hplace htable
    (hJ := by norm_num) (hK1 := by norm_num) (hwR := by norm_num) (hwR2 := by norm_num)
    (htR2 := by norm_num) (hkbR2 := by norm_num) (ha1R2 := by norm_num) (ha2R2 := by norm_num)
    (hMB := by norm_num) (hSB := by norm_num) (h4S := by norm_num) (h3S := by norm_num)
    (hKB := by norm_num) (hKS := by norm_num)
    (henvB := by unfold TransEnv; norm_num) (henvS := by unfold TransEnv; norm_num)
    (hnS := by norm_num) (hmS := by norm_num)
    (hK1mC := by norm_num) (hmCB := by norm_num) (hmCK := by norm_num) (hnCK := by norm_num)
    (hlenkB := by norm_num) (hlen1B := by norm_num) (hlen2B := by norm_num)
    (hallowedk := by intro v hv; simp at hv) (hallowed1 := by intro v hv; simp at hv)
    (hallowed2 := by intro v hv; simp at hv)
    (hkindBaseK := by norm_num) (harg1BaseK := by norm_num) (harg2BaseK := by norm_num)
    (hnCB := by norm_num) (hWK := by norm_num) (hTK1 := by norm_num)
  refine (hfam _ 41 ?_ (by norm_num) (by simp only [wpJ]; norm_num) (by norm_num)
    (by norm_num) ?_ ?_).1
  · unfold TransParamFrozen TransFrozen PinsAndWords3 PinsHold WordAt transParamPins0
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    · norm_num
    · intro k hk; simp at hk
    · norm_num
    · intro k hk; simp at hk
    · norm_num
    · intro k hk; simp at hk
  · intro i; simp only; split_ifs <;> omega
  · intro j hj2 hj24; simp only; split_ifs <;> omega

end

section
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- Non-vacuity witness: `clauseWriterBounded_uniquenessFamilyProgParam`'s hypotheses
all hold simultaneously at concrete values — ruling out a vacuous premise. -/
example :
    ∃ (K S B M Jmax nS W mS nC mC T wReg tReg : ℕ),
      UniquenessParamPlacement Jmax wReg tReg ∧ 24 ≤ Jmax ∧
      1 ≤ K ∧ 2 ≤ wReg ∧ wReg ≤ 23 ∧ tReg ≤ 23 ∧ M + 24 ≤ B ∧
      UniqEnv K B nS mS ∧ UniqEnv K S nS mS ∧ nS ≤ B ∧ mS ≤ B ∧
      S ≤ B ∧ K + 1 ≤ B ∧ K ≤ S ∧ nC ≤ K ∧ mC ≤ K ∧ W ≤ K ∧
      2 ≤ S ∧ T + 1 ≤ K := by
  refine ⟨2, 200, 300, 0, 24, 0, 1, 0, 1, 1, 1, 15, 16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num [ctlJmax], by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · unfold UniqEnv; norm_num
  · unfold UniqEnv; norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- The content-extraction test: a concrete store and write pointer actually
yield `ProgramBoundedIn`, which no vacuous hypothesis set could produce. -/
example : ProgramBoundedIn 400 (fun r => if r = 1 then (25 : ℕ) else if r = 15 then 2
      else if r = 16 then 1 else 0)
    (uniquenessFamilyProgParam 0 1 2 2 15 16) := by
  have hfam := clauseWriterBounded_uniquenessFamilyProgParam 2 300 400 0 24 0 2 1 2 2 1 15 16
    ⟨by norm_num [ctlJmax], by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold UniqEnv; norm_num) (by unfold UniqEnv; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine (hfam _ 25 ?_ (by norm_num) (by simp only [wpJ]; norm_num) (by omega) (by norm_num)
    ?_ ?_).1
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num
  · intro i
    by_cases h1 : i = 1
    · simp [h1]
    · by_cases h15 : i = 15
      · simp [h15]
      · by_cases h16 : i = 16
        · simp [h16]
        · simp [h1, h15, h16]
  · intro j h2 h24
    by_cases h15 : j = 15
    · simp [h15]
    · by_cases h16 : j = 16
      · simp [h16]
      · have : j ≠ 1 := by omega
        simp [this, h15, h16]

end

end NPComplete.CookLevin

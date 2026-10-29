module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAccept
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedTransFamily
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAcceptParam

/-!
The accept family is `PinsAndWord`-shaped, exactly like the init family's own
staged prefix word: its three `_of_word` expression lemmas
(`acceptWordReadEParam`/`acceptSymbolEParam`/`acceptOutputSymbolEParam`) are
the same shape as `wordReadEParam`/`symbolAtEParam`/
`initPrefixSymbolEParam` (`GeneratorBoundedInitFamily`) — register facts plus
the staged word's own `hallowed` bound, not a whole-store envelope — and the
leaf's `.seq` (stage into `tmpJ`, then `writeClauseProg`) closes through
plain `clauseWriterBounded_seq`, since neither bound obligation here needs
the staged value pinned.

The nest is two `W`-loops (`clauseWriterBounded_loopProg_up_to` twice) followed
by a `writeAtLeastOneProg` halt block, composed by `clauseWriterBounded_seq`
— the same shape as `initFamilyProgParam`'s `.seq` chain, one level
shallower.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Word-based expression bounds for the staged output symbol -/

/-- Structurally identical to `exprBoundedIn_wordReadEParam_of_word`
(`GeneratorBoundedInitFamily`): register facts (`hbase`, `hbR`) plus the
staged word's own `hallowed`/`hword` facts, not a whole-store envelope. -/
lemma exprBoundedIn_acceptWordReadEParam_of_word
    (M K B baseReg blank base : ℕ) (xs : List ℕ) (σ : Store) (kE : Expr) (KV : ℕ)
    (h0 : σ 0 = M) (hbase : σ (M + baseReg) = base)
    (hword : WordAt σ base xs) (hallowed : ∀ v ∈ xs, v ≤ K)
    (hbR : baseReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + KV ≤ B) (hblank : blank ≤ K) (hbaseK : base ≤ K)
    (hlenB : xs.length ≤ B)
    (hk : ExprBoundedIn B σ kE) (hkv : kE.eval σ ≤ KV) :
    ExprBoundedIn B σ (acceptWordReadEParam baseReg blank xs.length kE) ∧
      (acceptWordReadEParam baseReg blank xs.length kE).eval σ ≤ K := by
  unfold acceptWordReadEParam wordReadEExpr
  simp only [ExprBoundedIn, Expr.eval, ctlCell, ctlAddr, h0, hbase]
  by_cases hc : kE.eval σ < xs.length
  · have hgetv : xs.getD (kE.eval σ) 0 ≤ K :=
      hallowed _ (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc)
    have hdataval : σ (base + kE.eval σ) = xs.getD (kE.eval σ) 0 :=
      hword.2 (kE.eval σ) hc
    simp [hc]
    refine ⟨?_, ?_⟩ <;> (repeat' apply And.intro) <;> omega
  · simp [hc]
    refine ⟨?_, ?_⟩ <;> (repeat' apply And.intro) <;> omega

lemma exprBoundedIn_acceptSymbolEParam_of_word
    (M K B baseReg blank base : ℕ) (xs : List ℕ) (σ : Store) (pE qE : Expr) (KV : ℕ)
    (h0 : σ 0 = M) (hbase : σ (M + baseReg) = base)
    (hword : WordAt σ base xs) (hallowed : ∀ v ∈ xs, v ≤ K)
    (hbR : baseReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + KV ≤ B) (hblank : blank ≤ K) (hbaseK : base ≤ K)
    (hlenB : xs.length ≤ B)
    (hp : ExprBoundedIn B σ pE) (hq : ExprBoundedIn B σ qE)
    (hpv : pE.eval σ ≤ KV) :
    ExprBoundedIn B σ (acceptSymbolEParam baseReg blank xs.length pE qE) ∧
      (acceptSymbolEParam baseReg blank xs.length pE qE).eval σ ≤ K := by
  have hsub : ExprBoundedIn B σ (pE.sub qE) := ⟨hp, hq, by omega⟩
  have hsubv : (pE.sub qE).eval σ ≤ KV := by simp only [Expr.eval]; omega
  obtain ⟨hreadB, hreadV⟩ := exprBoundedIn_acceptWordReadEParam_of_word M K B baseReg blank
    base xs σ (pE.sub qE) KV h0 hbase hword hallowed hbR hMK h1B hK hblank hbaseK hlenB
    hsub hsubv
  unfold acceptSymbolEParam
  have h1 : ExprBoundedIn B σ (((Expr.const 1).sub (pE.lt qE)).mul
      (acceptWordReadEParam baseReg blank xs.length (pE.sub qE))) := by
    simp only [ExprBoundedIn, Expr.eval]
    refine ⟨⟨h1B, ⟨hp, hq⟩, h1B⟩, hreadB, ?_⟩
    by_cases h : pE.eval σ < qE.eval σ
    · simp [h]
    · simp [h]
      exact Nat.le_trans hreadV (by omega)
  have h2 : ExprBoundedIn B σ ((pE.lt qE).mul (Expr.const blank)) := by
    simp only [ExprBoundedIn, Expr.eval]
    refine ⟨⟨hp, hq⟩, by omega, ?_⟩
    by_cases h : pE.eval σ < qE.eval σ
    · simp [h]
      omega
    · simp [h]
  refine ⟨⟨h1, h2, ?_⟩, ?_⟩
  · simp only [Expr.eval]
    by_cases h : pE.eval σ < qE.eval σ <;> simp [h] <;> omega
  · simp only [Expr.eval]
    by_cases h : pE.eval σ < qE.eval σ <;> simp [h] <;> omega

/-- `acceptOutputSymbolEParam` bounded from register facts (`obReg` is a
control cell under `TightCells`) and the staged output word's own
`hallowed` bound, matching `exprBoundedIn_initPrefixSymbolEParam_of_word`'s
role for the init family. -/
lemma exprBoundedIn_acceptOutputSymbolEParam_of_word
    (M K B obReg blank outBase : ℕ) (outIdx : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (hbase : σ (M + obReg) = outBase)
    (hword : WordAt σ outBase outIdx) (hallowed : ∀ v ∈ outIdx, v ≤ K)
    (hobR : obReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + K ≤ B) (hblank : blank ≤ K) (houtBaseK : outBase ≤ K)
    (hlenB : outIdx.length ≤ B)
    (h3 : σ (M + lvJ1) ≤ K) :
    ExprBoundedIn B σ (acceptOutputSymbolEParam obReg blank outIdx.length) ∧
      (acceptOutputSymbolEParam obReg blank outIdx.length).eval σ ≤ K := by
  have hlv1 : ExprBoundedIn B σ (ctlCell lvJ1) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
    simp only [lvJ1] at h3 ⊢; omega
  have hlv1v : (ctlCell lvJ1).eval σ ≤ K := by
    simp only [ctlCell, ctlAddr, Expr.eval, h0]; omega
  have hlv0 : ExprBoundedIn B σ (ctlCell lvJ0) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
    simp only [lvJ0] at ⊢; omega
  unfold acceptOutputSymbolEParam
  exact exprBoundedIn_acceptSymbolEParam_of_word M K B obReg blank outBase outIdx σ
    (ctlCell lvJ1) (ctlCell lvJ0) K h0 hbase hword hallowed hobR hMK h1B hK hblank houtBaseK
    hlenB hlv1 hlv0 hlv1v

/-! ## The staged fixed-width leaf -/

/-- The leaf's `ClauseWriterBounded`: an unconditional `ctlAssign`-into-scratch
followed by a `writeClauseProg`, matching `acceptLeafProgParam`'s own `.seq`.
Composed with plain `clauseWriterBounded_seq` (rather than the `_seq_io`
Frozen-changing combinator) because neither bound obligation here needs the
staged value pinned — the value bound comes straight from `TightCells`.
`outBase ≤ K` is derived locally from `TightCells` via the pin rather than
carried as a hypothesis, matching how
`clauseWriterBounded_init_window_prefix_branch` derives `hprefBaseK`. -/
lemma clauseWriterBounded_acceptLeafProgParam
    (M Jmax K S B n W m T outBase blank pHead p wReg tReg obReg : ℕ) (outIdx : List ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg) (hJ : 24 ≤ Jmax)
    (hbase : M + obReg + 1 < outBase)
    (henvB : AcceptEnv K B n m) (henvS : AcceptEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hK1 : 1 ≤ K) (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hobR2 : obReg ≤ 23)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKS : K ≤ S)
    (hblank : blank ≤ K)
    (houtAllowed : ∀ v ∈ outIdx, v ≤ K)
    (hlenB : outIdx.length ≤ B) :
    ClauseWriterBounded (acceptLeafProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ K S B 6
      (PinsAndWord M (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx) := by
  have hw1' := hplace.w_min; have hw2' := hplace.w_t; have hw3' := hplace.t_ob
  have hw4' := hplace.ob_le; have hJctl := hplace.ctl_le
  unfold AcceptEnv at henvB henvS
  set Frozen := PinsAndWord M (acceptParamPins2 wReg tReg obReg W T outBase pHead p)
    outBase outIdx with hFrozenDef
  have hcellsFrozen : ∀ τ : Store, Frozen τ → τ 0 = M → TightCells K M τ →
      τ (M + obReg) ≤ K ∧ τ (M + lvJ0) ≤ K ∧ τ (M + lvJ1) ≤ K := by
    intro τ hF h0 ht
    exact ⟨ht obReg (by omega) (by omega), ht lvJ0 (by unfold lvJ0; omega) (by unfold lvJ0; omega),
      ht lvJ1 (by unfold lvJ1; omega) (by unfold lvJ1; omega)⟩
  have hb1 : ClauseWriterBounded
      (ctlAssign tmpJ (acceptOutputSymbolEParam obReg blank outIdx.length))
      M Jmax wpJ K S B 0 Frozen := by
    refine clauseWriterBounded_ctlAssign_scratch M Jmax K S B tmpJ
      (acceptOutputSymbolEParam obReg blank outIdx.length) Frozen
      (by unfold tmpJ; omega) (by unfold tmpJ; omega) hMB hKS ?_
    intro τ hF h0 ht hst
    obtain ⟨gob, _, g1⟩ := hcellsFrozen τ hF h0 ht
    have hob : τ (M + obReg) = outBase := by
      have := ctlCell_eval_of_pin M (acceptParamPins2 wReg tReg obReg W T outBase pHead p)
        obReg outBase τ (by simp [acceptParamPins2, acceptParamPins1, acceptParamPins0]) hF.1 h0
      rwa [ctlCell_eval, h0] at this
    exact exprBoundedIn_acceptOutputSymbolEParam_of_word M K B obReg blank outBase outIdx τ h0
      hob hF.2 houtAllowed hobR2 (by omega) (by omega) (by omega) hblank (hob ▸ gob) hlenB g1
  have hb2 : ClauseWriterBounded
      (writeClauseProg wpJ
        (implyPosLits (acceptHeadEParam n m wReg tReg) (acceptCellStagedEParam n m wReg tReg)))
      M Jmax wpJ K S B 6 Frozen := by
    have h := clauseWriterBounded_writeClauseProg M Jmax K S B
      (implyPosLits (acceptHeadEParam n m wReg tReg) (acceptCellStagedEParam n m wReg tReg))
      Frozen hJ hMB hSB (by simp [implyPosLits]; omega)
      (litsBounded_accept_leaf K S B M n m wReg tReg hK1 (by omega) hwR2 (by omega) htR2 hMB
        (by unfold AcceptEnv; omega) (by unfold AcceptEnv; omega) hn hm)
    simpa [implyPosLits] using h
  have hw1 : ClauseWriter (ctlAssign tmpJ (acceptOutputSymbolEParam obReg blank outIdx.length))
      M Jmax wpJ Frozen [] :=
    clauseWriter_ctlAssign_scratch M Jmax tmpJ
      (acceptOutputSymbolEParam obReg blank outIdx.length)
      (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx
      (by unfold tmpJ; omega) (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hJctl)
      (by unfold tmpJ wpJ; omega)
      (fun q hq => (accept_param_pins2_ok Jmax wReg tReg obReg W T outBase pHead p tmpJ hplace
        (by unfold tmpJ ctlJmax; omega) (by unfold lvJ0 tmpJ; omega)
        (by unfold lvJ1 tmpJ; omega) q hq).2.2.1)
      (by unfold tmpJ; omega)
  unfold acceptLeafProgParam
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B 0 6 Frozen [] hw1
    (le_of_eq (rowTableWidth_zero _)) hb1 hb2

/-! ## The two window loops -/

/-- The `p` loop as a `ClauseWriterBounded`, given the leaf's own bound at
every window position — mirroring `clauseWriterBounded_initWindowProgParam`. -/
lemma clauseWriterBounded_acceptInnerProgParam
    (M Jmax K S B n W m T outBase blank pHead wReg tReg obReg : ℕ) (outIdx : List ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase) (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B) (hKS : K ≤ S) (hKB : K ≤ B) (hWK : W ≤ K)
    (hleaf : ∀ p, ClauseWriterBounded
      (acceptLeafProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ K S B 6
      (PinsAndWord M (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)) :
    ClauseWriterBounded (acceptInnerProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ K S B (W * 6)
      (PinsAndWord M (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx) := by
  have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_ob
  have hw4 := hplace.ob_le
  have hctlbase : M + ctlJmax < outBase := by unfold ctlJmax; omega
  have hlvJ1le : lvJ1 ≤ 24 := by unfold lvJ1; omega
  unfold acceptInnerProgParam
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ1 W 6 (ctlCell wReg) _
    (PinsAndWord M (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx)
    (fun p => [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))])
    (by unfold lvJ1; omega) hlvJ1le hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ1 (.const 0)).eval τ = writeReg τ (M + lvJ1) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWord_writeReg_loop M
        (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx lvJ1 0 τ hF
        (by unfold lvJ1 lvJ3; omega) (fun q hq => by
          obtain ⟨_, _, hpne, _⟩ := accept_param_pins1_ok Jmax wReg tReg obReg W T outBase pHead
            lvJ1 hplace (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) q hq
          omega) hctlbase)
    (fun p _ => by
      have hcl : [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))].length = 1 := rfl
      rw [hcl, rowTableWidth_singleton, implyPos_len])
    (clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ1
      (acceptParamPins1 wReg tReg obReg W T outBase pHead) _ outBase outIdx
      (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega)
      (fun q hq => accept_param_pins1_ok Jmax wReg tReg obReg W T outBase pHead lvJ1 hplace
        (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) q hq)
      hctlbase (fun p => by
        have hpins : (lvJ1, p) :: acceptParamPins1 wReg tReg obReg W T outBase pHead =
            acceptParamPins2 wReg tReg obReg W T outBase pHead p := rfl
        rw [hpins]
        exact accept_leaf_writer_param M Jmax n W m T outBase blank pHead p wReg tReg obReg
          outIdx hplace hbase hfit))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_word _ M Jmax wpJ lvJ1 K S B W 6
      (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx
      (fun p => [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))])
      (by unfold lvJ1; omega) hlvJ1le hMB hKS hKB hWK
      (fun p => by
        have hpins : (lvJ1, p) :: acceptParamPins1 wReg tReg obReg W T outBase pHead =
            acceptParamPins2 wReg tReg obReg W T outBase pHead p := rfl
        rw [hpins]
        exact accept_leaf_writer_param M Jmax n W m T outBase blank pHead p wReg tReg obReg
          outIdx hplace hbase hfit)
      (fun p => by
        change ClauseWriterBounded _ M Jmax wpJ K S B 6
          (PinsAndWord M
            (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)
        exact hleaf p))
    (fun τ hF h0 => by
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by unfold lvJ1; omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ1 (.const 0)).eval τ = writeReg τ (M + lvJ1) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      have hF' : PinsAndWord M
          (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx
          ((ctlAssign lvJ1 (.const 0)).eval τ) := by
        rw [heq]
        exact pinsAndWord_writeReg_loop M
          (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx lvJ1 0 τ hF
          (by unfold lvJ1 lvJ3; omega) (fun q hq => by
            obtain ⟨_, _, hpne, _⟩ := accept_param_pins1_ok Jmax wReg tReg obReg W T outBase
              pHead lvJ1 hplace (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega) q hq
            omega) hctlbase
      have h1 : ((ctlAssign lvJ1 (.const 0)).eval τ) 0 = M := by
        rw [heq, writeReg_diff τ (M + lvJ1) 0 0 (by unfold lvJ1; omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [acceptParamPins1, acceptParamPins0]) hF'.1
        h1)

/-- The window loop's own `List.map` clause list has width at most `W * 6`:
every window position writes at most one `implyPos` row (two literals). -/
lemma accept_inner_map_width (n W m T pHead blank : ℕ) (outIdx : List ℕ) :
    rowTableWidth
      (rowW ((List.range W).map fun p =>
        implyPos ((denseLayout n W m).head T pHead)
          ((denseLayout n W m).cell T p
            (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))))
      ((List.range W).map fun p =>
        implyPos ((denseLayout n W m).head T pHead)
          ((denseLayout n W m).cell T p
            (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))).length
      ≤ W * 6 := by
  rw [List.length_map, List.length_range]
  refine rowTableWidth_le_count_mul _ _ 2 (fun i hi => ?_)
  have heq : (rowW ((List.range W).map fun p =>
      implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ)))))) i
      = (implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T i
          (natInitSymbol blank outIdx ((i : ℤ) - (pHead : ℤ))))).lits.length := by
    unfold rowW
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  rw [heq, implyPos_len]

/-- The `pHead` loop as a `ClauseWriterBounded`, given the leaf's own bound
at every `(pHead, p)` pair — mirroring `clauseWriterBounded_initWindowProgParam`
one level up. -/
lemma clauseWriterBounded_acceptOuterProgParam
    (M Jmax K S B n W m T outBase blank wReg tReg obReg : ℕ) (outIdx : List ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg)
    (hbase : M + obReg + 1 < outBase) (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B) (hKS : K ≤ S) (hKB : K ≤ B) (hWK : W ≤ K)
    (hleaf : ∀ pHead p, ClauseWriterBounded
      (acceptLeafProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ K S B 6
      (PinsAndWord M (acceptParamPins2 wReg tReg obReg W T outBase pHead p) outBase outIdx)) :
    ClauseWriterBounded (acceptOuterProgParam n m blank outIdx.length wReg tReg obReg)
      M Jmax wpJ K S B (W * (W * 6))
      (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx) := by
  have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_ob
  have hw4 := hplace.ob_le
  have hctlbase : M + ctlJmax < outBase := by unfold ctlJmax; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  unfold acceptOuterProgParam
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 W (W * 6) (ctlCell wReg) _
    (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx)
    (fun pHead => (List.range W).map fun p =>
      implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ)))))
    (by unfold lvJ0; omega) hlvJ0le hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWord_writeReg_loop M
        (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx lvJ0 0 τ hF
        (by unfold lvJ0 lvJ3; omega) (fun q hq => by
          obtain ⟨_, _, hpne, _⟩ := accept_param_pins0_ok Jmax wReg tReg obReg W T outBase
            lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) q hq
          omega) hctlbase)
    (fun pHead _ => accept_inner_map_width n W m T pHead blank outIdx)
    (clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0
      (acceptParamPins0 wReg tReg obReg W T outBase) _ outBase outIdx
      (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      (fun q hq => accept_param_pins0_ok Jmax wReg tReg obReg W T outBase lvJ0 hplace
        (by unfold lvJ0 ctlJmax; omega) q hq)
      hctlbase (fun pHead => by
        have hpins : (lvJ0, pHead) :: acceptParamPins0 wReg tReg obReg W T outBase =
            acceptParamPins1 wReg tReg obReg W T outBase pHead := rfl
        rw [hpins]
        exact accept_p_loop_writer_param M Jmax n W m T outBase blank pHead wReg tReg obReg
          outIdx hplace hbase hfit))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_word _ M Jmax wpJ lvJ0 K S B W (W * 6)
      (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx
      (fun pHead => (List.range W).map fun p =>
        implyPos ((denseLayout n W m).head T pHead)
          ((denseLayout n W m).cell T p
            (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ)))))
      (by unfold lvJ0; omega) hlvJ0le hMB hKS hKB hWK
      (fun pHead => by
        have hpins : (lvJ0, pHead) :: acceptParamPins0 wReg tReg obReg W T outBase =
            acceptParamPins1 wReg tReg obReg W T outBase pHead := rfl
        rw [hpins]
        exact accept_p_loop_writer_param M Jmax n W m T outBase blank pHead wReg tReg obReg
          outIdx hplace hbase hfit)
      (fun pHead => by
        change ClauseWriterBounded _ M Jmax wpJ K S B (W * 6)
          (PinsAndWord M
            (acceptParamPins1 wReg tReg obReg W T outBase pHead) outBase outIdx)
        exact clauseWriterBounded_acceptInnerProgParam M Jmax K S B n W m T outBase blank
          pHead wReg tReg obReg outIdx hplace hbase hfit hwR2 hMB hKS hKB hWK
          (fun p => hleaf pHead p)))
    (fun τ hF h0 => by
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      have hF' : PinsAndWord M
          (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx
          ((ctlAssign lvJ0 (.const 0)).eval τ) := by
        rw [heq]
        exact pinsAndWord_writeReg_loop M
          (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx lvJ0 0 τ hF
          (by unfold lvJ0 lvJ3; omega) (fun q hq => by
            obtain ⟨_, _, hpne, _⟩ := accept_param_pins0_ok Jmax wReg tReg obReg W T outBase
              lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) q hq
            omega) hctlbase
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        rw [heq, writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [acceptParamPins0]) hF'.1 h1)

/-! ## The final halt-state clause -/

/-- `acceptHaltProgParam`'s `ClauseWriterBounded`: a single
`writeAtLeastOneProg` row over the compile-time-constant `qs.length`, with
`exprBoundedIn_acceptHaltVarEParam` bounding its variable expression from
control cells alone (no staged word, unlike the leaf). -/
lemma clauseWriterBounded_acceptHaltProgParam
    (M Jmax K S B n m wReg tReg : ℕ) (qs : List ℕ) (Frozen : Store → Prop)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (htR : 2 ≤ tReg) (htR2 : tReg ≤ 23)
    (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hSB : S ≤ B)
    (henvB : AcceptEnv K B n m) (henvS : AcceptEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hqsK : ∀ v ∈ qs, v ≤ K) (hqslenK : qs.length ≤ K) :
    ClauseWriterBounded (acceptHaltProgParam n m wReg tReg qs)
      M Jmax wpJ K S B (2 + 2 * qs.length) Frozen := by
  unfold AcceptEnv at henvB henvS
  have hMK : M + 23 ≤ B := by omega
  have h1B : 1 ≤ B := by omega
  have hVB : K ≤ B := by omega
  have hprod : K * (n + K + K * m) + K ≤ B := by omega
  have hVS : K * (n + K + K * m) + K ≤ S := by omega
  unfold acceptHaltProgParam
  refine clauseWriterBounded_writeAtLeastOneProg_const M Jmax K S B litJ qs.length
    (acceptHaltVarEParam n m wReg tReg qs) Frozen hJ (by unfold litJ; omega)
    (by unfold litJ; omega) hMB hKB hKS hSB hqslenK ?_
  intro τ h0 ht hst
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  have gt : τ (M + tReg) ≤ K := ht tReg htR (by omega)
  have gl : τ (M + litJ) ≤ K := ht litJ (by unfold litJ; omega) (by unfold litJ; omega)
  refine ⟨exprBoundedIn_acceptHaltVarEParam M K B n m wReg tReg K qs τ hK1 h0 gw gt gl hwR2 htR2
    hMK h1B hVB hqsK hprod hn hm, ?_⟩
  exact le_trans (acceptHaltVarEParam_eval_le M K n m wReg tReg K qs τ h0 gw gt hqsK) hVS

/-! ## The whole family -/

/-- The `pHead × p` clause list has width at most `W * (W * 6)`: `W`
iterations of the `p` loop, each at most `W * 6`. -/
lemma accept_outer_width (n W m T : ℕ) (blank : ℕ) (outIdx : List ℕ) :
    rowTableWidth
      (rowW ((List.range W).flatMap fun pHead =>
        (List.range W).map fun p =>
          implyPos ((denseLayout n W m).head T pHead)
            ((denseLayout n W m).cell T p
              (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))))
      ((List.range W).flatMap fun pHead =>
        (List.range W).map fun p =>
          implyPos ((denseLayout n W m).head T pHead)
            ((denseLayout n W m).cell T p
              (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))).length
      ≤ W * (W * 6) :=
  rowTableWidth_flatMap_range_le
    (fun pHead => (List.range W).map fun p =>
      implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ)))))
    (W * 6) W (fun pHead _ => accept_inner_map_width n W m T pHead blank outIdx)

/-- The full accept family, as a `ClauseWriterBounded`: the two nested `W`
loops (width `W * (W * 6)`) followed by the halt block (width `2 + 2 *
qs.length`), composed via `.seq` matching `acceptFamilyProgParam`'s own
nest — mirroring `clauseWriterBounded_initFamilyProgParam`'s top-level
`.seq`. -/
lemma clauseWriterBounded_acceptFamilyProgParam
    (M Jmax K S B n W m T outBase : ℕ) (d : TableauDescriptor) (outIdx : List ℕ)
    (wReg tReg obReg : ℕ)
    (hplace : AcceptParamPlacement Jmax wReg tReg obReg) (hJ : 24 ≤ Jmax)
    (hbase : M + obReg + 1 < outBase) (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hK1 : 1 ≤ K) (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hobR2 : obReg ≤ 23)
    (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hSB : S ≤ B) (hWK : W ≤ K)
    (henvB : AcceptEnv K B n m) (henvS : AcceptEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hblank : d.blankIdx ≤ K)
    (houtAllowed : ∀ v ∈ outIdx, v ≤ K) (hlenB : outIdx.length ≤ B)
    (hqsK : ∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0), v ≤ K)
    (hqslenK : (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ K) :
    ClauseWriterBounded (acceptFamilyProgParam n m d outIdx wReg tReg obReg)
      M Jmax wpJ K S B
      (W * (W * 6) + (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length))
      (AcceptParamFrozen M wReg tReg obReg W T outBase outIdx) := by
  have hw1 := hplace.w_min
  have hw2 := hplace.w_t
  have hw3 := hplace.t_ob
  unfold acceptFamilyProgParam AcceptParamFrozen
  refine clauseWriterBounded_seq _ _ M Jmax wpJ K S B (W * (W * 6))
    (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length)
    (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx) _
    (accept_p_head_loop_writer_param M Jmax n W m T outBase d.blankIdx wReg tReg obReg outIdx
      hplace hbase hfit)
    (accept_outer_width n W m T d.blankIdx outIdx)
    (clauseWriterBounded_acceptOuterProgParam M Jmax K S B n W m T outBase d.blankIdx wReg
      tReg obReg outIdx hplace hbase hfit hwR2 hMB hKS (by omega) hWK
      (fun pHead p => clauseWriterBounded_acceptLeafProgParam M Jmax K S B n W m T outBase
        d.blankIdx pHead p wReg tReg obReg outIdx hplace hJ hbase henvB henvS hn hm hK1 hwR2 htR2
        hobR2 hMB hSB hKS hblank houtAllowed hlenB))
    (clauseWriterBounded_acceptHaltProgParam M Jmax K S B n m wReg tReg
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0))
      (PinsAndWord M (acceptParamPins0 wReg tReg obReg W T outBase) outBase outIdx)
      hJ hK1 (by omega) hwR2 (by omega) htR2 hMB hKB hKS hSB henvB henvS hn hm hqsK hqslenK)

end NPComplete.CookLevin

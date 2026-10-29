module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedTrans
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedInitFamily
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedKit
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyTransParam

/-!
The trans family nests four loops like persist (`t`, `p`, `qi`, `ai`), but its
innermost body is a run-time branch — `transLeafProgParam` is a tree of
`.ifNZ` reading the transition table's three staged columns, selecting among
`forbid3`/halt/write/move — rather than persist's single fixed leaf shape.
`clauseWriterBounded_ifNZ` (`GeneratorBoundedInitFamily`) wires each branch
point in; the four fixed-shape blocks it selects between
(`transForbidBlockProgParam`/`transHaltBlockProgParam`/
`transWriteBlockProgParam`/`transMoveBlockProgParam`) are each three
`imply3`/`forbid3` rows sharing one antecedent, matching
`imply3_writer_words3_param`'s own shape.

Two staged registers (`litJ`/`tmpJ`) hold the selected successor row before
the write/move blocks read them back, so those two blocks run under a
different `Frozen` (one more pin) than the antecedent and the halt/forbid
blocks — `clauseWriterBounded_seq_io` is the `.seq` combinator for that
Frozen-changing composition, mirroring `clauseWriterIO_seq`'s correctness
side. `wordReadEBaseParam`'s three column reads need their own
`ExprBoundedIn` lemmas here rather than the `TightCells`-only ones in
`GeneratorBoundedExpr`, since the touched table entry is bounded only by
`PinsAndWords3`'s own `WordAt`/allowed-list facts (a whole-store `∀ i, σ i
≤ K` is false past the write pointer).
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Word-based expression bounds for the three table columns

Structurally identical to `exprBoundedIn_wordReadEParam_of_word`
(`GeneratorBoundedInitFamily`), but for `wordReadEBaseParam`'s
compile-time-constant length. -/

lemma exprBoundedIn_wordReadEBaseParam_of_word
    (M K B baseReg blank base : ℕ) (xs : List ℕ) (σ : Store) (kE : Expr) (KV : ℕ)
    (h0 : σ 0 = M) (hbase : σ (M + baseReg) = base)
    (hword : WordAt σ base xs) (hallowed : ∀ v ∈ xs, v ≤ K)
    (hbR : baseReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + KV ≤ B) (hblank : blank ≤ K) (hbaseK : base ≤ K)
    (hlenB : xs.length ≤ B)
    (hk : ExprBoundedIn B σ kE) (hkv : kE.eval σ ≤ KV) :
    ExprBoundedIn B σ (wordReadEBaseParam baseReg blank xs.length kE) ∧
      (wordReadEBaseParam baseReg blank xs.length kE).eval σ ≤ K := by
  unfold wordReadEBaseParam wordReadEExpr
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

lemma exprBoundedIn_transKindEParam_of_word
    (M K B kbReg kindBase mC : ℕ) (colk : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hbase : σ (M + kbReg) = kindBase) (hword : WordAt σ kindBase colk)
    (hallowed : ∀ v ∈ colk, v ≤ K)
    (hkbR : kbReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hprod : K * mC + K + K ≤ B) (hlenB : colk.length ≤ B) (hmC : mC ≤ B)
    (hkindBaseK : kindBase ≤ K) :
    ExprBoundedIn B σ (transKindEParam kbReg colk.length mC) ∧
      (transKindEParam kbReg colk.length mC).eval σ ≤ K := by
  obtain ⟨hidxB, hidxV⟩ := exprBoundedIn_transIdxE M K B mC σ h0 h4 h5 (by omega) hmC (by omega)
  unfold transKindEParam
  exact exprBoundedIn_wordReadEBaseParam_of_word M K B kbReg 0 kindBase colk σ (transIdxE mC)
    (K * mC + K) h0 hbase hword hallowed hkbR hMK h1B (by omega) (by omega) hkindBaseK hlenB
    hidxB hidxV

lemma exprBoundedIn_transArg1EParam_of_word
    (M K B a1Reg arg1Base mC : ℕ) (col1 : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hbase : σ (M + a1Reg) = arg1Base) (hword : WordAt σ arg1Base col1)
    (hallowed : ∀ v ∈ col1, v ≤ K)
    (ha1R : a1Reg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hprod : K * mC + K + K ≤ B) (hlenB : col1.length ≤ B) (hmC : mC ≤ B)
    (harg1BaseK : arg1Base ≤ K) :
    ExprBoundedIn B σ (transArg1EParam a1Reg col1.length mC) ∧
      (transArg1EParam a1Reg col1.length mC).eval σ ≤ K := by
  obtain ⟨hidxB, hidxV⟩ := exprBoundedIn_transIdxE M K B mC σ h0 h4 h5 (by omega) hmC (by omega)
  unfold transArg1EParam
  exact exprBoundedIn_wordReadEBaseParam_of_word M K B a1Reg 0 arg1Base col1 σ (transIdxE mC)
    (K * mC + K) h0 hbase hword hallowed ha1R hMK h1B (by omega) (by omega) harg1BaseK hlenB
    hidxB hidxV

lemma exprBoundedIn_transArg2EParam_of_word
    (M K B a2Reg arg2Base mC : ℕ) (col2 : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (h4 : σ (M + lvJ2) ≤ K) (h5 : σ (M + lvJ3) ≤ K)
    (hbase : σ (M + a2Reg) = arg2Base) (hword : WordAt σ arg2Base col2)
    (hallowed : ∀ v ∈ col2, v ≤ K)
    (ha2R : a2Reg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hprod : K * mC + K + K ≤ B) (hlenB : col2.length ≤ B) (hmC : mC ≤ B)
    (harg2BaseK : arg2Base ≤ K) :
    ExprBoundedIn B σ (transArg2EParam a2Reg col2.length mC) ∧
      (transArg2EParam a2Reg col2.length mC).eval σ ≤ K := by
  obtain ⟨hidxB, hidxV⟩ := exprBoundedIn_transIdxE M K B mC σ h0 h4 h5 (by omega) hmC (by omega)
  unfold transArg2EParam
  exact exprBoundedIn_wordReadEBaseParam_of_word M K B a2Reg 0 arg2Base col2 σ (transIdxE mC)
    (K * mC + K) h0 hbase hword hallowed ha2R hMK h1B (by omega) (by omega) harg2BaseK hlenB
    hidxB hidxV

/-! ## A `Frozen`-changing `.seq` combinator

`transStageArgsProgParam` adds `litJ`/`tmpJ` pins mid-composition, so the
write/move blocks it feeds run under a strictly bigger `Frozen` than the
staging step's own entry — `clauseWriterBounded_seq` (`GeneratorBoundedCore`)
shares one `Frozen` across both halves and does not fit.  This is the bounded
companion to `clauseWriterIO_seq`. -/

lemma clauseWriterBounded_seq_io (p1 p2 : Program) (M Jmax wpJ K S B wid1 wid2 : ℕ)
    (Entry Mid : Store → Prop) (cs1 : List Clause)
    (hw1 : ClauseWriterIO p1 M Jmax wpJ Entry Mid cs1)
    (hwid1 : rowTableWidth (rowW cs1) cs1.length ≤ wid1)
    (hb1 : ClauseWriterBounded p1 M Jmax wpJ K S B wid1 Entry)
    (hb2 : ClauseWriterBounded p2 M Jmax wpJ K S B wid2 Mid) :
    ClauseWriterBounded (.seq p1 p2) M Jmax wpJ K S B (wid1 + wid2) Entry := by
  intro τ wp hF h0 hw hsep hslack hst ht
  obtain ⟨hF', h0', hw', _, _⟩ := hw1 τ wp hF h0 hw hsep
  obtain ⟨hpb1, hst1, ht1⟩ := hb1 τ wp hF h0 hw hsep (by omega) hst ht
  have hsep' : M + Jmax < wp + rowTableWidth (rowW cs1) cs1.length := by omega
  have hslack' : (wp + rowTableWidth (rowW cs1) cs1.length) + wid2 ≤ S := by omega
  obtain ⟨hpb2, hst2, ht2⟩ := hb2 (p1.eval τ) _ hF' h0' hw' hsep' hslack' hst1 ht1
  rw [eval_seq]
  exact ⟨⟨hpb1, hpb2⟩, hst2, ht2⟩

/-! ## Staging `litJ`/`tmpJ`

`transArg1EParam`/`transArg2EParam` bounded from register facts and the
staged table columns alone, then assigned into the scratch cells
`clauseWriterBounded_ctlAssign_scratch` wraps at width `0`. -/

lemma clauseWriterBounded_trans_stage_lit
    (M Jmax K S B a1Reg mC arg1Base : ℕ) (col1 : List ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg2Base : ℕ) (col2 : List ℕ) (pins : List (ℕ × ℕ))
    (ha1R2 : a1Reg ≤ 23) (hMB : M + 24 ≤ B) (hKS : K ≤ S)
    (ha1mem : (a1Reg, arg1Base) ∈ pins) (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlen1B : col1.length ≤ B) (hallowed1 : ∀ v ∈ col1, v ≤ K) (harg1BaseK : arg1Base ≤ K) :
    ClauseWriterBounded (ctlAssign litJ (transArg1EParam a1Reg col1.length mC))
      M Jmax wpJ K S B 0
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) := by
  refine clauseWriterBounded_ctlAssign_scratch M Jmax K S B litJ
    (transArg1EParam a1Reg col1.length mC)
    (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
    (by unfold litJ; omega) (by unfold litJ; omega) hMB hKS ?_
  intro τ hF h0 ht hst
  have hbase : τ (M + a1Reg) = arg1Base := hF.1 (a1Reg, arg1Base) ha1mem
  exact exprBoundedIn_transArg1EParam_of_word M K B a1Reg arg1Base mC col1 τ h0
    (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
    (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
    hbase hF.2.2.1 hallowed1 ha1R2 (by omega) (by omega) hK1mC hlen1B hmCB harg1BaseK

lemma clauseWriterBounded_trans_stage_tmp
    (M Jmax K S B a2Reg mC arg2Base : ℕ) (col2 : List ℕ)
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ) (pins : List (ℕ × ℕ))
    (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B) (hKS : K ≤ S)
    (ha2mem : (a2Reg, arg2Base) ∈ pins) (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlen2B : col2.length ≤ B) (hallowed2 : ∀ v ∈ col2, v ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (ctlAssign tmpJ (transArg2EParam a2Reg col2.length mC))
      M Jmax wpJ K S B 0
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) := by
  refine clauseWriterBounded_ctlAssign_scratch M Jmax K S B tmpJ
    (transArg2EParam a2Reg col2.length mC)
    (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
    (by unfold tmpJ; omega) (by unfold tmpJ; omega) hMB hKS ?_
  intro τ hF h0 ht hst
  have hbase : τ (M + a2Reg) = arg2Base := hF.1 (a2Reg, arg2Base) ha2mem
  exact exprBoundedIn_transArg2EParam_of_word M K B a2Reg arg2Base mC col2 τ h0
    (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
    (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
    hbase hF.2.2.2 hallowed2 ha2R2 (by omega) (by omega) hK1mC hlen2B hmCB harg2BaseK

/-- `transStageArgsProgParam`, as a `ClauseWriterBounded` at width `0` — both
assignments write into a scratch cell, touching no table row. -/
lemma clauseWriterBounded_transStageArgsProgParam
    (M Jmax K S B wReg tReg kbReg a1Reg a2Reg mC T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23)
    (hMB : M + 24 ≤ B) (hKS : K ≤ S)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowed1 : ∀ v ∈ col1, v ≤ K) (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (transStageArgsProgParam a1Reg a2Reg col1.length col2.length mC)
      M Jmax wpJ K S B 0
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hpinsDef
  set av1 := col1.getD (qi * mC + ai) 0 with hav1def
  set av2 := col2.getD (qi * mC + ai) 0 with hav2def
  have hscratchLit := trans_param_bases_above_scratch M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length litJ hplace htable
    (by unfold litJ ctlJmax; omega)
  have hscratchTmp := trans_param_bases_above_scratch M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length tmpJ hplace htable
    (by unfold tmpJ ctlJmax; omega)
  have hstage1 : ClauseWriterIO (ctlAssign litJ (transArg1EParam a1Reg col1.length mC))
      M Jmax wpJ (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((litJ, av1) :: pins) kindBase colk arg1Base col1 arg2Base col2) [] := by
    refine clause_writer_io_stage_words3_value M Jmax litJ kindBase arg1Base
      arg2Base av1 colk col1 col2 pins (transArg1EParam a1Reg col1.length mC)
      (by unfold litJ; omega)
      (Nat.le_trans (by unfold litJ ctlJmax; omega) hplace.ctl_le)
      (by unfold litJ wpJ; omega) ?_ hscratchLit.1 hscratchLit.2.1 hscratchLit.2.2 ?_
    · intro q hq
      have h := trans_param_pins4_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base t p qi ai litJ hplace
        (by unfold litJ ctlJmax; omega) (by unfold lvJ0 litJ; omega)
        (by unfold lvJ1 litJ; omega) (by unfold lvJ2 litJ; omega)
        (by unfold lvJ3 litJ; omega) q hq
      exact h.2.2.1
    · intro τ hF h0
      exact trans_arg1_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 hF h0
  have hstage2 : ClauseWriterIO (ctlAssign tmpJ (transArg2EParam a2Reg col2.length mC))
      M Jmax wpJ (PinsAndWords3 M ((litJ, av1) :: pins) kindBase colk arg1Base col1 arg2Base col2)
      (PinsAndWords3 M ((tmpJ, av2) :: (litJ, av1) :: pins)
        kindBase colk arg1Base col1 arg2Base col2) [] := by
    refine clause_writer_io_stage_words3_value M Jmax tmpJ kindBase arg1Base
      arg2Base av2 colk col1 col2 ((litJ, av1) :: pins)
      (transArg2EParam a2Reg col2.length mC) (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le)
      (by unfold tmpJ wpJ; omega) ?_ hscratchTmp.1 hscratchTmp.2.1 hscratchTmp.2.2 ?_
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · unfold litJ tmpJ; omega
      · have h := trans_param_pins4_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
          kindBase arg1Base arg2Base t p qi ai tmpJ hplace
          (by unfold tmpJ ctlJmax; omega) (by unfold lvJ0 tmpJ; omega)
          (by unfold lvJ1 tmpJ; omega) (by unfold lvJ2 tmpJ; omega)
          (by unfold lvJ3 tmpJ; omega) q hq
        exact h.2.2.1
    · intro τ hF h0
      have htail := pinsAndWords3_tail M (litJ, av1) pins kindBase colk
        arg1Base col1 arg2Base col2 τ hF
      exact trans_arg2_e_param_value M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base mC t p qi ai τ colk col1 col2 htail h0
  have hb1 := clauseWriterBounded_trans_stage_lit M Jmax K S B a1Reg mC arg1Base col1
    kindBase colk arg2Base col2 pins ha1R2 hMB hKS
    (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hK1mC hmCB hlen1B hallowed1 harg1BaseK
  have hb2 := clauseWriterBounded_trans_stage_tmp M Jmax K S B a2Reg mC arg2Base col2
    kindBase colk arg1Base col1 ((litJ, av1) :: pins) ha2R2 hMB hKS
    (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
      transParamPins1, transParamPins0]) hK1mC hmCB hlen2B hallowed2 harg2BaseK
  unfold transStageArgsProgParam
  exact clauseWriterBounded_seq_io _ _ M Jmax wpJ K S B 0 0 _ _ [] hstage1
    (by simp [rowTableWidth_zero]) hb1 hb2

/-! ## The three-row block combinator

Every `transForbidBlockProgParam`/`transHaltBlockProgParam`/
`transWriteBlockProgParam`/`transMoveBlockProgParam` is three
`writeClauseProg` rows of one shape sharing an antecedent, composed by
`.seq`.  One combinator, at whichever `imply3`/`forbid3` shape, builds every
block's `ClauseWriterBounded` from three row-level ones. -/

lemma clauseWriterBounded_trans_imply3_block
    (M Jmax K S B : ℕ) (Frozen : Store → Prop)
    (aE bE cE dE1 dE2 dE3 : Expr) (av bv cv dv1 dv2 _dv3 : ℕ)
    (hcw1 : ClauseWriter (writeClauseProg wpJ (imply3Lits aE bE cE dE1)) M Jmax wpJ Frozen
      [imply3 av bv cv dv1])
    (hcw2 : ClauseWriter (writeClauseProg wpJ (imply3Lits aE bE cE dE2)) M Jmax wpJ Frozen
      [imply3 av bv cv dv2])
    (hb1 : ClauseWriterBounded (writeClauseProg wpJ (imply3Lits aE bE cE dE1))
      M Jmax wpJ K S B 10 Frozen)
    (hb2 : ClauseWriterBounded (writeClauseProg wpJ (imply3Lits aE bE cE dE2))
      M Jmax wpJ K S B 10 Frozen)
    (hb3 : ClauseWriterBounded (writeClauseProg wpJ (imply3Lits aE bE cE dE3))
      M Jmax wpJ K S B 10 Frozen) :
    ClauseWriterBounded (.seq (.seq
        (writeClauseProg wpJ (imply3Lits aE bE cE dE1))
        (writeClauseProg wpJ (imply3Lits aE bE cE dE2)))
        (writeClauseProg wpJ (imply3Lits aE bE cE dE3)))
      M Jmax wpJ K S B 30 Frozen := by
  have hw1 : rowTableWidth (rowW [imply3 av bv cv dv1]) [imply3 av bv cv dv1].length ≤ 10 := by
    rw [show ([imply3 av bv cv dv1] : List Clause).length = 1 from rfl, rowTableWidth_singleton]
    simp [imply3]
  have hw12 : rowTableWidth (rowW ([imply3 av bv cv dv1] ++ [imply3 av bv cv dv2]))
      ([imply3 av bv cv dv1] ++ [imply3 av bv cv dv2]).length ≤ 20 := by
    rw [rowTableWidth_append_total]
    have hw2 : rowTableWidth (rowW [imply3 av bv cv dv2]) [imply3 av bv cv dv2].length ≤ 10 := by
      rw [show ([imply3 av bv cv dv2] : List Clause).length = 1 from rfl, rowTableWidth_singleton]
      simp [imply3]
    omega
  refine clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B (10 + 10 + 10) 30 Frozen (by omega) ?_
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B (10 + 10) 10 Frozen _
    (clauseWriter_seq _ _ M Jmax wpJ Frozen _ _ hcw1 hcw2) hw12
    (clauseWriterBounded_seq _ _ M Jmax wpJ K S B 10 10 Frozen _ hcw1 hw1 hb1 hb2) hb3

/-- Three `forbid3Lits` rows, the shape `transForbidBlockProgParam` alone uses. -/
lemma clauseWriterBounded_trans_forbid3_block
    (M Jmax K S B : ℕ) (Frozen : Store → Prop)
    (aE bE cE : Expr) (av bv cv : ℕ)
    (hcw : ClauseWriter (writeClauseProg wpJ (forbid3Lits aE bE cE)) M Jmax wpJ Frozen
      [forbid3 av bv cv])
    (hb : ClauseWriterBounded (writeClauseProg wpJ (forbid3Lits aE bE cE))
      M Jmax wpJ K S B 8 Frozen) :
    ClauseWriterBounded (.seq (.seq
        (writeClauseProg wpJ (forbid3Lits aE bE cE))
        (writeClauseProg wpJ (forbid3Lits aE bE cE)))
        (writeClauseProg wpJ (forbid3Lits aE bE cE)))
      M Jmax wpJ K S B 24 Frozen := by
  have hw : rowTableWidth (rowW [forbid3 av bv cv]) [forbid3 av bv cv].length ≤ 8 := by
    rw [show ([forbid3 av bv cv] : List Clause).length = 1 from rfl, rowTableWidth_singleton]
    simp [forbid3]
  refine clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B (8 + 8 + 8) 24 Frozen (by omega) ?_
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B (8 + 8) 8 Frozen _
    (clauseWriter_seq _ _ M Jmax wpJ Frozen _ _ hcw hcw)
    (by rw [rowTableWidth_append_total]; omega)
    (clauseWriterBounded_seq _ _ M Jmax wpJ K S B 8 8 Frozen _ hcw hw hb hb) hb

/-! ## Antecedent and consequent values

Every block shares the same three antecedent facts (state/head/cell), read at
whichever pins the block runs under — unstaged for forbid/halt, staged with
`litJ`/`tmpJ` for write/move.  Isolating them once each avoids repeating the
five-way `simp` unfolding of `transParamPins4` at every row. -/

lemma trans_sch_value
    (M nS W mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base T
      t p qi ai : ℕ) (colk col1 col2 : List ℕ) :
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transStateEParam nS mS wReg) ((denseLayout nS W mS).state t qi) ∧
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transHeadEParam nS mS wReg) ((denseLayout nS W mS).head t p) ∧
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transCellEParam nS mS wReg) ((denseLayout nS W mS).cell t p ai) := by
  set pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hpinsDef
  refine ⟨fun τ hF h0 =>
      trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3]) h0,
    fun τ hF h0 =>
      trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0,
    fun τ hF h0 =>
      trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
        (by simp [pins, transParamPins4]) h0⟩

lemma trans_sch_staged_value
    (M nS W mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base T
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ) :
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transStateEParam nS mS wReg) ((denseLayout nS W mS).state t qi) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transHeadEParam nS mS wReg) ((denseLayout nS W mS).head t p) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transCellEParam nS mS wReg) ((denseLayout nS W mS).cell t p ai) := by
  set pins := (tmpJ, av2) :: (litJ, av1) ::
    transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai
    with hpinsDef
  refine ⟨fun τ hF h0 =>
      trans_state_e_param_value M nS W mS wReg t qi τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3]) h0,
    fun τ hF h0 =>
      trans_head_e_param_value M nS W mS wReg t p τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0,
    fun τ hF h0 =>
      trans_cell_e_param_value M nS W mS wReg t p ai τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
        (by simp [pins, transParamPins4]) h0⟩

lemma trans_halt_consequent_value
    (M nS W mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base T
      t p qi ai : ℕ) (colk col1 col2 : List ℕ) :
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transStateSameEParam nS mS wReg) ((denseLayout nS W mS).state (t + 1) qi) ∧
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transHeadSameEParam nS mS wReg) ((denseLayout nS W mS).head (t + 1) p) ∧
    FrozenExprValue
      (PinsAndWords3 M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transCellSameEParam nS mS wReg) ((denseLayout nS W mS).cell (t + 1) p ai) := by
  set pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hpinsDef
  refine ⟨fun τ hF h0 =>
      trans_state_same_e_param_value M nS W mS wReg t qi τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3]) h0,
    fun τ hF h0 =>
      trans_head_same_e_param_value M nS W mS wReg t p τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2]) h0,
    fun τ hF h0 =>
      trans_cell_same_e_param_value M nS W mS wReg t p ai τ pins hF.1
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [pins, transParamPins4, transParamPins3, transParamPins2])
        (by simp [pins, transParamPins4]) h0⟩

lemma trans_write_consequent_value
    (M nS W mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base T
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ) :
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transStateNextEParam nS mS wReg) ((denseLayout nS W mS).state (t + 1) av1) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transHeadSameEParam nS mS wReg) ((denseLayout nS W mS).head (t + 1) p) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transCellWriteEParam nS mS wReg) ((denseLayout nS W mS).cell (t + 1) p av2) := by
  set basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hbasePinsDef
  refine ⟨fun τ hF h0 =>
      trans_state_next_e_param_value M nS W mS wReg t av1 av2 τ basePins hF.1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1]) h0,
    fun τ hF h0 =>
      trans_head_same_e_param_value M nS W mS wReg t p τ basePins
        (pinsAndWords3_tail M (litJ, av1) basePins kindBase colk arg1Base col1 arg2Base col2 _
          (pinsAndWords3_tail M (tmpJ, av2) ((litJ, av1) :: basePins) kindBase colk
            arg1Base col1 arg2Base col2 _ hF)).1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2]) h0,
    fun τ hF h0 =>
      trans_cell_write_e_param_value M nS W mS wReg t p av1 av2 τ basePins hF.1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2]) h0⟩

lemma trans_move_consequent_value
    (M nS W mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base T
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ) :
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transStateNextEParam nS mS wReg) ((denseLayout nS W mS).state (t + 1) av1) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transHeadMoveEParam nS mS wReg)
        ((denseLayout nS W mS).head (t + 1) (p + av2 - (1 - av2))) ∧
    FrozenExprValue
      (PinsAndWords3 M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
        kindBase colk arg1Base col1 arg2Base col2) M
      (transCellSameEParam nS mS wReg) ((denseLayout nS W mS).cell (t + 1) p ai) := by
  set basePins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hbasePinsDef
  refine ⟨fun τ hF h0 =>
      trans_state_next_e_param_value M nS W mS wReg t av1 av2 τ basePins hF.1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1]) h0,
    fun τ hF h0 =>
      trans_head_move_e_param_value M nS W mS wReg t p av1 av2
        (p + av2 - (1 - av2)) τ basePins hF.1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2]) h0 rfl,
    fun τ hF h0 =>
      trans_cell_same_e_param_value M nS W mS wReg t p ai τ basePins
        (pinsAndWords3_tail M (litJ, av1) basePins kindBase colk arg1Base col1 arg2Base col2 _
          (pinsAndWords3_tail M (tmpJ, av2) ((litJ, av1) :: basePins) kindBase colk
            arg1Base col1 arg2Base col2 _ hF)).1
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2,
          transParamPins1, transParamPins0])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2, transParamPins1])
        (by simp [basePins, transParamPins4, transParamPins3, transParamPins2])
        (by simp [basePins, transParamPins4]) h0⟩

/-! ## One row's `ClauseWriter`/`ClauseWriterBounded`

`trans_imply3_row_writer_param` specializes `imply3_writer_words3_param` to
the antecedent (state/head/cell) fixed and only the fourth expression
varying — the same shape every consequent row shares.
`clauseWriterBounded_trans_imply3_row` is its bounded companion, from a
`LitsBounded` fact `GeneratorBoundedTrans` already proves. -/

lemma trans_imply3_row_writer_param
    (M Jmax nS mS wReg tReg kbReg a1Reg a2Reg kindBase arg1Base arg2Base : ℕ)
    (colk col1 col2 : List ℕ) (pins : List (ℕ × ℕ))
    (dE : Expr) (av bv cv dv : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hfd : ParamExprFrame M Jmax wpJ dE)
    (hva : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M
        (transStateEParam nS mS wReg) av)
    (hvb : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M
        (transHeadEParam nS mS wReg) bv)
    (hvc : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M
        (transCellEParam nS mS wReg) cv)
    (hvd : FrozenExprValue
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) M dE dv) :
    ClauseWriter (writeClauseProg wpJ (imply3Lits
        (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
        (transCellEParam nS mS wReg) dE)) M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [imply3 av bv cv dv] :=
  imply3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 pins
    (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
    (transCellEParam nS mS wReg) dE av bv cv dv
    hplace htable hpin
    (trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    (trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    (trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hfd hva hvb hvc hvd

lemma clauseWriterBounded_trans_imply3_row
    (M Jmax K S B : ℕ) (aE bE cE dE : Expr) (Frozen : Store → Prop)
    (hJ : 24 ≤ Jmax) (hMB : M + 24 ≤ B) (hSB : S ≤ B) (h4S : 4 ≤ S)
    (hlits : LitsBounded K S B M (imply3Lits aE bE cE dE)) :
    ClauseWriterBounded (writeClauseProg wpJ (imply3Lits aE bE cE dE))
      M Jmax wpJ K S B 10 Frozen :=
  clauseWriterBounded_writeClauseProg M Jmax K S B _ Frozen hJ hMB hSB
    (by simp [imply3Lits]; omega) hlits

/-! ## The four blocks -/

/-- `transForbidBlockProgParam`'s `ClauseWriterBounded`. -/
lemma clauseWriterBounded_transForbidBlockProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h3S : 3 ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ClauseWriterBounded (transForbidBlockProgParam nS mS wReg) M Jmax wpJ K S B 24
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hpinsDef
  obtain ⟨hva, hvb, hvc⟩ := trans_sch_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai colk col1 col2
  have hcw : ClauseWriter (writeClauseProg wpJ (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg))) M Jmax wpJ
      (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2)
      [forbid3 ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
        ((denseLayout nS W mS).cell t p ai)] := by
    apply forbid3_writer_words3_param M Jmax wReg tReg kbReg a1Reg a2Reg
      kindBase arg1Base arg2Base colk col1 col2 pins
      (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
      (transCellEParam nS mS wReg) _ _ _ hplace htable
    · exact trans_param_leaf_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base t p qi ai hplace
    · exact trans_state_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
    · exact trans_head_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
    · exact trans_cell_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace
    · exact hva
    · exact hvb
    · exact hvc
  have hb := clauseWriterBounded_writeClauseProg M Jmax K S B
    (forbid3Lits (transStateEParam nS mS wReg) (transHeadEParam nS mS wReg)
      (transCellEParam nS mS wReg))
    (PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2) hJ hMB hSB
    (by simp [forbid3Lits]; omega)
    (litsBounded_trans_forbid K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  unfold transForbidBlockProgParam
  exact clauseWriterBounded_trans_forbid3_block M Jmax K S B _ _ _ _ _ _ _ hcw hb

/-- `transHaltBlockProgParam`'s `ClauseWriterBounded`. -/
lemma clauseWriterBounded_transHaltBlockProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ClauseWriterBounded (transHaltBlockProgParam nS mS wReg) M Jmax wpJ K S B 30
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set Frozen := PinsAndWords3 M
    (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
    kindBase colk arg1Base col1 arg2Base col2 with hFrozenDef
  obtain ⟨hva, hvb, hvc⟩ := trans_sch_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai colk col1 col2
  obtain ⟨hv1, hv2, hv3⟩ := trans_halt_consequent_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai colk col1 col2
  have hpin := trans_param_leaf_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai hplace
  have hcw1 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transStateSameEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_state_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv1
  have hcw2 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transHeadSameEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_head_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv2
  have hb1 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transStateSameEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_state_same K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb2 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transHeadSameEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_head_same K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb3 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transCellSameEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_cell_same K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  unfold transHaltBlockProgParam
  exact clauseWriterBounded_trans_imply3_block M Jmax K S B Frozen _ _ _ _ _ _
    ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
    ((denseLayout nS W mS).cell t p ai) _ _ ((denseLayout nS W mS).cell (t + 1) p ai)
    hcw1 hcw2 hb1 hb2 hb3

/-- `transWriteBlockProgParam`'s `ClauseWriterBounded`, at the staged pins
`(tmpJ, av2) :: (litJ, av1) :: transParamPins4 ...`. -/
lemma clauseWriterBounded_transWriteBlockProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ClauseWriterBounded (transWriteBlockProgParam nS mS wReg) M Jmax wpJ K S B 30
      (TransFrozen M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
            t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set Frozen := PinsAndWords3 M
    ((tmpJ, av2) :: (litJ, av1) ::
      transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
    kindBase colk arg1Base col1 arg2Base col2 with hFrozenDef
  obtain ⟨hva, hvb, hvc⟩ := trans_sch_staged_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai av1 av2 colk col1 col2
  obtain ⟨hv1, hv2, hv3⟩ := trans_write_consequent_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai av1 av2 colk col1 col2
  have hpin := trans_param_staged_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai av1 av2 hplace
  have hcw1 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transStateNextEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_state_next_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv1
  have hcw2 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transHeadSameEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_head_same_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv2
  have hb1 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transStateNextEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_state_next K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb2 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transHeadSameEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_head_same K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb3 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transCellWriteEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_cell_write K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  unfold transWriteBlockProgParam
  exact clauseWriterBounded_trans_imply3_block M Jmax K S B Frozen _ _ _ _ _ _
    ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
    ((denseLayout nS W mS).cell t p ai) _ _ ((denseLayout nS W mS).cell (t + 1) p av2)
    hcw1 hcw2 hb1 hb2 hb3

/-- `transMoveBlockProgParam`'s `ClauseWriterBounded`, at the staged pins. -/
lemma clauseWriterBounded_transMoveBlockProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai av1 av2 : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    ClauseWriterBounded (transMoveBlockProgParam nS mS wReg) M Jmax wpJ K S B 30
      (TransFrozen M
        ((tmpJ, av2) :: (litJ, av1) ::
          transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
            t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set Frozen := PinsAndWords3 M
    ((tmpJ, av2) :: (litJ, av1) ::
      transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
    kindBase colk arg1Base col1 arg2Base col2 with hFrozenDef
  obtain ⟨hva, hvb, hvc⟩ := trans_sch_staged_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai av1 av2 colk col1 col2
  obtain ⟨hv1, hv2, hv3⟩ := trans_move_consequent_value M nS W mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base T t p qi ai av1 av2 colk col1 col2
  have hpin := trans_param_staged_pins_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai av1 av2 hplace
  have hcw1 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transStateNextEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_state_next_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv1
  have hcw2 := trans_imply3_row_writer_param M Jmax nS mS wReg tReg kbReg a1Reg a2Reg
    kindBase arg1Base arg2Base colk col1 col2 _ (transHeadMoveEParam nS mS wReg)
    _ _ _ _ hplace htable hpin
    (trans_head_move_e_param_frame M Jmax nS mS wReg tReg kbReg a1Reg a2Reg hplace)
    hva hvb hvc hv2
  have hb1 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transStateNextEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_state_next K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb2 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transHeadMoveEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_head_move K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  have hb3 := clauseWriterBounded_trans_imply3_row M Jmax K S B (transStateEParam nS mS wReg)
    (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg) (transCellSameEParam nS mS wReg)
    Frozen hJ hMB hSB h4S
    (litsBounded_trans_cell_same K S B M nS mS wReg hK1 hwR hwR2 hMB henvB henvS hnS hmS)
  unfold transMoveBlockProgParam
  exact clauseWriterBounded_trans_imply3_block M Jmax K S B Frozen _ _ _ _ _ _
    ((denseLayout nS W mS).state t qi) ((denseLayout nS W mS).head t p)
    ((denseLayout nS W mS).cell t p ai) _ _ ((denseLayout nS W mS).cell (t + 1) p ai)
    hcw1 hcw2 hb1 hb2 hb3

/-! ## The two accepting leaves

`transAcceptWriteProgParam`/`transAcceptMoveProgParam` are
`transStageArgsProgParam` followed by the write/move block, at the staged
`Frozen` the stage step's own `ClauseWriterIO`
(`trans_stage_args_io_param`) already establishes. -/

/-- `transAcceptWriteProgParam`'s `ClauseWriterBounded`. -/
lemma clauseWriterBounded_transAcceptWriteProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg mC T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowed1 : ∀ v ∈ col1, v ≤ K) (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (transAcceptWriteProgParam nS mS mC wReg a1Reg a2Reg
        col1.length col2.length)
      M Jmax wpJ K S B 30
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  have hio := trans_stage_args_io_param M Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base mC t p qi ai colk col1 col2 hplace htable
  have hb1 := clauseWriterBounded_transStageArgsProgParam (W := W) M Jmax K S B wReg tReg kbReg
    a1Reg a2Reg mC T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
    ha1R2 ha2R2 hMB hKS hK1mC hmCB hlen1B hlen2B hallowed1 hallowed2 harg1BaseK harg2BaseK
  have hb2 := clauseWriterBounded_transWriteBlockProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg
    a2Reg T kindBase arg1Base arg2Base t p qi ai
    (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) colk col1 col2 hplace htable
    hJ hK1 hwR hwR2 hMB hSB h4S henvB henvS hnS hmS
  unfold transAcceptWriteProgParam
  exact clauseWriterBounded_seq_io _ _ M Jmax wpJ K S B 0 30 _ _ [] hio
    (by simp [rowTableWidth_zero]) hb1 hb2

/-- `transAcceptMoveProgParam`'s `ClauseWriterBounded`. -/
lemma clauseWriterBounded_transAcceptMoveProgParam
    (M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg mC T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowed1 : ∀ v ∈ col1, v ≤ K) (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K) :
    ClauseWriterBounded (transAcceptMoveProgParam nS mS mC wReg a1Reg a2Reg
        col1.length col2.length)
      M Jmax wpJ K S B 30
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  have hio := trans_stage_args_io_param M Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base mC t p qi ai colk col1 col2 hplace htable
  have hb1 := clauseWriterBounded_transStageArgsProgParam (W := W) M Jmax K S B wReg tReg kbReg
    a1Reg a2Reg mC T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable
    ha1R2 ha2R2 hMB hKS hK1mC hmCB hlen1B hlen2B hallowed1 hallowed2 harg1BaseK harg2BaseK
  have hb2 := clauseWriterBounded_transMoveBlockProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg
    a2Reg T kindBase arg1Base arg2Base t p qi ai
    (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0) colk col1 col2 hplace htable
    hJ hK1 hwR hwR2 hMB hSB h4S henvB henvS hnS hmS
  unfold transAcceptMoveProgParam
  exact clauseWriterBounded_seq_io _ _ M Jmax wpJ K S B 0 30 _ _ [] hio
    (by simp [rowTableWidth_zero]) hb1 hb2

/-! ## The `.ifNZ` guard bounds

Each guard reads a table column (or, for `moveOkEParam`, the window width and
head position too) at the trans family's own pins — `ExprBoundedIn` from the
word-based lemmas above, widened to the `.lt`/`.eq`/`moveOkEParam` wrapper. -/

/-- Every `ExprBoundedIn` fact `transLeafProgParam`'s guards need, packaged as
one obligation per guard.  `hpK`/`hWK` are what the outer `p`/`W` loops supply
from their own trip counts (`p < W ≤ K`). -/
lemma trans_leaf_cond_bounded
    (M _Jmax K S B _nS _mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai W : ℕ) (colk col1 col2 : List ℕ)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23)
    (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlenkB : colk.length ≤ B) (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowedk : ∀ v ∈ colk, v ≤ K) (hallowed1 : ∀ v ∈ col1, v ≤ K)
    (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hpK : p ≤ K) (hWK : W ≤ K) (hnCB : nC ≤ B) :
    (∀ τ : Store, TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ (.eq (transKindEParam kbReg colk.length mC) (.const 0))) ∧
    (∀ τ : Store, TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ (.eq (transKindEParam kbReg colk.length mC) (.const 1))) ∧
    (∀ τ : Store, TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ (.lt (transArg1EParam a1Reg col1.length mC) (.const nC))) ∧
    (∀ τ : Store, TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2 τ →
      τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ (moveOkEParam wReg (ctlCell lvJ1)
        (transArg2EParam a2Reg col2.length mC))) := by
  set pins := transParamPins4 wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi ai with hpinsDef
  have hkbmem : (kbReg, kindBase) ∈ pins := by
    simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1,
      transParamPins0]
  have ha1mem : (a1Reg, arg1Base) ∈ pins := by
    simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1,
      transParamPins0]
  have ha2mem : (a2Reg, arg2Base) ∈ pins := by
    simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1,
      transParamPins0]
  have hpmem : (lvJ1, p) ∈ pins := by
    simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1]
  have hwmem : (wReg, W) ∈ pins := by
    simp [pins, transParamPins4, transParamPins3, transParamPins2, transParamPins1,
      transParamPins0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ hF h0 ht hst
    have hbase : τ (M + kbReg) = kindBase := hF.1 (kbReg, kindBase) hkbmem
    refine ⟨(exprBoundedIn_transKindEParam_of_word M K B kbReg kindBase mC colk τ h0
      (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
      (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
      hbase hF.2.1 hallowedk hkbR2 (by omega) (by omega) hK1mC hlenkB hmCB hkindBaseK).1, ?_⟩
    simp only [ExprBoundedIn]; omega
  · intro τ hF h0 ht hst
    have hbase : τ (M + kbReg) = kindBase := hF.1 (kbReg, kindBase) hkbmem
    refine ⟨(exprBoundedIn_transKindEParam_of_word M K B kbReg kindBase mC colk τ h0
      (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
      (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
      hbase hF.2.1 hallowedk hkbR2 (by omega) (by omega) hK1mC hlenkB hmCB hkindBaseK).1, ?_⟩
    simp only [ExprBoundedIn]; omega
  · intro τ hF h0 ht hst
    have hbase : τ (M + a1Reg) = arg1Base := hF.1 (a1Reg, arg1Base) ha1mem
    refine ⟨(exprBoundedIn_transArg1EParam_of_word M K B a1Reg arg1Base mC col1 τ h0
      (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
      (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
      hbase hF.2.2.1 hallowed1 ha1R2 (by omega) (by omega) hK1mC hlen1B hmCB harg1BaseK).1, ?_⟩
    simp only [ExprBoundedIn]; omega
  · intro τ hF h0 ht hst
    have hbase : τ (M + a2Reg) = arg2Base := hF.1 (a2Reg, arg2Base) ha2mem
    have hpv : τ (M + lvJ1) = p := hF.1 (lvJ1, p) hpmem
    have hwv : τ (M + wReg) = W := hF.1 (wReg, W) hwmem
    obtain ⟨hargB, hargV⟩ := exprBoundedIn_transArg2EParam_of_word M K B a2Reg arg2Base mC col2 τ
      h0 (ht lvJ2 (by unfold lvJ2; omega) (by unfold lvJ2; omega))
      (ht lvJ3 (by unfold lvJ3; omega) (by unfold lvJ3; omega))
      hbase hF.2.2.2 hallowed2 ha2R2 (by omega) (by omega) hK1mC hlen2B hmCB harg2BaseK
    have h1 := ht lvJ1 (by unfold lvJ1; omega) (by unfold lvJ1; omega)
    have hw1 := ht wReg hwR (by omega)
    have hpB : ExprBoundedIn B τ (ctlCell lvJ1) := by
      simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]
      unfold lvJ1; omega
    have hpBv : (ctlCell lvJ1).eval τ + 1 ≤ B := by
      simp only [ctlCell, ctlAddr, Expr.eval, h0, hpv]; omega
    have hwB : ExprBoundedIn B τ (ctlCell wReg) := by
      simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0]; omega
    have hwBv : (ctlCell wReg).eval τ ≤ B := by
      simp only [ctlCell, ctlAddr, Expr.eval, h0, hwv]; omega
    exact exprBoundedIn_moveOkEParam B wReg τ (ctlCell lvJ1) (transArg2EParam a2Reg col2.length mC)
      (by omega) hpB hargB hpBv (by omega) hwB hwBv

/-! ## The leaf

`transLeafProgParam` is a four-deep `.ifNZ` tree: two successive `kind` tests
(0, then 1), followed by `arg1 < nC` and, on the move branch, `moveOkEParam`.
It selects among the four blocks.  `clauseWriterBounded_ifNZ` needs both arms at the same
width, so `transForbidBlockProgParam`'s own `24` is widened to `30` to match
the three accepting blocks it sits beside. -/

/-- `transLeafProgParam`'s `ClauseWriterBounded`, at width `30` — the widest
of its four blocks (`clauseWriterBounded_transForbidBlockProgParam`'s own `24`
widened to match). -/
lemma clauseWriterBounded_trans_leaf
    (M Jmax K S B nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi ai : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B)
    (hlenkB : colk.length ≤ B) (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowedk : ∀ v ∈ colk, v ≤ K) (hallowed1 : ∀ v ∈ col1, v ≤ K)
    (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : nC ≤ B) (hpK : p ≤ K) (hWK : W ≤ K) :
    ClauseWriterBounded (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
        colk.length col1.length col2.length)
      M Jmax wpJ K S B 30
      (TransFrozen M
        (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi ai) kindBase colk arg1Base col1 arg2Base col2) := by
  set Frozen := TransFrozen M
    (transParamPins4 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi ai)
    kindBase colk arg1Base col1 arg2Base col2 with hFrozenDef
  obtain ⟨hcondKind, hcondKind1, hcondArg1, hcondMove⟩ := trans_leaf_cond_bounded
    M Jmax K S B nS mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai W
    colk col1 col2 hwR hwR2 hkbR2 ha1R2 ha2R2 hMB hK1mC hmCB hlenkB hlen1B hlen2B
    hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK harg2BaseK hpK hWK hnCB
  have hforbid30 : ClauseWriterBounded (transForbidBlockProgParam nS mS wReg) M Jmax wpJ K S B 30
      Frozen := clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B 24 30 Frozen (by omega)
    (clauseWriterBounded_transForbidBlockProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg a2Reg T
      kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable hJ hK1 hwR hwR2 hMB hSB
      h3S henvB henvS hnS hmS)
  have hhalt := clauseWriterBounded_transHaltBlockProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg
    a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable hJ hK1 hwR hwR2 hMB
    hSB h4S henvB henvS hnS hmS
  have hwrite := clauseWriterBounded_transAcceptWriteProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg
    a2Reg mC T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable hJ hK1 hwR hwR2
    ha1R2 ha2R2 hMB hSB h4S hKS henvB henvS hnS hmS hK1mC hmCB hlen1B hlen2B hallowed1 hallowed2
    harg1BaseK harg2BaseK
  have hmove := clauseWriterBounded_transAcceptMoveProgParam M Jmax K S B nS W mS wReg tReg kbReg a1Reg
    a2Reg mC T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable hJ hK1 hwR hwR2
    ha1R2 ha2R2 hMB hSB h4S hKS henvB henvS hnS hmS hK1mC hmCB hlen1B hlen2B hallowed1 hallowed2
    harg1BaseK harg2BaseK
  unfold transLeafProgParam
  refine clauseWriterBounded_ifNZ _ _ _ M Jmax wpJ K S B 30 Frozen hcondKind hhalt ?_
  refine clauseWriterBounded_ifNZ _ _ _ M Jmax wpJ K S B 30 Frozen hcondKind1 ?_ ?_
  · exact clauseWriterBounded_ifNZ _ _ _ M Jmax wpJ K S B 30 Frozen hcondArg1 hwrite hforbid30
  · refine clauseWriterBounded_ifNZ _ _ _ M Jmax wpJ K S B 30 Frozen hcondArg1 ?_ hforbid30
    exact clauseWriterBounded_ifNZ _ _ _ M Jmax wpJ K S B 30 Frozen hcondMove hmove hforbid30

/-! ## The four range loops

The trans family closes over `ai`/`qi`/`p`/`t`, in that order, each level a
`loopProg` whose body is the previous level then a counter bump — the same
`clauseLoopBodyBoundedUpTo_of_clauseWriterBounded`/`clauseWriterBounded_loopProg_up_to`
composition `GeneratorBoundedPersist` uses, but at `PinsAndWords3` instead of
`PinsHold` (the trans family's own `Frozen`). -/

/-- `PinsAndWords3` companion to `clauseLoopBodyBoundedUpTo_of_clauseWriterBounded`:
a writer bounded for every counter value below the trip count, followed by
that counter's own bump, is an UpTo-bounded loop body over the outer pins
and staged words alone. -/
lemma clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_words3 (prog : Program)
    (M Jmax wpJ iJ K S B n wid : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (cs : ℕ → List Clause)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B) (hKS : K ≤ S) (hKB : K ≤ B) (hnK : n ≤ K)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ
      (PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2) (cs i))
    (hb : ∀ i, ClauseWriterBounded prog M Jmax wpJ K S B wid
      (PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2)) :
    ClauseLoopBodyBoundedUpTo (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ K S B n wid (PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2) := by
  intro τ i wp hF h0 hi hin hwp hsep hslack hst ht
  have hpins : PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2 τ :=
    pinsAndWords3_cons M (iJ, i) pins basek xsk base1 xs1 base2 xs2 τ hi hF
  obtain ⟨hpb1, hst1, ht1⟩ := hb i τ wp hpins h0 hwp hsep hslack hst ht
  obtain ⟨hF1, h01, _, _, _⟩ := hw i τ wp hpins h0 hwp hsep
  have hi' : prog.eval τ (M + iJ) = i := pinsHold_head M (iJ, i) pins (prog.eval τ) hF1.1
  have hb1 : prog.eval τ (M + iJ) + 1 ≤ K := by omega
  obtain ⟨_, gt, gs⟩ := ctlAssign_bump_preserves K S M iJ 1 _ h01 hiJ hiJ2 ht1 hst1 hb1 hKS
  rw [eval_seq]
  exact ⟨⟨hpb1, programBoundedIn_ctlAssign_bump B M _ iJ 1 _ h01 (by omega) rfl (by omega)⟩,
    gs, gt⟩

/-- Any three fixed-shape (`≤ 4` literals each) clauses have table width `≤
30` — the shape every `natTransClausesTriple` branch shares. -/
lemma rowTableWidth_three_clauses_le_30 (c1 c2 c3 : Clause)
    (h1 : c1.lits.length ≤ 4) (h2 : c2.lits.length ≤ 4) (h3 : c3.lits.length ≤ 4) :
    rowTableWidth (rowW [c1, c2, c3]) [c1, c2, c3].length ≤ 30 := by
  have := rowTableWidth_le_count_mul (rowW [c1, c2, c3]) 3 4
    (fun i hi => by interval_cases i <;> simp [rowW] <;> omega)
  simpa using this

/-- `natTransClausesTriple`'s own width, uniformly `≤ 30` across all six
branches (`imply3`/`forbid3`, three rows each). -/
lemma natTransClausesTriple_width_le_30 (v : ExecVarLayout) (n W t p qi ai k a1 a2 : ℕ) :
    rowTableWidth (rowW (natTransClausesTriple v n W t p qi ai k a1 a2))
      (natTransClausesTriple v n W t p qi ai k a1 a2).length ≤ 30 := by
  unfold natTransClausesTriple
  split <;> [skip; split <;> [split; split <;> [split; skip]]] <;>
    exact rowTableWidth_three_clauses_le_30 _ _ _ (by simp [imply3, forbid3])
      (by simp [imply3, forbid3]) (by simp [imply3, forbid3])

/-- The `ai` loop's `ClauseWriterBounded`: `mC` iterations of the leaf, each
of width `30`. -/
lemma clauseWriterBounded_trans_ai_loop
    (M Jmax K S B nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p qi : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B) (hmCK : mC ≤ K)
    (hlenkB : colk.length ≤ B) (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowedk : ∀ v ∈ colk, v ≤ K) (hallowed1 : ∀ v ∈ col1, v ≤ K)
    (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : nC ≤ B) (hpK : p ≤ K) (hWK : W ≤ K) :
    ClauseWriterBounded (loopProg lvJ3 (.const mC)
        (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
            colk.length col1.length col2.length)
          (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
      M Jmax wpJ K S B (mC * 30)
      (TransFrozen M
        (transParamPins3 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p qi) kindBase colk arg1Base col1 arg2Base col2) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins3_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p qi lvJ3 hplace
    (by unfold lvJ3 ctlJmax; omega) (by unfold lvJ0 lvJ3; omega)
    (by unfold lvJ1 lvJ3; omega) (by unfold lvJ2 lvJ3; omega)
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ3 mC 30 (.const mC) _
    (TransFrozen M
      (transParamPins3 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi)
      kindBase colk arg1Base col1 arg2Base col2)
    (fun ai => natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
      (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0))
    (by unfold lvJ3; omega) (by unfold lvJ3; omega) hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ3 (.const 0)).eval τ = writeReg τ (M + lvJ3) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWords3_writeReg_loop M
        (transParamPins3 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi)
        kindBase colk arg1Base col1 arg2Base col2 lvJ3 0 τ hF (le_refl lvJ3)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2)
    (fun ai _ => natTransClausesTriple_width_le_30 (denseLayout nS W mS) nC W t p qi ai
      (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0))
    (clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ3 _ _
      kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ3; omega)
      (Nat.le_trans (by unfold lvJ3 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ3 wpJ; omega) (le_refl lvJ3) hpin hbk hb1 hb2
      (fun ai => trans_leaf_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_words3 _ M Jmax wpJ lvJ3 K S B mC 30
      (transParamPins3 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p qi)
      kindBase colk arg1Base col1 arg2Base col2 _
      (by unfold lvJ3; omega) (by unfold lvJ3; omega) hMB hKS (by omega) hmCK
      (fun ai => trans_leaf_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable)
      (fun ai => clauseWriterBounded_trans_leaf M Jmax K S B nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi ai colk col1 col2 hplace htable hJ hK1
        hwR hwR2 hkbR2 ha1R2 ha2R2 hMB hSB h4S h3S hKS henvB henvS hnS hmS hK1mC hmCB hlenkB
        hlen1B hlen2B hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK harg2BaseK hnCB hpK
        hWK))
    (fun τ hF h0 => by simp only [ExprBoundedIn]; omega)
    (fun τ hF h0 => by simp only [Expr.eval])

/-- The `qi` loop's `ClauseWriterBounded`: `nC` iterations of the `ai` loop,
each of width `mC * 30`. -/
lemma clauseWriterBounded_trans_qi_loop
    (M Jmax K S B nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t p : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B) (hmCK : mC ≤ K) (hnCK : nC ≤ K)
    (hlenkB : colk.length ≤ B) (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowedk : ∀ v ∈ colk, v ≤ K) (hallowed1 : ∀ v ∈ col1, v ≤ K)
    (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : nC ≤ B) (hpK : p ≤ K) (hWK : W ≤ K) :
    ClauseWriterBounded (loopProg lvJ2 (.const nC)
        (.seq (loopProg lvJ3 (.const mC)
            (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
                colk.length col1.length col2.length)
              (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
          (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
      M Jmax wpJ K S B (nC * (mC * 30))
      (TransFrozen M
        (transParamPins2 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base
          t p) kindBase colk arg1Base col1 arg2Base col2) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins2_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t p lvJ2 hplace
    (by unfold lvJ2 ctlJmax; omega) (by unfold lvJ0 lvJ2; omega)
    (by unfold lvJ1 lvJ2; omega)
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ2 nC (mC * 30) (.const nC) _
    (TransFrozen M
      (transParamPins2 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p)
      kindBase colk arg1Base col1 arg2Base col2)
    (fun qi => (List.range mC).flatMap fun ai =>
      natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
        (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0))
    (by unfold lvJ2; omega) (by unfold lvJ2; omega) hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ2 (.const 0)).eval τ = writeReg τ (M + lvJ2) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWords3_writeReg_loop M
        (transParamPins2 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p)
        kindBase colk arg1Base col1 arg2Base col2 lvJ2 0 τ hF (by unfold lvJ2 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2)
    (fun qi _ =>
      rowTableWidth_flatMap_range_le
        (fun ai => natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)) 30 mC
        (fun i _ => natTransClausesTriple_width_le_30 (denseLayout nS W mS) nC W t p qi i
          (colk.getD (qi * mC + i) 0) (col1.getD (qi * mC + i) 0) (col2.getD (qi * mC + i) 0)))
    (clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ2 _ _
      kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ2; omega)
      (Nat.le_trans (by unfold lvJ2 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ2 wpJ; omega) (by unfold lvJ2 lvJ3; omega) hpin
      hbk hb1 hb2
      (fun qi => trans_ai_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi colk col1 col2 hplace htable))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_words3 _ M Jmax wpJ lvJ2 K S B nC (mC * 30)
      (transParamPins2 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t p)
      kindBase colk arg1Base col1 arg2Base col2 _
      (by unfold lvJ2; omega) (by unfold lvJ2; omega) hMB hKS (by omega) hnCK
      (fun qi => trans_ai_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi colk col1 col2 hplace htable)
      (fun qi => clauseWriterBounded_trans_ai_loop M Jmax K S B nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p qi colk col1 col2 hplace htable hJ hK1
        hwR hwR2 hkbR2 ha1R2 ha2R2 hMB hSB h4S h3S hKB hKS henvB henvS hnS hmS hK1mC hmCB hmCK
        hlenkB hlen1B hlen2B hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK harg2BaseK
        hnCB hpK hWK))
    (fun τ hF h0 => by simp only [ExprBoundedIn]; omega)
    (fun τ hF h0 => by simp only [Expr.eval])

/-- `PinsAndWords3` companion to `clauseWriterBounded_of_le_or_vacuous`: a
`ClauseWriterBounded` fact needed only when the pinned counter is inside the
tight envelope extends to every counter value for free, since outside it
`TightCells` contradicts the pin. -/
lemma clauseWriterBounded_of_le_or_vacuous_words3 (prog : Program)
    (M Jmax wpJ K S B wid iJ i : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (hreal : i ≤ K → ClauseWriterBounded prog M Jmax wpJ K S B wid
      (PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2)) :
    ClauseWriterBounded prog M Jmax wpJ K S B wid
      (PinsAndWords3 M ((iJ, i) :: pins) basek xsk base1 xs1 base2 xs2) := by
  by_cases hik : i ≤ K
  · exact hreal hik
  · intro τ wp hF h0 hw hsep hslack hst ht
    have hi' : τ (M + iJ) = i := pinsHold_head M (iJ, i) pins τ hF.1
    have := ht iJ hiJ hiJ2
    omega

/-- The `p` loop's `ClauseWriterBounded`: `W` iterations of the `qi` loop,
each of width `nC * (mC * 30)`.  Any `p ≥ W` is vacuous once `W ≤ K` — the
same `clauseWriterBounded_of_le_or_vacuous` device persist's own `t`-level
uses — so no separate `hpK` hypothesis is needed here, unlike the leaf
levels below it. -/
lemma clauseWriterBounded_trans_p_loop
    (M Jmax K S B nS W mS nC mC wReg tReg kbReg a1Reg a2Reg T kindBase arg1Base arg2Base
      t : ℕ) (colk col1 col2 : List ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase colk.length
      arg1Base col1.length arg2Base col2.length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23)
    (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B) (hmCK : mC ≤ K) (hnCK : nC ≤ K)
    (hlenkB : colk.length ≤ B) (hlen1B : col1.length ≤ B) (hlen2B : col2.length ≤ B)
    (hallowedk : ∀ v ∈ colk, v ≤ K) (hallowed1 : ∀ v ∈ col1, v ≤ K)
    (hallowed2 : ∀ v ∈ col2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : nC ≤ B) (hWK : W ≤ K) :
    ClauseWriterBounded (loopProg lvJ1 (ctlCell wReg)
        (.seq (loopProg lvJ2 (.const nC)
            (.seq (loopProg lvJ3 (.const mC)
                (.seq (transLeafProgParam nS mS nC mC wReg kbReg a1Reg a2Reg
                    colk.length col1.length col2.length)
                  (ctlAssign lvJ3 (.add (ctlCell lvJ3) (.const 1)))))
              (ctlAssign lvJ2 (.add (ctlCell lvJ2) (.const 1)))))
          (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1)))))
      M Jmax wpJ K S B (W * (nC * (mC * 30)))
      (TransFrozen M
        (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
        kindBase colk arg1Base col1 arg2Base col2) := by
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base colk.length col1.length col2.length hplace htable
  have hpin := trans_param_pins1_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base t lvJ1 hplace
    (by unfold lvJ1 ctlJmax; omega) (by unfold lvJ0 lvJ1; omega)
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ1 W (nC * (mC * 30)) (ctlCell wReg) _
    (TransFrozen M
      (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
      kindBase colk arg1Base col1 arg2Base col2)
    (fun p => (List.range nC).flatMap fun qi =>
      (List.range mC).flatMap fun ai =>
        natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0) (col2.getD (qi * mC + ai) 0))
    (by unfold lvJ1; omega) (by unfold lvJ1; omega) hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ1 (.const 0)).eval τ = writeReg τ (M + lvJ1) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWords3_writeReg_loop M
        (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
        kindBase colk arg1Base col1 arg2Base col2 lvJ1 0 τ hF (by unfold lvJ1 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2)
    (fun p _ =>
      rowTableWidth_flatMap_range_le
        (fun qi => (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)) (mC * 30) nC
        (fun qi _ =>
          rowTableWidth_flatMap_range_le
            (fun ai => natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0)) 30 mC
            (fun ai _ => natTransClausesTriple_width_le_30 (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0))))
    (clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ1 _ _
      kindBase colk arg1Base col1 arg2Base col2 (by unfold lvJ1; omega)
      (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega) hpin
      hbk hb1 hb2
      (fun p => trans_qi_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p colk col1 col2 hplace htable))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_words3 _ M Jmax wpJ lvJ1 K S B W (nC * (mC * 30))
      (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
      kindBase colk arg1Base col1 arg2Base col2 _
      (by unfold lvJ1; omega) (by unfold lvJ1; omega) hMB hKS (by omega) hWK
      (fun p => trans_qi_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t p colk col1 col2 hplace htable)
      (fun p => clauseWriterBounded_of_le_or_vacuous_words3 _ M Jmax wpJ K S B (nC * (mC * 30))
        lvJ1 p _ kindBase colk arg1Base col1 arg2Base col2
        (by unfold lvJ1; omega) (by unfold lvJ1; omega)
        (fun hpK => clauseWriterBounded_trans_qi_loop M Jmax K S B nS W mS nC mC wReg tReg kbReg
          a1Reg a2Reg T kindBase arg1Base arg2Base t p colk col1 col2 hplace htable hJ hK1
          hwR hwR2 hkbR2 ha1R2 ha2R2 hMB hSB h4S h3S hKB hKS henvB henvS hnS hmS hK1mC hmCB hmCK
          hnCK hlenkB hlen1B hlen2B hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK
          harg2BaseK hnCB hpK hWK)))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ1 (.const 0)).eval τ = writeReg τ (M + lvJ1) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      have hev := pinsAndWords3_writeReg_loop M
        (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
        kindBase colk arg1Base col1 arg2Base col2 lvJ1 0 τ hF (by unfold lvJ1 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2
      have h1 : (writeReg τ (M + lvJ1) 0) 0 = M := by
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by unfold lvJ1; omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ1 (.const 0)).eval τ = writeReg τ (M + lvJ1) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      have hev := pinsAndWords3_writeReg_loop M
        (transParamPins1 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base t)
        kindBase colk arg1Base col1 arg2Base col2 lvJ1 0 τ hF (by unfold lvJ1 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2
      have h1 : (writeReg τ (M + lvJ1) 0) 0 = M := by
        rw [writeReg_diff τ (M + lvJ1) 0 0 (by unfold lvJ1; omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [transParamPins1, transParamPins0])
        hev.1 h1)

/-- Width of one `t`-level clause list: at most `W` blocks of the `p` loop's
own width `nC * (mC * 30)`. -/
lemma trans_t_width (nS W mS nC mC t : ℕ) (colk col1 col2 : List ℕ) :
    rowTableWidth (rowW ((List.range W).flatMap fun p =>
      (List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)))
      ((List.range W).flatMap fun p =>
        (List.range nC).flatMap fun qi =>
          (List.range mC).flatMap fun ai =>
            natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0)).length
      ≤ W * (nC * (mC * 30)) :=
  rowTableWidth_flatMap_range_le
    (fun p => (List.range nC).flatMap fun qi =>
      (List.range mC).flatMap fun ai =>
        natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
          (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
          (col2.getD (qi * mC + ai) 0)) (nC * (mC * 30)) W
    (fun p _ =>
      rowTableWidth_flatMap_range_le
        (fun qi => (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
            (col2.getD (qi * mC + ai) 0)) (mC * 30) nC
        (fun qi _ =>
          rowTableWidth_flatMap_range_le
            (fun ai => natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0)) 30 mC
            (fun ai _ => natTransClausesTriple_width_le_30 (denseLayout nS W mS) nC W t p qi ai
              (colk.getD (qi * mC + ai) 0) (col1.getD (qi * mC + ai) 0)
              (col2.getD (qi * mC + ai) 0))))

/-- The full trans family, as a `ClauseWriterBounded`: `T` iterations of the
`p` loop, each of width `W * (nC * (mC * 30))`. -/
lemma clauseWriterBounded_transFamilyProgParam
    (M Jmax K S B nS W mS nC mC T : ℕ) (d : TableauDescriptor)
    (kindBase arg1Base arg2Base wReg tReg kbReg a1Reg a2Reg : ℕ)
    (hplace : TransParamPlacement Jmax wReg tReg kbReg a1Reg a2Reg)
    (htable : TransParamTablePlacement M Jmax a2Reg kindBase
      (d.table.map transKind).length arg1Base (d.table.map transArg1).length
      arg2Base (d.table.map transArg2).length)
    (hJ : 24 ≤ Jmax) (hK1 : 1 ≤ K) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23)
    (hkbR2 : kbReg ≤ 23) (ha1R2 : a1Reg ≤ 23) (ha2R2 : a2Reg ≤ 23) (hMB : M + 24 ≤ B)
    (hSB : S ≤ B) (h4S : 4 ≤ S) (h3S : 3 ≤ S) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B)
    (hK1mC : K * mC + K + K ≤ B) (hmCB : mC ≤ B) (hmCK : mC ≤ K) (hnCK : nC ≤ K)
    (hlenkB : (d.table.map transKind).length ≤ B) (hlen1B : (d.table.map transArg1).length ≤ B)
    (hlen2B : (d.table.map transArg2).length ≤ B)
    (hallowedk : ∀ v ∈ d.table.map transKind, v ≤ K)
    (hallowed1 : ∀ v ∈ d.table.map transArg1, v ≤ K)
    (hallowed2 : ∀ v ∈ d.table.map transArg2, v ≤ K)
    (hkindBaseK : kindBase ≤ K) (harg1BaseK : arg1Base ≤ K) (harg2BaseK : arg2Base ≤ K)
    (hnCB : nC ≤ B) (hWK : W ≤ K) (hTK1 : T + 1 ≤ K) :
    ClauseWriterBounded (transFamilyProgParam nS mS nC mC d wReg tReg kbReg a1Reg a2Reg)
      M Jmax wpJ K S B (T * (W * (nC * (mC * 30))))
      (TransParamFrozen M wReg tReg kbReg a1Reg a2Reg W T
        kindBase arg1Base arg2Base (d.table.map transKind) (d.table.map transArg1)
        (d.table.map transArg2)) := by
  unfold transFamilyProgParam TransParamFrozen
  obtain ⟨hbk, hb1, hb2⟩ := trans_param_bases_above_ctl M Jmax a2Reg
    kindBase arg1Base arg2Base (d.table.map transKind).length
    (d.table.map transArg1).length (d.table.map transArg2).length hplace htable
  have hpin := trans_param_pins0_ok Jmax wReg tReg kbReg a1Reg a2Reg W T
    kindBase arg1Base arg2Base lvJ0 hplace (by unfold lvJ0 ctlJmax; omega)
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 T (W * (nC * (mC * 30)))
    (ctlCell tReg) _
    (TransFrozen M (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
      kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2))
    (fun t => (List.range W).flatMap fun p =>
      (List.range nC).flatMap fun qi =>
        (List.range mC).flatMap fun ai =>
          natTransClausesTriple (denseLayout nS W mS) nC W t p qi ai
            ((d.table.map transKind).getD (qi * mC + ai) 0)
            ((d.table.map transArg1).getD (qi * mC + ai) 0)
            ((d.table.map transArg2).getD (qi * mC + ai) 0))
    (by unfold lvJ0; omega) (by unfold lvJ0; omega) hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWords3_writeReg_loop M
        (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
        kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2)
    (fun t _ => trans_t_width nS W mS nC mC t
      (d.table.map transKind) (d.table.map transArg1) (d.table.map transArg2))
    (clauseLoopBody_of_writer_words3 _ M Jmax wpJ lvJ0 _ _
      kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega) hpin
      hbk hb1 hb2
      (fun t => trans_p_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2) hplace htable))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_words3 _ M Jmax wpJ lvJ0 K S B T
      (W * (nC * (mC * 30)))
      (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
      kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
      arg2Base (d.table.map transArg2) _
      (by unfold lvJ0; omega) (by unfold lvJ0; omega) hMB hKS (by omega) (by omega)
      (fun t => trans_p_loop_writer_param M Jmax nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2) hplace htable)
      (fun t => clauseWriterBounded_trans_p_loop M Jmax K S B nS W mS nC mC wReg tReg kbReg
        a1Reg a2Reg T kindBase arg1Base arg2Base t (d.table.map transKind)
        (d.table.map transArg1) (d.table.map transArg2) hplace htable hJ hK1 hwR hwR2 hkbR2
        ha1R2 ha2R2 hMB hSB h4S h3S hKB hKS henvB henvS hnS hmS hK1mC hmCB hmCK hnCK hlenkB
        hlen1B hlen2B hallowedk hallowed1 hallowed2 hkindBaseK harg1BaseK harg2BaseK hnCB hWK))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      have hev := pinsAndWords3_writeReg_loop M
        (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
        kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2
      have h1 : (writeReg τ (M + lvJ0) 0) 0 = M := by
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact exprBoundedIn_ctlCell B M tReg _ h1 (by omega))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      have hev := pinsAndWords3_writeReg_loop M
        (transParamPins0 wReg tReg kbReg a1Reg a2Reg W T kindBase arg1Base arg2Base)
        kindBase (d.table.map transKind) arg1Base (d.table.map transArg1)
        arg2Base (d.table.map transArg2) lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega)
        (fun q hq => by have := hpin q hq; omega) hbk hb1 hb2
      have h1 : (writeReg τ (M + lvJ0) 0) 0 = M := by
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact ctlCell_eval_of_pin M _ tReg T _ (by simp [transParamPins0]) hev.1 h1)

end NPComplete.CookLevin

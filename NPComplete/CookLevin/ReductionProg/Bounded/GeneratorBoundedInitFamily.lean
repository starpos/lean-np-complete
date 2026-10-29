module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedInit
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedAtLeastOne
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInit

/-!
The initial family is the persist pattern's four-nest replaced by a
concatenation of four pieces (`.seq` throughout, no shared loop counter):
two fixed clauses, a window loop over `W`, and a free-suffix loop over
`freeLen`.  Each piece's `ClauseWriterBounded` is built the same way
`GeneratorBoundedPersist.lean` builds one loop level — an inner leaf bound
composed through `clauseWriterBounded_loopProg_up_to` — and the family bound
is `clauseWriterBounded_seq` applied three times, matching `initFamilyProg`'s
own `.seq` nest.

Two obligations arise here that the persist family never raises, because
`initWindowLeafProgParam` branches on run-time data and its prefix branch reads
a *word* staged in the store (`initPrefixSymbolEParam`) rather than only
control cells (the trans family later reuses the `.ifNZ` combinator):

* An `.ifNZ` combinator for `ClauseWriterBounded` — `ProgramBoundedIn`'s own
  `.ifNZ` clause asks for both arms regardless of which one a store actually
  takes, so `clauseWriterBounded_ifNZ` proves both bounded at the same width.
* A word-based expression bound for `symbolAtEParam`/`wordReadEParam`,
  avoiding their whole-store `∀ i, σ i ≤ K` hypothesis (false at any store
  outside the family's own envelope) in favour of the two facts `PinsAndWord`
  actually supplies: the base register's value is a control cell (so
  `TightCells` bounds it by `K`), and the word entry the read touches is
  bounded by the caller's own `hallowed`/`hprefAllowed` hypothesis.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Two general combinators

Neither names the init family: one bounds a `writeClauseProg` leaf, and the
other composes both branches of a run-time `.ifNZ`.  Both shapes recur whenever
a family's leaf branches on run-time data. -/

/-- A `writeClauseProg` leaf as a `ClauseWriterBounded`, generic in
`Jmax ≥ 24` and any `Frozen`. -/
lemma clauseWriterBounded_writeClauseProg (M Jmax K S B : ℕ) (lits : List (Expr × Expr))
    (Frozen : Store → Prop) (hJ : 24 ≤ Jmax) (hMB : M + 24 ≤ B) (hSB : S ≤ B)
    (hcnt : lits.length ≤ S) (hlits : LitsBounded K S B M lits) :
    ClauseWriterBounded (writeClauseProg wpJ lits) M Jmax wpJ K S B (2 + 2 * lits.length)
      Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  have hsep24 : M + 24 < wp := by omega
  have hlen : wp + 2 + 2 * lits.length ≤ S := by omega
  obtain ⟨hpb, _, _, ht', hst', _⟩ :=
    writeClauseProg_bounded K S B M wp τ lits h0 hw hsep24 hMB hlen hSB hcnt hlits ht hst
  exact ⟨hpb, hst', ht'⟩

/-- Assigning a bounded expression into a scratch control cell `reg ∈ [2,24]`
is a zero-width bounded writer, provided the assigned value stays inside
both envelopes at every store the caller's `Frozen` allows. -/
lemma clauseWriterBounded_ctlAssign_scratch
    (M Jmax K S B reg : ℕ) (aE : Expr) (Frozen : Store → Prop)
    (hreg2 : 2 ≤ reg) (hreg24 : reg ≤ 24) (hMB : M + 24 ≤ B) (hKS : K ≤ S)
    (hval : ∀ τ : Store, Frozen τ → τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ aE ∧ aE.eval τ ≤ K) :
    ClauseWriterBounded (ctlAssign reg aE) M Jmax wpJ K S B 0 Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  obtain ⟨haB, haK⟩ := hval τ hF h0 ht hst
  have hMreg : M + reg ≤ B := by omega
  have hpb : ProgramBoundedIn B τ (ctlAssign reg aE) := by
    unfold ctlAssign ctlAddr
    refine ⟨⟨by simp only [ExprBoundedIn]; omega, by simp only [ExprBoundedIn]; omega, ?_⟩,
      haB, ?_⟩
    · simp only [Expr.eval, h0]; omega
    · simp only [Expr.eval, h0]; omega
  refine ⟨hpb, ?_, ?_⟩
  · unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0]
    intro i
    by_cases hi : i = M + reg
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff τ (M + reg) (aE.eval τ) i hi]; exact hst i
  · unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0]
    intro j hj2 hj24
    by_cases hjr : j = reg
    · rw [hjr, writeReg_same]; exact haK
    · rw [writeReg_diff τ (M + reg) (aE.eval τ) (M + j) (by omega)]; exact ht j hj2 hj24

/-- Wiring `.ifNZ` into `ClauseWriterBounded`: both branches must be bounded
at the same width, since `ProgramBoundedIn`'s own `.ifNZ` clause asks for
both arms regardless of which one the guard actually selects. -/
lemma clauseWriterBounded_ifNZ (condE : Expr) (p1 p2 : Program)
    (M Jmax wpJ K S B wid : ℕ) (Frozen : Store → Prop)
    (hcondB : ∀ τ : Store, Frozen τ → τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ condE)
    (hb1 : ClauseWriterBounded p1 M Jmax wpJ K S B wid Frozen)
    (hb2 : ClauseWriterBounded p2 M Jmax wpJ K S B wid Frozen) :
    ClauseWriterBounded (.ifNZ condE p1 p2) M Jmax wpJ K S B wid Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  have hcond := hcondB τ hF h0 ht hst
  obtain ⟨hpb1, _, _⟩ := hb1 τ wp hF h0 hw hsep hslack hst ht
  obtain ⟨hpb2, _, _⟩ := hb2 τ wp hF h0 hw hsep hslack hst ht
  refine ⟨⟨hcond, hpb1, hpb2⟩, ?_, ?_⟩ <;>
  · rw [eval_ifNZ]
    by_cases hc : condE.eval τ ≠ 0
    · rw [ite_eq_left hc]
      first
        | exact (hb1 τ wp hF h0 hw hsep hslack hst ht).2.1
        | exact (hb1 τ wp hF h0 hw hsep hslack hst ht).2.2
    · rw [ite_eq_right hc]
      first
        | exact (hb2 τ wp hF h0 hw hsep hslack hst ht).2.1
        | exact (hb2 τ wp hF h0 hw hsep hslack hst ht).2.2

/-- `writeAtLeastOneProg` at a compile-time-constant trip count, as a
`ClauseWriterBounded`.  The width is `2 + 2 * n`, the row it always writes. -/
lemma clauseWriterBounded_writeAtLeastOneProg_const
    (M Jmax K S B iJ n : ℕ) (varE : Expr) (Frozen : Store → Prop)
    (hJ : 24 ≤ Jmax) (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B) (hKB : K + 1 ≤ B)
    (hKS : K ≤ S) (hSB : S ≤ B) (hnK : n ≤ K)
    (hvarE : ∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ varE ∧ varE.eval τ ≤ S) :
    ClauseWriterBounded (writeAtLeastOneProg wpJ iJ (.const n) varE) M Jmax wpJ K S B
      (2 + 2 * n) Frozen := by
  intro τ wp hF h0 hw hsep hslack hst ht
  have hsep24 : M + 24 < wp := by omega
  have hpb := programBoundedIn_writeAtLeastOneProg K S B M wp iJ n τ (.const n) varE h0 hw
    hsep24 hMB hiJ hiJ2 hKB hKS hSB hnK (by omega) (by simp [ExprBoundedIn]; omega) rfl
    (by simp [ExprBoundedIn]; omega) rfl hvarE ht hst
  obtain ⟨_, _, htc, hsv⟩ := writeAtLeastOneProg_exit K S M wp iJ n τ (.const n) varE h0 hw
    hsep24 hiJ hiJ2 hKS hnK (by omega) rfl rfl (fun τ' h0' ht' hst' => (hvarE τ' h0' ht' hst').2)
    ht hst
  exact ⟨hpb, hsv, htc⟩

/-- Assigning into a scratch cell that is neither pinned nor inside the
staged word writes nothing, so it is a `ClauseWriter` for `[]` under
`PinsAndWord` — the correctness-side companion `clauseWriterBounded_seq`
needs to compose `ctlAssign` with a `writeClauseProg`. -/
lemma clauseWriter_ctlAssign_scratch
    (M Jmax reg : ℕ) (aE : Expr) (pins : List (ℕ × ℕ)) (base : ℕ) (xs : List ℕ)
    (hreg1 : 1 ≤ reg) (hregJ : reg ≤ Jmax) (hregwp : reg ≠ wpJ)
    (hpin : ∀ q ∈ pins, q.1 ≠ reg) (hbase : M + reg + 1 < base) :
    ClauseWriter (ctlAssign reg aE) M Jmax wpJ (PinsAndWord M pins base xs) [] := by
  intro τ wp hF h0 hw hsep
  have heval : (ctlAssign reg aE).eval τ = writeReg τ (M + reg) (aE.eval τ) := by
    unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]
  rw [heval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact pinsAndWord_writeReg M pins base xs (M + reg) (aE.eval τ) τ hF
      (fun p hp => by have := hpin p hp; omega)
      (by omega) (fun k hk => by omega)
  · rw [writeReg_diff τ (M + reg) _ 0 (by omega), h0]
  · rw [List.length_nil, rowTableWidth_zero, Nat.add_zero,
      writeReg_diff τ (M + reg) _ (M + wpJ) (by omega), hw]
  · exact rowsWritten_nil _ wp
  · intro r hr1 hr2
    rw [writeReg_diff]
    unfold CtlFree at hr2
    omega

/-- `PinsAndWord` companion to `clauseLoopBodyBoundedUpTo_of_clauseWriterBounded`:
a writer bounded for every counter value below the trip count, followed by
that counter's own bump, is an UpTo-bounded loop body over the outer pins
and staged word alone. -/
lemma clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_word (prog : Program)
    (M Jmax wpJ iJ K S B n wid : ℕ) (pins : List (ℕ × ℕ)) (base : ℕ) (xs : List ℕ)
    (cs : ℕ → List Clause)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hMB : M + 24 ≤ B) (hKS : K ≤ S)
    (hKB : K ≤ B) (hnK : n ≤ K)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ
      (PinsAndWord M ((iJ, i) :: pins) base xs) (cs i))
    (hb : ∀ i, ClauseWriterBounded prog M Jmax wpJ K S B wid
      (PinsAndWord M ((iJ, i) :: pins) base xs)) :
    ClauseLoopBodyBoundedUpTo (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ K S B n wid (PinsAndWord M pins base xs) := by
  intro τ i wp hF h0 hi hin hwp hsep hslack hst ht
  have hpins : PinsAndWord M ((iJ, i) :: pins) base xs τ :=
    pinsAndWord_cons M (iJ, i) pins base xs τ hi hF
  obtain ⟨hpb1, hst1, ht1⟩ := hb i τ wp hpins h0 hwp hsep hslack hst ht
  obtain ⟨hF1, h01, _, _, _⟩ := hw i τ wp hpins h0 hwp hsep
  have hi' : prog.eval τ (M + iJ) = i := pinsHold_head M (iJ, i) pins (prog.eval τ) hF1.1
  have hb1 : prog.eval τ (M + iJ) + 1 ≤ K := by omega
  obtain ⟨_, gt, gs⟩ := ctlAssign_bump_preserves K S M iJ 1 _ h01 hiJ hiJ2 ht1 hst1 hb1 hKS
  rw [eval_seq]
  exact ⟨⟨hpb1, programBoundedIn_ctlAssign_bump B M _ iJ 1 _ h01 (by omega) rfl (by omega)⟩,
    gs, gt⟩

/-! ## The staged-word expression bounds

`initPrefixSymbolEParam` is `symbolAtEParam` at the staged prefix word, and
a generic bound on it would ask for `∀ i, σ i ≤ K` —
false at any store outside a family's own tight envelope, since the table
above the write pointer routinely holds values past `K`.  These three
lemmas use what `PinsAndWord` actually supplies instead: the base
register is a control cell (`TightCells` bounds it), and the touched word
entry is bounded by the caller's `hallowed` hypothesis on the list itself. -/

/-- `wordReadEParam` bounded from register facts and the staged word alone:
only the base register's own value (`prefBase ≤ K`, true when `baseReg` is
a control cell under `TightCells`) and the specific word cell the read
touches (via `WordAt`/`hallowed`) are needed. -/
lemma exprBoundedIn_wordReadEParam_of_word
    (M K B baseReg lenReg blank prefBase : ℕ) (prefIdx : List ℕ) (σ : Store) (kE : Expr)
    (h0 : σ 0 = M) (hbase : σ (M + baseReg) = prefBase) (hlen : σ (M + lenReg) = prefIdx.length)
    (hword : WordAt σ prefBase prefIdx) (hallowed : ∀ v ∈ prefIdx, v ≤ K)
    (hbR : baseReg ≤ 23) (hlR : lenReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + K ≤ B) (hblank : blank ≤ K) (hprefBaseK : prefBase ≤ K)
    (hk : ExprBoundedIn B σ kE) (hkv : kE.eval σ ≤ K) :
    ExprBoundedIn B σ (wordReadEParam baseReg lenReg blank kE) ∧
      (wordReadEParam baseReg lenReg blank kE).eval σ ≤ K := by
  unfold wordReadEParam
  simp only [ExprBoundedIn, Expr.eval, ctlCell, ctlAddr, h0, hbase, hlen]
  by_cases hc : kE.eval σ < prefIdx.length
  · have hgetv : prefIdx.getD (kE.eval σ) 0 ≤ K :=
      hallowed _ (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc)
    have hdataval : σ (prefBase + kE.eval σ) = prefIdx.getD (kE.eval σ) 0 :=
      hword.2 (kE.eval σ) hc
    simp only [ite_eq_left hc, Nat.one_mul]
    refine ⟨?_, ?_⟩ <;> (repeat' apply And.intro) <;> omega
  · simp only [ite_eq_right hc, Nat.zero_mul, Nat.add_zero]
    refine ⟨?_, ?_⟩ <;> (repeat' apply And.intro) <;> omega

/-- `symbolAtEParam` bounded from register facts and the staged word alone. -/
lemma exprBoundedIn_symbolAtEParam_of_word
    (M K B baseReg lenReg blank prefBase : ℕ) (prefIdx : List ℕ) (σ : Store) (pE qE : Expr)
    (h0 : σ 0 = M) (hbase : σ (M + baseReg) = prefBase) (hlen : σ (M + lenReg) = prefIdx.length)
    (hword : WordAt σ prefBase prefIdx) (hallowed : ∀ v ∈ prefIdx, v ≤ K)
    (hbR : baseReg ≤ 23) (hlR : lenReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + K ≤ B) (hblank : blank ≤ K) (hprefBaseK : prefBase ≤ K)
    (hp : ExprBoundedIn B σ pE) (hq : ExprBoundedIn B σ qE)
    (hpv : pE.eval σ ≤ K) :
    ExprBoundedIn B σ (symbolAtEParam baseReg lenReg blank pE qE) ∧
      (symbolAtEParam baseReg lenReg blank pE qE).eval σ ≤ K := by
  have hsub : ExprBoundedIn B σ (pE.sub qE) := ⟨hp, hq, by omega⟩
  have hsubv : (pE.sub qE).eval σ ≤ K := by simp only [Expr.eval]; omega
  obtain ⟨hreadB, hreadV⟩ := exprBoundedIn_wordReadEParam_of_word M K B baseReg lenReg blank
    prefBase prefIdx σ (pE.sub qE) h0 hbase hlen hword hallowed hbR hlR hMK h1B hK hblank
    hprefBaseK hsub hsubv
  unfold symbolAtEParam
  have h1 : ExprBoundedIn B σ (((Expr.const 1).sub (pE.lt qE)).mul
      (wordReadEParam baseReg lenReg blank (pE.sub qE))) := by
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

/-- `initPrefixSymbolEParam` bounded from `PinsAndWord`-derived facts. -/
lemma exprBoundedIn_initPrefixSymbolEParam_of_word
    (M K B tReg plReg pbReg blank prefBase : ℕ) (prefIdx : List ℕ) (σ : Store)
    (h0 : σ 0 = M) (hpb : σ (M + pbReg) = prefBase) (hpl : σ (M + plReg) = prefIdx.length)
    (hword : WordAt σ prefBase prefIdx) (hallowed : ∀ v ∈ prefIdx, v ≤ K)
    (hplR : plReg ≤ 23) (hpbR : pbReg ≤ 23) (htR : tReg ≤ 23) (hMK : M + 23 ≤ B) (h1B : 1 ≤ B)
    (hK : K + K ≤ B) (hblank : blank ≤ K) (hprefBaseK : prefBase ≤ K)
    (h2v : σ (M + lvJ0) ≤ K) :
    ExprBoundedIn B σ (initPrefixSymbolEParam tReg plReg pbReg blank) ∧
      (initPrefixSymbolEParam tReg plReg pbReg blank).eval σ ≤ K := by
  unfold initPrefixSymbolEParam
  refine exprBoundedIn_symbolAtEParam_of_word M K B pbReg plReg blank prefBase prefIdx σ
    (ctlCell lvJ0) (ctlCell tReg) h0 hpb hpl hword hallowed hpbR hplR hMK h1B hK hblank
    hprefBaseK ?_ ?_ ?_
  · simp only [ExprBoundedIn, ctlCell, ctlAddr, Expr.eval, h0]; unfold lvJ0; omega
  · simp only [ExprBoundedIn, ctlCell, ctlAddr, Expr.eval, h0]; omega
  · simp only [ctlCell, ctlAddr, Expr.eval, h0]; exact h2v

/-! ## Level: the window leaf

`initWindowLeafProgParam` is two nested `.ifNZ`: prefix vs (free/blank), then
free vs blank.  The prefix branch stages `initPrefixSymbolEParam` into
`tmpJ` first (`ClauseWriter` for `[]`, by `clauseWriter_ctlAssign_scratch`)
before the `writeClauseProg` reads it back — the same staging discipline
`ClauseFamilyInitWindow.lean`'s correctness proof already uses. -/

/-- The window leaf's prefix branch alone, as a `ClauseWriterBounded`.
`hcellsFrozen` is the control-cell fact shared by all three branches. -/
lemma clauseWriterBounded_init_window_prefix_branch
    (M Jmax K S B n W m T blank prefBase prefLen freeLen p wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx _allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) (hJ : 24 ≤ Jmax)
    (hlen : prefLen = prefIdx.length)
    (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hplR2 : plReg ≤ 23) (hpbR2 : pbReg ≤ 23)
    (hbase : M + pbReg + 1 < prefBase)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKS : K ≤ S)
    (hblank : blank ≤ K) (hprefAllowed : ∀ v ∈ prefIdx, v ≤ K)
    (hcellsFrozen : ∀ τ : Store,
      PinsAndWord M (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx τ →
      τ 0 = M → TightCells K M τ →
      τ (M + tReg) ≤ K ∧ τ (M + plReg) ≤ K ∧ τ (M + lvJ0) ≤ K ∧ τ (M + pbReg) ≤ K) :
    ClauseWriterBounded (.seq (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
        (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg))))
      M Jmax wpJ K S B 4
      (PinsAndWord M (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx) := by
  unfold InitEnv at henvB henvS
  set Frozen := PinsAndWord M
    (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p) prefBase prefIdx
    with hFrozenDef
  have hb1 : ClauseWriterBounded (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
      M Jmax wpJ K S B 0 Frozen := by
    refine clauseWriterBounded_ctlAssign_scratch M Jmax K S B tmpJ
      (initPrefixSymbolEParam tReg plReg pbReg blank) Frozen (by unfold tmpJ; omega)
      (by unfold tmpJ; omega) hMB hKS ?_
    intro τ hF h0 ht hst
    obtain ⟨gt, gpl, g0, gpb⟩ := hcellsFrozen τ hF h0 ht
    have hpb : τ (M + pbReg) = prefBase :=
      hF.1 (pbReg, prefBase) (by simp [initParamPins1, initParamPins0])
    have hplv : τ (M + plReg) = prefLen :=
      hF.1 (plReg, prefLen) (by simp [initParamPins1, initParamPins0])
    have hplen : prefLen = prefIdx.length := hlen
    exact exprBoundedIn_initPrefixSymbolEParam_of_word M K B tReg plReg pbReg blank prefBase
      prefIdx τ h0 hpb (hplen ▸ hplv) hF.2 hprefAllowed hplR2 hpbR2 htR2 (by omega) (by omega)
      (by omega) hblank (hpb ▸ gpb) g0
  have hb2 : ClauseWriterBounded
      (writeClauseProg wpJ (unitPosLits (initPrefixCellStagedEParam n m wReg)))
      M Jmax wpJ K S B 4 Frozen := by
    have h := clauseWriterBounded_writeClauseProg M Jmax K S B
      (unitPosLits (initPrefixCellStagedEParam n m wReg)) Frozen hJ hMB hSB
      (by simp [unitPosLits]; omega)
      (litsBounded_init_prefix_cell K S B M n m wReg (by have := hplace.w_min; omega) hwR2 hMB
        henvB henvS hn hm)
    simpa [unitPosLits] using h
  have hw1 : ClauseWriter (ctlAssign tmpJ (initPrefixSymbolEParam tReg plReg pbReg blank))
      M Jmax wpJ Frozen [] := by
    have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_f
    have hw4 := hplace.f_pl; have hw5 := hplace.pl_pb
    exact clauseWriter_ctlAssign_scratch M Jmax tmpJ
      (initPrefixSymbolEParam tReg plReg pbReg blank)
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hplace.ctl_le)
      (by unfold tmpJ wpJ; omega)
      (fun q hq => (init_param_pins1_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
        prefBase p tmpJ hplace (by unfold tmpJ ctlJmax; omega)
        (by unfold lvJ0 tmpJ; omega) q hq).2.2.1)
      (by unfold tmpJ; omega)
  exact clauseWriterBounded_seq _ _ M Jmax wpJ K S B 0 4 Frozen [] hw1
    (le_of_eq (rowTableWidth_zero _)) hb1 hb2

/-- The window loop's leaf, as a `ClauseWriterBounded` at any window
position `p`.  `hprefAllowed` is what the prefix branch's staged read
needs; the other two branches (free/blank) only ever touch control cells. -/
lemma clauseWriterBounded_initWindowLeafProgParam
    (M Jmax K S B n W m T blank prefBase prefLen freeLen p wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) (hJ : 24 ≤ Jmax)
    (hlen : prefLen = prefIdx.length)
    (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hfR2 : fReg ≤ 23) (hplR2 : plReg ≤ 23)
    (hpbR2 : pbReg ≤ 23)
    (hbase : M + pbReg + 1 < prefBase)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hblank : blank ≤ K) (hallowed : ∀ v ∈ allowedIdx, v ≤ K) (hlenK : allowedIdx.length + 1 ≤ K)
    (hprefAllowed : ∀ v ∈ prefIdx, v ≤ K) :
    ClauseWriterBounded (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      M Jmax wpJ K S B (2 + 2 * (allowedIdx.length + 1))
      (PinsAndWord M (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx) := by
  unfold InitEnv at henvB henvS
  have hrel : 3 * K * m = 3 * (K * m) := by ring
  have hJlow : 24 ≤ Jmax := hJ
  set Frozen := PinsAndWord M
    (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p) prefBase prefIdx
    with hFrozenDef
  have hcellsFrozen : ∀ τ : Store, Frozen τ → τ 0 = M → TightCells K M τ →
      τ (M + wReg) ≤ K ∧ τ (M + tReg) ≤ K ∧ τ (M + fReg) ≤ K ∧ τ (M + plReg) ≤ K ∧
      τ (M + lvJ0) ≤ K ∧ τ (M + pbReg) ≤ K := by
    intro τ hF h0 ht
    have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_f
    have hw4 := hplace.f_pl; have hw5 := hplace.pl_pb
    have gw : τ (M + wReg) ≤ K := ht wReg (by omega) (by omega)
    have gt : τ (M + tReg) ≤ K := ht tReg (by omega) (by omega)
    have gf : τ (M + fReg) ≤ K := ht fReg (by omega) (by omega)
    have gpl : τ (M + plReg) ≤ K := ht plReg (by omega) (by omega)
    have gp : τ (M + lvJ0) ≤ K := ht lvJ0 (by unfold lvJ0; omega) (by unfold lvJ0; omega)
    have gpb : τ (M + pbReg) ≤ K := ht pbReg (by omega) (by omega)
    exact ⟨gw, gt, gf, gpl, gp, gpb⟩
  unfold initWindowLeafProgParam
  refine clauseWriterBounded_ifNZ (initInPrefixEParam tReg plReg) _ _ M Jmax wpJ K S B
    (2 + 2 * (allowedIdx.length + 1)) Frozen ?_ ?_ ?_
  · intro τ hF h0 ht hst
    obtain ⟨_, gt, _, gpl, _, _⟩ := hcellsFrozen τ hF h0 ht
    exact exprBoundedIn_initInPrefixEParam M K B tReg plReg τ h0 htR2 hplR2 (by omega) gt gpl
      (by omega)
  · refine clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B 4 (2 + 2 * (allowedIdx.length + 1))
      Frozen (by omega) ?_
    exact clauseWriterBounded_init_window_prefix_branch M Jmax K S B n W m T blank prefBase prefLen
      freeLen p wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hJ hlen hwR2 htR2 hplR2
      hpbR2 hbase henvB henvS hn hm hMB hSB hKS hblank hprefAllowed
      (fun τ hF h0 ht => by
        obtain ⟨_, gt, _, gpl, gp, gpb⟩ := hcellsFrozen τ hF h0 ht
        exact ⟨gt, gpl, gp, gpb⟩)
  · refine clauseWriterBounded_ifNZ (initInFreeEParam tReg plReg fReg) _ _ M Jmax wpJ K S B
      (2 + 2 * (allowedIdx.length + 1)) Frozen ?_ ?_ ?_
    · intro τ hF h0 ht hst
      obtain ⟨_, gt, gf, gpl, _, _⟩ := hcellsFrozen τ hF h0 ht
      exact exprBoundedIn_initInFreeEParam M K B tReg plReg fReg τ h0 htR2 hplR2 hfR2 (by omega)
        gt gpl gf (by omega)
    · exact clauseWriterBounded_writeAtLeastOneProg_const M Jmax K S B litJ
        (allowedIdx.length + 1) (initFreeCellVarEParam n m wReg blank allowedIdx) Frozen hJlow
        (by unfold litJ; omega) (by unfold litJ; omega) hMB hKB hKS hSB hlenK
        (fun τ h0 ht hst => by
          have hw1 := hplace.w_min
          have gw : τ (M + wReg) ≤ K := ht wReg (by omega) (by omega)
          have gp : τ (M + lvJ0) ≤ K := ht lvJ0 (by unfold lvJ0; omega) (by unfold lvJ0; omega)
          have gl : τ (M + litJ) ≤ K := ht litJ (by unfold litJ; omega) (by unfold litJ; omega)
          refine ⟨exprBoundedIn_initFreeCellVarEParam M K B n m wReg blank K allowedIdx τ h0 gp gl
            gw hwR2 (by omega) (by omega) (by omega) hallowed hblank (by omega) hn hm, ?_⟩
          exact le_trans (initFreeCellVarEParam_eval_le M K n m wReg blank K allowedIdx τ h0 gp gw
            hallowed hblank) (by omega))
    · refine clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B 4 (2 + 2 * (allowedIdx.length + 1))
        Frozen (by omega) ?_
      have h := clauseWriterBounded_writeClauseProg M Jmax K S B
        (unitPosLits (initBlankCellEParam n m wReg blank)) Frozen hJ hMB hSB
        (by simp [unitPosLits]; omega)
        (litsBounded_init_blank_cell K S B M n m wReg blank (by have := hplace.w_min; omega) hwR2
          hMB henvB henvS hn hm hblank)
      simpa [unitPosLits] using h

/-! ## Level: the window loop -/

/-- The window loop as a `ClauseWriterBounded`, given the leaf's own bound
at every window position. -/
lemma clauseWriterBounded_initWindowProgParam
    (M Jmax K S B n W m T blank prefBase prefLen freeLen wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx allowedIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hlen : prefLen = prefIdx.length) (hwR2 : wReg ≤ 23)
    (hbase : M + pbReg + 1 < prefBase) (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (hMB : M + 24 ≤ B) (hKS : K ≤ S) (hKB : K ≤ B) (hWK : W ≤ K)
    (hleaf : ∀ p, ClauseWriterBounded
      (initWindowLeafProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      M Jmax wpJ K S B (2 + 2 * (allowedIdx.length + 1))
      (PinsAndWord M (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
        prefBase prefIdx)) :
    ClauseWriterBounded (initWindowProgParam n m blank wReg tReg fReg plReg pbReg allowedIdx)
      M Jmax wpJ K S B (W * (2 + 2 * (allowedIdx.length + 1)))
      (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
        prefBase prefIdx) := by
  have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_f
  have hw4 := hplace.f_pl; have hw5 := hplace.pl_pb
  have hctlbase : M + ctlJmax < prefBase := by unfold ctlJmax; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  unfold initWindowProgParam
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 W (2 + 2 * (allowedIdx.length + 1))
    (ctlCell wReg) _
    (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
      prefBase prefIdx)
    (fun p => [initWindowClause n W m T blank prefIdx allowedIdx freeLen p])
    (by unfold lvJ0; omega) hlvJ0le hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWord_writeReg_loop M
        (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
        prefIdx lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega) (fun p hp => by
          obtain ⟨_, _, hpne, _⟩ := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T
            freeLen prefLen prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) p hp
          omega) hctlbase)
    (fun p _ => by
      have hcl : [initWindowClause n W m T blank prefIdx allowedIdx freeLen p].length = 1 := rfl
      rw [hcl, rowTableWidth_singleton]
      unfold initWindowClause
      by_cases h1 : p < T + prefIdx.length
      · simp only [h1, ite_true, unitPos_len]; omega
      · by_cases h2 : p < T + prefIdx.length + freeLen
        · simp only [h1, ite_false, h2, ite_true]
          rw [atLeastOne_length]; simp
        · simp only [h1, ite_false, h2, unitPos_len]; omega)
    (clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0
      (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) _
      prefBase prefIdx (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      (fun q hq => init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
        prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) q hq)
      hctlbase (fun p => by
        change ClauseWriter _ M Jmax wpJ
          (PinsAndWord M
            (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
            prefBase prefIdx) _
        exact init_window_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen p
          wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hbase hfit))
    (clauseLoopBodyBoundedUpTo_of_clauseWriterBounded_word _ M Jmax wpJ lvJ0 K S B W
      (2 + 2 * (allowedIdx.length + 1))
      (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase prefIdx
      (fun p => [initWindowClause n W m T blank prefIdx allowedIdx freeLen p])
      (by unfold lvJ0; omega) hlvJ0le hMB hKS hKB hWK
      (fun p => by
        change ClauseWriter _ M Jmax wpJ
          (PinsAndWord M
            (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
            prefBase prefIdx) _
        exact init_window_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen p
          wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hbase hfit)
      (fun p => by
        change ClauseWriterBounded _ M Jmax wpJ K S B (2 + 2 * (allowedIdx.length + 1))
          (PinsAndWord M
            (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
            prefBase prefIdx)
        exact hleaf p))
    (fun τ hF h0 => by
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact exprBoundedIn_ctlCell B M wReg _ h1 (by omega : M + wReg ≤ B))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      have hF' : PinsAndWord M
          (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
          prefIdx ((ctlAssign lvJ0 (.const 0)).eval τ) := by
        rw [heq]
        exact pinsAndWord_writeReg_loop M
          (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
          prefIdx lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega) (fun p hp => by
            obtain ⟨_, _, hpne, _⟩ := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T
              freeLen prefLen prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) p hp
            omega) hctlbase
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        rw [heq, writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact ctlCell_eval_of_pin M _ wReg W _ (by simp [initParamPins0]) hF'.1 h1)

/-! ## Level: the tail loop

`initTailProgParam`'s leaf reads only control cells (no staged word), so it
closes through `clauseLoopBodyBoundedUpTo_leafProg` directly, the same way
`GeneratorBoundedPersist.lean`'s letter loop does. -/

/-- The tail loop as a `ClauseWriterBounded`.  Each of the `freeLen`
iterations writes one `implyPos` row (width `6`, two literals). -/
lemma clauseWriterBounded_initTailProgParam
    (M Jmax K S B n W m T blank prefBase prefLen freeLen wReg tReg fReg plReg pbReg : ℕ)
    (prefIdx : List ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) (hJ : 24 ≤ Jmax)
    (hlen : prefLen = prefIdx.length)
    (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hplR2 : plReg ≤ 23)
    (hbase : M + pbReg + 1 < prefBase) (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S)
    (hblank : blank ≤ K) (hfreeK : freeLen ≤ K) (h2S : 2 ≤ S) :
    ClauseWriterBounded (initTailProgParam n m blank wReg tReg fReg plReg)
      M Jmax wpJ K S B (freeLen * 6)
      (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
        prefBase prefIdx) := by
  have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_f
  have hw4 := hplace.f_pl; have hw5 := hplace.pl_pb
  have hctlbase : M + ctlJmax < prefBase := by unfold ctlJmax; omega
  have hlvJ0le : lvJ0 ≤ 24 := by unfold lvJ0; omega
  unfold initTailProgParam
  refine clauseWriterBounded_loopProg_up_to K S B M Jmax lvJ0 freeLen 6 (ctlCell fReg) _
    (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
      prefBase prefIdx)
    (fun i => [implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
        ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)])
    (by unfold lvJ0; omega) hlvJ0le hMB
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      rw [heq]
      exact pinsAndWord_writeReg_loop M
        (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
        prefIdx lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega) (fun p hp => by
          obtain ⟨_, _, hpne, _⟩ := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T
            freeLen prefLen prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) p hp
          omega) hctlbase)
    (fun i _ => by
      have hcl : ([implyPos ((denseLayout n W m).cell 0 (T + prefIdx.length + i) blank)
        ((denseLayout n W m).cell 0 (T + prefIdx.length + i + 1) blank)] : List Clause).length
          = 1 := rfl
      rw [hcl, rowTableWidth_singleton, implyPos_len])
    (clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0
      (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) _
      prefBase prefIdx (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le)
      (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
      (fun q hq => init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
        prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) q hq)
      hctlbase (fun i => by
        have hpins : (lvJ0, i) ::
            initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase
            = initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase i := rfl
        rw [hpins]
        exact init_tail_leaf_writer_param M Jmax n W m T blank prefBase prefLen freeLen i
          wReg tReg fReg plReg pbReg prefIdx hplace hlen hbase hfit))
    (clauseLoopBodyBoundedUpTo_leafProg K S B M Jmax lvJ0 freeLen
      (implyPosLits (initTailCellEParam n m wReg tReg plReg blank)
        (initTailCellNextEParam n m wReg tReg plReg blank))
      (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
        prefBase prefIdx)
      (by unfold lvJ0; omega) hlvJ0le hJ hMB hSB hKB hKS hfreeK
      (by simp [implyPosLits]; omega)
      (litsBounded_init_tail K S B M n m wReg tReg plReg blank (by omega) hwR2 (by omega) htR2
        (by omega) hplR2 hMB henvB henvS hn hm hblank))
    (fun τ hF h0 => by
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        unfold ctlAssign; rw [eval_assignInd]; simp only [Expr.eval, ctlAddr, h0]
        rw [writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact exprBoundedIn_ctlCell B M fReg _ h1 (by omega))
    (fun τ hF h0 => by
      have heq : (ctlAssign lvJ0 (.const 0)).eval τ = writeReg τ (M + lvJ0) 0 := by
        unfold ctlAssign; rw [eval_assignInd, ctlAddr_eval, h0]; rfl
      have hF' : PinsAndWord M
          (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
          prefIdx ((ctlAssign lvJ0 (.const 0)).eval τ) := by
        rw [heq]
        exact pinsAndWord_writeReg_loop M
          (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase) prefBase
          prefIdx lvJ0 0 τ hF (by unfold lvJ0 lvJ3; omega) (fun p hp => by
            obtain ⟨_, _, hpne, _⟩ := init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T
              freeLen prefLen prefBase lvJ0 hplace (by unfold lvJ0 ctlJmax; omega) p hp
            omega) hctlbase
      have h1 : ((ctlAssign lvJ0 (.const 0)).eval τ) 0 = M := by
        rw [heq, writeReg_diff τ (M + lvJ0) 0 0 (by unfold lvJ0; omega), h0]
      exact ctlCell_eval_of_pin M _ fReg freeLen _ (by simp [initParamPins0]) hF'.1 h1)

/-! ## The two fixed leaves (state and head) -/

lemma clauseWriterBounded_initStateProgParam
    (M Jmax K S B n m wReg : ℕ) (d : TableauDescriptor) (Frozen : Store → Prop)
    (hJ : 24 ≤ Jmax) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (h1S : 1 ≤ S) (hstart : d.startState ≤ K) :
    ClauseWriterBounded (initStateProgParam n m wReg d) M Jmax wpJ K S B 4 Frozen := by
  unfold initStateProgParam
  by_cases hst : d.startState < d.numStates
  · simp only [ite_eq_left hst]
    have h := clauseWriterBounded_writeClauseProg M Jmax K S B
      (unitPosLits (initStateEParam n m wReg d.startState)) Frozen hJ hMB hSB
      (by simp [unitPosLits]; omega)
      (litsBounded_init_state K S B M n m wReg d.startState hwR hwR2 hMB henvB henvS hn hm hstart)
    simpa [unitPosLits] using h
  · simp only [ite_eq_right hst]
    exact clauseWriterBounded_of_wid_le _ M Jmax wpJ K S B 2 4 Frozen (by omega)
      (clauseWriterBounded_writeClauseProg M Jmax K S B [] Frozen hJ hMB hSB (by simp)
        (litsBounded_nil K S B M))

lemma clauseWriterBounded_initHeadProgParam
    (M Jmax K S B n m wReg tReg : ℕ) (Frozen : Store → Prop)
    (hJ : 24 ≤ Jmax) (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (htR : 2 ≤ tReg) (htR2 : tReg ≤ 23)
    (hMB : M + 24 ≤ B)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hSB : S ≤ B) (h1S : 1 ≤ S) :
    ClauseWriterBounded (initHeadProgParam n m wReg tReg) M Jmax wpJ K S B 4 Frozen := by
  unfold initHeadProgParam
  have h := clauseWriterBounded_writeClauseProg M Jmax K S B
    (unitPosLits (initHeadEParam n m wReg tReg)) Frozen hJ hMB hSB
    (by simp [unitPosLits]; omega)
    (litsBounded_init_head K S B M n m wReg tReg hwR hwR2 htR htR2 hMB henvB henvS hn hm)
  simpa [unitPosLits] using h

/-! ## The whole family -/

/-- The window loop's own clause list, as a `List.map`, has width at most
`W * (2 + 2 * (allowedIdx.length + 1))`: every window position writes at
most one `atLeastOne`-shaped row (the widest of the three branches). -/
lemma init_window_map_width (n W m T blank : ℕ) (prefIdx allowedIdx : List ℕ) (freeLen : ℕ) :
    rowTableWidth
      (rowW ((List.range W).map fun p =>
        initWindowClause n W m T blank prefIdx allowedIdx freeLen p))
      ((List.range W).map fun p =>
        initWindowClause n W m T blank prefIdx allowedIdx freeLen p).length
      ≤ W * (2 + 2 * (allowedIdx.length + 1)) := by
  rw [List.length_map, List.length_range]
  refine rowTableWidth_le_count_mul _ _ _ (fun i hi => ?_)
  have heq : (rowW ((List.range W).map fun p =>
      initWindowClause n W m T blank prefIdx allowedIdx freeLen p)) i
      = (initWindowClause n W m T blank prefIdx allowedIdx freeLen i).lits.length := by
    unfold rowW
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  rw [heq]
  unfold initWindowClause
  by_cases h1 : i < T + prefIdx.length
  · simp [h1, unitPos]
  · by_cases h2 : i < T + prefIdx.length + freeLen
    · simp only [h1, ite_false, h2, ite_true, atLeastOne]
      simp
    · simp [h1, h2, unitPos]

/-- The full initial family, as a `ClauseWriterBounded`: the state clause
(width `4`), the head clause (width `4`), the window loop (width
`W * (2 + 2 * (allowedIdx.length + 1))`), and the tail loop (width
`freeLen * 6`), composed via `.seq` matching `initFamilyProgParam`'s own
nest. -/
lemma clauseWriterBounded_initFamilyProgParam
    (M Jmax K S B n W m T wReg tReg fReg plReg pbReg : ℕ) (d : TableauDescriptor)
    (allowedIdx prefIdx : List ℕ) (prefLen freeLen prefBase : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg) (hJ : 24 ≤ Jmax)
    (hlen : prefLen = prefIdx.length)
    (hwR2 : wReg ≤ 23) (htR2 : tReg ≤ 23) (hfR2 : fReg ≤ 23) (hplR2 : plReg ≤ 23)
    (hpbR2 : pbReg ≤ 23)
    (hbase : M + pbReg + 1 < prefBase) (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (henvB : InitEnv K B n m) (henvS : InitEnv K S n m) (hn : n ≤ B) (hm : m ≤ B)
    (hMB : M + 24 ≤ B) (hSB : S ≤ B) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (h2S : 2 ≤ S)
    (hblank : d.blankIdx ≤ K) (hallowed : ∀ v ∈ allowedIdx, v ≤ K)
    (hlenK : allowedIdx.length + 1 ≤ K) (hprefAllowed : ∀ v ∈ prefIdx, v ≤ K)
    (hWK : W ≤ K) (hfreeK : freeLen ≤ K) (hstart : d.startState ≤ K) :
    ClauseWriterBounded (initFamilyProgParam n m d allowedIdx wReg tReg fReg plReg pbReg)
      M Jmax wpJ K S B (4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)))
      (InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase prefIdx) := by
  have hw1 := hplace.w_min; have hw2 := hplace.w_t; have hw3 := hplace.t_f
  have hw4 := hplace.f_pl; have hw5 := hplace.pl_pb
  have hwindow := clauseWriterBounded_initWindowProgParam M Jmax K S B n W m T d.blankIdx prefBase
    prefLen freeLen wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hwR2 hbase hfit
    hMB hKS (by omega) hWK
    (fun p => clauseWriterBounded_initWindowLeafProgParam M Jmax K S B n W m T d.blankIdx prefBase
      prefLen freeLen p wReg tReg fReg plReg pbReg prefIdx allowedIdx hplace hJ hlen hwR2 htR2
      hfR2 hplR2 hpbR2 hbase henvB henvS hn hm hMB hSB hKB hKS hblank hallowed hlenK
      hprefAllowed)
  have htail := clauseWriterBounded_initTailProgParam M Jmax K S B n W m T d.blankIdx prefBase
    prefLen freeLen wReg tReg fReg plReg pbReg prefIdx hplace hJ hlen hwR2 htR2 hplR2 hbase hfit
    henvB henvS hn hm hMB hSB hKB hKS hblank hfreeK h2S
  unfold initFamilyProgParam InitParamFrozen
  refine clauseWriterBounded_seq _ _ M Jmax wpJ K S B 4
    (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6))
    (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
      prefBase prefIdx) [descInitStateClause (denseLayout n W m) d]
    (init_state_writer_param M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg pbReg
      d prefIdx hplace hbase hfit) ?_
    (clauseWriterBounded_initStateProgParam M Jmax K S B n m wReg d _ hJ (by omega) hwR2 hMB
      henvB henvS hn hm hSB (by omega) hstart) ?_
  · have hcl : [descInitStateClause (denseLayout n W m) d].length = 1 := rfl
    rw [hcl, rowTableWidth_singleton]
    unfold descInitStateClause
    by_cases h : d.startState < d.numStates
    · simp [h, unitPos_len]
    · simp [h]
  · refine clauseWriterBounded_seq _ _ M Jmax wpJ K S B 4
      (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)
      (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
        prefBase prefIdx) [unitPos ((denseLayout n W m).head 0 (originIdx T))]
      (init_head_writer_param M Jmax n W m T freeLen prefLen prefBase wReg tReg fReg plReg pbReg
        prefIdx hplace hbase hfit) (by
        have hcl : [unitPos ((denseLayout n W m).head 0 (originIdx T))].length = 1 := rfl
        rw [hcl, rowTableWidth_singleton, unitPos_len])
      (clauseWriterBounded_initHeadProgParam M Jmax K S B n m wReg tReg _ hJ (by omega) hwR2
        (by omega) htR2 hMB henvB henvS hn hm hSB (by omega))
      (clauseWriterBounded_seq _ _ M Jmax wpJ K S B (W * (2 + 2 * (allowedIdx.length + 1)))
        (freeLen * 6)
        (PinsAndWord M (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
          prefBase prefIdx)
        ((List.range W).map fun p => initWindowClause n W m T d.blankIdx prefIdx allowedIdx
          freeLen p)
        (init_window_loop_writer_param M Jmax n W m T d.blankIdx prefBase prefLen freeLen wReg
          tReg fReg plReg pbReg prefIdx allowedIdx hplace hlen hbase hfit)
        (init_window_map_width n W m T d.blankIdx prefIdx allowedIdx freeLen)
        hwindow htail)

end NPComplete.CookLevin

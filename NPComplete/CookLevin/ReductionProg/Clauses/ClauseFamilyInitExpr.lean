module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableFrame
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteFrozen
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.Tableau.NatTableau

/-!
The initial family is the only one whose per-position clause changes *shape*
rather than just its variable numbers: a window cell either carries a prefix
symbol, or is free to be any allowed letter, or must be blank, depending on where
it sits relative to the prefix and the free region.  A `forN` body writes the same
number of clauses at every index, so the three cases have to be selected by an
`ifNZ` on comparisons rather than by three different loops.

Both comparisons are on the loop counter against compile-time constants, and the
prefix read reuses the accept family's machinery — the signed index reduces to a
natural comparison, and the word is staged in the store with its length a
constant.  What is new here is only the nesting of the two tests.

The start-state clause is a separate matter: its guard `startState < numStates`
is decided once when the producer is chosen, not per input, so it needs no
run-time branch at all.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Variable expressions

The window position is the level's own counter (`lvJ0`); the time index is the
constant `0`, since every initial clause lives on the tableau's first row. -/

/-- `cell 0 p a` for a letter index given by an expression. -/
def initCellE (n W m : ℕ) (aE : Expr) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.const 0) (ctlCell lvJ0) aE

/-- `cell 0 p s`, where `s` is the prefix word's symbol at window index `p`. -/
def initPrefixCellE (n W m T prefBase blank prefLen : ℕ) : Expr :=
  initCellE n W m
    (symbolAtE prefBase blank prefLen (ctlCell lvJ0) (.const T))

/-- `cell 0 p blank`, the clause for positions past the free region. -/
def initBlankCellE (n W m blank : ℕ) : Expr :=
  initCellE n W m (.const blank)

/-- `state 0 startState`, the start-state clause's only variable. -/
def initStateE (n W m startState : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (.const 0) (.const startState)

/-- `head 0 (originIdx T)`, the head's initial position. -/
def initHeadE (n W m T : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (.const 0) (.const (originIdx T))

/-! ## Frame conditions

`initStateE` and `initHeadE` read nothing at all — every operand is a constant —
so they are stable under any change.  The cell expressions read the counter, and
the prefix one also reads the staged word. -/

lemma initStateE_frame (n W m startState : ℕ) (σ σ' : Store) :
    (initStateE n W m startState).eval σ' = (initStateE n W m startState).eval σ := by
  unfold initStateE
  rw [denseStateE_eval, denseStateE_eval]
  simp [Expr.eval]

lemma initHeadE_frame (n W m T : ℕ) (σ σ' : Store) :
    (initHeadE n W m T).eval σ' = (initHeadE n W m T).eval σ := by
  unfold initHeadE
  rw [denseHeadE_eval, denseHeadE_eval]
  simp [Expr.eval]

lemma initBlankCellE_frame_below (M n W m blank bound : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hbound : M + ctlJmax < bound)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (initBlankCellE n W m blank).eval σ' = (initBlankCellE n W m blank).eval σ := by
  have hctl : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  unfold initBlankCellE initCellE
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl]

lemma initPrefixCellE_frame_below (M n W m T prefBase blank prefLen bound : ℕ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hbound : M + ctlJmax < bound)
    (hw : WordBelow prefBase prefLen bound) (hbase : M + ctlJmax < prefBase)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (initPrefixCellE n W m T prefBase blank prefLen).eval σ'
      = (initPrefixCellE n W m T prefBase blank prefLen).eval σ := by
  have hctl : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  have e0 := ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl
  have hsym := symbolAtE_frame prefBase blank prefLen bound (M + wpJ)
    (ctlCell lvJ0) (.const T) σ σ' hw
    (fun k _ => (word_ne_ctl M prefBase k hbase).1) hagree e0 rfl
  unfold initPrefixCellE initCellE
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval, e0, hsym]

/-! ## Values

The counter holds the window position; the constants are what they are. -/

lemma initStateE_value (n W m startState : ℕ) (τ : Store) :
    (initStateE n W m startState).eval τ = (denseLayout n W m).state 0 startState := by
  unfold initStateE
  rw [denseStateE_eval]
  simp [Expr.eval]

lemma initHeadE_value (n W m T : ℕ) (τ : Store) :
    (initHeadE n W m T).eval τ = (denseLayout n W m).head 0 (originIdx T) := by
  unfold initHeadE
  rw [denseHeadE_eval]
  simp [Expr.eval]

lemma initBlankCellE_value (M n W m blank p : ℕ) (τ : Store)
    (h0 : τ 0 = M) (hp : τ (M + lvJ0) = p) :
    (initBlankCellE n W m blank).eval τ = (denseLayout n W m).cell 0 p blank := by
  have e0 : (ctlCell lvJ0).eval τ = p := by rw [ctlCell_eval, h0]; exact hp
  unfold initBlankCellE initCellE
  rw [denseCellE_eval]
  simp only [Expr.eval, e0]

lemma initPrefixCellE_value (M n W m T prefBase blank p : ℕ) (τ : Store)
    (prefIdx : List ℕ) (h0 : τ 0 = M) (hp : τ (M + lvJ0) = p)
    (hw : WordAt τ prefBase prefIdx) :
    (initPrefixCellE n W m T prefBase blank prefIdx.length).eval τ
      = (denseLayout n W m).cell 0 p (natInitSymbol blank prefIdx (idxToPos T p)) := by
  have e0 : (ctlCell lvJ0).eval τ = p := by rw [ctlCell_eval, h0]; exact hp
  have hsym := symbolAtE_eval τ prefBase blank prefIdx (ctlCell lvJ0) (.const T) hw
  rw [e0] at hsym
  simp only [Expr.eval] at hsym
  unfold initPrefixCellE initCellE
  rw [denseCellE_eval]
  simp only [Expr.eval, e0, hsym, idxToPos]

/-! ## The two guards

Both tests compare the window position against a compile-time constant, so each
is an `Expr` comparison and the three-way choice is two nested `ifNZ`. -/

/-- Whether position `p` still lies inside the prefix. -/
def initInPrefixE (T prefLen : ℕ) : Expr :=
  .lt (ctlCell lvJ0) (.const (T + prefLen))

/-- Whether position `p` lies inside the prefix or the free region. -/
def initInFreeE (T prefLen freeLen : ℕ) : Expr :=
  .lt (ctlCell lvJ0) (.const (T + prefLen + freeLen))

lemma initInPrefixE_eval (M T prefLen p : ℕ) (τ : Store)
    (h0 : τ 0 = M) (hp : τ (M + lvJ0) = p) :
    (initInPrefixE T prefLen).eval τ = if p < T + prefLen then 1 else 0 := by
  unfold initInPrefixE
  simp only [Expr.eval, ctlCell_eval, h0, hp]

lemma initInFreeE_eval (M T prefLen freeLen p : ℕ) (τ : Store)
    (h0 : τ 0 = M) (hp : τ (M + lvJ0) = p) :
    (initInFreeE T prefLen freeLen).eval τ
      = if p < T + prefLen + freeLen then 1 else 0 := by
  unfold initInFreeE
  simp only [Expr.eval, ctlCell_eval, h0, hp]


/-! ## A `unitPos` writer over a word-carrying `Frozen`

Two of the three initial cases write a single positive literal, differing only in
which expression names its variable.  Both may read the staged prefix word, so
neither goes through the control-block leaf combinator; this states the shared
shape once, against the frame condition `writeClauseProg_eval_state` supplies. -/

lemma clauseWriter_unitPos_word (M Jmax prefBase : ℕ) (prefIdx : List ℕ) (aE : Expr)
    (av : ℕ) (pins : List (ℕ × ℕ))
    (hJ : ctlJmax ≤ Jmax) (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ ctlJmax ∧ q.1 ≠ wpJ)
    (hdep : ∀ (bound : ℕ) (σ σ' : Store), σ 0 = M → σ' 0 = M → M + ctlJmax < bound →
      WordBelow prefBase prefIdx.length bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → aE.eval σ' = aE.eval σ)
    (hval : ∀ τ : Store, PinsAndWord M pins prefBase prefIdx τ → τ 0 = M → aE.eval τ = av) :
    ClauseWriter (writeClauseProg wpJ (unitPosLits aE))
      M Jmax wpJ (PinsAndWord M pins prefBase prefIdx) [unitPos av] := by
  intro τ wp hF h0 hw hsep
  have hmax : ctlJmax = 7 := rfl
  have hwp1 : wpJ = 1 := rfl
  have hpins : PinsHold M pins τ := hF.1
  have hword : WordAt τ prefBase prefIdx := hF.2
  have hctlwp : M + ctlJmax < wp := by omega
  have hbelow : WordBelow prefBase prefIdx.length wp := ⟨by omega, by omega⟩
  have hinv : ∀ q ∈ unitPosLits aE, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ := by
    intro q hq σ σ' hσ hσ' hagree
    have hq0 : q = (Expr.const 0, aE) := by
      simpa only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] using hq
    subst hq0
    exact ⟨rfl, hdep wp σ σ' hσ hσ' hctlwp hbelow hagree⟩
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ _ M wp τ (by omega) h0 hw (by omega) hinv
  refine ⟨⟨?_, ?_⟩, w4, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hpin q hq
    rw [w5 (M + q.1) (by omega) (by omega)]
    exact hpins q hq
  · obtain ⟨hlen, hdata⟩ := hword
    exact ⟨by rw [w5 (prefBase - 1) (by omega) (by omega)]; exact hlen,
      fun k hk => by rw [w5 (prefBase + k) (by omega) (by omega)]; exact hdata k hk⟩
  · rw [w3, unitPosLits_length,
      show [unitPos av].length = 1 from rfl, rowTableWidth_singleton, unitPos_len]
  · refine rowsWritten_singleton _ wp _ ?_ ?_ ?_
    · rw [w1, unitPosLits_length, unitPos_len]
    · intro k hk
      rw [unitPos_len] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [(w2 0 (by rw [unitPosLits_length]; omega)).1, unitPosLits_get0]
      rfl
    · intro k hk
      rw [unitPos_len] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [(w2 0 (by rw [unitPosLits_length]; omega)).2, unitPosLits_get0, unitPos_var0]
      exact hval τ hF h0
  · intro r hr1 hr2
    exact w5 r hr1 (by rcases hr2 with h | h <;> omega)

/-! ## Run-time initial-family parameters -/

/-- Placement of the five initial-family parameter cells. -/
structure InitParamPlacement
    (Jmax wReg tReg fReg plReg pbReg : ℕ) : Prop where
  ctl_le : ctlJmax ≤ Jmax
  w_min : 15 ≤ wReg
  w_t : wReg < tReg
  t_f : tReg < fReg
  f_pl : fReg < plReg
  pl_pb : plReg < pbReg
  pb_le : pbReg ≤ Jmax

def initWReg : ℕ := 15
def initTReg : ℕ := 16
def initFreeLenReg : ℕ := 17
def initPrefLenReg : ℕ := 18
def initPrefBaseReg : ℕ := 19
def initParamJmax : ℕ := 19

lemma init_param_fixed_placement :
    InitParamPlacement initParamJmax initWReg initTReg initFreeLenReg
      initPrefLenReg initPrefBaseReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initParamJmax, initWReg, initTReg, initFreeLenReg, initPrefLenReg,
      initPrefBaseReg, ctlJmax]

lemma init_param_placement_satisfiable :
    ∃ Jmax wReg tReg fReg plReg pbReg,
      InitParamPlacement Jmax wReg tReg fReg plReg pbReg :=
  ⟨initParamJmax, initWReg, initTReg, initFreeLenReg, initPrefLenReg,
    initPrefBaseReg, init_param_fixed_placement⟩

lemma init_param_full_placement_satisfiable :
    ∃ M Jmax prefBase, ∃ prefIdx : List ℕ,
      InitParamPlacement Jmax initWReg initTReg initFreeLenReg initPrefLenReg
          initPrefBaseReg ∧
        M + initPrefBaseReg + 1 < prefBase ∧
        prefBase + prefIdx.length ≤ M + Jmax := by
  refine ⟨0, 22, 21, [0], ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [initWReg, initTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg,
        ctlJmax]
  · simp [initPrefBaseReg]
  · simp

/-- Parameter pins at the entry to either initial-family loop. -/
def initParamPins0 (wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase : ℕ) :
    List (ℕ × ℕ) :=
  [(wReg, W), (tReg, T), (fReg, freeLen), (plReg, prefLen), (pbReg, prefBase)]

/-- Parameter pins together with the window or suffix counter. -/
def initParamPins1
    (wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p : ℕ) :
    List (ℕ × ℕ) :=
  (lvJ0, p) :: initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase

/-- Initial-family parameters together with the staged prefix word. -/
def InitParamFrozen (M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase : ℕ)
    (prefIdx : List ℕ) (τ : Store) : Prop :=
  PinsAndWord M
    (initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase)
    prefBase prefIdx τ

lemma init_param_pins0_ok
    (Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase iJ : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hiJctl : iJ ≤ ctlJmax) :
    ∀ q ∈ initParamPins0 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  have hw := hplace.w_min
  have hwt := hplace.w_t
  have htf := hplace.t_f
  have hfp := hplace.f_pl
  have hpb := hplace.pl_pb
  have hle := hplace.pb_le
  simp only [initParamPins0, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, by omega, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩
  · exact ⟨by omega, hle, by unfold ctlJmax at hiJctl; omega,
      by unfold wpJ; omega⟩

lemma init_param_pins1_ok
    (Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p iJ : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hiJctl : iJ ≤ ctlJmax) (hne : lvJ0 ≠ iJ) :
    ∀ q ∈ initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p,
      1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ iJ ∧ q.1 ≠ wpJ := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by unfold lvJ0; omega,
      Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hplace.ctl_le, hne,
      by unfold lvJ0 wpJ; omega⟩
  · exact init_param_pins0_ok Jmax wReg tReg fReg plReg pbReg W T freeLen prefLen
      prefBase iJ hplace hiJctl q hq

lemma init_param_reg_frame
    (M Jmax wReg tReg fReg plReg pbReg j : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (hj : j = wReg ∨ j = tReg ∨ j = fReg ∨ j = plReg ∨ j = pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  rcases hplace with ⟨_, _, _, _, _, _, _⟩
  exact ctlCell_frame M Jmax j (by omega) (by omega) (by unfold wpJ; omega)
    σ σ' hσ hσ' hagree

lemma init_param_ctl_frame (M Jmax j : ℕ) (hJ : ctlJmax ≤ Jmax)
    (hj : j = lvJ0 ∨ j = litJ ∨ j = tmpJ)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ k, 1 ≤ k → k ≤ Jmax → k ≠ wpJ → σ' (M + k) = σ (M + k)) :
    (ctlCell j).eval σ' = (ctlCell j).eval σ := by
  rcases hj with rfl | rfl | rfl
  · exact ctlCell_frame M Jmax lvJ0 (by unfold lvJ0; omega)
      (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
      (by unfold lvJ0 wpJ; omega) σ σ' hσ hσ' hagree
  · exact ctlCell_frame M Jmax litJ (by unfold litJ; omega)
      (Nat.le_trans (by unfold litJ ctlJmax; omega) hJ)
      (by unfold litJ wpJ; omega) σ σ' hσ hσ' hagree
  · exact ctlCell_frame M Jmax tmpJ (by unfold tmpJ; omega)
      (Nat.le_trans (by unfold tmpJ ctlJmax; omega) hJ)
      (by unfold tmpJ wpJ; omega) σ σ' hσ hσ' hagree

/-- A word read whose base and length are read from fixed parameter cells. -/
def wordReadEParam (baseReg lenReg blank : ℕ) (kE : Expr) : Expr :=
  .add
    (.mul (.lt kE (ctlCell lenReg))
      (.regInd (.add (ctlCell baseReg) (.mul (.lt kE (ctlCell lenReg)) kE))))
    (.mul (.sub (.const 1) (.lt kE (ctlCell lenReg))) (.const blank))

lemma word_read_e_param_eval (σ : Store) (base blank baseReg lenReg : ℕ)
    (xs : List ℕ) (kE : Expr)
    (hbase : (ctlCell baseReg).eval σ = base)
    (hlen : (ctlCell lenReg).eval σ = xs.length) (hw : WordAt σ base xs) :
    (wordReadEParam baseReg lenReg blank kE).eval σ = xs.getD (kE.eval σ) blank := by
  obtain ⟨_, hdata⟩ := hw
  unfold wordReadEParam
  simp only [Expr.eval, hbase, hlen]
  by_cases h : kE.eval σ < xs.length
  · rw [ite_eq_left h]
    simp only [Nat.one_mul]
    rw [hdata (kE.eval σ) h]
    have heq : xs.getD (kE.eval σ) 0 = xs.getD (kE.eval σ) blank := by
      rw [List.getD_eq_getElem xs 0 h, List.getD_eq_getElem xs blank h]
    omega
  · rw [ite_eq_right h]
    have hout : xs.getD (kE.eval σ) blank = blank :=
      List.getD_eq_default xs blank (by omega)
    rw [hout]
    omega

/-- A signed word lookup with a run-time base and length. -/
def symbolAtEParam (baseReg lenReg blank : ℕ) (pE qE : Expr) : Expr :=
  .add
    (.mul (.sub (.const 1) (.lt pE qE))
      (wordReadEParam baseReg lenReg blank (.sub pE qE)))
    (.mul (.lt pE qE) (.const blank))

lemma symbol_at_e_param_eval (σ : Store) (base blank baseReg lenReg : ℕ)
    (xs : List ℕ) (pE qE : Expr)
    (hbase : (ctlCell baseReg).eval σ = base)
    (hlen : (ctlCell lenReg).eval σ = xs.length) (hw : WordAt σ base xs) :
    (symbolAtEParam baseReg lenReg blank pE qE).eval σ
      = natInitSymbol blank xs ((pE.eval σ : ℤ) - (qE.eval σ : ℤ)) := by
  rw [natInitSymbol_sub]
  unfold symbolAtEParam
  simp only [Expr.eval]
  by_cases h : pE.eval σ < qE.eval σ
  · rw [ite_eq_left h, ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right h, ite_eq_left (by omega)]
    have hread := word_read_e_param_eval σ base blank baseReg lenReg xs (.sub pE qE)
      hbase hlen hw
    simp only [Expr.eval] at hread
    rw [hread]
    omega

def initCellEParam (n m wReg : ℕ) (aE : Expr) : Expr :=
  denseCellE (.const n) (ctlCell wReg) (.const m) (.const 0) (ctlCell lvJ0) aE

def initStateEParam (n m wReg startState : ℕ) : Expr :=
  denseStateE (.const n) (ctlCell wReg) (.const m) (.const 0) (.const startState)

def initHeadEParam (n m wReg tReg : ℕ) : Expr :=
  denseHeadE (.const n) (ctlCell wReg) (.const m) (.const 0)
    (ctlCell tReg)

def initBlankCellEParam (n m wReg blank : ℕ) : Expr :=
  initCellEParam n m wReg (.const blank)

def initPrefixCellStagedEParam (n m wReg : ℕ) : Expr :=
  initCellEParam n m wReg (ctlCell tmpJ)

def initPrefixSymbolEParam (tReg plReg pbReg blank : ℕ) : Expr :=
  symbolAtEParam pbReg plReg blank (ctlCell lvJ0) (ctlCell tReg)

def initInPrefixEParam (tReg plReg : ℕ) : Expr :=
  .lt (ctlCell lvJ0) (.add (ctlCell tReg) (ctlCell plReg))

def initInFreeEParam (tReg plReg fReg : ℕ) : Expr :=
  .lt (ctlCell lvJ0)
    (.add (.add (ctlCell tReg) (ctlCell plReg)) (ctlCell fReg))

lemma init_state_e_param_frame (M Jmax n m wReg tReg fReg plReg pbReg startState : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initStateEParam n m wReg startState).eval σ'
      = (initStateEParam n m wReg startState).eval σ := by
  unfold initStateEParam
  rw [denseStateE_eval, denseStateE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
    (Or.inl rfl) σ σ' hσ hσ' hagree]

lemma init_head_e_param_frame (M Jmax n m wReg tReg fReg plReg pbReg : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initHeadEParam n m wReg tReg).eval σ' = (initHeadEParam n m wReg tReg).eval σ := by
  unfold initHeadEParam
  rw [denseHeadE_eval, denseHeadE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg tReg hplace
      (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree]

lemma init_blank_cell_e_param_frame (M Jmax n m wReg tReg fReg plReg pbReg blank : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initBlankCellEParam n m wReg blank).eval σ'
      = (initBlankCellEParam n m wReg blank).eval σ := by
  unfold initBlankCellEParam initCellEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree]

lemma init_prefix_cell_staged_e_param_frame
    (M Jmax n m wReg tReg fReg plReg pbReg : ℕ)
    (hplace : InitParamPlacement Jmax wReg tReg fReg plReg pbReg)
    (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (initPrefixCellStagedEParam n m wReg).eval σ'
      = (initPrefixCellStagedEParam n m wReg).eval σ := by
  unfold initPrefixCellStagedEParam initCellEParam
  rw [denseCellE_eval, denseCellE_eval]
  simp only [Expr.eval]
  rw [init_param_reg_frame M Jmax wReg tReg fReg plReg pbReg wReg hplace
      (Or.inl rfl) σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax lvJ0 hplace.ctl_le (Or.inl rfl)
      σ σ' hσ hσ' hagree,
    init_param_ctl_frame M Jmax tmpJ hplace.ctl_le (Or.inr (Or.inr rfl))
      σ σ' hσ hσ' hagree]

lemma init_state_e_param_value
    (M n W m wReg tReg fReg plReg pbReg T freeLen prefLen prefBase startState : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase
      prefIdx τ) (h0 : τ 0 = M) :
    (initStateEParam n m wReg startState).eval τ
      = (denseLayout n W m).state 0 startState := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ (by simp [initParamPins0]) hF.1 h0
  unfold initStateEParam
  rw [denseStateE_eval, eW]
  simp [Expr.eval]

lemma init_head_e_param_value
    (M n W m wReg tReg fReg plReg pbReg T freeLen prefLen prefBase : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : InitParamFrozen M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase
      prefIdx τ) (h0 : τ 0 = M) :
    (initHeadEParam n m wReg tReg).eval τ
      = (denseLayout n W m).head 0 (originIdx T) := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ (by simp [initParamPins0]) hF.1 h0
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ (by simp [initParamPins0]) hF.1 h0
  unfold initHeadEParam
  rw [denseHeadE_eval, eW, eT]
  simp [Expr.eval, originIdx]

lemma init_blank_cell_e_param_value
    (M n W m wReg tReg fReg plReg pbReg T freeLen prefLen prefBase blank p : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initBlankCellEParam n m wReg blank).eval τ
      = (denseLayout n W m).cell 0 p blank := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  unfold initBlankCellEParam initCellEParam
  rw [denseCellE_eval, eW, ep]
  simp [Expr.eval]

lemma init_prefix_cell_staged_e_param_value
    (M n W m wReg tReg fReg plReg pbReg T freeLen prefLen prefBase a p : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      ((tmpJ, a) ::
        initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initPrefixCellStagedEParam n m wReg).eval τ
      = (denseLayout n W m).cell 0 p a := by
  have eW : (ctlCell wReg).eval τ = W :=
    ctlCell_eval_of_pin M _ wReg W τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  have ea : (ctlCell tmpJ).eval τ = a :=
    ctlCell_eval_of_pin M _ tmpJ a τ (by simp) hF.1 h0
  unfold initPrefixCellStagedEParam initCellEParam
  rw [denseCellE_eval, eW, ep, ea]
  simp [Expr.eval]

lemma init_prefix_symbol_e_param_value
    (M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase blank p : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) (hlen : prefLen = prefIdx.length) :
    (initPrefixSymbolEParam tReg plReg pbReg blank).eval τ
      = natInitSymbol blank prefIdx (idxToPos T p) := by
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL0 : (ctlCell plReg).eval τ = prefLen :=
    ctlCell_eval_of_pin M _ plReg prefLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL : (ctlCell plReg).eval τ = prefIdx.length := by rw [eL0, hlen]
  have eB : (ctlCell pbReg).eval τ = prefBase :=
    ctlCell_eval_of_pin M _ pbReg prefBase τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  have hsym := symbol_at_e_param_eval τ prefBase blank pbReg plReg prefIdx
    (ctlCell lvJ0) (ctlCell tReg) eB eL hF.2
  simp only [ep, eT] at hsym
  simpa [initPrefixSymbolEParam, idxToPos] using hsym

lemma init_in_prefix_e_param_eval
    (M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initInPrefixEParam tReg plReg).eval τ = if p < T + prefLen then 1 else 0 := by
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL : (ctlCell plReg).eval τ = prefLen :=
    ctlCell_eval_of_pin M _ plReg prefLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  simp [initInPrefixEParam, Expr.eval, eT, eL, ep]

lemma init_in_free_e_param_eval
    (M wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p : ℕ)
    (prefIdx : List ℕ) (τ : Store)
    (hF : PinsAndWord M
      (initParamPins1 wReg tReg fReg plReg pbReg W T freeLen prefLen prefBase p)
      prefBase prefIdx τ) (h0 : τ 0 = M) :
    (initInFreeEParam tReg plReg fReg).eval τ
      = if p < T + prefLen + freeLen then 1 else 0 := by
  have eT : (ctlCell tReg).eval τ = T :=
    ctlCell_eval_of_pin M _ tReg T τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eF : (ctlCell fReg).eval τ = freeLen :=
    ctlCell_eval_of_pin M _ fReg freeLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have eL : (ctlCell plReg).eval τ = prefLen :=
    ctlCell_eval_of_pin M _ plReg prefLen τ
      (by simp [initParamPins1, initParamPins0]) hF.1 h0
  have ep : (ctlCell lvJ0).eval τ = p :=
    ctlCell_eval_of_pin M _ lvJ0 p τ (by simp [initParamPins1]) hF.1 h0
  simp [initInFreeEParam, Expr.eval, eT, eF, eL, ep]

lemma clause_writer_io_stage_word_value (M Jmax reg base av : ℕ) (xs : List ℕ)
    (pins : List (ℕ × ℕ)) (aE : Expr)
    (hreg1 : 1 ≤ reg) (hregJ : reg ≤ Jmax) (hregwp : reg ≠ wpJ)
    (hpin : ∀ q ∈ pins, q.1 ≠ reg) (hbase : M + reg + 1 < base)
    (hval : ∀ τ : Store, PinsAndWord M pins base xs τ → τ 0 = M → aE.eval τ = av) :
    ClauseWriterIO (ctlAssign reg aE) M Jmax wpJ
      (PinsAndWord M pins base xs) (PinsAndWord M ((reg, av) :: pins) base xs) [] := by
  intro τ wp hF h0 hw _
  have heval : (ctlAssign reg aE).eval τ = writeReg τ (M + reg) av := by
    unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0, hval τ hF h0]
  rw [heval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [writeReg_same]
      · rw [writeReg_diff τ (M + reg) av (M + q.1) (by have := hpin q hq; omega)]
        exact hF.1 q hq
    · obtain ⟨hlen, hdata⟩ := hF.2
      exact ⟨by rw [writeReg_diff τ (M + reg) av (base - 1) (by omega)]; exact hlen,
        fun k hk => by
          rw [writeReg_diff τ (M + reg) av (base + k) (by omega)]
          exact hdata k hk⟩
  · rw [writeReg_diff τ (M + reg) av 0 (by omega), h0]
  · rw [List.length_nil, rowTableWidth_zero, Nat.add_zero,
      writeReg_diff τ (M + reg) av (M + wpJ) (by omega), hw]
  · exact rowsWritten_nil _ wp
  · intro r _ hr
    rw [writeReg_diff]
    unfold CtlFree at hr
    omega

lemma clause_writer_unit_pos_word_wide
    (M Jmax prefBase : ℕ) (prefIdx : List ℕ) (aE : Expr) (av : ℕ)
    (pins : List (ℕ × ℕ))
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < prefBase)
    (hfit : prefBase + prefIdx.length ≤ M + Jmax)
    (hpin : ∀ q ∈ pins, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ wpJ)
    (hdep : ∀ (bound : ℕ) (σ σ' : Store), σ 0 = M → σ' 0 = M →
      M + Jmax < bound → WordBelow prefBase prefIdx.length bound →
      (∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) → aE.eval σ' = aE.eval σ)
    (hval : ∀ τ : Store, PinsAndWord M pins prefBase prefIdx τ →
      τ 0 = M → aE.eval τ = av) :
    ClauseWriter (writeClauseProg wpJ (unitPosLits aE)) M Jmax wpJ
      (PinsAndWord M pins prefBase prefIdx) [unitPos av] := by
  intro τ wp hF h0 hw hsep
  have hwpJle : wpJ ≤ Jmax := Nat.le_trans wpJ_le hJ
  have hwpsep : M + wpJ < wp := by omega
  have hlen_ne_ctl : prefBase - 1 ≠ M + wpJ :=
    word_len_disjoint_ctl M prefBase (M + wpJ) hbase (by unfold wpJ ctlJmax; omega)
  have hdata_ne_ctl : ∀ k, k < prefIdx.length → prefBase + k ≠ M + wpJ :=
    fun k _ => word_disjoint_ctl M prefBase (M + wpJ) k hbase
      (by unfold wpJ ctlJmax; omega)
  have hctl_free_ne : ∀ r, CtlFree M Jmax r → r ≠ M + wpJ := by
    intro r hr
    unfold CtlFree at hr
    rcases hr with hr | hr
    · intro heq
      rw [heq] at hr
      have := wpJ_pos
      omega
    · intro heq
      rw [heq] at hr
      omega
  have hbelow : WordBelow prefBase prefIdx.length wp := ⟨by omega, by omega⟩
  have hinv : ∀ q ∈ unitPosLits aE, ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ := by
    intro q hq σ σ' hσ hσ' hagree
    have hq0 : q = (Expr.const 0, aE) := by
      simpa only [unitPosLits, List.mem_cons, List.not_mem_nil, or_false] using hq
    subst hq0
    exact ⟨rfl, hdep wp σ σ' hσ hσ' hsep hbelow hagree⟩
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ _ M wp τ wpJ_pos h0 hw hwpsep hinv
  refine ⟨⟨?_, ?_⟩, w4, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨_, hq2, hq3⟩ := hpin q hq
    rw [w5 (M + q.1) (by omega) (by omega)]
    exact hF.1 q hq
  · obtain ⟨hlen, hdata⟩ := hF.2
    have hlen_lt : prefBase - 1 < wp := by omega
    exact ⟨by rw [w5 (prefBase - 1) hlen_lt hlen_ne_ctl]; exact hlen,
      fun k hk => by
        have hdata_lt : prefBase + k < wp := by omega
        rw [w5 (prefBase + k) hdata_lt (hdata_ne_ctl k hk)]
        exact hdata k hk⟩
  · rw [w3, unitPosLits_length,
      show [unitPos av].length = 1 from rfl, rowTableWidth_singleton, unitPos_len]
  · refine rowsWritten_singleton _ wp _ ?_ ?_ ?_
    · rw [w1, unitPosLits_length, unitPos_len]
    · intro k hk
      rw [unitPos_len] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [(w2 0 (by rw [unitPosLits_length]; omega)).1, unitPosLits_get0]
      rfl
    · intro k hk
      rw [unitPos_len] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [(w2 0 (by rw [unitPosLits_length]; omega)).2, unitPosLits_get0, unitPos_var0]
      exact hval τ hF h0
  · intro r hr1 hr2
    exact w5 r hr1 (hctl_free_ne r hr2)

end NPComplete.CookLevin

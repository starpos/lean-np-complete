module

public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelopeAgg
public import NPComplete.CookLevin.ReductionProg.GeneratorScanFree
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedLoad
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedRowCount

/-!
# The top-level `ProgramBoundedIn` for `generatorProgFromBits`

`generatorProgFromBits` is `.seq (loadWordsProg ...) generatorProg`, and
`generatorProg` is itself `.seq (generatorSetupProg ...) (.seq
(.assign 0 (setupME p)) (.seq (clauseCountProg ...) (tableWriterProgParam ...)))`, so
`ProgramBoundedIn` splits into five per-stage obligations at the stores each earlier
stage hands the next (`ProgramBoundedIn.seq`'s own unfolding). The load stage
(`programBoundedIn_loadWordsProg_envB_any`, proved in this file) and the
first two generator stages (`programBoundedIn_generatorSetupProg`,
`programBoundedIn_setupME_assign`) ask for nothing beyond `ProgramBoundedIn`,
and their arithmetic hypotheses are discharged directly against `envB` here
and in `GeneratorBoundedLoad.lean`.

The final writer stage's contract, `clauseWriterBounded_tableWriterProgParam`, is not
merely `ProgramBoundedIn` at its entry — it *demands* `StoreValuesLe S` and
`TightCells K M` at the entry store, and returns them (together with
`ProgramBoundedIn`) at the exit. Discharging those two at the store the load
and setup stages produce from `bitInputStore bits` is the real content of this
file: `post_setup_tightCells` / `post_setup_storeValuesLe` below take a general
entry store `σ` (not fixed to `bitInputStore bits`) together with a frame
hypothesis on the twelve control cells / a `StoreValuesLe` hypothesis on `σ`,
and produce the corresponding facts on the post-setup store, by pins
(`GeneratorProg.lean`'s `generator_setup_prog_scalar_pins` /
`generator_setup_prog_layout_pins`) on the twelve written cells and frame
(`paramSetupWrites_frame`) on everything else. The load stage discharges those
two hypotheses at `σ := (loadWordsProg ...).eval (bitInputStore bits)`:
`loadWordsProg_untouched_ctl_zero` shows the control cells survive the load
untouched (they sit far above every cell the load stage ever writes), and
`program_eval_storeValuesLe` transports `StoreValuesLe` from
`bitInputStore bits` through the load stage's own `ProgramBoundedIn`.

`generatorProgFromBits` composes `loadWordsProg` with `generatorProg`.  The
load stage writes the certificate prefix and transition-table columns before
`tableWriterProgParam` runs, establishing the `GeneratorWordsAt` data required
by `GeneratorTableFrozen`.  The load-stage frame and `StoreValuesLe` results
supply the writer's entry contract.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-! ## `setupM p N` dominates `N` and the raw entry frame -/

/-- `setupM p time d allowedIdx N = (2 * N + 3 + p.eval N)^3 + 30
      + (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
          allowedIdx.length).eval N` strictly exceeds `N`: the cube of a quantity
    at least `N` is at least that quantity, so the workspace base sits clear of
    every input cell. -/
lemma setupM_gt (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) (N : ℕ) :
    N < setupM p time d allowedIdx N := by
  unfold setupM setupSpan
  have h1 : (0 : ℕ) ≤ p.eval N := Nat.zero_le _
  have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
    allowedIdx.length).eval N := Nat.zero_le _
  nlinarith [sq_nonneg (2 * N + 3 + p.eval N)]

/-- Any cell not among the twelve registers `generatorSetupProg` followed by
    `.assign 0 (setupME p)` writes survives the whole handoff unchanged: neither
    `setupPairs` nor `generatorLayoutPairs` targets it (`paramSetupWrites_frame`
    applied twice), and the final `.assign 0` only ever touches register `0`. -/
lemma handoff_frame_ne (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (σ : Store) (N r : ℕ) (h0 : σ 0 = N) (hr0 : r ≠ 0)
    (hr1 : r ≠ setupM p time d allowedIdx N + 1)
    (hr14 : r ≠ setupM p time d allowedIdx N + 14)
    (hr15 : r ≠ setupM p time d allowedIdx N + 15)
    (hr16 : r ≠ setupM p time d allowedIdx N + 16)
    (hr17 : r ≠ setupM p time d allowedIdx N + 17)
    (hr18 : r ≠ setupM p time d allowedIdx N + 18)
    (hr19 : r ≠ setupM p time d allowedIdx N + 19)
    (hr20 : r ≠ setupM p time d allowedIdx N + 20)
    (hr21 : r ≠ setupM p time d allowedIdx N + 21)
    (hr22 : r ≠ setupM p time d allowedIdx N + 22)
    (hr23 : r ≠ setupM p time d allowedIdx N + 23)
    (hr24 : r ≠ setupM p time d allowedIdx N + 24) :
    (Program.assign 0 (setupME p time d allowedIdx)).eval
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ) r
      = σ r := by
  rw [generator_handoff_frame p time d allowedIdx _ r hr0]
  unfold generatorSetupProg
  rw [eval_seq]
  have hσ1 : (setupProg p time d allowedIdx).eval σ r = σ r := by
    apply paramSetupWrites_frame (setupME p time d allowedIdx) (setupME_reg0 p time d allowedIdx)
      (setupPairs p time d allowedIdx) σ r (setupPairs_pos p time d allowedIdx)
    intro j hj
    rw [setupME_eval p time d allowedIdx σ N h0]
    simp only [setupPairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [persistWReg, persistTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg,
        transKindBaseReg, transArg1BaseReg, transArg2BaseReg, acceptOutBaseReg]
  have hτ0 : (setupProg p time d allowedIdx).eval σ 0 = N := by rw [setup_prog_zero, h0]
  apply Eq.trans _ hσ1
  apply paramSetupWrites_frame (setupME p time d allowedIdx) (setupME_reg0 p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx)
    _ r (generator_layout_pairs_pos p time d allowedIdx outIdx)
  intro j hj
  rw [setupME_eval p time d allowedIdx _ N hτ0]
  simp only [generatorLayoutPairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [initPrefBaseReg, transKindBaseReg, transArg1BaseReg, transArg2BaseReg,
      acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]

/-! ## The setup pins and cell 0, gathered -/

/-- Values of the twelve cells written by `generatorSetupProg`, plus cell `0`
    written by the following `.assign 0`, for any entry store with
    `σ 0 = N`.  The pin lemmas depend only on `σ 0`, so each conjunct follows
    by composing `generator_handoff_pins` with the scalar and layout pin lemmas. -/
lemma post_setup_pins (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    let ρ := (Program.assign 0 (setupME p time d allowedIdx)).eval
      ((generatorSetupProg p time d allowedIdx outIdx).eval σ)
    ρ 0 = setupM p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + wpJ) = generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + emTblJ) = generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + generatorTableBaseReg) =
      generatorTableBase p time d allowedIdx outIdx N ∧
    ρ (setupM p time d allowedIdx N + persistWReg) = (cookWindowPoly p time).eval N ∧
    ρ (setupM p time d allowedIdx N + persistTReg) = (timePoly p time).eval N ∧
    ρ (setupM p time d allowedIdx N + initFreeLenReg) = p.eval N ∧
    ρ (setupM p time d allowedIdx N + initPrefLenReg) = generatorPrefLen N ∧
    ρ (setupM p time d allowedIdx N + initPrefBaseReg) = generatorPrefBase p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + transKindBaseReg) = generatorKindBase p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + transArg1BaseReg)
      = generatorArg1Base p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + transArg2BaseReg)
      = generatorArg2Base p time d allowedIdx N ∧
    ρ (setupM p time d allowedIdx N + acceptOutBaseReg) = generatorOutBase p time d allowedIdx N
      := by
  intro ρ
  have hM1 : (1 : ℕ) ≤ setupM p time d allowedIdx N := by
    have := setupM_gt p time d allowedIdx N; omega
  have hsPins := generator_setup_prog_scalar_pins p time d allowedIdx outIdx σ N h0
  have hlPins := generator_setup_prog_layout_pins p time d allowedIdx outIdx σ N h0
  have hρs : PinsHold (setupM p time d allowedIdx N) (generatorScalarPins p time N) ρ :=
    generator_handoff_pins p time d allowedIdx _ (setupM p time d allowedIdx N) _ hM1
      (fun q hq => by
        simp only [generatorScalarPins, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;>
          simp [persistWReg, persistTReg, initFreeLenReg, initPrefLenReg]) hsPins
  have hρl : PinsHold (setupM p time d allowedIdx N)
      (generatorLayoutPins p time d allowedIdx outIdx N) ρ :=
    generator_handoff_pins p time d allowedIdx _ (setupM p time d allowedIdx N) _ hM1
      (fun q hq => by
        simp only [generatorLayoutPins, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg, transArg2BaseReg,
            acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]) hlPins
  have hτ0 : (generatorSetupProg p time d allowedIdx outIdx).eval σ 0 = N := by
    rw [generator_setup_prog_zero]; exact h0
  refine ⟨generator_handoff_zero p time d allowedIdx _ N hτ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact hρl (wpJ, generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (emTblJ, generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (generatorTableBaseReg, generatorTableBase p time d allowedIdx outIdx N)
      (by simp [generatorLayoutPins])
  · exact hρs (persistWReg, (cookWindowPoly p time).eval N) (by simp [generatorScalarPins])
  · exact hρs (persistTReg, (timePoly p time).eval N) (by simp [generatorScalarPins])
  · exact hρs (initFreeLenReg, p.eval N) (by simp [generatorScalarPins])
  · exact hρs (initPrefLenReg, generatorPrefLen N) (by simp [generatorScalarPins])
  · exact hρl (initPrefBaseReg, generatorPrefBase p time d allowedIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (transKindBaseReg, generatorKindBase p time d allowedIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (transArg1BaseReg, generatorArg1Base p time d allowedIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (transArg2BaseReg, generatorArg2Base p time d allowedIdx N)
      (by simp [generatorLayoutPins])
  · exact hρl (acceptOutBaseReg, generatorOutBase p time d allowedIdx N)
      (by simp [generatorLayoutPins])

/-- `bitInputStore bits` is bounded by any `S` at least `1` and at least
    `bits.length`: cell `0` holds `bits.length`, every other cell holds `0` or
    `1`. -/
lemma bitInputStore_storeValuesLe (bits : Bits) (S : ℕ)
    (h1 : 1 ≤ S) (hlen : bits.length ≤ S) : StoreValuesLe S (bitInputStore bits) := by
  intro r
  match r with
  | 0 => simpa [bitInputStore] using hlen
  | r + 1 =>
    simp only [bitInputStore]
    split <;> omega

/-! ## `TightCells` and `StoreValuesLe` after the setup and handoff

Both take a general entry store `σ` (not fixed to `bitInputStore bits`), with
the frame/`StoreValuesLe` responsibility for the untouched cells pushed onto
the caller as a hypothesis: the setup layer's `ProgramBoundedIn`
(`GeneratorBoundedSetup.lean`) does not state either condition; these lemmas establish
them for the post-setup store.  The load-stage caller below
discharges the two hypotheses at `σ := (loadWordsProg ...).eval
(bitInputStore bits)` via `loadWordsProg_untouched_ctl_zero` and
`program_eval_storeValuesLe`. -/

/-- The control and parameter cells `M+2 .. M+24` all hold values `≤ envK` on
    the store `generatorSetupProg` then `.assign 0 (setupME p)` produce from
    any entry `σ` with `σ 0 = N`, given the twelve untouched cells (`M+2 ..
    M+13`) are already `≤ envK` there (`hUntouched`). Cells `M+14 .. M+24`
    hold exactly the scalar parameters / staged-word base addresses
    `post_setup_pins` gives, each of which `envK_ge_*` bounds — independent of
    `hUntouched`. -/
lemma post_setup_tightCells (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hUntouched : ∀ j, 2 ≤ j → j ≤ 13 →
      σ (setupM p time d allowedIdx N + j) ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    TightCells (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (setupM p time d allowedIdx N)
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval σ)) := by
  have hpins := post_setup_pins p time d allowedIdx outIdx σ N h0
  simp only at hpins
  obtain ⟨_, hwp, hemt, htblreg, hW, hT, hfree, hpreflen, hprefbase, hkind, harg1, harg2, hout⟩ :=
    hpins
  have huntouched : ∀ j, 2 ≤ j → j ≤ 13 →
      (Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval σ)
        (setupM p time d allowedIdx N + j) ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) := by
    intro j hj2 hj13
    rw [handoff_frame_ne p time d allowedIdx outIdx σ N (setupM p time d allowedIdx N + j) h0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hUntouched j hj2 hj13
  intro j hj2 hj24
  interval_cases j
  · exact huntouched 2 (by omega) (by omega)
  · exact huntouched 3 (by omega) (by omega)
  · exact huntouched 4 (by omega) (by omega)
  · exact huntouched 5 (by omega) (by omega)
  · exact huntouched 6 (by omega) (by omega)
  · exact huntouched 7 (by omega) (by omega)
  · exact huntouched 8 (by omega) (by omega)
  · exact huntouched 9 (by omega) (by omega)
  · exact huntouched 10 (by omega) (by omega)
  · exact huntouched 11 (by omega) (by omega)
  · exact huntouched 12 (by omega) (by omega)
  · exact huntouched 13 (by omega) (by omega)
  · rw [show setupM p time d allowedIdx N + (14 : ℕ)
      = setupM p time d allowedIdx N + emTblJ from rfl, hemt]
    exact envK_ge_tableBase p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (15 : ℕ)
      = setupM p time d allowedIdx N + persistWReg from rfl, hW]
    exact envK_ge_window p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (16 : ℕ)
      = setupM p time d allowedIdx N + persistTReg from rfl, hT]
    exact envK_ge_time p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (17 : ℕ)
      = setupM p time d allowedIdx N + initFreeLenReg from rfl, hfree]
    exact envK_ge_freeLen p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (18 : ℕ)
      = setupM p time d allowedIdx N + initPrefLenReg from rfl, hpreflen]
    exact envK_ge_prefLen p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (19 : ℕ)
      = setupM p time d allowedIdx N + initPrefBaseReg from rfl, hprefbase]
    exact envK_ge_prefBase p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (20 : ℕ)
      = setupM p time d allowedIdx N + transKindBaseReg from rfl, hkind]
    exact envK_ge_kindBase p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (21 : ℕ)
      = setupM p time d allowedIdx N + transArg1BaseReg from rfl, harg1]
    exact envK_ge_arg1Base p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (22 : ℕ)
      = setupM p time d allowedIdx N + transArg2BaseReg from rfl, harg2]
    exact envK_ge_arg2Base p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (23 : ℕ)
      = setupM p time d allowedIdx N + acceptOutBaseReg from rfl, hout]
    exact envK_ge_outBase p time d prefIdx allowedIdx outIdx N
  · rw [show setupM p time d allowedIdx N + (24 : ℕ)
      = setupM p time d allowedIdx N + generatorTableBaseReg from rfl, htblreg]
    exact envK_ge_tableBase p time d prefIdx allowedIdx outIdx N

/-- Every cell of the post-setup store holds a value `≤ envB`, given the
    entry store `σ` already does (`hσB`): the twelve written cells hold
    `envK`-bounded quantities (`post_setup_pins` + `envK_ge_*`, transported to
    `envB` via `envB_ge_envK`), and every other cell survives from `σ`
    unchanged (`handoff_frame_ne`), where it is `≤ envB` by `hσB`. -/
lemma post_setup_storeValuesLe (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N)
    (hσB : StoreValuesLe (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) σ) :
    StoreValuesLe (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval σ)) := by
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  have hK1 : (1 : ℕ) ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) :=
    envK_ge_one p time d prefIdx allowedIdx outIdx N
  have hpins := post_setup_pins p time d allowedIdx outIdx σ N h0
  simp only at hpins
  obtain ⟨h0', hwp, hemt, htblreg, hW, hT, hfree, hpreflen, hprefbase, hkind, harg1, harg2, hout⟩ :=
    hpins
  intro r
  by_cases hr0 : r = 0
  · subst hr0; rw [h0']
    have := envK_ge_setupM p time d prefIdx allowedIdx outIdx N
    omega
  by_cases hr1 : r = setupM p time d allowedIdx N + wpJ
  · subst hr1; rw [hwp]
    have := envK_ge_tableBase p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr14 : r = setupM p time d allowedIdx N + 14
  · subst hr14
    rw [show setupM p time d allowedIdx N + (14 : ℕ)
      = setupM p time d allowedIdx N + emTblJ from rfl, hemt]
    have := envK_ge_tableBase p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr15 : r = setupM p time d allowedIdx N + 15
  · subst hr15
    rw [show setupM p time d allowedIdx N + (15 : ℕ)
      = setupM p time d allowedIdx N + persistWReg from rfl, hW]
    have := envK_ge_window p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr16 : r = setupM p time d allowedIdx N + 16
  · subst hr16
    rw [show setupM p time d allowedIdx N + (16 : ℕ)
      = setupM p time d allowedIdx N + persistTReg from rfl, hT]
    have := envK_ge_time p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr17 : r = setupM p time d allowedIdx N + 17
  · subst hr17
    rw [show setupM p time d allowedIdx N + (17 : ℕ)
      = setupM p time d allowedIdx N + initFreeLenReg from rfl,
      hfree]
    have := envK_ge_freeLen p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr18 : r = setupM p time d allowedIdx N + 18
  · subst hr18
    rw [show setupM p time d allowedIdx N + (18 : ℕ)
      = setupM p time d allowedIdx N + initPrefLenReg from rfl,
      hpreflen]
    have := envK_ge_prefLen p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr19 : r = setupM p time d allowedIdx N + 19
  · subst hr19
    rw [show setupM p time d allowedIdx N + (19 : ℕ)
      = setupM p time d allowedIdx N + initPrefBaseReg from rfl,
      hprefbase]
    have := envK_ge_prefBase p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr20 : r = setupM p time d allowedIdx N + 20
  · subst hr20
    rw [show setupM p time d allowedIdx N + (20 : ℕ)
      = setupM p time d allowedIdx N + transKindBaseReg from rfl,
      hkind]
    have := envK_ge_kindBase p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr21 : r = setupM p time d allowedIdx N + 21
  · subst hr21
    rw [show setupM p time d allowedIdx N + (21 : ℕ)
      = setupM p time d allowedIdx N + transArg1BaseReg from rfl,
      harg1]
    have := envK_ge_arg1Base p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr22 : r = setupM p time d allowedIdx N + 22
  · subst hr22
    rw [show setupM p time d allowedIdx N + (22 : ℕ)
      = setupM p time d allowedIdx N + transArg2BaseReg from rfl,
      harg2]
    have := envK_ge_arg2Base p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr23 : r = setupM p time d allowedIdx N + 23
  · subst hr23
    rw [show setupM p time d allowedIdx N + (23 : ℕ)
      = setupM p time d allowedIdx N + acceptOutBaseReg from rfl,
      hout]
    have := envK_ge_outBase p time d prefIdx allowedIdx outIdx N; omega
  by_cases hr24 : r = setupM p time d allowedIdx N + 24
  · subst hr24
    rw [show setupM p time d allowedIdx N + (24 : ℕ) =
      setupM p time d allowedIdx N + generatorTableBaseReg from rfl, htblreg]
    have := envK_ge_tableBase p time d prefIdx allowedIdx outIdx N; omega
  · rw [handoff_frame_ne p time d allowedIdx outIdx σ N r h0 hr0
      hr1 hr14 hr15 hr16 hr17 hr18 hr19 hr20 hr21 hr22 hr23 hr24]
    exact hσB r

/-! ## Stage 1 and stage 2 are unconditionally bounded at `envB`

Neither stage needs `GeneratorTableFrozen`; both close purely from `envK_ge_*`
/ `envB_ge_envK` against `programBoundedIn_setupProg` /
`programBoundedIn_generatorLayoutProg` / `programBoundedIn_setupME_assign`
(`GeneratorBoundedSetup.lean`). -/

/-- `setupProg` stays bounded by `envB.eval N` at any store holding `N` at
    register `0`. -/
lemma setupProg_bounded_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (hσ0 : σ 0 = N) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) σ
      (setupProg p time d allowedIdx) := by
  set B := Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) with hB
  apply programBoundedIn_setupProg B N p time d allowedIdx σ hσ0
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · have hspanM : setupSpan p N ≤ setupM p time d allowedIdx N := by
      unfold setupM
      unfold setupSpan
      have h1 : (0 : ℕ) ≤ p.eval N := Nat.zero_le _
      have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N := Nat.zero_le _
      nlinarith [sq_nonneg (2 * N + 3 + p.eval N)]
    have hK := envK_ge_setupM p time d prefIdx allowedIdx outIdx N
    have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · have hK := envK_ge_two_n p time d prefIdx allowedIdx outIdx N
    have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega
  · have hK := envK_eval_ge_setupM_add_70 p time d prefIdx allowedIdx outIdx N
    have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega

/-- `generatorLayoutProg` stays bounded by `envB.eval N` at any store holding
    `N` at register `0`. -/
lemma layout_prog_bounded_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (hσ0 : σ 0 = N) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) σ
      (generatorLayoutProg p time d allowedIdx outIdx) := by
  set B := Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) with hB
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  apply programBoundedIn_generatorLayoutProg B N p time d allowedIdx outIdx σ hσ0
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · have hspanM : setupSpan p N ≤ setupM p time d allowedIdx N := by
      unfold setupM
      unfold setupSpan
      have h1 : (0 : ℕ) ≤ p.eval N := Nat.zero_le _
      have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N := Nat.zero_le _
      nlinarith [sq_nonneg (2 * N + 3 + p.eval N)]
    have hK := envK_ge_setupM p time d prefIdx allowedIdx outIdx N
    omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · have hK := envK_eval_ge_setupM_add_70 p time d prefIdx allowedIdx outIdx N
    omega
  · have hK := envK_ge_prefBase p time d prefIdx allowedIdx outIdx N
    simp only [generatorPrefBase] at hK ⊢
    omega
  · have hK := envK_ge_two_n p time d prefIdx allowedIdx outIdx N
    omega
  · have hK := envK_ge_kindBase p time d prefIdx allowedIdx outIdx N
    simp only [generatorKindBase, generatorKindOffset, generatorPrefBase] at hK ⊢
    omega
  · have hK := envK_ge_arg1Base p time d prefIdx allowedIdx outIdx N
    simp only [generatorArg1Base, generatorArg1Offset, generatorKindBase] at hK ⊢
    omega
  · have hK := envK_ge_arg2Base p time d prefIdx allowedIdx outIdx N
    simp only [generatorArg2Base, generatorArg2Offset, generatorArg1Base] at hK ⊢
    omega
  · have hK := envK_ge_outBase p time d prefIdx allowedIdx outIdx N
    simp only [generatorOutBase, generatorOutOffset, generatorArg2Base] at hK ⊢
    omega
  · have hK := envK_ge_tableBase p time d prefIdx allowedIdx outIdx N
    simp only [generatorTableBase, generatorJmax, generatorOutOffset, generatorOutBase] at hK ⊢
    omega

/-- Stage 1 (`generatorSetupProg`) stays bounded by `envB.eval N`, composing the
    two lemmas above through `programBoundedIn_generatorSetupProg`. -/
lemma generatorSetupProg_bounded_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (σ : Store) (N : ℕ) (hσ0 : σ 0 = N) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) σ
      (generatorSetupProg p time d allowedIdx outIdx) :=
  programBoundedIn_generatorSetupProg _ N p time d allowedIdx outIdx σ hσ0
    (setupProg_bounded_envB p time d prefIdx allowedIdx outIdx σ N hσ0)
    (fun τ hτ => layout_prog_bounded_envB p time d prefIdx allowedIdx outIdx τ N hτ)

/-- Stage 2 (`.assign 0 (setupME p)`) stays bounded by `envB.eval N` at any
    store holding `N` at register `0` — the only obligation is
    `ExprBoundedIn` on `setupME p`. -/
lemma assign_setupME_bounded_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (τ : Store) (N : ℕ) (hτ0 : τ 0 = N) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) τ
      (Program.assign 0 (setupME p time d allowedIdx)) := by
  set B := Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) with hB
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  have hspanM : setupSpan p N ≤ setupM p time d allowedIdx N := by
    unfold setupM
    unfold setupSpan
    have h1 : (0 : ℕ) ≤ p.eval N := Nat.zero_le _
    have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval N := Nat.zero_le _
    nlinarith [sq_nonneg (2 * N + 3 + p.eval N)]
  have hK := envK_ge_setupM p time d prefIdx allowedIdx outIdx N
  apply programBoundedIn_setupME_assign B p time d allowedIdx τ
  apply exprBoundedIn_setupME B N p time d allowedIdx τ
  · apply exprBoundedIn_setupSpanE B N p τ hτ0
    · rw [hB, envB_eval]; omega
    · rw [hB, envB_eval]; omega
    · rw [hB, envB_eval]; omega
    · omega
  · exact setupSpanE_eval p τ N hτ0
  · exact hτ0
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · rw [hB, envB_eval]; omega
  · omega

/-! ## The load stage: frame lemmas and an envelope-level bound

`GeneratorBoundedLoad.lean` proves `programBoundedIn_loadWordsProg_envB`
(`ProgramBoundedIn` for `loadWordsProg` at `envB`), but only for `bits = b ::
rest`: its proof needs `d.trueIdx ≤ envK`, which holds because `d.trueIdx ∈
prefixWord d (b :: rest)` (`envK_ge_trueIdx`) — a fact that is simply false
for `bits = []`, since `prefixWord d []` never contains `d.trueIdx`. This
section supplies the `bits = []` case directly (the prefix loop runs zero
times, so `d.trueIdx` is never actually written, hence no hypothesis on it is
needed), then combines both cases into `programBoundedIn_loadWordsProg_envB_any`
— unconditional in `bits`, given only the pre-existing list-membership
hypotheses `programBoundedIn_loadWordsProg_envB` already asks for on the table
columns and `outIdx`. Finally, `loadWordsProg_frame_below` /
`loadWordsProg_untouched_ctl_zero` show the load stage never touches the
generator's own control cells `M+2 .. M+24` (they sit strictly below
`generatorPrefBase - 2`, the lowest cell any load-stage write ever reaches),
which is what the vertex needs to transport `TightCells` across the load
stage. -/

/-- `loadPrefixProg` stays bounded by `B` on the empty-bits input, with no
    hypothesis on `d.trueIdx`: the loop runs zero times, so `d.trueIdx` is
    never actually written — only the trailing `d.falseIdx` separator is.
    Mirrors `programBoundedIn_loadPrefixProg` (`GeneratorBoundedLoad.lean`)
    structurally, specialized to `N = 0` where the loop body is vacuous. -/
lemma programBoundedIn_loadPrefixProg_nil (B : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (hprefB : ∀ τ : Store, τ 0 = 0 → ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx))
    (hprefBound : generatorPrefBase p time d allowedIdx 0 ≤ B) (hfB : d.falseIdx ≤ B)
    (h2B : 2 ≤ B) :
    ProgramBoundedIn B (bitInputStore ([] : List Bool)) (loadPrefixProg p time d allowedIdx) := by
  set N := (0 : ℕ)
  have hge := generatorPrefBase_ge p time d allowedIdx N
  set σ := bitInputStore ([] : List Bool) with hσdef
  have hσ0 : σ 0 = N := rfl
  unfold loadPrefixProg
  have hstep0 : ProgramBoundedIn B σ
      (Program.assignInd (loadPrefixCounterE p time d allowedIdx) (Expr.const 0)) :=
    ⟨exprBoundedIn_loadPrefixCounterE B N p time d allowedIdx σ hσ0 (hprefB σ hσ0) hprefBound,
      by simp only [ExprBoundedIn]; omega,
      by rw [loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]; omega⟩
  refine ⟨hstep0, ?_⟩
  simp only [eval_assignInd]
  set σ0 := writeReg σ ((loadPrefixCounterE p time d allowedIdx).eval σ)
    ((Expr.const (0 : ℕ)).eval σ) with hσ0def
  have hσ0_0 : σ0 0 = N := by
    rw [hσ0def, writeReg_diff σ _ _ 0
      (by rw [loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]; omega)]
    exact hσ0
  have hσ0_ctr : σ0 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ0def, loadPrefixCounterE_eval p time d allowedIdx N σ hσ0]
    show writeReg σ (generatorPrefBase p time d allowedIdx N - 2) 0
      (generatorPrefBase p time d allowedIdx N - 2) = 0
    rw [writeReg_same]
  have hforNB : ExprBoundedIn B σ0 (Expr.reg 0) := by simp only [ExprBoundedIn]; omega
  refine ⟨?_, ?_⟩
  · refine ⟨hforNB, ?_⟩
    simp only [Expr.eval, hσ0_0]
    intro m' hm'; omega
  · simp only [eval_forN, Expr.eval, hσ0_0]
    rw [show N = 0 from rfl, loopEval_zero]
    have hwriteB := exprBoundedIn_loadPrefixWriteAddrE B N N p time d allowedIdx σ0 hσ0_0 hσ0_ctr
      (hprefB σ0 hσ0_0) hprefBound (by omega)
    have hwriteEval := loadPrefixWriteAddrE_eval p time d allowedIdx N N σ0 hσ0_0 hσ0_ctr
    have hstepF : ProgramBoundedIn B σ0
        (Program.assignInd (loadPrefixWriteAddrE p time d allowedIdx) (Expr.const d.falseIdx)) :=
      ⟨hwriteB, hfB, by rw [hwriteEval]; omega⟩
    refine ⟨hstepF, ?_⟩
    simp only [eval_assignInd]
    set σ3 := writeReg σ0 ((loadPrefixWriteAddrE p time d allowedIdx).eval σ0)
      ((Expr.const d.falseIdx).eval σ0) with hσ3def
    have hσ3_0 : σ3 0 = N := by
      rw [hσ3def, writeReg_diff σ0 _ _ 0 (by rw [hwriteEval]; omega)]; exact hσ0_0
    exact ⟨exprBoundedIn_loadPrefixLenAddrE B N p time d allowedIdx σ3 hσ3_0
      (hprefB σ3 hσ3_0) hprefBound,
      exprBoundedIn_generatorPrefLenE B N σ3 hσ3_0 (by omega) (by omega),
      by
        have := generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0
        unfold loadPrefixLenAddrE
        simp only [Expr.eval]
        rw [this]; omega⟩

/-- `loadWordsProg` stays bounded by `B` on the empty-bits input, with no
    hypothesis on `d.trueIdx`. Mirrors `programBoundedIn_loadWordsProg`
    (`GeneratorBoundedLoad.lean`), specialized to `N = 0`. -/
lemma programBoundedIn_loadWordsProg_nil (B : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (hB1 : 1 ≤ B)
    (h1p : p.eval 1 ≤ B) (hsp : p.eval 1 ≤ B)
    (hspan : setupSpan p 0 ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hpref30 : setupM p time d allowedIdx 0 + generatorPrefOffset ≤ B)
    (hpref2b : 1 ≤ B)
    (hkindsum : generatorPrefBase p time d allowedIdx 0 + generatorPrefLen 0 + 2 ≤ B)
    (harg1sum : generatorKindBase p time d allowedIdx 0 + (d.table.length + 2) ≤ B)
    (harg2sum : generatorArg1Base p time d allowedIdx 0 + (d.table.length + 2) ≤ B)
    (houtsum : generatorArg2Base p time d allowedIdx 0 + (d.table.length + 2) ≤ B)
    (hfB : d.falseIdx ≤ B)
    (hkindSum : generatorKindBase p time d allowedIdx 0 + (d.table.map transKind).length ≤ B)
    (harg1Sum : generatorArg1Base p time d allowedIdx 0 + (d.table.map transArg1).length ≤ B)
    (harg2Sum : generatorArg2Base p time d allowedIdx 0 + (d.table.map transArg2).length ≤ B)
    (houtSum : generatorOutBase p time d allowedIdx 0 + outIdx.length ≤ B)
    (hkindVB : ∀ k, k < (d.table.map transKind).length → (d.table.map transKind).getD k 0 ≤ B)
    (harg1VB : ∀ k, k < (d.table.map transArg1).length → (d.table.map transArg1).getD k 0 ≤ B)
    (harg2VB : ∀ k, k < (d.table.map transArg2).length → (d.table.map transArg2).getD k 0 ≤ B)
    (houtVB : ∀ k, k < outIdx.length → outIdx.getD k 0 ≤ B) :
    ProgramBoundedIn B (bitInputStore ([] : List Bool))
      (loadWordsProg p time d allowedIdx outIdx) := by
  obtain ⟨hprefB, hkindB, harg1B, harg2B, houtB⟩ :=
    exprBoundedIn_loadWordsProg_bases B 0 p time d allowedIdx h1p hsp (by omega)
      hspan h1e hshifte (by omega) hpref30 hpref2b hkindsum harg1sum harg2sum houtsum
  have h0init : (bitInputStore ([] : List Bool)) 0 = 0 := rfl
  unfold loadWordsProg
  refine ⟨programBoundedIn_loadPrefixProg_nil B p time d allowedIdx hprefB (by omega) hfB
    (by omega), ?_⟩
  have h0mid : (loadPrefixProg p time d allowedIdx).eval (bitInputStore ([] : List Bool)) 0 = 0 :=
    loadPrefixProg_reg0 p time d allowedIdx []
  exact programBoundedIn_loadConstWordsProg B 0 p time d allowedIdx outIdx _ h0mid hB1
    hkindB harg1B harg2B houtB hkindSum harg1Sum harg2Sum houtSum
    hkindVB harg1VB harg2VB houtVB

/-! ## `programBoundedIn_loadWordsProg_envB_nil`, split into three groups

The arithmetic hypotheses of `programBoundedIn_loadWordsProg_nil` are grouped
below.  The three groups separate the address and sum bounds, the envelope
and list-length bounds, and the list-value bounds. -/

/-- Group A: the hypotheses through `houtsum` needed by
    `programBoundedIn_loadWordsProg_nil`, at `B := envB.eval 0`. -/
lemma load_words_prog_nil_addr_hyps_a (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    1 ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    p.eval 1 ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    p.eval 1 ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    setupSpan p 0 ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval 1 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval 1 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    setupM p time d allowedIdx 0 + generatorPrefOffset ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    (1:ℕ) ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorPrefBase p time d allowedIdx 0 + generatorPrefLen 0 + 2 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorKindBase p time d allowedIdx 0 + (d.table.length + 2) ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorArg1Base p time d allowedIdx 0 + (d.table.length + 2) ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorArg2Base p time d allowedIdx 0 + (d.table.length + 2) ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hK1 := envK_ge_one p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · have hspanM : setupSpan p 0 ≤ setupM p time d allowedIdx 0 := by
      unfold setupM setupSpan
      have h1 : (0 : ℕ) ≤ p.eval 0 := Nat.zero_le _
      have h2 : (0 : ℕ) ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval 0 := Nat.zero_le _
      nlinarith [sq_nonneg (2 * 0 + 3 + p.eval 0)]
    have hK := envK_ge_setupM p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · rw [envB_eval]; omega
  · rw [envB_eval]; omega
  · have hK := envK_eval_ge_setupM_add_70 p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    simp only [generatorPrefOffset]
    omega
  · have hK := envK_ge_two_n p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · have heq : generatorKindBase p time d allowedIdx 0
        = generatorPrefBase p time d allowedIdx 0 + generatorPrefLen 0 + 2 := by
      unfold generatorKindBase generatorKindOffset generatorPrefBase; ring
    have hK := envK_ge_kindBase p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · have heq : generatorArg1Base p time d allowedIdx 0
        = generatorKindBase p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorArg1Base generatorArg1Offset generatorKindBase; ring
    have hK := envK_ge_arg1Base p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · have heq : generatorArg2Base p time d allowedIdx 0
        = generatorArg1Base p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorArg2Base generatorArg2Offset generatorArg1Base; ring
    have hK := envK_ge_arg2Base p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · have heq : generatorOutBase p time d allowedIdx 0
        = generatorArg2Base p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorOutBase generatorOutOffset generatorArg2Base; ring
    have hK := envK_ge_outBase p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega

/-- Group B: `hfB` and the four `*Sum` bounds (with the `List.map` lengths),
    at `B := envB.eval 0`. -/
lemma load_words_prog_nil_addr_hyps_b (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    d.falseIdx ≤ Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorKindBase p time d allowedIdx 0 + (d.table.map transKind).length ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorArg1Base p time d allowedIdx 0 + (d.table.map transArg1).length ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorArg2Base p time d allowedIdx 0 + (d.table.map transArg2).length ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) ∧
    generatorOutBase p time d allowedIdx 0 + outIdx.length ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hK := envK_ge_falseIdx p time d [] allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · have heq : generatorArg1Base p time d allowedIdx 0
        = generatorKindBase p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorArg1Base generatorArg1Offset generatorKindBase; ring
    have hK := envK_ge_arg1Base p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    simp only [List.length_map]
    omega
  · have heq : generatorArg2Base p time d allowedIdx 0
        = generatorArg1Base p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorArg2Base generatorArg2Offset generatorArg1Base; ring
    have hK := envK_ge_arg2Base p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    simp only [List.length_map]
    omega
  · have heq : generatorOutBase p time d allowedIdx 0
        = generatorArg2Base p time d allowedIdx 0 + (d.table.length + 2) := by
      unfold generatorOutBase generatorOutOffset generatorArg2Base; ring
    have hK := envK_ge_outBase p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    simp only [List.length_map]
    omega
  · have hK := envK_ge_outBase p time d (prefixWord d []) allowedIdx outIdx 0
    have hKB := envB_ge_env_ksq p time d (prefixWord d []) allowedIdx outIdx 0
    have hK2 : 2 ≤ Polynomial.eval (0:ℕ) (envK p time d (prefixWord d []) allowedIdx outIdx) :=
      envK_ge_two p time d (prefixWord d []) allowedIdx outIdx 0
    have hlen : outIdx.length ≤ Polynomial.eval (0:ℕ) (envK p time d (prefixWord d [])
      allowedIdx outIdx) := by rw [envK_eval]; unfold envKConst; omega
    nlinarith [sq_nonneg (Polynomial.eval (0:ℕ) (envK p time d (prefixWord d [])
      allowedIdx outIdx))]

/-- Group C: the four list-value bounds (`hkindVB`/`harg1VB`/`harg2VB`/
    `houtVB`), at `B := envB.eval 0`. -/
lemma load_words_prog_nil_addr_hyps_c (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    (∀ k, k < (d.table.map transKind).length → (d.table.map transKind).getD k 0 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx)) ∧
    (∀ k, k < (d.table.map transArg1).length → (d.table.map transArg1).getD k 0 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx)) ∧
    (∀ k, k < (d.table.map transArg2).length → (d.table.map transArg2).getD k 0 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx)) ∧
    (∀ k, k < outIdx.length → outIdx.getD k 0 ≤
      Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    have hmem : (d.table.map transKind).getD k 0 ∈ d.table.map transKind := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_kind (d := d) (prefIdx := prefixWord d []) (allowedIdx := allowedIdx)
      (outIdx := outIdx) hmem
    have h2 := envIdxMax_le_envKConst d (prefixWord d []) allowedIdx outIdx
    have hKeval : (d.table.map transKind).getD k 0 ≤
        Polynomial.eval (0:ℕ) (envK p time d (prefixWord d []) allowedIdx outIdx) := by
      rw [envK_eval]; omega
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · intro k hk
    have hmem : (d.table.map transArg1).getD k 0 ∈ d.table.map transArg1 := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_arg1 (d := d) (prefIdx := prefixWord d []) (allowedIdx := allowedIdx)
      (outIdx := outIdx) hmem
    have h2 := envIdxMax_le_envKConst d (prefixWord d []) allowedIdx outIdx
    have hKeval : (d.table.map transArg1).getD k 0 ≤
        Polynomial.eval (0:ℕ) (envK p time d (prefixWord d []) allowedIdx outIdx) := by
      rw [envK_eval]; omega
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · intro k hk
    have hmem : (d.table.map transArg2).getD k 0 ∈ d.table.map transArg2 := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_arg2 (d := d) (prefIdx := prefixWord d []) (allowedIdx := allowedIdx)
      (outIdx := outIdx) hmem
    have h2 := envIdxMax_le_envKConst d (prefixWord d []) allowedIdx outIdx
    have hKeval : (d.table.map transArg2).getD k 0 ≤
        Polynomial.eval (0:ℕ) (envK p time d (prefixWord d []) allowedIdx outIdx) := by
      rw [envK_eval]; omega
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega
  · intro k hk
    have hmem : outIdx.getD k 0 ∈ outIdx := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have h1 := envIdxMax_ge_out (d := d) (prefIdx := prefixWord d []) (allowedIdx := allowedIdx)
      (outIdx := outIdx) hmem
    have h2 := envIdxMax_le_envKConst d (prefixWord d []) allowedIdx outIdx
    have hKeval : outIdx.getD k 0 ≤
        Polynomial.eval (0:ℕ) (envK p time d (prefixWord d []) allowedIdx outIdx) := by
      rw [envK_eval]; omega
    have hKB := envB_ge_envK p time d (prefixWord d []) allowedIdx outIdx 0
    omega

/-- `loadWordsProg` at `bits = []`, bounded by `envB.eval 0`: unconditional in
    `d`, `allowedIdx`, `outIdx`. Assembled from the three groups above. -/
lemma programBoundedIn_loadWordsProg_envB_nil (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) :
    ProgramBoundedIn (Polynomial.eval (0:ℕ) (envB p time d (prefixWord d []) allowedIdx outIdx))
      (bitInputStore ([] : List Bool)) (loadWordsProg p time d allowedIdx outIdx) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    load_words_prog_nil_addr_hyps_a p time d allowedIdx outIdx
  obtain ⟨h13, h14, h15, h16, h17⟩ := load_words_prog_nil_addr_hyps_b p time d allowedIdx outIdx
  obtain ⟨h18, h19, h20, h21⟩ := load_words_prog_nil_addr_hyps_c p time d allowedIdx outIdx
  exact programBoundedIn_loadWordsProg_nil _ p time d allowedIdx outIdx h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

/-- `loadWordsProg` stays bounded by `envB.eval N` on `bitInputStore bits`, for
    ANY `bits` (empty included): the empty case is
    `programBoundedIn_loadWordsProg_envB_nil` above (needs no `d.trueIdx`
    bound), the nonempty case is `programBoundedIn_loadWordsProg_envB`
    (`GeneratorBoundedLoad.lean`, needs `d.trueIdx ≤ envK`, discharged by
    `envK_ge_trueIdx` since `d.trueIdx ∈ prefixWord d (b :: rest)`). -/
lemma programBoundedIn_loadWordsProg_envB_any (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hkindVB : ∀ k, k < (d.table.map transKind).length →
      (d.table.map transKind).getD k 0 ≤
        Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx))
    (harg1VB : ∀ k, k < (d.table.map transArg1).length →
      (d.table.map transArg1).getD k 0 ≤
        Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx))
    (harg2VB : ∀ k, k < (d.table.map transArg2).length →
      (d.table.map transArg2).getD k 0 ≤
        Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx))
    (houtVB : ∀ k, k < outIdx.length →
      outIdx.getD k 0 ≤
        Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx)) :
    ProgramBoundedIn (Polynomial.eval bits.length
        (envB p time d (prefixWord d bits) allowedIdx outIdx)) (bitInputStore bits)
      (loadWordsProg p time d allowedIdx outIdx) := by
  cases bits with
  | nil => exact programBoundedIn_loadWordsProg_envB_nil p time d allowedIdx outIdx
  | cons b rest =>
    apply programBoundedIn_loadWordsProg_envB
    · exact envK_ge_trueIdx p time d b rest allowedIdx outIdx (b :: rest).length
    · exact envK_ge_falseIdx p time d (b :: rest) allowedIdx outIdx (b :: rest).length
    · exact hkindVB
    · exact harg1VB
    · exact harg2VB
    · exact houtVB

/-- `loadPrefixProg` leaves every cell strictly below the prefix's own
    counter cell (`generatorPrefBase - 2`) unchanged — generalizing
    `loadPrefixProg_input_frame` (`GeneratorLoadPrefix.lean`, which only
    covers the raw input region `1 .. bits.length`) to every untouched cell,
    control cells included. -/
lemma loadPrefixProg_frame_below (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ)
    (bits : List Bool) (r : ℕ) (hr : r < generatorPrefBase p time d allowedIdx bits.length - 2) :
    (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) r = bitInputStore bits r := by
  set N := bits.length with hN
  have hb := generatorPrefBase_ge p time d allowedIdx N
  have h0init : (bitInputStore bits) 0 = N := rfl
  unfold loadPrefixProg
  rw [eval_seq, eval_assignInd]
  set σ1 : Store := writeReg (bitInputStore bits)
    ((loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits))
    ((Expr.const 0).eval (bitInputStore bits)) with hσ1def
  have haddr1 : (loadPrefixCounterE p time d allowedIdx).eval (bitInputStore bits)
      = generatorPrefBase p time d allowedIdx N - 2 :=
    loadPrefixCounterE_eval p time d allowedIdx N (bitInputStore bits) h0init
  have hval1 : (Expr.const (0 : ℕ)).eval (bitInputStore bits) = 0 := rfl
  have hσ1_0 : σ1 0 = N := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 0 (by omega)]
    exact h0init
  have hσ1_ctr : σ1 (generatorPrefBase p time d allowedIdx N - 2) = 0 := by
    rw [hσ1def, haddr1, hval1, writeReg_same]
  have hσ1_input : ∀ j, j < N → σ1 (j + 1) = if bits.getD j false then 1 else 0 := by
    intro j hj
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 (j + 1) (by omega)]
    show (if bits.getD j false then 1 else 0) = _
    rfl
  have hσ1_r : σ1 r = bitInputStore bits r := by
    rw [hσ1def, haddr1, hval1]
    rw [writeReg_diff (bitInputStore bits) _ 0 r (by omega)]
  rw [eval_seq, eval_forN]
  simp only [Expr.eval]
  rw [hσ1_0]
  set result : Store := loopEval (loadPrefixStep p time d allowedIdx) N σ1 with hresultdef
  obtain ⟨hres0, hresctr, _, hresframe⟩ :=
    load_prefix_loop_inv p time d allowedIdx N bits hN σ1 hσ1_0 hσ1_ctr hσ1_input N (le_refl N)
  have hresr : result r = σ1 r := hresframe r (by omega)
  rw [eval_seq]
  simp only [eval_assignInd]
  have haddr3 : (loadPrefixWriteAddrE p time d allowedIdx).eval result
      = generatorPrefBase p time d allowedIdx N + 2 * N :=
    loadPrefixWriteAddrE_eval p time d allowedIdx N N result hres0 hresctr
  have hval3 : (Expr.const d.falseIdx).eval result = d.falseIdx := rfl
  rw [haddr3, hval3]
  set σ3 : Store := writeReg result (generatorPrefBase p time d allowedIdx N + 2 * N) d.falseIdx
    with hσ3def
  have hσ3_r : σ3 r = result r := by
    rw [hσ3def, writeReg_diff result _ _ r (by omega)]
  have hσ3_0 : σ3 0 = N := by
    rw [hσ3def, writeReg_diff result _ _ 0 (by omega)]
    exact hres0
  have haddr4 : (loadPrefixLenAddrE p time d allowedIdx).eval σ3
      = generatorPrefBase p time d allowedIdx N - 1 := by
    unfold loadPrefixLenAddrE
    simp only [Expr.eval]
    rw [generator_pref_base_e_eval p time d allowedIdx σ3 N hσ3_0]
  rw [haddr4]
  rw [writeReg_diff _ _ _ r (by omega)]
  rw [hσ3_r, hresr, hσ1_r]

/-- `loadWordsProg` leaves every cell strictly below `generatorPrefBase - 2`
    unchanged: neither `loadPrefixProg` nor `loadConstWordsProg` writes there,
    the former by `loadPrefixProg_frame_below`, the latter because its own
    floor sits at `generatorKindBase - 1`, strictly above
    `generatorPrefBase - 2`. -/
lemma loadWordsProg_frame_below (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : List Bool) (r : ℕ)
    (hr : r < generatorPrefBase p time d allowedIdx bits.length - 2) :
    (loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits) r
      = bitInputStore bits r := by
  set N := bits.length with hN
  unfold loadWordsProg
  rw [eval_seq]
  have h0 : (loadPrefixProg p time d allowedIdx).eval (bitInputStore bits) 0 = N :=
    loadPrefixProg_reg0 p time d allowedIdx bits
  have hrk : r < generatorKindBase p time d allowedIdx N - 1 := by
    unfold generatorKindBase generatorKindOffset generatorPrefLen generatorPrefOffset
      generatorPrefBase generatorPrefOffset at *
    omega
  rw [loadConstWordsProg_preserves_below p time d allowedIdx outIdx _ N r h0 hrk]
  exact loadPrefixProg_frame_below p time d allowedIdx bits r hr

/-- Every control cell `M+2 .. M+24` is `0` after the load stage, on
    `bitInputStore bits`: these cells sit strictly below
    `generatorPrefBase - 2` (`loadWordsProg_frame_below` applies), so they
    survive the load unchanged, and `bitInputStore` itself is `0` there
    (`bitInputStore_eq_zero_of_ge_inputEnd`, since `setupM p N > N`). -/
lemma loadWordsProg_untouched_ctl_zero (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) (j : ℕ) (hj2 : 2 ≤ j) (hj13 : j ≤ 24) :
    (loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)
      (setupM p time d allowedIdx bits.length + j) = 0 := by
  have hM := lt_setupM p time d allowedIdx bits.length
  have hlt : setupM p time d allowedIdx bits.length + j
      < generatorPrefBase p time d allowedIdx bits.length - 2 := by
    unfold generatorPrefBase generatorPrefOffset
    omega
  rw [loadWordsProg_frame_below p time d allowedIdx outIdx bits _ hlt]
  exact bitInputStore_eq_zero_of_ge_inputEnd bits _ (by omega)

/-! ## Bounds for descriptor scalars and lists

`clauseWriterBounded_tableWriterProgParam` needs `≤ K` and `≤ B` bounds for
the descriptor's scalar fields and elements of its table columns and index
lists.  `GeneratorEnvelopeAgg.lean` bounds the generator's layout addresses;
the lemmas below bound descriptor data in the same envelope, unconditionally
for any `d`, `allowedIdx`, and `outIdx`. -/

lemma envK_ge_numStates (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.numStates ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_numLetters (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.numLetters ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_blankIdx (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.blankIdx ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_startState (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.startState ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_table_len (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    d.table.length ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_halt_len (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤
      (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_allowed_len (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    allowedIdx.length + 1 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_outLen (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    outIdx.length ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; unfold envKConst; omega

lemma envK_ge_time_succ (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (timePoly p time).eval N + 1 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; omega

lemma envK_ge_mem_pref (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ prefIdx) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_pref (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_allowed (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ allowedIdx) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_allowed (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_out (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ outIdx) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_out (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_kind (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ d.table.map transKind) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_kind (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_arg1 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ d.table.map transArg1) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_arg1 (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_arg2 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ) (hv : v ∈ d.table.map transArg2) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_arg2 (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envK_ge_mem_halt (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N v : ℕ)
    (hv : v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0)) :
    v ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 := envIdxMax_ge_halt (d := d) (prefIdx := prefIdx) (allowedIdx := allowedIdx)
    (outIdx := outIdx) hv
  have h2 := envIdxMax_le_envKConst d prefIdx allowedIdx outIdx
  omega

lemma envB_ge_envK_succ (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envK p time d prefIdx allowedIdx outIdx).eval N + 1 ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  have hsq := envB_ge_env_ksq p time d prefIdx allowedIdx outIdx N
  have hK2 : 2 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N :=
    envK_ge_two p time d prefIdx allowedIdx outIdx N
  set K := (envK p time d prefIdx allowedIdx outIdx).eval N
  nlinarith [sq_nonneg K]

lemma envB_ge_K_numLetters_plus (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envK p time d prefIdx allowedIdx outIdx).eval N * d.numLetters +
      (envK p time d prefIdx allowedIdx outIdx).eval N +
      (envK p time d prefIdx allowedIdx outIdx).eval N ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  have hK1 : (1 : ℕ) ≤ (envK p time d prefIdx allowedIdx outIdx).eval N :=
    envK_ge_one p time d prefIdx allowedIdx outIdx N
  have hsq := envB_ge_env_ksq p time d prefIdx allowedIdx outIdx N
  set K := (envK p time d prefIdx allowedIdx outIdx).eval N
  nlinarith [sq_nonneg K, hK1, hsq]

/-- The stage-3 writer's own `GeneratorPlacement`, at `prefIdx := prefixWord d
    bits` matching the load stage's own indexing. -/
lemma generatorPlacement_from_bits (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    GeneratorPlacement (setupM p time d allowedIdx bits.length)
      (generatorJmax d outIdx bits.length)
      (generatorPrefLen bits.length) (generatorPrefBase p time d allowedIdx bits.length)
      (generatorKindBase p time d allowedIdx bits.length)
      (generatorArg1Base p time d allowedIdx bits.length)
      (generatorArg2Base p time d allowedIdx bits.length)
      (generatorOutBase p time d allowedIdx bits.length)
      d (prefixWord d bits) outIdx :=
  generator_placement_of_layout p time d allowedIdx outIdx (prefixWord d bits) bits.length
    (by rw [prefixWord_length]; rfl)

/-! ## Discharging `clauseWriterBounded_tableWriterProgParam` at the envelope

The three groups below cover the `K ≤ S ≤ B` nesting and placement/`Jmax`
facts, descriptor scalar bounds, and the list-membership and length obligations
for the clause families and staged-word bases, all at `S := B := envB.eval N`.
The groups contain independent facts; the final assembly
(`clauseWriterBounded_envB_tableWriterProgParam`) destructures their conjunctions
and applies `clauseWriterBounded_tableWriterProgParam`. -/

/-- Group 1: the `K ≤ S ≤ B` nesting, `Jmax`, and the placement contract, at
    `S := B := envB.eval N` and `prefIdx := prefixWord d bits`. -/
lemma stage3_nesting_hyps_b (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    let N := bits.length
    let prefIdx := prefixWord d bits
    GeneratorPlacement (setupM p time d allowedIdx N) (generatorJmax d outIdx N)
        (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
        (generatorKindBase p time d allowedIdx N)
        (generatorArg1Base p time d allowedIdx N) (generatorArg2Base p time d allowedIdx N)
        (generatorOutBase p time d allowedIdx N)
        d prefIdx outIdx ∧
      24 ≤ generatorJmax d outIdx N ∧
      1 ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) + 1 ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      setupM p time d allowedIdx N + 24 ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      2 ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      3 ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      4 ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) := by
  intro N prefIdx
  refine ⟨generatorPlacement_from_bits p time d allowedIdx outIdx bits, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · unfold generatorJmax generatorOutOffset generatorArg2Offset generatorArg1Offset
      generatorKindOffset generatorPrefLen generatorPrefOffset
    omega
  · exact envK_ge_one p time d prefIdx allowedIdx outIdx N
  · exact envB_ge_envK_succ p time d prefIdx allowedIdx outIdx N
  · have h1 := envK_eval_ge_setupM_add_70 p time d prefIdx allowedIdx outIdx N
    have h2 := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega
  · exact envB_ge_envK p time d prefIdx allowedIdx outIdx N
  · have := envK_ge_two p time d prefIdx allowedIdx outIdx N
    have := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega
  · have := envK_ge_thirty p time d prefIdx allowedIdx outIdx N
    have := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega
  · have := envK_ge_thirty p time d prefIdx allowedIdx outIdx N
    have := envB_ge_envK p time d prefIdx allowedIdx outIdx N
    omega

/-- Group 2: the descriptor's own scalar fields against `K`, and their lift to
    `B` where the writer needs it, at `S := B := envB.eval N`. -/
lemma stage3_scalar_hyps_b (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    let N := bits.length
    let prefIdx := prefixWord d bits
    d.numStates + 1 ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      d.numLetters + 1 ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      d.numLetters ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      (cookWindowPoly p time).eval N ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      (cookWindowPoly p time).eval N ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      (timePoly p time).eval N + 1 ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      d.blankIdx ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      p.eval N ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      d.startState ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) * d.numLetters +
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) +
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      d.numStates ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) := by
  intro N prefIdx
  have h1 := envK_ge_numStates p time d prefIdx allowedIdx outIdx N
  have h2 := envK_ge_numLetters p time d prefIdx allowedIdx outIdx N
  have h3 := envB_ge_envK_succ p time d prefIdx allowedIdx outIdx N
  have h4 := envK_ge_window p time d prefIdx allowedIdx outIdx N
  refine ⟨by omega, by omega, h1, h2, by omega, h4, by omega,
    envK_ge_time_succ p time d prefIdx allowedIdx outIdx N,
    envK_ge_blankIdx p time d prefIdx allowedIdx outIdx N,
    envK_ge_freeLen p time d prefIdx allowedIdx outIdx N,
    envK_ge_startState p time d prefIdx allowedIdx outIdx N,
    envB_ge_K_numLetters_plus p time d prefIdx allowedIdx outIdx N, by omega⟩

/-- Group 3: every list-membership / length obligation the five clause
    families and the staged-word bases need — the table columns, `prefIdx`,
    `allowedIdx`, `outIdx`, and the halt-state list — at `S := B := envB.eval
    N`. -/
lemma stage3_list_hyps_b (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    let N := bits.length
    let prefIdx := prefixWord d bits
    (d.table.map transKind).length ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      (d.table.map transArg1).length ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      (d.table.map transArg2).length ≤
        Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      (∀ v ∈ d.table.map transKind, v ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      (∀ v ∈ d.table.map transArg1, v ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      (∀ v ∈ d.table.map transArg2, v ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      generatorKindBase p time d allowedIdx N ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      generatorArg1Base p time d allowedIdx N ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      generatorArg2Base p time d allowedIdx N ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      (∀ v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0),
        v ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      generatorOutBase p time d allowedIdx N ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      (∀ v ∈ prefIdx, v ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      (∀ v ∈ allowedIdx, v ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      allowedIdx.length + 1 ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ∧
      (∀ v ∈ outIdx, v ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) ∧
      outIdx.length ≤ Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) ∧
      generatorOutBase p time d allowedIdx N + outIdx.length + 1 ≤
        Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) := by
  intro N prefIdx
  have h1 := envK_ge_table_len p time d prefIdx allowedIdx outIdx N
  have h2 := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  have h3 := envK_ge_outLen p time d prefIdx allowedIdx outIdx N
  refine ⟨by simp only [List.length_map]; omega, by simp only [List.length_map]; omega,
    by simp only [List.length_map]; omega,
    fun v hv => envK_ge_mem_kind p time d prefIdx allowedIdx outIdx N v hv,
    fun v hv => envK_ge_mem_arg1 p time d prefIdx allowedIdx outIdx N v hv,
    fun v hv => envK_ge_mem_arg2 p time d prefIdx allowedIdx outIdx N v hv,
    envK_ge_kindBase p time d prefIdx allowedIdx outIdx N,
    envK_ge_arg1Base p time d prefIdx allowedIdx outIdx N,
    envK_ge_arg2Base p time d prefIdx allowedIdx outIdx N,
    fun v hv => envK_ge_mem_halt p time d prefIdx allowedIdx outIdx N v hv,
    envK_ge_halt_len p time d prefIdx allowedIdx outIdx N,
    envK_ge_outBase p time d prefIdx allowedIdx outIdx N,
    fun v hv => envK_ge_mem_pref p time d prefIdx allowedIdx outIdx N v hv,
    fun v hv => envK_ge_mem_allowed p time d prefIdx allowedIdx outIdx N v hv,
    envK_ge_allowed_len p time d prefIdx allowedIdx outIdx N,
    fun v hv => envK_ge_mem_out p time d prefIdx allowedIdx outIdx N v hv,
    by omega, envK_ge_out_base_len p time d prefIdx allowedIdx outIdx N⟩

/-- Stage 3's writer, `tableWriterProgParam`, discharged at the aggregated
    envelope with `S := B := envB.eval N` (not `envS`): every hypothesis
    `clauseWriterBounded_tableWriterProgParam` needs at `S = B` is discharged
    by the "at `envB`" family (`uniqEnv_envB` etc., already proved), so this
    choice avoids ever needing `StoreValuesLe envS` — only `StoreValuesLe
    envB`, which `post_setup_storeValuesLe` above already supplies. Assembled
    from the three groups above (`stage3_nesting_hyps_b` /
    `stage3_scalar_hyps_b` / `stage3_list_hyps_b`), each independently
    unconditional, so no side condition on `p`/`time`/`d`/`allowedIdx`/`outIdx`
    beyond `bits` remains. -/
lemma clauseWriterBounded_envB_tableWriterProgParam (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    ClauseWriterBounded (tableWriterProgParam d allowedIdx outIdx)
      (setupM p time d allowedIdx bits.length) (generatorJmax d outIdx bits.length) wpJ
      (Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx))
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (Polynomial.eval bits.length (envWid p time d (prefixWord d bits) allowedIdx outIdx))
      (GeneratorTableFrozen (setupM p time d allowedIdx bits.length)
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length) (p.eval bits.length) (generatorPrefLen bits.length)
        (generatorPrefBase p time d allowedIdx bits.length) (prefixWord d bits)
        (generatorKindBase p time d allowedIdx bits.length)
        (d.table.map transKind) (generatorArg1Base p time d allowedIdx bits.length)
        (d.table.map transArg1)
        (generatorArg2Base p time d allowedIdx bits.length) (d.table.map transArg2)
        (generatorOutBase p time d allowedIdx bits.length) outIdx) := by
  set N := bits.length with hN
  set prefIdx := prefixWord d bits with hprefIdx
  obtain ⟨hplace, hJ, hK1, hKB, hMB, hKS, h2B, h3B, h4B⟩ :=
    stage3_nesting_hyps_b p time d allowedIdx outIdx bits
  obtain ⟨hnB, hmB, hnCK, hmCK, hmCB, hWK, hWB, hTK1, hblank, hfreeK, hstart, hK1mC, hnCB⟩ :=
    stage3_scalar_hyps_b p time d allowedIdx outIdx bits
  obtain ⟨hlenkB, hlen1B, hlen2B, hallowedk, hallowed1, hallowed2, hkindBaseK, harg1BaseK,
    harg2BaseK, hqsK, hqslenK, houtBaseK, hprefAllowed, hallowedK, hallowedLen, hallowedB,
    houtLenB, htableBaseK⟩ := stage3_list_hyps_b p time d allowedIdx outIdx bits
  have henvUB := uniqEnv_envB p time d prefIdx allowedIdx outIdx N hnCK hmCK
  have henvIB := initEnv_envB p time d prefIdx allowedIdx outIdx N hnCK hmCK
  have henvTB := transEnv_envB p time d prefIdx allowedIdx outIdx N hnCK hmCK
  have henvPB := persistEnv_envB p time d prefIdx allowedIdx outIdx N hnCK hmCK
  have henvAB := acceptEnv_envB p time d prefIdx allowedIdx outIdx N hnCK hmCK
  have hwid := envWid_ge_stage_wid p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
    rfl hWK hTK1 hfreeK
  have hfam := clauseWriterBounded_tableWriterProgParam (setupM p time d allowedIdx N)
    (generatorJmax d outIdx N)
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
    (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
    (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
    (generatorKindBase p time d allowedIdx N)
    (generatorArg1Base p time d allowedIdx N) (generatorArg2Base p time d allowedIdx N)
    (generatorOutBase p time d allowedIdx N)
    d prefIdx allowedIdx outIdx hplace hJ hK1 hMB hKB hKS (le_refl _) h2B h3B h4B
    henvUB henvUB henvIB henvIB henvTB henvTB henvPB henvPB henvAB henvAB
    hnB hmB hnCK hmCK hmCB hWK hWB hTK1 hblank hallowedK hallowedLen hprefAllowed
    hfreeK hstart hK1mC hlenkB hlen1B hlen2B hallowedk hallowed1 hallowed2
    hkindBaseK harg1BaseK harg2BaseK hnCB hallowedB houtLenB hqsK hqslenK houtBaseK htableBaseK
  exact clauseWriterBounded_of_wid_le (tableWriterProgParam d allowedIdx outIdx)
    (setupM p time d allowedIdx N) (generatorJmax d outIdx N) wpJ
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
    (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) _
    (Polynomial.eval N (envWid p time d prefIdx allowedIdx outIdx)) _ hwid hfam

/-! ## The top-level vertex

`ProgramBoundedIn` splits `generatorProgFromBits` into five per-stage
obligations: the load stage (`loadWordsProg`), then `generatorProg`'s setup,
workspace, clause-count, and table-writer stages. The load stage is bounded unconditionally by
`programBoundedIn_loadWordsProg_envB_any` (proved in this file, handling
both empty and nonempty `bits`); the setup and workspace stages close unconditionally at
`envB` as before. The clause-count stage computes the row count while staying under
`envB`, and the final writer closes here because the load stage
supplies exactly the `GeneratorWordsAt` fact `generator_setup_handoff_entry`
needs to produce `GeneratorTableFrozen`, and `post_setup_tightCells` /
`post_setup_storeValuesLe` transport `TightCells` / `StoreValuesLe` from the
load stage's output store (via `loadWordsProg_untouched_ctl_zero` /
`program_eval_storeValuesLe`) to the post-setup store. -/

/-- The load stage's output store stays under `envB.eval N`. -/
lemma stage4BoundedEnvB_load_store_le (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    StoreValuesLe
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)) := by
  have hK1 := envK_ge_one p time d (prefixWord d bits) allowedIdx outIdx bits.length
  have hKB := envB_ge_envK p time d (prefixWord d bits) allowedIdx outIdx bits.length
  have h2N := envK_ge_two_n p time d (prefixWord d bits) allowedIdx outIdx bits.length
  refine program_eval_storeValuesLe (bitInputStore bits)
    (loadWordsProg p time d allowedIdx outIdx) (by omega)
    (bitInputStore_storeValuesLe bits _ (by omega) (by omega))
    (programBoundedIn_loadWordsProg_envB_any p time d allowedIdx outIdx bits
      (fun k hk => envK_ge_mem_kind p time d (prefixWord d bits) allowedIdx outIdx
        bits.length _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_arg1 p time d (prefixWord d bits) allowedIdx outIdx
        bits.length _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_arg2 p time d (prefixWord d bits) allowedIdx outIdx
        bits.length _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_out p time d (prefixWord d bits) allowedIdx outIdx
        bits.length _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)))
    (scanFree_loadWordsProg p time d allowedIdx outIdx)

/-- The post-setup store has all control cells `M+2 .. M+24` under `envK.eval N`. -/
lemma stage4BoundedEnvB_post_setup_tight (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    TightCells
      (Polynomial.eval bits.length (envK p time d (prefixWord d bits) allowedIdx outIdx))
      (setupM p time d allowedIdx bits.length)
      ((Program.assign 0 (setupME p time d allowedIdx)).eval
        ((generatorSetupProg p time d allowedIdx outIdx).eval
          ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)))) :=
  post_setup_tightCells p time d (prefixWord d bits) allowedIdx outIdx _ bits.length
    (loadWordsProg_reg0 p time d allowedIdx outIdx bits)
    (fun j hj2 hj13 => by
      rw [loadWordsProg_untouched_ctl_zero p time d allowedIdx outIdx bits j hj2
        (by omega)]
      exact Nat.zero_le _)

/-- The frozen table parameters pin the three scalars the clause-count stage reads. -/
lemma stage4BoundedEnvB_clause_pins (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (ρ : Store)
    (hF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ) :
    ρ (setupM p time d allowedIdx N + persistTReg) = (timePoly p time).eval N ∧
      ρ (setupM p time d allowedIdx N + persistWReg) = (cookWindowPoly p time).eval N ∧
      ρ (setupM p time d allowedIdx N + initFreeLenReg) = p.eval N := by
  refine ⟨hF.1.1.1.1.1 (persistTReg, (timePoly p time).eval N) ?_,
    hF.1.1.1.1.1 (persistWReg, (cookWindowPoly p time).eval N) ?_,
    hF.1.1.1.1.1 (initFreeLenReg, p.eval N) ?_⟩ <;>
  simp [initParamPins0, initWReg, initTReg, initFreeLenReg, initPrefLenReg,
    initPrefBaseReg, persistTReg, persistWReg]

/-- KEY CONTRACT of the clause-count stage: it stays bounded and hands the table
    writer a frozen table, the control pointer, the table-base pin, and the
    store and tight-cell bounds. -/
lemma stage4BoundedEnvB_clause_phase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (ρ : Store)
    (hρ0 : ρ 0 = setupM p time d allowedIdx N)
    (hF : GeneratorTableFrozen (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
      (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
      prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ)
    (hwp : ρ (setupM p time d allowedIdx N + wpJ) =
      generatorTableBase p time d allowedIdx outIdx N)
    (hTight : TightCells (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (setupM p time d allowedIdx N) ρ)
    (hStore : StoreValuesLe (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) ρ) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) ρ
        (clauseCountProg d.numStates d.numLetters) ∧
      GeneratorTableFrozen (setupM p time d allowedIdx N)
        ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
        (p.eval N) (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N)
        prefIdx (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
        (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
        (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
        (generatorOutBase p time d allowedIdx N) outIdx ((clauseCountProg d.numStates d.numLetters).eval ρ) ∧
      (clauseCountProg d.numStates d.numLetters).eval ρ 0 =
        setupM p time d allowedIdx N ∧
      (clauseCountProg d.numStates d.numLetters).eval ρ (setupM p time d allowedIdx N + wpJ) =
        generatorTableBase p time d allowedIdx outIdx N ∧
      StoreValuesLe (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
        ((clauseCountProg d.numStates d.numLetters).eval ρ) ∧
      TightCells (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
        (setupM p time d allowedIdx N) ((clauseCountProg d.numStates d.numLetters).eval ρ) := by
  obtain ⟨hT, hW, hfree⟩ :=
    stage4BoundedEnvB_clause_pins p time d prefIdx allowedIdx outIdx N ρ hF
  have hbases := generator_staged_bases_above_count_cells p time d allowedIdx N
  have hClause := programBoundedIn_clauseCountProg p time d prefIdx allowedIdx outIdx N ρ
    hρ0 hT hW hfree
  have hK1 := envK_ge_one p time d prefIdx allowedIdx outIdx N
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  refine ⟨hClause, clauseCountProg_preserves_generatorTableFrozen
      d.numStates d.numLetters (setupM p time d allowedIdx N)
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N) (p.eval N)
      (generatorPrefLen N) (generatorPrefBase p time d allowedIdx N) prefIdx
      (generatorKindBase p time d allowedIdx N) (d.table.map transKind)
      (generatorArg1Base p time d allowedIdx N) (d.table.map transArg1)
      (generatorArg2Base p time d allowedIdx N) (d.table.map transArg2)
      (generatorOutBase p time d allowedIdx N) outIdx ρ hρ0
      hbases.1 hbases.2.1 hbases.2.2.1 hbases.2.2.2.1 hbases.2.2.2.2 hF,
    clauseCountProg_zero d.numStates d.numLetters (setupM p time d allowedIdx N) ρ hρ0,
    ?_, program_eval_storeValuesLe ρ (clauseCountProg d.numStates d.numLetters)
      (by omega) hStore hClause (scanFree_clauseCountProg d.numStates d.numLetters),
    fun j hj2 hj24 => ?_⟩
  · rw [clauseCountProg_frame d.numStates d.numLetters (setupM p time d allowedIdx N)
      (setupM p time d allowedIdx N + wpJ) ρ hρ0 (by omega)
      (by norm_num [wpJ, rowCountReg]) (by norm_num [wpJ, iterReg])]
    exact hwp
  · rw [clauseCountProg_frame d.numStates d.numLetters (setupM p time d allowedIdx N)
      (setupM p time d allowedIdx N + j) ρ hρ0 (by omega)
      (by norm_num [rowCountReg]; omega) (by norm_num [iterReg]; omega)]
    exact hTight j hj2 hj24

/-- The clause-count and final-writer stages are bounded at `envB.eval N`.
    The setup handoff supplies the frozen table and pointer at the common entry
    store; the clause-count fragment then preserves the table cells, tight cells,
    and store bound before the final writer runs. -/
lemma stage4_bounded_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (bits : Bits) :
    ProgramBoundedIn
        (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
        ((Program.assign 0 (setupME p time d allowedIdx)).eval
          ((generatorSetupProg p time d allowedIdx outIdx).eval
            ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits))))
        (clauseCountProg d.numStates d.numLetters) ∧
      ProgramBoundedIn
        (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
        ((clauseCountProg d.numStates d.numLetters).eval
          ((Program.assign 0 (setupME p time d allowedIdx)).eval
            ((generatorSetupProg p time d allowedIdx outIdx).eval
              ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)))))
        (tableWriterProgParam d allowedIdx outIdx) := by
  have h0L := loadWordsProg_reg0 p time d allowedIdx outIdx bits
  have hStore := post_setup_storeValuesLe p time d (prefixWord d bits) allowedIdx outIdx _
    bits.length h0L (stage4BoundedEnvB_load_store_le p time d allowedIdx outIdx bits)
  have he := generator_setup_handoff_entry p time d allowedIdx outIdx (prefixWord d bits) _
    bits.length h0L (loadWordsProg_words p time d allowedIdx outIdx bits)
  simp only at he
  obtain ⟨hFrozen, hρ0, hwp, _, _⟩ := he
  obtain ⟨hClause, hFrozen3, hσ30, hσ3wp, hClauseStore, hClauseTight⟩ :=
    stage4BoundedEnvB_clause_phase p time d (prefixWord d bits) allowedIdx outIdx
      bits.length _ hρ0 hFrozen hwp
      (stage4BoundedEnvB_post_setup_tight p time d allowedIdx outIdx bits) hStore
  have hsep : setupM p time d allowedIdx bits.length + generatorJmax d outIdx bits.length
      < generatorTableBase p time d allowedIdx outIdx bits.length := by
    unfold generatorTableBase; omega
  have hwidFit : generatorTableBase p time d allowedIdx outIdx bits.length +
      Polynomial.eval bits.length (envWid p time d (prefixWord d bits) allowedIdx outIdx) ≤
      Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx) := by
    have hKtb := envK_ge_tableBase p time d (prefixWord d bits) allowedIdx outIdx bits.length
    have hSeval := envS_eval p time d (prefixWord d bits) allowedIdx outIdx bits.length
    have hSB := envS_le_envB p time d (prefixWord d bits) allowedIdx outIdx bits.length
    omega
  exact ⟨hClause, (clauseWriterBounded_envB_tableWriterProgParam p time d allowedIdx outIdx
    bits _ (generatorTableBase p time d allowedIdx outIdx bits.length) hFrozen3 hσ30 hσ3wp
    hsep hwidFit hClauseStore hClauseTight).1⟩

/-! ## The top-level vertex, assembled from the five stages -/

/-- The top-level vertex: `generatorProgFromBits` stays bounded by `envB.eval
    N` on `bitInputStore bits`, unconditionally in `p`, `time`, `d`,
    `allowedIdx`, `outIdx`, `bits`. `ProgramBoundedIn`'s own `.seq` clause
    (`GeneratorBoundedTop.lean` header) splits the five stages open; each is
    discharged at the entry store the previous stages hand it, in order:
    the load stage (`programBoundedIn_loadWordsProg_envB_any`), the setup and
    workspace stages (`generatorSetupProg_bounded_envB`, `assign_setupME_bounded_envB`),
    then the clause-count and final-writer pair (`stage4_bounded_envB` above). -/
lemma programBoundedIn_generatorProgFromBits (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits) :
    ProgramBoundedIn
      (Polynomial.eval bits.length (envB p time d (prefixWord d bits) allowedIdx outIdx))
      (bitInputStore bits)
      (generatorProgFromBits p time d allowedIdx outIdx) := by
  set N := bits.length with hN
  set prefIdx := prefixWord d bits with hprefIdx
  unfold generatorProgFromBits generatorProg
  simp only [ProgramBoundedIn]
  have h0L : (loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits) 0 = N :=
    loadWordsProg_reg0 p time d allowedIdx outIdx bits
  have hstage4 := stage4_bounded_envB p time d allowedIdx outIdx bits
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact programBoundedIn_loadWordsProg_envB_any p time d allowedIdx outIdx bits
      (fun k hk => envK_ge_mem_kind p time d prefIdx allowedIdx outIdx N _
        (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_arg1 p time d prefIdx allowedIdx outIdx N _
        (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_arg2 p time d prefIdx allowedIdx outIdx N _
        (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
      (fun k hk => envK_ge_mem_out p time d prefIdx allowedIdx outIdx N _
        (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
  · exact generatorSetupProg_bounded_envB p time d prefIdx allowedIdx outIdx _ N h0L
  · have hτ0 : (generatorSetupProg p time d allowedIdx outIdx).eval
        ((loadWordsProg p time d allowedIdx outIdx).eval (bitInputStore bits)) 0 = N := by
      rw [generator_setup_prog_zero]; exact h0L
    exact assign_setupME_bounded_envB p time d prefIdx allowedIdx outIdx _ N hτ0
  · exact hstage4.1
  · exact hstage4.2

/-! ## `CompiledOperandBound` for `generatorProgFromBits`

The operand bound for `generatorProg` is `ScanFree` plus a `ProgramBoundedIn`
at an envelope; the statement for
`generatorProgFromBits` composes the generic `compiledOperandBound_of_programBoundedIn`
(`UniformPackaging.lean`) with `scanFree_generatorProgFromBits`
(`GeneratorLoad.lean`) instead. -/

/-- `generatorProgFromBits` satisfies the packaging's `CompiledOperandBound`
    obligation at any `B` with `1 ≤ B` and `StoreValuesLe B (bitInputStore
    bits)`: only `ScanFree` (`scanFree_generatorProgFromBits`) and
    `ProgramBoundedIn` are needed, exactly as for the bare `generatorProg`. -/
lemma compiledOperandBound_generatorProgFromBits_of_programBoundedIn
    (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx outIdx : List ℕ)
    (bits : Bits) (B : ℕ) (hB : 1 ≤ B)
    (hσ : StoreValuesLe B (bitInputStore bits))
    (hpb : ProgramBoundedIn B (bitInputStore bits)
      (generatorProgFromBits p time d allowedIdx outIdx)) :
    CompiledOperandBound (generatorProgFromBits p time d allowedIdx outIdx) bits
      (NPComplete.BitCostRAM.bitLen B) :=
  compiledOperandBound_of_programBoundedIn _ bits B hB hσ hpb
    (scanFree_generatorProgFromBits p time d allowedIdx outIdx)

end NPComplete.CookLevin

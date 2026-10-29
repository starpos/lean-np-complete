module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmit
public import NPComplete.RAMToTM.Generic.Machine.GenericSub

/-!
# Converting a RAM-level output length into `EmitK.countdown` markers

`GenericEmit.lean`'s `emit_run_length_bounded` takes the number of loop iterations as a
caller-supplied `rest0 : List Unit` already sitting on `EmitK.countdown` — nothing there converts a
RAM register holding `natToDigits n` into that many `()` markers. This file supplies exactly that
conversion, as its own small loop machine sharing `GenericEmit`'s stack space `EmitK p` (so its
writes to `EmitK.countdown` are the literal markers `emit_run_length_bounded` later consumes) but
with its own local phase/state (`EmitPrepPhase`/`PrepState`) rather than growing `EmitPhase`/`AllEmitState`
themselves, so `GenericEmit.lean` is independent of this file. One iteration:
peek the length register non-destructively (`checkLen`); if it still holds a digit, push a
`countdown` marker and run the embedded `GenericSub.subProg rLen rLen rOne` (alias-safe
self-decrement, `GenericSub.lean`'s module docstring) to subtract `1`, transported via
`StmtTransport.liftStmt` exactly as `GenericEmit.lean`'s own `emit_run_load_bounded`/`emit_run_add_bounded`
transport `loadProg`/`addProg`; otherwise exit at `done`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits liftStmt iterate_bind_step_liftStmt SubState)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rLen rOne : Fin (regBound p))

/-- One prep-loop iteration's phases: `checkLen` (peek `rLen`, non-destructive), `dec` (the
    embedded `subProg`'s own phase space), `done` (halt). -/
inductive EmitPrepPhase
  | checkLen
  | dec : SubPhase → EmitPrepPhase
  | done
  deriving DecidableEq, Fintype

/-- The prep loop's own local state: the embedded `subProg`'s `SubState`, and the last peeked
    `rLen` marker (`checkLen`'s loop-continue flag). -/
structure PrepState where
  sub : SubState
  more : Option Digit
  deriving DecidableEq, Fintype

/-- The state every loop iteration starts and ends at, apart from `more`'s freshly peeked value:
    the embedded `subProg` is never mid-computation between iterations. -/
def PrepState.canonical : PrepState := ⟨⟨none, none, false⟩, none⟩

def PrepState.getSub : PrepState → SubState := (·.sub)
def PrepState.setSub : PrepState → SubState → PrepState := fun s v => { s with sub := v }

lemma getSub_setSub (s : PrepState) (v : SubState) : PrepState.getSub (PrepState.setSub s v) = v :=
  rfl
lemma setSub_setSub (s : PrepState) (v w : SubState) :
    PrepState.setSub (PrepState.setSub s v) w = PrepState.setSub s w := rfl
lemma setSub_getSub (s : PrepState) : PrepState.setSub s (PrepState.getSub s) = s := by
  cases s; rfl

/-- The prep loop's `Stmt` tree. `dec`'s own local `done` label is intercepted (matching
    `GenericEmit.emitProg`'s `load`/`add` bridge pattern) and redirected back to `checkLen`
    instead of running the embedded `subProg`'s literal `halt`. -/
def prepProg : EmitPrepPhase → Turing.TM2.Stmt (EmitΓ p) EmitPrepPhase PrepState
  | .checkLen =>
      peek (EmitK.base (Kg.reg rLen)) (fun s ov => { s with more := ov })
        (branch (fun s => s.more.isSome)
          (push EmitK.countdown (fun _ => ())
            (goto (fun _ => EmitPrepPhase.dec SubPhase.copyLhs)))
          (goto (fun _ => EmitPrepPhase.done)))
  | .dec l =>
      if l = SubPhase.done then
        goto (fun _ => EmitPrepPhase.checkLen)
      else
        liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPrepPhase.dec)
          PrepState.getSub PrepState.setSub (subProg rLen rLen rOne l)
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindPrep : Option (Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState) →
    Option (Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState) :=
  fun x => x.bind (Turing.TM2.step (prepProg rLen rOne))

/-! ## `checkLen`: the loop-continue test, driven by `rLen`'s content -/

lemma flipBindPrep_checkLen_cons (d : Digit) (rest : List Digit) (Sg : ∀ k, List (EmitΓ p k))
    (s0 : PrepState) (hLen : Sg (EmitK.base (Kg.reg rLen)) = d :: rest) :
    flipBindPrep rLen rOne
        (some (⟨some EmitPrepPhase.checkLen, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some (EmitPrepPhase.dec SubPhase.copyLhs), { s0 with more := some d },
          Function.update Sg EmitK.countdown (() :: Sg EmitK.countdown)⟩ := by
  show (Turing.TM2.step (prepProg rLen rOne))
      (⟨some EmitPrepPhase.checkLen, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState) = _
  simp [prepProg, hLen]

lemma flipBindPrep_checkLen_nil (Sg : ∀ k, List (EmitΓ p k)) (s0 : PrepState)
    (hLen : Sg (EmitK.base (Kg.reg rLen)) = ([] : List Digit)) :
    flipBindPrep rLen rOne
        (some (⟨some EmitPrepPhase.checkLen, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some EmitPrepPhase.done, { s0 with more := none }, Sg⟩ := by
  show (Turing.TM2.step (prepProg rLen rOne))
      (⟨some EmitPrepPhase.checkLen, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState) = _
  simp [prepProg, hLen]

/-! ## `dec`: transporting `GenericSub.realize_sub_bounded` via `StmtTransport.iterate_bind_step_liftStmt` -/

lemma prepProg_dec_agrees (l : SubPhase) (hl : l ≠ SubPhase.done) :
    prepProg rLen rOne (EmitPrepPhase.dec l) =
      liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPrepPhase.dec)
        PrepState.getSub PrepState.setSub (subProg rLen rLen rOne l) := by
  simp [prepProg, hl]

/-- Running the embedded `subProg rLen rLen rOne` to completion inside the prep loop: `rLen`
    (alias-safe self-decrement, `rd = rs = rLen`) ends up holding `natToDigits (n - 1)`, and every
    other stack (in particular `EmitK.countdown`, which `checkLen` does not read again until the
    next iteration) is untouched.  The witness step count is bounded, transported unchanged from
    `realize_sub_bounded` (`iterate_bind_step_liftStmt` preserves the step count literally, so no new
    arithmetic is needed here). -/
lemma prep_run_dec_bounded (n : ℕ) (Sg0 : ∀ k, List (EmitΓ p k)) (s0 : PrepState)
    (hSubCanon : s0.sub = ⟨none, none, false⟩)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)) :
    ∃ n' sf Sgf, (flipBindPrep rLen rOne)^[n']
        (some (⟨some (EmitPrepPhase.dec SubPhase.copyLhs), s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some (EmitPrepPhase.dec SubPhase.done), sf, Sgf⟩
      ∧ sf = { s0 with sub := ⟨none, none, false⟩ }
      ∧ Sgf (EmitK.base (Kg.reg rLen)) = natToDigits (n - 1)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rLen → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ Sgf EmitK.countdown = Sg0 EmitK.countdown
      ∧ n' ≤ 16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) := by
  obtain ⟨n', hrun, hnbound⟩ := realize_sub_bounded rLen rLen rOne n 1 (fun k => Sg0 (EmitK.base k))
    hLen hOne hWorkRev hCopyScratch hLhsOperand hRhsOperand hDiffScratch
  rw [hLen] at hnbound
  obtain ⟨sf, Sgf, hrunG, hsetf, hstkf, hfrf⟩ :=
    iterate_bind_step_liftStmt EmitK.base emitΓEquiv EmitPrepPhase.dec PrepState.getSub PrepState.setSub
      (subProg rLen rLen rOne) (prepProg rLen rOne) emitK_inj getSub_setSub setSub_setSub
      setSub_getSub n' SubPhase.copyLhs (⟨none, none, false⟩ : SubState)
      (fun k => Sg0 (EmitK.base k)) s0 Sg0 hSubCanon
      (fun k => by simp [emitΓEquiv, Equiv.coe_refl, List.map_id]) SubPhase.done
      ⟨none, none, false⟩ (Function.update (fun k => Sg0 (EmitK.base k)) (Kg.reg rLen)
        (natToDigits (n - 1))) rfl (fun l hl => prepProg_dec_agrees rLen rOne l hl) hrun
  refine ⟨n', sf, Sgf, hrunG, hsetf, ?_, ?_, ?_, ?_, by omega⟩
  · have := hstkf (Kg.reg rLen)
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id] using this
  · intro k hk
    have := hstkf k
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id, Function.update_of_ne hk] using this
  · exact hfrf EmitK.out (fun kl h => by cases h)
  · exact hfrf EmitK.countdown (fun kl h => by cases h)

/-! ## Chaining one iteration: `checkLen` → `dec` → back to `checkLen`, popping one digit off
    `rLen` and pushing one marker onto `countdown`. -/

lemma flipBindPrep_dec_done (Sg : ∀ k, List (EmitΓ p k)) (s0 : PrepState) :
    flipBindPrep rLen rOne
        (some (⟨some (EmitPrepPhase.dec SubPhase.done), s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some EmitPrepPhase.checkLen, s0, Sg⟩ := by
  show (Turing.TM2.step (prepProg rLen rOne))
      (⟨some (EmitPrepPhase.dec SubPhase.done), s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState) = _
  simp [prepProg]

/-- Splicing two known-length runs (`GenericEmit.flipBindEmit_trans`'s analogue for
    `flipBindPrep`). -/
lemma flipBindPrep_trans {k1 k2 : ℕ}
    {x y z : Option (Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState)}
    (h1 : (flipBindPrep rLen rOne)^[k1] x = y) (h2 : (flipBindPrep rLen rOne)^[k2] y = z) :
    (flipBindPrep rLen rOne)^[k2 + k1] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

lemma flipBindPrep_one {x y : Option (Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState)}
    (h : flipBindPrep rLen rOne x = y) : (flipBindPrep rLen rOne)^[1] x = y := by
  rw [Function.iterate_one]; exact h

/-- One full prep-loop iteration: `rLen` holds `natToDigits (n+1)` (so `checkLen` sees a digit and
    continues), pushes one `countdown` marker, decrements `rLen` to `natToDigits n`, and lands
    back at `checkLen` with every other stack unchanged.  The witness step count is bounded by
    `prep_run_dec_bounded`'s bound plus the two bridge steps (`checkLen`'s peek and `dec.done`'s
    return). -/
lemma prep_run_iteration_bounded (n : ℕ) (Sg0 : ∀ k, List (EmitΓ p k)) (s0 : PrepState)
    (hLO : rOne ≠ rLen) (hSubCanon : s0.sub = ⟨none, none, false⟩)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits (n + 1))
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)) :
    ∃ n' sf Sgf, (flipBindPrep rLen rOne)^[n']
        (some (⟨some EmitPrepPhase.checkLen, s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some EmitPrepPhase.checkLen, sf, Sgf⟩
      ∧ sf.sub = ⟨none, none, false⟩
      ∧ Sgf EmitK.countdown = () :: Sg0 EmitK.countdown
      ∧ Sgf (EmitK.base (Kg.reg rLen)) = natToDigits n
      ∧ Sgf (EmitK.base (Kg.reg rOne)) = natToDigits 1
      ∧ Sgf (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rLen → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ n' ≤ 16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1) + 2 := by
  have hbase1 : ∀ k : Kg p, (Function.update Sg0 EmitK.countdown (() :: Sg0 EmitK.countdown))
      (EmitK.base k) = Sg0 (EmitK.base k) := fun k => Function.update_of_ne (by simp) _ _
  have hbaseOut : (Function.update Sg0 EmitK.countdown (() :: Sg0 EmitK.countdown)) EmitK.out
      = Sg0 EmitK.out := Function.update_of_ne (by simp) _ _
  obtain ⟨d, rest, hcons⟩ := List.exists_cons_of_ne_nil
    ((natToDigits_ne_nil_iff (n + 1)).mpr (Nat.succ_ne_zero n))
  have hA := flipBindPrep_one rLen rOne
    (flipBindPrep_checkLen_cons rLen rOne d rest Sg0 s0 (hLen.trans hcons))
  have hres := prep_run_dec_bounded rLen rOne (n + 1) (Function.update Sg0 EmitK.countdown
      (() :: Sg0 EmitK.countdown)) { s0 with more := some d } hSubCanon
    (by rw [hbase1]; exact hLen) (by rw [hbase1]; exact hOne) (by rw [hbase1]; exact hWorkRev)
    (by rw [hbase1]; exact hCopyScratch) (by rw [hbase1]; exact hLhsOperand)
    (by rw [hbase1]; exact hRhsOperand) (by rw [hbase1]; exact hDiffScratch)
  obtain ⟨n1, sf1, Sgf1, hbody1⟩ := hres
  obtain ⟨hrun1, hsf1, hRLen1, hFrame1, hOut1, hCd1, hn1bound⟩ := hbody1
  have hStep2 := flipBindPrep_trans rLen rOne hA hrun1
  have hStep3 := flipBindPrep_trans rLen rOne hStep2
    (flipBindPrep_one rLen rOne (flipBindPrep_dec_done rLen rOne Sgf1 sf1))
  have hRLen1' : Sgf1 (EmitK.base (Kg.reg rLen)) = natToDigits n := by
    rw [hRLen1, show n + 1 - 1 = n from by omega]
  have hneRLen : (Kg.reg rOne : Kg p) ≠ Kg.reg rLen := fun h => hLO (by injection h)
  refine ⟨_, sf1, Sgf1, hStep3, by rw [hsf1], hCd1, hRLen1', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hFrame1 (Kg.reg rOne) hneRLen).trans (by rw [hbase1]; exact hOne)
  · exact (hFrame1 (Kg.scratch .workRev) (by simp)).trans (by rw [hbase1]; exact hWorkRev)
  · exact (hFrame1 (Kg.scratch .copyScratch) (by simp)).trans (by rw [hbase1]; exact hCopyScratch)
  · exact (hFrame1 (Kg.scratch .lhsOperand) (by simp)).trans (by rw [hbase1]; exact hLhsOperand)
  · exact (hFrame1 (Kg.scratch .rhsOperand) (by simp)).trans (by rw [hbase1]; exact hRhsOperand)
  · exact (hFrame1 (Kg.scratch .diffScratch) (by simp)).trans (by rw [hbase1]; exact hDiffScratch)
  · exact ⟨fun k hk => (hFrame1 k hk).trans (hbase1 k), hOut1.trans hbaseOut, by omega⟩

/-- Closing the whole prep loop by induction on `n`: repeat `prep_run_iteration_bounded` once per digit of
    `rLen`'s value until it empties, landing at `done` with exactly `n` fresh markers pushed onto
    `countdown` and `rLen` cleared, with a polynomial bound on the witness step count.
    `natToDigits_length_mono` bounds every iteration's cost (which depends on
    the *current*, shrinking value of `rLen`) by the *initial* value `n`'s digit length, so `n`
    iterations at that uniform per-iteration cost dominate the true (telescoping, strictly
    smaller) total. -/
lemma prep_run_length_bounded (n : ℕ) (Sg0 : ∀ k, List (EmitΓ p k)) (s0 : PrepState)
    (hLO : rOne ≠ rLen) (hSubCanon : s0.sub = ⟨none, none, false⟩)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)) :
    ∃ n' sf Sgf, (flipBindPrep rLen rOne)^[n']
        (some (⟨some EmitPrepPhase.checkLen, s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPrepPhase PrepState))
      = some ⟨some EmitPrepPhase.done, sf, Sgf⟩
      ∧ Sgf EmitK.countdown = List.replicate n () ++ Sg0 EmitK.countdown
      ∧ Sgf (EmitK.base (Kg.reg rLen)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.reg rOne)) = natToDigits 1
      ∧ Sgf (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rLen → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ n' ≤ n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) + 1 := by
  induction n generalizing Sg0 s0 with
  | zero =>
    have hLen0 : Sg0 (EmitK.base (Kg.reg rLen)) = ([] : List Digit) := by
      rw [hLen, natToDigits_zero]
    refine ⟨1, { s0 with more := none }, Sg0, ?_, by simp, hLen0, hOne, hWorkRev, hCopyScratch,
      hLhsOperand, hRhsOperand, hDiffScratch, fun _ _ => rfl, rfl, by omega⟩
    exact flipBindPrep_one rLen rOne (flipBindPrep_checkLen_nil rLen rOne Sg0 s0 hLen0)
  | succ n ih =>
    obtain ⟨n1, sf1, Sgf1, hbody1⟩ :=
      prep_run_iteration_bounded rLen rOne n Sg0 s0 hLO hSubCanon hLen hOne hWorkRev hCopyScratch
        hLhsOperand hRhsOperand hDiffScratch
    obtain ⟨hrun1, hsubf1, hCd1, hRLen1, hOne1, hWorkRev1, hCopyScratch1, hLhsOperand1,
      hRhsOperand1, hDiffScratch1, hFrame1, hOut1, hn1bound⟩ := hbody1
    obtain ⟨n2, sf2, Sgf2, hbody2⟩ :=
      ih Sgf1 sf1 hsubf1 hRLen1 hOne1 hWorkRev1 hCopyScratch1 hLhsOperand1 hRhsOperand1
        hDiffScratch1
    obtain ⟨hrun2, hCd2, hRLen2, hOne2, hWorkRev2, hCopyScratch2, hLhsOperand2, hRhsOperand2,
      hDiffScratch2, hFrame2, hOut2, hn2bound⟩ := hbody2
    have hmono : (natToDigits n).length ≤ (natToDigits (n + 1)).length :=
      natToDigits_length_mono (by omega)
    have hCLe : 16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2 ≤
        16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1) + 2 := by omega
    have hmul : n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) ≤
        n * (16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1) + 2) :=
      Nat.mul_le_mul (le_refl n) hCLe
    have hdist : (n + 1) * (16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1)
        + 2) = n * (16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1) + 2) +
        (16 * (2 * (natToDigits (n + 1)).length + (natToDigits 1).length + 1) + 2) := by ring
    refine ⟨n2 + n1, sf2, Sgf2, flipBindPrep_trans rLen rOne hrun1 hrun2, ?_, hRLen2, hOne2,
      hWorkRev2, hCopyScratch2, hLhsOperand2, hRhsOperand2, hDiffScratch2,
      fun k hk => (hFrame2 k hk).trans (hFrame1 k hk), hOut2.trans hOut1, by omega⟩
    rw [hCd2, hCd1, List.replicate_succ', List.append_assoc]; rfl

end NPComplete.RAMToTM.Generic

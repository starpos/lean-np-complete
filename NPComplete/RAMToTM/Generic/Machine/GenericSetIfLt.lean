module

public import NPComplete.RAMToTM.Generic.Machine.GenericCompare
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `setIfLt` realized against an arbitrary site's register triple

`setIfLt rd rs rt`'s effect is the shared compare core (`GenericCompare.lean`) followed by
draining `rd` (`clearDest`, mirroring `GenericMove.lean`'s `clearDest`/`GenericAdd.lean`'s
`clearDest`) and pushing a single `1` digit iff the comparison was `.lt` (nothing, i.e. `0`,
otherwise). `SetIfLtPhase` (`GenericProgramMachine.lean`) embeds `CompareCorePhase` via
`compare`, with `clearDest`/`writeResult`/`done` the extra phases: `.compare .done` bridges to
`clearDest`, `done` is `halt` locally, overridden at the site level with the uniform
`bridgeTo p (pc.1+1)` (unlike `branchIfLt`, `setIfLt`'s control flow never depends on the
comparison outcome, only `rd`'s content does).

**`rd` alias safety, for free**: by the time `clearDest` runs, the compare core has already fully
restored `rs`/`rt` to their original content (`GenericCompare.lean`'s `compare_core_run_bounded`), so
draining `rd` — even if `rd = rs`/`rd = rt` (the same physical stack) — only discards a value no
longer needed; the machine's `Stmt` tree does not branch on whether `rd` aliases `rs`/`rt`,
matching `GenericMove.lean`'s `clearDest` reasoning.

`rs = rt`: `setIfLtImpl` dispatches with an `if` on the raw `ℕ` operands, exactly as in
`GenericBranchIfLt.lean` — the aliased tree never touches `rs`/`rt`. The comparison is
trivially `.eq`, so `writeResult` never fires and `rd` is simply drained to empty.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits scanCompare scanCompare_eq_compareDigits
  compareDigits compareDigits_natToDigits)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs rt : Fin (regBound p))

/-- `setIfLt`'s local `Stmt` tree, self-contained against `SetIfLtPhase`/`CompareState`: the
    shared compare core is embedded via `liftStmt` at every non-`done` `compare` phase,
    `.compare .done` bridges to `clearDest` (draining `rd`, reusing `left` as the popped-digit
    scratch — safe since the compare core's own use of `left` is long finished by then),
    `writeResult` pushes `1` iff `acc = .lt`, and `.done` is `halt`
    (`StmtTransport`'s fixed-exit requirement, overridden at the site level). -/
def setIfLtProg : SetIfLtPhase → Turing.TM2.Stmt (Γg p) SetIfLtPhase CompareState
  | .compare ph =>
      if ph = CompareCorePhase.done then goto (fun _ => .clearDest)
      else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfLtPhase.compare
        id (fun _ v => v) (compareCoreProg rs rt ph)
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .writeResult)))
  | .writeResult =>
      branch (fun s => decide (s.acc = Ordering.lt))
        (push (Kg.reg rd) (fun _ => (⟨1, by norm_num⟩ : Digit)) (goto (fun _ => .done)))
        (goto (fun _ => .done))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindSetIfLt :
    Option (Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (setIfLtProg rd rs rt))

/-- Any dispatcher agreeing with `setIfLtProg` at every non-`done` `compare` phase installs the
    lifted compare core there — trivially true by `setIfLtProg`'s own definition. -/
lemma setIfLtProg_agrees :
    ∀ l : CompareCorePhase, l ≠ CompareCorePhase.done →
      setIfLtProg rd rs rt (SetIfLtPhase.compare l)
        = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfLtPhase.compare
            id (fun _ v => v) (compareCoreProg rs rt l) := by
  intro l hl
  simp [setIfLtProg, hl]

lemma flipBindSetIfLt_compare_done_step (v0 : CompareState) (Sg : ∀ k, List (Γg p k)) :
    flipBindSetIfLt rd rs rt
        (some (⟨some (SetIfLtPhase.compare CompareCorePhase.done), v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfLtProg rd rs rt))
      (⟨some (SetIfLtPhase.compare CompareCorePhase.done), v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtProg]

/-! ## `clearDest`: draining whatever `rd` currently holds -/

lemma flipBindSetIfLt_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindSetIfLt rd rs rt
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, ({v0 with left := some d} : CompareState),
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (setIfLtProg rd rs rt))
      (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtProg, hRd]

lemma flipBindSetIfLt_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindSetIfLt rd rs rt
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.writeResult, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (setIfLtProg rd rs rt))
      (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtProg, hRd]

/-- Draining register `rd`, discarding its content (no scratch relay needed, mirroring
    `GenericMove.lean`'s `move_clearDest_loop`). -/
lemma flipBindSetIfLt_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfLt rd rs rt)^[dest.length + 1]
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.writeResult, ({v0 with left := none} : CompareState),
          Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k; by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindSetIfLt_clearDest_nil_exit rd rs rt Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSetIfLt_clearDest_cons rd rs rt d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') ({v0 with left := some d} : CompareState)
          (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `writeResult`: push `1` iff `acc = .lt` -/

lemma flipBindSetIfLt_writeResult_lt (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hacc : v0.acc = Ordering.lt) :
    flipBindSetIfLt rd rs rt
        (some (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.done, v0,
          Function.update Sg (Kg.reg rd) ((⟨1, by norm_num⟩ : Digit) :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (setIfLtProg rd rs rt))
      (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtProg, hacc]

lemma flipBindSetIfLt_writeResult_ne_lt (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hacc : v0.acc ≠ Ordering.lt) :
    flipBindSetIfLt rd rs rt
        (some (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.done, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfLtProg rd rs rt))
      (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtProg, hacc]

/-- The whole `setIfLtProg` run, with a bound on the witness step count combining
    `compare_core_run_bounded`'s bound with the already-closed-form `clearDest`/`writeResult`
    costs. -/
lemma flipBindSetIfLt_run_bounded (hne : rs ≠ rt) (xs ys dest : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = xs) (hRt : Sg (Kg.reg rt) = ys) (hRd : Sg (Kg.reg rd) = dest)
    (hL : Sg (Kg.scratch .lhsOperand) = []) (hR : Sg (Kg.scratch .rhsOperand) = []) :
    ∃ n, (flipBindSetIfLt rd rs rt)^[n]
        (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan),
          (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.done,
          (⟨none, none, scanCompare .eq xs ys⟩ : CompareState),
          Function.update
            (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys)
            (Kg.reg rd)
            (if scanCompare .eq xs ys = Ordering.lt then [(⟨1, by norm_num⟩ : Digit)] else [])⟩ ∧
        n ≤ dest.length + 2 * (xs.length + ys.length) + 8 := by
  obtain ⟨n1, hn1, hn1bound⟩ := compare_core_run_bounded rs rt hne xs ys Sg
    (⟨none, none, .eq⟩ : CompareState) hRs hRt hL hR
  have hstkTriv : ∀ k, Sg (id k) = List.map (⇑(Equiv.refl (Γg p k))) (Sg k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfLtPhase.compare
      id (fun _ v => v) (compareCoreProg rs rt) (setIfLtProg rd rs rt)
      Function.injective_id (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      n1 CompareCorePhase.scan (⟨none, none, .eq⟩ : CompareState) Sg
      (⟨none, none, .eq⟩ : CompareState) Sg rfl hstkTriv
      CompareCorePhase.done (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩
        : CompareState)
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) rfl
      (setIfLtProg_agrees rd rs rt) hn1
  have hsfEq : sf = (⟨none, none, scanCompare .eq xs ys⟩ : CompareState) := hsetf
  have hSgfEq : Sgf = Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys := by
    funext k
    exact stack_eq_of_map_equiv_refl Sgf
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) hstkf k
  have hstep1 : flipBindSetIfLt rd rs rt
      (some (⟨some (SetIfLtPhase.compare CompareCorePhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, sf, Sgf⟩ :=
    flipBindSetIfLt_compare_done_step rd rs rt sf Sgf
  have hRdEq : Sgf (Kg.reg rd) = dest := by
    rw [hSgfEq]
    by_cases hdt : rd = rt
    · subst hdt; rw [Function.update_self, ← hRd, hRt]
    · by_cases hds : rd = rs
      · subst hds
        rw [Function.update_of_ne (show Kg.reg rd ≠ Kg.reg rt from fun hh => hdt (by injection hh)),
          Function.update_self, ← hRd, hRs]
      · rw [Function.update_of_ne (show Kg.reg rd ≠ Kg.reg rt from fun hh => hdt (by injection hh)),
          Function.update_of_ne (show Kg.reg rd ≠ Kg.reg rs from fun hh => hds (by injection hh))]
        exact hRd
  have hClear := flipBindSetIfLt_clearDest_loop rd rs rt dest Sgf sf hRdEq
  have hrun' : (flipBindSetIfLt rd rs rt)^[n1]
      (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some (SetIfLtPhase.compare CompareCorePhase.done), sf, Sgf⟩ := hrun
  have hcombined1 : (flipBindSetIfLt rd rs rt)^[n1 + 1]
      (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, sf, Sgf⟩ := by
    rw [Function.iterate_succ_apply', hrun']; exact hstep1
  have hcombined2 : (flipBindSetIfLt rd rs rt)^[(dest.length + 1) + (n1 + 1)]
      (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.writeResult, ({sf with left := none} : CompareState),
          Function.update Sgf (Kg.reg rd) []⟩ := by
    rw [Function.iterate_add_apply, hcombined1]; exact hClear
  refine ⟨(dest.length + 1) + (n1 + 1) + 1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hcombined2]
  by_cases hlt : scanCompare Ordering.eq xs ys = Ordering.lt
  · rw [ite_eq_left hlt, flipBindSetIfLt_writeResult_lt rd rs rt (Function.update Sgf (Kg.reg rd) [])
      ({sf with left := none} : CompareState)
      (show sf.acc = Ordering.lt from by rw [hsfEq]; exact hlt)]
    simp only [hsfEq, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    by_cases hk : k = Kg.reg rd
    · subst hk; rw [Function.update_self, Function.update_self, Function.update_self]
    · simp [Function.update, hk, hSgfEq]
  · rw [ite_eq_right hlt, flipBindSetIfLt_writeResult_ne_lt rd rs rt (Function.update Sgf (Kg.reg rd) [])
      ({sf with left := none} : CompareState)
      (show sf.acc ≠ Ordering.lt from by rw [hsfEq]; exact hlt)]
    simp only [hsfEq, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    rw [hSgfEq]

/-! ## Site dispatcher package, non-aliased register triple -/

/-- `setIfLt`'s `Stmt` tree at site `pc`, before embedding into `Λg p`, for the *non-aliased*
    case: `done` unconditionally bridges to `pc.1+1` (`setIfLt`'s control flow never depends on
    the comparison outcome, only `rd`'s content does — unlike `branchIfLt`), every other phase is
    `setIfLtProg` lifted via `execVia`. -/
def setIfLtCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) :
    SetIfLtPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = SetIfLtPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getSetIfLt AllInstrState.setSetIfLt
        (setIfLtProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `setIfLtCodeBody`, cast once to the `SiteCode p pc` shape. -/
def setIfLtCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (setIfLtCodeBody p pc rd rs rt h)

/-- `setIfLtCode` undoes its own cast when applied to a correspondingly-cast `SetIfLtPhase`
    value. -/
lemma setIfLtCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) (l : SetIfLtPhase) :
    setIfLtCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l)
      = setIfLtCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (setIfLtCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `setIfLtCode` at site `pc` installs the lifted `setIfLtProg`
    tree at every non-`done` label. -/
lemma setIfLtCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtCode p pc rd rs rt h) M) :
    ∀ l : SetIfLtPhase, l ≠ SetIfLtPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getSetIfLt AllInstrState.setSetIfLt
        (setIfLtProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) (regAt p pc rt (by rw [h]; simp [regsOf])) l)
      := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    setIfLtCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `setIfLtCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `setIfLt`'s own `done` label. -/
lemma setIfLtCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtCode p pc rd rs rt h) M) :
    M (execVia p pc h SetIfLtPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) SetIfLtPhase.done)
  rw [show execVia p pc h SetIfLtPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) SetIfLtPhase.done) from rfl, hone,
    setIfLtCode_apply]
  rfl

/-! ## Quantitative companion -/

/-- The `writeResult` output `[1]`/`[]` is the digit encoding of the `0`/`1` that `setIfLt`
    writes, which lets the register frame be stated against `natToDigits`. -/
lemma setIfLtMainImpl_growing_bounded_result_digits (a b : ℕ) :
    (if scanCompare Ordering.eq (natToDigits a) (natToDigits b) = Ordering.lt
      then [(⟨1, by norm_num⟩ : Digit)] else [])
      = natToDigits (if a < b then 1 else 0) := by
  rw [scanCompare_eq_compareDigits]
  have hthEq : ∀ x : Ordering, x.then Ordering.eq = x := fun x => by cases x <;> rfl
  rw [hthEq, compareDigits_natToDigits]
  by_cases hlt : a < b
  · rw [ite_eq_left (compare_lt_iff_lt.mpr hlt), ite_eq_left hlt]; rfl
  · rw [ite_eq_right (by rw [compare_lt_iff_lt]; exact hlt), ite_eq_right hlt]
    simp [natToDigits]

/-- A `setIfLt` step only rewrites register `rd`. -/
lemma setIfLtMainImpl_growing_bounded_step_regs (rd rs rt : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.setIfLt rd rs rt) :
    (step r).regs = bankWrite r.regs rd (if r.regs rs < r.regs rt then 1 else 0) := by
  simp [step, hcurEq]

/-- The current instruction is `setIfLt` at the site's program counter. -/
lemma setIfLtMainImpl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfLt rd rs rt) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.setIfLt rd rs rt := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's compare entry. -/
lemma setIfLtMainImpl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfLt rd rs rt)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan)) := by
  have hstart : startPhaseOpt (Instruction.setIfLt rd rs rt)
      = some (SetIfLtPhase.compare CompareCorePhase.scan) := rfl
  have hentry : entryAt p pc.1
      = execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan) :=
    entryAt_eq_execVia p pc h _ hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `setIfLt` site run on the global machine: the compare/clear/write run transported
    via `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks and a step
    count bound. -/
lemma setIfLtMainImpl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan)))
    (rd' rs' rt' : Fin (regBound p))
    (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (hrs' : rs' = regAt p pc rs (by rw [h]; simp [regsOf]))
    (hrt' : rt' = regAt p pc rt (by rw [h]; simp [regsOf]))
    (hne' : rs' ≠ rt') (xs ys dest : List Digit)
    (hRs : cfg.stk (Kg.reg rs') = xs) (hRt : cfg.stk (Kg.reg rt') = ys)
    (hRd : cfg.stk (Kg.reg rd') = dest)
    (hL : cfg.stk (Kg.scratch ScratchKind.lhsOperand) = [])
    (hR : cfg.stk (Kg.scratch ScratchKind.rhsOperand) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ dest.length + 2 * (xs.length + ys.length) + 9 ∧
      Sgf = Function.update
        (Function.update (Function.update cfg.stk (Kg.reg rs') xs) (Kg.reg rt') ys)
        (Kg.reg rd')
        (if scanCompare Ordering.eq xs ys = Ordering.lt
          then [(⟨1, by norm_num⟩ : Digit)] else []) := by
  have hag := setIfLtCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd', ← hrs', ← hrt'] at hag
  obtain ⟨n1, hn1, hn1bound⟩ :=
    flipBindSetIfLt_run_bounded rd' rs' rt' hne' xs ys dest cfg.stk hRs hRt hRd hL hR
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getSetIfLt AllInstrState.setSetIfLt (setIfLtProg rd' rs' rt') M
      Function.injective_id AllInstrState.getSetIfLt_setSetIfLt
      AllInstrState.setSetIfLt_setSetIfLt AllInstrState.setSetIfLt_getSetIfLt
      _ (SetIfLtPhase.compare CompareCorePhase.scan) (⟨none, none, .eq⟩ : CompareState) cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      SetIfLtPhase.done
      (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩ : CompareState)
      (Function.update
        (Function.update (Function.update cfg.stk (Kg.reg rs') xs) (Kg.reg rt') ys) (Kg.reg rd')
        (if scanCompare Ordering.eq xs ys = Ordering.lt
          then [(⟨1, by norm_num⟩ : Digit)] else []))
      rfl hag hn1
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h SetIfLtPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h SetIfLtPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h SetIfLtPhase.done)) sf Sgf) from rfl,
      setIfLtCode_agrees_done p pc rd rs rt h M hAgrees, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan)),
      AllInstrState.canonical, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨n1 + 1, Sgf, ?_, by omega, funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `setIfLt` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma setIfLtMainImpl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrdval : rd'.1 = rd) (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt)
    (hcurEq : r.current = Instruction.setIfLt rd rs rt)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update
      (Function.update (Function.update stk (Kg.reg rs') (natToDigits (r.regs rs)))
        (Kg.reg rt') (natToDigits (r.regs rt))) (Kg.reg rd')
      (natToDigits (if r.regs rs < r.regs rt then 1 else 0))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  have hRs : stk (Kg.reg rs') = natToDigits (r.regs rs) := by
    simpa [hrsval] using hregs rs'
  have hRt : stk (Kg.reg rt') = natToDigits (r.regs rt) := by
    simpa [hrtval] using hregs rt'
  rw [update2_self stk (Kg.reg rs') (Kg.reg rt') _ _ hRs hRt]
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [setIfLtMainImpl_growing_bounded_step_regs rd rs rt r hcurEq]
    by_cases hi : i = rd'
    · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
    · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
      rw [bankWrite_diff _ _ _ _ hid,
        Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
      exact hregs i
  · rw [Function.update_of_ne (hk rd')]

/-- The configuration reached after a `setIfLt` run represents the stepped RAM, given the
    register frame and the untouched non-register stacks. -/
lemma setIfLtMainImpl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.setIfLt rd rs rt)
    (Sgf : ∀ k, List (Γg p k))
    (hreg : ∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    Represents p ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ (step r) := by
  obtain ⟨hprog, -, ⟨log, hmemstk, hmemlookup⟩, -, hscratch, -⟩ := hRep
  have hpcSucc : (step r).pc = pc.1 + 1 := by simp [step, hcurEq]; simpa using hpcEq
  refine ⟨by simp [step, hcurEq, hprog], hreg, ⟨log, ?_, ?_⟩, rfl, ?_, ?_⟩
  · show Sgf Kg.mem = _
    rw [hother _ (by simp)]; exact hmemstk
  · intro a; rw [step, hcurEq]; exact hmemlookup a
  · intro s; show Sgf (Kg.scratch s) = _
    rw [hother _ (by simp)]; exact hscratch s
  · simp only [ControlRep]; exact congrArg some (congrArg (entryAt p) hpcSucc.symm)

/-- Step-count bound: the run's cost is at most `64` times the squared potential, since each of
    the three operand lengths is bounded by `regSize`. -/
lemma setIfLtMainImpl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rd rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrdval : rd'.1 = rd) (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt) (n : ℕ)
    (hn : n ≤ (natToDigits (r.regs rd)).length +
      2 * ((natToDigits (r.regs rs)).length + (natToDigits (r.regs rt)).length) + 9) :
    n ≤ 64 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle1 := natToDigits_length_le_regSize p r rd'
  have hle2 := natToDigits_length_le_regSize p r rs'
  have hle3 := natToDigits_length_le_regSize p r rt'
  rw [hrdval] at hle1
  rw [hrsval] at hle2
  rw [hrtval] at hle3
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  have hlX : regSize p r + 1 ≤ X ^ 2 := le_trans (by omega : regSize p r + 1 ≤ X) hXsq
  omega

/-- Potential growth: only `rd` changes, to at most one digit, and the memory stack is untouched. -/
lemma setIfLtMainImpl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs rt : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.setIfLt rd rs rt) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := setIfLtMainImpl_growing_bounded_step_regs rd rs rt r hcurEq
  have hnewlen : (natToDigits (if r.regs rs < r.regs rt then 1 else 0)).length ≤ 1 := by
    by_cases hlt : r.regs rs < r.regs rt <;> simp [hlt, natToDigits]
  have hgrow : regSize p (step r) ≤ regSize p r + 1 := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' _ 1 hnewlen
  rw [hother _ (by simp)]
  omega

/-- `setIfLtMainImpl`'s growth companion: `mem` is untouched, and the only register that can grow
    is `rd`, to a single `0`/`1` digit (`length ≤ 1`), trivially `≤ instructionCost + 1`. -/
lemma setIfLtMainImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .setIfLt rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfLtCode p pc rd rs rt h) 64 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := setIfLtMainImpl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := setIfLtMainImpl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rt', hrt'⟩ : ∃ x, x = regAt p pc rt (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hrtval : rt'.1 = rt := by rw [hrt']; rfl
  have hne' : rs' ≠ rt' := fun heq => hrsrt (by rw [← hrsval, ← hrtval, heq])
  have hRs : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  have hRt : cfg.stk (Kg.reg rt') = natToDigits (r.regs rt) := by rw [hregs rt', hrtval]
  have hRd : cfg.stk (Kg.reg rd') = natToDigits (r.regs rd) := by rw [hregs rd', hrdval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := setIfLtMainImpl_growing_bounded_run p pc rd rs rt h M hAgrees
    cfg hvar hcl rd' rs' rt' hrd' hrs' hrt' hne' _ _ _ hRs hRt hRd (hscratch .lhsOperand)
    (hscratch .rhsOperand)
  rw [setIfLtMainImpl_growing_bounded_result_digits] at hSgf
  obtain ⟨hreg, hother⟩ := setIfLtMainImpl_growing_bounded_stk cfg.stk r rd rs rt rd' rs' rt'
    hrdval hrsval hrtval hcurEq hregs Sgf hSgf
  exact ⟨n, _, hrun,
    setIfLtMainImpl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    setIfLtMainImpl_growing_bounded_time p cfg r rd rs rt rd' rs' rt' hrdval hrsval hrtval n hn,
    setIfLtMainImpl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩

/-- The realized non-aliased `setIfLt` site: its `sim` is `setIfLtMainImpl_growingBoundedSiteStepSim`
    forgetting the growth and step-count conjuncts. -/
def setIfLtMainImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .setIfLt rd rs rt) : InstrImpl p pc where
  code := setIfLtCode p pc rd rs rt h
  sim := siteStepSim_of_boundedSiteStepSim p pc _ 64
    (boundedSiteStepSim_of_growingBoundedSiteStepSim p pc _ 64 1
      (setIfLtMainImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h))

/-- `setIfLt`'s local `Stmt` tree for the *aliased* case (`rs = rt`), self-contained against
    `SetIfLtPhase`/`CompareState` (mirroring `setIfLtProg`'s standalone shape, module docstring):
    the entry phase skips straight to `clearDest` (no register access, comparison trivially
    `.eq`), `clearDest`/`writeResult` are `setIfLtProg`'s own trees (only `rd` is ever read/
    written there), other `compare` phases are unreachable placeholders. -/
def setIfLtAliasedProg (rd : Fin (regBound p)) :
    SetIfLtPhase → Turing.TM2.Stmt (Γg p) SetIfLtPhase CompareState
  | .compare CompareCorePhase.scan => goto (fun _ => .clearDest)
  | .compare _ => halt
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .writeResult)))
  | .writeResult =>
      branch (fun s => decide (s.acc = Ordering.lt))
        (push (Kg.reg rd) (fun _ => (⟨1, by norm_num⟩ : Digit)) (goto (fun _ => .done)))
        (goto (fun _ => .done))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindSetIfLtAliased (rd : Fin (regBound p)) :
    Option (Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (setIfLtAliasedProg rd))

lemma flipBindSetIfLtAliased_scan_step (rd : Fin (regBound p)) (v0 : CompareState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindSetIfLtAliased rd
        (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan), v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfLtAliasedProg rd))
      (⟨some (SetIfLtPhase.compare CompareCorePhase.scan), v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtAliasedProg]

lemma flipBindSetIfLtAliased_clearDest_cons (rd : Fin (regBound p)) (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindSetIfLtAliased rd
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.clearDest, ({v0 with left := some d} : CompareState),
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (setIfLtAliasedProg rd))
      (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtAliasedProg, hRd]

lemma flipBindSetIfLtAliased_clearDest_nil_exit (rd : Fin (regBound p))
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindSetIfLtAliased rd
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.writeResult, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (setIfLtAliasedProg rd))
      (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtAliasedProg, hRd]

/-- Draining register `rd`'s content and finishing at `writeResult`, for the aliased local
    program (mirroring `flipBindSetIfLt_clearDest_loop`). -/
lemma flipBindSetIfLtAliased_clearDest_loop (rd : Fin (regBound p)) (dest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfLtAliased rd)^[dest.length + 1]
        (some (⟨some SetIfLtPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.writeResult, ({v0 with left := none} : CompareState),
          Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k; by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindSetIfLtAliased_clearDest_nil_exit rd Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSetIfLtAliased_clearDest_cons rd d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') ({v0 with left := some d} : CompareState)
          (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

lemma flipBindSetIfLtAliased_writeResult_ne_lt (rd : Fin (regBound p)) (Sg : ∀ k, List (Γg p k))
    (v0 : CompareState) (hacc : v0.acc ≠ Ordering.lt) :
    flipBindSetIfLtAliased rd
        (some (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.done, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfLtAliasedProg rd))
      (⟨some SetIfLtPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState) = _
  simp [setIfLtAliasedProg, hacc]

/-- The whole aliased-`setIfLt` run: skip to `clearDest` (1 step), drain `rd`
    (`flipBindSetIfLtAliased_clearDest_loop`), then `writeResult`'s no-push branch (`acc = .eq`, never
    `.lt`) — `rd` ends drained to empty (`0`). -/
lemma flipBindSetIfLtAliased_run (rd : Fin (regBound p)) (dest : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfLtAliased rd)^[dest.length + 1 + 1 + 1]
        (some (⟨some (SetIfLtPhase.compare CompareCorePhase.scan),
          (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfLtPhase CompareState))
      = some ⟨some SetIfLtPhase.done, (⟨none, none, .eq⟩ : CompareState),
          Function.update Sg (Kg.reg rd) []⟩ := by
  rw [show dest.length + 1 + 1 + 1 = (dest.length + 1 + 1) + 1 from rfl,
    Function.iterate_succ_apply, flipBindSetIfLtAliased_scan_step,
    show dest.length + 1 + 1 = (dest.length + 1) + 1 from rfl, Function.iterate_succ_apply',
    flipBindSetIfLtAliased_clearDest_loop rd dest Sg (⟨none, none, .eq⟩ : CompareState) hRd]
  exact flipBindSetIfLtAliased_writeResult_ne_lt rd (Function.update Sg (Kg.reg rd) [])
    (⟨none, none, .eq⟩ : CompareState) (by simp)

/-! ## Site dispatcher package, aliased register pair (`rs = rt`) -/

/-- `setIfLt`'s `Stmt` tree at site `pc` for the *aliased* case: `done` unconditionally bridges
    to `pc.1+1` (matching `setIfLtCodeBody`), every other phase is `setIfLtAliasedProg` lifted
    via `execVia`. -/
def setIfLtAliasedCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) :
    SetIfLtPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = SetIfLtPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getSetIfLt AllInstrState.setSetIfLt
        (setIfLtAliasedProg (regAt p pc rd (by rw [h]; simp [regsOf])) l)

/-- `setIfLtAliasedCodeBody`, cast once to the `SiteCode p pc` shape. -/
def setIfLtAliasedCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (setIfLtAliasedCodeBody p pc rd rs rt h)

lemma setIfLtAliasedCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) (l : SetIfLtPhase) :
    setIfLtAliasedCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l)
      = setIfLtAliasedCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (setIfLtAliasedCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `setIfLtAliasedCode` at site `pc` installs the lifted
    `setIfLtAliasedProg` tree at every non-`done` label. -/
lemma setIfLtAliasedCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtAliasedCode p pc rd rs rt h) M) :
    ∀ l : SetIfLtPhase, l ≠ SetIfLtPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getSetIfLt AllInstrState.setSetIfLt
        (setIfLtAliasedProg (regAt p pc rd (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    setIfLtAliasedCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `setIfLtAliasedCode` at site `pc` installs `bridgeTo p (pc.1+1)`
    at `setIfLt`'s own `done` label. -/
lemma setIfLtAliasedCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtAliasedCode p pc rd rs rt h) M) :
    M (execVia p pc h SetIfLtPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) SetIfLtPhase.done)
  rw [show execVia p pc h SetIfLtPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) SetIfLtPhase.done) from rfl, hone,
    setIfLtAliasedCode_apply]
  rfl

/-! ## Quantitative companion, aliased register pair -/

/-- The whole aliased-`setIfLt` site run on the global machine: `flipBindSetIfLtAliased_run` transported
    via `iterate_bind_step_liftStmt`, then the unconditional bridge to the next entry; only `rd` changes. -/
lemma setIfLtAliasedImpl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfLt rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfLtAliasedCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan)))
    (rd' : Fin (regBound p)) (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (dest : List Digit) (hRd : cfg.stk (Kg.reg rd') = dest) :
    ∃ Sgf, (flipBindG p M)^[dest.length + 1 + 1 + 1 + 1] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') [] := by
  have hag := setIfLtAliasedCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd'] at hag
  have hAliasedRun := flipBindSetIfLtAliased_run rd' dest cfg.stk hRd
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getSetIfLt AllInstrState.setSetIfLt (setIfLtAliasedProg rd') M
      Function.injective_id AllInstrState.getSetIfLt_setSetIfLt
      AllInstrState.setSetIfLt_setSetIfLt AllInstrState.setSetIfLt_getSetIfLt
      _ (SetIfLtPhase.compare CompareCorePhase.scan) (⟨none, none, .eq⟩ : CompareState) cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      SetIfLtPhase.done (⟨none, none, .eq⟩ : CompareState)
      (Function.update cfg.stk (Kg.reg rd') [])
      rfl hag hAliasedRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h SetIfLtPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h SetIfLtPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h SetIfLtPhase.done)) sf Sgf) from rfl,
      setIfLtAliasedCode_agrees_done p pc rd rs rt h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h (SetIfLtPhase.compare CompareCorePhase.scan)),
      AllInstrState.canonical, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨Sgf, ?_, funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of an aliased-`setIfLt` run encode the stepped registers on every register
    stack (only `rd` is rewritten) and agree with the initial stacks everywhere else. -/
lemma setIfLtAliasedImpl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (hnew : (step r).regs = bankWrite r.regs rd 0) (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') []) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [hnew]
    by_cases hi : i = rd'
    · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
      simp [natToDigits]
    · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
      rw [bankWrite_diff _ _ _ _ hid,
        Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
      exact hregs i
  · exact Function.update_of_ne (hk rd') _ _

/-- Step-count bound: the aliased run costs `dest.length + 4` steps, at most `8` times the squared
    potential since `rd`'s length is bounded by `regSize`. -/
lemma setIfLtAliasedImpl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd) (n : ℕ)
    (hn : n ≤ (natToDigits (r.regs rd)).length + 4) :
    n ≤ 8 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle := natToDigits_length_le_regSize p r rd'
  rw [hrdval] at hle
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  have hlX : regSize p r + 1 ≤ X ^ 2 := le_trans (by omega : regSize p r + 1 ≤ X) hXsq
  omega

/-- Potential growth: `rd` is drained to empty and the memory stack is untouched, so the potential
    cannot grow at all. -/
lemma setIfLtAliasedImpl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hnew : (step r).regs = bankWrite r.regs rd 0) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 0 * (instructionCost r.regs r.mem r.current + 1) := by
  have hgrow : regSize p (step r) ≤ regSize p r := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hnew, ← hrdval]
    have := regSize_bankWrite_le p r rd' 0 0 (by simp [natToDigits])
    omega
  rw [hother _ (by simp)]
  omega

/-- `setIfLtAliasedImpl`'s growth companion: `mem` is untouched, and `rd` is drained to `[]`
    (`r.regs rs < r.regs rt` fails by `hrsrt : rs = rt`), so `regSize` cannot grow at all
    (`G = 0`). -/
lemma setIfLtAliasedImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs = rt) (h : p.get pc = .setIfLt rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfLtAliasedCode p pc rd rs rt h) 8 0 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hcurEq := setIfLtMainImpl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := setIfLtMainImpl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hRd : cfg.stk (Kg.reg rd') = natToDigits (r.regs rd) := by rw [hregs rd', hrdval]
  have hnew : (step r).regs = bankWrite r.regs rd 0 := by simp [step, hcurEq, hrsrt]
  obtain ⟨Sgf, hrun, hSgf⟩ := setIfLtAliasedImpl_growing_bounded_run p pc rd rs rt h M hAgrees cfg
    hvar hcl rd' hrd' _ hRd
  obtain ⟨hreg, hother⟩ := setIfLtAliasedImpl_growing_bounded_stk cfg.stk r rd rd' hrdval hregs hnew
    Sgf hSgf
  exact ⟨_, _, hrun,
    setIfLtMainImpl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    setIfLtAliasedImpl_growing_bounded_time p cfg r rd rd' hrdval _ (by omega),
    setIfLtAliasedImpl_growing_bounded_growth p cfg r rd rd' hrdval hnew Sgf hother⟩


/-- The realized aliased-`setIfLt` site: its `sim` is `setIfLtAliasedImpl_growingBoundedSiteStepSim`
    forgetting the growth and step-count conjuncts. -/
def setIfLtAliasedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs = rt) (h : p.get pc = .setIfLt rd rs rt) : InstrImpl p pc where
  code := setIfLtAliasedCode p pc rd rs rt h
  sim := siteStepSim_of_boundedSiteStepSim p pc _ 8
    (boundedSiteStepSim_of_growingBoundedSiteStepSim p pc _ 8 0
      (setIfLtAliasedImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h))

/-- The realized `setIfLt` site: `setIfLtAliasedImpl` when `rs = rt` (decidable on the raw `ℕ`
    operands), `setIfLtMainImpl` otherwise — the meta-level split the lockstep-pop compare core
    requires (module docstring). -/
def setIfLtImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) : InstrImpl p pc :=
  if hrsrt : rs = rt then setIfLtAliasedImpl p pc rd rs rt hrsrt h
  else setIfLtMainImpl p pc rd rs rt hrsrt h

/-- `setIfLtImpl`'s growth companion: dispatches to `setIfLtAliasedImpl_growingBoundedSiteStepSim`
    (`G = 0`, weakened to `1`) or `setIfLtMainImpl_growingBoundedSiteStepSim` (`G = 1` already), mirroring
    `setIfLtImpl`'s own `rs = rt` case split. -/
lemma setIfLtImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfLtImpl p pc rd rs rt h).code 64 1 := by
  unfold setIfLtImpl
  by_cases hrsrt : rs = rt
  · simp only [dite_eq_left hrsrt]
    intro M hAgrees cfg r hRep hpcEq hcur
    obtain ⟨n, cfg', hrun, hRepr, hio, hbound, hgrowth⟩ :=
      setIfLtAliasedImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h M hAgrees cfg r hRep hpcEq hcur
    exact ⟨n, cfg', hrun, hRepr, hio, by omega, by omega⟩
  · simp only [dite_eq_right hrsrt]
    exact setIfLtMainImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h

/-- `setIfLt`'s `GrowingTimedInstrImpl` package. -/
def setIfLtGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfLt rd rs rt) : GrowingTimedInstrImpl p pc where
  code := (setIfLtImpl p pc rd rs rt h).code
  C := 64
  G := 1
  growingSim := setIfLtImpl_growingBoundedSiteStepSim p pc rd rs rt h

end NPComplete.RAMToTM.Generic

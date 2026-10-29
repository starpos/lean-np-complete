module

public import NPComplete.RAMToTM.Generic.Machine.GenericCompare
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `setIfEq` realized against an arbitrary site's register triple

`setIfEq rd rs rt`'s effect is the shared compare core (`GenericCompare.lean`) followed by
draining `rd` (`clearDest`, mirroring `GenericSetIfLt.lean`'s `clearDest`) and pushing a single
`1` digit iff the comparison was `.eq` (nothing, i.e. `0`, otherwise). `SetIfEqPhase`
(`GenericProgramMachine.lean`) embeds `CompareCorePhase` via `compare`, with
`clearDest`/`writeResult`/`done` the extra phases: `.compare .done` bridges to `clearDest`, `done`
is `halt` locally, overridden at the site level with the uniform `bridgeTo p (pc.1+1)` (unlike
`branchIfLt`, `setIfEq`'s control flow never depends on the comparison outcome, only `rd`'s content
does).

**`rd` alias safety, for free**: by the time `clearDest` runs, the compare core has already fully
restored `rs`/`rt` to their original content (`GenericCompare.lean`'s `compare_core_run_bounded`), so
draining `rd` — even if `rd = rs`/`rd = rt` (the same physical stack) — only discards a value no
longer needed; the machine's `Stmt` tree does not branch on whether `rd` aliases `rs`/`rt`,
matching `GenericSetIfLt.lean`'s `clearDest` reasoning.

`rs = rt`: `setIfEqImpl` dispatches with an `if` on the raw `ℕ` operands, exactly as in
`GenericSetIfLt.lean`. The aliased tree skips comparison because the sources are equal, so
`writeResult` always writes `1` to `rd`, whether or not `rd` aliases a source; in particular,
`setIfEq rd rd rd` sets `rd` to `1`. -/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits scanCompare scanCompare_eq_compareDigits
  compareDigits compareDigits_natToDigits)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs rt : Fin (regBound p))

/-- `setIfEq`'s local `Stmt` tree, self-contained against `SetIfEqPhase`/`CompareState`: the
    shared compare core is embedded via `liftStmt` at every non-`done` `compare` phase,
    `.compare .done` bridges to `clearDest` (draining `rd`, reusing `left` as the popped-digit
    scratch — safe since the compare core's own use of `left` is long finished by then),
    `writeResult` pushes `1` iff `acc = .eq`, and `.done` is `halt`
    (`StmtTransport`'s fixed-exit requirement, overridden at the site level). -/
def setIfEqProg : SetIfEqPhase → Turing.TM2.Stmt (Γg p) SetIfEqPhase CompareState
  | .compare ph =>
      if ph = CompareCorePhase.done then goto (fun _ => .clearDest)
      else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfEqPhase.compare
        id (fun _ v => v) (compareCoreProg rs rt ph)
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .writeResult)))
  | .writeResult =>
      branch (fun s => decide (s.acc = Ordering.eq))
        (push (Kg.reg rd) (fun _ => (⟨1, by norm_num⟩ : Digit)) (goto (fun _ => .done)))
        (goto (fun _ => .done))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindSetIfEq :
    Option (Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (setIfEqProg rd rs rt))

/-- Any dispatcher agreeing with `setIfEqProg` at every non-`done` `compare` phase installs the
    lifted compare core there — trivially true by `setIfEqProg`'s own definition. -/
lemma setIfEqProg_agrees :
    ∀ l : CompareCorePhase, l ≠ CompareCorePhase.done →
      setIfEqProg rd rs rt (SetIfEqPhase.compare l)
        = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfEqPhase.compare
            id (fun _ v => v) (compareCoreProg rs rt l) := by
  intro l hl
  simp [setIfEqProg, hl]

lemma flipBindSetIfEq_compare_done_step (v0 : CompareState) (Sg : ∀ k, List (Γg p k)) :
    flipBindSetIfEq rd rs rt
        (some (⟨some (SetIfEqPhase.compare CompareCorePhase.done), v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfEqProg rd rs rt))
      (⟨some (SetIfEqPhase.compare CompareCorePhase.done), v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqProg]

/-! ## `clearDest`: draining whatever `rd` currently holds -/

lemma flipBindSetIfEq_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindSetIfEq rd rs rt
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, ({v0 with left := some d} : CompareState),
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (setIfEqProg rd rs rt))
      (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqProg, hRd]

lemma flipBindSetIfEq_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindSetIfEq rd rs rt
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.writeResult, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (setIfEqProg rd rs rt))
      (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqProg, hRd]

/-- Draining register `rd`, discarding its content (no scratch relay needed, mirroring
    `GenericSetIfLt.lean`'s `flipBindSetIfLt_clearDest_loop`). -/
lemma flipBindSetIfEq_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfEq rd rs rt)^[dest.length + 1]
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.writeResult, ({v0 with left := none} : CompareState),
          Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k; by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindSetIfEq_clearDest_nil_exit rd rs rt Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSetIfEq_clearDest_cons rd rs rt d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') ({v0 with left := some d} : CompareState)
          (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `writeResult`: push `1` iff `acc = .eq` -/

lemma flipBindSetIfEq_writeResult_eq (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hacc : v0.acc = Ordering.eq) :
    flipBindSetIfEq rd rs rt
        (some (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.done, v0,
          Function.update Sg (Kg.reg rd) ((⟨1, by norm_num⟩ : Digit) :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (setIfEqProg rd rs rt))
      (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqProg, hacc]

lemma flipBindSetIfEq_writeResult_ne_eq (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hacc : v0.acc ≠ Ordering.eq) :
    flipBindSetIfEq rd rs rt
        (some (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.done, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfEqProg rd rs rt))
      (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqProg, hacc]

/-- The whole `setIfEqProg` run, with a bound on the witness step count combining
    `compare_core_run_bounded`'s bound with the already-closed-form `clearDest`/`writeResult`
    costs (mirrors `GenericSetIfLt.flipBindSetIfLt_run_bounded`). -/
lemma flipBindSetIfEq_run_bounded (hne : rs ≠ rt) (xs ys dest : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = xs) (hRt : Sg (Kg.reg rt) = ys) (hRd : Sg (Kg.reg rd) = dest)
    (hL : Sg (Kg.scratch .lhsOperand) = []) (hR : Sg (Kg.scratch .rhsOperand) = []) :
    ∃ n, (flipBindSetIfEq rd rs rt)^[n]
        (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan),
          (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.done,
          (⟨none, none, scanCompare .eq xs ys⟩ : CompareState),
          Function.update
            (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys)
            (Kg.reg rd)
            (if scanCompare .eq xs ys = Ordering.eq then [(⟨1, by norm_num⟩ : Digit)] else [])⟩ ∧
        n ≤ dest.length + 2 * (xs.length + ys.length) + 8 := by
  obtain ⟨n1, hn1, hn1bound⟩ := compare_core_run_bounded rs rt hne xs ys Sg
    (⟨none, none, .eq⟩ : CompareState) hRs hRt hL hR
  have hstkTriv : ∀ k, Sg (id k) = List.map (⇑(Equiv.refl (Γg p k))) (Sg k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) SetIfEqPhase.compare
      id (fun _ v => v) (compareCoreProg rs rt) (setIfEqProg rd rs rt)
      Function.injective_id (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      n1 CompareCorePhase.scan (⟨none, none, .eq⟩ : CompareState) Sg
      (⟨none, none, .eq⟩ : CompareState) Sg rfl hstkTriv
      CompareCorePhase.done (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩
        : CompareState)
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) rfl
      (setIfEqProg_agrees rd rs rt) hn1
  have hsfEq : sf = (⟨none, none, scanCompare .eq xs ys⟩ : CompareState) := hsetf
  have hSgfEq : Sgf = Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys := by
    funext k
    exact stack_eq_of_map_equiv_refl Sgf
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) hstkf k
  have hstep1 : flipBindSetIfEq rd rs rt
      (some (⟨some (SetIfEqPhase.compare CompareCorePhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, sf, Sgf⟩ :=
    flipBindSetIfEq_compare_done_step rd rs rt sf Sgf
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
  have hClear := flipBindSetIfEq_clearDest_loop rd rs rt dest Sgf sf hRdEq
  have hrun' : (flipBindSetIfEq rd rs rt)^[n1]
      (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some (SetIfEqPhase.compare CompareCorePhase.done), sf, Sgf⟩ := hrun
  have hcombined1 : (flipBindSetIfEq rd rs rt)^[n1 + 1]
      (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, sf, Sgf⟩ := by
    rw [Function.iterate_succ_apply', hrun']; exact hstep1
  have hcombined2 : (flipBindSetIfEq rd rs rt)^[(dest.length + 1) + (n1 + 1)]
      (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.writeResult, ({sf with left := none} : CompareState),
          Function.update Sgf (Kg.reg rd) []⟩ := by
    rw [Function.iterate_add_apply, hcombined1]; exact hClear
  refine ⟨(dest.length + 1) + (n1 + 1) + 1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hcombined2]
  by_cases heq : scanCompare Ordering.eq xs ys = Ordering.eq
  · rw [ite_eq_left heq, flipBindSetIfEq_writeResult_eq rd rs rt (Function.update Sgf (Kg.reg rd) [])
      ({sf with left := none} : CompareState)
      (show sf.acc = Ordering.eq from by rw [hsfEq]; exact heq)]
    simp only [hsfEq, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    by_cases hk : k = Kg.reg rd
    · subst hk; rw [Function.update_self, Function.update_self, Function.update_self]
    · simp [Function.update, hk, hSgfEq]
  · rw [ite_eq_right heq, flipBindSetIfEq_writeResult_ne_eq rd rs rt (Function.update Sgf (Kg.reg rd) [])
      ({sf with left := none} : CompareState)
      (show sf.acc ≠ Ordering.eq from by rw [hsfEq]; exact heq)]
    simp only [hsfEq, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    rw [hSgfEq]

/-! ## Site dispatcher package, non-aliased register triple -/

/-- `setIfEq`'s `Stmt` tree at site `pc`, before embedding into `Λg p`, for the *non-aliased*
    case: `done` unconditionally bridges to `pc.1+1` (`setIfEq`'s control flow never depends on
    the comparison outcome, only `rd`'s content does — unlike `branchIfLt`), every other phase is
    `setIfEqProg` lifted via `execVia`. -/
def setIfEqCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) :
    SetIfEqPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = SetIfEqPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getSetIfEq AllInstrState.setSetIfEq
        (setIfEqProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `setIfEqCodeBody`, cast once to the `SiteCode p pc` shape. -/
def setIfEqCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (setIfEqCodeBody p pc rd rs rt h)

/-- `setIfEqCode` undoes its own cast when applied to a correspondingly-cast `SetIfEqPhase`
    value. -/
lemma setIfEqCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) (l : SetIfEqPhase) :
    setIfEqCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l)
      = setIfEqCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (setIfEqCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `setIfEqCode` at site `pc` installs the lifted `setIfEqProg`
    tree at every non-`done` label. -/
lemma setIfEqCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqCode p pc rd rs rt h) M) :
    ∀ l : SetIfEqPhase, l ≠ SetIfEqPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getSetIfEq AllInstrState.setSetIfEq
        (setIfEqProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) (regAt p pc rt (by rw [h]; simp [regsOf])) l)
      := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    setIfEqCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `setIfEqCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `setIfEq`'s own `done` label. -/
lemma setIfEqCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqCode p pc rd rs rt h) M) :
    M (execVia p pc h SetIfEqPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) SetIfEqPhase.done)
  rw [show execVia p pc h SetIfEqPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) SetIfEqPhase.done) from rfl, hone,
    setIfEqCode_apply]
  rfl

/-! ## Quantitative companion -/

/-- The `writeResult` output `[1]`/`[]` is the digit encoding of the `0`/`1` that `setIfEq`
    writes, which lets the register frame be stated against `natToDigits`. -/
lemma setIfEqMainImpl_growing_bounded_result_digits (a b : ℕ) :
    (if scanCompare Ordering.eq (natToDigits a) (natToDigits b) = Ordering.eq
      then [(⟨1, by norm_num⟩ : Digit)] else [])
      = natToDigits (if a = b then 1 else 0) := by
  rw [scanCompare_eq_compareDigits]
  have hthEq : ∀ x : Ordering, x.then Ordering.eq = x := fun x => by cases x <;> rfl
  rw [hthEq, compareDigits_natToDigits]
  by_cases heq : a = b
  · rw [ite_eq_left (compare_eq_iff_eq.mpr heq), ite_eq_left heq]; rfl
  · rw [ite_eq_right (by rw [compare_eq_iff_eq]; exact heq), ite_eq_right heq]
    simp [natToDigits]

/-- A `setIfEq` step only rewrites register `rd`. -/
lemma setIfEqMainImpl_growing_bounded_step_regs (rd rs rt : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.setIfEq rd rs rt) :
    (step r).regs = bankWrite r.regs rd (if r.regs rs = r.regs rt then 1 else 0) := by
  simp [step, hcurEq]

/-- The current instruction is `setIfEq` at the site's program counter. -/
lemma setIfEqMainImpl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfEq rd rs rt) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.setIfEq rd rs rt := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's compare entry. -/
lemma setIfEqMainImpl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfEq rd rs rt)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan)) := by
  have hstart : startPhaseOpt (Instruction.setIfEq rd rs rt)
      = some (SetIfEqPhase.compare CompareCorePhase.scan) := rfl
  have hentry : entryAt p pc.1
      = execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan) :=
    entryAt_eq_execVia p pc h _ hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `setIfEq` site run on the global machine: the compare/clear/write run transported
    via `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks and a step
    count bound. -/
lemma setIfEqMainImpl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan)))
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
        (if scanCompare Ordering.eq xs ys = Ordering.eq
          then [(⟨1, by norm_num⟩ : Digit)] else []) := by
  have hag := setIfEqCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd', ← hrs', ← hrt'] at hag
  obtain ⟨n1, hn1, hn1bound⟩ :=
    flipBindSetIfEq_run_bounded rd' rs' rt' hne' xs ys dest cfg.stk hRs hRt hRd hL hR
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getSetIfEq AllInstrState.setSetIfEq (setIfEqProg rd' rs' rt') M
      Function.injective_id AllInstrState.getSetIfEq_setSetIfEq
      AllInstrState.setSetIfEq_setSetIfEq AllInstrState.setSetIfEq_getSetIfEq
      _ (SetIfEqPhase.compare CompareCorePhase.scan) (⟨none, none, .eq⟩ : CompareState) cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      SetIfEqPhase.done
      (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩ : CompareState)
      (Function.update
        (Function.update (Function.update cfg.stk (Kg.reg rs') xs) (Kg.reg rt') ys) (Kg.reg rd')
        (if scanCompare Ordering.eq xs ys = Ordering.eq
          then [(⟨1, by norm_num⟩ : Digit)] else []))
      rfl hag hn1
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h SetIfEqPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h SetIfEqPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h SetIfEqPhase.done)) sf Sgf) from rfl,
      setIfEqCode_agrees_done p pc rd rs rt h M hAgrees, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan)),
      AllInstrState.canonical, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨n1 + 1, Sgf, ?_, by omega, funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `setIfEq` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma setIfEqMainImpl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrdval : rd'.1 = rd) (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt)
    (hcurEq : r.current = Instruction.setIfEq rd rs rt)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update
      (Function.update (Function.update stk (Kg.reg rs') (natToDigits (r.regs rs)))
        (Kg.reg rt') (natToDigits (r.regs rt))) (Kg.reg rd')
      (natToDigits (if r.regs rs = r.regs rt then 1 else 0))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  have hRs : stk (Kg.reg rs') = natToDigits (r.regs rs) := by
    simpa [hrsval] using hregs rs'
  have hRt : stk (Kg.reg rt') = natToDigits (r.regs rt) := by
    simpa [hrtval] using hregs rt'
  rw [update2_self stk (Kg.reg rs') (Kg.reg rt') _ _ hRs hRt]
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [setIfEqMainImpl_growing_bounded_step_regs rd rs rt r hcurEq]
    by_cases hi : i = rd'
    · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
    · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
      rw [bankWrite_diff _ _ _ _ hid,
        Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
      exact hregs i
  · rw [Function.update_of_ne (hk rd')]

/-- The configuration reached after a `setIfEq` run represents the stepped RAM, given the
    register frame and the untouched non-register stacks. -/
lemma setIfEqMainImpl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.setIfEq rd rs rt)
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
lemma setIfEqMainImpl_growing_bounded_time (p : List Instruction)
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
lemma setIfEqMainImpl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs rt : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.setIfEq rd rs rt) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := setIfEqMainImpl_growing_bounded_step_regs rd rs rt r hcurEq
  have hnewlen : (natToDigits (if r.regs rs = r.regs rt then 1 else 0)).length ≤ 1 := by
    by_cases heq : r.regs rs = r.regs rt <;> simp [heq, natToDigits]
  have hgrow : regSize p (step r) ≤ regSize p r + 1 := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' _ 1 hnewlen
  rw [hother _ (by simp)]
  omega

/-- `setIfEqMainImpl`'s growth companion: `mem` is untouched, and the only register that can grow
    is `rd`, to a single `0`/`1` digit (`length ≤ 1`), trivially `≤ instructionCost + 1`. -/
lemma setIfEqMainImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .setIfEq rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfEqCode p pc rd rs rt h) 64 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := setIfEqMainImpl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := setIfEqMainImpl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
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
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := setIfEqMainImpl_growing_bounded_run p pc rd rs rt h M hAgrees
    cfg hvar hcl rd' rs' rt' hrd' hrs' hrt' hne' _ _ _ hRs hRt hRd (hscratch .lhsOperand)
    (hscratch .rhsOperand)
  rw [setIfEqMainImpl_growing_bounded_result_digits] at hSgf
  obtain ⟨hreg, hother⟩ := setIfEqMainImpl_growing_bounded_stk cfg.stk r rd rs rt rd' rs' rt'
    hrdval hrsval hrtval hcurEq hregs Sgf hSgf
  exact ⟨n, _, hrun,
    setIfEqMainImpl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    setIfEqMainImpl_growing_bounded_time p cfg r rd rs rt rd' rs' rt' hrdval hrsval hrtval n hn,
    setIfEqMainImpl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩

/-- The realized non-aliased `setIfEq` site: its `sim` is `setIfEqMainImpl_growingBoundedSiteStepSim`
    forgetting the growth and step-count conjuncts. -/
def setIfEqMainImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .setIfEq rd rs rt) : InstrImpl p pc where
  code := setIfEqCode p pc rd rs rt h
  sim := siteStepSim_of_boundedSiteStepSim p pc _ 64
    (boundedSiteStepSim_of_growingBoundedSiteStepSim p pc _ 64 1
      (setIfEqMainImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h))

/-- `setIfEq`'s local `Stmt` tree for the *aliased* case (`rs = rt`), self-contained against
    `SetIfEqPhase`/`CompareState` (mirroring `setIfEqProg`'s standalone shape, module docstring):
    the entry phase skips straight to `clearDest` (no register access, comparison trivially
    `.eq`), `clearDest`/`writeResult` are `setIfEqProg`'s own trees (only `rd` is ever read/
    written there), other `compare` phases are unreachable placeholders. -/
def setIfEqAliasedProg (rd : Fin (regBound p)) :
    SetIfEqPhase → Turing.TM2.Stmt (Γg p) SetIfEqPhase CompareState
  | .compare CompareCorePhase.scan => goto (fun _ => .clearDest)
  | .compare _ => halt
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .writeResult)))
  | .writeResult =>
      branch (fun s => decide (s.acc = Ordering.eq))
        (push (Kg.reg rd) (fun _ => (⟨1, by norm_num⟩ : Digit)) (goto (fun _ => .done)))
        (goto (fun _ => .done))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindSetIfEqAliased (rd : Fin (regBound p)) :
    Option (Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (setIfEqAliasedProg rd))

lemma flipBindSetIfEqAliased_scan_step (rd : Fin (regBound p)) (v0 : CompareState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindSetIfEqAliased rd
        (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan), v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, v0, Sg⟩ := by
  show (Turing.TM2.step (setIfEqAliasedProg rd))
      (⟨some (SetIfEqPhase.compare CompareCorePhase.scan), v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqAliasedProg]

lemma flipBindSetIfEqAliased_clearDest_cons (rd : Fin (regBound p)) (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindSetIfEqAliased rd
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.clearDest, ({v0 with left := some d} : CompareState),
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (setIfEqAliasedProg rd))
      (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqAliasedProg, hRd]

lemma flipBindSetIfEqAliased_clearDest_nil_exit (rd : Fin (regBound p))
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindSetIfEqAliased rd
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.writeResult, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (setIfEqAliasedProg rd))
      (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqAliasedProg, hRd]

/-- Draining register `rd`'s content and finishing at `writeResult`, for the aliased local
    program (mirroring `flipBindSetIfEq_clearDest_loop`). -/
lemma flipBindSetIfEqAliased_clearDest_loop (rd : Fin (regBound p)) (dest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfEqAliased rd)^[dest.length + 1]
        (some (⟨some SetIfEqPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.writeResult, ({v0 with left := none} : CompareState),
          Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k; by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindSetIfEqAliased_clearDest_nil_exit rd Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSetIfEqAliased_clearDest_cons rd d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') ({v0 with left := some d} : CompareState)
          (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-- **Differs from `flipBindSetIfLtAliased_writeResult_ne_lt`**: the aliased compare result is always
    `.eq` (`rs = rt`), which is exactly `setIfEq`'s push condition — so unlike `setIfLt`'s aliased
    case (which never pushes, draining `rd` to `0`), `setIfEq rd rd rd` always pushes `1`. -/
lemma flipBindSetIfEqAliased_writeResult_eq (rd : Fin (regBound p)) (Sg : ∀ k, List (Γg p k))
    (v0 : CompareState) (hacc : v0.acc = Ordering.eq) :
    flipBindSetIfEqAliased rd
        (some (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.done, v0,
          Function.update Sg (Kg.reg rd) ((⟨1, by norm_num⟩ : Digit) :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (setIfEqAliasedProg rd))
      (⟨some SetIfEqPhase.writeResult, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState) = _
  simp [setIfEqAliasedProg, hacc]

/-- The whole aliased-`setIfEq` run: skip to `clearDest` (1 step), drain `rd`
    (`flipBindSetIfEqAliased_clearDest_loop`), then `writeResult`'s push branch (`acc = .eq`, always) —
    `rd` ends holding a single `1` digit (module docstring: unlike `setIfLt`, the aliased case
    here always fires the push). -/
lemma flipBindSetIfEqAliased_run (rd : Fin (regBound p)) (dest : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSetIfEqAliased rd)^[dest.length + 1 + 1 + 1]
        (some (⟨some (SetIfEqPhase.compare CompareCorePhase.scan),
          (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) SetIfEqPhase CompareState))
      = some ⟨some SetIfEqPhase.done, (⟨none, none, .eq⟩ : CompareState),
          Function.update Sg (Kg.reg rd) [(⟨1, by norm_num⟩ : Digit)]⟩ := by
  rw [show dest.length + 1 + 1 + 1 = (dest.length + 1 + 1) + 1 from rfl,
    Function.iterate_succ_apply, flipBindSetIfEqAliased_scan_step,
    show dest.length + 1 + 1 = (dest.length + 1) + 1 from rfl, Function.iterate_succ_apply',
    flipBindSetIfEqAliased_clearDest_loop rd dest Sg (⟨none, none, .eq⟩ : CompareState) hRd]
  rw [flipBindSetIfEqAliased_writeResult_eq rd (Function.update Sg (Kg.reg rd) [])
    (⟨none, none, .eq⟩ : CompareState) rfl]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.reg rd
  · subst hk; rw [Function.update_self, Function.update_self, Function.update_self]
  · simp [Function.update, hk]

/-! ## Site dispatcher package, aliased register pair (`rs = rt`) -/

/-- `setIfEq`'s `Stmt` tree at site `pc` for the *aliased* case: `done` unconditionally bridges
    to `pc.1+1` (matching `setIfEqCodeBody`), every other phase is `setIfEqAliasedProg` lifted
    via `execVia`. -/
def setIfEqAliasedCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) :
    SetIfEqPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = SetIfEqPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getSetIfEq AllInstrState.setSetIfEq
        (setIfEqAliasedProg (regAt p pc rd (by rw [h]; simp [regsOf])) l)

/-- `setIfEqAliasedCodeBody`, cast once to the `SiteCode p pc` shape. -/
def setIfEqAliasedCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (setIfEqAliasedCodeBody p pc rd rs rt h)

lemma setIfEqAliasedCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) (l : SetIfEqPhase) :
    setIfEqAliasedCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l)
      = setIfEqAliasedCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (setIfEqAliasedCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `setIfEqAliasedCode` at site `pc` installs the lifted
    `setIfEqAliasedProg` tree at every non-`done` label. -/
lemma setIfEqAliasedCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqAliasedCode p pc rd rs rt h) M) :
    ∀ l : SetIfEqPhase, l ≠ SetIfEqPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getSetIfEq AllInstrState.setSetIfEq
        (setIfEqAliasedProg (regAt p pc rd (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    setIfEqAliasedCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `setIfEqAliasedCode` at site `pc` installs `bridgeTo p (pc.1+1)`
    at `setIfEq`'s own `done` label. -/
lemma setIfEqAliasedCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqAliasedCode p pc rd rs rt h) M) :
    M (execVia p pc h SetIfEqPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) SetIfEqPhase.done)
  rw [show execVia p pc h SetIfEqPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) SetIfEqPhase.done) from rfl, hone,
    setIfEqAliasedCode_apply]
  rfl

/-! ## Quantitative companion, aliased register pair -/

/-- The whole aliased-`setIfEq` site run on the global machine: `flipBindSetIfEqAliased_run` transported
    via `iterate_bind_step_liftStmt`, then the unconditional bridge to the next entry; only `rd` changes. -/
lemma setIfEqAliasedImpl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .setIfEq rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (setIfEqAliasedCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan)))
    (rd' : Fin (regBound p)) (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (dest : List Digit) (hRd : cfg.stk (Kg.reg rd') = dest) :
    ∃ Sgf, (flipBindG p M)^[dest.length + 1 + 1 + 1 + 1] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') [(⟨1, by norm_num⟩ : Digit)] := by
  have hag := setIfEqAliasedCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd'] at hag
  have hAliasedRun := flipBindSetIfEqAliased_run rd' dest cfg.stk hRd
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getSetIfEq AllInstrState.setSetIfEq (setIfEqAliasedProg rd') M
      Function.injective_id AllInstrState.getSetIfEq_setSetIfEq
      AllInstrState.setSetIfEq_setSetIfEq AllInstrState.setSetIfEq_getSetIfEq
      _ (SetIfEqPhase.compare CompareCorePhase.scan) (⟨none, none, .eq⟩ : CompareState) cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      SetIfEqPhase.done (⟨none, none, .eq⟩ : CompareState)
      (Function.update cfg.stk (Kg.reg rd') [(⟨1, by norm_num⟩ : Digit)])
      rfl hag hAliasedRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h SetIfEqPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h SetIfEqPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h SetIfEqPhase.done)) sf Sgf) from rfl,
      setIfEqAliasedCode_agrees_done p pc rd rs rt h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h (SetIfEqPhase.compare CompareCorePhase.scan)),
      AllInstrState.canonical, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨Sgf, ?_, funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of an aliased-`setIfEq` run encode the stepped registers on every register
    stack (only `rd` is rewritten) and agree with the initial stacks everywhere else. -/
lemma setIfEqAliasedImpl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (hnew : (step r).regs = bankWrite r.regs rd 1) (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') [(⟨1, by norm_num⟩ : Digit)]) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [hnew]
    by_cases hi : i = rd'
    · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
      rfl
    · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
      rw [bankWrite_diff _ _ _ _ hid,
        Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
      exact hregs i
  · exact Function.update_of_ne (hk rd') _ _

/-- Step-count bound: the aliased run costs `dest.length + 4` steps, at most `8` times the squared
    potential since `rd`'s length is bounded by `regSize`. -/
lemma setIfEqAliasedImpl_growing_bounded_time (p : List Instruction)
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

/-- `setIfEqAliasedImpl`'s growth companion: `mem` is untouched, and `rd` always ends holding a
    single `1` digit (`r.regs rs = r.regs rt` holds by `hrsrt : rs = rt`), so `regSize` grows by at
    most `1 ≤ instructionCost + 1`. -/
lemma setIfEqAliasedImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs = rt) (h : p.get pc = .setIfEq rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfEqAliasedCode p pc rd rs rt h) 8 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hcurEq := setIfEqMainImpl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := setIfEqMainImpl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hRd : cfg.stk (Kg.reg rd') = natToDigits (r.regs rd) := by rw [hregs rd', hrdval]
  have hnew : (step r).regs = bankWrite r.regs rd 1 := by simp [step, hcurEq, hrsrt]
  obtain ⟨Sgf, hrun, hSgf⟩ := setIfEqAliasedImpl_growing_bounded_run p pc rd rs rt h M hAgrees cfg
    hvar hcl rd' hrd' _ hRd
  obtain ⟨hreg, hother⟩ := setIfEqAliasedImpl_growing_bounded_stk cfg.stk r rd rd' hrdval hregs hnew
    Sgf hSgf
  exact ⟨_, _, hrun,
    setIfEqMainImpl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    setIfEqAliasedImpl_growing_bounded_time p cfg r rd rd' hrdval _ (by omega),
    setIfEqMainImpl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩


/-- The realized aliased-`setIfEq` site: its `sim` is `setIfEqAliasedImpl_growingBoundedSiteStepSim`
    forgetting the growth and step-count conjuncts. -/
def setIfEqAliasedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (hrsrt : rs = rt) (h : p.get pc = .setIfEq rd rs rt) : InstrImpl p pc where
  code := setIfEqAliasedCode p pc rd rs rt h
  sim := siteStepSim_of_boundedSiteStepSim p pc _ 8
    (boundedSiteStepSim_of_growingBoundedSiteStepSim p pc _ 8 1
      (setIfEqAliasedImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h))

/-- The realized `setIfEq` site: `setIfEqAliasedImpl` when `rs = rt` (decidable on the raw `ℕ`
    operands), `setIfEqMainImpl` otherwise — the meta-level split the lockstep-pop compare core
    requires (module docstring). -/
def setIfEqImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) : InstrImpl p pc :=
  if hrsrt : rs = rt then setIfEqAliasedImpl p pc rd rs rt hrsrt h
  else setIfEqMainImpl p pc rd rs rt hrsrt h

/-- `setIfEqImpl`'s growth companion: dispatches to `setIfEqAliasedImpl_growingBoundedSiteStepSim` or
    `setIfEqMainImpl_growingBoundedSiteStepSim` (both `G = 1` already), mirroring `setIfEqImpl`'s own
    `rs = rt` case split. -/
lemma setIfEqImpl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) :
    GrowingBoundedSiteStepSim p pc (setIfEqImpl p pc rd rs rt h).code 64 1 := by
  unfold setIfEqImpl
  by_cases hrsrt : rs = rt
  · simp only [dite_eq_left hrsrt]
    intro M hAgrees cfg r hRep hpcEq hcur
    obtain ⟨n, cfg', hrun, hRepr, hio, hbound, hgrowth⟩ :=
      setIfEqAliasedImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h M hAgrees cfg r hRep hpcEq hcur
    exact ⟨n, cfg', hrun, hRepr, hio, by omega, hgrowth⟩
  · simp only [dite_eq_right hrsrt]
    exact setIfEqMainImpl_growingBoundedSiteStepSim p pc rd rs rt hrsrt h

/-- `setIfEq`'s `GrowingTimedInstrImpl` package. -/
def setIfEqGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .setIfEq rd rs rt) : GrowingTimedInstrImpl p pc where
  code := (setIfEqImpl p pc rd rs rt h).code
  C := 64
  G := 1
  growingSim := setIfEqImpl_growingBoundedSiteStepSim p pc rd rs rt h

end NPComplete.RAMToTM.Generic

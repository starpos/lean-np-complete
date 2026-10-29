module

public import NPComplete.RAMToTM.Generic.Machine.GenericCompare
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `branchIfLt` realized against an arbitrary site's register pair

`branchIfLt rs rt target`'s whole effect is the shared compare core (`GenericCompare.lean`)
followed by a conditional jump — no register write, unlike `setIfLt`/`setIfEq`. `BranchIfLtPhase`
(`GenericProgramMachine.lean`) embeds `CompareCorePhase` via `compare`, with `done` the only extra
phase: `.compare .done` transitions straight to `.done` (no `clearDest`/`writeResult`), and `done`
itself is `halt` locally (`StmtTransport`'s requirement) — the *site*-level code overrides it with
a `branch` on the compare core's final `acc` field, picking `bridgeTo p target` or
`bridgeTo p (pc.1+1)`, mirroring `GenericBranch.lean`'s `branchIfNZ` but resolved only after the
(possibly multi-step) compare finishes rather than in one atomic tree.

`rs = rt`: handled entirely at site-construction level (`branchIfLtCode`) via a `by_cases` on the
raw `ℕ` operands — the aliased branch never touches a register (comparison is trivially `.eq`, so
the aliased-site tree is a single `load`+`goto` selecting `bridgeTo p (pc.1+1)`, since `.eq` never
takes `.lt`'s branch).
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits scanCompare scanCompare_eq_compareDigits
  compareDigits compareDigits_natToDigits)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rs rt : Fin (regBound p))

/-- `branchIfLt`'s local `Stmt` tree, self-contained against `BranchIfLtPhase`/`CompareState`
    (mirroring every other instruction's own standalone local program): the shared compare core
    is embedded via `liftStmt` at every non-`done` `compare` phase, `.compare .done` bridges
    straight to `.done` (no further register work needed), and `.done` is `halt`
    (`StmtTransport`'s fixed-exit requirement, overridden at the site level). -/
def branchIfLtProg : BranchIfLtPhase → Turing.TM2.Stmt (Γg p) BranchIfLtPhase CompareState
  | .compare ph =>
      if ph = CompareCorePhase.done then goto (fun _ => .done)
      else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) BranchIfLtPhase.compare
        id (fun _ v => v) (compareCoreProg rs rt ph)
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindBranchIfLt :
    Option (Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (branchIfLtProg rs rt))

/-- Any dispatcher agreeing with `branchIfLtProg` at every non-`done` `compare` phase installs
    the lifted compare core there — trivially true by `branchIfLtProg`'s own definition, stated
    as a hypothesis in the shape `StmtTransport.iterate_bind_step_liftStmt` expects. -/
lemma branchIfLtProg_agrees :
    ∀ l : CompareCorePhase, l ≠ CompareCorePhase.done →
      branchIfLtProg rs rt (BranchIfLtPhase.compare l)
        = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) BranchIfLtPhase.compare
            id (fun _ v => v) (compareCoreProg rs rt l) := by
  intro l hl
  simp [branchIfLtProg, hl]

lemma flipBindBranchIfLt_compare_done_step (v0 : CompareState) (Sg : ∀ k, List (Γg p k)) :
    flipBindBranchIfLt rs rt
        (some (⟨some (BranchIfLtPhase.compare CompareCorePhase.done), v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState))
      = some ⟨some BranchIfLtPhase.done, v0, Sg⟩ := by
  show (Turing.TM2.step (branchIfLtProg rs rt))
      (⟨some (BranchIfLtPhase.compare CompareCorePhase.done), v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState) = _
  simp [branchIfLtProg]

/-- The whole `branchIfLtProg` run, with a bound on the witness step count, combining
    `compare_core_run_bounded`'s bound with the trivial one-step `.compare .done → .done` bridge (no
    `clearDest`/`writeResult` tail, unlike `setIfLt`/`setIfEq`). -/
lemma flipBindBranchIfLt_run_bounded (hne : rs ≠ rt) (xs ys : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = xs) (hRt : Sg (Kg.reg rt) = ys)
    (hL : Sg (Kg.scratch .lhsOperand) = []) (hR : Sg (Kg.scratch .rhsOperand) = []) :
    ∃ n, (flipBindBranchIfLt rs rt)^[n]
        (some (⟨some (BranchIfLtPhase.compare CompareCorePhase.scan),
          (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState))
      = some ⟨some BranchIfLtPhase.done,
          (⟨none, none, scanCompare .eq xs ys⟩ : CompareState),
          Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys⟩ ∧
        n ≤ 2 * (xs.length + ys.length) + 6 := by
  obtain ⟨n1, hn1, hn1bound⟩ := compare_core_run_bounded rs rt hne xs ys Sg
    (⟨none, none, .eq⟩ : CompareState) hRs hRt hL hR
  have hstkTriv : ∀ k, Sg (id k) = List.map (⇑(Equiv.refl (Γg p k))) (Sg k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) BranchIfLtPhase.compare
      id (fun _ v => v) (compareCoreProg rs rt) (branchIfLtProg rs rt)
      Function.injective_id (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      n1 CompareCorePhase.scan (⟨none, none, .eq⟩ : CompareState) Sg
      (⟨none, none, .eq⟩ : CompareState) Sg rfl hstkTriv
      CompareCorePhase.done (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩
        : CompareState)
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) rfl
      (branchIfLtProg_agrees rs rt) hn1
  have hsfEq : sf = (⟨none, none, scanCompare .eq xs ys⟩ : CompareState) := hsetf
  have hSgfEq : Sgf = Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys := by
    funext k
    exact stack_eq_of_map_equiv_refl Sgf
      (Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys) hstkf k
  refine ⟨n1 + 1, ?_, by omega⟩
  rw [Function.iterate_succ_apply']
  rw [show (flipBindBranchIfLt rs rt)^[n1]
      (some (⟨some (BranchIfLtPhase.compare CompareCorePhase.scan),
        (⟨none, none, .eq⟩ : CompareState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) BranchIfLtPhase CompareState))
    = some ⟨some (BranchIfLtPhase.compare CompareCorePhase.done), sf, Sgf⟩ from hrun,
    hsfEq, hSgfEq]
  exact flipBindBranchIfLt_compare_done_step rs rt _ _

/-! ## Site dispatcher package, non-aliased register pair -/

/-- `branchIfLt`'s `Stmt` tree at site `pc`, before embedding into `Λg p`, for the *non-aliased*
    case: `.compare .done` is overridden with a conditional bridge — `bridgeTo p target` iff the
    compare core landed on `.lt`, `bridgeTo p (pc.1+1)` otherwise — every other phase is
    `branchIfLtProg` lifted via `execVia` (mirroring `moveCodeBody`'s shape). -/
def branchIfLtCodeBody (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) :
    BranchIfLtPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = BranchIfLtPhase.done then
      Turing.TM2.Stmt.branch (fun s => decide ((AllInstrState.getBranchIfLt s).acc = .lt))
        (bridgeTo p target) (bridgeTo p (pc.1 + 1))
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getBranchIfLt AllInstrState.setBranchIfLt
        (branchIfLtProg (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `branchIfLtCodeBody`, cast once from `BranchIfLtPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def branchIfLtCode (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (branchIfLtCodeBody p pc rs rt target h)

/-- `branchIfLtCode` undoes its own cast when applied to a correspondingly-cast `BranchIfLtPhase`
    value. -/
lemma branchIfLtCode_apply (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) (l : BranchIfLtPhase) :
    branchIfLtCode p pc rs rt target h (cast (congrArg PhaseOf h.symm) l)
      = branchIfLtCodeBody p pc rs rt target h l :=
  cast_apply_phaseOf p pc h (branchIfLtCodeBody p pc rs rt target h) l

/-- Any dispatcher agreeing with `branchIfLtCode` at site `pc` installs the lifted
    `branchIfLtProg` tree at every non-`done` label. -/
lemma branchIfLtCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (branchIfLtCode p pc rs rt target h) M) :
    ∀ l : BranchIfLtPhase, l ≠ BranchIfLtPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getBranchIfLt AllInstrState.setBranchIfLt
        (branchIfLtProg (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    branchIfLtCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `branchIfLtCode` at site `pc` installs the conditional bridge at
    `branchIfLt`'s own `done` label. -/
lemma branchIfLtCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (branchIfLtCode p pc rs rt target h) M) :
    M (execVia p pc h BranchIfLtPhase.done)
      = Turing.TM2.Stmt.branch (fun s => decide ((AllInstrState.getBranchIfLt s).acc = .lt))
          (bridgeTo p target) (bridgeTo p (pc.1 + 1)) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) BranchIfLtPhase.done)
  rw [show execVia p pc h BranchIfLtPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) BranchIfLtPhase.done) from rfl, hone,
    branchIfLtCode_apply]
  rfl

/-! ## Site dispatcher package, aliased register pair (`rs = rt`) -/

/-- `branchIfLt`'s `Stmt` tree at site `pc` for the *aliased* case (`rs = rt`): the comparison is
    trivially `.eq` (`r.regs rs = r.regs rt`), which never satisfies `branchIfLt`'s `.lt` jump
    condition, so the whole effect collapses to an unconditional `bridgeTo p (pc.1+1)` — no
    register access, no compare core instantiated (module docstring: avoids the lockstep-pop
    alias hazard entirely). Only the entry phase (`compare .scan`, `startPhaseOpt`'s value) is
    ever actually visited; every other phase gets the same placeholder, matching `haltImpl`-style
    "never reached, but must still typecheck" totality. -/
def branchIfLtAliasedCodeBody (p : List Instruction) (pc : Fin p.length) :
    BranchIfLtPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun _ => bridgeTo p (pc.1 + 1)

/-- `branchIfLtAliasedCodeBody`, cast once to the `SiteCode p pc` shape. -/
def branchIfLtAliasedCode (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (branchIfLtAliasedCodeBody p pc)

lemma branchIfLtAliasedCode_apply (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) (l : BranchIfLtPhase) :
    branchIfLtAliasedCode p pc rs rt target h (cast (congrArg PhaseOf h.symm) l)
      = branchIfLtAliasedCodeBody p pc l :=
  cast_apply_phaseOf p pc h (branchIfLtAliasedCodeBody p pc) l

/-! ## Quantitative companion, aliased register pair -/

/-- `branchIfLtAliasedImpl`'s growth companion: `regs`/`mem` untouched, and the destination
    config shares `cfg.stk` verbatim, so the potential is unchanged (`G = 0`). -/
lemma branchIfLtAliasedImpl_growing_bounded (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (hrsrt : rs = rt) (h : p.get pc = .branchIfLt rs rt target) :
    GrowingBoundedSiteStepSim p pc (branchIfLtAliasedCode p pc rs rt target h) 1 0 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  obtain ⟨hprog, hregs, hmem, _hvar, hscratch, hctrl⟩ := hRep
  have hcurEq : r.current = Instruction.branchIfLt rs rt target := by
    rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
  have hstart : startPhaseOpt (Instruction.branchIfLt rs rt target)
      = some (BranchIfLtPhase.compare CompareCorePhase.scan) := rfl
  have hentry : entryAt p pc.1
      = execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan) :=
    entryAt_eq_execVia p pc h _ hstart
  have hcl : cfg.l = some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)) := by
    rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]
  have hMdone : M (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan))
      = bridgeTo p (pc.1 + 1) := by
    have hone := hAgrees
      (cast (congrArg PhaseOf h.symm) (BranchIfLtPhase.compare CompareCorePhase.scan))
    rw [show execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)
        = Λg.exec pc (cast (congrArg PhaseOf h.symm)
          (BranchIfLtPhase.compare CompareCorePhase.scan)) from rfl,
      hone, branchIfLtAliasedCode_apply]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)),
      cfg.var, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl]
  have hstep : Turing.TM2.step M cfg
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
    conv_lhs => rw [hcfgEq]
    show some (Turing.TM2.stepAux
        (M (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan))) cfg.var cfg.stk) = _
    rw [hMdone, bridgeTo]
    rfl
  have hN : (flipBindG p M)^[1] (some cfg)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
    show flipBindG p M (some cfg) = _
    rw [flipBindG]; show Turing.TM2.step M cfg = _; exact hstep
  refine ⟨_, _, hN, ?_, rfl, ?_, ?_⟩
  · have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq]
    have hMemUnchanged : (step r).mem = r.mem := by simp [step, hcurEq]
    have hpcElse : (step r).pc = pc.1 + 1 := by
      simp only [step, hcurEq, hpcEq]
      rw [hrsrt]
      simp
    refine ⟨by simp [step, hcurEq, hprog], ?_, ?_, rfl, ?_, ?_⟩
    · intro i; rw [hRegsUnchanged]; exact hregs i
    · obtain ⟨log, hmemstk, hmemlookup⟩ := hmem
      exact ⟨log, hmemstk, by rw [hMemUnchanged]; exact hmemlookup⟩
    · intro s; exact hscratch s
    · rw [ControlRep, hpcElse]
  · nlinarith [Nat.zero_le (regSize p r), Nat.zero_le (cfg.stk Kg.mem).length,
      Nat.zero_le (instructionCost r.regs r.mem r.current)]
  · have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq]
    have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hRegsUnchanged]
    have hstk2 :
        ({ l := some (entryAt p (pc.1 + 1)), var := AllInstrState.canonical, stk := cfg.stk } :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState).stk Kg.mem = cfg.stk Kg.mem := rfl
    rw [hstk2, hrs]; omega

/-- The realized aliased-`branchIfLt` site: a single unconditional bridge (`n = 1`), leaving
    every stack untouched — `r.regs rs = r.regs rt` (same register) makes the RAM step's own
    `.lt` jump condition false, matching `bridgeTo p (pc.1+1)`'s target unconditionally. -/
def branchIfLtAliasedImpl (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (hrsrt : rs = rt) (h : p.get pc = .branchIfLt rs rt target) : InstrImpl p pc where
  code := branchIfLtAliasedCode p pc rs rt target h
  sim := by
    intro M hAgrees cfg r hRep hpcEq _hcur
    obtain ⟨hprog, hregs, hmem, _hvar, hscratch, hctrl⟩ := hRep
    have hcurEq : r.current = Instruction.branchIfLt rs rt target := by
      rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
    have hstart : startPhaseOpt (Instruction.branchIfLt rs rt target)
        = some (BranchIfLtPhase.compare CompareCorePhase.scan) := rfl
    have hentry : entryAt p pc.1
        = execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan) :=
      entryAt_eq_execVia p pc h _ hstart
    have hcl : cfg.l = some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)) := by
      rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]
    have hMdone : M (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan))
        = bridgeTo p (pc.1 + 1) := by
      have hone := hAgrees
        (cast (congrArg PhaseOf h.symm) (BranchIfLtPhase.compare CompareCorePhase.scan))
      rw [show execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)
          = Λg.exec pc (cast (congrArg PhaseOf h.symm)
            (BranchIfLtPhase.compare CompareCorePhase.scan)) from rfl,
        hone, branchIfLtAliasedCode_apply]
      rfl
    have hcfgEq : cfg = (⟨some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)),
        cfg.var, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
      have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
      rw [heta, hcl]
    have hstep : Turing.TM2.step M cfg
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
      conv_lhs => rw [hcfgEq]
      show some (Turing.TM2.stepAux
          (M (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan))) cfg.var cfg.stk) = _
      rw [hMdone, bridgeTo]
      rfl
    have hN : (flipBindG p M)^[1] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
      show flipBindG p M (some cfg) = _
      rw [flipBindG]; show Turing.TM2.step M cfg = _; exact hstep
    refine ⟨_, _, hN, ?_⟩
    have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq]
    have hMemUnchanged : (step r).mem = r.mem := by simp [step, hcurEq]
    have hpcElse : (step r).pc = pc.1 + 1 := by
      simp only [step, hcurEq, hpcEq]
      rw [hrsrt]
      simp
    refine ⟨by simp [step, hcurEq, hprog], ?_, ?_, rfl, ?_, ?_⟩
    · intro i; rw [hRegsUnchanged]; exact hregs i
    · obtain ⟨log, hmemstk, hmemlookup⟩ := hmem
      exact ⟨log, hmemstk, by rw [hMemUnchanged]; exact hmemlookup⟩
    · intro s; exact hscratch s
    · rw [ControlRep, hpcElse]

/-! ## Quantitative companion, non-aliased register pair -/

/-- The current instruction is `branchIfLt` at the site's program counter. -/
lemma branchIfLtMainImpl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (h : p.get pc = .branchIfLt rs rt target) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.branchIfLt rs rt target := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's compare entry. -/
lemma branchIfLtMainImpl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (h : p.get pc = .branchIfLt rs rt target)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)) := by
  have hstart : startPhaseOpt (Instruction.branchIfLt rs rt target)
      = some (BranchIfLtPhase.compare CompareCorePhase.scan) := rfl
  have hentry : entryAt p pc.1
      = execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan) :=
    entryAt_eq_execVia p pc h _ hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The conditional bridge at `done` jumps to `target` iff the compare accumulator is `.lt`, and
    otherwise falls through to the next entry, leaving the stacks untouched. -/
lemma branchIfLtMainImpl_growing_bounded_done_step (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (h : p.get pc = .branchIfLt rs rt target)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (branchIfLtCode p pc rs rt target h) M)
    (sf : AllInstrState) (Sgf : ∀ k, List (Γg p k)) {xs ys : List Digit}
    (hsf : (AllInstrState.getBranchIfLt sf).acc = scanCompare .eq xs ys) :
    Turing.TM2.step M
      (⟨some (execVia p pc h BranchIfLtPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p
          (if scanCompare Ordering.eq xs ys = Ordering.lt then target else pc.1 + 1)),
        AllInstrState.canonical, Sgf⟩ := by
  rw [show Turing.TM2.step M
      (⟨some (execVia p pc h BranchIfLtPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some (Turing.TM2.stepAux (M (execVia p pc h BranchIfLtPhase.done)) sf Sgf) from rfl,
    branchIfLtCode_agrees_done p pc rs rt target h M hAgrees]
  by_cases hlt : scanCompare Ordering.eq xs ys = Ordering.lt
  · have hdec : decide ((AllInstrState.getBranchIfLt sf).acc = Ordering.lt) = true := by
      rw [hsf]; simpa using hlt
    simp [Turing.TM2.stepAux, hdec, bridgeTo, hlt]
  · have hdec : decide ((AllInstrState.getBranchIfLt sf).acc = Ordering.lt) = false := by
      rw [hsf]; simpa using hlt
    simp [Turing.TM2.stepAux, hdec, bridgeTo, hlt]

/-- The whole `branchIfLt` site run on the global machine: the compare run transported via
    `iterate_bind_step_liftStmt`, then the conditional bridge to `target` or the next entry according to
    whether the compare core landed on `.lt`, with the final stacks and a step count bound. -/
lemma branchIfLtMainImpl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (h : p.get pc = .branchIfLt rs rt target)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (branchIfLtCode p pc rs rt target h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)))
    (rs' rt' : Fin (regBound p))
    (hrs' : rs' = regAt p pc rs (by rw [h]; simp [regsOf]))
    (hrt' : rt' = regAt p pc rt (by rw [h]; simp [regsOf]))
    (hne' : rs' ≠ rt') (xs ys : List Digit)
    (hRs : cfg.stk (Kg.reg rs') = xs) (hRt : cfg.stk (Kg.reg rt') = ys)
    (hL : cfg.stk (Kg.scratch ScratchKind.lhsOperand) = [])
    (hR : cfg.stk (Kg.scratch ScratchKind.rhsOperand) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p
            (if scanCompare Ordering.eq xs ys = Ordering.lt then target else pc.1 + 1)),
          AllInstrState.canonical, Sgf⟩ ∧
      n ≤ 2 * (xs.length + ys.length) + 7 ∧
      Sgf = Function.update (Function.update cfg.stk (Kg.reg rs') xs) (Kg.reg rt') ys := by
  have hag := branchIfLtCode_agrees_ne_done p pc rs rt target h M hAgrees
  rw [← hrs', ← hrt'] at hag
  obtain ⟨n1, hn1, hn1bound⟩ := flipBindBranchIfLt_run_bounded rs' rt' hne' xs ys cfg.stk hRs hRt hL hR
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getBranchIfLt AllInstrState.setBranchIfLt (branchIfLtProg rs' rt') M
      Function.injective_id AllInstrState.getBranchIfLt_setBranchIfLt
      AllInstrState.setBranchIfLt_setBranchIfLt AllInstrState.setBranchIfLt_getBranchIfLt
      _ (BranchIfLtPhase.compare CompareCorePhase.scan) (⟨none, none, .eq⟩ : CompareState) cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      BranchIfLtPhase.done
      (⟨none, none, scanCompare (⟨none, none, .eq⟩ : CompareState).acc xs ys⟩ : CompareState)
      (Function.update (Function.update cfg.stk (Kg.reg rs') xs) (Kg.reg rt') ys)
      rfl hag hn1
  have hMdone := branchIfLtCode_agrees_done p pc rs rt target h M hAgrees
  have hsfCanon : (AllInstrState.getBranchIfLt sf).acc = scanCompare .eq xs ys := by
    rw [hsetf, AllInstrState.getBranchIfLt_setBranchIfLt]
  have hstepM := branchIfLtMainImpl_growing_bounded_done_step p pc rs rt target h M hAgrees sf Sgf
    (xs := xs) (ys := ys) hsfCanon
  have hcfgEq : cfg = (⟨some (execVia p pc h (BranchIfLtPhase.compare CompareCorePhase.scan)),
      AllInstrState.canonical, cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨n1 + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hstepM

/-- A `branchIfLt` step leaves the registers untouched and jumps on `.lt`. -/
lemma branchIfLtMainImpl_growing_bounded_step (rs rt target : ℕ) (r : RAM) (pc : ℕ)
    (hpcEq : r.pc = pc) (hcurEq : r.current = Instruction.branchIfLt rs rt target) :
    (step r).regs = r.regs ∧ (step r).mem = r.mem ∧
    (step r).pc = (if scanCompare Ordering.eq (natToDigits (r.regs rs)) (natToDigits (r.regs rt))
        = Ordering.lt then target else pc + 1) := by
  have hcompareEq : scanCompare .eq (natToDigits (r.regs rs)) (natToDigits (r.regs rt))
      = compare (r.regs rs) (r.regs rt) := by
    rw [scanCompare_eq_compareDigits]
    have hthEq : ∀ x : Ordering, x.then Ordering.eq = x := fun x => by cases x <;> rfl
    rw [hthEq, compareDigits_natToDigits]
  refine ⟨by simp [step, hcurEq], by simp [step, hcurEq], ?_⟩
  rw [hcompareEq]
  by_cases hlt : r.regs rs < r.regs rt
  · rw [ite_eq_left (compare_lt_iff_lt.mpr hlt)]; simp [step, hcurEq, hlt]
  · rw [ite_eq_right (by rw [compare_lt_iff_lt]; exact hlt)]; simp [step, hcurEq, hlt, hpcEq]

/-- The final stacks of a `branchIfLt` run are the initial stacks: both compared registers are
    restored to the contents they started with. -/
lemma branchIfLtMainImpl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (rs' rt' : Fin (regBound p)) (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update (Function.update stk (Kg.reg rs') (stk (Kg.reg rs')))
      (Kg.reg rt') (stk (Kg.reg rt'))) : Sgf = stk := by
  rw [hSgf, Function.update_eq_self, Function.update_eq_self]

/-- The configuration at `entryAt p (step r).pc` with the original stacks represents the stepped
    RAM, since a `branchIfLt` step changes only the program counter. -/
lemma branchIfLtMainImpl_growing_bounded_represents (p : List Instruction)
    (rs rt target : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hcurEq : r.current = Instruction.branchIfLt rs rt target)
    (hregs : (step r).regs = r.regs) (hmem : (step r).mem = r.mem) :
    Represents p ⟨some (entryAt p (step r).pc), AllInstrState.canonical, cfg.stk⟩ (step r) := by
  obtain ⟨hprog, hr, ⟨log, hmemstk, hmemlookup⟩, -, hscratch, -⟩ := hRep
  refine ⟨by simp [step, hcurEq, hprog], fun i => ?_, ⟨log, hmemstk, fun a => ?_⟩, rfl,
    hscratch, rfl⟩
  · rw [hregs]; exact hr i
  · rw [hmem]; exact hmemlookup a

/-- Step-count bound: the run's cost is at most `64` times the squared potential, since each of
    the two operand lengths is bounded by `regSize`. -/
lemma branchIfLtMainImpl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rs rt : ℕ) (rs' rt' : Fin (regBound p))
    (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt) (n : ℕ)
    (hn : n ≤ 2 * ((natToDigits (r.regs rs)).length + (natToDigits (r.regs rt)).length) + 7) :
    n ≤ 64 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle1 := natToDigits_length_le_regSize p r rs'
  have hle2 := natToDigits_length_le_regSize p r rt'
  rw [hrsval] at hle1
  rw [hrtval] at hle2
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  have hlX : regSize p r + 1 ≤ X ^ 2 := le_trans (by omega : regSize p r + 1 ≤ X) hXsq
  omega

/-- Potential growth: registers and memory are untouched, so the potential is unchanged. -/
lemma branchIfLtMainImpl_growing_bounded_growth (p : List Instruction) (stk : ∀ k, List (Γg p k))
    (r : RAM) (hregs : (step r).regs = r.regs) :
    regSize p (step r) + (stk Kg.mem).length ≤
      regSize p r + (stk Kg.mem).length + 0 * (instructionCost r.regs r.mem r.current + 1) := by
  have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hregs]
  omega

/-- `branchIfLtMainImpl`'s growth companion: `regs`/`mem` untouched on both branches (the
    conditional bridge never writes any register or the memory stack), so the potential is
    unchanged (`G = 0`). -/
lemma branchIfLtMainImpl_growing_bounded (p : List Instruction) (pc : Fin p.length)
    (rs rt target : ℕ) (hrsrt : rs ≠ rt) (h : p.get pc = .branchIfLt rs rt target) :
    GrowingBoundedSiteStepSim p pc (branchIfLtCode p pc rs rt target h) 64 0 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := branchIfLtMainImpl_growing_bounded_current p pc rs rt target h r hprog hpcEq
  have hcl := branchIfLtMainImpl_growing_bounded_label p pc rs rt target h cfg r hpcEq
    hRep.2.2.2.2.2
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rt', hrt'⟩ : ∃ x, x = regAt p pc rt (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hrtval : rt'.1 = rt := by rw [hrt']; rfl
  have hne' : rs' ≠ rt' := fun heq => hrsrt (by rw [← hrsval, ← hrtval, heq])
  have hRs : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  have hRt : cfg.stk (Kg.reg rt') = natToDigits (r.regs rt) := by rw [hregs rt', hrtval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := branchIfLtMainImpl_growing_bounded_run p pc rs rt target h M
    hAgrees cfg hvar hcl rs' rt' hrs' hrt' hne' _ _ hRs hRt (hscratch .lhsOperand)
    (hscratch .rhsOperand)
  rw [← hRs, ← hRt] at hSgf
  have hstk := branchIfLtMainImpl_growing_bounded_stk cfg.stk rs' rt' Sgf hSgf
  obtain ⟨hregsEq, hmemEq, hpc⟩ :=
    branchIfLtMainImpl_growing_bounded_step rs rt target r pc.1 hpcEq hcurEq
  rw [← hpc, hstk] at hrun
  exact ⟨n, _, hrun,
    branchIfLtMainImpl_growing_bounded_represents p rs rt target cfg r hRep hcurEq hregsEq hmemEq,
    rfl, branchIfLtMainImpl_growing_bounded_time p cfg r rs rt rs' rt' hrsval hrtval n
      hn,
    branchIfLtMainImpl_growing_bounded_growth p cfg.stk r hregsEq⟩


/-- `branchIfLtMainImpl`'s quantitative companion: `branchIfLtMainImpl_growing_bounded` forgetting
    its growth and `io` conjuncts. -/
lemma branchIfLtMainImpl_bounded (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .branchIfLt rs rt target) :
    BoundedSiteStepSim p pc (branchIfLtCode p pc rs rt target h) 64 :=
  boundedSiteStepSim_of_growingBoundedSiteStepSim p pc _ 64 0
    (branchIfLtMainImpl_growing_bounded p pc rs rt target hrsrt h)

/-- The realized non-aliased-`branchIfLt` site: `branchIfLtMainImpl_bounded` forgetting its
    bound, via `siteStepSim_of_boundedSiteStepSim`. -/
def branchIfLtMainImpl (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (hrsrt : rs ≠ rt) (h : p.get pc = .branchIfLt rs rt target) : InstrImpl p pc where
  code := branchIfLtCode p pc rs rt target h
  sim := siteStepSim_of_boundedSiteStepSim p pc _ 64
    (branchIfLtMainImpl_bounded p pc rs rt target hrsrt h)

/-- The realized `branchIfLt` site: `branchIfLtAliasedImpl` when `rs = rt` (decidable on the raw
    `ℕ` operands), `branchIfLtMainImpl` otherwise — the meta-level split the lockstep-pop compare
    core requires (module docstring). -/
def branchIfLtImpl (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) : InstrImpl p pc :=
  if hrsrt : rs = rt then branchIfLtAliasedImpl p pc rs rt target hrsrt h
  else branchIfLtMainImpl p pc rs rt target hrsrt h

/-- `branchIfLtImpl`'s growth companion: dispatches to `branchIfLtAliasedImpl_growing_bounded` or
    `branchIfLtMainImpl_growing_bounded` (both `G = 0` already), mirroring `branchIfLtImpl`'s own
    `rs = rt` case split. -/
lemma branchIfLtImpl_growing_bounded (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) :
    GrowingBoundedSiteStepSim p pc (branchIfLtImpl p pc rs rt target h).code 64 0 := by
  unfold branchIfLtImpl
  by_cases hrsrt : rs = rt
  · simp only [dite_eq_left hrsrt]
    intro M hAgrees cfg r hRep hpcEq hcur
    obtain ⟨n, cfg', hrun, hRepr, hio, hbound, hgrowth⟩ :=
      branchIfLtAliasedImpl_growing_bounded p pc rs rt target hrsrt h M hAgrees cfg r hRep hpcEq
        hcur
    exact ⟨n, cfg', hrun, hRepr, hio, by omega, hgrowth⟩
  · simp only [dite_eq_right hrsrt]
    exact branchIfLtMainImpl_growing_bounded p pc rs rt target hrsrt h

/-- `branchIfLt`'s `GrowingTimedInstrImpl` package. -/
def branchIfLtGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rs rt target : ℕ)
    (h : p.get pc = .branchIfLt rs rt target) : GrowingTimedInstrImpl p pc where
  code := (branchIfLtImpl p pc rs rt target h).code
  C := 64
  G := 0
  growingSim := branchIfLtImpl_growing_bounded p pc rs rt target h

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine

/-!
# `jump`/`branchIfNZ`/`halt` realized against an arbitrary site

Unlike `store`/`load`/`add` (`GenericStore.lean`/`GenericLoad.lean`/`GenericAdd.lean`), which loop
over variable-length digit lists and thus need their own local phase type embedded into the shared
`AllInstrState` via `StmtTransport.liftStmt`'s lens machinery, `jump` and `branchIfNZ`'s whole
effect fits in one `Turing.TM2.Stmt` tree with no internal `goto` (`Turing.TM2.stepAux` evaluates
an entire tree — including `peek`/`branch` — in one `Cfg → Cfg` step; only `goto`/`halt` leaves
consume a label). So both are written directly against the shared `Λg p`/`AllInstrState`
(`GenericProgramMachine.lean`'s `CtrlPhase`), reusing `bridgeTo` for their target(s) with no lens,
no orthogonality lemmas, and (`jump_impl_growing_bounded`) no register access at all.

`branchIfNZ`'s `Stmt` tree `peek`s (non-destructively) the top of its operand register's digit
stack into `AllInstrState.decision`, then `branch`es on that bit — `natToDigits_ne_nil_iff`
(`Binary.lean`) ties "digit stack nonempty" to `regs rs ≠ 0` via `Nat.digits`'s empty-list-for-zero
convention, so a single `peek` (not a full drain-and-restore loop) suffices.

`halt` needs no realization at all: `PhaseOf .halt`/`startPhaseOpt .halt` are unchanged (`Empty`/
`none`), so `entryAt`'s existing `startPhaseOpt = none` fallback already routes an explicit in-range
`halt` to `cleanup`, exactly like an out-of-range PC. `ProgramSupported`'s `InstructionSupported`
disjunct only has to establish the position exists; `SiteStepSim` itself is never satisfiable there
(`r.pc = pc.1` together with `Represents`'s `r.program = p` forces `r.current = Instruction.halt`,
contradicting `SiteStepSim`'s own `r.current ≠ Instruction.halt` hypothesis), so `haltImpl`'s `sim`
is a one-line contradiction.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (natToDigits_ne_nil_iff)

/-! ## `halt` -/

/-- `halt` needs no realized phase: a site naming an explicit `halt` can never actually be visited
    by `SiteStepSim`, since `r.pc = pc.1` together with `Represents`'s `r.program = p` component
    forces `r.current = Instruction.halt`, contradicting `SiteStepSim`'s own
    `r.current ≠ Instruction.halt` hypothesis — so `code` only ever needs to eliminate the
    uninhabited `PhaseOf Instruction.halt` (`= Empty`). -/
def haltImpl (p : List Instruction) (pc : Fin p.length) (h : p.get pc = Instruction.halt) :
    InstrImpl p pc where
  code := fun ph => (cast (congrArg PhaseOf h) ph : Empty).elim
  sim := by
    intro M _hAgrees cfg r hRep hpcEq hcur
    have hcurEq : r.current = Instruction.halt := by
      rw [RAM.current, hRep.1, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
    exact absurd hcurEq hcur

/-! ## `jump` -/

/-- `jump target`'s `Stmt` tree at site `pc`: `BitCostRAM.step`'s `.jump` case only ever changes
    `pc` (to `target`, unconditionally), so its whole effect is exactly one `bridgeTo p target` —
    no register access, no internal phase. -/
def jumpCodeBody (p : List Instruction) (target : ℕ) :
    CtrlPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun _ => bridgeTo p target

/-- `jumpCodeBody`, cast once from `CtrlPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires (matching `storeCode`'s
    whole-function-cast pattern, `GenericStore.lean`). -/
def jumpCode (p : List Instruction) (pc : Fin p.length) (target : ℕ)
    (h : p.get pc = .jump target) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (jumpCodeBody p target)

/-- `jumpCode` undoes its own cast when applied to a correspondingly-cast `CtrlPhase` value. -/
lemma jumpCode_apply (p : List Instruction) (pc : Fin p.length) (target : ℕ)
    (h : p.get pc = .jump target) (l : CtrlPhase) :
    jumpCode p pc target h (cast (congrArg PhaseOf h.symm) l) = jumpCodeBody p target l :=
  cast_apply_phaseOf p pc h (jumpCodeBody p target) l

/-! ## `branchIfNZ` -/

/-- `branchIfNZ rs target`'s `Stmt` tree at site `pc`: non-destructively `peek` the top of `rs`'s
    digit stack into the transient `AllInstrState.decision` bit (`natToDigits_ne_nil_iff` ties
    "digit stack nonempty" to `BitCostRAM.step`'s `regs rs ≠ 0` condition), then `branch` between
    `bridgeTo p target` (nonzero) and `bridgeTo p (pc.1 + 1)` (zero). -/
def branchIfNZCodeBody (p : List Instruction) (pc : Fin p.length) (rs target : ℕ)
    (h : p.get pc = .branchIfNZ rs target) :
    CtrlPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun _ =>
    Turing.TM2.Stmt.peek (Kg.reg (regAt p pc rs (by rw [h]; simp [regsOf])))
      (fun s ov => { s with decision := ov.isSome })
      (Turing.TM2.Stmt.branch (fun s => s.decision) (bridgeTo p target) (bridgeTo p (pc.1 + 1)))

/-- `branchIfNZCodeBody`, cast once from `CtrlPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def branchIfNZCode (p : List Instruction) (pc : Fin p.length) (rs target : ℕ)
    (h : p.get pc = .branchIfNZ rs target) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (branchIfNZCodeBody p pc rs target h)

/-- `branchIfNZCode` undoes its own cast when applied to a correspondingly-cast `CtrlPhase`
    value. -/
lemma branchIfNZCode_apply (p : List Instruction) (pc : Fin p.length) (rs target : ℕ)
    (h : p.get pc = .branchIfNZ rs target) (l : CtrlPhase) :
    branchIfNZCode p pc rs target h (cast (congrArg PhaseOf h.symm) l)
      = branchIfNZCodeBody p pc rs target h l :=
  cast_apply_phaseOf p pc h (branchIfNZCodeBody p pc rs target h) l

/-! ## Growth-aware companions (run_sim aggregation stage)

`halt`/`jump`/`branchIfNZ` never touch `regs` or `mem` at all — only `pc` moves — so their growth
bound is always `0`: the potential after the step is literally the same as before. -/

/-- `haltImpl`'s growth companion: same one-line contradiction as `haltImpl`'s own `sim`, no
    witness needed. -/
lemma haltImpl_growing_bounded (p : List Instruction) (pc : Fin p.length)
    (h : p.get pc = Instruction.halt) :
    GrowingBoundedSiteStepSim p pc (haltImpl p pc h).code 1 0 := by
  intro M _hAgrees cfg r hRep hpcEq hcur
  have hcurEq : r.current = Instruction.halt := by
    rw [RAM.current, hRep.1, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
  exact absurd hcurEq hcur

/-- `jumpCode`'s growth companion: `regs`/`mem` untouched, and the destination config shares
    `cfg.stk` verbatim (only the label changes), so the potential is unchanged (`G = 0`). -/
lemma jump_impl_growing_bounded (p : List Instruction) (pc : Fin p.length) (target : ℕ)
    (h : p.get pc = .jump target) :
    GrowingBoundedSiteStepSim p pc (jumpCode p pc target h) 1 0 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  obtain ⟨hprog, hregs, hmem, _hvar, hscratch, hctrl⟩ := hRep
  have hcurEq : r.current = Instruction.jump target := by
    rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
  have hstart : startPhaseOpt (Instruction.jump target) = some CtrlPhase.entry := rfl
  have hentry : entryAt p pc.1 = execVia p pc h CtrlPhase.entry :=
    entryAt_eq_execVia p pc h CtrlPhase.entry hstart
  have hcl : cfg.l = some (execVia p pc h CtrlPhase.entry) := by
    rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]
  have hMdone : M (execVia p pc h CtrlPhase.entry) = bridgeTo p target := by
    have hone := hAgrees (cast (congrArg PhaseOf h.symm) CtrlPhase.entry)
    rw [show execVia p pc h CtrlPhase.entry
        = Λg.exec pc (cast (congrArg PhaseOf h.symm) CtrlPhase.entry) from rfl, hone,
      jumpCode_apply]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h CtrlPhase.entry), cfg.var, cfg.stk⟩ :
      Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl]
  have hstep : Turing.TM2.step M cfg
      = some ⟨some (entryAt p target), AllInstrState.canonical, cfg.stk⟩ := by
    conv_lhs => rw [hcfgEq]
    show some (Turing.TM2.stepAux (M (execVia p pc h CtrlPhase.entry)) cfg.var cfg.stk) = _
    rw [hMdone, bridgeTo]
    rfl
  have hN : (flipBindG p M)^[1] (some cfg)
      = some ⟨some (entryAt p target), AllInstrState.canonical, cfg.stk⟩ := by
    show flipBindG p M (some cfg) = _
    rw [flipBindG]; show Turing.TM2.step M cfg = _; exact hstep
  have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq]
  have hMemUnchanged : (step r).mem = r.mem := by simp [step, hcurEq]
  have hpcJump : (step r).pc = target := by simp [step, hcurEq]
  refine ⟨_, _, hN, ?_, rfl, ?_, ?_⟩
  · refine ⟨by simp [step, hcurEq, hprog], ?_, ?_, rfl, ?_, ?_⟩
    · intro i; rw [hRegsUnchanged]; exact hregs i
    · obtain ⟨log, hmemstk, hmemlookup⟩ := hmem
      exact ⟨log, hmemstk, by rw [hMemUnchanged]; exact hmemlookup⟩
    · intro s; exact hscratch s
    · rw [ControlRep, hpcJump]
  · rw [hcurEq]; simp only [instructionCost, one_mul]
    nlinarith [Nat.zero_le (regSize p r), Nat.zero_le (cfg.stk Kg.mem).length]
  · have hstkEq :
        ({ l := some (entryAt p target), var := AllInstrState.canonical, stk := cfg.stk } :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState).stk Kg.mem = cfg.stk Kg.mem := rfl
    have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hRegsUnchanged]
    rw [hstkEq, hrs]; omega

/-- `branchIfNZCode`'s growth companion: `regs`/`mem` untouched on both branches, and both
    destination configs share `cfg.stk` verbatim, so the potential is unchanged (`G = 0`). -/
lemma branchIfNZ_impl_growing_bounded (p : List Instruction) (pc : Fin p.length) (rs target : ℕ)
    (h : p.get pc = .branchIfNZ rs target) :
    GrowingBoundedSiteStepSim p pc (branchIfNZCode p pc rs target h) 1 0 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  obtain ⟨hprog, hregs, hmem, _hvar, hscratch, hctrl⟩ := hRep
  have hcurEq : r.current = Instruction.branchIfNZ rs target := by
    rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h
  have hstart : startPhaseOpt (Instruction.branchIfNZ rs target) = some CtrlPhase.entry := rfl
  have hentry : entryAt p pc.1 = execVia p pc h CtrlPhase.entry :=
    entryAt_eq_execVia p pc h CtrlPhase.entry hstart
  have hcl : cfg.l = some (execVia p pc h CtrlPhase.entry) := by
    rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]
  set rs' := regAt p pc rs (by rw [h]; simp [regsOf]) with hrs'def
  have hMcode : M (execVia p pc h CtrlPhase.entry)
      = Turing.TM2.Stmt.peek (Kg.reg rs') (fun s ov => { s with decision := ov.isSome })
          (Turing.TM2.Stmt.branch (fun s => s.decision)
            (bridgeTo p target) (bridgeTo p (pc.1 + 1))) := by
    have hone := hAgrees (cast (congrArg PhaseOf h.symm) CtrlPhase.entry)
    rw [show execVia p pc h CtrlPhase.entry
        = Λg.exec pc (cast (congrArg PhaseOf h.symm) CtrlPhase.entry) from rfl, hone,
      branchIfNZCode_apply]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h CtrlPhase.entry), cfg.var, cfg.stk⟩ :
      Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl]
  have hRegVal : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := hregs rs'
  have hbound : (1 : ℕ) ≤ 1 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
    rw [hcurEq]; simp only [instructionCost, one_mul]
    nlinarith [Nat.zero_le (bitLen (r.regs rs)), Nat.zero_le (regSize p r),
      Nat.zero_le (cfg.stk Kg.mem).length]
  by_cases hz : r.regs rs = 0
  · have hnil : cfg.stk (Kg.reg rs') = [] := by rw [hRegVal, hz]; simp [natToDigits]
    have hstep : Turing.TM2.step M cfg
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
      conv_lhs => rw [hcfgEq]
      show some (Turing.TM2.stepAux (M (execVia p pc h CtrlPhase.entry)) cfg.var cfg.stk) = _
      rw [hMcode, Turing.TM2.stepAux, hnil]
      rfl
    have hN : (flipBindG p M)^[1] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, cfg.stk⟩ := by
      show flipBindG p M (some cfg) = _
      rw [flipBindG]; show Turing.TM2.step M cfg = _; exact hstep
    have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq, hz]
    have hMemUnchanged : (step r).mem = r.mem := by simp [step, hcurEq]
    have hpcElse : (step r).pc = pc.1 + 1 := by simp [step, hcurEq, hz, hpcEq]
    refine ⟨_, _, hN, ?_, rfl, hbound, ?_⟩
    · refine ⟨by simp [step, hcurEq, hprog], ?_, ?_, rfl, ?_, ?_⟩
      · intro i; rw [hRegsUnchanged]; exact hregs i
      · obtain ⟨log, hmemstk, hmemlookup⟩ := hmem
        exact ⟨log, hmemstk, by rw [hMemUnchanged]; exact hmemlookup⟩
      · intro s; exact hscratch s
      · rw [ControlRep, hpcElse]
    · have hstkEq :
          ({ l := some (entryAt p (pc.1 + 1)), var := AllInstrState.canonical, stk := cfg.stk } :
            Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState).stk Kg.mem = cfg.stk Kg.mem := rfl
      have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hRegsUnchanged]
      rw [hstkEq, hrs]; omega
  · obtain ⟨d, ds, hcons⟩ :=
      List.exists_cons_of_ne_nil ((natToDigits_ne_nil_iff (r.regs rs)).mpr hz)
    have hcons' : cfg.stk (Kg.reg rs') = d :: ds := by rw [hRegVal, hcons]
    have hstep : Turing.TM2.step M cfg
        = some ⟨some (entryAt p target), AllInstrState.canonical, cfg.stk⟩ := by
      conv_lhs => rw [hcfgEq]
      show some (Turing.TM2.stepAux (M (execVia p pc h CtrlPhase.entry)) cfg.var cfg.stk) = _
      rw [hMcode, Turing.TM2.stepAux, hcons']
      rfl
    have hN : (flipBindG p M)^[1] (some cfg)
        = some ⟨some (entryAt p target), AllInstrState.canonical, cfg.stk⟩ := by
      show flipBindG p M (some cfg) = _
      rw [flipBindG]; show Turing.TM2.step M cfg = _; exact hstep
    have hRegsUnchanged : (step r).regs = r.regs := by simp [step, hcurEq, hz]
    have hMemUnchanged : (step r).mem = r.mem := by simp [step, hcurEq]
    have hpcJump : (step r).pc = target := by simp [step, hcurEq, hz]
    refine ⟨_, _, hN, ?_, rfl, hbound, ?_⟩
    · refine ⟨by simp [step, hcurEq, hprog], ?_, ?_, rfl, ?_, ?_⟩
      · intro i; rw [hRegsUnchanged]; exact hregs i
      · obtain ⟨log, hmemstk, hmemlookup⟩ := hmem
        exact ⟨log, hmemstk, by rw [hMemUnchanged]; exact hmemlookup⟩
      · intro s; exact hscratch s
      · rw [ControlRep, hpcJump]
    · have hstkEq :
          ({ l := some (entryAt p target), var := AllInstrState.canonical, stk := cfg.stk } :
            Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState).stk Kg.mem = cfg.stk Kg.mem := rfl
      have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hRegsUnchanged]
      rw [hstkEq, hrs]; omega

/-- `halt`'s `GrowingTimedInstrImpl` package. -/
def haltGrowingTimedImpl (p : List Instruction) (pc : Fin p.length)
    (h : p.get pc = Instruction.halt) : GrowingTimedInstrImpl p pc where
  code := (haltImpl p pc h).code
  C := 1
  G := 0
  growingSim := haltImpl_growing_bounded p pc h

/-- `jump`'s `GrowingTimedInstrImpl` package. -/
def jumpGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (target : ℕ)
    (h : p.get pc = .jump target) : GrowingTimedInstrImpl p pc where
  code := jumpCode p pc target h
  C := 1
  G := 0
  growingSim := jump_impl_growing_bounded p pc target h

/-- `branchIfNZ`'s `GrowingTimedInstrImpl` package. -/
def branchIfNZGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rs target : ℕ)
    (h : p.get pc = .branchIfNZ rs target) : GrowingTimedInstrImpl p pc where
  code := branchIfNZCode p pc rs target h
  C := 1
  G := 0
  growingSim := branchIfNZ_impl_growing_bounded p pc rs target h

end NPComplete.RAMToTM.Generic

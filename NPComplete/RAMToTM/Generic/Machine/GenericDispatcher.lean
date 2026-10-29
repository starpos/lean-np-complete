module

public import NPComplete.RAMToTM.Generic.Machine.GenericStore
public import NPComplete.RAMToTM.Generic.Machine.GenericLoad
public import NPComplete.RAMToTM.Generic.Machine.GenericAdd
public import NPComplete.RAMToTM.Generic.Machine.GenericSub
public import NPComplete.RAMToTM.Generic.Machine.GenericMul
public import NPComplete.RAMToTM.Generic.Machine.GenericBranch
public import NPComplete.RAMToTM.Generic.Machine.GenericMove
public import NPComplete.RAMToTM.Generic.Machine.GenericLoadImm
public import NPComplete.RAMToTM.Generic.Machine.GenericBranchIfLt
public import NPComplete.RAMToTM.Generic.Machine.GenericSetIfLt
public import NPComplete.RAMToTM.Generic.Machine.GenericSetIfEq
public import NPComplete.RAMToTM.Generic.Machine.GenericPrologue
public import NPComplete.RAMToTM.Generic.Machine.GenericCleanup
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider

/-!
# Site dispatcher assembly for an arbitrary supported program

Closes the non-uniform compiler theorem's core: given a program `p` where every position names a
currently-realized instruction (`ProgramSupported p`), assembles a single global dispatcher `Mg p`
and proves it correctly simulates every RAM step (`instrStepSim_of_programSupported`).

`siteImpl` dispatches on `p.get pc` — the only place that decides *which* instruction lives at a
site — reusing `siteTimedImpl`'s per-instruction sites (`storeGrowingTimedImpl`/
`loadGrowingTimedImpl`/`addGrowingTimedImpl`/`subGrowingTimedImpl`/`mulGrowingTimedImpl`/
`jumpGrowingTimedImpl`/`branchIfNZGrowingTimedImpl`/`haltGrowingTimedImpl`/`moveGrowingTimedImpl`/
`loadImmGrowingTimedImpl`/`branchIfLtGrowingTimedImpl`/`setIfLtGrowingTimedImpl`/
`setIfEqGrowingTimedImpl`, defined across `GenericStore.lean`/`GenericLoad.lean`/`GenericAdd.lean`/
`GenericSub.lean`/`GenericMul.lean`/`GenericBranch.lean`/`GenericMove.lean`/`GenericLoadImm.lean`/
`GenericBranchIfLt.lean`/`GenericSetIfLt.lean`/`GenericSetIfEq.lean`) for all thirteen `Instruction`
constructors — `siteImpl` is total, with no
`ProgramSupported`-contradiction branch.
`Mg p hSup outReg` then dispatches every `exec`-labeled position to its site's `InstrImpl.code`,
every `prologue`-labeled position to `Generic.prologueProg p` (`GenericPrologue.lean`), and every
`cleanup`-labeled position to `Generic.cleanupProg p outReg` (`GenericCleanup.lean`) — the
dispatcher wiring. `InstrStepSim`'s own hypotheses (`Represents` + `r.current ≠ halt`) never reach
the `prologue`/`cleanup` labels during normal execution (`Represents`'s `ControlRep` component only
ever places `cfg.l` at an `exec` label for an in-range, supported PC,
`pc_lt_length_of_current_ne_halt`), so wiring in the real `Stmt` trees changes nothing about
`instrStepSim_of_programSupported` et al.'s own proofs; what it *does* unlock is
`prologueAgrees_of_Mg`/`cleanupAgrees_of_Mg` below, which let `GenericPrologue.lean`'s
`prologue_run` and `GenericCleanup.lean`'s `cleanup_run_bound` (both proved abstractly against any
dispatcher satisfying `PrologueAgrees`/`CleanupAgrees`) specialize to this concrete `Mg`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program)
open NPComplete.BitEncoding (Bits)

/-- The realized instruction site at `pc`, dispatched on `p.get pc`, quantitatively (time bound
    plus growth bound): `storeGrowingTimedImpl`/`loadGrowingTimedImpl`/
    `addGrowingTimedImpl`/`subGrowingTimedImpl`/`mulGrowingTimedImpl`/`jumpGrowingTimedImpl`/
    `branchIfNZGrowingTimedImpl`/`haltGrowingTimedImpl`/`moveGrowingTimedImpl`/
    `loadImmGrowingTimedImpl`/`branchIfLtGrowingTimedImpl`/`setIfLtGrowingTimedImpl`/
    `setIfEqGrowingTimedImpl`, one for each of the thirteen `Instruction` constructors. `siteImpl`
    below is defined as this package's forgetful projection, so `Mg`'s dispatch and this one's
    `code` fields agree definitionally without a per-instruction bridge lemma. -/
def siteTimedImpl (p : List Instruction) (_hSup : ProgramSupported p) (pc : Fin p.length) :
    GrowingTimedInstrImpl p pc :=
  match hi : p.get pc with
  | .loadImm rd n => loadImmGrowingTimedImpl p pc rd n hi
  | .move rd rs => moveGrowingTimedImpl p pc rd rs hi
  | .load rDest rAddr => loadGrowingTimedImpl p pc rDest rAddr hi
  | .store rSrc rAddr => storeGrowingTimedImpl p pc rSrc rAddr hi
  | .add rd rs rt => addGrowingTimedImpl p pc rd rs rt hi
  | .sub rd rs rt => subGrowingTimedImpl p pc rd rs rt hi
  | .mul rd rs rt => mulGrowingTimedImpl p pc rd rs rt hi
  | .setIfLt rd rs rt => setIfLtGrowingTimedImpl p pc rd rs rt hi
  | .setIfEq rd rs rt => setIfEqGrowingTimedImpl p pc rd rs rt hi
  | .branchIfLt rs rt target => branchIfLtGrowingTimedImpl p pc rs rt target hi
  | .branchIfNZ rs target => branchIfNZGrowingTimedImpl p pc rs target hi
  | .jump target => jumpGrowingTimedImpl p pc target hi
  | .halt => haltGrowingTimedImpl p pc hi

/-- The realized instruction site at `pc`, qualitatively: `siteTimedImpl` forgetting its `C`/`G`
    bounds, via the two `toTimedInstrImpl`/`toInstrImpl` forgetful maps. `hSup` is threaded
    through only because `InstrImpl` sites in `Mg` are parameterized over it;
    `siteImpl` itself does not inspect it. -/
def siteImpl (p : List Instruction) (hSup : ProgramSupported p) (pc : Fin p.length) :
    InstrImpl p pc :=
  (siteTimedImpl p hSup pc).toTimedInstrImpl.toInstrImpl

/-- The global site dispatcher for a supported program `p`: every `exec pc ph` label runs
    `siteImpl`'s code for that site, `prologue ph` runs `prologueProg p ph`, and `cleanup ph` runs
    `cleanupProg p outReg ph` (module docstring). -/
def Mg (p : List Instruction) (hSup : ProgramSupported p) (outReg : Fin (regBound p)) :
    Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState
  | .exec pc ph => (siteImpl p hSup pc).code ph
  | .prologue ph => prologueProg p ph
  | .cleanup ph => cleanupProg p outReg ph

/-- `Mg`'s `prologue` case is definitionally `prologueProg p`, so it trivially satisfies
    `PrologueAgrees` — the bridge `GenericPrologue.lean`'s `prologue_run` needs to specialize to
    this concrete dispatcher. -/
lemma prologueAgrees_of_Mg (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) : PrologueAgrees p (Mg p hSup outReg) := fun _ => rfl

/-- `Mg`'s `cleanup` case is definitionally `cleanupProg p outReg`, so it trivially satisfies
    `CleanupAgrees` — the bridge `GenericCleanup.lean`'s `cleanup_run_bound` needs to specialize to
    this concrete dispatcher. -/
lemma cleanupAgrees_of_Mg (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) : CleanupAgrees p outReg (Mg p hSup outReg) := fun _ => rfl

/-- `RAM.current`'s out-of-range-is-halt convention (`BitCostRAM.RAM.current` /
    `List.getD_eq_default`), contrapositived: a non-`halt` current instruction forces the PC
    in-range, so `Represents`'s `ControlRep` component always places a live config at some site's
    `entryAt`, never at the out-of-range `cleanup` fallback. -/
lemma pc_lt_length_of_current_ne_halt (p : List Instruction) (r : RAM) (hprog : r.program = p)
    (hcur : r.current ≠ Instruction.halt) : r.pc < p.length := by
  by_contra hge
  push Not at hge
  exact hcur (by rw [RAM.current, hprog]; exact List.getD_eq_default p Instruction.halt hge)

/-- The global dispatcher theorem: a supported program's global dispatcher correctly simulates every RAM
    step. Site `⟨r.pc, hlt⟩`'s own `InstrImpl.sim` does all the work once `SiteAgrees` is
    established — true by `rfl`, since `Mg`'s `exec` case is defined as exactly that site's
    `code`. -/
lemma instrStepSim_of_programSupported (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) : InstrStepSim p (Mg p hSup outReg) := by
  intro cfg r hRep hcur
  have hprog : r.program = p := hRep.1
  have hlt : r.pc < p.length := pc_lt_length_of_current_ne_halt p r hprog hcur
  have hAgrees : SiteAgrees p ⟨r.pc, hlt⟩ (siteImpl p hSup ⟨r.pc, hlt⟩).code (Mg p hSup outReg) :=
    fun _ => rfl
  exact (siteImpl p hSup ⟨r.pc, hlt⟩).sim (Mg p hSup outReg) hAgrees cfg r hRep rfl hcur

/-- The arbitrary-length simulation theorem: a supported program's global dispatcher correctly simulates *any* number of
    RAM steps, not just one — `runSim_of_instrStepSim` applied to `Mg p`'s own `InstrStepSim`. -/
lemma runSim_of_programSupported (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) : RunSim p (Mg p hSup outReg) :=
  runSim_of_instrStepSim p (Mg p hSup outReg) (instrStepSim_of_programSupported p hSup outReg)

/-- The quantitative dispatcher theorem: a supported program's global dispatcher satisfies
    the quantitative one-step simulation `GrowingInstrStepSim`, with `C`/`G` taken as the sup over
    all program positions' own `siteTimedImpl` constants, as required by
    `boundedRunSim_of_growingInstrStepSim`. -/
lemma growingInstrStepSim_of_programSupported (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) :
    GrowingInstrStepSim p (Mg p hSup outReg)
      (Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).C))
      (Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).G)) := by
  intro cfg r hRep hcur
  have hprog : r.program = p := hRep.1
  have hlt : r.pc < p.length := pc_lt_length_of_current_ne_halt p r hprog hcur
  set pc : Fin p.length := ⟨r.pc, hlt⟩ with hpc
  have hAgrees : SiteAgrees p pc (siteTimedImpl p hSup pc).code (Mg p hSup outReg) := fun _ => rfl
  obtain ⟨n, cfg', hrun, hRep', hio, hbound, hgrowth⟩ :=
    (siteTimedImpl p hSup pc).growingSim (Mg p hSup outReg) hAgrees cfg r hRep rfl hcur
  have hCle : (siteTimedImpl p hSup pc).C ≤
      Finset.univ.sup (fun q : Fin p.length => (siteTimedImpl p hSup q).C) :=
    Finset.le_sup (f := fun q : Fin p.length => (siteTimedImpl p hSup q).C) (Finset.mem_univ pc)
  have hGle : (siteTimedImpl p hSup pc).G ≤
      Finset.univ.sup (fun q : Fin p.length => (siteTimedImpl p hSup q).G) :=
    Finset.le_sup (f := fun q : Fin p.length => (siteTimedImpl p hSup q).G) (Finset.mem_univ pc)
  refine ⟨n, cfg', hrun, hRep', hio, ?_, ?_⟩
  · calc n ≤ (siteTimedImpl p hSup pc).C *
        (regSize p r + (cfg.stk Kg.mem).length +
          instructionCost r.regs r.mem r.current + 1) ^ 2 := hbound
      _ ≤ Finset.univ.sup (fun q : Fin p.length => (siteTimedImpl p hSup q).C) *
          (regSize p r + (cfg.stk Kg.mem).length +
            instructionCost r.regs r.mem r.current + 1) ^ 2 := by gcongr
  · calc regSize p (step r) + (cfg'.stk Kg.mem).length
        ≤ regSize p r + (cfg.stk Kg.mem).length +
            (siteTimedImpl p hSup pc).G * (instructionCost r.regs r.mem r.current + 1) := hgrowth
      _ ≤ regSize p r + (cfg.stk Kg.mem).length +
            Finset.univ.sup (fun q : Fin p.length => (siteTimedImpl p hSup q).G) *
              (instructionCost r.regs r.mem r.current + 1) := by gcongr

/-- The full non-uniform compiler theorem, quantitatively: composing
    `growingInstrStepSim_of_programSupported` with `boundedRunSim_of_growingInstrStepSim` gives a
    concrete `BoundedRunSim` for the actual dispatcher `Mg p hSup` of any supported program. -/
lemma boundedRunSim_of_programSupported (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) :
    BoundedRunSim p (Mg p hSup outReg)
      ((Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).C)) *
        (2 * Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).G) + 1) ^ 2) :=
  boundedRunSim_of_growingInstrStepSim p (Mg p hSup outReg) _ _
    (growingInstrStepSim_of_programSupported p hSup outReg)

/-- `boundedRunSim_of_programSupported`'s growth-exposing counterpart: needed to
    bound `GenericCleanup.lean`'s `cleanup_run_bound`, whose own step count depends on the
    register/memory-log *sizes* present when cleanup starts, not just on how many TM steps the
    main run took to get there. -/
lemma boundedRunSimWithGrowth_of_programSupported (p : List Instruction)
    (hSup : ProgramSupported p) (outReg : Fin (regBound p)) :
    BoundedRunSimWithGrowth p (Mg p hSup outReg)
      ((Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).C)) *
        (2 * Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).G) + 1) ^ 2)
      (Finset.univ.sup (fun pc : Fin p.length => (siteTimedImpl p hSup pc).G)) :=
  boundedRunSimWithGrowth_of_growingInstrStepSim p (Mg p hSup outReg) _ _
    (growingInstrStepSim_of_programSupported p hSup outReg)

/-- `flipBindPrologue`/`flipBindCleanup`/`flipBindG` all unfold to `fun x => x.bind
    (Turing.TM2.step M)` for the same `M`, so they are the exact same function once applied to a
    shared dispatcher — the "same function" `Function.iterate_add_apply` needs to chain a
    prologue run onto a main run into one `Function.iterate` composition. -/
lemma flipBindPrologue_eq_flipBindG (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) :
    flipBindPrologue p M = flipBindG p M := rfl

/-- `flipBindCleanup`'s counterpart to `flipBindPrologue_eq_flipBindG`, needed to chain a main run
    onto a cleanup run. -/
lemma flipBindCleanup_eq_flipBindG (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) :
    flipBindCleanup p M = flipBindG p M := rfl

/-- `GenericPrologue.lean`'s `prologue_run`, specialized to the concrete dispatcher
    `Mg p hSup outReg` via `prologueAgrees_of_Mg` — the prologue correctness theorem now
    holds for an actual, buildable machine rather than an abstract `PrologueAgrees`-satisfying
    one. -/
lemma prologue_run_of_Mg (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) (bits : List Bool) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hIo : Sg Kg.io = bits)
    (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit))
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hMem : Sg Kg.mem = ([] : List MemSym)) :
    ∃ n, (flipBindPrologue p (Mg p hSup outReg))^[n]
        (some ⟨some (Λg.prologue .scanInput), var, Sg⟩)
      = some ⟨some (entryAt p 0), AllInstrState.canonical,
          Function.update
            (Function.update
              (Function.update (Function.update Sg Kg.io []) (Kg.scratch .prologueCounter) [])
              (Kg.scratch .prologueWork) [])
            Kg.mem (encodeLog (inputLogRev bits))⟩ ∧
      n ≤ bitLen bits.length + bits.length * (4 * bitLen bits.length + 10) + 3 :=
  prologue_run (prologueAgrees_of_Mg p hSup outReg) bits var Sg hIo hCounter hWork hMem

/-- `GenericCleanup.lean`'s `cleanup_run_bound`, specialized to the concrete dispatcher
    `Mg p hSup outReg` via `cleanupAgrees_of_Mg` — mirrors how `prologue_run_of_Mg` specializes
    `prologue_run`, giving cleanup correctness for an actual, buildable machine together with the
    total step bound needed below. -/
lemma cleanup_run_of_Mg_bound (p : List Instruction) (hSup : ProgramSupported p)
    (outReg : Fin (regBound p)) (regs : Fin (regBound p) → ℕ) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hReg : ∀ i : Fin (regBound p), Sg (Kg.reg i) = natToDigits (regs i)) (hMem : Sg Kg.mem = m0)
    (hCopy : Sg (Kg.scratch .copyScratch) = copyc) (hQuery : Sg (Kg.scratch .query) = queryc)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = queryTmpc)
    (hLogTmp : Sg (Kg.scratch .logTmp) = logTmpc)
    (hWorkRev : Sg (Kg.scratch .workRev) = workRevc)
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = lhsOperandc)
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = rhsOperandc)
    (hSumScratch : Sg (Kg.scratch .sumScratch) = sumScratchc)
    (hDiffScratch : Sg (Kg.scratch .diffScratch) = diffScratchc)
    (hPrologueCounter : Sg (Kg.scratch .prologueCounter) = prologueCounterc)
    (hPrologueWork : Sg (Kg.scratch .prologueWork) = prologueWorkc) :
    ∃ n Sg', (flipBindCleanup p (Mg p hSup outReg))^[n]
        (some ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩)
      = some ⟨none, AllInstrState.canonical, Sg'⟩ ∧
        (∀ i : Fin (regBound p), Sg' (Kg.reg i) = []) ∧ Sg' Kg.mem = [] ∧
        (∀ sk : ScratchKind, Sg' (Kg.scratch sk) = []) ∧
        Sg' Kg.io = decide (regs outReg = 1) :: Sg Kg.io ∧
        n ≤ (∑ i : Fin (regBound p), (natToDigits (regs i)).length) + regBound p +
          m0.length + copyc.length + queryc.length + queryTmpc.length + logTmpc.length +
          workRevc.length + lhsOperandc.length + rhsOperandc.length + sumScratchc.length +
          diffScratchc.length + prologueCounterc.length + prologueWorkc.length + 17 :=
  cleanup_run_bound (cleanupAgrees_of_Mg p hSup outReg) regs m0 copyc queryc queryTmpc logTmpc
    workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc
    var Sg hReg hMem hCopy hQuery hQueryTmp hLogTmp hWorkRev hLhsOperand hRhsOperand hSumScratch
    hDiffScratch hPrologueCounter hPrologueWork

/-- The machine-start stack assignment `prologue_run`'s docstring calls for: every stack empty
    except `Kg.io`, holding the raw input bits. -/
def initialSg (p : List Instruction) (bits : Bits) : ∀ k, List (Γg p k)
  | .reg _ => []
  | .mem => []
  | .io => bits
  | .scratch _ => []

/-- The prologue lands on a config representing `compiledInputFullRAM prog dOutReg bits` for
    `fullProgram` (the main program plus its `outputLoad` epilogue, `BoundedWhileDecider.lean`
    module comment) — `prologue_run_of_Mg` is already generic in its program-list argument, so the
    same proof script applies regardless of which program list `Mg`/`Λg`/`prologueProg` operate
    over. Also exposes `cfg.stk Kg.io = []` alongside the same witness (`prologue_run_of_Mg`'s own
    conclusion drains `Kg.io` to `[]` first and never touches it again) — the cleanup-wiring
    composition (`answer_run_full_bound_of_boundedWhileDecider`) needs this to know the main run's own
    `io` preservation (`GrowingBoundedSiteStepSim`'s bundled `io` conjunct) starts from `[]`. -/
lemma represents_compiledInputFullRAM_of_Mg (prog : Program) (dOutReg : ℕ)
    (mgReg : Fin (regBound (fullProgram prog dOutReg))) (bits : Bits) :
    ∃ n cfg, (flipBindPrologue (fullProgram prog dOutReg)
        (Mg (fullProgram prog dOutReg) (programSupported_any _) mgReg))^[n]
        (some ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
          initialSg (fullProgram prog dOutReg) bits⟩)
      = some cfg ∧ Represents (fullProgram prog dOutReg) cfg
        (compiledInputFullRAM prog dOutReg bits) ∧
      (cfg.stk Kg.mem).length ≤ (bits.length + 1) * (2 * bitLen bits.length + 2) ∧
      cfg.stk Kg.io = [] ∧
      n ≤ bitLen bits.length + bits.length * (4 * bitLen bits.length + 10) + 3 := by
  obtain ⟨n, hrun, hn⟩ := prologue_run_of_Mg (fullProgram prog dOutReg) (programSupported_any _)
    mgReg bits AllInstrState.canonical (initialSg (fullProgram prog dOutReg) bits) rfl rfl rfl rfl
  refine ⟨n, _, hrun, ⟨rfl, ?_, ?_, rfl, ?_, rfl⟩, ?_, ?_, hn⟩
  · intro i
    rw [show (compiledInputFullRAM prog dOutReg bits).regs i = 0 from rfl, natToDigits_zero]
    simp [Function.update, initialSg]
  · exact ⟨inputLogRev bits, rfl, lookupD_inputLogRev bits⟩
  · intro s
    cases s <;> simp [Function.update, initialSg]
  · exact encodeLog_inputLogRev_length_le bits
  · simp [Function.update]

/-- Bounds `bitLen (r.mem addr)` for any `addr`, using only `Represents`'s memory-log length —
    needed to turn the `regSize`+memory-log-length growth bound
    `boundedRunSimWithGrowth_of_programSupported` gives `answer_run_full_bound_of_boundedWhileDecider`
    into an `instructionCost`-phrased (`bitLen`-based) cost bound for `outputLoad`'s epilogue.
    `Represents`'s memory conjunct is existentially quantified over the
    write-log, so this goes through the concrete log `cfg` carries
    (`natToDigits_length_lookupD_le`), not through `r.mem addr`'s value alone. -/
lemma bitLen_mem_le_of_represents (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (addr : ℕ) :
    bitLen (r.mem addr) ≤ 4 * (cfg.stk Kg.mem).length + 1 := by
  obtain ⟨-, -, ⟨log, hlog, hlookup⟩, -, -, -⟩ := hRep
  rw [← hlookup addr]
  calc bitLen (lookupD log addr 0) ≤ 4 * (natToDigits (lookupD log addr 0)).length + 1 :=
        bitLen_le_of_natToDigits_length _
    _ ≤ 4 * (max (natToDigits 0).length (encodeLog log).length) + 1 := by
        gcongr
        exact natToDigits_length_lookupD_le log addr 0
    _ = 4 * (cfg.stk Kg.mem).length + 1 := by
        rw [natToDigits_zero, hlog]; simp

/-- The register `fullProgram`'s `outputLoad` epilogue always stages its answer into (`register 0`,
    `BoundedWhileDecider.lean`'s module comment) — every `fullProgram` has at least this register
    (`regBound` is `1 + ...`, never `0`), so this needs no side condition. -/
def outReg0 {α : Type} {enc : α → Bits} {D L : α → Prop} (d : BoundedWhileDecider enc D L) :
    Fin (regBound (fullProgram d.p d.outReg)) :=
  ⟨0, by unfold regBound; omega⟩

/-! ## A single polynomial bound on the total step count

Composing all four legs (prologue/main/epilogue-sim/cleanup) into one run needs a single
polynomial bound on the total step count, not just qualitative termination. The four named
quantities below factor the recurring sub-polynomials (the `mem0`/cost bounds
`answer_run_full_bound_of_boundedWhileDecider`'s proof establishes, `Mg`'s site sup constants) out
of `answer_run_full_bound_of_boundedWhileDecider`'s statement and proof — otherwise each would need to
be repeated verbatim three or more times (as the epilogue's own cost-delta bound depends on the
main run's growth bound, which itself depends on `mem0`/cost), which is exactly the kind of
duplication this file's other `def`s (`regSize`, `Csup`/`Gsup`-shaped `Finset.univ.sup`
expressions) exist to avoid at smaller scale. -/

/-- The polynomial bound on the write-log encoding's length right after the prologue lands —
    `represents_compiledInputFullRAM_of_Mg`'s own bound, factored out since it recurs as the base
    case of both the main run's step-count bound and its growth bound. -/
def mem0Bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (_d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  ((enc x).length + 1) * (2 * bitLen (enc x).length + 2)

/-- The polynomial bound on the compiled main program's accumulated bit-cost —
    `answer_run_full_bound_of_boundedWhileDecider`'s own `hcostle`, factored out for the same reason
    as `mem0Bound`. -/
def costBound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  8 * d.c * ((enc x).length + 1) ^ d.c *
    (2 * max (d.bit_c * ((enc x).length + 1) ^ d.bit_c)
      (max (programImmBound d.p) (bitLen d.outReg)) + 1)

/-- `Mg (fullProgram d.p d.outReg)`'s uniform site time-bound constant `C`, factored out of
    `answer_run_full_bound_of_boundedWhileDecider` for readability (it recurs in every leg's own
    step-count bound). -/
def siteCsup {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : ℕ :=
  Finset.univ.sup (fun pc : Fin (fullProgram d.p d.outReg).length =>
    (siteTimedImpl (fullProgram d.p d.outReg) (programSupported_any _) pc).C)

/-- `Mg (fullProgram d.p d.outReg)`'s uniform site growth-bound constant `G`, `siteCsup`'s
    counterpart. -/
def siteGsup {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : ℕ :=
  Finset.univ.sup (fun pc : Fin (fullProgram d.p d.outReg).length =>
    (siteTimedImpl (fullProgram d.p d.outReg) (programSupported_any _) pc).G)

/-- The compiled main program's RAM run on the full input halts at `codeLenP d.p` with its
    `mem` equal to `Program.eval` and accumulated cost within `costBound`; this is the semantic
    half of the main leg, kept apart from the machine-level simulation. -/
lemma answer_run_full_bound_of_boundedWhileDecider_main_cost {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (x : α) (hx : D x) :
    ∃ k, (run k (compiledInputFullRAM d.p d.outReg (enc x))).pc = codeLenP d.p ∧
      (run k (compiledInputFullRAM d.p d.outReg (enc x))).mem =
        Program.eval d.p (bitInputStore (enc x)) ∧
      (run k (compiledInputFullRAM d.p d.outReg (enc x))).cost ≤ costBound d x := by
  obtain ⟨k, hkpc, hkmem, -, -, hkle3, hcost⟩ :=
    compile_exec_cost d.p 0 (compiledInputFullRAM d.p d.outReg (enc x))
      (max (programImmBound d.p) (bitLen d.outReg))
      (segmentAt_fullProgram_compile d.p d.outReg)
      (programImmediatesLe_fullProgram d.p d.outReg)
  obtain ⟨W, hWle, hDyn⟩ := d.compiled_operands_le x hx
  have hkbudget : k ≤ 8 * d.p.cost (compiledInputFullRAM d.p d.outReg (enc x)).mem := by omega
  have hcost0 : (compiledInputFullRAM d.p d.outReg (enc x)).cost = 0 := rfl
  have hkpc' : (run k (compiledInputFullRAM d.p d.outReg (enc x))).pc = codeLenP d.p := by
    have h0 : (compiledInputFullRAM d.p d.outReg (enc x)).pc = 0 := rfl
    rw [h0, zero_add] at hkpc
    exact hkpc
  have hDynFull : RunDynLe W k (compiledInputFullRAM d.p d.outReg (enc x)) :=
    runDynLe_bare_to_full d.p d.outReg (enc x) W k hkpc' (hDyn k hkbudget)
  refine ⟨k, hkpc', hkmem, ?_⟩
  calc (run k (compiledInputFullRAM d.p d.outReg (enc x))).cost
      ≤ (compiledInputFullRAM d.p d.outReg (enc x)).cost +
          8 * d.p.cost (compiledInputFullRAM d.p d.outReg (enc x)).mem *
            (2 * max W (max (programImmBound d.p) (bitLen d.outReg)) + 1) :=
        hcost W hDynFull
    _ ≤ 8 * (d.c * ((enc x).length + 1) ^ d.c) *
          (2 * max (d.bit_c * ((enc x).length + 1) ^ d.bit_c)
            (max (programImmBound d.p) (bitLen d.outReg)) + 1) := by
        rw [hcost0, zero_add]
        gcongr
        exact d.cost_le x hx
    _ = costBound d x := by unfold costBound; ring

/-- Simulates the main leg on the TM: from a configuration representing the initial RAM, the
    dispatcher reaches one representing the RAM after `k` steps, within the cubic step bound and
    with the register/memory-log potential bounded by `mem0Bound` and `costBound`. -/
lemma answer_run_full_bound_of_boundedWhileDecider_main_run {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (x : α) (k : ℕ)
    (cfg0 : Turing.TM2.Cfg (Γg (fullProgram d.p d.outReg)) (Λg (fullProgram d.p d.outReg))
      AllInstrState)
    (hRep0 : Represents (fullProgram d.p d.outReg) cfg0
      (compiledInputFullRAM d.p d.outReg (enc x)))
    (hmem0 : (cfg0.stk Kg.mem).length ≤ mem0Bound d x)
    (hcostle : (run k (compiledInputFullRAM d.p d.outReg (enc x))).cost ≤ costBound d x) :
    ∃ n cfg, (flipBindG (fullProgram d.p d.outReg)
        (Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)))^[n] (some cfg0)
        = some cfg ∧
      Represents (fullProgram d.p d.outReg) cfg (run k (compiledInputFullRAM d.p d.outReg (enc x))) ∧
      cfg.stk Kg.io = cfg0.stk Kg.io ∧
      n ≤ siteCsup d * (2 * siteGsup d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 ∧
      regSize (fullProgram d.p d.outReg) (run k (compiledInputFullRAM d.p d.outReg (enc x))) +
          (cfg.stk Kg.mem).length ≤ mem0Bound d x + 2 * siteGsup d * costBound d x := by
  have hcost0 : (compiledInputFullRAM d.p d.outReg (enc x)).cost = 0 := rfl
  have hRegSize : regSize (fullProgram d.p d.outReg) (compiledInputFullRAM d.p d.outReg (enc x))
      = 0 := by
    simp [regSize, compiledInputFullRAM, emptyBank, natToDigits_zero]
  obtain ⟨n, cfg, hrun, hRepr, hio, hnbound, hgrowth⟩ :=
    boundedRunSimWithGrowth_of_programSupported (fullProgram d.p d.outReg)
      (programSupported_any _) (outReg0 d) k cfg0 (compiledInputFullRAM d.p d.outReg (enc x)) hRep0
  rw [hRegSize, hcost0, Nat.sub_zero] at hnbound hgrowth
  refine ⟨n, cfg, hrun, hRepr, hio, ?_, ?_⟩
  · rw [zero_add] at hnbound
    refine hnbound.trans ?_
    unfold siteCsup siteGsup
    gcongr
  · refine hgrowth.trans ?_
    unfold siteGsup
    gcongr
    simpa using hmem0


/-- Simulates `outputLoad`'s epilogue on the TM from a potential bound `B`: the cost delta is
    controlled via `bitLen_mem_le_of_represents`, and the landing PC is `fullProgram`'s length. -/
lemma answer_run_full_bound_of_boundedWhileDecider_epilogue {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (B : ℕ) (rr : RAM)
    (cfg : Turing.TM2.Cfg (Γg (fullProgram d.p d.outReg)) (Λg (fullProgram d.p d.outReg))
      AllInstrState)
    (hRepr : Represents (fullProgram d.p d.outReg) cfg rr)
    (hprog : rr.program = fullProgram d.p d.outReg) (hpc : rr.pc = codeLenP d.p)
    (hB : regSize (fullProgram d.p d.outReg) rr + (cfg.stk Kg.mem).length ≤ B) :
    ∃ k2 n2 cfg2, (flipBindG (fullProgram d.p d.outReg)
        (Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)))^[n2] (some cfg)
        = some cfg2 ∧
      Represents (fullProgram d.p d.outReg) cfg2 (run k2 rr) ∧
      cfg2.stk Kg.io = cfg.stk Kg.io ∧
      (run k2 rr).pc = (fullProgram d.p d.outReg).length ∧
      (run k2 rr).regs 0 = rr.mem d.outReg ∧
      n2 ≤ siteCsup d * (2 * siteGsup d + 1) ^ 2 *
        (B + (2 * bitLen d.outReg + 4 * B + 3) + 1) ^ 3 ∧
      regSize (fullProgram d.p d.outReg) (run k2 rr) + (cfg2.stk Kg.mem).length ≤
        B + 2 * siteGsup d * (2 * bitLen d.outReg + 4 * B + 3) := by
  have hseg : SegmentAt rr.program rr.pc (outputLoad d.outReg) := by
    rw [hprog, hpc]; exact segmentAt_fullProgram_outputLoad d.p d.outReg
  obtain ⟨k2, hk2pc, hk2reg, -, -, -, hk2cost⟩ := outputLoad_exec_cost d.outReg rr hseg
  have hbitLenMem : bitLen (rr.mem d.outReg) ≤ 4 * (cfg.stk Kg.mem).length + 1 :=
    bitLen_mem_le_of_represents _ cfg rr hRepr d.outReg
  have hdelta : (run k2 rr).cost - rr.cost ≤ 2 * bitLen d.outReg + 4 * B + 3 := by
    omega
  obtain ⟨n2, cfg2, hrun2, hRepr2, hio2, hn2bound, hgrowth2⟩ :=
    boundedRunSimWithGrowth_of_programSupported (fullProgram d.p d.outReg)
      (programSupported_any _) (outReg0 d) k2 cfg rr hRepr
  refine ⟨k2, n2, cfg2, hrun2, hRepr2, hio2, ?_, hk2reg, ?_, ?_⟩
  · rw [hk2pc, hpc, outputLoad_length, fullProgram_length]
  · refine hn2bound.trans ?_
    unfold siteCsup siteGsup
    gcongr
  · refine hgrowth2.trans ?_
    unfold siteGsup
    gcongr


/-- Cleanup leg: from a configuration whose PC has run off the end of `fullProgram`, the
    dispatcher halts with every non-`io` stack empty and the staged answer bit pushed on `io`, in
    at most `B + regBound + 17` steps. -/
lemma answer_run_full_bound_of_boundedWhileDecider_cleanup {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (B : ℕ) (r2 : RAM)
    (cfg2 : Turing.TM2.Cfg (Γg (fullProgram d.p d.outReg)) (Λg (fullProgram d.p d.outReg))
      AllInstrState)
    (hRepr2 : Represents (fullProgram d.p d.outReg) cfg2 r2)
    (hpc : r2.pc = (fullProgram d.p d.outReg).length)
    (hB : regSize (fullProgram d.p d.outReg) r2 + (cfg2.stk Kg.mem).length ≤ B) :
    ∃ n3 Sg', (flipBindG (fullProgram d.p d.outReg)
        (Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)))^[n3] (some cfg2)
        = some ⟨none, AllInstrState.canonical, Sg'⟩ ∧
      (∀ i : Fin (regBound (fullProgram d.p d.outReg)), Sg' (Kg.reg i) = []) ∧
      Sg' Kg.mem = [] ∧ (∀ sk : ScratchKind, Sg' (Kg.scratch sk) = []) ∧
      Sg' Kg.io = decide (r2.regs 0 = 1) :: cfg2.stk Kg.io ∧
      n3 ≤ B + regBound (fullProgram d.p d.outReg) + 17 := by
  have hcfg2l : cfg2.l = some (Λg.cleanup CleanupPhase.checkHead) := by
    have hctrl := hRepr2.2.2.2.2.2
    rw [ControlRep] at hctrl
    rw [hctrl, hpc, entryAt]
    simp
  have hcfg2eq : (⟨some (Λg.cleanup CleanupPhase.checkHead), cfg2.var, cfg2.stk⟩ :
      Turing.TM2.Cfg (Γg (fullProgram d.p d.outReg)) (Λg (fullProgram d.p d.outReg))
        AllInstrState) = cfg2 := by
    have heta : cfg2 = ⟨cfg2.l, cfg2.var, cfg2.stk⟩ := by cases cfg2; rfl
    rw [heta, hcfg2l]
  obtain ⟨n3, Sg', hrun3, hSgReg, hSgMem, hSgScr, hSgIo, hn3bound⟩ :=
    cleanup_run_of_Mg_bound (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)
      (fun i => r2.regs i) (cfg2.stk Kg.mem)
      [] [] [] [] [] [] [] [] [] [] [] cfg2.var cfg2.stk hRepr2.2.1 rfl
      (hRepr2.2.2.2.2.1 .copyScratch) (hRepr2.2.2.2.2.1 .query) (hRepr2.2.2.2.2.1 .queryTmp)
      (hRepr2.2.2.2.2.1 .logTmp) (hRepr2.2.2.2.2.1 .workRev) (hRepr2.2.2.2.2.1 .lhsOperand)
      (hRepr2.2.2.2.2.1 .rhsOperand) (hRepr2.2.2.2.2.1 .sumScratch)
      (hRepr2.2.2.2.2.1 .diffScratch) (hRepr2.2.2.2.2.1 .prologueCounter)
      (hRepr2.2.2.2.2.1 .prologueWork)
  rw [hcfg2eq, flipBindCleanup_eq_flipBindG] at hrun3
  refine ⟨n3, Sg', hrun3, hSgReg, hSgMem, hSgScr, hSgIo, ?_⟩
  have hregSizeEq : regSize (fullProgram d.p d.outReg) r2 =
      ∑ i : Fin (regBound (fullProgram d.p d.outReg)), (natToDigits (r2.regs i)).length := rfl
  simp only [List.length_nil, add_zero] at hn3bound
  omega


/-- The strong form that the `Turing.FinTM2` bridge needs: a full run, plus the *entire* final
    config, not just `cfg'.l`/`cfg'.stk Kg.io`: `cfg'.var = AllInstrState.canonical` and every
    non-`Kg.io` stack is empty, matching
    `Turing.FinTM2.haltList`'s full-stack specification exactly (`Kg` has no constructors besides
    `reg`/`mem`/`io`/`scratch`) — and a single polynomial (in `(enc x).length`, treating
    `d.c`/`d.bit_c`/`programImmBound d.p`/`bitLen d.outReg`/`Mg`'s site constants as fixed
    constants of `d`) bound on the total step count `n`. `cleanup_run_of_Mg_bound` already proves
    the `reg`/`mem`/`scratch`-empty facts (`hSgReg`/`hSgMem`/`hSgScr` below) as part of its own
    conclusion, and they are passed on here.
    The proof derives the main-run and
    epilogue legs with `boundedRunSimWithGrowth_of_programSupported` (rather than the plain
    `boundedRunSim_of_programSupported`, which does not expose the register/memory-log potential
    needed below) since the epilogue's own cost delta (`outputLoad_exec_cost`, via
    `bitLen_mem_le_of_represents`) and
    `cleanup_run_of_Mg_bound`'s step bound both need the combined register/memory-log potential at
    the point they start from, not just the step count to get there. No attempt is made at a tight
    closed form: the four legs' bounds are simply summed via `Nat.add_le_add`. -/
lemma answer_run_full_bound_of_boundedWhileDecider {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (hx : D x) :
    ∃ n cfg', (flipBindG (fullProgram d.p d.outReg)
        (Mg (fullProgram d.p d.outReg) (programSupported_any _) (outReg0 d)))^[n]
        (some ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
          initialSg (fullProgram d.p d.outReg) (enc x)⟩) = some cfg' ∧
      cfg'.l = none ∧ cfg'.var = AllInstrState.canonical ∧
      (∀ i : Fin (regBound (fullProgram d.p d.outReg)), cfg'.stk (Kg.reg i) = []) ∧
      cfg'.stk Kg.mem = [] ∧
      (∀ sk : ScratchKind, cfg'.stk (Kg.scratch sk) = []) ∧
      cfg'.stk Kg.io = [decide (d.p.eval (bitInputStore (enc x)) d.outReg = 1)] ∧
      n ≤ (bitLen (enc x).length + (enc x).length * (4 * bitLen (enc x).length + 10) + 3) +
        siteCsup d * (2 * siteGsup d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 +
        siteCsup d * (2 * siteGsup d + 1) ^ 2 *
          (mem0Bound d x + 2 * siteGsup d * costBound d x +
            (2 * bitLen d.outReg + 4 * (mem0Bound d x + 2 * siteGsup d * costBound d x) + 3) +
            1) ^ 3 +
        (mem0Bound d x + 2 * siteGsup d * costBound d x +
          2 * siteGsup d *
            (2 * bitLen d.outReg + 4 * (mem0Bound d x + 2 * siteGsup d * costBound d x) + 3) +
          regBound (fullProgram d.p d.outReg) + 17) := by
  obtain ⟨n0, cfg0, hrun0, hRep0, hmem0, hio0, hn0bound⟩ :=
    represents_compiledInputFullRAM_of_Mg d.p d.outReg (outReg0 d) (enc x)
  obtain ⟨k, hkpc, hkmem, hcostle⟩ :=
    answer_run_full_bound_of_boundedWhileDecider_main_cost d x hx
  obtain ⟨n, cfg, hrun, hRepr, hio, hnbound, hP1⟩ :=
    answer_run_full_bound_of_boundedWhileDecider_main_run d x k cfg0 hRep0 hmem0 hcostle
  have hprog : (run k (compiledInputFullRAM d.p d.outReg (enc x))).program =
      fullProgram d.p d.outReg := by rw [run_program]; rfl
  obtain ⟨k2, n2, cfg2, hrun2, hRepr2, hio2, hk2pc, hk2reg, hn2bound, hP2⟩ :=
    answer_run_full_bound_of_boundedWhileDecider_epilogue d _ _ cfg hRepr hprog hkpc hP1
  obtain ⟨n3, Sg', hrun3, hSgReg, hSgMem, hSgScr, hSgIo, hn3bound⟩ :=
    answer_run_full_bound_of_boundedWhileDecider_cleanup d _ _ cfg2 hRepr2 hk2pc hP2
  refine ⟨n0 + n + n2 + n3, ⟨none, AllInstrState.canonical, Sg'⟩, ?_, rfl, rfl, hSgReg, hSgMem,
    hSgScr, ?_, ?_⟩
  · rw [flipBindPrologue_eq_flipBindG] at hrun0
    rw [show n0 + n + n2 + n3 = n3 + (n2 + (n + n0)) from by ring,
      Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      hrun0, hrun, hrun2, hrun3]
  · show Sg' Kg.io = _
    rw [hSgIo, hio2, hio, hio0, hk2reg]
    have hkmem' : (run k (compiledInputFullRAM d.p d.outReg (enc x))).mem =
        Program.eval d.p (bitInputStore (enc x)) := hkmem
    rw [hkmem']
  · exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hn0bound hnbound) hn2bound) hn3bound

end NPComplete.RAMToTM.Generic

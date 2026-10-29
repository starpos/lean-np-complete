module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiLayout
public import NPComplete.RAMToTM.Generic.Machine.GenericEmitMasterRam

/-!
# Wiring `fullProgramAbi` into the master RAM→prep path

`CallerAbiEpilogue`/`CallerAbiLayout` establish the RAM-level ABI epilogue, but the non-ABI
dispatcher (`Mg` over `fullProgram`) never executes `abiSuffix`. This file is the ABI-program
parallel of `GenericEmitMasterRam.master_ram_run_of_ramStop`: the TM runs `abiProgram` end-to-end,
reaching `Λg.cleanup CleanupPhase.checkHead` with the four ABI registers filled from
`outAddrCell`/`outLenCell` (`ram_run_to_cleanup_abi` below), leaving the existing single-bit decision
path's non-ABI cleanup (`Mg` over `fullProgram`) unchanged.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program Expr)
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits)

/-- The ABI program SSOT: main `d.p`, single-bit `outputLoad`, then the four-register ABI
    epilogue. -/
def abiProgram (p : Program) (outReg : ℕ) : List Instruction :=
  fullProgramAbi p outReg outAddrCell outLenCell

/-- Initial RAM state for `abiProgram`, mirroring `compiledInputFullRAM`. -/
def compiledInputAbiRAM (p : Program) (outReg : ℕ) (bits : Bits) : RAM :=
  { regs := emptyBank
    mem := bitInputStore bits
    pc := 0
    cost := 0
    program := abiProgram p outReg }

/-- `abiSuffix` is the six-instruction block naming `abiBase..abiBase+4`. -/
lemma abiSuffix_eq (p : Program) (addrCell lenCell : ℕ) :
    abiSuffix p addrCell lenCell =
      [Instruction.loadImm (abiBase p + 4) addrCell,
        Instruction.load (abiBase p) (abiBase p + 4),
        Instruction.loadImm (abiBase p + 4) lenCell,
        Instruction.load (abiBase p + 1) (abiBase p + 4),
        Instruction.loadImm (abiBase p + 2) 1,
        Instruction.loadImm (abiBase p + 3) 0] := by
  simp [abiSuffix, NPComplete.RAMToTM.compileExpr]

lemma abiBase_add_mem_abiSuffix (p : Program) (addrCell lenCell i : ℕ) (hi : i ≤ 4) :
    abiBase p + i ∈ (abiSuffix p addrCell lenCell).flatMap regsOf := by
  rw [abiSuffix_eq]
  match i with
  | 0 =>
      refine List.mem_flatMap.mpr ⟨Instruction.load (abiBase p) (abiBase p + 4), ?_, ?_⟩
      · simp
      · simp [regsOf]
  | 1 =>
      refine List.mem_flatMap.mpr
        ⟨Instruction.load (abiBase p + 1) (abiBase p + 4), ?_, ?_⟩
      · simp
      · simp [regsOf]
  | 2 =>
      refine List.mem_flatMap.mpr ⟨Instruction.loadImm (abiBase p + 2) 1, ?_, ?_⟩
      · simp
      · simp [regsOf]
  | 3 =>
      refine List.mem_flatMap.mpr ⟨Instruction.loadImm (abiBase p + 3) 0, ?_, ?_⟩
      · simp
      · simp [regsOf]
  | 4 =>
      refine List.mem_flatMap.mpr ⟨Instruction.loadImm (abiBase p + 4) addrCell, ?_, ?_⟩
      · simp
      · simp [regsOf]
  | n + 5 => omega

lemma abiBase_add_lt_regBound_abiProgram (p : Program) (outReg i : ℕ) (hi : i ≤ 4) :
    abiBase p + i < regBound (abiProgram p outReg) := by
  have hmemS := abiBase_add_mem_abiSuffix p outAddrCell outLenCell i hi
  have hmem : abiBase p + i ∈ (abiProgram p outReg).flatMap regsOf := by
    simp only [abiProgram, fullProgramAbi, List.flatMap_append, List.mem_append]
    exact Or.inr hmemS
  have hle := le_foldr_max_of_mem _ _ hmem
  simp only [regBound]; omega

/-- ABI register holding the output physical base address (`abiBase`). -/
def abiAddrReg (p : Program) (outReg : ℕ) : Fin (regBound (abiProgram p outReg)) :=
  ⟨abiBase p, abiBase_add_lt_regBound_abiProgram p outReg 0 (by omega)⟩

/-- ABI register holding the output bit length (`abiBase + 1`). -/
def abiLenReg (p : Program) (outReg : ℕ) : Fin (regBound (abiProgram p outReg)) :=
  ⟨abiBase p + 1, abiBase_add_lt_regBound_abiProgram p outReg 1 (by omega)⟩

/-- ABI register holding the constant `1` (`abiBase + 2`). -/
def abiOneReg (p : Program) (outReg : ℕ) : Fin (regBound (abiProgram p outReg)) :=
  ⟨abiBase p + 2, abiBase_add_lt_regBound_abiProgram p outReg 2 (by omega)⟩

/-- ABI register holding the constant `0` destination (`abiBase + 3`). -/
def abiDestReg (p : Program) (outReg : ℕ) : Fin (regBound (abiProgram p outReg)) :=
  ⟨abiBase p + 3, abiBase_add_lt_regBound_abiProgram p outReg 3 (by omega)⟩

/-- The `Mg` cleanup `outReg` parameter for the single-bit decision path: register `0` always
    exists (`regBound ≥ 1` via `outputLoad`'s own footprint, and `abiBase ≥ 2` forces still more).
    Master redirects at `checkHead`, so this value is never used as a real answer channel. -/
def masterOutRegAbi (p : Program) (outReg : ℕ) : Fin (regBound (abiProgram p outReg)) :=
  ⟨0, by
    have h := abiBase_add_lt_regBound_abiProgram p outReg 0 (by omega)
    have : 2 ≤ abiBase p := abiBase_ge_two p
    omega⟩

lemma segmentAt_abiProgram_compile (p : Program) (outReg : ℕ) :
    SegmentAt (abiProgram p outReg) 0 (compile p 0 0) := by
  refine ⟨[], outputLoad outReg ++ abiSuffix p outAddrCell outLenCell, ?_, rfl⟩
  simp [abiProgram, fullProgramAbi, fullProgram, List.append_assoc]

lemma segmentAt_abiProgram_outputLoad (p : Program) (outReg : ℕ) :
    SegmentAt (abiProgram p outReg) (codeLenP p) (outputLoad outReg) := by
  have h := segmentAt_fullProgramAbi_outputLoad p outReg outAddrCell outLenCell
  simpa [abiProgram] using h

lemma segmentAt_abiProgram_abiSuffix (p : Program) (outReg : ℕ) :
    SegmentAt (abiProgram p outReg) (codeLenP p + 2)
      (abiSuffix p outAddrCell outLenCell) := by
  have h := segmentAt_fullProgramAbi_abiSuffix p outReg outAddrCell outLenCell
  simpa [abiProgram] using h

lemma abiProgram_length (p : Program) (outReg : ℕ) :
    (abiProgram p outReg).length = codeLenP p + 8 := by
  simpa [abiProgram] using fullProgramAbi_length p outReg outAddrCell outLenCell

/-- Prologue on `abiProgram` lands representing `compiledInputAbiRAM`. -/
lemma represents_compiledInputAbiRAM_of_Mg (prog : Program) (dOutReg : ℕ)
    (mgReg : Fin (regBound (abiProgram prog dOutReg))) (bits : Bits) :
    ∃ n cfg, (flipBindPrologue (abiProgram prog dOutReg)
        (Mg (abiProgram prog dOutReg) (programSupported_any _) mgReg))^[n]
        (some ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
          initialSg (abiProgram prog dOutReg) bits⟩)
      = some cfg ∧ Represents (abiProgram prog dOutReg) cfg
        (compiledInputAbiRAM prog dOutReg bits) ∧
      (cfg.stk Kg.mem).length ≤ (bits.length + 1) * (2 * bitLen bits.length + 2) ∧
      cfg.stk Kg.io = [] ∧
      n ≤ bitLen bits.length + bits.length * (4 * bitLen bits.length + 10) + 3 := by
  obtain ⟨n, hrun, hn⟩ := prologue_run_of_Mg (abiProgram prog dOutReg) (programSupported_any _)
    mgReg bits AllInstrState.canonical (initialSg (abiProgram prog dOutReg) bits) rfl rfl rfl rfl
  refine ⟨n, _, hrun, ⟨rfl, ?_, ?_, rfl, ?_, rfl⟩, ?_, ?_, hn⟩
  · intro i
    rw [show (compiledInputAbiRAM prog dOutReg bits).regs i = 0 from rfl, natToDigits_zero]
    simp [Function.update, initialSg]
  · exact ⟨inputLogRev bits, rfl, lookupD_inputLogRev bits⟩
  · intro s
    cases s <;> simp [Function.update, initialSg]
  · exact encodeLog_inputLogRev_length_le bits
  · simp [Function.update]

/-- `Mg`-driven run of `abiProgram` reaches `Λg.cleanup CleanupPhase.checkHead` after main +
    `outputLoad` + `abiSuffix`, with ABI registers filled from the post-main memory cells. -/
lemma ram_run_to_cleanup_abi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    ∃ n cfg' k kEpi,
      (flipBindG (abiProgram d.p d.outReg)
          (Mg (abiProgram d.p d.outReg) (programSupported_any _)
            (masterOutRegAbi d.p d.outReg)))^[n]
        (some ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
          initialSg (abiProgram d.p d.outReg) (enc x)⟩) = some cfg' ∧
      cfg'.l = some (Λg.cleanup CleanupPhase.checkHead) ∧
      cfg'.stk Kg.io = [] ∧
      (run k (compiledInputAbiRAM d.p d.outReg (enc x))).pc = codeLenP d.p ∧
      (run k (compiledInputAbiRAM d.p d.outReg (enc x))).mem =
        Program.eval d.p (bitInputStore (enc x)) ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).pc =
        (abiProgram d.p d.outReg).length ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs (abiBase d.p) =
        (run k (compiledInputAbiRAM d.p d.outReg (enc x))).mem outAddrCell ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs (abiBase d.p + 1) =
        (run k (compiledInputAbiRAM d.p d.outReg (enc x))).mem outLenCell ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs (abiBase d.p + 2) = 1 ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs (abiBase d.p + 3) = 0 ∧
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).mem =
        (run k (compiledInputAbiRAM d.p d.outReg (enc x))).mem ∧
      Represents (abiProgram d.p d.outReg) cfg'
        (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))) := by
  set P := abiProgram d.p d.outReg with hP
  set oReg := masterOutRegAbi d.p d.outReg
  set R0 := compiledInputAbiRAM d.p d.outReg (enc x)
  obtain ⟨n0, cfg0, hrun0, hRep0, -, hio0, -⟩ :=
    represents_compiledInputAbiRAM_of_Mg d.p d.outReg oReg (enc x)
  obtain ⟨k, hkpc, hkmem, -, hprogk, -⟩ :=
    compile_exec d.p 0 R0 (by
      simpa [R0, compiledInputAbiRAM] using segmentAt_abiProgram_compile d.p d.outReg)
  have hkpc' : (run k R0).pc = codeLenP d.p := by
    have h0 : R0.pc = 0 := rfl
    rw [h0, zero_add] at hkpc
    exact hkpc
  obtain ⟨n, cfg, hrun, hRepr, hio, -⟩ :=
    boundedRunSim_of_programSupported P (programSupported_any _) oReg k cfg0 R0 hRep0
  set rr := run k R0 with hrr
  have hprr : rr.program = P := by
    rw [hrr, run_program]; rfl
  have hsegOL : SegmentAt rr.program rr.pc (outputLoad d.outReg) := by
    rw [hprr, hkpc']; exact segmentAt_abiProgram_outputLoad d.p d.outReg
  obtain ⟨k1, hpc1, hmem1, hprog1, hfr1⟩ := outputLoad_regs_frame d.outReg rr hsegOL
  have hpc1' : (run k1 rr).pc = codeLenP d.p + 2 := by
    rw [hpc1, hkpc']; simp [outputLoad, compileExpr]
  have hsegAS : SegmentAt (run k1 rr).program (run k1 rr).pc
      (abiSuffix d.p outAddrCell outLenCell) := by
    rw [hprog1, hprr, hpc1']; exact segmentAt_abiProgram_abiSuffix d.p d.outReg
  obtain ⟨k2, hpc2, hrAddr, hrLen, hrOne, hrDest, hfr2, hmem2, hprog2, -⟩ :=
    abiSuffix_exec d.p outAddrCell outLenCell (run k1 rr) hsegAS
  set kEpi := k1 + k2 with hkEpi
  have hrunEpi : run kEpi rr = run k2 (run k1 rr) := by
    rw [hkEpi, run_add]
  have hkEpiPc : (run kEpi rr).pc = P.length := by
    rw [hrunEpi, hpc2, hpc1', abiProgram_length, abiSuffix_length]
  have hrAddr' : (run kEpi rr).regs (abiBase d.p) = rr.mem outAddrCell := by
    rw [hrunEpi, hrAddr, hmem1]
  have hrLen' : (run kEpi rr).regs (abiBase d.p + 1) = rr.mem outLenCell := by
    rw [hrunEpi, hrLen, hmem1]
  have hrOne' : (run kEpi rr).regs (abiBase d.p + 2) = 1 := by
    rw [hrunEpi, hrOne]
  have hrDest' : (run kEpi rr).regs (abiBase d.p + 3) = 0 := by
    rw [hrunEpi, hrDest]
  have hmemEpi : (run kEpi rr).mem = rr.mem := by
    rw [hrunEpi, hmem2, hmem1]
  obtain ⟨n2, cfg2, hrun2, hRepr2, hio2, -⟩ :=
    boundedRunSim_of_programSupported P (programSupported_any _) oReg kEpi cfg rr hRepr
  have hcfg2l : cfg2.l = some (Λg.cleanup CleanupPhase.checkHead) := by
    have hctrl := hRepr2.2.2.2.2.2
    rw [ControlRep] at hctrl
    rw [hctrl, hkEpiPc, entryAt]
    simp
  have hioFinal : cfg2.stk Kg.io = [] := by
    rw [hio2, hio, hio0]
  refine ⟨n0 + n + n2, cfg2, k, kEpi, ?_, hcfg2l, hioFinal, hkpc', hkmem, ?_, hrAddr', hrLen',
    hrOne', hrDest', hmemEpi, hRepr2⟩
  · rw [flipBindPrologue_eq_flipBindG] at hrun0
    rw [show n0 + n + n2 = n2 + (n + n0) from by ring,
      Function.iterate_add_apply, Function.iterate_add_apply, hrun0, hrun, hrun2]
  · rw [hkEpiPc]

end NPComplete.RAMToTM.Generic

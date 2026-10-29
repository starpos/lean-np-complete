module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiLocality

/-!
# Quantitative `ram_run_to_cleanup_abi`

`ram_run_to_cleanup_abi` (`CallerAbiMasterRam.lean`) shows the ABI RAM run reaches cleanup, but its
own step count `n` is existential with no bound — `master_init_to_halt_abi` inherits that gap.
`ramRunToCleanupAbi_bound` closes it, mirroring `GenericDispatcher.lean`'s
`answer_run_full_bound_of_boundedWhileDecider` (prologue + main-with-growth + epilogue-with-growth
legs, summed via `Nat.add_le_add`) but stopping at `Λg.cleanup CleanupPhase.checkHead` instead of
running cleanup, and replacing `fullProgram`'s two-instruction `outputLoad` epilogue with
`abiProgram`'s eight-instruction `outputLoad ++ abiSuffix` epilogue.

The main-program leg reuses `GenericDispatcher.lean`'s `mem0Bound`/`costBound` verbatim;
no ABI-specific variant is needed.
`programImmediatesLe_abiProgram_of_full_program_bound` shows `abiProgram`'s own
immediate bound never exceeds `fullProgram`'s, since `abiSuffix`'s extra immediates
(`outAddrCell`/`outLenCell`/the ABI constants `1`/`0`) are all fixed small values dominated by
`bitLen d.outReg` (`bitLen` is always positive). Only the epilogue leg's cost-delta formula is new,
covering three `bitLen (rr.mem _)` unknowns (`d.outReg`/`outAddrCell`/`outLenCell`) instead of one.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program Expr)
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits)

/-- `Mg (abiProgram d.p d.outReg)`'s uniform site time-bound constant `C`. -/
def siteCsupAbi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : ℕ :=
  Finset.univ.sup (fun pc : Fin (abiProgram d.p d.outReg).length =>
    (siteTimedImpl (abiProgram d.p d.outReg) (programSupported_any _) pc).C)

/-- `Mg (abiProgram d.p d.outReg)`'s uniform site growth-bound constant `G`. -/
def siteGsupAbi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : ℕ :=
  Finset.univ.sup (fun pc : Fin (abiProgram d.p d.outReg).length =>
    (siteTimedImpl (abiProgram d.p d.outReg) (programSupported_any _) pc).G)

/-- `abiProgram`'s `loadImm` immediates are within `fullProgram`'s own bound `max (programImmBound
    d.p) (bitLen d.outReg)`: `outAddrCell`/`outLenCell` are the fixed constants `0`/`1`, and
    `bitLen` is always positive, so `abiSuffix`'s own extra immediates never widen the bound. -/
lemma programImmediatesLe_abiProgram_of_full_program_bound (p : Program) (outReg : ℕ) :
    ProgramImmediatesLe (max (programImmBound p) (bitLen outReg)) (abiProgram p outReg) := by
  refine ProgramImmediatesLe.mono ?_ (programImmediatesLe_abiProgram p outReg)
  simp only [outAddrCell, outLenCell, bitLen_zero, bitLen_one]
  have := bitLen_pos outReg
  omega

/-- A closed-form bound (in terms of `d`/`x` alone) on `regSize` right after
    `ramRunToCleanupAbi_bound`'s run lands at cleanup — needed as the `CallerContract`
    register-content digit-length bound `M` a caller (`master_init_to_halt_abi_bound`)
    supplies to `master_run_bound_of_callerContract`. -/
def regSizeBoundAbi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  mem0Bound d x + 2 * siteGsupAbi d * costBound d x +
    2 * siteGsupAbi d *
      (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
        bitLen 1 + bitLen 0 +
        12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11)

/-- The compiled main program's ABI RAM run reaches PC `codeLenP d.p` (the main-program/epilogue
    boundary), with `mem` equal to `Program.eval` and accumulated cost within `costBound`;
    this is the semantic half of the main leg. -/
lemma ramRunToCleanupAbi_bound_main_cost {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (x : α) (hx : D x) :
    ∃ k, (run k (compiledInputAbiRAM d.p d.outReg (enc x))).pc = codeLenP d.p ∧
      (run k (compiledInputAbiRAM d.p d.outReg (enc x))).mem =
        Program.eval d.p (bitInputStore (enc x)) ∧
      (run k (compiledInputAbiRAM d.p d.outReg (enc x))).cost ≤ costBound d x := by
  obtain ⟨k, hkpc, hkmem, -, -, hkle3, hcost⟩ :=
    compile_exec_cost d.p 0 (compiledInputAbiRAM d.p d.outReg (enc x))
      (max (programImmBound d.p) (bitLen d.outReg))
      (segmentAt_abiProgram_compile d.p d.outReg)
      (programImmediatesLe_abiProgram_of_full_program_bound d.p d.outReg)
  obtain ⟨W, hWle, hDyn⟩ := d.compiled_operands_le x hx
  have hkbudget : k ≤ 8 * d.p.cost (compiledInputAbiRAM d.p d.outReg (enc x)).mem := by omega
  have hcost0 : (compiledInputAbiRAM d.p d.outReg (enc x)).cost = 0 := rfl
  have hkpc' : (run k (compiledInputAbiRAM d.p d.outReg (enc x))).pc = codeLenP d.p := by
    have h0 : (compiledInputAbiRAM d.p d.outReg (enc x)).pc = 0 := rfl
    rw [h0, zero_add] at hkpc
    exact hkpc
  have hDynFull : RunDynLe W k (compiledInputAbiRAM d.p d.outReg (enc x)) :=
    runDynLe_bare_to_abi d.p d.outReg (enc x) W k hkpc' (hDyn k hkbudget)
  refine ⟨k, hkpc', hkmem, ?_⟩
  calc (run k (compiledInputAbiRAM d.p d.outReg (enc x))).cost
      ≤ (compiledInputAbiRAM d.p d.outReg (enc x)).cost +
          8 * d.p.cost (compiledInputAbiRAM d.p d.outReg (enc x)).mem *
            (2 * max W (max (programImmBound d.p) (bitLen d.outReg)) + 1) :=
        hcost W hDynFull
    _ ≤ 8 * (d.c * ((enc x).length + 1) ^ d.c) *
          (2 * max (d.bit_c * ((enc x).length + 1) ^ d.bit_c)
            (max (programImmBound d.p) (bitLen d.outReg)) + 1) := by
        rw [hcost0, zero_add]
        gcongr
        exact d.cost_le x hx
    _ = costBound d x := by unfold costBound; ring

/-- Simulates the main leg on the TM: the dispatcher reaches a configuration representing the
    RAM after `k` steps, within the cubic step bound and with the register/memory-log potential
    bounded by `mem0Bound` and `costBound`. -/
lemma ramRunToCleanupAbi_bound_main_run {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (x : α) (k : ℕ)
    (cfg0 : Turing.TM2.Cfg (Γg (abiProgram d.p d.outReg)) (Λg (abiProgram d.p d.outReg))
      AllInstrState)
    (hRep0 : Represents (abiProgram d.p d.outReg) cfg0
      (compiledInputAbiRAM d.p d.outReg (enc x)))
    (hmem0 : (cfg0.stk Kg.mem).length ≤ mem0Bound d x)
    (hcostle : (run k (compiledInputAbiRAM d.p d.outReg (enc x))).cost ≤ costBound d x) :
    ∃ n cfg, (flipBindG (abiProgram d.p d.outReg)
        (Mg (abiProgram d.p d.outReg) (programSupported_any _)
          (masterOutRegAbi d.p d.outReg)))^[n] (some cfg0) = some cfg ∧
      Represents (abiProgram d.p d.outReg) cfg (run k (compiledInputAbiRAM d.p d.outReg (enc x))) ∧
      cfg.stk Kg.io = cfg0.stk Kg.io ∧
      n ≤ siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 ∧
      regSize (abiProgram d.p d.outReg) (run k (compiledInputAbiRAM d.p d.outReg (enc x))) +
          (cfg.stk Kg.mem).length ≤ mem0Bound d x + 2 * siteGsupAbi d * costBound d x := by
  have hcost0 : (compiledInputAbiRAM d.p d.outReg (enc x)).cost = 0 := rfl
  have hRegSize : regSize (abiProgram d.p d.outReg) (compiledInputAbiRAM d.p d.outReg (enc x))
      = 0 := by
    simp [regSize, compiledInputAbiRAM, emptyBank, natToDigits_zero]
  obtain ⟨n, cfg, hrun, hRepr, hio, hnbound, hgrowth⟩ :=
    boundedRunSimWithGrowth_of_programSupported (abiProgram d.p d.outReg)
      (programSupported_any _) (masterOutRegAbi d.p d.outReg) k cfg0
      (compiledInputAbiRAM d.p d.outReg (enc x)) hRep0
  rw [hRegSize, hcost0, Nat.sub_zero] at hnbound hgrowth
  refine ⟨n, cfg, hrun, hRepr, hio, ?_, ?_⟩
  · rw [zero_add] at hnbound
    refine hnbound.trans ?_
    unfold siteCsupAbi siteGsupAbi
    gcongr
  · refine hgrowth.trans ?_
    unfold siteGsupAbi
    gcongr
    simpa using hmem0


/-- Simulates the eight-instruction ABI epilogue (`outputLoad ++ abiSuffix`) on the TM from a
    potential bound `B`, exposing the ABI register contents and the landing PC. -/
lemma ramRunToCleanupAbi_bound_epilogue {α : Type} {enc : α → Bits}
    {D L : α → Prop} (d : BoundedWhileDecider enc D L) (B : ℕ) (rr : RAM)
    (cfg : Turing.TM2.Cfg (Γg (abiProgram d.p d.outReg)) (Λg (abiProgram d.p d.outReg))
      AllInstrState)
    (hRepr : Represents (abiProgram d.p d.outReg) cfg rr)
    (hprog : rr.program = abiProgram d.p d.outReg) (hpc : rr.pc = codeLenP d.p)
    (hB : regSize (abiProgram d.p d.outReg) rr + (cfg.stk Kg.mem).length ≤ B) :
    ∃ kEpi n2 cfg2, (flipBindG (abiProgram d.p d.outReg)
        (Mg (abiProgram d.p d.outReg) (programSupported_any _)
          (masterOutRegAbi d.p d.outReg)))^[n2] (some cfg) = some cfg2 ∧
      Represents (abiProgram d.p d.outReg) cfg2 (run kEpi rr) ∧
      cfg2.stk Kg.io = cfg.stk Kg.io ∧
      (run kEpi rr).pc = (abiProgram d.p d.outReg).length ∧
      (run kEpi rr).regs (abiBase d.p) = rr.mem outAddrCell ∧
      (run kEpi rr).regs (abiBase d.p + 1) = rr.mem outLenCell ∧
      (run kEpi rr).regs (abiBase d.p + 2) = 1 ∧
      (run kEpi rr).regs (abiBase d.p + 3) = 0 ∧
      (run kEpi rr).mem = rr.mem ∧
      n2 ≤ siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
        (B + (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
          bitLen 1 + bitLen 0 + 12 * B + 11) + 1) ^ 3 ∧
      regSize (abiProgram d.p d.outReg) (run kEpi rr) + (cfg2.stk Kg.mem).length ≤
        B + 2 * siteGsupAbi d * (2 * bitLen d.outReg + 2 * bitLen outAddrCell +
          2 * bitLen outLenCell + bitLen 1 + bitLen 0 + 12 * B + 11) := by
  have hsegOL : SegmentAt rr.program rr.pc (outputLoad d.outReg) := by
    rw [hprog, hpc]; exact segmentAt_abiProgram_outputLoad d.p d.outReg
  obtain ⟨k1, hk1pc, hk1reg, hk1mem, hk1prog, hk1le, hk1cost⟩ :=
    outputLoad_exec_cost d.outReg rr hsegOL
  have hk1pc' : (run k1 rr).pc = codeLenP d.p + 2 := by
    rw [hk1pc, hpc]; simp [outputLoad, compileExpr]
  have hsegAS : SegmentAt (run k1 rr).program (run k1 rr).pc
      (abiSuffix d.p outAddrCell outLenCell) := by
    rw [hk1prog, hprog, hk1pc']; exact segmentAt_abiProgram_abiSuffix d.p d.outReg
  obtain ⟨k2, hk2pc, hk2rAddr, hk2rLen, hk2rOne, hk2rDest, hk2fr, hk2mem, hk2prog, hk2le,
    hk2cost⟩ := abiSuffix_exec_cost d.p outAddrCell outLenCell (run k1 rr) hsegAS
  have hrunEpi : run (k1 + k2) rr = run k2 (run k1 rr) := by rw [run_add]
  have hdelta : (run (k1 + k2) rr).cost - rr.cost ≤
      2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
        bitLen 1 + bitLen 0 + 12 * B + 11 := by
    have hb1 := bitLen_mem_le_of_represents _ cfg rr hRepr d.outReg
    have hb2 := bitLen_mem_le_of_represents _ cfg rr hRepr outAddrCell
    have hb3 := bitLen_mem_le_of_represents _ cfg rr hRepr outLenCell
    rw [hrunEpi, hk2cost, hk1cost, hk1mem]
    omega
  obtain ⟨n2, cfg2, hrun2, hRepr2, hio2, hn2bound, hgrowth2⟩ :=
    boundedRunSimWithGrowth_of_programSupported (abiProgram d.p d.outReg)
      (programSupported_any _) (masterOutRegAbi d.p d.outReg) (k1 + k2) cfg rr hRepr
  refine ⟨k1 + k2, n2, cfg2, hrun2, hRepr2, hio2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrunEpi, hk2pc, hk1pc', abiProgram_length, abiSuffix_length]
  · rw [hrunEpi, hk2rAddr, hk1mem]
  · rw [hrunEpi, hk2rLen, hk1mem]
  · rw [hrunEpi, hk2rOne]
  · rw [hrunEpi, hk2rDest]
  · rw [hrunEpi, hk2mem, hk1mem]
  · refine hn2bound.trans ?_
    unfold siteCsupAbi siteGsupAbi
    gcongr
  · refine hgrowth2.trans ?_
    unfold siteGsupAbi
    gcongr

/-- `ram_run_to_cleanup_abi`'s step-count-exposing companion: the same run, plus (a) a polynomial (in
    `(enc x).length`, treating `d.c`/`d.bit_c`/`programImmBound d.p`/`bitLen d.outReg`/`Mg`'s ABI
    site constants as fixed constants of `d`) bound on the total step count `n`, and (b) a bound
    on the final `regSize` (needed to supply `CallerContract`'s `M`). No attempt is made at a
    tight closed form: each leg's bound is simply summed/composed. -/
lemma ramRunToCleanupAbi_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (hx : D x) :
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
         (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))) ∧
       regSize (abiProgram d.p d.outReg)
         (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))) ≤ regSizeBoundAbi d x ∧
       regSize (abiProgram d.p d.outReg)
           (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))) +
           (cfg'.stk Kg.mem).length ≤ regSizeBoundAbi d x ∧
       n ≤ (bitLen (enc x).length + (enc x).length * (4 * bitLen (enc x).length + 10) + 3) +
        siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 +
        siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
          (mem0Bound d x + 2 * siteGsupAbi d * costBound d x +
            (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
              bitLen 1 + bitLen 0 +
              12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11) + 1) ^ 3 := by
  obtain ⟨n0, cfg0, hrun0, hRep0, hmem0, hio0, hn0bound⟩ :=
    represents_compiledInputAbiRAM_of_Mg d.p d.outReg (masterOutRegAbi d.p d.outReg) (enc x)
  obtain ⟨k, hkpc, hkmem, hcostle⟩ := ramRunToCleanupAbi_bound_main_cost d x hx
  obtain ⟨n, cfg, hrun, hRepr, hio, hnbound, hP1⟩ :=
    ramRunToCleanupAbi_bound_main_run d x k cfg0 hRep0 hmem0 hcostle
  have hprog : (run k (compiledInputAbiRAM d.p d.outReg (enc x))).program =
      abiProgram d.p d.outReg := by rw [run_program]; rfl
  obtain ⟨kEpi, n2, cfg2, hrun2, hRepr2, hio2, hkEpiPc, hrAddr, hrLen, hrOne, hrDest, hmemEpi,
    hn2bound, hP2⟩ := ramRunToCleanupAbi_bound_epilogue d _ _ cfg hRepr hprog hkpc hP1
  have hcfg2l : cfg2.l = some (Λg.cleanup CleanupPhase.checkHead) := by
    have hctrl := hRepr2.2.2.2.2.2
    rw [ControlRep] at hctrl
    rw [hctrl, hkEpiPc, entryAt]
    simp
  have hP2combined : regSize (abiProgram d.p d.outReg)
      (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))) +
      (cfg2.stk Kg.mem).length ≤ regSizeBoundAbi d x := hP2
  refine ⟨n0 + n + n2, cfg2, k, kEpi, ?_, hcfg2l, by rw [hio2, hio, hio0], hkpc, hkmem, hkEpiPc,
    hrAddr, hrLen, hrOne, hrDest, hmemEpi, hRepr2, le_trans (Nat.le_add_right _ _) hP2combined,
    hP2combined, ?_⟩
  · rw [flipBindPrologue_eq_flipBindG] at hrun0
    rw [show n0 + n + n2 = n2 + (n + n0) from by ring,
      Function.iterate_add_apply, Function.iterate_add_apply, hrun0, hrun, hrun2]
  · exact Nat.add_le_add (Nat.add_le_add hn0bound hnbound) hn2bound

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiMasterRam
public import NPComplete.RAMToTM.Generic.Machine.CallerContract

/-!
# Building `CallerContract` from the ABI master RAM landing

`ram_run_to_cleanup_abi` (`CallerAbiMasterRam.lean`) lands at `Λg.cleanup CleanupPhase.checkHead`.
This module lifts that state to the master's canonical prep landing, constructs `CallerContract`
from a `ReductionOutput` postcondition on the post-main memory, and composes the resulting
hypothesis with `master_run_to_halt` to prove initialization-to-halt correctness.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program)
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits)

variable {p : List Instruction}

lemma abiAddrReg_ne_abiLenReg (prog : Program) (outReg : ℕ) :
    abiAddrReg prog outReg ≠ abiLenReg prog outReg := by
  intro h
  have : abiBase prog = abiBase prog + 1 := congrArg Fin.val h
  omega

lemma abiDestReg_ne_abiLenReg (prog : Program) (outReg : ℕ) :
    abiDestReg prog outReg ≠ abiLenReg prog outReg := by
  intro h
  have : abiBase prog + 3 = abiBase prog + 1 := congrArg Fin.val h
  omega

lemma abiDestReg_ne_abiAddrReg (prog : Program) (outReg : ℕ) :
    abiDestReg prog outReg ≠ abiAddrReg prog outReg := by
  intro h
  have : abiBase prog + 3 = abiBase prog := congrArg Fin.val h
  omega

lemma abiOneReg_ne_abiLenReg (prog : Program) (outReg : ℕ) :
    abiOneReg prog outReg ≠ abiLenReg prog outReg := by
  intro h
  have : abiBase prog + 2 = abiBase prog + 1 := congrArg Fin.val h
  omega

lemma abiOneReg_ne_abiAddrReg (prog : Program) (outReg : ℕ) :
    abiOneReg prog outReg ≠ abiAddrReg prog outReg := by
  intro h
  have : abiBase prog + 2 = abiBase prog := congrArg Fin.val h
  omega

lemma abiOneReg_ne_abiDestReg (prog : Program) (outReg : ℕ) :
    abiOneReg prog outReg ≠ abiDestReg prog outReg := by
  intro h
  have : abiBase prog + 2 = abiBase prog + 3 := congrArg Fin.val h
  omega

/-- Uniform digit-length cap for every register value in `regs`. -/
noncomputable def regsDigitBound {n : ℕ} (regs : Fin n → ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin n => (natToDigits (regs i)).length)

lemma le_regsDigitBound {n : ℕ} (regs : Fin n → ℕ) (i : Fin n) :
    (natToDigits (regs i)).length ≤ regsDigitBound regs :=
  Finset.le_sup (f := fun j : Fin n => (natToDigits (regs j)).length) (Finset.mem_univ i)

/-- `CallerContract` adapter for the correctness (bound-free) master run. -/
lemma master_run_to_halt_of_callerContract (hSup : ProgramSupported p)
    (oReg rAddr rDest rOne rLen : Fin (regBound p))
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ) (M : ℕ)
    (cc : CallerContract rAddr rDest rOne rLen sf0 Sg0 n addr log regs0 M) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
      = some ⟨none, sf, Sgf⟩
      ∧ Sgf EmitK.out = (OutputSlice.physicalBits log ⟨addr, n⟩).reverse :=
  master_run_to_halt hSup oReg rAddr rDest rOne rLen cc.one_ne_len cc.addr_ne_len
    cc.dest_ne_len cc.dest_ne_addr cc.one_ne_addr cc.one_ne_dest n addr log regs0 sf0 Sg0
    cc.prep_canonical cc.len_eq cc.addr_eq cc.one_eq cc.dest_eq cc.other_regs_eq cc.mem_eq
    cc.countdown_empty cc.out_empty cc.work_rev_empty cc.copy_scratch_empty cc.lhs_operand_empty
    cc.rhs_operand_empty cc.diff_scratch_empty cc.query_empty cc.query_tmp_empty cc.log_tmp_empty
    cc.sum_scratch_empty cc.prologue_counter_empty cc.prologue_work_empty cc.io_empty cc.bit_valid

/-- Lifts the ABI RAM run that lands at cleanup into the master machine: the master reaches
    `prep.checkLen` after `nRam + 1` steps, with every base stack equal to the RAM run's. -/
lemma master_init_to_halt_abi_landing {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (nRam : ℕ)
    (cfg' : Turing.TM2.Cfg (Γg (abiProgram d.p d.outReg)) (Λg (abiProgram d.p d.outReg))
      AllInstrState)
    (hrunMg : (flipBindG (abiProgram d.p d.outReg)
          (Mg (abiProgram d.p d.outReg) (programSupported_any _)
            (masterOutRegAbi d.p d.outReg)))^[nRam]
        (some ⟨some (Λg.prologue .scanInput), AllInstrState.canonical,
          initialSg (abiProgram d.p d.outReg) (enc x)⟩) = some cfg')
    (hfinal : cfg'.l = some (Λg.cleanup CleanupPhase.checkHead)) :
    ∃ (sf0 : MasterState (abiProgram d.p d.outReg))
      (Sg0 : ∀ k, List (EmitΓ (abiProgram d.p d.outReg) k)),
      (master_flipBind (programSupported_any _) (masterOutRegAbi d.p d.outReg)
          (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
          (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg))^[nRam + 1]
        (some ⟨some (MasterΛ.ram (Λg.prologue .scanInput)), MasterState.canonical,
          initialMasterSg (initialSg (abiProgram d.p d.outReg) (enc x))⟩)
        = some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩ ∧
      sf0.prep = PrepState.canonical ∧
      (∀ kg, Sg0 (EmitK.base kg) = cfg'.stk kg) ∧
      Sg0 EmitK.countdown = ([] : List Unit) ∧ Sg0 EmitK.out = [] := by
  have hl₀ : (Λg.prologue ProloguePhase.scanInput : Λg (abiProgram d.p d.outReg)) ≠
      Λg.cleanup CleanupPhase.checkHead := by simp
  have hswap := ramStop_iterate_eq_of_mg_landing (programSupported_any _)
    (masterOutRegAbi d.p d.outReg) nRam (Λg.prologue .scanInput) hl₀ AllInstrState.canonical
    (initialSg (abiProgram d.p d.outReg) (enc x)) cfg' hrunMg hfinal
  have hcfg'eta : cfg' = ⟨some (Λg.cleanup CleanupPhase.checkHead), cfg'.var, cfg'.stk⟩ := by
    cases cfg' with | mk l var stk => simp_all
  rw [hcfg'eta] at hswap
  obtain ⟨sfRam, SgfRam, hrunRam, -, hSgfBase, hSgfFrame⟩ :=
    master_ram_run_of_ramStop (programSupported_any _) (masterOutRegAbi d.p d.outReg)
      (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg) (abiOneReg d.p d.outReg)
      (abiLenReg d.p d.outReg) (Λg.prologue .scanInput)
      (initialSg (abiProgram d.p d.outReg) (enc x)) nRam cfg'.var cfg'.stk hswap
  have hrunPrep := master_flipBind_ram_checkHead (programSupported_any _)
    (masterOutRegAbi d.p d.outReg) (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
    (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg) sfRam SgfRam
  refine ⟨MasterState.setPrep sfRam PrepState.canonical, SgfRam, ?_, rfl, ?_, ?_, ?_⟩
  · rw [Function.iterate_succ_apply', hrunRam, hrunPrep]
  · intro kg
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id] using hSgfBase kg
  · have hfr := hSgfFrame EmitK.countdown (by intro kl; cases kl <;> simp)
    simpa [initialMasterSg] using hfr
  · have hfr := hSgfFrame EmitK.out (by intro kl; cases kl <;> simp)
    simpa [initialMasterSg] using hfr

/-- Every cell of the emitted range holds a bit, transported from `ReductionOutput` through the
    write-log's lookup function. -/
lemma master_init_to_halt_abi_bit_valid {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (outputBase outputLength : ℕ)
    (hOut : ReductionOutput (Program.eval d.p (bitInputStore (enc x))) outputBase outputLength)
    (log : WriteLog)
    (hlook : (fun a => lookupD log a 0) = Program.eval d.p (bitInputStore (enc x))) :
    ∀ i < outputLength,
      lookupD log (outputBase + i) 0 = 0 ∨ lookupD log (outputBase + i) 0 = 1 := by
  intro i hi
  have h := congrFun hlook (outputBase + i)
  rw [h]
  exact hOut.bits_valid i hi

/-- Builds the `CallerContract` for the master's prep phase from the ABI RAM run's final
    state, for any digit-length cap `M` covering the registers and the output range end. -/
lemma master_init_to_halt_abi_contract {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (outputBase outputLength : ℕ)
    (hOut : ReductionOutput (Program.eval d.p (bitInputStore (enc x))) outputBase outputLength)
    (cfg' : Turing.TM2.Cfg (Γg (abiProgram d.p d.outReg)) (Λg (abiProgram d.p d.outReg))
      AllInstrState)
    (rFinal : RAM) (sf0 : MasterState (abiProgram d.p d.outReg))
    (Sg0 : ∀ k, List (EmitΓ (abiProgram d.p d.outReg) k))
    (hRepr : Represents (abiProgram d.p d.outReg) cfg' rFinal)
    (hmem : rFinal.mem = Program.eval d.p (bitInputStore (enc x)))
    (hrAddr : rFinal.regs (abiBase d.p) = outputBase)
    (hrLen : rFinal.regs (abiBase d.p + 1) = outputLength)
    (hrOne : rFinal.regs (abiBase d.p + 2) = 1) (hrDest : rFinal.regs (abiBase d.p + 3) = 0)
    (hio : cfg'.stk Kg.io = [])
    (hprep : sf0.prep = PrepState.canonical)
    (hSgBase : ∀ kg, Sg0 (EmitK.base kg) = cfg'.stk kg)
    (hcd : Sg0 EmitK.countdown = ([] : List Unit)) (hout : Sg0 EmitK.out = [])
    (M : ℕ)
    (hMregs : ∀ i : Fin (regBound (abiProgram d.p d.outReg)),
      (natToDigits (rFinal.regs i)).length ≤ M)
    (hMaddr : (natToDigits (outputBase + outputLength)).length ≤ M) :
    ∃ log, CallerContract (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
        (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg) sf0 Sg0 outputLength outputBase log
        (fun i => rFinal.regs i) M ∧
      (encodeLog log).length = (cfg'.stk Kg.mem).length ∧
      (fun a => lookupD log a 0) = Program.eval d.p (bitInputStore (enc x)) := by
  obtain ⟨-, hRegF, hMemF, -, hScrF, -⟩ := hRepr
  obtain ⟨log, hlogEnc, hlogLookup⟩ := hMemF
  have hlogLookup' : (fun a => lookupD log a 0) = Program.eval d.p (bitInputStore (enc x)) := by
    funext a
    rw [hlogLookup a, hmem]
  have hRegSg (i : Fin (regBound (abiProgram d.p d.outReg))) :
      Sg0 (EmitK.base (Kg.reg i)) = natToDigits (rFinal.regs i) := by
    rw [hSgBase, hRegF i]
  have hscr (sk : ScratchKind) : Sg0 (EmitK.base (Kg.scratch sk)) = [] := by
    rw [hSgBase, hScrF sk]
  refine ⟨log, ?_, by rw [hlogEnc], hlogLookup'⟩
  exact
    { one_ne_len := abiOneReg_ne_abiLenReg d.p d.outReg
      addr_ne_len := abiAddrReg_ne_abiLenReg d.p d.outReg
      dest_ne_len := abiDestReg_ne_abiLenReg d.p d.outReg
      dest_ne_addr := abiDestReg_ne_abiAddrReg d.p d.outReg
      one_ne_addr := abiOneReg_ne_abiAddrReg d.p d.outReg
      one_ne_dest := abiOneReg_ne_abiDestReg d.p d.outReg
      regs0_len_le := hMregs
      addr_n_len_le := hMaddr
      prep_canonical := hprep
      len_eq := by
        rw [hRegSg]
        simp only [abiLenReg, Fin.val_mk]
        rw [hrLen]
      addr_eq := by
        rw [hRegSg]
        simp only [abiAddrReg, Fin.val_mk]
        rw [hrAddr]
      one_eq := by
        rw [hRegSg]
        simp only [abiOneReg, Fin.val_mk]
        rw [hrOne]
      dest_eq := by
        rw [hRegSg]
        simp only [abiDestReg, Fin.val_mk]
        rw [hrDest, natToDigits_zero]
      other_regs_eq := fun i _ _ _ => hRegSg i
      mem_eq := by rw [hSgBase, hlogEnc]
      countdown_empty := hcd
      out_empty := hout
      work_rev_empty := hscr .workRev
      copy_scratch_empty := hscr .copyScratch
      lhs_operand_empty := hscr .lhsOperand
      rhs_operand_empty := hscr .rhsOperand
      diff_scratch_empty := hscr .diffScratch
      query_empty := hscr .query
      query_tmp_empty := hscr .queryTmp
      log_tmp_empty := hscr .logTmp
      sum_scratch_empty := hscr .sumScratch
      prologue_counter_empty := hscr .prologueCounter
      prologue_work_empty := hscr .prologueWork
      io_empty := by rw [hSgBase, hio]
      bit_valid := master_init_to_halt_abi_bit_valid d x outputBase outputLength hOut log
        hlogLookup' }

/-- From the ABI master start config, under `ReductionOutput` on the post-main memory, the run
    reaches a genuine halt whose `out` stream is the physical bits of that output range. -/
lemma master_init_to_halt_abi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ)
    (hOut : ReductionOutput (Program.eval d.p (bitInputStore (enc x)))
      outputBase outputLength) :
    ∃ nTotal sf Sgf log,
      (master_flipBind (programSupported_any _)
          (masterOutRegAbi d.p d.outReg)
          (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
          (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg))^[nTotal]
        (some ⟨some (MasterΛ.ram (Λg.prologue .scanInput)), MasterState.canonical,
          initialMasterSg (initialSg (abiProgram d.p d.outReg) (enc x))⟩)
      = some ⟨none, sf, Sgf⟩
      ∧ Sgf EmitK.out =
          (OutputSlice.physicalBits log ⟨outputBase, outputLength⟩).reverse := by
  obtain ⟨nRam, cfg', k, kEpi, hrunMg, hfinal, hioFinal, hkpc, hkmem, hkEpiPc,
    hrAddr, hrLen, hrOne, hrDest, hmemEpi, hRepr⟩ := ram_run_to_cleanup_abi d x
  obtain ⟨sf0, Sg0, hrunToPrep, hprep, hSgBase, hcd, houtE⟩ :=
    master_init_to_halt_abi_landing d x nRam cfg' hrunMg hfinal
  have hmemF : (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).mem =
      Program.eval d.p (bitInputStore (enc x)) := by rw [hmemEpi, hkmem]
  obtain ⟨log, cc, -, -⟩ :=
    master_init_to_halt_abi_contract d x outputBase outputLength hOut cfg' _ sf0 Sg0 hRepr
      hmemF (by rw [hrAddr, hkmem, hOut.addr_eq]) (by rw [hrLen, hkmem, hOut.len_eq]) hrOne hrDest
      hioFinal hprep hSgBase hcd houtE
      (max (regsDigitBound fun i : Fin (regBound (abiProgram d.p d.outReg)) =>
        (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs i)
        (natToDigits (outputBase + outputLength)).length)
      (fun i => le_trans (le_regsDigitBound (fun j : Fin (regBound (abiProgram d.p d.outReg)) =>
        (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).regs j) i)
        (le_max_left _ _)) (le_max_right _ _)
  obtain ⟨nHalt, sfHalt, SgfHalt, hrunHalt, houtHalt⟩ :=
    master_run_to_halt_of_callerContract (programSupported_any _) (masterOutRegAbi d.p d.outReg)
      (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg) (abiOneReg d.p d.outReg)
      (abiLenReg d.p d.outReg) sf0 Sg0 outputLength outputBase log _ _ cc
  refine ⟨nRam + 1 + nHalt, sfHalt, SgfHalt, log, ?_, houtHalt⟩
  rw [show nRam + 1 + nHalt = nHalt + (nRam + 1) from by omega,
    Function.iterate_add_apply, hrunToPrep, hrunHalt]

end NPComplete.RAMToTM.Generic

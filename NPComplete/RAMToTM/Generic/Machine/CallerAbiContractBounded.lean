module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiContract
public import NPComplete.RAMToTM.Generic.Machine.CallerAbiMasterRamBounded

/-!
# Bound for the ABI master path

A caller's ABI machine must carry the RAM result through the master's preparation
and cleanup phases without losing output or register bounds. These lemmas
assemble the landing, output-bit, and register-content facts needed to derive a
total step bound for that path.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program)
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits)

/-- Builds the `CallerContract` for the master's prep phase from the ABI RAM run's final
    state, together with the write-log bound and lookup agreement; `M` is the `regSize` bound. -/
lemma master_init_to_halt_abi_bound_contract {α : Type} {enc : α → Bits} {D L : α → Prop}
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
    (hregSize : regSize (abiProgram d.p d.outReg) rFinal ≤ regSizeBoundAbi d x)
    (hregMem : regSize (abiProgram d.p d.outReg) rFinal + (cfg'.stk Kg.mem).length ≤
      regSizeBoundAbi d x)
    (hio : cfg'.stk Kg.io = [])
    (hprep : sf0.prep = PrepState.canonical)
    (hSgBase : ∀ kg, Sg0 (EmitK.base kg) = cfg'.stk kg)
    (hcd : Sg0 EmitK.countdown = ([] : List Unit)) (hout : Sg0 EmitK.out = []) :
    ∃ log, CallerContract (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
        (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg) sf0 Sg0 outputLength outputBase log
        (fun i => rFinal.regs i)
        (max (regSizeBoundAbi d x) (natToDigits (outputBase + outputLength)).length) ∧
      (encodeLog log).length ≤ regSizeBoundAbi d x ∧
      (fun a => lookupD log a 0) = Program.eval d.p (bitInputStore (enc x)) := by
  obtain ⟨log, cc, hlogLen, hlook⟩ :=
    master_init_to_halt_abi_contract d x outputBase outputLength hOut cfg' rFinal sf0 Sg0 hRepr
      hmem hrAddr hrLen hrOne hrDest hio hprep hSgBase hcd hout
      (max (regSizeBoundAbi d x) (natToDigits (outputBase + outputLength)).length)
      (fun i => le_trans (le_trans (natToDigits_length_le_regSize _ rFinal i) hregSize)
        (le_max_left _ _))
      (le_max_right _ _)
  exact ⟨log, cc, hlogLen ▸ le_trans (Nat.le_add_left _ _) hregMem, hlook⟩

/-- `master_init_to_halt_abi`'s step-count-exposing companion: the same run, plus a polynomial (in
    `(enc x).length`/`outputBase`/`outputLength`, treating `d`'s own constants and `Mg`'s ABI site
    constants as fixed) bound on the total step count `nTotal`. No attempt is made at a tight
    closed form: `nRam`'s bound (`ramRunToCleanupAbi_bound`) and `nHalt`'s bound
    (`master_run_bound_of_callerContract`) are simply summed. -/
lemma master_init_to_halt_abi_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) (hx : D x)
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
        ∧ sf = MasterState.canonical
        ∧ Sgf EmitK.out =
           (OutputSlice.physicalBits log ⟨outputBase, outputLength⟩).reverse
       ∧ (∀ i : Fin (regBound (abiProgram d.p d.outReg)),
           Sgf (EmitK.base (Kg.reg i)) = [])
       ∧ Sgf (EmitK.base Kg.mem) = []
       ∧ (∀ sk : ScratchKind, Sgf (EmitK.base (Kg.scratch sk)) = [])
       ∧ Sgf (EmitK.base Kg.io) = []
       ∧ Sgf EmitK.countdown = []
       ∧ (encodeLog log).length ≤ regSizeBoundAbi d x
       ∧ (fun a => lookupD log a 0) =
           Program.eval d.p (bitInputStore (enc x))
       ∧ nTotal ≤
          (bitLen (enc x).length + (enc x).length * (4 * bitLen (enc x).length + 10) + 3) +
            siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 * (mem0Bound d x + costBound d x + 1) ^ 3 +
            siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
              (mem0Bound d x + 2 * siteGsupAbi d * costBound d x +
                (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
                  bitLen 1 + bitLen 0 +
                  12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11) + 1) ^ 3
          + 1 +
          (outputLength * (16 * (2 * (natToDigits outputLength).length +
                (natToDigits 1).length + 1) + 2) + 1) +
            (outputLength * (32 * ((encodeLog log).length +
                  (natToDigits (outputBase + outputLength)).length + 1) ^ 2
                + 16 * (2 * (natToDigits (outputBase + outputLength)).length +
                    (natToDigits 1).length + bitLen (outputBase + outputLength) + bitLen 1 + 1)
                + 6) + 1) +
            ((0 + 1) + ((0 + 1) + ((0 + 1 + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) +
                  (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1)) +
                (((encodeLog log).length + 1) +
                  (regBound (abiProgram d.p d.outReg) *
                    ((max (regSizeBoundAbi d x) (natToDigits (outputBase + outputLength)).length)
                      + 1) + 1)))) + 1) + 2 := by
  obtain ⟨nRam, cfg', k, kEpi, hrunMg, hfinal, hioFinal, hkpc, hkmem, hkEpiPc,
     hrAddr, hrLen, hrOne, hrDest, hmemEpi, hRepr, hregSizeBound, hregMemBound, hnRambound⟩ :=
    ramRunToCleanupAbi_bound d x hx
  obtain ⟨sf0, Sg0, hrunToPrep, hprep, hSgBase, hcd, houtE⟩ :=
    master_init_to_halt_abi_landing d x nRam cfg' hrunMg hfinal
  have hmemF : (run kEpi (run k (compiledInputAbiRAM d.p d.outReg (enc x)))).mem =
      Program.eval d.p (bitInputStore (enc x)) := by rw [hmemEpi, hkmem]
  obtain ⟨log, cc, hlogBound, hlogLookup'⟩ :=
    master_init_to_halt_abi_bound_contract d x outputBase outputLength hOut cfg' _ sf0 Sg0 hRepr
      hmemF (by rw [hrAddr, hkmem, hOut.addr_eq]) (by rw [hrLen, hkmem, hOut.len_eq]) hrOne hrDest
      hregSizeBound hregMemBound hioFinal hprep hSgBase hcd houtE
  obtain ⟨nHalt, sfHalt, SgfHalt, hrunHalt, hsfHalt, houtHalt, hRegHalt, hMemHalt, hScrHalt,
      hIoHalt, hCdHalt, hnHaltbound⟩ :=
    master_run_bound_of_callerContract (programSupported_any _) (masterOutRegAbi d.p d.outReg)
      (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg) (abiOneReg d.p d.outReg)
      (abiLenReg d.p d.outReg) sf0 Sg0 outputLength outputBase log _ _ cc
  refine ⟨nRam + 1 + nHalt, sfHalt, SgfHalt, log, ?_, hsfHalt, houtHalt, hRegHalt, hMemHalt,
     hScrHalt, hIoHalt, hCdHalt, hlogBound, hlogLookup', ?_⟩
  · rw [show nRam + 1 + nHalt = nHalt + (nRam + 1) from by omega,
      Function.iterate_add_apply, hrunToPrep, hrunHalt]
  · omega

end NPComplete.RAMToTM.Generic

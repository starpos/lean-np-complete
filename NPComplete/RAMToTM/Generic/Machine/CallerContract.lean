module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmitMasterStage

/-!
# `CallerContract`: `master_run_bound`'s ABI hypotheses as a single named interface

`master_run_bound` (`GenericEmitMasterStage.lean`) states the facts a caller must establish about
the master machine's landing state (`sf0`/`Sg0`) before it takes over. `CallerContract` groups these
requirements into one `Prop`, and `master_run_bound_of_callerContract` adapts that bundled
hypothesis back to `master_run_bound` itself.

This interface fixes the facts required of `sf0` and `Sg0`, but does not construct them from an
actual RAM run. A caller must supply the register layout, memory separation, and values of `n`,
`addr`, and `regs0` needed to satisfy `CallerContract`; the adapter then converts that bundled
hypothesis to the assumptions of `master_run_bound`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits)

/-- Everything `master_run_bound` needs about the master machine's landing state
    (`sf0`/`Sg0`, right before `MasterΛ.prep EmitPrepPhase.checkLen` runs), bundled as a single
    Prop. `n`/`addr` describe the physical bit range `⟨addr, n⟩` to emit, `log` the memory
    write-log, with `regs0` giving the values of registers other than `rLen`, `rAddr`, and `rDest`.
    `M` is a uniform digit-length cap for register content used by cleanup. -/
structure CallerContract {p : List Instruction} (rAddr rDest rOne rLen : Fin (regBound p))
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ) (M : ℕ) : Prop where
  one_ne_len : rOne ≠ rLen
  addr_ne_len : rAddr ≠ rLen
  dest_ne_len : rDest ≠ rLen
  dest_ne_addr : rDest ≠ rAddr
  one_ne_addr : rOne ≠ rAddr
  one_ne_dest : rOne ≠ rDest
  regs0_len_le : ∀ i : Fin (regBound p), (natToDigits (regs0 i)).length ≤ M
  addr_n_len_le : (natToDigits (addr + n)).length ≤ M
  prep_canonical : sf0.prep = PrepState.canonical
  len_eq : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n
  addr_eq : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr
  one_eq : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1
  dest_eq : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit)
  other_regs_eq : ∀ i : Fin (regBound p), i ≠ rLen → i ≠ rAddr → i ≠ rDest →
    Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs0 i)
  mem_eq : Sg0 (EmitK.base Kg.mem) = encodeLog log
  countdown_empty : Sg0 EmitK.countdown = ([] : List Unit)
  out_empty : Sg0 EmitK.out = []
  work_rev_empty : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit)
  copy_scratch_empty : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit)
  lhs_operand_empty : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit)
  rhs_operand_empty : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit)
  diff_scratch_empty : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)
  query_empty : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit)
  query_tmp_empty : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit)
  log_tmp_empty : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym)
  sum_scratch_empty : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit)
  prologue_counter_empty : Sg0 (EmitK.base (Kg.scratch .prologueCounter)) = ([] : List Digit)
  prologue_work_empty : Sg0 (EmitK.base (Kg.scratch .prologueWork)) = ([] : List Digit)
  io_empty : Sg0 (EmitK.base Kg.io) = ([] : List Bool)
  bit_valid : ∀ i < n, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1

/-- `master_run_bound` restated against a single `CallerContract` hypothesis instead of its
    individual assumptions. This is an internal bundle of construction-specific ABI assumptions,
    not a stable public interface. -/
lemma master_run_bound_of_callerContract {p : List Instruction} (hSup : ProgramSupported p)
    (oReg rAddr rDest rOne rLen : Fin (regBound p))
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ) (M : ℕ)
    (cc : CallerContract rAddr rDest rOne rLen sf0 Sg0 n addr log regs0 M) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
        = some ⟨none, sf, Sgf⟩
        ∧ sf = MasterState.canonical
        ∧ Sgf EmitK.out = (OutputSlice.physicalBits log ⟨addr, n⟩).reverse
       ∧ (∀ i : Fin (regBound p), Sgf (EmitK.base (Kg.reg i)) = [])
       ∧ Sgf (EmitK.base Kg.mem) = []
       ∧ (∀ sk : ScratchKind, Sgf (EmitK.base (Kg.scratch sk)) = [])
       ∧ Sgf (EmitK.base Kg.io) = []
       ∧ Sgf EmitK.countdown = []
       ∧ n' ≤ (n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) + 1) +
          (n * (32 * ((encodeLog log).length + (natToDigits (addr + n)).length + 1) ^ 2
              + 16 * (2 * (natToDigits (addr + n)).length + (natToDigits 1).length
                  + bitLen (addr + n) + bitLen 1 + 1)
              + 6) + 1) +
          ((0 + 1) + ((0 + 1) + ((0 + 1 + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) +
                (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1)) +
              (((encodeLog log).length + 1) + (regBound p * (M + 1) + 1)))) + 1) + 2 :=
  master_run_bound hSup oReg rAddr rDest rOne rLen cc.one_ne_len cc.addr_ne_len cc.dest_ne_len
    cc.dest_ne_addr cc.one_ne_addr cc.one_ne_dest n addr log regs0 M cc.regs0_len_le
    cc.addr_n_len_le sf0 Sg0 cc.prep_canonical cc.len_eq cc.addr_eq cc.one_eq cc.dest_eq
    cc.other_regs_eq cc.mem_eq cc.countdown_empty cc.out_empty cc.work_rev_empty
    cc.copy_scratch_empty cc.lhs_operand_empty cc.rhs_operand_empty cc.diff_scratch_empty
    cc.query_empty cc.query_tmp_empty cc.log_tmp_empty cc.sum_scratch_empty
    cc.prologue_counter_empty cc.prologue_work_empty cc.io_empty cc.bit_valid

end NPComplete.RAMToTM.Generic

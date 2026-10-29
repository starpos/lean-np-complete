module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiEpilogue

/-!
# Fixing the ABI convention and composing `fullProgramAbi`'s full run

`abiSuffix` loads the output address and length from caller-selected cells. This module fixes
those cells as `outAddrCell` and `outLenCell`, defines the `ReductionOutput` postcondition for
their contents, and identifies `outputLoad` as a segment of `fullProgramAbi`. The reduction's
correctness proof supplies the output-range and bit-validity facts; they do not follow from the
ABI layout alone.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program)

/-- The fixed DSL cell holding the reduction's output physical base address once `d.p` halts.
    Reuses `bitInputStore`'s own cell `0` (its input-staging role is over by then, so a
    well-behaved `d.p` may repurpose it as output metadata). -/
def outAddrCell : ℕ := 0

/-- The fixed DSL cell holding the reduction's output bit length once `d.p` halts, mirroring
    `outAddrCell`. -/
def outLenCell : ℕ := 1

/-- Required postcondition on a reduction's final memory: cells `outAddrCell`/`outLenCell`
    hold a well-formed output range, with each bit in the range equal to `0` or `1`. -/
structure ReductionOutput (mem : ℕ → ℕ) (outputBase outputLength : ℕ) : Prop where
  addr_eq : mem outAddrCell = outputBase
  len_eq : mem outLenCell = outputLength
  bits_valid : ∀ i < outputLength, mem (outputBase + i) = 0 ∨ mem (outputBase + i) = 1

/-- Running `outputLoad outReg` changes only registers `0` (the loaded answer) and `1` (the
    staged address) — every other register is untouched. A `compileExpr_exec`-style frame
    conjunct would be vacuous here (`sb = 1` protects nothing below itself besides `dst = 0`), so
    this is proved directly from the two instructions' own `step_loadImm`/`step_load` frames
    instead. -/
lemma outputLoad_regs_frame (outReg : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (outputLoad outReg)) :
    ∃ k, (run k rr).pc = rr.pc + (outputLoad outReg).length ∧
      (run k rr).mem = rr.mem ∧ (run k rr).program = rr.program ∧
      ∀ y, y ≠ 0 → y ≠ 1 → (run k rr).regs y = rr.regs y := by
  simp only [outputLoad, compileExpr] at hseg ⊢
  have hcur0 : rr.current = Instruction.loadImm 1 outReg := by
    have := current_of_segment 0 hseg (by simp) rr rfl rfl
    simpa using this
  obtain ⟨_, e0pc, e0mem, e0prog, e0fr⟩ := step_loadImm rr 1 outReg hcur0
  have hcur1 : (step rr).current = Instruction.load 0 1 := by
    have := current_of_segment 1 hseg (by simp) (step rr) e0pc e0prog
    simpa using this
  obtain ⟨_, e1pc, e1mem, e1prog, e1fr⟩ := step_load (step rr) 0 1 hcur1
  refine ⟨2, ?_, ?_, ?_, ?_⟩ <;>
    rw [show run 2 rr = step (step rr) from by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_add]; rfl]
  · rw [e1pc, e0pc]; simp
  · rw [e1mem, e0mem]
  · rw [e1prog, e0prog]
  · intro y hy0 hy1
    rw [e1fr y hy0, e0fr y hy1]

/-- `outputLoad outReg` sits as a genuine segment of `fullProgramAbi`, right at the
    `compile p 0 0`/`outputLoad` boundary — the `fullProgramAbi` counterpart of
    `segmentAt_fullProgram_outputLoad`. -/
lemma segmentAt_fullProgramAbi_outputLoad (p : Program) (outReg addrCell lenCell : ℕ) :
    SegmentAt (fullProgramAbi p outReg addrCell lenCell) (codeLenP p) (outputLoad outReg) :=
  ⟨compile p 0 0, abiSuffix p addrCell lenCell, by simp [fullProgramAbi, fullProgram],
    compile_length p 0 0⟩

end NPComplete.RAMToTM.Generic

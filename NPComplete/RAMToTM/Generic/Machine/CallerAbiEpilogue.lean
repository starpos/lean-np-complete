module

public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine

/-!
# Reserving fresh ABI registers after a concrete `d.p`

This module places the four ABI registers above the register footprint of `compile p 0 0` and
`outputLoad`. That separation provides fresh ABI registers for the epilogue and ensures that
running it leaves every lower register unchanged. The output-memory requirements are expressed
separately by `ReductionOutput` and `CallerContract`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program Expr)

/-- Base index for the caller's four ABI registers: past both `outputLoad`'s own two registers
    (`0`/`1`) and everything `compile p 0 0` can name, so a caller can reserve fresh register
    slots for `p` without colliding with either. -/
def abiBase (p : Program) : ℕ := max 2 (regBound (compile p 0 0))

/-- The caller-reserved ABI epilogue: read the caller-designated `addrCell`/`lenCell` DSL cells
    (RAM `mem` addresses, per the mem-unified compiler) into fresh registers `abiBase p`/
    `abiBase p + 1`, and materialize the `1`/`0` constants `CallerContract` needs into
    `abiBase p + 2`/`abiBase p + 3`. Mirrors `outputLoad`'s own `.reg` epilogue
    (`BoundedWhileDecider.lean`), using `abiBase p + 4` as shared scratch for both loads (its
    own final content is a caller-computable constant, not part of the caller's ABI
    contract). -/
def abiSuffix (p : Program) (addrCell lenCell : ℕ) : List Instruction :=
  compileExpr (Expr.reg addrCell) (abiBase p) (abiBase p + 4) ++
    (compileExpr (Expr.reg lenCell) (abiBase p + 1) (abiBase p + 4) ++
      [Instruction.loadImm (abiBase p + 2) 1, Instruction.loadImm (abiBase p + 3) 0])

/-- `fullProgram p outReg` with the ABI epilogue appended after the existing single-bit
    `outputLoad` — the program a concrete decider actually compiles to. -/
def fullProgramAbi (p : Program) (outReg addrCell lenCell : ℕ) : List Instruction :=
  fullProgram p outReg ++ abiSuffix p addrCell lenCell

/-- `abiSuffix`'s instruction count: two `.reg` loads (two instructions each) plus two
    `loadImm`s. -/
lemma abiSuffix_length (p : Program) (addrCell lenCell : ℕ) :
    (abiSuffix p addrCell lenCell).length = 6 := by
  simp [abiSuffix, compileExpr]

/-- `fullProgramAbi`'s instruction count: `fullProgram`'s `codeLenP p + 2` plus `abiSuffix`'s
    six instructions. -/
lemma fullProgramAbi_length (p : Program) (outReg addrCell lenCell : ℕ) :
    (fullProgramAbi p outReg addrCell lenCell).length = codeLenP p + 8 := by
  show (fullProgram p outReg ++ abiSuffix p addrCell lenCell).length = codeLenP p + 8
  rw [List.length_append, fullProgram_length, abiSuffix_length]

/-- `abiSuffix` sits as a genuine segment of `fullProgramAbi`, right at the
    `fullProgram`/`abiSuffix` boundary (`codeLenP p + 2`, `fullProgram`'s own length). -/
lemma segmentAt_fullProgramAbi_abiSuffix (p : Program) (outReg addrCell lenCell : ℕ) :
    SegmentAt (fullProgramAbi p outReg addrCell lenCell) (codeLenP p + 2)
      (abiSuffix p addrCell lenCell) := by
  refine ⟨fullProgram p outReg, [], by simp [fullProgramAbi], ?_⟩
  rw [fullProgram_length]

/-- `abiBase p` is past `outputLoad`'s own two registers (`0`/`1`). -/
lemma abiBase_ge_two (p : Program) : 2 ≤ abiBase p := le_max_left _ _

/-- Running `abiSuffix p addrCell lenCell` from right after it starts copies the two
    caller-designated memory cells into the first two ABI registers, materializes the `1`/`0`
    constants into the remaining two, leaves every register below `abiBase p` exactly as it
    was, and touches neither `mem` nor `program` — in `≤ 6` RAM steps. -/
lemma abiSuffix_exec (p : Program) (addrCell lenCell : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (abiSuffix p addrCell lenCell)) :
    ∃ k, (run k rr).pc = rr.pc + (abiSuffix p addrCell lenCell).length ∧
      (run k rr).regs (abiBase p) = rr.mem addrCell ∧
      (run k rr).regs (abiBase p + 1) = rr.mem lenCell ∧
      (run k rr).regs (abiBase p + 2) = 1 ∧
      (run k rr).regs (abiBase p + 3) = 0 ∧
      (∀ x, x < abiBase p → (run k rr).regs x = rr.regs x) ∧
      (run k rr).mem = rr.mem ∧ (run k rr).program = rr.program ∧ k ≤ 6 := by
  set b := abiBase p with hbdef
  obtain ⟨k1, hpc1, hrA, hmemA, hfrA, hprogA, hk1⟩ :=
    compileExpr_exec (Expr.reg addrCell) b (b + 4) (by omega) rr hseg.append_left
  have hsegBC := hseg.append_right
  rw [← hprogA, ← hpc1] at hsegBC
  obtain ⟨k2, hpc2, hrB, hmemB, hfrB, hprogB, hk2⟩ :=
    compileExpr_exec (Expr.reg lenCell) (b + 1) (b + 4) (by omega) (run k1 rr) hsegBC.append_left
  have hsegC := hsegBC.append_right
  rw [← hprogB, ← hpc2] at hsegC
  have hcurC0 : (run k2 (run k1 rr)).current = Instruction.loadImm (b + 2) 1 := by
    have := current_of_segment 0 hsegC (by simp) (run k2 (run k1 rr)) rfl rfl
    simpa using this
  obtain ⟨hrC0, hpcC0, hmemC0, hprogC0, hfrC0⟩ :=
    step_loadImm (run k2 (run k1 rr)) (b + 2) 1 hcurC0
  have hcurC1 : (step (run k2 (run k1 rr))).current = Instruction.loadImm (b + 3) 0 := by
    have := current_of_segment 1 hsegC (by simp) (step (run k2 (run k1 rr))) hpcC0 hprogC0
    simpa using this
  obtain ⟨hrC1, hpcC1, hmemC1, hprogC1, hfrC1⟩ :=
    step_loadImm (step (run k2 (run k1 rr))) (b + 3) 0 hcurC1
  have hrun : run (k1 + k2 + 1 + 1) rr = step (step (run k2 (run k1 rr))) := by
    have e1 : k1 + k2 + 1 + 1 = k1 + (k2 + (1 + 1)) := by omega
    rw [e1, run_add, run_add, run_succ_right, show (1 : ℕ) = 0 + 1 from rfl, run_succ_right,
      run_zero]
  have hrAddr : (run k1 rr).regs b = rr.mem addrCell := by
    rw [hrA]; simp [Expr.eval]
  have hrLen : (run k2 (run k1 rr)).regs (b + 1) = rr.mem lenCell := by
    rw [hrB, hmemA]; simp [Expr.eval]
  have hk1' : k1 ≤ 2 := by simp only [Expr.cost] at hk1; omega
  have hk2' : k2 ≤ 2 := by simp only [Expr.cost] at hk2; omega
  refine ⟨k1 + k2 + 1 + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [hrun, hpcC1, hpcC0, hpc2, hpc1]
    simp only [abiSuffix, compileExpr, List.length_append, List.length_cons, List.length_nil]
  · rw [hrun, hfrC1 b (by omega), hfrC0 b (by omega), hfrB b (by omega) (by omega), hrAddr]
  · rw [hrun, hfrC1 (b + 1) (by omega), hfrC0 (b + 1) (by omega), hrLen]
  · rw [hrun, hfrC1 (b + 2) (by omega), hrC0]
  · rw [hrun, hrC1]
  · intro x hx
    rw [hrun, hfrC1 x (by omega), hfrC0 x (by omega), hfrB x (by omega) (by omega),
      hfrA x (by omega) (by omega)]
  · rw [hrun, hmemC1, hmemC0, hmemB, hmemA]
  · rw [hrun, hprogC1, hprogC0, hprogB, hprogA]

/-- The `abiSuffix` run takes at most six steps and has accumulated cost
    `rr.cost + 2 * bitLen addrCell + 2 * bitLen lenCell + bitLen (rr.mem addrCell) +
    bitLen (rr.mem lenCell) + bitLen 1 + bitLen 0 + 6`. -/
lemma abiSuffix_exec_cost (p : Program) (addrCell lenCell : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (abiSuffix p addrCell lenCell)) :
    ∃ k, (run k rr).pc = rr.pc + (abiSuffix p addrCell lenCell).length ∧
      (run k rr).regs (abiBase p) = rr.mem addrCell ∧
      (run k rr).regs (abiBase p + 1) = rr.mem lenCell ∧
      (run k rr).regs (abiBase p + 2) = 1 ∧
      (run k rr).regs (abiBase p + 3) = 0 ∧
      (∀ x, x < abiBase p → (run k rr).regs x = rr.regs x) ∧
      (run k rr).mem = rr.mem ∧ (run k rr).program = rr.program ∧ k ≤ 6 ∧
      (run k rr).cost = rr.cost + 2 * bitLen addrCell + 2 * bitLen lenCell +
        bitLen (rr.mem addrCell) + bitLen (rr.mem lenCell) + bitLen 1 + bitLen 0 + 6 := by
  set b := abiBase p with hbdef
  simp only [abiSuffix, compileExpr] at hseg ⊢
  have hcur0 : rr.current = Instruction.loadImm (b + 4) addrCell := by
    have := current_of_segment 0 hseg (by simp) rr rfl rfl; simpa using this
  obtain ⟨e0regs, e0pc, e0mem, e0prog, e0fr⟩ := step_loadImm rr (b + 4) addrCell hcur0
  have hcur1 : (step rr).current = Instruction.load b (b + 4) := by
    have := current_of_segment 1 hseg (by simp) (step rr) e0pc e0prog; simpa using this
  obtain ⟨e1regs, e1pc, e1mem, e1prog, e1fr⟩ := step_load (step rr) b (b + 4) hcur1
  have hcur2 : (step (step rr)).current = Instruction.loadImm (b + 4) lenCell := by
    have := current_of_segment 2 hseg (by simp) (step (step rr))
      (by rw [e1pc, e0pc]) (by rw [e1prog, e0prog])
    simpa using this
  obtain ⟨e2regs, e2pc, e2mem, e2prog, e2fr⟩ :=
    step_loadImm (step (step rr)) (b + 4) lenCell hcur2
  have hcur3 : (step (step (step rr))).current = Instruction.load (b + 1) (b + 4) := by
    have := current_of_segment 3 hseg (by simp) (step (step (step rr)))
      (by rw [e2pc, e1pc, e0pc]) (by rw [e2prog, e1prog, e0prog])
    simpa using this
  obtain ⟨e3regs, e3pc, e3mem, e3prog, e3fr⟩ :=
    step_load (step (step (step rr))) (b + 1) (b + 4) hcur3
  have hcur4 : (step (step (step (step rr)))).current = Instruction.loadImm (b + 2) 1 := by
    have := current_of_segment 4 hseg (by simp) (step (step (step (step rr))))
      (by rw [e3pc, e2pc, e1pc, e0pc]) (by rw [e3prog, e2prog, e1prog, e0prog])
    simpa using this
  obtain ⟨e4regs, e4pc, e4mem, e4prog, e4fr⟩ :=
    step_loadImm (step (step (step (step rr)))) (b + 2) 1 hcur4
  have hcur5 : (step (step (step (step (step rr))))).current = Instruction.loadImm (b + 3) 0 := by
    have := current_of_segment 5 hseg (by simp) (step (step (step (step (step rr)))))
      (by rw [e4pc, e3pc, e2pc, e1pc, e0pc]) (by rw [e4prog, e3prog, e2prog, e1prog, e0prog])
    simpa using this
  obtain ⟨e5regs, e5pc, e5mem, e5prog, e5fr⟩ :=
    step_loadImm (step (step (step (step (step rr))))) (b + 3) 0 hcur5
  have hrun : run 6 rr = step (step (step (step (step (step rr))))) := by
    show run (5+1) rr = _
    rw [run_succ_right]
    show step (run (4+1) rr) = _
    rw [run_succ_right]
    show step (step (run (3+1) rr)) = _
    rw [run_succ_right]
    show step (step (step (run (2+1) rr))) = _
    rw [run_succ_right]
    show step (step (step (step (run (1+1) rr)))) = _
    rw [run_succ_right]
    show step (step (step (step (step (run (0+1) rr))))) = _
    rw [run_succ_right, run_zero]
  have hcost0 : (step rr).cost = rr.cost + (bitLen addrCell + 1) := by
    rw [cost_step_eq_add rr, hcur0]; simp [instructionCost]
  have hcost1 : (step (step rr)).cost =
      (step rr).cost +
        (bitLen ((step rr).regs (b+4)) + bitLen ((step rr).mem ((step rr).regs (b+4))) + 1) := by
    rw [cost_step_eq_add (step rr), hcur1]; simp [instructionCost]
  have hcost2 : (step (step (step rr))).cost = (step (step rr)).cost + (bitLen lenCell + 1) := by
    rw [cost_step_eq_add (step (step rr)), hcur2]; simp [instructionCost]
  have hcost3 : (step (step (step (step rr)))).cost = (step (step (step rr))).cost +
      (bitLen ((step (step (step rr))).regs (b+4)) +
        bitLen ((step (step (step rr))).mem ((step (step (step rr))).regs (b+4))) + 1) := by
    rw [cost_step_eq_add (step (step (step rr))), hcur3]; simp [instructionCost]
  have hcost4 : (step (step (step (step (step rr))))).cost =
      (step (step (step (step rr)))).cost + (bitLen 1 + 1) := by
    rw [cost_step_eq_add (step (step (step (step rr)))), hcur4]; simp [instructionCost]
  have hcost5 : (step (step (step (step (step (step rr)))))).cost =
      (step (step (step (step (step rr))))).cost + (bitLen 0 + 1) := by
    rw [cost_step_eq_add (step (step (step (step (step rr))))), hcur5]; simp [instructionCost]
  refine ⟨6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_refl 6, ?_⟩
  · rw [hrun, e5pc, e4pc, e3pc, e2pc, e1pc, e0pc]; simp
  · rw [hrun, e5fr b (by omega), e4fr b (by omega), e3fr b (by omega), e2fr b (by omega),
      e1regs, e0regs, e0mem]
  · rw [hrun, e5fr (b+1) (by omega), e4fr (b+1) (by omega), e3regs, e2regs, e2mem, e1mem, e0mem]
  · rw [hrun, e5fr (b+2) (by omega), e4regs]
  · rw [hrun, e5regs]
  · intro x hx
    rw [hrun, e5fr x (by omega), e4fr x (by omega), e3fr x (by omega), e2fr x (by omega),
      e1fr x (by omega), e0fr x (by omega)]
  · rw [hrun, e5mem, e4mem, e3mem, e2mem, e1mem, e0mem]
  · rw [hrun, e5prog, e4prog, e3prog, e2prog, e1prog, e0prog]
  · rw [hrun, hcost5, hcost4, hcost3, hcost2, hcost1, hcost0, e0regs, e2regs, e2mem, e1mem, e0mem]
    ring

/-- `abiSuffix`'s own `loadImm` immediates are bounded by the larger of `addrCell`/`lenCell`'s
    `bitLen` and `1` (the `abiOneReg` constant) — `abiDestReg`'s `0` needs no separate case since
    `bitLen 0 = 1 = bitLen 1`. -/
lemma programImmediatesLe_abiSuffix (p : Program) (addrCell lenCell : ℕ) :
    ProgramImmediatesLe (max (bitLen addrCell) (max (bitLen lenCell) 1))
      (abiSuffix p addrCell lenCell) := by
  unfold abiSuffix
  refine ProgramImmediatesLe.append ?_ (ProgramImmediatesLe.append ?_ ?_)
  · exact ProgramImmediatesLe.mono (le_max_left _ _)
      (programImmediatesLe_compileExpr (Expr.reg addrCell) (abiBase p) (abiBase p + 4))
  · exact ProgramImmediatesLe.mono (le_trans (le_max_left _ _) (le_max_right _ _))
      (programImmediatesLe_compileExpr (Expr.reg lenCell) (abiBase p + 1) (abiBase p + 4))
  · intro i hi d n hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> simp only [Instruction.loadImm.injEq] at hin <;>
      obtain ⟨_, rfl⟩ := hin
    · exact le_trans (le_refl (bitLen 1)) (le_trans (le_max_right _ _) (le_max_right _ _))
    · simp

end NPComplete.RAMToTM.Generic

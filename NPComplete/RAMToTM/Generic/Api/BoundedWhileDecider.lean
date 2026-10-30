module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BitEncoding
public import Mathlib.Computability.TuringMachine.Computable
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileRefinement
public import NPComplete.BoundedWhile.Basic
public import Mathlib.Tactic.Ring

/-!
# `BoundedWhile.Program` realizability as a `TM2ComputableInPolyTime` machine

`bitInputStore` fixes the RAM input representation: cell `0` stores the encoded input's bit
length, and cell `i + 1` stores bit `i`. Using this single `enc`-determined loader for every
instance prevents correctness from being witnessed by an arbitrary initial store containing a
precomputed answer. `BoundedWhileDecider` bundles a `Program` with correctness and a cost bound
*against this loader*. `TMRealizable` is a separate obligation asserting that the resulting
`Bool`-valued function is `FinTM2`-computable in polynomial time, independently of how downstream
APIs use the result.

`cost_le` alone bounds `p`'s *operation count*, not the *bit-cost* of running its
`BoundedWhileRefinement`-compiled RAM form: a fixed operation count can still blow
operand values up (e.g. repeated squaring), which `instructionCost` charges for. A
`BoundedWhileDecider` therefore separately supplies `compiled_operands_le`, a dynamic
operand bit-length bound (`CompiledOperandBound`, phrased against the compiled RAM
`compiledInputRAM p (enc x)`) that `compile_exec_cost` needs to turn `cost_le`'s
operation-count bound into an actual RAM bit-cost bound, closing the gap between operation count
and bit cost.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr)
open NPComplete.BitEncoding (Bits encodeBool)
open NPComplete.BitCostRAM (RAM emptyBank run Instruction bitLen
  step run_succ_right run_zero run_halted cost_step_eq_add instructionCost)
open NPComplete.BoundedWhile (loopEval loopEval_succ loopEval_zero)

export NPComplete.BoundedWhile (loopEval_one loopEval_add)

/-- The canonical loader shared by every `BoundedWhileDecider`: cell `0` holds the
    bit length of `bits`, cell `i + 1` holds bit `i` (as `0`/`1`), every other cell
    is `0`. Fixed once and for all, so it cannot itself encode an answer — a
    `BoundedWhileDecider`'s `Program` has to compute `L x` from these cells alone. -/
@[construction_api] def bitInputStore (bits : Bits) : Store :=
  fun r => match r with
    | 0 => bits.length
    | r + 1 => if bits.getD r false then 1 else 0

@[construction_api] lemma bitInputStore_zero (bits : Bits) :
    bitInputStore bits 0 = bits.length := rfl

@[construction_api] lemma bitInputStore_succ_of_lt (bits : Bits) (i : ℕ)
    (h : i < bits.length) : bitInputStore bits (i + 1) = if bits[i] then 1 else 0 := by
  simp only [bitInputStore, List.getD_eq_getElem _ false h]

/-! ## Blank cells after the encoded input -/

/-- Every cell at or past `bits.length + 1` (one past the encoded input bits) is `0` on a
    freshly loaded `bitInputStore` — the workspace a reduction grows into starts blank, so heap
    appends do not inherit residual bits from the loader. -/
@[construction_api] lemma bitInputStore_eq_zero_of_ge_inputEnd (bits : Bits) (r : ℕ)
    (hr : bits.length + 1 ≤ r) : bitInputStore bits r = 0 := by
  match r with
  | 0 => omega
  | r' + 1 =>
    have hr' : bits.length ≤ r' := by omega
    simp only [bitInputStore]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-- The RAM state right after loading `p` (compiled with no register frame, `sb := 0`, at
    absolute `pc := 0`) against `bits` via the canonical `bitInputStore` loader. -/
@[construction_api] def compiledInputRAM (p : Program) (bits : Bits) : RAM :=
  { regs := emptyBank
    mem := bitInputStore bits
    pc := 0
    cost := 0
    program := compile p 0 0 }

/-- `DynamicOperandsLe W` (`BoundedWhileRefinement.lean`) holds at every one of the first `k`
    RAM steps of running `p`'s compiled form loaded against `bits` — the hypothesis
    `compile_exec_cost` needs, together with `cost_le`'s operation-count bound, to bound the
    compiled program's accumulated `RAM.cost`. -/
@[construction_api] def CompiledOperandBound (p : Program) (bits : Bits) (W : ℕ) : Prop :=
  ∀ k, k ≤ 8 * p.cost (bitInputStore bits) → RunDynLe W k (compiledInputRAM p bits)

/-! ## Output epilogue

`BoundedWhileDecider.outReg : ℕ` names a *DSL* `Store` address: `p.eval store outReg` reads it
through `Program.eval`'s abstract `Store`, and the compiler routes every DSL `Store` cell to
`RAM.mem`, never to a RAM register (`BoundedWhileRefinement.lean`'s module docstring —
`compileExpr`'s `.reg` case stages the address into a scratch register only to `load` through it).
So after `compile p 0 0` halts on its own, the decided answer sits in `RAM.mem outReg`, not in any
register. But `TransducerMachine`'s cleanup phase (`GenericCleanup.lean`) reads its answer
bit out of a *register* (`Fin (regBound p)`), the RAM-level scratch address space `Mg`/`Λg` are
built around — a different address space than `outReg`'s. Closing that gap needs one more compiled
block appended after `compile p 0 0`: a plain `Expr.reg outReg` load, copying `mem outReg` into
register `0`. This mirrors `compileExpr`'s own `.reg` case exactly, so `compileExpr_exec` already
proves its correctness (`outputLoad_exec_cost` below) — no new step-simulation lemma is needed, only
the composition. -/

/-- The two-instruction epilogue that copies the decided answer from its DSL `Store` address
    `outReg` into register `0`, the address the cleanup phase reads from. -/
def outputLoad (outReg : ℕ) : List Instruction := compileExpr (Expr.reg outReg) 0 1

/-- `p` compiled together with the epilogue that stages its `outReg` answer into register `0` —
    the actual program `TransducerMachine` realizes, as opposed to `compile p 0 0` alone (module
    comment above). -/
def fullProgram (p : Program) (outReg : ℕ) : List Instruction := compile p 0 0 ++ outputLoad outReg

/-- The RAM state right after loading `fullProgram p outReg` against `bits` via the canonical
    loader — `compiledInputRAM`'s counterpart for the main-program-plus-epilogue. -/
def compiledInputFullRAM (p : Program) (outReg : ℕ) (bits : Bits) : RAM :=
  { regs := emptyBank
    mem := bitInputStore bits
    pc := 0
    cost := 0
    program := fullProgram p outReg }

/-- `compile p 0 0` sits as a genuine prefix segment of `fullProgram p outReg`, at PC `0` — the
    fact that lets `compile_exec_cost` run the main program *within* the larger `fullProgram`
    rather than requiring `RAM.program` to equal `compile p 0 0` exactly. -/
lemma segmentAt_fullProgram_compile (p : Program) (outReg : ℕ) :
    SegmentAt (fullProgram p outReg) 0 (compile p 0 0) := by
  refine ⟨[], outputLoad outReg, ?_, rfl⟩
  simp [fullProgram]

/-- `outputLoad`'s instruction count: a `loadImm` staging the address followed by one `load` —
    `compileExpr`'s `.reg` case, unfolded. -/
lemma outputLoad_length (outReg : ℕ) : (outputLoad outReg).length = 2 := by
  simp [outputLoad, compileExpr]

/-- `fullProgram`'s instruction count: the main program's `codeLenP` plus `outputLoad`'s two
    instructions. -/
lemma fullProgram_length (p : Program) (outReg : ℕ) :
    (fullProgram p outReg).length = codeLenP p + 2 := by
  show (compile p 0 0 ++ outputLoad outReg).length = codeLenP p + 2
  rw [List.length_append, compile_length]
  simp [outputLoad, compileExpr]

/-- `outputLoad outReg` sits as a genuine segment of `fullProgram p outReg` right at the
    `compile p 0 0`/`outputLoad` boundary — the fact `outputLoad_exec_cost` needs to run from a RAM
    state whose `.program` is the larger `fullProgram`, not just the bare `outputLoad` list. -/
lemma segmentAt_fullProgram_outputLoad (p : Program) (outReg : ℕ) :
    SegmentAt (fullProgram p outReg) (codeLenP p) (outputLoad outReg) :=
  ⟨compile p 0 0, [], by simp [fullProgram], compile_length p 0 0⟩

/-- `outputLoad`'s 2-step run (obligation (a)): the PC/register/memory facts of
    the run, together with the exact RAM bit-cost `outputLoad` charges — `loadImm 1 outReg` (cost
    `bitLen outReg + 1`) then `load 0 1` (cost `bitLen outReg + bitLen (rr.mem outReg) + 1`, since
    `regs 1 = outReg` by then). The cost half is needed as the `costDelta` input to
    `BoundedRunSim`'s cubic bound when simulating this epilogue in TM steps; re-derives the run
    directly (rather than generalizing `compileExpr_exec` itself with a cost conjunct) since only
    this one `.reg` instantiation needs it. -/
lemma outputLoad_exec_cost (outReg : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (outputLoad outReg)) :
    ∃ k, (run k rr).pc = rr.pc + (outputLoad outReg).length ∧
      (run k rr).regs 0 = rr.mem outReg ∧ (run k rr).mem = rr.mem ∧
      (run k rr).program = rr.program ∧ k ≤ 2 ∧
      (run k rr).cost = rr.cost + 2 * bitLen outReg + bitLen (rr.mem outReg) + 2 := by
  simp only [outputLoad, compileExpr] at hseg ⊢
  have hcur0 : rr.current = Instruction.loadImm 1 outReg := by
    have := current_of_segment 0 hseg (by simp) rr rfl rfl; simpa using this
  obtain ⟨e0regs, e0pc, e0mem, e0prog, e0fr⟩ := step_loadImm rr 1 outReg hcur0
  have hcur1 : (step rr).current = Instruction.load 0 1 := by
    have := current_of_segment 1 hseg (by simp) (step rr) e0pc e0prog; simpa using this
  obtain ⟨e1regs, e1pc, e1mem, e1prog, e1fr⟩ := step_load (step rr) 0 1 hcur1
  have hcost0 : (step rr).cost = rr.cost + (bitLen outReg + 1) := by
    rw [cost_step_eq_add rr, hcur0]; simp [instructionCost]
  have hcost1 : (step (step rr)).cost =
      (step rr).cost +
        (bitLen ((step rr).regs 1) + bitLen ((step rr).mem ((step rr).regs 1)) + 1) := by
    rw [cost_step_eq_add (step rr), hcur1]; simp [instructionCost]
  refine ⟨2, ?_, ?_, ?_, ?_, le_refl 2, ?_⟩ <;>
    rw [show run 2 rr = step (step rr) from by
      rw [show (2:ℕ) = 1 + 1 from rfl, run_add]; rfl]
  · rw [e1pc, e0pc]; simp
  · rw [e1regs, e0mem, e0regs]
  · rw [e1mem, e0mem]
  · rw [e1prog, e0prog]
  · rw [hcost1, e0regs, hcost0, e0mem]
    ring

/-- `outputLoad`'s only `loadImm` immediate is `outReg` itself (staged before the closing
    `load`) — the `.reg` case of `exprImmBound`, specialized. -/
lemma programImmediatesLe_outputLoad (outReg : ℕ) :
    ProgramImmediatesLe (bitLen outReg) (outputLoad outReg) :=
  programImmediatesLe_compileExpr (Expr.reg outReg) 0 1

/-- `fullProgram`'s `loadImm` immediates are bounded by the larger of `compile p 0 0`'s own bound
    and `outputLoad`'s (`bitLen outReg`) — the `I` `compile_exec_cost` needs when run against
    `compiledInputFullRAM` instead of `compiledInputRAM` (module comment above). -/
lemma programImmediatesLe_fullProgram (p : Program) (outReg : ℕ) :
    ProgramImmediatesLe (max (programImmBound p) (bitLen outReg)) (fullProgram p outReg) :=
  ProgramImmediatesLe.append
    (ProgramImmediatesLe.mono (le_max_left _ _) (programImmediatesLe_compile_zero p))
    (ProgramImmediatesLe.mono (le_max_right _ _) (programImmediatesLe_outputLoad outReg))

/-! ## Locality bridge

`compiled_operands_le` (`BoundedWhileDecider.compiled_operands_le` below) is stated against
the *bare* `compiledInputRAM`, deliberately kept that way so the epilogue doesn't ripple into
every instance (module comment above). Bridging its `RunDynLe` bound to `compiledInputFullRAM`
needs confinement for the *full* run specifically: `fullProgram_pc_no_return` shows the PC
never returns to the `compile p 0 0` / `outputLoad` boundary once it has crossed it (`outputLoad`
is two non-jump instructions, after which execution runs off `fullProgram`'s end and freezes),
and `fullProgram_run_confined` combines that with `compile_targets_in`/`step_confined`
(`BoundedWhileRefinement.lean`) via a least-counterexample argument to get strict confinement
for every step before *any* given completion witness `k` — without needing to know `k` is the
*first* arrival, and without a bare-vs-full trajectory comparison. -/

/-- Once a `fullProgram`-labelled RAM's PC reaches `codeLenP p` (the boundary between
    `compile p 0 0` and the `outputLoad` epilogue), it never returns there: `outputLoad`
    is two non-jump instructions, after which the PC runs off the end of `fullProgram`
    and freezes (`run_halted`) strictly past the boundary. -/
lemma fullProgram_pc_no_return (p : Program) (outReg : ℕ) (t : RAM)
    (hprog : t.program = fullProgram p outReg) (hpc : t.pc = codeLenP p) :
    ∀ m, 0 < m → (run m t).pc ≠ codeLenP p := by
  have hsegOL : SegmentAt (fullProgram p outReg) (codeLenP p) (outputLoad outReg) :=
    ⟨compile p 0 0, [], by simp [fullProgram], compile_length p 0 0⟩
  have holLen : (outputLoad outReg).length = 2 := by simp [outputLoad, compileExpr]
  have hc0 : t.current = Instruction.loadImm 1 outReg := by
    rw [current_eq_getD, hprog, hpc]
    have := segment_getD hsegOL (show 0 < (outputLoad outReg).length from by omega)
    simpa [outputLoad, compileExpr] using this
  obtain ⟨_, hp1, _, hprog1, _⟩ := step_loadImm t 1 outReg hc0
  have hpc1 : (step t).pc = codeLenP p + 1 := by rw [hp1, hpc]
  have hc1 : (step t).current = Instruction.load 0 1 := by
    rw [current_eq_getD, hprog1, hprog, hpc1]
    have := segment_getD hsegOL (show 1 < (outputLoad outReg).length from by omega)
    simpa [outputLoad, compileExpr] using this
  obtain ⟨_, hp2, _, hprog2, _⟩ := step_load (step t) 0 1 hc1
  have hpc2 : (step (step t)).pc = codeLenP p + 2 := by rw [hp2, hpc1]
  have hprog2' : (step (step t)).program = t.program := by rw [hprog2, hprog1]
  have hflen : (fullProgram p outReg).length = codeLenP p + 2 := by
    show (compile p 0 0 ++ outputLoad outReg).length = codeLenP p + 2
    rw [List.length_append, compile_length, holLen]
  have hcur2 : (step (step t)).current = Instruction.halt := by
    rw [current_eq_getD, hprog2', hprog, hpc2]
    exact List.getD_eq_default _ _ (by rw [hflen])
  have hrun2 : run 2 t = step (step t) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, run_succ_right, run_succ_right, run_zero]
  intro m hm
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · have hm1 : m = 1 := by omega
    subst hm1
    rw [show (1:ℕ) = 0 + 1 from rfl, run_succ_right, run_zero, hpc1]
    omega
  · have heq : run m t = run (m - 2) (run 2 t) := by
      conv_lhs => rw [show m = 2 + (m - 2) from by omega]
      rw [run_add]
    rw [heq, hrun2, run_halted _ hcur2, hpc2]
    omega

/-- Confinement for the `fullProgram`-labelled run: given *any* completion witness `k` (a step
    count at which the PC lands exactly on the `compile p 0 0`/`outputLoad` boundary), every
    earlier step's PC stays strictly inside `compile p 0 0`'s segment. Combines the static
    jump-range fact (`compile_targets_in`) with the no-return fact via a least-counterexample
    argument, so it needs neither a bare-vs-full trajectory comparison nor a redo of
    `compile_exec`'s own induction (module comment above). -/
lemma fullProgram_run_confined (p : Program) (outReg : ℕ) (R : RAM)
    (hprog : R.program = fullProgram p outReg) (hpc0 : R.pc = 0) (k : ℕ)
    (hk : (run k R).pc = codeLenP p) :
    ∀ j, j < k → (run j R).pc < codeLenP p := by
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨j0, hj0lt, hj0ge⟩ := hcon
  have hex : ∃ j, j < k ∧ codeLenP p ≤ (run j R).pc := ⟨j0, hj0lt, hj0ge⟩
  set j0' := Nat.find hex with hj0'def
  have hspec := Nat.find_spec hex
  rw [← hj0'def] at hspec
  obtain ⟨hj0'lt, hj0'ge⟩ := hspec
  have hrunprog : ∀ i, (run i R).program = fullProgram p outReg := by
    intro i; rw [run_program, hprog]
  rcases Nat.eq_zero_or_pos j0' with hz | hpos
  · have hpceq : R.pc = codeLenP p := by
      have := hj0'ge; rw [hz, run_zero, hpc0] at this; omega
    exact (fullProgram_pc_no_return p outReg R hprog hpceq k (by omega)) hk
  · have hmin : ¬ (j0' - 1 < k ∧ codeLenP p ≤ (run (j0' - 1) R).pc) :=
      Nat.find_min hex (by omega)
    have hlt' : (run (j0' - 1) R).pc < codeLenP p := by
      by_contra h; exact hmin ⟨by omega, by omega⟩
    have hseg : SegmentAt (run (j0' - 1) R).program 0 (compile p 0 0) := by
      rw [hrunprog]; exact segmentAt_fullProgram_compile p outReg
    have hstep := step_confined (s := run (j0' - 1) R) (start := 0) (len := codeLenP p)
      (code := compile p 0 0) hseg (compile_length p 0 0) (compile_targets_in p 0 0)
      (by omega) (by omega)
    have hj0eq : (run j0' R).pc = codeLenP p := by
      have hstepeq : step (run (j0' - 1) R) = run j0' R := by
        have hsr : run (j0' - 1 + 1) R = step (run (j0' - 1) R) := run_succ_right (j0' - 1) R
        rw [show j0' - 1 + 1 = j0' from by omega] at hsr
        exact hsr.symm
      rw [hstepeq] at hstep
      omega
    have hnr := fullProgram_pc_no_return p outReg (run j0' R) (hrunprog j0') hj0eq
      (k - j0') (by omega)
    apply hnr
    have heq : run (k - j0') (run j0' R) = run k R := by
      rw [← run_add]
      congr 1
      omega
    rw [heq, hk]

/-- State-agreement: `compiledInputRAM` (bare) and `compiledInputFullRAM` (full) start with
    identical `regs`/`mem`/`pc`/`cost` and differ only in `.program` (bare vs. `fullProgram`).
    Given a full-run completion witness `k`, `fullProgram_run_confined` keeps `full`'s PC
    strictly inside the shared `compile p 0 0` prefix for every `j < k`, so both runs read the
    same `.current` there (`segmentAt_self`/`segmentAt_fullProgram_compile` place the *same*
    code at the same offset) and `step_congr` propagates agreement one step at a time. -/
lemma compiledInputRAM_full_agree (p : Program) (outReg : ℕ) (bits : Bits) (k : ℕ)
    (hk : (run k (compiledInputFullRAM p outReg bits)).pc = codeLenP p) :
    ∀ j, j ≤ k →
      (run j (compiledInputRAM p bits)).regs = (run j (compiledInputFullRAM p outReg bits)).regs ∧
      (run j (compiledInputRAM p bits)).mem = (run j (compiledInputFullRAM p outReg bits)).mem ∧
      (run j (compiledInputRAM p bits)).pc = (run j (compiledInputFullRAM p outReg bits)).pc ∧
      (run j (compiledInputRAM p bits)).cost = (run j (compiledInputFullRAM p outReg bits)).cost := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl, rfl, rfl⟩
  | succ j ih =>
      intro hjk
      obtain ⟨hr, hm, hp, hco⟩ := ih (by omega)
      have hconf := fullProgram_run_confined p outReg (compiledInputFullRAM p outReg bits)
        rfl rfl k hk j (by omega)
      have hpb : (run j (compiledInputRAM p bits)).pc < codeLenP p := by rw [hp]; exact hconf
      have hsegB : SegmentAt (run j (compiledInputRAM p bits)).program 0 (compile p 0 0) := by
        rw [run_program]; exact segmentAt_self (compile p 0 0)
      have hsegF : SegmentAt (run j (compiledInputFullRAM p outReg bits)).program 0
          (compile p 0 0) := by
        rw [run_program]; exact segmentAt_fullProgram_compile p outReg
      have hcurB : (run j (compiledInputRAM p bits)).current =
          (compile p 0 0).getD (run j (compiledInputRAM p bits)).pc Instruction.halt := by
        rw [current_eq_getD]
        have := segment_getD hsegB (by rw [compile_length]; exact hpb)
        rwa [show (0:ℕ) + (run j (compiledInputRAM p bits)).pc
          = (run j (compiledInputRAM p bits)).pc from by omega] at this
      have hcurF : (run j (compiledInputFullRAM p outReg bits)).current =
          (compile p 0 0).getD (run j (compiledInputFullRAM p outReg bits)).pc Instruction.halt := by
        rw [current_eq_getD]
        have := segment_getD hsegF (by rw [compile_length]; exact hconf)
        rwa [show (0:ℕ) + (run j (compiledInputFullRAM p outReg bits)).pc
          = (run j (compiledInputFullRAM p outReg bits)).pc from by omega] at this
      have hcur : (run j (compiledInputRAM p bits)).current =
          (run j (compiledInputFullRAM p outReg bits)).current := by
        rw [hcurB, hcurF, hp]
      obtain ⟨hr', hm', hp', hco'⟩ := step_congr hcur hr hm hp hco
      rw [run_succ_right, run_succ_right]
      exact ⟨hr', hm', hp', hco'⟩

/-- Bare and full agree on `.current` too at every step *before* completion (`j < k`, so
    confinement still applies): the same segment argument `compiledInputRAM_full_agree`'s
    inductive step uses, exposed standalone for `RunDynLe`'s per-step predicate. -/
lemma compiledInputRAM_full_current_agree (p : Program) (outReg : ℕ) (bits : Bits) (k j : ℕ)
    (hk : (run k (compiledInputFullRAM p outReg bits)).pc = codeLenP p) (hj : j < k) :
    (run j (compiledInputRAM p bits)).current =
      (run j (compiledInputFullRAM p outReg bits)).current := by
  obtain ⟨hr, hm, hp, hco⟩ := compiledInputRAM_full_agree p outReg bits k hk j (by omega)
  have hconf := fullProgram_run_confined p outReg (compiledInputFullRAM p outReg bits)
    rfl rfl k hk j hj
  have hpb : (run j (compiledInputRAM p bits)).pc < codeLenP p := by rw [hp]; exact hconf
  have hsegB : SegmentAt (run j (compiledInputRAM p bits)).program 0 (compile p 0 0) := by
    rw [run_program]; exact segmentAt_self (compile p 0 0)
  have hsegF : SegmentAt (run j (compiledInputFullRAM p outReg bits)).program 0
      (compile p 0 0) := by
    rw [run_program]; exact segmentAt_fullProgram_compile p outReg
  have hcurB : (run j (compiledInputRAM p bits)).current =
      (compile p 0 0).getD (run j (compiledInputRAM p bits)).pc Instruction.halt := by
    rw [current_eq_getD]
    have := segment_getD hsegB (by rw [compile_length]; exact hpb)
    rwa [show (0:ℕ) + (run j (compiledInputRAM p bits)).pc
      = (run j (compiledInputRAM p bits)).pc from by omega] at this
  have hcurF : (run j (compiledInputFullRAM p outReg bits)).current =
      (compile p 0 0).getD (run j (compiledInputFullRAM p outReg bits)).pc Instruction.halt := by
    rw [current_eq_getD]
    have := segment_getD hsegF (by rw [compile_length]; exact hconf)
    rwa [show (0:ℕ) + (run j (compiledInputFullRAM p outReg bits)).pc
      = (run j (compiledInputFullRAM p outReg bits)).pc from by omega] at this
  rw [hcurB, hcurF, hp]

/-- The `RunDynLe` bridge (module comment above `fullProgram_pc_no_return`):
    `compiled_operands_le`'s bare bound transfers to `compiledInputFullRAM`, for any `k` at
    which the full run's own `compile_exec` completes. `DynamicOperandsLe` reads only
    `.current`/`.regs`/`.mem` (`BoundedWhileRefinement.lean`), all agreeing between bare and
    full at every `j < k` by `compiledInputRAM_full_agree`/`_current_agree`. -/
lemma runDynLe_bare_to_full (p : Program) (outReg : ℕ) (bits : Bits) (W k : ℕ)
    (hk : (run k (compiledInputFullRAM p outReg bits)).pc = codeLenP p)
    (hbare : RunDynLe W k (compiledInputRAM p bits)) :
    RunDynLe W k (compiledInputFullRAM p outReg bits) := by
  intro j hj
  obtain ⟨hr, hm, _, _⟩ := compiledInputRAM_full_agree p outReg bits k hk j (by omega)
  have hcur := compiledInputRAM_full_current_agree p outReg bits k j hk hj
  have hbareDyn := hbare j hj
  unfold DynamicOperandsLe at hbareDyn ⊢
  rw [← hcur, ← hr, ← hm]
  exact hbareDyn

/-- A `BoundedWhile.Program` that decides `L` on the promise domain `D`, reading its
    input through the canonical `bitInputStore (enc x)` loader and leaving its `Bool`
    answer in `outReg`, at a cost polynomial in the encoded input length. -/
@[construction_api] structure BoundedWhileDecider {α : Type} (enc : α → Bits) (D L : α → Prop) where
  /-- The decider program, run against `bitInputStore (enc x)`. -/
  p : Program
  /-- The register `p` leaves its answer in. -/
  outReg : ℕ
  /-- The polynomial-bound exponent/coefficient shared by `cost_le`. -/
  c : ℕ
  /-- `p` decides `L x` correctly for every `x` in the promise domain `D`. -/
  correct : ∀ x, D x → ((p.eval (bitInputStore (enc x))) outReg = 1 ↔ L x)
  /-- `p`'s cost against the loaded input is polynomial in the encoded input length. -/
  cost_le : ∀ x, D x → p.cost (bitInputStore (enc x)) ≤ c * ((enc x).length + 1) ^ c
  /-- The polynomial-bound exponent/coefficient shared by `compiled_operands_le`. -/
  bit_c : ℕ
  /-- The compiled program's dynamic operand bit-lengths stay polynomial in the encoded input
      length — the bit-cost companion to `cost_le` (module docstring). -/
  compiled_operands_le : ∀ x, D x →
    ∃ W, W ≤ bit_c * ((enc x).length + 1) ^ bit_c ∧ CompiledOperandBound p (enc x) W

/-- The `Bool`-valued function a `BoundedWhileDecider` computes on its promise domain. -/
@[construction_api] def BoundedWhileDecider.result {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : {x // D x} → Bool :=
  fun x => decide ((d.p.eval (bitInputStore (enc x.1))) d.outReg = 1)

/-- The obligation that `d.result` be realizable by a polynomial-time `FinTM2` computation.
    This proposition separates the program-level correctness and cost conditions from the
    existence of a finite-stack machine computing the same result. -/
@[construction_api] def BoundedWhileDecider.TMRealizable {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (enc ∘ Subtype.val) encodeBool d.result)


end NPComplete.RAMToTM

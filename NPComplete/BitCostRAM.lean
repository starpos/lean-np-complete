module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Data.Nat.Log

/-!
# Bit-cost RAM machine

This module gives a machine model in which arithmetic operand size contributes directly to
execution cost. Each instruction charges according to the bit-length of its operands, allowing
runtime bounds to account for bit-level work rather than only instruction count.

## Design

* `bitLen n := Nat.log2 n + 1` — binary bit-length; `bitLen 0 = 1`, `bitLen 1 = 1`,
  `bitLen 2 = 2`, `bitLen 4 = 3`, ....
* `Bank := ℕ → ℕ` — either the register file or the memory bank.  Unwritten
  cells default to `0`.
* `Instruction` — a small load / arithmetic / branch / halt set.  Constants are
  inlined via `loadImm`; memory addresses are held in registers.
* `RAM` — machine state: `regs`, `mem`, `pc`, `cost`, and the immutable
  `program`.  `pc` past the program's end reads as `Instruction.halt` (a
  fixed-point instruction).
* `step` — one-step transition; each instruction updates the appropriate bank,
  advances `pc`, and adds its bit-cost to the accumulator.
* `run k r` — iterate `step` at most `k` times; halted states are `run`-stable.

## Cost model

Every instruction charges a base `1` for the fetch / dispatch, plus the sum of
`bitLen` of its actual operands. Control-flow targets in `jump` and `branchIf*`
are program constants and are not charged; for a fixed program, their omission
affects only program-dependent constants, not asymptotic bounds. Notably
`Instruction.halt` charges `0` — so running past the halt is free, and `run k`
for `k` past the effective step count is a plateau in `cost`. The instruction-level
cost is captured by `instructionCost regs mem i` so downstream compilers can
budget compile-time without unfolding the whole `step` match.
-/

@[expose] public section

namespace NPComplete.BitCostRAM

/-! ## Bit-length -/

/-- Binary bit-length: `bitLen 0 = 1` (one bit for the zero numeral), otherwise
    the number of bits needed to represent `n`.  Used as the per-operand cost
    unit throughout the RAM. -/
@[construction_api] def bitLen (n : ℕ) : ℕ := Nat.log2 n + 1

@[simp] lemma bitLen_zero : bitLen 0 = 1 := rfl

@[simp] lemma bitLen_one : bitLen 1 = 1 := rfl

lemma bitLen_pos (n : ℕ) : 0 < bitLen n := by
  unfold bitLen; omega

/-- Bit-length is monotone: larger values need at least as many bits. -/
lemma bitLen_le_of_le {n m : ℕ} (h : n ≤ m) : bitLen n ≤ bitLen m := by
  unfold bitLen
  have : Nat.log2 n ≤ Nat.log2 m := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right h
  omega

/-- Every `n` sits below `2 ^ bitLen n`. -/
lemma lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  unfold bitLen
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h)).mp (Nat.lt_succ_self _)

/-- Conversely, `bitLen n ≤ b` follows from `n < 2 ^ b` for positive `b`. -/
lemma bitLen_le_of_lt_two_pow {n b : ℕ} (hb : 1 ≤ b) (h : n < 2 ^ b) :
    bitLen n ≤ b := by
  unfold bitLen
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simpa using hb
  · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h0)).mpr h
    omega

/-- A polynomial (indeed linear) majorant for `bitLen`, needed to turn a `bitLen`-mentioning `ℕ`
    step-count bound into an actual `Polynomial ℕ` (`Turing.TM2ComputableInPolyTime.time`). -/
@[construction_api] lemma bitLen_le_succ (n : ℕ) : bitLen n ≤ n + 1 := by
  apply bitLen_le_of_lt_two_pow (by omega)
  calc n < 2 ^ n := n.lt_two_pow_self
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bit-length is subadditive. -/
lemma bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b := by
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have hA := bitLen_pos a
  have hB := bitLen_pos b
  apply bitLen_le_of_lt_two_pow (by omega)
  have h1a : (2 : ℕ) ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h1b : (2 : ℕ) ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hm : bitLen a + bitLen b - 1 + 1 = bitLen a + bitLen b := by omega
  have hsplit : (2 : ℕ) ^ (bitLen a + bitLen b - 1) * 2 =
      2 ^ (bitLen a + bitLen b - 1 + 1) := (Nat.pow_succ 2 _).symm
  rw [hm] at hsplit
  omega

/-- Bit-length is submultiplicative. -/
lemma bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have hA := bitLen_pos a
  have hB := bitLen_pos b
  apply bitLen_le_of_lt_two_pow (by omega)
  have h3 : (a + 1) * (b + 1) ≤ 2 ^ bitLen a * 2 ^ bitLen b :=
    Nat.mul_le_mul ha hb
  have h4 : (a + 1) * (b + 1) = a * b + a + b + 1 := by
    rw [Nat.succ_mul, Nat.mul_succ]
    omega
  have hpow : (2 : ℕ) ^ bitLen a * 2 ^ bitLen b = 2 ^ (bitLen a + bitLen b) :=
    (Nat.pow_add 2 _ _).symm
  omega

/-- Bit-length of a power grows linearly in the exponent. -/
lemma bitLen_pow_le (x k : ℕ) : bitLen (x ^ k) ≤ k * bitLen x + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : bitLen (x ^ (k + 1)) ≤ bitLen (x ^ k) + bitLen x := by
        rw [Nat.pow_succ]
        exact bitLen_mul_le _ _
      have h2 : (k + 1) * bitLen x = k * bitLen x + bitLen x := by
        rw [Nat.succ_mul]
      omega

/-! ## Register / memory banks -/

/-- Infinitely-indexed bank of `Nat` cells.  Both the register file and the
    memory of the RAM are `Bank`s.  Unwritten cells default to `0` (below via
    `emptyBank`). -/
@[construction_api] def Bank : Type := ℕ → ℕ

/-- The all-zero initial bank. -/
def emptyBank : Bank := fun _ => 0

/-- Point-update: `bankWrite b addr v` yields the bank that maps `addr` to `v`
    and every other address `a'` to `b a'`. -/
def bankWrite (b : Bank) (addr v : ℕ) : Bank :=
  fun a => if a = addr then v else b a

@[simp] lemma bankWrite_same (b : Bank) (addr v : ℕ) :
    bankWrite b addr v addr = v := by
  simp [bankWrite]

lemma bankWrite_diff (b : Bank) (addr v a : ℕ) (h : a ≠ addr) :
    bankWrite b addr v a = b a := by simp [bankWrite, h]

/-! ## Instruction set

Every operand is either a register index (`Nat`, into `regs`), an immediate
(`Nat`, inlined), or an absolute program-counter target (`Nat`, into
`program`).  Memory addresses are held in registers, so `load` / `store`
name the address by register index.  `halt` is a fixed-point instruction:
`step` on `halt` returns the RAM unchanged and adds zero cost. -/

/-- The RAM instruction set. -/
@[construction_api] inductive Instruction : Type where
  /-- `loadImm rd n` : `regs rd ← n`. -/
  | loadImm : ℕ → ℕ → Instruction
  /-- `move rd rs` : `regs rd ← regs rs`. -/
  | move : ℕ → ℕ → Instruction
  /-- `load rd rAddr` : `regs rd ← mem (regs rAddr)`. -/
  | load : ℕ → ℕ → Instruction
  /-- `store rSrc rAddr` : `mem (regs rAddr) ← regs rSrc`. -/
  | store : ℕ → ℕ → Instruction
  /-- `add rd rs rt` : `regs rd ← regs rs + regs rt`. -/
  | add : ℕ → ℕ → ℕ → Instruction
  /-- `sub rd rs rt` : `regs rd ← regs rs - regs rt` (natural subtraction). -/
  | sub : ℕ → ℕ → ℕ → Instruction
  /-- `mul rd rs rt` : `regs rd ← regs rs * regs rt`. -/
  | mul : ℕ → ℕ → ℕ → Instruction
  /-- `setIfLt rd rs rt` : `regs rd ← if regs rs < regs rt then 1 else 0`. -/
  | setIfLt : ℕ → ℕ → ℕ → Instruction
  /-- `setIfEq rd rs rt` : `regs rd ← if regs rs = regs rt then 1 else 0`. -/
  | setIfEq : ℕ → ℕ → ℕ → Instruction
  /-- `branchIfLt rs rt target` : `pc ← if regs rs < regs rt then target else pc+1`. -/
  | branchIfLt : ℕ → ℕ → ℕ → Instruction
  /-- `branchIfNZ rs target` : `pc ← if regs rs ≠ 0 then target else pc+1`. -/
  | branchIfNZ : ℕ → ℕ → Instruction
  /-- `jump target` : `pc ← target`. -/
  | jump : ℕ → Instruction
  /-- `halt` : fixed-point instruction; `step` on `halt` is a no-op. -/
  | halt : Instruction
  deriving Repr, DecidableEq

attribute [construction_api] instReprInstruction instDecidableEqInstruction

/-! ## RAM state -/

/-- Bit-cost RAM machine state: register / memory banks, program counter,
    accumulated cost, and the immutable program. -/
@[construction_api] structure RAM : Type where
  regs : Bank
  mem : Bank
  pc : ℕ
  cost : ℕ
  program : List Instruction

/-- Initial RAM state for a given program: empty banks, PC at 0, no cost. -/
def initRAM (prog : List Instruction) : RAM :=
  { regs := emptyBank, mem := emptyBank, pc := 0, cost := 0, program := prog }

/-- Current instruction: the program entry at `pc`, or `Instruction.halt` if
    the PC is past the program's end (so out-of-range PCs are stable fixed
    points of `step`). -/
@[construction_api] def RAM.current (r : RAM) : Instruction :=
  r.program.getD r.pc Instruction.halt

/-! ## Per-instruction bit cost

Each instruction's cost is `1` (fetch / dispatch) plus the sum of `bitLen`
applied to each accessed operand value.  `halt` charges `0` — the model
sees `halt` as a stable no-op that stops charging further work. -/

/-- Per-instruction bit-cost as a function of the current register / memory
    banks.  Downstream compilers use this to budget cost accounting without
    unfolding the `step` match. -/
def instructionCost (regs : Bank) (mem : Bank) : Instruction → ℕ
  | Instruction.loadImm _ n => bitLen n + 1
  | Instruction.move _ rs => bitLen (regs rs) + 1
  | Instruction.load _ rAddr => bitLen (regs rAddr) + bitLen (mem (regs rAddr)) + 1
  | Instruction.store rSrc rAddr => bitLen (regs rAddr) + bitLen (regs rSrc) + 1
  | Instruction.add _ rs rt => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.sub _ rs rt => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.mul _ rs rt => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.setIfLt _ rs rt => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.setIfEq _ rs rt => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.branchIfLt rs rt _ => bitLen (regs rs) + bitLen (regs rt) + 1
  | Instruction.branchIfNZ rs _ => bitLen (regs rs) + 1
  | Instruction.jump _ => 1
  | Instruction.halt => 0

/-! ## Single-step transition -/

/-- Execute one instruction: update the appropriate bank, advance `pc`, and add
    the instruction's bit cost.  `Instruction.halt` is a fixed point (no state
    or PC change, zero cost). -/
def step (r : RAM) : RAM :=
  let c := instructionCost r.regs r.mem r.current
  match r.current with
  | Instruction.loadImm rd n =>
      { r with regs := bankWrite r.regs rd n,
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.move rd rs =>
      { r with regs := bankWrite r.regs rd (r.regs rs),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.load rd rAddr =>
      { r with regs := bankWrite r.regs rd (r.mem (r.regs rAddr)),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.store rSrc rAddr =>
      { r with mem := bankWrite r.mem (r.regs rAddr) (r.regs rSrc),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.add rd rs rt =>
      { r with regs := bankWrite r.regs rd (r.regs rs + r.regs rt),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.sub rd rs rt =>
      { r with regs := bankWrite r.regs rd (r.regs rs - r.regs rt),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.mul rd rs rt =>
      { r with regs := bankWrite r.regs rd (r.regs rs * r.regs rt),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.setIfLt rd rs rt =>
      { r with regs := bankWrite r.regs rd
                        (if r.regs rs < r.regs rt then 1 else 0),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.setIfEq rd rs rt =>
      { r with regs := bankWrite r.regs rd
                        (if r.regs rs = r.regs rt then 1 else 0),
               pc := r.pc + 1, cost := r.cost + c }
  | Instruction.branchIfLt rs rt target =>
      { r with pc := if r.regs rs < r.regs rt then target else r.pc + 1,
               cost := r.cost + c }
  | Instruction.branchIfNZ rs target =>
      { r with pc := if r.regs rs ≠ 0 then target else r.pc + 1,
               cost := r.cost + c }
  | Instruction.jump target =>
      { r with pc := target, cost := r.cost + c }
  | Instruction.halt => r

/-! ## Iterated run

`run k r` executes at most `k` steps starting from `r`.  Because `Instruction.halt`
is a fixed point of `step`, extending `k` past the effective step count is a
no-op — `cost` plateaus and the machine state stays put. -/

/-- Iterated step: `run k r` executes at most `k` steps. -/
@[construction_api] def run : ℕ → RAM → RAM
  | 0, r => r
  | k+1, r => run k (step r)

/-! ## Sanity lemmas -/

@[simp] lemma run_zero (r : RAM) : run 0 r = r := rfl

@[simp] lemma run_succ (k : ℕ) (r : RAM) : run (k+1) r = run k (step r) := rfl

/-- Iteration is left-associative: peeling one step from the outside equals
    running `k` steps first then stepping once more. -/
lemma run_succ_right (k : ℕ) (r : RAM) : run (k+1) r = step (run k r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => rw [run_succ]; rw [ih]; rfl

/-- `Instruction.halt` is a fixed point of `step`: state and cost stay put. -/
@[simp] lemma step_halt (r : RAM) (hh : r.current = Instruction.halt) :
    step r = r := by
  simp [step, hh]

/-- A `halt`ed RAM is stable under `run`. -/
lemma run_halted (r : RAM) (hh : r.current = Instruction.halt) (k : ℕ) :
    run k r = r := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run_succ, step_halt r hh]; exact ih

/-! ## Cost monotonicity -/

/-- One `step` never decreases `cost`. -/
lemma cost_step_ge (r : RAM) : r.cost ≤ (step r).cost := by
  simp only [step]
  cases hcur : r.current <;> simp

/-- `run k` never decreases `cost`. -/
@[construction_api] lemma cost_run_ge (k : ℕ) (r : RAM) : r.cost ≤ (run k r).cost := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      rw [run_succ]
      exact le_trans (cost_step_ge r) (ih (step r))

/-- `step` adds exactly the current instruction's bit cost — true even for `halt`, since
    `instructionCost` charges `0` there and `step` fixes `halt` states. -/
lemma cost_step_eq_add (r : RAM) :
    (step r).cost = r.cost + instructionCost r.regs r.mem r.current := by
  simp only [step]
  cases hc : r.current <;> simp [instructionCost]

/-- Every non-`halt` instruction charges at least `1` (the fetch/dispatch unit every
    `instructionCost` branch adds on top of its operand costs). -/
lemma instructionCost_pos (regs mem : Bank) {i : Instruction} (hi : i ≠ Instruction.halt) :
    1 ≤ instructionCost regs mem i := by
  cases i <;> simp_all [instructionCost]

end NPComplete.BitCostRAM

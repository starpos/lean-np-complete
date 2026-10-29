module

public import NPComplete.BitCostRAM
public import NPComplete.RAMToTM.Generic.Machine.MemoryStore2
public import NPComplete.RAMToTM.Generic.Machine.MemoryLoad
public import NPComplete.RAMToTM.Generic.Machine.DigitAdd
public import NPComplete.RAMToTM.Generic.Machine.DigitSub
public import NPComplete.RAMToTM.Generic.Machine.Binary
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Generic machine for a fixed `BitCostRAM` program

A finite-stack machine needs finite register, symbol, and control-state types. This module derives
those types from a fixed instruction list, so each program's machine shape is explicit in its type.

`Kg p`, `Γg p`, `PhaseOf`, and `Λg p` define the stack, alphabet, and control-state types from `p`.
The shared instruction state is one product across all program positions: only one instruction is
active at a time, so its local state can reuse the same product fields. A per-position sum would
require total lenses into states absent at that position. Scratch stacks likewise form a fixed
finite set reused at every instruction site.

Every non-halt instruction has a finite local phase type. The explicit `halt` constructor maps to
`Empty`, because the dispatcher exits to cleanup rather than entering an `exec` phase.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym Store2Phase LoadState AddState SubState
  WriteLog lookupD encodeLog natToDigits)

/-- Register indices an instruction reads or writes (excludes jump targets and immediates,
    which never index a register stack). -/
def regsOf : Instruction → List ℕ
  | .loadImm rd _ => [rd]
  | .move rd rs => [rd, rs]
  | .load rd rAddr => [rd, rAddr]
  | .store rSrc rAddr => [rSrc, rAddr]
  | .add rd rs rt => [rd, rs, rt]
  | .sub rd rs rt => [rd, rs, rt]
  | .mul rd rs rt => [rd, rs, rt]
  | .setIfLt rd rs rt => [rd, rs, rt]
  | .setIfEq rd rs rt => [rd, rs, rt]
  | .branchIfLt rs rt _ => [rs, rt]
  | .branchIfNZ rs _ => [rs]
  | .jump _ => []
  | .halt => []

/-- Number of dedicated register stacks a program needs: one more than the largest register
    index it names, so `Fin (regBound p)` covers every register `p` touches. -/
def regBound (p : List Instruction) : ℕ :=
  1 + (p.flatMap regsOf).foldr max 0

lemma le_foldr_max_of_mem (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l' ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1; omega
    · exact le_trans (ih h1) (le_max_right _ _)

/-- Every register an instruction at position `pc` names is within `p`'s dedicated register
    stacks: the site dispatcher uses this to turn an `Instruction` operand (a raw `ℕ`) into
    the `Fin (regBound p)` value `storeProg`/`loadProg`/`addProg` expect. -/
def regAt (p : List Instruction) (pc : Fin p.length) (r : ℕ) (hr : r ∈ regsOf (p.get pc)) :
    Fin (regBound p) :=
  ⟨r, by
    have hmem : r ∈ p.flatMap regsOf := List.mem_flatMap.mpr ⟨p.get pc, List.get_mem p pc, hr⟩
    have hbound := le_foldr_max_of_mem _ r hmem
    simp only [regBound]; omega⟩


attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `load`'s local phase space for the register-index-generalized realization
    (`GenericLoad.lean`): `MemoryLoad.Phase2` plus a `clearDest` phase inserted between
    `copyQueryRestore` and `compareAddr`. `MemoryLoad.lean`'s `prog2` assumes the destination
    register starts empty (true only for its own fixed vertical-slice program); an arbitrary
    site's destination register may already hold a stale value (or, if `rDest = rAddr`, is the
    very register `copyQueryRestore` just restored), so it must be drained to `[]` explicitly
    before `readValue` pushes the loaded digits onto it. Placed after `copyQueryRestore` since
    nothing from `compareAddr` onward reads
    `rAddr` again (the address is already fully captured in `query`), so draining `rDest` here
    is alias-safe even when `rDest = rAddr`. -/
inductive LoadPhase
  | copyQuery | copyQueryRestore
  | clearDest
  | compareAddr
  | restoreQuery
  | skipValue
  | readValue
  | restoreMem
  | drainQuery
  | drainQueryTmp
  | done
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `add rd rs rt` snapshots both source registers non-destructively before `clearDest` drains
    `rd`. This ordering makes the phase sequence safe when the destination aliases either source. -/
inductive AddPhase
  | copyLhs | copyLhsRestore
  | reverseLhs
  | copyRhs | copyRhsRestore
  | reverseRhs
  | clearDest
  | addLoop
  | reverseSum
  | done
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `sub`'s local phase space for the register-index-generalized realization (`GenericSub.lean`).
    The non-destructive snapshot prefix (`copyLhs` through `clearDest`) is identical
    to `AddPhase`'s, since `sub rd rs rt` needs the same alias-safe capture of both operands before
    draining `rd`. What follows differs from `add`'s single `reverseSum`: `subLoop` (mirroring
    `addLoop`, but stopping once *both* operands are exhausted regardless of the pending borrow —
    `DigitSub.subRawFull`'s own termination discipline, module docstring there) leaves the raw,
    possibly-non-canonical difference on `diffScratch` plus a final borrow bit. A live final borrow
    means underflow (`regs rs < regs rt`, RAM truncates to `0`): `drainDiff` discards the raw digits
    without ever touching `rd` (already empty from `clearDest`). No borrow means the raw digits are
    the true difference, but may carry new most-significant zero digits (`100 - 99 = 1`) that
    `addRaw` never has to worry about (`DigitAdd.addRaw_getLast_ne_zero` has no `sub` analogue):
    `skipZeros` discards a leading run of zero digits until the first nonzero (writing it directly
    to `rd`, the new most-significant digit) or exhausting `diffScratch` entirely (`rd` stays empty,
    i.e. the difference was exactly `0`); `copyRest` then finishes copying whatever remains
    verbatim, mirroring `reverseSum`'s unconditional drain. -/
inductive SubPhase
  | copyLhs | copyLhsRestore
  | reverseLhs
  | copyRhs | copyRhsRestore
  | reverseRhs
  | clearDest
  | subLoop
  | drainDiff
  | skipZeros
  | copyRest
  | done
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `mul`'s local phase space for the register-index-generalized realization (`GenericMul.lean`).
    Long multiplication uses a fused Horner-scheme loop, not a materialized-row-then-add.
    `copyLhs` through
    `clearDest` mirror `AddPhase`'s non-destructive snapshot prefix for `rs`, but `copyRhs` needs
    only *one* reversal (`copyRhs`/`copyRhsRestore`, no `reverseRhs`): the multiplier must be read
    MSB-first (Horner processes the most-significant digit first), and a single pop-then-push
    pass over a LSB-first register already yields MSB-first order on the target scratch, which is
    exactly what `add`/`sub`'s own `workRev` intermediate looks like before *their* second
    reversal — `mul` simply stops there instead of reversing back. Each outer iteration
    (`nextDigit`) pops one multiplier digit into `factor`, shifts the live accumulator (held
    directly in register `rd` itself, needing no dedicated accumulator scratch) left by one
    position via a single `push default`, then `mulAddLoop` ripples `mulAddDigit` in lockstep over
    `lhsOperand` (the persistent copy of `rs`, non-destructively re-read every iteration) and `rd`
    (the shifted accumulator), pushing onto `sumScratch` while simultaneously stashing each popped
    `lhsOperand` digit onto `copyScratch` for `restoreLhs` to replay back — mirroring
    `copyLhs`/`copyLhsRestore`'s own restore-via-intermediate-reversal shape, just nested inside
    the outer loop. `skipZeros`/`copyRest` trim `sumScratch`'s MSB-first raw output and relocate it
    onto the now-empty `rd`, exactly as `SubPhase`'s own trailing pair does, then loop back to
    `nextDigit`. `drainLhs` empties the now-unneeded `lhsOperand` once the multiplier is
    exhausted, the only cleanup `SubPhase.clearDest`'s alias-safety argument doesn't already cover
    (there is no `rhsOperand` scratch left over, since the multiplier was consumed digit-by-digit
    directly off `rhsOperand` itself). -/
inductive MulPhase
  | copyLhs | copyLhsRestore
  | reverseLhs
  | copyRhs | copyRhsRestore
  | clearDest
  | nextDigit
  | mulAddLoop
  | restoreLhs
  | skipZeros
  | copyRest
  | drainLhs
  | done
  deriving DecidableEq, Fintype

/-- `mul`'s own multiply-accumulate scratch: `a`/`b` are the transient "just popped"
    digits reused sequentially across every `MulPhase` that pops a single stack (mirroring
    `AddState.a`/`SubState.a`'s reuse convention) — `a` alone during the single-operand phases
    (`copyLhs`/`copyRhs`/`restoreLhs`/`skipZeros`/`copyRest`/`drainLhs`), both `a` (`lhsOperand`)
    and `b` (`rd`, the shifted accumulator) during `mulAddLoop`'s lockstep pop, matching
    `AddState`'s own `a`/`b` roles in `addLoop`. `factor` (the current multiplier digit) and
    `carry` (the running multiply-accumulate carry) persist across `mulAddLoop`'s many steps, so —
    unlike `a`/`b` — each needs its own non-transient field (`GenericProgramMachine.lean`'s
    "spans multiple phases ⇒ dedicated field" principle), and neither is `Option` since both
    always hold a meaningful `Digit` for `mulAddLoop`'s whole duration. -/
structure MulState where
  a : Option Digit
  b : Option Digit
  factor : Digit
  carry : Digit
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `jump`/`branchIfNZ`'s local phase space: both instructions' whole effect fits in
    one `Turing.TM2.Stmt` tree with no internal `goto` (`jump` is exactly one `bridgeTo`;
    `branchIfNZ` is one `peek` + `branch` immediately followed by two `bridgeTo`s), so no distinct
    phase names are needed beyond a single entry point — unlike `store`/`load`/`add`, which loop
    over variable-length digit lists and thus need internal labels to re-enter. -/
inductive CtrlPhase | entry deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `move rd rs`'s local phase space. To handle `rd = rs`, it captures `rs` safely with
    `copySrc`/`copySrcRestore` before draining `rd` in `clearDest`; this makes the alias a no-op
    without a case split. A separate `AddPhase.reverseLhs`-style scratch phase is unnecessary:
    `reverseCopy` rebuilds `rd` directly from the saved copy. -/
inductive MovePhase
  | copySrc | copySrcRestore
  | clearDest
  | reverseCopy
  | done
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- `loadImm rd n`'s local phase space: `n`'s digits are a statically-known (once
    `n` is fixed) finite list, materialized by a plain `List.foldr`-built `push` chain with no
    internal `goto` of its own — the only genuine loop is draining whatever `rd` already holds
    (`drain`, unbounded at proof time since it depends on runtime register content), reusing
    `store`/`move`'s "pop discarding the old digit" shape. `done` is the fixed exit every
    per-instruction local machine needs (`Ml done = halt`, `StmtTransport`'s requirement). -/
inductive LoadImmPhase | drain | done deriving DecidableEq, Fintype

/-- The comparison scratch state shared by `setIfLt`/`setIfEq`/`branchIfLt`'s multi-digit
    compare core (`GenericCompare.lean`): `left`/`right` hold whatever digit was just
    popped/peeked from the two operand registers (or, after the compare is done, are free for
    an instruction's own post-compare phases to repurpose — e.g. `left` as a generic popped-digit
    scratch, mirroring `AllInstrState.decision`'s "transient, no cross-checkpoint meaning" reuse
    principle), `acc` is the running/final `Ordering`. Defined here (not in `GenericCompare.lean`)
    since `AllInstrState` below needs it as a field type, and `GenericCompare.lean` imports this
    file, not the reverse. -/
structure CompareState where
  left : Option Digit
  right : Option Digit
  acc : Ordering
  deriving DecidableEq, Fintype

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- The shared comparison sub-automaton's local phases (`GenericCompare.lean`'s
    `compareCoreProg`), embedded into each of `setIfLt`/`setIfEq`/`branchIfLt`'s own phase type
    via a `compare : CompareCorePhase → ...Phase` constructor — `done` is the fixed exit every
    per-instruction local machine needs (`Ml done = halt`, `StmtTransport`'s requirement),
    matching every other standalone local program in this codebase (`AddPhase.done`,
    `MovePhase.done`, ...). -/
inductive CompareCorePhase | scan | drainLeft | drainRight | restoreLeft | restoreRight | done
  deriving DecidableEq, Fintype

/-- `setIfLt rd rs rt`'s local phase space: the shared `compare` core determines
    `Ordering`, then `clearDest` drains whatever `rd` holds (mirroring `AddPhase.clearDest`,
    alias-safe against `rd = rs`/`rd = rt` since the compare core has already restored `rs`/`rt`
    and no longer reads them), then `writeResult` pushes a single `1` digit iff the comparison
    was `.lt` (nothing, i.e. `0`, otherwise). -/
inductive SetIfLtPhase
  | compare : CompareCorePhase → SetIfLtPhase
  | clearDest
  | writeResult
  | done
  deriving DecidableEq, Fintype

/-- `setIfEq rd rs rt`'s local phase space: identical shape to `SetIfLtPhase`, only
    `writeResult`'s condition differs (`.eq` instead of `.lt`). -/
inductive SetIfEqPhase
  | compare : CompareCorePhase → SetIfEqPhase
  | clearDest
  | writeResult
  | done
  deriving DecidableEq, Fintype

/-- `branchIfLt rs rt target`'s local phase space: no register write, so nothing
    beyond the shared `compare` core is needed. Sequential instruction-site code uses the uniform
    `bridgeTo p (pc.1+1)`, but `done`'s site-level code branches on the compare core's `acc` to
    choose `bridgeTo p target` or `bridgeTo p (pc.1+1)`. This mirrors `branchIfNZ`'s
    `CtrlPhase.entry` branch (`GenericBranch.lean`), but only after the comparison finishes rather
    than in a single atomic tree. -/
inductive BranchIfLtPhase
  | compare : CompareCorePhase → BranchIfLtPhase
  | done
  deriving DecidableEq, Fintype

/-- The local phase type for an instruction kind, ignoring its register operands. The instruction
    constructor determines the phase space; `Empty` is used for `halt`, which exits via cleanup. -/
def PhaseOf : Instruction → Type
  | .store _ _ => Store2Phase
  | .load _ _ => LoadPhase
  | .add _ _ _ => AddPhase
  | .sub _ _ _ => SubPhase
  | .mul _ _ _ => MulPhase
  | .move _ _ => MovePhase
  | .loadImm _ _ => LoadImmPhase
  | .jump _ => CtrlPhase
  | .branchIfNZ _ _ => CtrlPhase
  | .setIfLt _ _ _ => SetIfLtPhase
  | .setIfEq _ _ _ => SetIfEqPhase
  | .branchIfLt _ _ _ => BranchIfLtPhase
  | _ => Empty

instance instFintypePhaseOf (i : Instruction) : Fintype (PhaseOf i) := by
  cases i <;> first | exact (inferInstance : Fintype Store2Phase)
                    | exact (inferInstance : Fintype LoadPhase)
                    | exact (inferInstance : Fintype AddPhase)
                    | exact (inferInstance : Fintype SubPhase)
                    | exact (inferInstance : Fintype MulPhase)
                    | exact (inferInstance : Fintype MovePhase)
                    | exact (inferInstance : Fintype LoadImmPhase)
                    | exact (inferInstance : Fintype CtrlPhase)
                    | exact (inferInstance : Fintype SetIfLtPhase)
                    | exact (inferInstance : Fintype SetIfEqPhase)
                    | exact (inferInstance : Fintype BranchIfLtPhase)
                    | exact (inferInstance : Fintype Empty)

instance instDecidableEqPhaseOf (i : Instruction) : DecidableEq (PhaseOf i) := by
  cases i <;> first | exact (inferInstance : DecidableEq Store2Phase)
                    | exact (inferInstance : DecidableEq LoadPhase)
                    | exact (inferInstance : DecidableEq AddPhase)
                    | exact (inferInstance : DecidableEq SubPhase)
                    | exact (inferInstance : DecidableEq MulPhase)
                    | exact (inferInstance : DecidableEq MovePhase)
                    | exact (inferInstance : DecidableEq LoadImmPhase)
                    | exact (inferInstance : DecidableEq CtrlPhase)
                    | exact (inferInstance : DecidableEq SetIfLtPhase)
                    | exact (inferInstance : DecidableEq SetIfEqPhase)
                    | exact (inferInstance : DecidableEq BranchIfLtPhase)
                    | exact (inferInstance : DecidableEq Empty)

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- Scratch stacks private to some instruction's realization, reused by *every* program
    position that runs that instruction (not one copy per position): only one instruction is
    ever mid-computation, so simultaneous use across positions never happens. `workRev` is
    itself reused sequentially within a single `add` (first for `rs`'s reversed snapshot, then
    for `rt`'s), while `lhsOperand`/`rhsOperand` must be two distinct stacks since `addLoop`
    needs both operands live at once. `diffScratch` is `sub`'s own analogue of
    `sumScratch`, holding the raw (possibly non-canonical) ripple-borrow difference before
    `SubPhase.skipZeros`/`copyRest` trim and relocate it to `rd`. -/
inductive ScratchKind
  | copyScratch | query | queryTmp | logTmp | workRev | lhsOperand | rhsOperand | sumScratch
  | diffScratch
  /-- The prologue's own running address counter, LSB-first like every register:
      holds `natToDigits i` while scanning bit `i` of `Kg.io`, non-destructively copied onto
      `Kg.mem` (mirroring `Store2Phase.copyAddr`'s restore-via-scratch trick) whenever a `true`
      bit needs an entry, and destructively drained into the final length entry once `Kg.io` is
      exhausted. -/
  | prologueCounter
  /-- The prologue's transient copy/increment scratch: reused both by
      `prologueCounter`'s non-destructive-copy restore pass (mirroring every other instruction's
      `copyScratch`) and by the increment ripple-carry pass that computes `prologueCounter + 1`
      between bits. -/
  | prologueWork
  deriving DecidableEq, Fintype

/-- Every scratch stack holds `Digit` except `logTmp`, a saved slice of the memory write-log. -/
abbrev ScratchΓ : ScratchKind → Type
  | .logTmp => MemSym
  | _ => Digit

instance (s : ScratchKind) : Fintype (ScratchΓ s) := by cases s <;> infer_instance
instance (s : ScratchKind) : DecidableEq (ScratchΓ s) := by cases s <;> infer_instance

/-- The stacks a machine for program `p` needs: one per register `p` names, the shared memory
    write-log, a `Bool` input/output channel (unused until the prologue/cleanup wiring
    loads bit input into it / writes the output bit to it), and the fixed scratch enum. -/
inductive Kg (p : List Instruction)
  | reg : Fin (regBound p) → Kg p
  | mem : Kg p
  | io : Kg p
  | scratch : ScratchKind → Kg p
  deriving DecidableEq, Fintype

abbrev Γg (p : List Instruction) : Kg p → Type
  | .reg _ => Digit
  | .mem => MemSym
  | .io => Bool
  | .scratch s => ScratchΓ s

instance (p : List Instruction) (k : Kg p) : Fintype (Γg p k) := by cases k <;> infer_instance
instance (p : List Instruction) (k : Kg p) : DecidableEq (Γg p k) := by cases k <;> infer_instance

attribute [local implicit_reducible] Multiset.Nodup Multiset.ofList in
/-- The prologue's phase space: scan `Kg.io`
    one bit at a time, maintaining a running LSB-first address counter
    (`ScratchKind.prologueCounter`) that tracks how many bits have been consumed so far, and emit
    a write-log entry `(i+1, 1)` onto `Kg.mem` for every `true` bit `i` — building exactly
    `inputLogRev` (`GenericPrologue.lean`).
    - `scanInput`: pop one bit off `Kg.io`; `none` (input exhausted) moves to `writeLength`,
      `some b` stashes `b` in `AllInstrState.prologue.bit` and moves to `incPop`.
    - `incPop`/`incCopyRest`/`incRestore`: increment `prologueCounter` by `1` regardless of `b`
      (the address advances for every bit, not just `true` ones), via `prologueWork` as a
      temporary buffer — `incPop` ripples a carry through `15`-digits (mirroring
      `DigitAdd.addDigits`'s carry rule) until it finds a digit to bump or the counter runs out
      (pushing a fresh `1` digit, i.e. a new most-significant digit), `incCopyRest` copies
      whatever's left verbatim once the carry is spent, `incRestore` copies `prologueWork` back
      onto `prologueCounter` (undoing the pop-then-push reversal, exactly
      `Store2Phase.copyValueRestore`'s shape) and then dispatches on the stashed `bit`: `true`
      continues to `emitTrue`, `false` loops back to `scanInput`.
    - `emitTrue`/`emitAddr`/`emitAddrRestore`: push the entry's fixed `entryEnd`/`digit 1`
      /`addrEnd` markers (the value field is always the single digit `1`), then non-destructively
      copy `prologueCounter`'s digits onto `Kg.mem` (`emitAddr`/`emitAddrRestore`, the same
      copy-while-pushing-then-restore shape `incPop`/`incRestore` already use) before looping back
      to `scanInput` — `push` always prepending turns this LSB-first read into the MSB-first field
      `encodeEntry` needs, with no separate reversal pass (`MemoryEncoding.lean`'s module
      docstring). -/
inductive ProloguePhase
  | scanInput
  | incPop | incCopyRest | incRestore
  | emitTrue
  | emitAddr | emitAddrRestore
  | writeLength
  | done
  deriving DecidableEq, Fintype

/-- Cleanup's phase space: check the decider's output register denotes
    exactly `1` (`checkHead`/`checkTail`, via `AllInstrState.decision`), push that bit as the
    machine's answer, then drain every stack `Represents` requires empty at a checkpoint before
    halting. Deliberately drains *every* register including the output one (rather than trying
    to skip it) — `outReg`'s own value is checked, not assumed already fully consumed, so a
    malformed (non-`0`/`1`) decider output still leaves cleanup itself total. `outReg` is *not*
    a parameter of this type (only of `Generic.cleanupProg`, which realizes it): a given `p`'s
    `Λg p`/`entryAt`/`bridgeTo`/`Represents` must stay independent of which register some
    particular decider instance answers through, so only the *phase space*'s shape (which does
    depend on `p`, via `regBound p`) lives here.
    - `checkHead`/`checkTail`: pop `outReg`'s two possible digits; `decision` ends up `true`
      exactly when the popped sequence was the singleton `[1]` (`checkHead` sets it from the
      first pop, `checkTail` `&&`s in "the second pop was `none`").
    - `pushAnswer`: push `decision` onto `Kg.io` once (prologue leaves `io` empty, so no encoding
      is needed) — the machine's sole output bit.
    - `drainReg cursor`: drains register `cursor.val` (when in range) to empty via a self-loop,
      then advances `cursor`; `cursor = ⟨regBound p, _⟩` (out of range) signals every register
      drained, falling through to `drainMem`.
    - `drainMem`/`drainScratch s`: the same self-loop-then-advance shape for `Kg.mem` and each
      `ScratchKind` in turn (`nextScratchKind`'s fixed chain), so every stack is drained
      before halt. -/
inductive CleanupPhase (p : List Instruction)
  | checkHead | checkTail | pushAnswer
  | drainReg (cursor : Fin (regBound p + 1))
  | drainMem
  | drainScratch (s : ScratchKind)
  | done
  deriving DecidableEq, Fintype

/-- The fixed chain that `drainScratch` follows visits every `ScratchKind`. After the last kind,
    `nextScratchKind` returns `none` and control passes to `CleanupPhase.done`. -/
def nextScratchKind : ScratchKind → Option ScratchKind
  | .copyScratch => some .query
  | .query => some .queryTmp
  | .queryTmp => some .logTmp
  | .logTmp => some .workRev
  | .workRev => some .lhsOperand
  | .lhsOperand => some .rhsOperand
  | .rhsOperand => some .sumScratch
  | .sumScratch => some .diffScratch
  | .diffScratch => some .prologueCounter
  | .prologueCounter => some .prologueWork
  | .prologueWork => none

/-- Labels are site-dependent (unlike `σg`): each program position `pc` gets its own copy of
    that position's instruction's phase space, plus the shared prologue/cleanup phases. A
    `done`-bridge for position `pc` `goto`s `exec target _` / `exec ⟨pc+1,_⟩ _` for the RAM's
    (possibly backward) next-PC, or `cleanup` when that next PC is out of range or names an
    explicit `halt` — mirroring `BitCostRAM.RAM.current`'s out-of-range-is-halt convention, so
    no separate fetch-decode dispatch loop is needed. -/
inductive Λg (p : List Instruction)
  | exec : (pc : Fin p.length) → PhaseOf (p.get pc) → Λg p
  | prologue : ProloguePhase → Λg p
  | cleanup : CleanupPhase p → Λg p
  deriving DecidableEq, Fintype

/-- The prologue's own transient scratch (`ProloguePhase`'s docstring): `bit` holds
    the just-popped `Kg.io` bit across the increment sub-sequence (`incPop`/`incCopyRest`
    /`incRestore`) so `incRestore` can dispatch to `emitTrue` or loop back to `scanInput`;
    `digit` holds the last popped/peeked counter digit during the increment ripple and the
    entry-emission copy, mirroring `store`'s bare `Option Digit` scratch. -/
structure PrologueState where
  bit : Option Bool
  digit : Option Digit
  deriving DecidableEq, Fintype

/-- The shared internal state, fixed across the whole ISA (not per program position): one field
    per *currently realized* instruction kind. Extending realization to another `Instruction`
    constructor adds a field here (and a case to `PhaseOf`), never restructures the existing
    ones. -/
structure AllInstrState where
  store : Option Digit
  load : LoadState
  add : AddState
  /-- `sub`'s own ripple-borrow scratch, mirroring `add`'s `AddState` field —
      structurally identical shape, but a dedicated field per `GenericProgramMachine.lean`'s
      "one field per realized instruction" convention. -/
  sub : SubState
  /-- Transient one-bit decision scratch shared by `branchIfNZ` and cleanup control flow, whose
      `Stmt` trees use a `peek`/`pop` result to route an immediate `branch` or loop-continue
      choice. Never inspected across a `Represents` checkpoint (each use resets it before the tree's
      next `bridgeTo`/loop-back), so unlike `store`/`load`/`add` it needs no lens/orthogonality
      lemmas — and unlike those, it is not dedicated to one instruction, since its disposable bit
      is read only to make the immediate routing choice. -/
  decision : Bool
  /-- `move`'s own popped-digit scratch, mirroring `store`'s bare `Option Digit`:
      every `MovePhase` only ever needs "the digit I just popped", no extra flags. -/
  move : Option Digit
  /-- `loadImm`'s own popped-digit scratch, mirroring `move`: its drain loop only
      needs "the digit I just popped (if any)" to decide whether to keep draining. -/
  loadImm : Option Digit
  /-- `setIfLt`'s own compare-core scratch: the shared `CompareCorePhase` sub-machine
      (`GenericCompare.lean`) reads/writes this field via a dedicated lens while `setIfLt`'s own
      `clearDest`/`writeResult` phases run. -/
  setIfLt : CompareState
  /-- `setIfEq`'s own compare-core scratch, mirroring `setIfLt`. -/
  setIfEq : CompareState
  /-- `branchIfLt`'s own compare-core scratch, mirroring `setIfLt`/`setIfEq` (no
      `clearDest`/`writeResult` needed, only the shared compare core). -/
  branchIfLt : CompareState
  /-- `mul`'s own fused multiply-accumulate scratch, mirroring `add`/`sub`'s own
      `AddState`/`SubState` fields. -/
  mul : MulState
  /-- The prologue's own scratch, mirroring every other per-realization field —
      never inspected outside `Λg.prologue`'s own phases, so it needs no orthogonality lemmas
      against `exec`-site fields (those never touch it, by construction). -/
  prologue : PrologueState
  deriving DecidableEq

/-- The `deriving Fintype` handler searches instances through the deeply nested `Sigma`
    representation of this structure and exceeds the default instance-synthesis size limit,
    so we build the `Fintype` one `Sigma` level at a time with the same proxy equivalence;
    the result is definitionally the derived instance. -/
instance : Fintype AllInstrState := by
  refine @Fintype.ofEquiv AllInstrState _ ?_ (proxy_equiv% AllInstrState)
  repeat' first
    | (intro _)
    | refine @Sigma.instFintype _ _ ?_ ?_
    | exact inferInstance

/-- The state every `done`-bridge resets to before dispatching the next instruction, so a
    position's proof only ever needs "the other fields are canonical", never a chain of
    invariance facts back through every prior instruction. -/
def AllInstrState.canonical : AllInstrState :=
  ⟨none, ⟨none, none, true⟩, ⟨none, none, false⟩, ⟨none, none, false⟩, false, none, none,
    ⟨none, none, .eq⟩, ⟨none, none, .eq⟩, ⟨none, none, .eq⟩, ⟨none, none, default, default⟩,
    ⟨none, none⟩⟩

def AllInstrState.getStore : AllInstrState → Option Digit := (·.store)
def AllInstrState.setStore : AllInstrState → Option Digit → AllInstrState :=
  fun s v => { s with store := v }
def AllInstrState.getLoad : AllInstrState → LoadState := (·.load)
def AllInstrState.setLoad : AllInstrState → LoadState → AllInstrState :=
  fun s v => { s with load := v }
def AllInstrState.getAdd : AllInstrState → AddState := (·.add)
def AllInstrState.setAdd : AllInstrState → AddState → AllInstrState :=
  fun s v => { s with add := v }
def AllInstrState.getSub : AllInstrState → SubState := (·.sub)
def AllInstrState.setSub : AllInstrState → SubState → AllInstrState :=
  fun s v => { s with sub := v }
def AllInstrState.getMove : AllInstrState → Option Digit := (·.move)
def AllInstrState.setMove : AllInstrState → Option Digit → AllInstrState :=
  fun s v => { s with move := v }
def AllInstrState.getLoadImm : AllInstrState → Option Digit := (·.loadImm)
def AllInstrState.setLoadImm : AllInstrState → Option Digit → AllInstrState :=
  fun s v => { s with loadImm := v }
def AllInstrState.getSetIfLt : AllInstrState → CompareState := (·.setIfLt)
def AllInstrState.setSetIfLt : AllInstrState → CompareState → AllInstrState :=
  fun s v => { s with setIfLt := v }
def AllInstrState.getSetIfEq : AllInstrState → CompareState := (·.setIfEq)
def AllInstrState.setSetIfEq : AllInstrState → CompareState → AllInstrState :=
  fun s v => { s with setIfEq := v }
def AllInstrState.getBranchIfLt : AllInstrState → CompareState := (·.branchIfLt)
def AllInstrState.setBranchIfLt : AllInstrState → CompareState → AllInstrState :=
  fun s v => { s with branchIfLt := v }
def AllInstrState.getMul : AllInstrState → MulState := (·.mul)
def AllInstrState.setMul : AllInstrState → MulState → AllInstrState :=
  fun s v => { s with mul := v }
lemma AllInstrState.getStore_setStore : ∀ s a, getStore (setStore s a) = a := fun _ _ => rfl
lemma AllInstrState.setStore_setStore :
    ∀ s a b, setStore (setStore s a) b = setStore s b := fun _ _ _ => rfl
lemma AllInstrState.setStore_getStore : ∀ s, setStore s (getStore s) = s := fun _ => rfl

lemma AllInstrState.getLoad_setLoad : ∀ s a, getLoad (setLoad s a) = a := fun _ _ => rfl
lemma AllInstrState.setLoad_setLoad :
    ∀ s a b, setLoad (setLoad s a) b = setLoad s b := fun _ _ _ => rfl
lemma AllInstrState.setLoad_getLoad : ∀ s, setLoad s (getLoad s) = s := fun _ => rfl

lemma AllInstrState.getAdd_setAdd : ∀ s a, getAdd (setAdd s a) = a := fun _ _ => rfl
lemma AllInstrState.setAdd_setAdd :
    ∀ s a b, setAdd (setAdd s a) b = setAdd s b := fun _ _ _ => rfl
lemma AllInstrState.setAdd_getAdd : ∀ s, setAdd s (getAdd s) = s := fun _ => rfl

lemma AllInstrState.getSub_setSub : ∀ s a, getSub (setSub s a) = a := fun _ _ => rfl
lemma AllInstrState.setSub_setSub :
    ∀ s a b, setSub (setSub s a) b = setSub s b := fun _ _ _ => rfl
lemma AllInstrState.setSub_getSub : ∀ s, setSub s (getSub s) = s := fun _ => rfl

lemma AllInstrState.getMove_setMove : ∀ s a, getMove (setMove s a) = a := fun _ _ => rfl
lemma AllInstrState.setMove_setMove :
    ∀ s a b, setMove (setMove s a) b = setMove s b := fun _ _ _ => rfl
lemma AllInstrState.setMove_getMove : ∀ s, setMove s (getMove s) = s := fun _ => rfl

lemma AllInstrState.getLoadImm_setLoadImm : ∀ s a, getLoadImm (setLoadImm s a) = a :=
  fun _ _ => rfl
lemma AllInstrState.setLoadImm_setLoadImm :
    ∀ s a b, setLoadImm (setLoadImm s a) b = setLoadImm s b := fun _ _ _ => rfl
lemma AllInstrState.setLoadImm_getLoadImm : ∀ s, setLoadImm s (getLoadImm s) = s := fun _ => rfl

lemma AllInstrState.getSetIfLt_setSetIfLt : ∀ s a, getSetIfLt (setSetIfLt s a) = a := fun _ _ => rfl
lemma AllInstrState.setSetIfLt_setSetIfLt :
    ∀ s a b, setSetIfLt (setSetIfLt s a) b = setSetIfLt s b := fun _ _ _ => rfl
lemma AllInstrState.setSetIfLt_getSetIfLt : ∀ s, setSetIfLt s (getSetIfLt s) = s := fun _ => rfl

lemma AllInstrState.getSetIfEq_setSetIfEq : ∀ s a, getSetIfEq (setSetIfEq s a) = a := fun _ _ => rfl
lemma AllInstrState.setSetIfEq_setSetIfEq :
    ∀ s a b, setSetIfEq (setSetIfEq s a) b = setSetIfEq s b := fun _ _ _ => rfl
lemma AllInstrState.setSetIfEq_getSetIfEq : ∀ s, setSetIfEq s (getSetIfEq s) = s := fun _ => rfl

lemma AllInstrState.getBranchIfLt_setBranchIfLt :
    ∀ s a, getBranchIfLt (setBranchIfLt s a) = a := fun _ _ => rfl
lemma AllInstrState.setBranchIfLt_setBranchIfLt :
    ∀ s a b, setBranchIfLt (setBranchIfLt s a) b = setBranchIfLt s b := fun _ _ _ => rfl
lemma AllInstrState.setBranchIfLt_getBranchIfLt :
    ∀ s, setBranchIfLt s (getBranchIfLt s) = s := fun _ => rfl

lemma AllInstrState.getMul_setMul : ∀ s a, getMul (setMul s a) = a := fun _ _ => rfl
lemma AllInstrState.setMul_setMul :
    ∀ s a b, setMul (setMul s a) b = setMul s b := fun _ _ _ => rfl
lemma AllInstrState.setMul_getMul : ∀ s, setMul s (getMul s) = s := fun _ => rfl

/-- Cross-lens orthogonality for `StmtTransport.iterate_bind_step_liftStmt_getO`: each `set` changes only
    its own field. -/
lemma AllInstrState.getLoad_setStore : ∀ s a, getLoad (setStore s a) = getLoad s := fun _ _ => rfl

/-! ## `Represents` and the simulation invariant

The representation statements are parameterized by an abstract dispatcher `M`, so the invariant
can be stated independently of a particular machine witness. The raw `flipBind`-iterate equation
lives in `Prop`; clients can construct the `TM2OutputsInTime` witness when supplying the dispatcher
and its proofs. -/

/-- The initial local phase for an instruction with a nonempty `PhaseOf`; `none` corresponds to
    an empty phase type, as for `halt`. -/
def startPhaseOpt : ∀ i : Instruction, Option (PhaseOf i)
  | .store _ _ => some Store2Phase.pushEntryEnd
  | .load _ _ => some LoadPhase.copyQuery
  | .add _ _ _ => some AddPhase.copyLhs
  | .sub _ _ _ => some SubPhase.copyLhs
  | .mul _ _ _ => some MulPhase.copyLhs
  | .move _ _ => some MovePhase.copySrc
  | .loadImm _ _ => some LoadImmPhase.drain
  | .jump _ => some CtrlPhase.entry
  | .branchIfNZ _ _ => some CtrlPhase.entry
  | .branchIfLt _ _ _ => some (BranchIfLtPhase.compare CompareCorePhase.scan)
  | .setIfLt _ _ _ => some (SetIfLtPhase.compare CompareCorePhase.scan)
  | .setIfEq _ _ _ => some (SetIfEqPhase.compare CompareCorePhase.scan)
  | _ => none

/-- Whether a program position can be dispatched: either its instruction has a realized phase
    (`startPhaseOpt` gives `some`), or it is an explicit `halt` — which needs no realization at
    all, since `entryAt`'s `startPhaseOpt = none` fallback already routes it to `cleanup` exactly
    like an out-of-range PC, and `InstrStepSim`'s own `r.current ≠ Instruction.halt` hypothesis
    means no site ever has to *simulate* a halt step: without this disjunct, a program
    containing an explicit in-range `halt` — semantically identical to just ending there, per
    `RAM.current`'s out-of-range-is-halt convention — could never be `ProgramSupported`). -/
def InstructionSupported (i : Instruction) : Prop :=
  i = Instruction.halt ∨ (startPhaseOpt i).isSome

/-- Every position of `p` names a currently-realized instruction, or an explicit `halt`. -/
def ProgramSupported (p : List Instruction) : Prop :=
  ∀ pc : Fin p.length, InstructionSupported (p.get pc)

/-- `startPhaseOpt` covers every non-`halt` constructor, so `InstructionSupported` holds
    unconditionally — `siteImpl`'s totality (module docstring) means `ProgramSupported` is not
    actually a hypothesis on `p`, just an obligation every `List Instruction` discharges the
    same way. -/
lemma instructionSupported_total (i : Instruction) : InstructionSupported i := by
  cases i <;> simp [InstructionSupported, startPhaseOpt, Option.isSome]

/-- Every `List Instruction` is supported (`instructionSupported_total` at every position) —
    in particular `compile p 0 0` for any `Program p`, so every compiled program has this support
    fact. -/
lemma programSupported_any (p : List Instruction) : ProgramSupported p :=
  fun pc => instructionSupported_total (p.get pc)

/-- Embed a site-local phase into the shared label type `Λg p`, for a site whose instruction is
    known (via `h`) to be some concrete `i` — the site dispatcher constructs each
    instruction's `Stmt` tree once against its own `PhaseOf i`, then uses this to place every
    `goto`/label it emits into `Λg p` without re-deriving the dependent match at every use site.
    The `cast` only ever fires against `h`'s own reflexivity once `i` is unified with `p.get pc`,
    so it reduces away exactly like the plain (non-dependent) embeddings elsewhere in this
    codebase. -/
def execVia (p : List Instruction) (pc : Fin p.length) {i : Instruction} (h : p.get pc = i) :
    PhaseOf i → Λg p :=
  fun ph => Λg.exec pc (cast (congrArg PhaseOf h.symm) ph)

/-- The label a config must be at for RAM PC `target` to be mid-execution of `p`: the start phase
    of the site at `target` if it names a realized instruction, otherwise (out of range, or an
    explicit/unrealized `halt`-equivalent, per `BitCostRAM.RAM.current`'s out-of-range-is-halt
    convention) the cleanup entry (`CleanupPhase.checkHead`). Factored out of `ControlRep` so
    both it and every site's `done`-bridge (`bridgeTo`) share one definition of "where does RAM
    PC `n` land" — deliberately independent of any decider's `outReg` choice
    (`CleanupPhase`'s own docstring), so this definition, `ControlRep`, `bridgeTo`, and
    `Represents` need no `outReg` parameter at all; only `Generic.cleanupProg` (which actually
    realizes `checkHead`'s `Stmt` tree) does. -/
def entryAt (p : List Instruction) (target : ℕ) : Λg p :=
  if h : target < p.length then
    match startPhaseOpt (p.get ⟨target, h⟩) with
    | some ph => Λg.exec ⟨target, h⟩ ph
    | none => Λg.cleanup CleanupPhase.checkHead
  else
    Λg.cleanup CleanupPhase.checkHead

/-- `iterate_bind_step_liftStmt`'s stack conclusion, specialized to the `ιK := id`/`eΓ := fun k =>
    Equiv.refl _` instantiation every site's `InstrImpl.sim` uses (`StmtTransport.lean`'s
    embedding data collapses to identities once there is no separate local `K`): the embedded
    `List.map`/`Equiv.refl` bookkeeping simplifies away, leaving a bare stack equation. -/
lemma stack_eq_of_map_equiv_refl {p : List Instruction} (Sgf Slf : ∀ k, List (Γg p k))
    (hstk : ∀ k, Sgf (id k) = List.map (⇑(Equiv.refl (Γg p k))) (Slf k)) (k : Kg p) :
    Sgf k = Slf k := by
  have hk := hstk k
  simpa using hk

/-- `lookupD` at the just-written address of a freshly-prepended write-log entry: the entry
    itself, ignoring the rest of the log — matching `bankWrite`'s point-update semantics. -/
lemma lookupD_cons_eq (addr val : ℕ) (log : WriteLog) (a : ℕ) (ha : a = addr) :
    lookupD ((addr, val) :: log) a 0 = val := by
  simp [lookupD, List.find?, ha]

/-- `lookupD` at any other address skips the freshly-prepended entry and falls through to the
    rest of the log, unchanged. -/
lemma lookupD_cons_ne (addr val : ℕ) (log : WriteLog) (a : ℕ) (ha : a ≠ addr) :
    lookupD ((addr, val) :: log) a 0 = lookupD log a 0 := by
  simp [lookupD, List.find?, ha.symm]

/-- Casting a `PhaseOf i → X`-typed function along `p.get pc = i` and then applying it to a
    correspondingly-cast argument is the same as applying the original, uncast function — the key
    fact behind building each instruction's `SiteCode` as a *single* cast of a plain
    `Store2Phase`/`LoadPhase`/`AddPhase`-indexed function, rather than casting every individual
    phase value where it is used (which duplicates the cast expression at each use site and
    defeats syntactic rewriting). -/
lemma cast_apply_phaseOf (p : List Instruction) (pc : Fin p.length) {i : Instruction}
    (h : p.get pc = i) {X : Type} (f : PhaseOf i → X) (l : PhaseOf i) :
    (cast (congrArg (fun j => PhaseOf j → X) h.symm) f) (cast (congrArg PhaseOf h.symm) l) = f l := by
  revert h
  generalize hq : p.get pc = q
  intro h
  subst h
  rfl

/-- `entryAt` at a supported site is exactly `execVia` applied to that site's start phase — the
    site dispatcher uses this to seed `InstrImpl.sim`'s initial label without re-deriving
    `entryAt`'s own `if`/`match` at every instruction. -/
lemma entryAt_eq_execVia (p : List Instruction) (pc : Fin p.length) {i : Instruction}
    (h : p.get pc = i) (ph : PhaseOf i) (hstart : startPhaseOpt i = some ph) :
    entryAt p pc.1 = execVia p pc h ph := by
  have hscrut : startPhaseOpt (p.get pc) = some (cast (congrArg PhaseOf h.symm) ph) := by
    revert h
    generalize hq : p.get pc = q
    intro h
    subst h
    rw [hstart]; rfl
  simp only [entryAt, dite_eq_left pc.2, hscrut]
  rfl

/-- Every site's `done`-bridge resets `AllInstrState` to canonical, as required by the `Represents`
    invariant between instructions, and jumps to `entryAt p target`. A sequential instruction uses
    `target := pc.1 + 1`; jump and branch instructions use their respective targets. -/
def bridgeTo (p : List Instruction) (target : ℕ) :
    Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  Turing.TM2.Stmt.load (fun _ => AllInstrState.canonical)
    (Turing.TM2.Stmt.goto (fun _ => entryAt p target))

/-- The label a config must be at for RAM PC `pc` to be mid-execution of `p`: literally
    `entryAt p pc`, spelled out via `Option.some` since `Represents` states it as an equation on
    `cfg.l : Option (Λg p)` rather than on the label type itself. -/
def ControlRep (p : List Instruction) (pc : ℕ) (l : Option (Λg p)) : Prop :=
  l = some (entryAt p pc)

/-- A TM config represents a RAM state: same program, registers/memory/scratch agree (memory
    via *some* write-log the stack decodes to, matching `FiniteStore.lean`'s reference model —
    reachability of `r.mem` from a trace is exactly what makes this representable at all),
    internal state is canonical (the invariant every `done`-bridge restores), and the label
    matches the RAM's current PC via `ControlRep`. -/
def Represents (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) : Prop :=
  r.program = p ∧
  (∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) ∧
  (∃ log : WriteLog, cfg.stk Kg.mem = encodeLog log ∧ ∀ a, lookupD log a 0 = r.mem a) ∧
  cfg.var = AllInstrState.canonical ∧
  (∀ s : ScratchKind, cfg.stk (Kg.scratch s) = []) ∧
  ControlRep p r.pc cfg.l

/-- One "global-machine step" function, folding `TM2.step M` through `Option`, matching every
    per-instruction file's own local `flipBind` (just generalized over `p`/`M`). -/
def flipBindG (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) :
    Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) →
      Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) :=
  fun x => x.bind (Turing.TM2.step M)

/-- One RAM step (assumed non-halting) is realized by some run of the global machine `M`,
    preserving `Represents`. -/
def InstrStepSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) : Prop :=
  ∀ cfg r, Represents p cfg r → r.current ≠ Instruction.halt →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (step r)

/-- The simulation invariant extends to arbitrary run length: after any number of RAM steps,
    some run of `M` reaches a config representing that RAM state. At a halted RAM state
    (`RAM.step`'s fixed point) the `cleanup`-entry label `ControlRep` demands there is simply
    where the represented config already sits — no further TM steps are forced by this
    invariant alone; actually draining into a genuine `halt` is `cleanup`'s own job, outside
    `RunSim`. -/
def RunSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) : Prop :=
  ∀ (k : ℕ) cfg r, Represents p cfg r →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (run k r)

/-- `RunSim` follows from `InstrStepSim` by induction on the RAM step count: at a halted RAM
    state `step` is a no-op (`step_halt`), so the induction hypothesis transports across `run`
    unchanged; otherwise `InstrStepSim` supplies the one extra RAM step, chained onto the
    induction hypothesis's remaining `k` steps via `Function.iterate_add_apply` (the
    "arbitrary run length" half of `RunSim`'s own docstring). -/
lemma runSim_of_instrStepSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (hSim : InstrStepSim p M) :
    RunSim p M := by
  intro k
  induction k with
  | zero => intro cfg r hRep; exact ⟨0, cfg, rfl, hRep⟩
  | succ k ih =>
    intro cfg r hRep
    by_cases hcur : r.current = Instruction.halt
    · obtain ⟨n, cfg', hrun, hRep'⟩ := ih cfg r hRep
      refine ⟨n, cfg', hrun, ?_⟩
      rw [run_succ, step_halt r hcur]; exact hRep'
    · obtain ⟨n1, cfg1, hrun1, hRep1⟩ := hSim cfg r hRep hcur
      obtain ⟨n2, cfg2, hrun2, hRep2⟩ := ih cfg1 (step r) hRep1
      refine ⟨n1 + n2, cfg2, ?_, ?_⟩
      · rw [show n1 + n2 = n2 + n1 from Nat.add_comm _ _, Function.iterate_add_apply,
          hrun1, hrun2]
      · rw [run_succ]; exact hRep2

/-! ## Site-local realization packages

`InstrStepSim`/`RunSim` above state what the *whole* dispatcher `Mg p` must satisfy, but that
dispatcher (`GenericDispatcher.lean`) is itself assembled from one realization per program
position. The following let each site's realization be proved independently of `Mg p`'s own
definition. -/

/-- The `Stmt` tree a site dispatcher installs for one program position, as a function of that
    position's current local phase (only `PhaseOf (p.get pc)`, the site's own instruction kind,
    determines the shape — the site index `pc` only matters for *label targets* inside the tree,
    via `execVia`/`bridgeTo`). -/
abbrev SiteCode (p : List Instruction) (pc : Fin p.length) :=
  PhaseOf (p.get pc) → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState

/-- Dispatcher `M` installs exactly `code` at every label belonging to site `pc`. -/
def SiteAgrees (p : List Instruction) (pc : Fin p.length) (code : SiteCode p pc)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) : Prop :=
  ∀ ph, M (Λg.exec pc ph) = code ph

/-- One RAM step at site `pc` is realized by some run of *any* dispatcher `M` that agrees with
    `code` there — abstracting over `M` (rather than requiring the concrete global dispatcher to
    already exist) is what lets each instruction's `InstrImpl` be proved before `Mg p` itself is
    assembled. -/
def SiteStepSim (p : List Instruction) (pc : Fin p.length) (code : SiteCode p pc) : Prop :=
  ∀ M, SiteAgrees p pc code M → ∀ cfg r, Represents p cfg r → r.pc = pc.1 →
    r.current ≠ Instruction.halt →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (step r)

/-- A proved realization of the instruction at site `pc`: the `Stmt` tree to install, packaged
    with the proof that it correctly simulates one RAM step there. `sim` is stated against
    `SiteStepSim` (an arbitrary agreeing dispatcher) rather than a fixed `InstrStepSim (Mg p)`, so
    constructing this package never has to refer to `Mg p`'s own (later, `GenericDispatcher.lean`)
    definition. -/
structure InstrImpl (p : List Instruction) (pc : Fin p.length) where
  code : SiteCode p pc
  sim : SiteStepSim p pc code

/-! ## Quantitative companions

`SiteStepSim`/`InstrImpl` above only assert *some* run of length `n` simulates a step; the
quantitative bound needs a bound on `n` that can later be aggregated into a single polynomial in
`(initialEncodingLength + cumulativeCost)`. `BitCostRAM.instructionCost` alone is not
enough to bound it: a site that overwrites a register first drains that register's *existing*
content (e.g. `loadImm`'s `drain_loop`, `GenericLoadImm.lean`), whose length `instructionCost` never
charges for (it only charges for the values an instruction *reads*, not the destination it
overwrites). `regSize` below is the potential `S` that closes this gap. Every site realizes its RAM
step in a number of TM2 steps that is *at most quadratic* in `regSize + instructionCost` — `mul`'s
Horner realization (`GenericMul.lean`) is the tightest instance (its outer×inner ripple loops
multiply, not add, the two operand digit lengths) — so a single shared quadratic shape covers every
site without needing a separate polynomial degree per instruction. -/

/-- Total digit-length across every register the program `p` names: the quantitative potential `S`. -/
def regSize (p : List Instruction) (r : RAM) : ℕ :=
  ∑ i : Fin (regBound p), (natToDigits (r.regs i)).length

/-- Every individual register's digit length is at most the total `regSize`. -/
lemma natToDigits_length_le_regSize (p : List Instruction) (r : RAM) (i : Fin (regBound p)) :
    (natToDigits (r.regs i)).length ≤ regSize p r := by
  unfold regSize
  exact Finset.single_le_sum (f := fun j : Fin (regBound p) => (natToDigits (r.regs j)).length)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Quantitative companion to `SiteStepSim`: the same one-RAM-step simulation, but the witness
    step count `n` is additionally bounded by `C * (regSize p r + (cfg.stk Kg.mem).length +
    instructionCost r.regs r.mem r.current + 1)^2` for some site-specific constant `C` — `mul`'s
    realization is quadratic in its own charged cost, so this shape (rather than a linear
    multiple) is the loosest one every site can share. The extra `(cfg.stk Kg.mem).length` term
    (rather than folding memory into `regSize`) is needed because `Represents`'s memory component
    is existential over the write-log (`∃ log, ...`): the same `r.mem` allows arbitrarily padded
    logs, so `load`'s scan length cannot be bounded by a function of `r` alone, only by the
    concrete log length actually present in `cfg`. Every
    other site's proof simply discards this term via `Nat.zero_le`. -/
def BoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (code : SiteCode p pc)
    (C : ℕ) : Prop :=
  ∀ M, SiteAgrees p pc code M → ∀ cfg r, Represents p cfg r → r.pc = pc.1 →
    r.current ≠ Instruction.halt →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (step r) ∧
      n ≤ C * (regSize p r + (cfg.stk Kg.mem).length +
        instructionCost r.regs r.mem r.current + 1) ^ 2

/-- `BoundedSiteStepSim` is strictly stronger than `SiteStepSim`: forgetting the step-count bound
    recovers the qualitative simulation guarantee. -/
lemma siteStepSim_of_boundedSiteStepSim (p : List Instruction) (pc : Fin p.length)
    (code : SiteCode p pc) (C : ℕ) (h : BoundedSiteStepSim p pc code C) :
    SiteStepSim p pc code := by
  intro M hAgrees cfg r hRep hpcEq hcur
  obtain ⟨n, cfg', hrun, hRep', _hbound⟩ := h M hAgrees cfg r hRep hpcEq hcur
  exact ⟨n, cfg', hrun, hRep'⟩

/-- A proved realization of the instruction at site `pc`, quantitatively: `InstrImpl` plus a
    step-count bound on its own `sim` witness. `boundedSim`'s constant `C` is this site's own
    contribution to the whole-run aggregation; `InstrImpl.sim` is recovered via
    `siteStepSim_of_boundedSiteStepSim`, so a `TimedInstrImpl` can substitute for an `InstrImpl`
    wherever the latter is expected. -/
structure TimedInstrImpl (p : List Instruction) (pc : Fin p.length) where
  code : SiteCode p pc
  C : ℕ
  boundedSim : BoundedSiteStepSim p pc code C

/-- Forgetful map: a `TimedInstrImpl` is in particular an `InstrImpl`. -/
def TimedInstrImpl.toInstrImpl (p : List Instruction) (pc : Fin p.length)
    (t : TimedInstrImpl p pc) : InstrImpl p pc where
  code := t.code
  sim := siteStepSim_of_boundedSiteStepSim p pc t.code t.C t.boundedSim

/-! ## Growth-aware companions (aggregation stage)

Aggregating `BoundedSiteStepSim` across many RAM steps needs to know not just the per-step TM time
bound, but how much the potential itself (`regSize` plus the concrete memory-log length) can grow
in one step, so the potential occurring in later steps' time bounds can be re-expressed in terms of
the *initial* potential plus accumulated `instructionCost`. This growth fact must be a conjunct of
the very same existential as the time bound: `Represents`'s memory component is existential over
the write-log, so a growth fact obtained independently could refer to a different (more heavily
padded) `cfg'` than the one the time bound's own witness happens to produce, and the aggregation
needs both facts about one shared witness. -/

/-- Writing a value into one dedicated register stack changes `regSize` by at most that value's
    own digit length: every other register stack is untouched, so the total can only move by the
    difference at that one coordinate, and dropping the (nonnegative) old digit length gives this
    looser, reusable bound. -/
lemma regSize_bankWrite_le (p : List Instruction) (r : RAM) (i : Fin (regBound p)) (v B : ℕ)
    (hv : (natToDigits v).length ≤ B) :
    (∑ j : Fin (regBound p), (natToDigits (bankWrite r.regs i.val v j)).length) ≤
      regSize p r + B := by
  have hkey : ∀ j : Fin (regBound p), j ≠ i →
      (natToDigits (bankWrite r.regs i.val v j)).length = (natToDigits (r.regs j)).length := by
    intro j hj
    have : (j : ℕ) ≠ i.val := fun h => hj (Fin.ext h)
    simp [bankWrite, this]
  unfold regSize
  calc (∑ j : Fin (regBound p), (natToDigits (bankWrite r.regs i.val v j)).length)
      = (∑ j ∈ Finset.univ.erase i, (natToDigits (bankWrite r.regs i.val v j)).length) +
          (natToDigits (bankWrite r.regs i.val v i)).length := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = (∑ j ∈ Finset.univ.erase i, (natToDigits (r.regs j)).length) + (natToDigits v).length := by
        congr 1
        · exact Finset.sum_congr rfl (fun j hj => hkey j (Finset.ne_of_mem_erase hj))
        · simp [bankWrite]
    _ ≤ (∑ j : Fin (regBound p), (natToDigits (r.regs j)).length) + B := by
        have h1 : (∑ j ∈ Finset.univ.erase i, (natToDigits (r.regs j)).length) ≤
            (∑ j : Fin (regBound p), (natToDigits (r.regs j)).length) :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        omega

/-- Quantitative companion to `BoundedSiteStepSim` that additionally bounds, within the same
    witness, how much the combined potential (`regSize` plus the concrete memory-log length) can
    grow across the one step. Also bundles `Kg.io` preservation into the same witness: `io` is
    exclusively prologue/cleanup territory, so every site's own realization
    leaves it untouched, but that fact must ride along with the *same* `cfg'` the time/growth
    bounds are about (`Represents`'s memory component being existential over the write-log means
    a frame fact proved independently could refer to a differently-padded `cfg'`). -/
def GrowingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (code : SiteCode p pc)
    (C G : ℕ) : Prop :=
  ∀ M, SiteAgrees p pc code M → ∀ cfg r, Represents p cfg r → r.pc = pc.1 →
    r.current ≠ Instruction.halt →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (step r) ∧
      cfg'.stk Kg.io = cfg.stk Kg.io ∧
      n ≤ C * (regSize p r + (cfg.stk Kg.mem).length +
        instructionCost r.regs r.mem r.current + 1) ^ 2 ∧
      regSize p (step r) + (cfg'.stk Kg.mem).length ≤
        regSize p r + (cfg.stk Kg.mem).length +
          G * (instructionCost r.regs r.mem r.current + 1)

/-- `GrowingBoundedSiteStepSim` forgetting the growth (and `io`) conjuncts recovers
    `BoundedSiteStepSim`. -/
lemma boundedSiteStepSim_of_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length)
    (code : SiteCode p pc) (C G : ℕ) (h : GrowingBoundedSiteStepSim p pc code C G) :
    BoundedSiteStepSim p pc code C := by
  intro M hAgrees cfg r hRep hpcEq hcur
  obtain ⟨n, cfg', hrun, hRep', _hio, hbound, _hgrowth⟩ := h M hAgrees cfg r hRep hpcEq hcur
  exact ⟨n, cfg', hrun, hRep', hbound⟩

/-- A proved realization of the instruction at site `pc`, quantitatively, plus a growth bound on
    the same witness: `TimedInstrImpl` plus the potential-growth conjunct the run_sim aggregation
    needs. -/
structure GrowingTimedInstrImpl (p : List Instruction) (pc : Fin p.length) where
  code : SiteCode p pc
  C : ℕ
  G : ℕ
  growingSim : GrowingBoundedSiteStepSim p pc code C G

/-- Forgetful map: a `GrowingTimedInstrImpl` is in particular a `TimedInstrImpl`. -/
def GrowingTimedInstrImpl.toTimedInstrImpl (p : List Instruction) (pc : Fin p.length)
    (t : GrowingTimedInstrImpl p pc) : TimedInstrImpl p pc where
  code := t.code
  C := t.C
  boundedSim := boundedSiteStepSim_of_growingBoundedSiteStepSim p pc t.code t.C t.G t.growingSim

/-! ## Aggregating a whole RAM run

`GrowingBoundedSiteStepSim` above bounds one RAM step, site by site. This section aggregates
across an arbitrary run length `k`, at the whole-dispatcher level (`GrowingInstrStepSim`, the
quantitative analog of `InstrStepSim` above), yielding a single cubic polynomial in the initial
potential plus cumulative cost (`BoundedRunSim`, the quantitative analog of `RunSim`). A concrete
dispatcher can instantiate `GrowingInstrStepSim` from the per-site `GrowingTimedInstrImpl`s. -/

/-- Quantitative companion to `InstrStepSim`: one RAM step is realized in TM time at most
    quadratic in the current potential plus instruction cost, and the potential itself grows by
    at most `G` times the instruction cost across that same step — both facts about the same
    witness, mirroring `GrowingBoundedSiteStepSim`'s own reason for bundling the two into one
    existential. -/
def GrowingInstrStepSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C G : ℕ) : Prop :=
  ∀ cfg r, Represents p cfg r → r.current ≠ Instruction.halt →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (step r) ∧
      cfg'.stk Kg.io = cfg.stk Kg.io ∧
      n ≤ C * (regSize p r + (cfg.stk Kg.mem).length +
        instructionCost r.regs r.mem r.current + 1) ^ 2 ∧
      regSize p (step r) + (cfg'.stk Kg.mem).length ≤
        regSize p r + (cfg.stk Kg.mem).length +
          G * (instructionCost r.regs r.mem r.current + 1)

/-- Quantitative companion to `RunSim`: after any number `k` of RAM steps, some run of `M` reaches
    a representing config, in TM time at most cubic in the initial potential plus the RAM's
    cumulative cost over those `k` steps. -/
def BoundedRunSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C : ℕ) : Prop :=
  ∀ (k : ℕ) cfg r, Represents p cfg r →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (run k r) ∧
      cfg'.stk Kg.io = cfg.stk Kg.io ∧
      n ≤ C * (regSize p r + (cfg.stk Kg.mem).length + ((run k r).cost - r.cost) + 1) ^ 3

/-- Additive telescoping form of `boundedRunSim_of_growingInstrStepSim`'s induction: the cumulative
    cost is carried as an additive witness `d` with `(run k r).cost = r.cost + d` (avoiding `Nat`
    subtraction inside the induction), and the step-count bound is stated in the
    strengthened intermediate shape `C * d * (P + a*d + 1)^2` (`a := 2*G+1`) that this induction
    actually telescopes on — the final cubic-in-`(P+Δ+1)` shape is recovered afterward, once, by
    `boundedRunSim_of_growingInstrStepSim`. -/
lemma boundedRunSim_aux (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C G : ℕ)
    (hSim : GrowingInstrStepSim p M C G) :
    ∀ (k : ℕ) cfg r, Represents p cfg r →
      ∃ n cfg' d, (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (run k r) ∧
        cfg'.stk Kg.io = cfg.stk Kg.io ∧
        (run k r).cost = r.cost + d ∧
        n ≤ C * d * (regSize p r + (cfg.stk Kg.mem).length + (2 * G + 1) * d + 1) ^ 2 ∧
        regSize p (run k r) + (cfg'.stk Kg.mem).length ≤
          regSize p r + (cfg.stk Kg.mem).length + 2 * G * d := by
  intro k
  induction k with
  | zero => intro cfg r hRep; exact ⟨0, cfg, 0, rfl, hRep, rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro cfg r hRep
    by_cases hcur : r.current = Instruction.halt
    · obtain ⟨n, cfg', d, hrun, hRep', hio, hcost, hbound, hgrowthFinal⟩ := ih cfg r hRep
      refine ⟨n, cfg', d, hrun, ?_, hio, ?_, hbound, ?_⟩
      · rw [run_succ, step_halt r hcur]; exact hRep'
      · rw [run_succ, step_halt r hcur]; exact hcost
      · rw [run_succ, step_halt r hcur]; exact hgrowthFinal
    · obtain ⟨n1, cfg1, hrun1, hRep1, hio1, hbound1, hgrowth1⟩ := hSim cfg r hRep hcur
      obtain ⟨n2, cfg2, d2, hrun2, hRep2, hio2, hcost2, hbound2, hgrowthFinal2⟩ :=
        ih cfg1 (step r) hRep1
      set P := regSize p r + (cfg.stk Kg.mem).length with hP
      set P1 := regSize p (step r) + (cfg1.stk Kg.mem).length with hP1
      set c := instructionCost r.regs r.mem r.current with hc
      set a := 2 * G + 1 with ha
      set d := c + d2 with hd
      have hcpos : 1 ≤ c := instructionCost_pos r.regs r.mem hcur
      have ha1 : 1 ≤ a := by omega
      refine ⟨n1 + n2, cfg2, d, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show n1 + n2 = n2 + n1 from Nat.add_comm _ _, Function.iterate_add_apply,
          hrun1, hrun2]
      · rw [run_succ]; exact hRep2
      · exact hio2.trans hio1
      · rw [run_succ, hcost2, cost_step_eq_add r]; omega
      · clear hgrowthFinal2
        have hgcd : G * (c + 1) ≤ a * c := by nlinarith
        have hP1le : P1 + a * d2 + 1 ≤ P + a * d + 1 := by
          have h1 : P1 ≤ P + G * (c + 1) := hgrowth1
          nlinarith
        have hn2 : n2 ≤ C * d2 * (P + a * d + 1) ^ 2 := by
          calc n2 ≤ C * d2 * (P1 + a * d2 + 1) ^ 2 := hbound2
            _ ≤ C * d2 * (P + a * d + 1) ^ 2 := by gcongr
        have hcled : c ≤ a * d := by nlinarith
        have hn1 : n1 ≤ C * (P + a * d + 1) ^ 2 := by
          calc n1 ≤ C * (P + c + 1) ^ 2 := hbound1
            _ ≤ C * (P + a * d + 1) ^ 2 := by gcongr
        have hsum : n1 + n2 ≤ C * (1 + d2) * (P + a * d + 1) ^ 2 := by nlinarith
        have hfin : C * (1 + d2) * (P + a * d + 1) ^ 2 ≤ C * d * (P + a * d + 1) ^ 2 := by
          gcongr
          omega
        omega
      · clear hbound1 hbound2 hrun1 hrun2 hio1 hio2 hcost2
        rw [run_succ]
        have hgc : G * (c + 1) ≤ 2 * G * c := by nlinarith
        have hP1le : P1 ≤ P + G * (c + 1) := hgrowth1
        clear hgrowth1
        calc regSize p (run k (step r)) + (cfg2.stk Kg.mem).length
            ≤ P1 + 2 * G * d2 := hgrowthFinal2
          _ ≤ P + 2 * G * d := by nlinarith

/-- A whole-dispatcher quantitative one-step simulation (`GrowingInstrStepSim`)
    aggregates to a quantitative arbitrary-length simulation (`BoundedRunSim`), via
    `boundedRunSim_aux`'s telescoped induction converted to the final cubic shape by
    `P + a*d + 1 ≤ a*(P+d+1)` and `d ≤ P+d+1`. -/
lemma boundedRunSim_of_growingInstrStepSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C G : ℕ)
    (hSim : GrowingInstrStepSim p M C G) :
    BoundedRunSim p M (C * (2 * G + 1) ^ 2) := by
  intro k cfg r hRep
  obtain ⟨n, cfg', d, hrun, hRep', hio, hcost, hbound, -⟩ :=
    boundedRunSim_aux p M C G hSim k cfg r hRep
  refine ⟨n, cfg', hrun, hRep', hio, ?_⟩
  have hΔ : (run k r).cost - r.cost = d := by omega
  rw [hΔ]
  set P := regSize p r + (cfg.stk Kg.mem).length with hP
  set a := 2 * G + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have step1 : P + a * d + 1 ≤ a * (P + d + 1) := by nlinarith
  calc n ≤ C * d * (P + a * d + 1) ^ 2 := hbound
    _ ≤ C * d * (a * (P + d + 1)) ^ 2 := by gcongr
    _ = C * a ^ 2 * (d * (P + d + 1) ^ 2) := by ring
    _ ≤ C * a ^ 2 * ((P + d + 1) * (P + d + 1) ^ 2) := by gcongr; omega
    _ = C * a ^ 2 * (P + d + 1) ^ 3 := by ring

/-! ## Exposing the final potential

`BoundedRunSim` above only uses the potential-growth conjunct `boundedRunSim_aux` derives
internally to bound the TM step count `n`, then discards it. Bounding cleanup's own step count
(`GenericCleanup.lean`'s `cleanup_run_bound`, which drains every register/memory cell present at the
run's end) needs the *final* potential itself — `regSize p (run k r)` (register digit lengths) and
the final memory-log length — not just a bound on how many TM steps got there. The separate
companion (`BoundedRunSimWithGrowth`) keeps `BoundedRunSim` focused on its existing callers, which
only need the step-count bound and would otherwise have to thread an unused conjunct through. -/

/-- `BoundedRunSim`'s companion exposing the final potential: after `k` RAM steps, the combined
    register/memory-log size can only have grown by `2 * G` times the accumulated cost `d` (the
    same telescoping `boundedRunSim_aux` already performs internally, here surfaced instead of
    discarded). -/
def BoundedRunSimWithGrowth (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C G : ℕ) : Prop :=
  ∀ (k : ℕ) cfg r, Represents p cfg r →
    ∃ n cfg', (flipBindG p M)^[n] (some cfg) = some cfg' ∧ Represents p cfg' (run k r) ∧
      cfg'.stk Kg.io = cfg.stk Kg.io ∧
      n ≤ C * (regSize p r + (cfg.stk Kg.mem).length + ((run k r).cost - r.cost) + 1) ^ 3 ∧
      regSize p (run k r) + (cfg'.stk Kg.mem).length ≤
        regSize p r + (cfg.stk Kg.mem).length + 2 * G * ((run k r).cost - r.cost)

/-- `boundedRunSim_of_growingInstrStepSim`'s growth-exposing counterpart: same cubic step-count
    bound, plus the final-potential bound `boundedRunSim_aux` already computes internally. -/
lemma boundedRunSimWithGrowth_of_growingInstrStepSim (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) (C G : ℕ)
    (hSim : GrowingInstrStepSim p M C G) :
    BoundedRunSimWithGrowth p M (C * (2 * G + 1) ^ 2) G := by
  intro k cfg r hRep
  obtain ⟨n, cfg', d, hrun, hRep', hio, hcost, hbound, hgrowth⟩ :=
    boundedRunSim_aux p M C G hSim k cfg r hRep
  have hΔ : (run k r).cost - r.cost = d := by omega
  refine ⟨n, cfg', hrun, hRep', hio, ?_, by rw [hΔ]; exact hgrowth⟩
  rw [hΔ]
  set P := regSize p r + (cfg.stk Kg.mem).length with hP
  set a := 2 * G + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have step1 : P + a * d + 1 ≤ a * (P + d + 1) := by nlinarith
  calc n ≤ C * d * (P + a * d + 1) ^ 2 := hbound
    _ ≤ C * d * (a * (P + d + 1)) ^ 2 := by gcongr
    _ = C * a ^ 2 * (d * (P + d + 1) ^ 2) := by ring
    _ ≤ C * a ^ 2 * ((P + d + 1) * (P + d + 1) ^ 2) := by gcongr; omega
    _ = C * a ^ 2 * (P + d + 1) ^ 3 := by ring

end NPComplete.RAMToTM.Generic

module

public import Mathlib.Data.List.Basic

/-!
# Memory write-log: a scan-based finite representation of an unbounded `Bank`

`BitCostRAM.Bank := ℕ → ℕ` is not finite-support in general, so it cannot be encoded onto a
`Turing.FinTM2` stack directly. Since `store`/`load` address memory *indirectly through a
register* (the address is a runtime value, not a literal baked into the instruction), the set
of addresses touched by a run is not statically known from the program text the way register
indices are — unlike registers (one dedicated stack each, since a fixed program only ever
names finitely many literal register indices), memory needs a genuinely dynamic
representation. The representation is a write-log: each
`store` prepends an `(addr, value)` entry, and a `load` scans from the front for the first
(= most recent) matching address — newest-wins, matching `bankWrite`'s point-update semantics.

This file fixes the pure reference model (a `List (ℕ × ℕ)` and a `List.find?`-based lookup,
independent of any `FinTM2` stack or digit encoding) and proves it agrees with the `Bank` produced
by replaying a store trace. `MemoryLoad.lean` provides the finite-stack program that implements the
lookup while restoring the scanned log.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- A memory write-log, newest entry first: the `(addr, value)` pairs a `FinTM2` stack would
    hold if each `store` instruction pushed a fresh entry onto it. -/
abbrev WriteLog : Type := List (ℕ × ℕ)

/-- Scan-and-restore read with an explicit fallback: the first (= most recent) entry matching
    `addr`, or `default` if `addr` was never written. -/
def lookupD (log : WriteLog) (addr default : ℕ) : ℕ :=
  match log.find? (fun e => e.1 = addr) with
  | some (_, v) => v
  | none => default

/-- Scan-and-restore read, defaulting to `0` — matching `BitCostRAM.emptyBank`. -/
def lookup (log : WriteLog) (addr : ℕ) : ℕ := lookupD log addr 0

end NPComplete.RAMToTM

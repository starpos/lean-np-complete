module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.MemoryLoad
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `load` realized against an arbitrary site's register pair

`MemoryLoad.lean`'s `prog2` realizes `load rd rAddr` against one hardcoded register pair
(`LK.r4`/`LK.r0`) and assumes the destination register `r4` starts empty — true only for its own
fixed vertical-slice program. This file builds `load`'s `Stmt` tree directly against the shared,
program-parametrized `Generic.Kg p` (`GenericProgramMachine.lean`), with the destination/address
registers `rDest`/`rAddr` passed as `Fin (regBound p)` values, following the same "no local `K`,
    no embedding" decision as `GenericStore.lean`.

**`clearDest` (the new phase)**: unlike `store`, `load` *writes* a register (`BitCostRAM.step`'s
`.load` case does `bankWrite r.regs rd (...)`, i.e. `rd`'s content is fully replaced, not
appended to). An arbitrary site's `rDest` may already hold a stale value, so `LoadPhase.clearDest`
drains it to `[]` right after `copyQueryRestore` and before `compareAddr` starts scanning. This is
alias-safe even when `rDest = rAddr`: `copyQuery`/`copyQueryRestore` is a non-destructive
read-restore round trip (`rAddr`'s stack is back to its exact original content once
`copyQueryRestore` exits), and nothing from `compareAddr` onward reads `rAddr`'s stack again (the
address is already fully captured in `query`), so draining whatever `Kg.reg rDest` names at that
point is always exactly "drain the original `rDest` content" — no case split on `rDest = rAddr` is
needed anywhere in the `Stmt` tree or its step lemmas, only in the final bookkeeping of which
    key(s) a given `Function.update` touches.

Proof style: as in `GenericStore.lean`, configs are tracked as a raw `Sg : ∀ k, List (Γg p k)`
rather than named-field helpers; `Function.update` chains are equated via `funext` + `by_cases` on
each relevant key.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym LoadState WriteLog lookupD encodeLog encodeEntry
  natToDigits scanResult natToDigits_injective liftStmt iterate_bind_step_liftStmt scanResult_eq_lookupD)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rDest rAddr : Fin (regBound p))

/-- `load`'s `Stmt` tree at an arbitrary register pair: non-destructively copy `rAddr`'s digits
    into `query` (`copyQuery`/`copyQueryRestore`, `GenericStore.storeProg`'s `copyValue`/
    `copyValueRestore` shape with `emb := id`), drain `rDest` to empty (`clearDest`, new), then
    scan the write-log entry by entry (`compareAddr`/`restoreQuery`/`skipValue`/`readValue`/
    `restoreMem`/`drainQuery`/`drainQueryTmp`) exactly as `MemoryLoad.prog2` does, writing a match
    onto the now-empty `rDest`. -/
def loadProg : LoadPhase → Turing.TM2.Stmt (Γg p) LoadPhase LoadState
  | .copyQuery =>
      pop (Kg.reg rAddr) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push (Kg.scratch .query) (fun s => s.queryDigit.getD default)
            (push (Kg.scratch .copyScratch) (fun s => s.queryDigit.getD default)
              (goto (fun _ => .copyQuery))))
          (goto (fun _ => .copyQueryRestore)))
  | .copyQueryRestore =>
      pop (Kg.scratch .copyScratch) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push (Kg.reg rAddr) (fun s => s.queryDigit.getD default)
            (goto (fun _ => .copyQueryRestore)))
          (goto (fun _ => .clearDest)))
  | .clearDest =>
      pop (Kg.reg rDest) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .compareAddr)))
  | .compareAddr =>
      pop Kg.mem (fun s ov => {s with memSym := ov})
        (branch (fun s => s.memSym.isSome)
          (branch (fun s => (s.memSym.bind MemSym.digit?).isSome)
            (pop (Kg.scratch .query) (fun s ov => {s with queryDigit := ov})
              (push (Kg.scratch .logTmp) (fun s => s.memSym.getD MemSym.entryEnd)
                (branch (fun s => s.queryDigit.isSome)
                  (push (Kg.scratch .queryTmp) (fun s => s.queryDigit.getD default)
                    (load
                      (fun s => {s with equal :=
                        s.equal && (s.memSym.bind MemSym.digit?) = s.queryDigit})
                      (goto (fun _ => .compareAddr))))
                  (load (fun s => {s with equal := false})
                    (goto (fun _ => .compareAddr))))))
            (peek (Kg.scratch .query) (fun s ov => {s with queryDigit := ov})
              (load (fun s => {s with equal := s.equal && s.queryDigit.isNone})
                (push (Kg.scratch .logTmp) (fun s => s.memSym.getD MemSym.entryEnd)
                  (branch (fun s => s.equal)
                    (goto (fun _ => .readValue))
                    (goto (fun _ => .restoreQuery)))))))
          (goto (fun _ => .restoreMem)))
  | .restoreQuery =>
      pop (Kg.scratch .queryTmp) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push (Kg.scratch .query) (fun s => s.queryDigit.getD default)
            (goto (fun _ => .restoreQuery)))
          (goto (fun _ => .skipValue)))
  | .skipValue =>
      pop Kg.mem (fun s ov => {s with memSym := ov})
        (push (Kg.scratch .logTmp) (fun s => s.memSym.getD MemSym.entryEnd)
          (branch (fun s => decide (s.memSym = some MemSym.entryEnd))
            (load (fun s => {s with equal := true}) (goto (fun _ => .compareAddr)))
            (goto (fun _ => .skipValue))))
  | .readValue =>
      pop Kg.mem (fun s ov => {s with memSym := ov})
        (push (Kg.scratch .logTmp) (fun s => s.memSym.getD MemSym.entryEnd)
          (branch (fun s => decide (s.memSym = some MemSym.entryEnd))
            (goto (fun _ => .restoreMem))
            (push (Kg.reg rDest) (fun s => (s.memSym.bind MemSym.digit?).getD default)
              (goto (fun _ => .readValue)))))
  | .restoreMem =>
      pop (Kg.scratch .logTmp) (fun s ov => {s with memSym := ov})
        (branch (fun s => s.memSym.isSome)
          (push Kg.mem (fun s => s.memSym.getD MemSym.entryEnd)
            (goto (fun _ => .restoreMem)))
          (goto (fun _ => .drainQuery)))
  | .drainQuery =>
      pop (Kg.scratch .query) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (goto (fun _ => .drainQuery))
          (goto (fun _ => .drainQueryTmp)))
  | .drainQueryTmp =>
      pop (Kg.scratch .queryTmp) (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (goto (fun _ => .drainQueryTmp))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindLoad :
    Option (Turing.TM2.Cfg (Γg p) LoadPhase LoadState) →
      Option (Turing.TM2.Cfg (Γg p) LoadPhase LoadState) :=
  fun x => x.bind (Turing.TM2.step (loadProg rDest rAddr))

/-! ## `copyQuery` / `copyQueryRestore` / `clearDest`: the setup phase -/

lemma flipBindLoad_copyQuery_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hAddr : Sg (Kg.reg rAddr) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.copyQuery, {s0 with queryDigit := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rAddr) rest)
            (Kg.scratch .query) (d :: Sg (Kg.scratch .query)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hAddr]

lemma flipBindLoad_copyQuery_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hAddr : Sg (Kg.reg rAddr) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.copyQueryRestore, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hAddr]

lemma flipBindLoad_copyQueryRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.copyQueryRestore, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.copyQueryRestore, {s0 with queryDigit := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rAddr) (d :: Sg (Kg.reg rAddr))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.copyQueryRestore, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hSc]

lemma flipBindLoad_copyQueryRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.copyQueryRestore, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.clearDest, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.copyQueryRestore, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hSc]

lemma flipBindLoad_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hDest : Sg (Kg.reg rDest) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.clearDest, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.clearDest, {s0 with queryDigit := some d},
          Function.update Sg (Kg.reg rDest) rest⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.clearDest, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hDest]

lemma flipBindLoad_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hDest : Sg (Kg.reg rDest) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.clearDest, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.clearDest, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hDest]

/-- Draining register `rAddr`, prepending its reverse onto both `query` and `copyScratch`.
    Generalizes `MemoryLoad.copyQuery_loop`. -/
lemma copyQuery_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hAddr : Sg (Kg.reg rAddr) = src) :
    (flipBindLoad rDest rAddr)^[src.length + 1]
        (some (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.copyQueryRestore, {s0 with queryDigit := none},
          Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
            (Kg.scratch .query) (src.reverse ++ Sg (Kg.scratch .query)))
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch))⟩ := by
  induction src generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
          (Kg.scratch .query) (Sg (Kg.scratch .query)))
          (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rAddr
        · subst hk; simp [Function.update, hAddr]
        · by_cases hk2 : k = Kg.scratch .query
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .copyScratch
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindLoad_copyQuery_nil_exit rDest rAddr Sg s0 hAddr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_copyQuery_cons rDest rAddr d src' Sg s0 hAddr,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rAddr) src')
              (Kg.scratch .query) (d :: Sg (Kg.scratch .query)))
              (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
           {s0 with queryDigit := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rAddr
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .query
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

/-- Draining `copyScratch` restores register `rAddr` to `copyScratch.reverse ++ src`.
    Generalizes `MemoryLoad.copyQueryRestore_loop`. -/
lemma copyQueryRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k))
    (s0 : LoadState) (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindLoad rDest rAddr)^[copyScratch.length + 1]
        (some (⟨some LoadPhase.copyQueryRestore, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.clearDest, {s0 with queryDigit := none},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.reg rAddr) (copyScratch.reverse ++ Sg (Kg.reg rAddr))⟩ := by
  induction copyScratch generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
          (Kg.reg rAddr) (Sg (Kg.reg rAddr)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .copyScratch
        · subst hk; simp [Function.update, hSc]
        · by_cases hk2 : k = Kg.reg rAddr
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindLoad_copyQueryRestore_nil_exit rDest rAddr Sg s0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_copyQueryRestore_cons rDest rAddr d cs' Sg s0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rAddr) (d :: Sg (Kg.reg rAddr))) {s0 with queryDigit := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rAddr
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Draining register `rDest`, discarding every digit (`Represents` only needs it empty
    afterward; whichever content it held is irrelevant, per `load`'s overwrite semantics).
    `MemoryLoad.lean`'s fixed machine has no equivalent since its `r4` starts empty by
    construction. -/
lemma load_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hDest : Sg (Kg.reg rDest) = dest) :
    (flipBindLoad rDest rAddr)^[dest.length + 1]
        (some (⟨some LoadPhase.clearDest, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr, {s0 with queryDigit := none},
          Function.update Sg (Kg.reg rDest) []⟩ := by
  induction dest generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rDest) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rDest
        · subst hk; simp [Function.update, hDest]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindLoad_clearDest_nil_exit rDest rAddr Sg s0 hDest
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_clearDest_cons rDest rAddr d ds' Sg s0 hDest,
        ih (Function.update Sg (Kg.reg rDest) ds') {s0 with queryDigit := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rDest
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-- Running the setup (`copyQuery` → `copyQueryRestore` → `clearDest`) to completion, landing at
    `compareAddr`. Rather than a single closed-form resulting `Sg`, this exposes exactly the
    facts `scan_phase` needs about the four keys it reads (`rDest`/`query`, both freshly set) or
    leaves untouched (`mem`/`queryTmp`/`logTmp`, forwarded verbatim) — `Kg.reg rAddr`'s own final
    value is deliberately not characterized here, since nothing from `compareAddr` onward ever
    reads it again (alias-safe per the module docstring: whether or not `rDest = rAddr`, `clearDest`
    drains whatever `Kg.reg rDest` names, and this fact alone is all `scan_phase` needs).
    Generalizes `MemoryLoad.copyQuery_phase`. -/
lemma setup_phase (src dest : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hAddr : Sg (Kg.reg rAddr) = src) (hDest : Sg (Kg.reg rDest) = dest)
    (hSc : Sg (Kg.scratch .copyScratch) = []) :
    ∃ Sg' : ∀ k, List (Γg p k),
      (flipBindLoad rDest rAddr)^[(dest.length + 1) + (2 * src.length + 2)]
          (some (⟨some LoadPhase.copyQuery, s0, Sg⟩ :
            Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
        = some ⟨some LoadPhase.compareAddr, {s0 with queryDigit := none}, Sg'⟩
      ∧ Sg' (Kg.reg rDest) = []
      ∧ Sg' (Kg.scratch .query) = src.reverse ++ Sg (Kg.scratch .query)
      ∧ Sg' Kg.mem = Sg Kg.mem
      ∧ Sg' (Kg.scratch .queryTmp) = Sg (Kg.scratch .queryTmp)
      ∧ Sg' (Kg.scratch .logTmp) = Sg (Kg.scratch .logTmp)
      ∧ ∀ k, k ≠ Kg.reg rDest → k ≠ Kg.mem → k ≠ Kg.scratch .query →
          k ≠ Kg.scratch .queryTmp → k ≠ Kg.scratch .logTmp → Sg' k = Sg k := by
  rw [Function.iterate_add_apply (flipBindLoad rDest rAddr) (dest.length + 1) (2 * src.length + 2)]
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount,
    Function.iterate_add_apply (flipBindLoad rDest rAddr) (src.reverse.length + 1) (src.length + 1),
    copyQuery_loop rDest rAddr src Sg s0 hAddr]
  simp only [hSc, List.append_nil]
  set A := Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
      (Kg.scratch .query) (src.reverse ++ Sg (Kg.scratch .query)))
      (Kg.scratch .copyScratch) src.reverse with hA
  have hAaddr : A (Kg.reg rAddr) = [] := by
    rw [hA, Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
    simp [Function.update]
  rw [copyQueryRestore_loop rDest rAddr src.reverse A {s0 with queryDigit := none}
    (by rw [hA]; simp [Function.update])]
  set B := Function.update (Function.update A (Kg.scratch .copyScratch) [])
      (Kg.reg rAddr) (src.reverse.reverse ++ A (Kg.reg rAddr)) with hB
  have hBdest : B (Kg.reg rDest) = dest := by
    by_cases hk : rDest = rAddr
    · subst hk
      have hds : dest = src := hDest.symm.trans hAddr
      subst hds
      rw [hB, Function.update_self, hAaddr, List.append_nil, List.reverse_reverse]
    · have hne : (Kg.reg rDest : Kg p) ≠ Kg.reg rAddr := fun h => hk (by injection h)
      rw [hB, Function.update_of_ne hne, Function.update_of_ne (by simp), hA,
        Function.update_of_ne (by simp), Function.update_of_ne (by simp),
        Function.update_of_ne hne]
      exact hDest
  rw [load_clearDest_loop rDest rAddr dest B {s0 with queryDigit := none} hBdest]
  set C := Function.update B (Kg.reg rDest) [] with hC
  have hCdest : C (Kg.reg rDest) = [] := by rw [hC]; simp [Function.update]
  have hCquery : C (Kg.scratch .query) = src.reverse ++ Sg (Kg.scratch .query) := by
    rw [hC, Function.update_of_ne (by simp), hB, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), hA, Function.update_of_ne (by simp)]
    simp [Function.update]
  have hCmem : C Kg.mem = Sg Kg.mem := by
    rw [hC, Function.update_of_ne (by simp), hB, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), hA, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  have hCqueryTmp : C (Kg.scratch .queryTmp) = Sg (Kg.scratch .queryTmp) := by
    rw [hC, Function.update_of_ne (by simp), hB, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), hA, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  have hClogTmp : C (Kg.scratch .logTmp) = Sg (Kg.scratch .logTmp) := by
    rw [hC, Function.update_of_ne (by simp), hB, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), hA, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  have hCother : ∀ k, k ≠ Kg.reg rDest → k ≠ Kg.mem → k ≠ Kg.scratch .query →
      k ≠ Kg.scratch .queryTmp → k ≠ Kg.scratch .logTmp → C k = Sg k := by
    intro k hk1 hk2 hk3 hk4 hk5
    rw [hC, Function.update_of_ne hk1, hB]
    by_cases hkA : k = Kg.reg rAddr
    · subst hkA
      rw [Function.update_self, hAaddr]
      simp [hAddr]
    · by_cases hk6 : k = Kg.scratch .copyScratch
      · subst hk6
        rw [Function.update_of_ne hkA, Function.update_self, hSc]
      · rw [Function.update_of_ne hkA, Function.update_of_ne hk6, hA,
          Function.update_of_ne hk6, Function.update_of_ne (by simp [hk3]),
          Function.update_of_ne hkA]
  exact ⟨C, rfl, hCdest, hCquery, hCmem, hCqueryTmp, hClogTmp, hCother⟩

/-! ## `restoreQuery` / `skipValue` / `readValue` / `restoreMem` / `drainQuery` / `drainQueryTmp`:
    the scan tail, unchanged in shape from `MemoryLoad.lean` (`clearDest` sits earlier, before
    `compareAddr`, so nothing here needs alias-safety reasoning). -/

lemma flipBindLoad_restoreQuery_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hQt : Sg (Kg.scratch .queryTmp) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.restoreQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreQuery, {s0 with queryDigit := some d},
          Function.update (Function.update Sg (Kg.scratch .queryTmp) rest)
            (Kg.scratch .query) (d :: Sg (Kg.scratch .query))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.restoreQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQt]

lemma flipBindLoad_restoreQuery_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hQt : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.restoreQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.skipValue, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.restoreQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQt]

/-- Draining `qt` (the digits `compareAddr` consumed from `query` during one entry's comparison),
    pushing them back onto `query` and restoring it to `qt.reverse ++ q`. Generalizes
    `MemoryLoad.restoreQuery_loop`. -/
lemma restoreQuery_loop (qt : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hQt : Sg (Kg.scratch .queryTmp) = qt) :
    (flipBindLoad rDest rAddr)^[qt.length + 1]
        (some (⟨some LoadPhase.restoreQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.skipValue, {s0 with queryDigit := none},
          Function.update (Function.update Sg (Kg.scratch .queryTmp) [])
            (Kg.scratch .query) (qt.reverse ++ Sg (Kg.scratch .query))⟩ := by
  induction qt generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .queryTmp) [])
          (Kg.scratch .query) (Sg (Kg.scratch .query)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .queryTmp
        · subst hk; simp [Function.update, hQt]
        · by_cases hk2 : k = Kg.scratch .query
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindLoad_restoreQuery_nil_exit rDest rAddr Sg s0 hQt
  | cons d qt' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_restoreQuery_cons rDest rAddr d qt' Sg s0 hQt,
        ih (Function.update (Function.update Sg (Kg.scratch .queryTmp) qt')
              (Kg.scratch .query) (d :: Sg (Kg.scratch .query))) {s0 with queryDigit := some d}
           (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .queryTmp
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .query
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma flipBindLoad_skipValue_digit (d : Digit) (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hMem : Sg Kg.mem = MemSym.digit d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.skipValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.skipValue, {s0 with memSym := some (MemSym.digit d)},
          Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp) (MemSym.digit d :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.skipValue, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem]

lemma flipBindLoad_skipValue_entryEnd (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hMem : Sg Kg.mem = MemSym.entryEnd :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.skipValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr,
          {memSym := some MemSym.entryEnd, queryDigit := s0.queryDigit, equal := true},
          Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp) (MemSym.entryEnd :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.skipValue, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem]

/-- Consumes a mismatched entry's value field (`vd`, MSB-first) and the `entryEnd` after it into
    `logTmp` only (never touching any register), then returns to `compareAddr` for the next
    entry. Generalizes `MemoryLoad.skipValue_loop`. -/
lemma skipValue_loop (vd : List Digit) (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = (vd.map MemSym.digit) ++ (MemSym.entryEnd :: rest)) :
    (flipBindLoad rDest rAddr)^[vd.length + 1]
        (some (⟨some LoadPhase.skipValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr,
          {memSym := some MemSym.entryEnd, queryDigit := s0.queryDigit, equal := true},
          Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp)
            ((MemSym.entryEnd :: (vd.map MemSym.digit).reverse) ++ Sg (Kg.scratch .logTmp))⟩ := by
  induction vd generalizing Sg s0 with
  | nil =>
      simp only [List.map_nil, List.nil_append] at hMem
      simpa using flipBindLoad_skipValue_entryEnd rDest rAddr rest Sg s0 hMem
  | cons d vd' ih =>
      simp only [List.map_cons, List.cons_append] at hMem
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_skipValue_digit rDest rAddr d
          (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest) Sg s0 hMem,
        ih (Function.update (Function.update Sg Kg.mem
              (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest))
              (Kg.scratch .logTmp) (MemSym.digit d :: Sg (Kg.scratch .logTmp)))
           {s0 with memSym := some (MemSym.digit d)} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.mem
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .logTmp
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma flipBindLoad_readValue_digit (d : Digit) (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hMem : Sg Kg.mem = MemSym.digit d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.readValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.readValue, {s0 with memSym := some (MemSym.digit d)},
          Function.update (Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp) (MemSym.digit d :: Sg (Kg.scratch .logTmp)))
            (Kg.reg rDest) (d :: Sg (Kg.reg rDest))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.readValue, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, MemSym.digit?]

lemma flipBindLoad_readValue_entryEnd (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hMem : Sg Kg.mem = MemSym.entryEnd :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.readValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreMem, {s0 with memSym := some MemSym.entryEnd},
          Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp) (MemSym.entryEnd :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.readValue, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem]

/-- Running `readValue` for `vd.length + 1` steps consumes the value field (`vd`, MSB-first) and
    the `entryEnd` after it: `vd`'s reverse lands on `rDest` (prepended — `rDest` is already `[]`
    by the time `compareAddr` is ever reached, per `setup_phase`'s `clearDest` guarantee, so this
    prepend is really an overwrite), and every popped symbol is preserved on `logTmp`. Generalizes
    `MemoryLoad.readValue_loop`. -/
lemma readValue_loop (vd : List Digit) (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = (vd.map MemSym.digit) ++ (MemSym.entryEnd :: rest)) :
    (flipBindLoad rDest rAddr)^[vd.length + 1]
        (some (⟨some LoadPhase.readValue, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreMem, {s0 with memSym := some MemSym.entryEnd},
          Function.update (Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp)
            ((MemSym.entryEnd :: (vd.map MemSym.digit).reverse) ++ Sg (Kg.scratch .logTmp)))
            (Kg.reg rDest) (vd.reverse ++ Sg (Kg.reg rDest))⟩ := by
  induction vd generalizing Sg s0 with
  | nil =>
      simp only [List.map_nil, List.nil_append, List.reverse_nil, List.singleton_append]
        at hMem ⊢
      have hcollapse : Function.update
          (Function.update (Function.update Sg Kg.mem rest)
            (Kg.scratch .logTmp) (MemSym.entryEnd :: Sg (Kg.scratch .logTmp)))
          (Kg.reg rDest) (Sg (Kg.reg rDest))
          = Function.update (Function.update Sg Kg.mem rest)
              (Kg.scratch .logTmp) (MemSym.entryEnd :: Sg (Kg.scratch .logTmp)) := by
        funext k
        by_cases hk : k = Kg.reg rDest
        · subst hk; simp [Function.update]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindLoad_readValue_entryEnd rDest rAddr rest Sg s0 hMem
  | cons d vd' ih =>
      simp only [List.map_cons, List.cons_append] at hMem
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_readValue_digit rDest rAddr d
          (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest) Sg s0 hMem,
        ih (Function.update (Function.update (Function.update Sg Kg.mem
              (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest))
              (Kg.scratch .logTmp) (MemSym.digit d :: Sg (Kg.scratch .logTmp)))
              (Kg.reg rDest) (d :: Sg (Kg.reg rDest)))
           {s0 with memSym := some (MemSym.digit d)} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.mem
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .logTmp
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.reg rDest
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindLoad_restoreMem_cons (m : MemSym) (rest : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hLt : Sg (Kg.scratch .logTmp) = m :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreMem, {s0 with memSym := some m},
          Function.update (Function.update Sg (Kg.scratch .logTmp) rest)
            Kg.mem (m :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hLt]

lemma flipBindLoad_restoreMem_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hLt : Sg (Kg.scratch .logTmp) = ([] : List MemSym)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQuery, {s0 with memSym := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hLt]

lemma flipBindLoad_drainQuery_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hQ : Sg (Kg.scratch .query) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.drainQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQuery, {s0 with queryDigit := some d},
          Function.update Sg (Kg.scratch .query) rest⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.drainQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQ]

lemma flipBindLoad_drainQuery_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hQ : Sg (Kg.scratch .query) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.drainQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQueryTmp, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.drainQuery, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQ]

/-- Draining `query` to empty discards whatever it holds — `Represents` only needs it empty
    afterward. Generalizes `MemoryLoad.drainQuery_loop`. -/
lemma drainQuery_loop (q : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hQ : Sg (Kg.scratch .query) = q) :
    (flipBindLoad rDest rAddr)^[q.length + 1]
        (some (⟨some LoadPhase.drainQuery, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQueryTmp, {s0 with queryDigit := none},
          Function.update Sg (Kg.scratch .query) []⟩ := by
  induction q generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.scratch .query) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .query
        · subst hk; simp [Function.update, hQ]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindLoad_drainQuery_nil_exit rDest rAddr Sg s0 hQ
  | cons d q' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_drainQuery_cons rDest rAddr d q' Sg s0 hQ,
        ih (Function.update Sg (Kg.scratch .query) q') {s0 with queryDigit := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .query
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

lemma flipBindLoad_drainQueryTmp_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hQt : Sg (Kg.scratch .queryTmp) = d :: rest) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.drainQueryTmp, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQueryTmp, {s0 with queryDigit := some d},
          Function.update Sg (Kg.scratch .queryTmp) rest⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.drainQueryTmp, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQt]

lemma flipBindLoad_drainQueryTmp_nil_exit
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hQt : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.drainQueryTmp, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {s0 with queryDigit := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.drainQueryTmp, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hQt]

/-- `drainQuery_loop`'s twin for `queryTmp`. -/
lemma drainQueryTmp_loop (qt : List Digit) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hQt : Sg (Kg.scratch .queryTmp) = qt) :
    (flipBindLoad rDest rAddr)^[qt.length + 1]
        (some (⟨some LoadPhase.drainQueryTmp, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {s0 with queryDigit := none},
          Function.update Sg (Kg.scratch .queryTmp) []⟩ := by
  induction qt generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.scratch .queryTmp) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .queryTmp
        · subst hk; simp [Function.update, hQt]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindLoad_drainQueryTmp_nil_exit rDest rAddr Sg s0 hQt
  | cons d qt' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_drainQueryTmp_cons rDest rAddr d qt' Sg s0 hQt,
        ih (Function.update Sg (Kg.scratch .queryTmp) qt') {s0 with queryDigit := some d}
           (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .queryTmp
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-- Draining `savedLog` off `logTmp` prepends its reverse onto `mem`, landing at `drainQuery`.
    Generalizes the mem-restoring half of `MemoryLoad.restoreMem_loop`. -/
lemma restoreMem_drain_loop (savedLog : List MemSym) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hLt : Sg (Kg.scratch .logTmp) = savedLog) :
    (flipBindLoad rDest rAddr)^[savedLog.length + 1]
        (some (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.drainQuery, {s0 with memSym := none},
          Function.update (Function.update Sg Kg.mem (savedLog.reverse ++ Sg Kg.mem))
            (Kg.scratch .logTmp) []⟩ := by
  induction savedLog generalizing Sg s0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg Kg.mem (Sg Kg.mem))
          (Kg.scratch .logTmp) [] = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .logTmp
        · subst hk; simp [Function.update, hLt]
        · by_cases hk2 : k = Kg.mem
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindLoad_restoreMem_nil_exit rDest rAddr Sg s0 hLt
  | cons m saved' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_restoreMem_cons rDest rAddr m saved' Sg s0 hLt,
        ih (Function.update (Function.update Sg (Kg.scratch .logTmp) saved') Kg.mem
              (m :: Sg Kg.mem)) {s0 with memSym := some m} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .logTmp
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.mem
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- `restoreMem_drain_loop` chained with `drainQuery_loop`/`drainQueryTmp_loop`: discards whatever
    `query`/`queryTmp` still hold — exactly one of the two per `loadProg`'s docstring — so both
    end up empty. Generalizes `MemoryLoad.restoreMem_loop`. -/
lemma restoreMem_loop (savedLog : List MemSym) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hLt : Sg (Kg.scratch .logTmp) = savedLog) :
    (flipBindLoad rDest rAddr)^[(Sg (Kg.scratch .queryTmp)).length + 1
        + ((Sg (Kg.scratch .query)).length + 1) + (savedLog.length + 1)]
        (some (⟨some LoadPhase.restoreMem, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {s0 with memSym := none, queryDigit := none},
          Function.update (Function.update
            (Function.update (Function.update Sg Kg.mem (savedLog.reverse ++ Sg Kg.mem))
              (Kg.scratch .logTmp) [])
            (Kg.scratch .query) [])
            (Kg.scratch .queryTmp) []⟩ := by
  rw [Function.iterate_add_apply (flipBindLoad rDest rAddr)
    ((Sg (Kg.scratch .queryTmp)).length + 1 + ((Sg (Kg.scratch .query)).length + 1))
    (savedLog.length + 1), restoreMem_drain_loop rDest rAddr savedLog Sg s0 hLt]
  set S1 := Function.update (Function.update Sg Kg.mem (savedLog.reverse ++ Sg Kg.mem))
      (Kg.scratch .logTmp) [] with hS1
  have hQ1 : S1 (Kg.scratch .query) = Sg (Kg.scratch .query) := by
    rw [hS1, Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  rw [Function.iterate_add_apply (flipBindLoad rDest rAddr)
    ((Sg (Kg.scratch .queryTmp)).length + 1) ((Sg (Kg.scratch .query)).length + 1),
    drainQuery_loop rDest rAddr (Sg (Kg.scratch .query)) S1 {s0 with memSym := none} hQ1]
  set S2 := Function.update S1 (Kg.scratch .query) [] with hS2
  have hQt2 : S2 (Kg.scratch .queryTmp) = Sg (Kg.scratch .queryTmp) := by
    rw [hS2, Function.update_of_ne (by simp), hS1, Function.update_of_ne (by simp),
      Function.update_of_ne (by simp)]
  rw [drainQueryTmp_loop rDest rAddr (Sg (Kg.scratch .queryTmp)) S2
    {s0 with memSym := none, queryDigit := none} hQt2]

/-! ## `compareAddr`: per-entry address comparison, unchanged in shape from `MemoryLoad.lean`
    (queried by `query`/`queryTmp`/`logTmp`/`mem` only — never a register, so no alias-safety
    reasoning is needed here either; `digit_match`/`addrEnd_match` collapse into the more general
    `digit_eq`/`addrEnd_qempty_true` below, since `compareAddr_loop_matched`'s own `h : s0.equal =
    true` invariant already specializes them). -/

lemma flipBindLoad_compareAddr_digit_qempty (a : Digit) (ad' : List Digit) (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
    (hQuery : Sg (Kg.scratch .query) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr,
          {memSym := some (MemSym.digit a), queryDigit := none, equal := false},
          Function.update
              (Function.update (Function.update Sg Kg.mem
                (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
                (Kg.scratch .query) [])
            (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?]

lemma flipBindLoad_compareAddr_digit_neq (a d : Digit) (ad' q' : List Digit)
    (valTail : List MemSym) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hne : a ≠ d)
    (hMem : Sg Kg.mem = MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
    (hQuery : Sg (Kg.scratch .query) = d :: q') :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr,
          {memSym := some (MemSym.digit a), queryDigit := some d, equal := false},
          Function.update (Function.update
              (Function.update (Function.update Sg Kg.mem
                (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
                (Kg.scratch .query) q')
              (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
            (Kg.scratch .queryTmp) (d :: Sg (Kg.scratch .queryTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?, hne]

lemma flipBindLoad_compareAddr_addrEnd_qnonempty (d : Digit) (q' : List Digit)
    (valTail : List MemSym) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = MemSym.addrEnd :: valTail) (hQuery : Sg (Kg.scratch .query) = d :: q') :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreQuery,
          {memSym := some MemSym.addrEnd, queryDigit := some d, equal := false},
          Function.update (Function.update Sg Kg.mem valTail)
            (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?]

lemma flipBindLoad_compareAddr_digit_eq (a : Digit) (ad' q' : List Digit) (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
    (hQuery : Sg (Kg.scratch .query) = a :: q') :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.compareAddr,
          {memSym := some (MemSym.digit a), queryDigit := some a, equal := s0.equal},
          Function.update (Function.update
              (Function.update (Function.update Sg Kg.mem
                (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
                (Kg.scratch .query) q')
              (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
            (Kg.scratch .queryTmp) (a :: Sg (Kg.scratch .queryTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?]

lemma flipBindLoad_compareAddr_addrEnd_qempty_true (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (h : s0.equal = true)
    (hMem : Sg Kg.mem = MemSym.addrEnd :: valTail)
    (hQuery : Sg (Kg.scratch .query) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.readValue,
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := true},
          Function.update (Function.update Sg Kg.mem valTail)
            (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?, h]

lemma flipBindLoad_compareAddr_addrEnd_qempty_false (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (h : s0.equal = false)
    (hMem : Sg Kg.mem = MemSym.addrEnd :: valTail)
    (hQuery : Sg (Kg.scratch .query) = ([] : List Digit)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreQuery,
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := false},
          Function.update (Function.update Sg Kg.mem valTail)
            (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp))⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem, hQuery, MemSym.digit?, h]

lemma flipBindLoad_compareAddr_nomore (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (hMem : Sg Kg.mem = ([] : List MemSym)) :
    flipBindLoad rDest rAddr
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.restoreMem, {s0 with memSym := none}, Sg⟩ := by
  show (Turing.TM2.step (loadProg rDest rAddr))
      (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadPhase LoadState) = _
  simp [loadProg, hMem]

/-- `compareAddr`, on a query that turns out to equal the entry's own (stored) address
    digit-for-digit: running for `ad.length + 1` steps consumes the whole address field and the
    `addrEnd` after it, draining `query` to empty (`ad`'s reverse lands on `queryTmp`) and
    transitioning straight to `readValue`. Generalizes `MemoryLoad.compareAddr_loop_matched`. -/
lemma compareAddr_loop_matched (ad : List Digit) (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (h : s0.equal = true)
    (hMem : Sg Kg.mem = ad.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
    (hQuery : Sg (Kg.scratch .query) = ad) :
    (flipBindLoad rDest rAddr)^[ad.length + 1]
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.readValue,
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := true},
          Function.update
              (Function.update
                (Function.update (Function.update Sg Kg.mem valTail)
                  (Kg.scratch .query) [])
                (Kg.scratch .logTmp)
                ((MemSym.addrEnd :: ad.reverse.map MemSym.digit) ++ Sg (Kg.scratch .logTmp)))
            (Kg.scratch .queryTmp) (ad.reverse ++ Sg (Kg.scratch .queryTmp))⟩ := by
  induction ad generalizing Sg s0 with
  | nil =>
      simp only [List.map_nil, List.nil_append] at hMem
      simp only [List.length_nil, List.reverse_nil, List.map_nil, List.nil_append,
        List.singleton_append]
      have hcollapse : Function.update (Function.update Sg Kg.mem valTail)
          (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp))
          = Function.update
              (Function.update
                (Function.update (Function.update Sg Kg.mem valTail)
                  (Kg.scratch .query) [])
                (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp)))
              (Kg.scratch .queryTmp) (Sg (Kg.scratch .queryTmp)) := by
        funext k
        cases k with
        | reg i => simp [Function.update]
        | mem => simp [Function.update]
        | io => simp [Function.update]
        | scratch s => cases s <;> simp [Function.update, hQuery]
      rw [← hcollapse]
      exact flipBindLoad_compareAddr_addrEnd_qempty_true rDest rAddr valTail Sg s0 h hMem hQuery
  | cons a ad' ih =>
      simp only [List.map_cons, List.cons_append] at hMem
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoad_compareAddr_digit_eq rDest rAddr a ad' ad' valTail Sg s0 hMem hQuery,
        ih (Function.update
              (Function.update
                (Function.update (Function.update Sg Kg.mem
                  (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
                  (Kg.scratch .query) ad')
                (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
              (Kg.scratch .queryTmp) (a :: Sg (Kg.scratch .queryTmp)))
           {memSym := some (MemSym.digit a), queryDigit := some a, equal := s0.equal}
           h (by simp) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      cases k with
      | reg i => simp [Function.update]
      | mem => simp [Function.update]
      | io => simp [Function.update]
      | scratch s => cases s <;> simp [Function.update, List.reverse_cons, List.append_assoc]

/-- The mismatch-then-restore statement of `compareAddr_mismatch_then_restore` at a fixed entry
    address `ad` and query `q`, quantified over the store so that the per-case lemmas below can
    be stated and chained without restating the long result configuration. -/
def CompareAddrMismatchAt (valTail : List MemSym) (ad q : List Digit) : Prop :=
  ∀ (Sg : ∀ k, List (Γg p k)) (s0 : LoadState),
    ¬ (s0.equal = true ∧ ad = q) →
    Sg Kg.mem = ad.map MemSym.digit ++ (MemSym.addrEnd :: valTail) →
    Sg (Kg.scratch .query) = q →
    (flipBindLoad rDest rAddr)^[(ad.length + 1)
        + (min ad.length q.length + (Sg (Kg.scratch .queryTmp)).length + 1)]
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.skipValue,
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := false},
          Function.update
              (Function.update
                (Function.update (Function.update Sg Kg.mem valTail)
                  (Kg.scratch .logTmp)
                  ((MemSym.addrEnd :: ad.reverse.map MemSym.digit) ++ Sg (Kg.scratch .logTmp)))
                (Kg.scratch .queryTmp) [])
              (Kg.scratch .query) ((Sg (Kg.scratch .queryTmp)).reverse ++ q)⟩

/-- `CompareAddrMismatchAt` for every query: the induction hypothesis shape of
    `compareAddrMismatchThenRestore_goal`. -/
def CompareAddrMismatchGoal (valTail : List MemSym) (ad : List Digit) : Prop :=
  ∀ q, CompareAddrMismatchAt rDest rAddr valTail ad q

/-- `compareAddr_mismatch_then_restore` for an empty address and an empty query: the mismatch can
    only come from the incoming `equal = false`, so `addrEnd` is consumed with an empty query and
    `restoreQuery` drains `queryTmp`. -/
lemma compareAddrMismatchThenRestore_nil_nil (valTail : List MemSym) :
    CompareAddrMismatchAt rDest rAddr valTail [] [] := by
  intro Sg s0 hmis hMem hQuery
  have heq : s0.equal = false := by
    rcases hs : s0.equal with _ | _
    · rfl
    · exact absurd ⟨hs, rfl⟩ hmis
  simp only [List.map_nil, List.nil_append] at hMem
  have hcount : ([] : List Digit).length + 1
      + (min ([] : List Digit).length ([] : List Digit).length
        + (Sg (Kg.scratch .queryTmp)).length + 1)
      = ((Sg (Kg.scratch .queryTmp)).length + 1) + 1 := by simp; omega
  rw [hcount, Function.iterate_add_apply, Function.iterate_one,
    flipBindLoad_compareAddr_addrEnd_qempty_false rDest rAddr valTail Sg s0 heq hMem hQuery]
  simpa [hQuery] using restoreQuery_loop rDest rAddr (Sg (Kg.scratch .queryTmp))
    (Function.update (Function.update Sg Kg.mem valTail)
      (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp)))
    ({memSym := some MemSym.addrEnd, queryDigit := none, equal := false} : LoadState)
    (by simp)

/-- `compareAddr_mismatch_then_restore` for an empty address and a non-empty query: `addrEnd` is met
    while `query` still has digits, and `restoreQuery` then drains `queryTmp`. -/
lemma compareAddrMismatchThenRestore_nil_cons (valTail : List MemSym) (d : Digit)
    (q' : List Digit) : CompareAddrMismatchAt rDest rAddr valTail [] (d :: q') := by
  intro Sg s0 hmis hMem hQuery
  simp only [List.map_nil, List.nil_append] at hMem
  have hcount : ([] : List Digit).length + 1
      + (min ([] : List Digit).length (d :: q').length
        + (Sg (Kg.scratch .queryTmp)).length + 1)
      = ((Sg (Kg.scratch .queryTmp)).length + 1) + 1 := by simp; omega
  rw [hcount, Function.iterate_add_apply, Function.iterate_one,
    flipBindLoad_compareAddr_addrEnd_qnonempty rDest rAddr d q' valTail Sg s0 hMem hQuery]
  simpa [hQuery] using restoreQuery_loop rDest rAddr (Sg (Kg.scratch .queryTmp))
    (Function.update (Function.update Sg Kg.mem valTail)
      (Kg.scratch .logTmp) (MemSym.addrEnd :: Sg (Kg.scratch .logTmp)))
    ({memSym := some MemSym.addrEnd, queryDigit := some d, equal := false} : LoadState)
    (by simp)

/-- `compareAddr_mismatch_then_restore` for a non-empty address and an empty query: one `compareAddr`
    step consumes an address digit (the query has run out), then the tail is the induction
    hypothesis at `[]`. -/
lemma compareAddrMismatchThenRestore_cons_nil (valTail : List MemSym) (a : Digit)
    (ad' : List Digit) (ih : CompareAddrMismatchGoal rDest rAddr valTail ad') :
    CompareAddrMismatchAt rDest rAddr valTail (a :: ad') [] := by
  intro Sg s0 hmis hMem hQuery
  simp only [List.map_cons, List.cons_append] at hMem
  have hcount : (a :: ad').length + 1
      + (min (a :: ad').length ([] : List Digit).length
        + (Sg (Kg.scratch .queryTmp)).length + 1)
      = (ad'.length + 1 + (min ad'.length ([] : List Digit).length
          + (Sg (Kg.scratch .queryTmp)).length + 1)) + 1 := by simp; omega
  rw [hcount, Function.iterate_add_apply, Function.iterate_one,
    flipBindLoad_compareAddr_digit_qempty rDest rAddr a ad' valTail Sg s0 hMem hQuery]
  have hQ' : Function.update
        (Function.update (Function.update Sg Kg.mem
          (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
          (Kg.scratch .query) [])
        (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp))
        (Kg.scratch .queryTmp) = Sg (Kg.scratch .queryTmp) := by
    rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      Function.update_of_ne (by simp)]
  have := ih [] (Function.update
        (Function.update (Function.update Sg Kg.mem
          (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
          (Kg.scratch .query) [])
        (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
      {memSym := some (MemSym.digit a), queryDigit := none, equal := false}
      (by simp) (by simp) (by simp)
  rw [hQ'] at this
  rw [this]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k with
  | reg i => simp [Function.update]
  | mem => simp [Function.update]
  | io => simp [Function.update]
  | scratch s => cases s <;> simp [Function.update, List.reverse_cons, List.append_assoc]

/-- `compareAddr_mismatch_then_restore` when the leading address digit equals the leading query
    digit: `compareAddr` consumes both, the incoming `equal` is carried unchanged, and the tail is
    the induction hypothesis at `q'`. -/
lemma compareAddrMismatchThenRestore_cons_eq (valTail : List MemSym) (a : Digit)
    (ad' q' : List Digit) (ih : CompareAddrMismatchGoal rDest rAddr valTail ad') :
    CompareAddrMismatchAt rDest rAddr valTail (a :: ad') (a :: q') := by
  intro Sg s0 hmis hMem hQuery
  simp only [List.map_cons, List.cons_append] at hMem
  have hcount : (a :: ad').length + 1 + (min (a :: ad').length (a :: q').length
        + (Sg (Kg.scratch .queryTmp)).length + 1)
      = (ad'.length + 1 + (min ad'.length q'.length
          + (a :: Sg (Kg.scratch .queryTmp)).length + 1)) + 1 := by simp; omega
  rw [hcount, Function.iterate_add_apply, Function.iterate_one,
    flipBindLoad_compareAddr_digit_eq rDest rAddr a ad' q' valTail Sg s0 hMem hQuery]
  have hmis' : ¬ (s0.equal = true ∧ ad' = q') := fun ⟨he, hl⟩ => hmis ⟨he, by rw [hl]⟩
  have := ih q'
      (Function.update
        (Function.update
          (Function.update (Function.update Sg Kg.mem
            (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
            (Kg.scratch .query) q')
          (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
        (Kg.scratch .queryTmp) (a :: Sg (Kg.scratch .queryTmp)))
      {memSym := some (MemSym.digit a), queryDigit := some a, equal := s0.equal}
      hmis' (by simp) (by simp)
  simp only [Function.update_self] at this
  rw [this]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k with
  | reg i => simp [Function.update]
  | mem => simp [Function.update]
  | io => simp [Function.update]
  | scratch s => cases s <;> simp [Function.update, List.reverse_cons, List.append_assoc]

/-- `compareAddr_mismatch_then_restore` when the leading address digit differs from the leading
    query digit: `compareAddr` consumes both and sets `equal := false`, then the tail is the
    induction hypothesis at `q'`. -/
lemma compareAddrMismatchThenRestore_cons_neq (valTail : List MemSym) (a d : Digit)
    (ad' q' : List Digit) (hne : a ≠ d) (ih : CompareAddrMismatchGoal rDest rAddr valTail ad') :
    CompareAddrMismatchAt rDest rAddr valTail (a :: ad') (d :: q') := by
  intro Sg s0 hmis hMem hQuery
  simp only [List.map_cons, List.cons_append] at hMem
  have hcount : (a :: ad').length + 1 + (min (a :: ad').length (d :: q').length
        + (Sg (Kg.scratch .queryTmp)).length + 1)
      = (ad'.length + 1 + (min ad'.length q'.length
          + (d :: Sg (Kg.scratch .queryTmp)).length + 1)) + 1 := by simp; omega
  rw [hcount, Function.iterate_add_apply, Function.iterate_one,
    flipBindLoad_compareAddr_digit_neq rDest rAddr a d ad' q' valTail Sg s0 hne hMem hQuery]
  have := ih q'
      (Function.update
        (Function.update
          (Function.update (Function.update Sg Kg.mem
            (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
            (Kg.scratch .query) q')
          (Kg.scratch .logTmp) (MemSym.digit a :: Sg (Kg.scratch .logTmp)))
        (Kg.scratch .queryTmp) (d :: Sg (Kg.scratch .queryTmp)))
      {memSym := some (MemSym.digit a), queryDigit := some d, equal := false}
      (by simp) (by simp) (by simp)
  simp only [Function.update_self] at this
  rw [this]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k with
  | reg i => simp [Function.update]
  | mem => simp [Function.update]
  | io => simp [Function.update]
  | scratch s => cases s <;> simp [Function.update, List.reverse_cons, List.append_assoc]

/-- `compareAddr_mismatch_then_restore` for every address and query, by induction on the address. -/
lemma compareAddrMismatchThenRestore_goal (valTail : List MemSym) (ad : List Digit) :
    CompareAddrMismatchGoal rDest rAddr valTail ad := by
  induction ad with
  | nil =>
      intro q
      rcases q with _ | ⟨d, q'⟩
      · exact compareAddrMismatchThenRestore_nil_nil rDest rAddr valTail
      · exact compareAddrMismatchThenRestore_nil_cons rDest rAddr valTail d q'
  | cons a ad' ih =>
      intro q
      rcases q with _ | ⟨d, q'⟩
      · exact compareAddrMismatchThenRestore_cons_nil rDest rAddr valTail a ad' ih
      · by_cases hne : a = d
        · subst hne
          exact compareAddrMismatchThenRestore_cons_eq rDest rAddr valTail a ad' q' ih
        · exact compareAddrMismatchThenRestore_cons_neq rDest rAddr valTail a d ad' q' hne ih

/-- `compareAddr`'s mismatch path, combined with the `restoreQuery` drain that necessarily
    follows it: whenever the incoming `equal` is already `false`, or this entry's address `ad`
    differs from `q`, running for `(ad.length + 1) + (min ad.length q.length +
    (Sg (Kg.scratch .queryTmp)).length + 1)` steps consumes the address field and `addrEnd`, then
    fully restores `query`. Generalizes `MemoryLoad.compareAddr_mismatch_then_restore`. -/
lemma compareAddr_mismatch_then_restore (ad q : List Digit) (valTail : List MemSym)
    (Sg : ∀ k, List (Γg p k)) (s0 : LoadState) (hmis : ¬ (s0.equal = true ∧ ad = q))
    (hMem : Sg Kg.mem = ad.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
    (hQuery : Sg (Kg.scratch .query) = q) :
    (flipBindLoad rDest rAddr)^[(ad.length + 1)
        + (min ad.length q.length + (Sg (Kg.scratch .queryTmp)).length + 1)]
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.skipValue,
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := false},
          Function.update
              (Function.update
                (Function.update (Function.update Sg Kg.mem valTail)
                  (Kg.scratch .logTmp)
                  ((MemSym.addrEnd :: ad.reverse.map MemSym.digit) ++ Sg (Kg.scratch .logTmp)))
                (Kg.scratch .queryTmp) [])
              (Kg.scratch .query) ((Sg (Kg.scratch .queryTmp)).reverse ++ q)⟩ := by
  exact compareAddrMismatchThenRestore_goal rDest rAddr valTail ad q Sg s0 hmis hMem hQuery

/-! ### Quantitative companion

`scan_phase` below is a pure existential (`∃ n, ...`): its induction on `log` already builds a
concrete closed-form witness at each case (via `refine ⟨CONCRETE_EXPR, ...⟩`), but that witness
is not exposed to callers. `scan_phase`'s own `instructionCost` (`BitCostRAM.instructionCost`'s
`load` case) only charges for the final matched address/value, not for the entries scanned past
along the way. Because `Represents` stores memory through an existential write-log, the scan's
step count cannot be bounded by a function of the RAM state `r` alone — only by the concrete log
actually present in `Sg Kg.mem`.

`scanPotential` below is the quantity that closes this gap. Each `cons` step of `scan_phase`'s
induction moves one entry's encoding (`encodeEntry`, length `e`) verbatim from `mem` into
`logTmp` — `mem` shrinks by exactly `e`, `logTmp` grows by exactly `e` — while `query` stays
fixed at the target address and `queryTmp` is always drained back to empty before recursing, so
`scanPotential` is *exactly conserved* across the whole scan. This is what lets a single
quadratic bound (`K * (log.length + 1) * scanPotential`, converted to `K * scanPotential ^ 2` via
`log.length ≤ (encodeLog log).length ≤ scanPotential`) absorb the scan's worst case: many
mismatches, each an `O(scanPotential)`-length comparison against the fixed target address. -/

/-- The quantitative potential for `load`'s scan phase: total digit/symbol content across the memory
    write-log, the target-address `query` scratch, and the write-log restoration scratch
    `logTmp` (`queryTmp` is omitted — `scan_phase`'s own invariant keeps it empty on every
    entry). -/
def scanPotential (Sg : ∀ k, List (Γg p k)) : ℕ :=
  (Sg Kg.mem).length + (Sg (Kg.scratch .query)).length + (Sg (Kg.scratch .logTmp)).length + 1

/-- `encodeEntry`'s length, unfolded: the address digits, `addrEnd`, the value digits,
    `entryEnd`. -/
lemma length_encodeEntry (a v : ℕ) :
    (encodeEntry a v).length = (natToDigits a).length + (natToDigits v).length + 2 := by
  simp only [encodeEntry, List.length_append, List.length_map, List.length_reverse,
    List.length_cons, List.length_nil]
  omega

/-- Every entry contributes at least `2` symbols (the two boundary markers alone), so
    `encodeLog`'s total length dominates the entry count — the fact that converts
    `scanPhase_bounded`'s `(log.length + 1) * scanPotential` shape into a pure
    `scanPotential ^ 2` bound. -/
lemma log_length_le_encodeLog_length (log : WriteLog) :
    log.length ≤ (encodeLog log).length := by
  induction log with
  | nil => simp [encodeLog]
  | cons e xs ih =>
      obtain ⟨a, v⟩ := e
      simp only [encodeLog, List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons]
      have he : (encodeEntry a v).length ≥ 1 := by
        rw [length_encodeEntry]; omega
      simp only [encodeLog] at ih
      omega

/-- The conclusion of `scanPhase_bounded`, named so that the per-case lemmas can take the
    induction hypothesis for the tail of the log as a hypothesis. -/
def ScanPhaseBoundedGoal (addr : ℕ) (log : WriteLog) (Sg : ∀ k, List (Γg p k))
    (s0 : LoadState) : Prop :=
  ∃ n, (flipBindLoad rDest rAddr)^[n]
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {memSym := none, queryDigit := none, equal := true},
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update Sg Kg.mem
                    ((Sg (Kg.scratch .logTmp)).reverse ++ encodeLog log))
                  (Kg.scratch .logTmp) [])
                (Kg.scratch .query) [])
              (Kg.scratch .queryTmp) [])
            (Kg.reg rDest) (scanResult addr log)⟩ ∧
        n ≤ 16 * (log.length + 1) * scanPotential Sg

/-- `scanPhase_bounded` for an exhausted log: one `nomore` step, then `restoreMem_loop` puts the
    scanned prefix back, leaving `rDest` empty. -/
lemma scanPhase_bounded_nil (addr : ℕ) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (heq : s0.equal = true) (hDest : Sg (Kg.reg rDest) = ([] : List Digit))
    (hMem : Sg Kg.mem = encodeLog ([] : WriteLog))
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) :
    ScanPhaseBoundedGoal rDest rAddr addr [] Sg s0 := by
  unfold ScanPhaseBoundedGoal
  simp only [encodeLog, List.map_nil, List.flatten_nil] at hMem
  refine ⟨((Sg (Kg.scratch .queryTmp)).length + 1 + ((Sg (Kg.scratch .query)).length + 1)
      + ((Sg (Kg.scratch .logTmp)).length + 1)) + 1, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_one,
      flipBindLoad_compareAddr_nomore rDest rAddr Sg s0 hMem,
      restoreMem_loop rDest rAddr (Sg (Kg.scratch .logTmp)) Sg {s0 with memSym := none} rfl]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, heq, true_and]
    funext k
    cases k with
    | reg i =>
        by_cases hi : i = rDest
        · subst hi; simp [Function.update, hDest, scanResult]
        · simp [Function.update, hi]
    | mem => simp [Function.update, encodeLog, hMem]
    | io => simp [Function.update]
    | scratch s => cases s <;> simp [Function.update]
  · have hqt0 : (Sg (Kg.scratch .queryTmp)).length = 0 := by rw [hQueryTmp]; rfl
    have hmem0 : (Sg Kg.mem).length = 0 := by rw [hMem]; rfl
    simp only [scanPotential, List.length_nil]
    omega

/-- `scanPhase_bounded` when the first log entry matches the target address: compare, read the
    value into `rDest`, then restore memory; the cost is a single `32 * scanPotential` charge. -/
lemma scanPhase_bounded_match (a v : ℕ) (xs : WriteLog) (Sg : ∀ k, List (Γg p k))
    (s0 : LoadState) (heq : s0.equal = true)
    (hDest : Sg (Kg.reg rDest) = ([] : List Digit))
    (hMem : Sg Kg.mem = encodeLog ((a, v) :: xs))
    (hQuery : Sg (Kg.scratch .query) = (natToDigits a).reverse)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) :
    ScanPhaseBoundedGoal rDest rAddr a ((a, v) :: xs) Sg s0 := by
  unfold ScanPhaseBoundedGoal
  have hMem1 : Sg Kg.mem = (natToDigits a).reverse.map MemSym.digit
      ++ (MemSym.addrEnd :: ((natToDigits v).reverse.map MemSym.digit
        ++ (MemSym.entryEnd :: encodeLog xs))) := by
    simp [hMem, encodeLog, encodeEntry, List.append_assoc]
  have hMemLen : (Sg Kg.mem).length
      = (natToDigits a).length + (natToDigits v).length + 2 + (encodeLog xs).length := by
    rw [hMem1]; simp only [List.length_append, List.length_map, List.length_reverse,
      List.length_cons]; omega
  have step1 := compareAddr_loop_matched rDest rAddr (natToDigits a).reverse
    ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs))
    Sg s0 heq hMem1 hQuery
  rw [List.reverse_reverse] at step1
  set Sg1 := Function.update
        (Function.update
          (Function.update (Function.update Sg Kg.mem
            ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs)))
            (Kg.scratch .query) [])
          (Kg.scratch .logTmp)
          ((MemSym.addrEnd :: (natToDigits a).map MemSym.digit) ++ Sg (Kg.scratch .logTmp)))
        (Kg.scratch .queryTmp) (natToDigits a ++ Sg (Kg.scratch .queryTmp))
    with hSg1
  have hMem2 : Sg1 Kg.mem = (natToDigits v).reverse.map MemSym.digit
      ++ (MemSym.entryEnd :: encodeLog xs) := by
    rw [hSg1]; simp [Function.update]
  have hDest1 : Sg1 (Kg.reg rDest) = ([] : List Digit) := by
    rw [hSg1]; simp [Function.update, hDest]
  have step2 := readValue_loop rDest rAddr (natToDigits v).reverse (encodeLog xs) Sg1
    {memSym := some MemSym.addrEnd, queryDigit := none, equal := true} hMem2
  rw [List.reverse_reverse, hDest1, List.append_nil] at step2
  conv at step2 => rhs; rw [List.map_reverse, List.reverse_reverse]
  set Sg2 := Function.update
        (Function.update (Function.update Sg1 Kg.mem (encodeLog xs))
          (Kg.scratch .logTmp)
          ((MemSym.entryEnd :: (natToDigits v).map MemSym.digit) ++ Sg1 (Kg.scratch .logTmp)))
        (Kg.reg rDest) (natToDigits v) with hSg2
  have step3 := restoreMem_loop rDest rAddr (Sg2 (Kg.scratch .logTmp)) Sg2
    ({memSym := some MemSym.entryEnd, queryDigit := none, equal := true} : LoadState) rfl
  set CA := (natToDigits a).reverse.length + 1 with hCA
  set RV := (natToDigits v).reverse.length + 1 with hRV
  set RM := (Sg2 (Kg.scratch .queryTmp)).length + 1
      + ((Sg2 (Kg.scratch .query)).length + 1) + ((Sg2 (Kg.scratch .logTmp)).length + 1)
    with hRM
  refine ⟨RM + (RV + CA), ?_, ?_⟩
  · rw [Function.iterate_add_apply (flipBindLoad rDest rAddr) RM (RV + CA),
      Function.iterate_add_apply (flipBindLoad rDest rAddr) RV CA, step1, step2, step3]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k with
    | reg i =>
        by_cases hi : i = rDest
        · subst hi; simp [Function.update, hSg2, scanResult]
        · simp [Function.update, hSg2, hSg1, hi]
    | mem =>
        simp [Function.update, hSg2, hSg1, encodeLog, encodeEntry, List.append_assoc]
    | io => simp [Function.update, hSg2, hSg1]
    | scratch s => cases s <;> simp [Function.update, hSg2, hSg1]
  · have hRVlen : (natToDigits v).reverse.length ≤ (Sg Kg.mem).length := by
      rw [List.length_reverse, hMemLen]; omega
    have hCAlen : (natToDigits a).reverse.length ≤ (Sg Kg.mem).length := by
      rw [List.length_reverse, hMemLen]; omega
    have hSg2qt : Sg2 (Kg.scratch .queryTmp) = natToDigits a ++ Sg (Kg.scratch .queryTmp) := by
      rw [hSg2, hSg1]; simp [Function.update]
    have hSg2q : Sg2 (Kg.scratch .query) = ([] : List Digit) := by
      rw [hSg2, hSg1]; simp [Function.update]
    have hSg2lt : Sg2 (Kg.scratch .logTmp) = (MemSym.entryEnd :: (natToDigits v).map
        MemSym.digit) ++ ((MemSym.addrEnd :: (natToDigits a).map MemSym.digit)
          ++ Sg (Kg.scratch .logTmp)) := by
      rw [hSg2, hSg1]; simp [Function.update]
    have hqt0 : (Sg (Kg.scratch .queryTmp)).length = 0 := by rw [hQueryTmp]; rfl
    have hstep_le : RM + (RV + CA) ≤ 32 * scanPotential Sg := by
      rw [hRM, hSg2qt, hSg2q, hSg2lt, hCA, hRV]
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
        List.length_reverse, hqt0, scanPotential]
      omega
    have h2le : (2 : ℕ) ≤ xs.length + 1 + 1 := by omega
    calc RM + (RV + CA) ≤ 32 * scanPotential Sg := hstep_le
      _ ≤ 16 * (xs.length + 1 + 1) * scanPotential Sg := by
          have := Nat.mul_le_mul_right (scanPotential Sg) (by omega : (32:ℕ) ≤ 16 * (xs.length+1+1))
          simpa using this

/-- `scanPhase_bounded` when the first log entry misses the target address: compare and restore,
    skip the value, then continue on the tail by the induction hypothesis (`scanPotential` is
    conserved across the entry). -/
lemma scanPhase_bounded_mismatch (a v addr : ℕ) (xs : WriteLog) (Sg : ∀ k, List (Γg p k))
    (s0 : LoadState)
    (hDest : Sg (Kg.reg rDest) = ([] : List Digit))
    (hMem : Sg Kg.mem = encodeLog ((a, v) :: xs))
    (hQuery : Sg (Kg.scratch .query) = (natToDigits addr).reverse)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) (hmatch : ¬ a = addr)
    (ih : ∀ (Sg : ∀ k, List (Γg p k)) (s0 : LoadState), s0.equal = true →
      s0.queryDigit = none → Sg (Kg.reg rDest) = ([] : List Digit) →
      Sg Kg.mem = encodeLog xs → Sg (Kg.scratch .query) = (natToDigits addr).reverse →
      Sg (Kg.scratch .queryTmp) = ([] : List Digit) →
      ScanPhaseBoundedGoal rDest rAddr addr xs Sg s0) :
    ScanPhaseBoundedGoal rDest rAddr addr ((a, v) :: xs) Sg s0 := by
  unfold ScanPhaseBoundedGoal
  have hne : (natToDigits a).reverse ≠ (natToDigits addr).reverse :=
    fun h => hmatch (natToDigits_injective (List.reverse_injective h))
  have hmis : ¬ (s0.equal = true ∧ (natToDigits a).reverse = (natToDigits addr).reverse) :=
    fun ⟨_, h⟩ => hne h
  have hMem1 : Sg Kg.mem = (natToDigits a).reverse.map MemSym.digit
      ++ (MemSym.addrEnd :: ((natToDigits v).reverse.map MemSym.digit
        ++ (MemSym.entryEnd :: encodeLog xs))) := by
    simp [hMem, encodeLog, encodeEntry, List.append_assoc]
  have hMemLen : (Sg Kg.mem).length
      = (natToDigits a).length + (natToDigits v).length + 2 + (encodeLog xs).length := by
    rw [hMem1]; simp only [List.length_append, List.length_map, List.length_reverse,
      List.length_cons]; omega
  have step1 := compareAddr_mismatch_then_restore rDest rAddr (natToDigits a).reverse
    (natToDigits addr).reverse
    ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs))
    Sg s0 hmis hMem1 hQuery
  rw [List.reverse_reverse, hQueryTmp] at step1
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at step1
  set Sg1 := Function.update
        (Function.update
          (Function.update (Function.update Sg Kg.mem
            ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs)))
            (Kg.scratch .logTmp)
            ((MemSym.addrEnd :: (natToDigits a).map MemSym.digit) ++ Sg (Kg.scratch .logTmp)))
          (Kg.scratch .queryTmp) [])
        (Kg.scratch .query) (natToDigits addr).reverse
    with hSg1
  have hMem2 : Sg1 Kg.mem = (natToDigits v).reverse.map MemSym.digit
      ++ (MemSym.entryEnd :: encodeLog xs) := by
    rw [hSg1]; simp [Function.update]
  have step2 := skipValue_loop rDest rAddr (natToDigits v).reverse (encodeLog xs) Sg1
    {memSym := some MemSym.addrEnd, queryDigit := none, equal := false} hMem2
  conv at step2 => rhs; rw [List.map_reverse, List.reverse_reverse]
  set Sg2 := Function.update (Function.update Sg1 Kg.mem (encodeLog xs))
        (Kg.scratch .logTmp)
        ((MemSym.entryEnd :: (natToDigits v).map MemSym.digit) ++ Sg1 (Kg.scratch .logTmp))
    with hSg2
  have hDest2 : Sg2 (Kg.reg rDest) = ([] : List Digit) := by
    rw [hSg2, hSg1]; simp [Function.update, hDest]
  have hQuery2 : Sg2 (Kg.scratch .query) = (natToDigits addr).reverse := by
    rw [hSg2, hSg1]; simp [Function.update]
  have hQueryTmp2 : Sg2 (Kg.scratch .queryTmp) = ([] : List Digit) := by
    rw [hSg2, hSg1]; simp [Function.update]
  have hSg2mem : Sg2 Kg.mem = encodeLog xs := by rw [hSg2, hSg1]; simp [Function.update]
  have hSg2lt : Sg2 (Kg.scratch .logTmp) = (MemSym.entryEnd :: (natToDigits v).map
      MemSym.digit) ++ ((MemSym.addrEnd :: (natToDigits a).map MemSym.digit)
        ++ Sg (Kg.scratch .logTmp)) := by
    rw [hSg2, hSg1]; simp [Function.update]
  obtain ⟨n', hstep3, hn'bound⟩ := ih Sg2
    {memSym := some MemSym.entryEnd, queryDigit := none, equal := true}
    rfl rfl hDest2 hSg2mem hQuery2 hQueryTmp2
  set CAM := (natToDigits a).reverse.length + 1
    + (min (natToDigits a).reverse.length (natToDigits addr).reverse.length + 1) with hCAM
  set SV := (natToDigits v).reverse.length + 1 with hSV
  refine ⟨n' + (SV + CAM), ?_, ?_⟩
  · rw [Function.iterate_add_apply (flipBindLoad rDest rAddr) n' (SV + CAM),
      Function.iterate_add_apply (flipBindLoad rDest rAddr) SV CAM, step1, step2, hstep3]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k with
    | reg i =>
        by_cases hi : i = rDest
        · subst hi
          simp [Function.update, scanResult, hmatch]
        · simp [Function.update, hSg2, hSg1, hi]
    | mem =>
        simp [Function.update, hSg2, hSg1, encodeLog, encodeEntry, List.append_assoc,
          List.reverse_append, List.map_reverse]
    | io => simp [Function.update, hSg2, hSg1]
    | scratch s => cases s <;> simp [Function.update, hSg2, hSg1]
  · have hn'potential : scanPotential Sg2 = scanPotential Sg := by
      simp only [scanPotential, hSg2mem, hQuery2, hSg2lt, hQuery]
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    rw [hn'potential] at hn'bound
    have hstep_le : SV + CAM ≤ 16 * scanPotential Sg := by
      rw [hCAM, hSV]
      simp only [List.length_reverse, scanPotential, hQuery]
      have hqmin : min (natToDigits a).length (natToDigits addr).length
          ≤ (natToDigits addr).length := min_le_right _ _
      have hAlen : (natToDigits a).length ≤ (Sg Kg.mem).length := by rw [hMemLen]; omega
      have hVlen : (natToDigits v).length ≤ (Sg Kg.mem).length := by rw [hMemLen]; omega
      omega
    calc n' + (SV + CAM) ≤ 16 * (xs.length + 1) * scanPotential Sg + 16 * scanPotential Sg :=
          by omega
      _ = 16 * (xs.length + 1 + 1) * scanPotential Sg := by ring


/-- Quantitative companion to `scan_phase`: same statement, plus a bound on the witness step
    count `n`, linear in the number of remaining log entries and in `scanPotential`. Proved by
    the same induction as `scan_phase`; see the module notes above `scanPotential` for why the
    bound has this shape. -/
lemma scanPhase_bounded (addr : ℕ) (log : WriteLog) (Sg : ∀ k, List (Γg p k)) (s0 : LoadState)
    (heq : s0.equal = true) (hqd : s0.queryDigit = none)
    (hDest : Sg (Kg.reg rDest) = ([] : List Digit)) (hMem : Sg Kg.mem = encodeLog log)
    (hQuery : Sg (Kg.scratch .query) = (natToDigits addr).reverse)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = ([] : List Digit)) :
    ∃ n, (flipBindLoad rDest rAddr)^[n]
        (some (⟨some LoadPhase.compareAddr, s0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {memSym := none, queryDigit := none, equal := true},
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update Sg Kg.mem
                    ((Sg (Kg.scratch .logTmp)).reverse ++ encodeLog log))
                  (Kg.scratch .logTmp) [])
                (Kg.scratch .query) [])
              (Kg.scratch .queryTmp) [])
            (Kg.reg rDest) (scanResult addr log)⟩ ∧
        n ≤ 16 * (log.length + 1) * scanPotential Sg := by
  induction log generalizing Sg s0 with
  | nil => exact scanPhase_bounded_nil rDest rAddr addr Sg s0 heq hDest hMem hQueryTmp
  | cons e xs ih =>
      obtain ⟨a, v⟩ := e
      by_cases hmatch : a = addr
      · subst hmatch
        exact scanPhase_bounded_match rDest rAddr a v xs Sg s0 heq hDest hMem hQuery hQueryTmp
      · exact scanPhase_bounded_mismatch rDest rAddr a v addr xs Sg s0 hDest hMem hQuery
          hQueryTmp hmatch ih

/-- Quantitative companion to `realize_load`: same statement, plus a bound on the witness step
    count, combining `setup_phase`'s (already closed-form) drain/restore cost with
    `scanPhase_bounded`'s scan bound (converted from linear-in-`log.length` to quadratic via
    `log_length_le_encodeLog_length`). -/
lemma realize_load_bounded (addr : ℕ) (log : WriteLog) (Sg : ∀ k, List (Γg p k))
    (v0 : LoadState)
    (hAddr : Sg (Kg.reg rAddr) = natToDigits addr) (hMem : Sg Kg.mem = encodeLog log)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hQ : Sg (Kg.scratch .query) = ([] : List Digit))
    (hQt : Sg (Kg.scratch .queryTmp) = ([] : List Digit))
    (hLt : Sg (Kg.scratch .logTmp) = ([] : List MemSym)) (heq : v0.equal = true) :
    ∃ n, (flipBindLoad rDest rAddr)^[n]
        (some (⟨some LoadPhase.copyQuery, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {memSym := none, queryDigit := none, equal := true},
          Function.update Sg (Kg.reg rDest) (scanResult addr log)⟩ ∧
      n ≤ 32 * ((Sg (Kg.reg rDest)).length + (Sg Kg.mem).length
        + (natToDigits addr).length + 1) ^ 2 := by
  obtain ⟨Sg', hEq, hRDest', hQuery', hMem', hQueryTmp', hLogTmp', hOther'⟩ :=
    setup_phase rDest rAddr (natToDigits addr) (Sg (Kg.reg rDest)) Sg v0 hAddr rfl hSc
  obtain ⟨n2, hstep2, hn2bound⟩ := scanPhase_bounded rDest rAddr addr log Sg'
    {v0 with queryDigit := none} heq rfl hRDest' (by rw [hMem']; exact hMem)
    (by rw [hQuery']; simp [hQ]) (by rw [hQueryTmp']; exact hQt)
  refine ⟨n2 + ((Sg (Kg.reg rDest)).length + 1 + (2 * (natToDigits addr).length + 2)), ?_, ?_⟩
  · rw [Function.iterate_add_apply, hEq, hstep2]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    by_cases hk : k = Kg.reg rDest
    · subst hk; simp [Function.update]
    · cases k with
      | reg i =>
          simp [Function.update, hOther' (Kg.reg i) hk (by simp) (by simp) (by simp) (by simp)]
      | mem => simp [Function.update, hLogTmp', hLt, hMem]
      | io => simp [Function.update, hOther' Kg.io hk (by simp) (by simp) (by simp) (by simp)]
      | scratch s =>
          cases s with
          | query => simp [Function.update, hQ]
          | queryTmp => simp [Function.update, hQt]
          | logTmp => simp [Function.update, hLt]
          | copyScratch =>
              simp [Function.update,
                hOther' (Kg.scratch .copyScratch) hk (by simp) (by simp) (by simp) (by simp)]
          | workRev =>
              simp [Function.update,
                hOther' (Kg.scratch .workRev) hk (by simp) (by simp) (by simp) (by simp)]
          | lhsOperand =>
              simp [Function.update,
                hOther' (Kg.scratch .lhsOperand) hk (by simp) (by simp) (by simp) (by simp)]
          | rhsOperand =>
              simp [Function.update,
                hOther' (Kg.scratch .rhsOperand) hk (by simp) (by simp) (by simp) (by simp)]
          | sumScratch =>
              simp [Function.update,
                hOther' (Kg.scratch .sumScratch) hk (by simp) (by simp) (by simp) (by simp)]
          | diffScratch =>
              simp [Function.update,
                hOther' (Kg.scratch .diffScratch) hk (by simp) (by simp) (by simp) (by simp)]
          | prologueCounter =>
              simp [Function.update,
                hOther' (Kg.scratch .prologueCounter) hk (by simp) (by simp) (by simp) (by simp)]
          | prologueWork =>
              simp [Function.update,
                hOther' (Kg.scratch .prologueWork) hk (by simp) (by simp) (by simp) (by simp)]
  · have hpot : scanPotential Sg' = (Sg Kg.mem).length + (natToDigits addr).length + 1 := by
      simp only [scanPotential, hMem', hLogTmp', hLt, hQuery', hQ]
      simp only [List.length_append, List.length_reverse, List.length_nil]
      omega
    have hloglen : log.length + 1 ≤ scanPotential Sg' := by
      have h1 := log_length_le_encodeLog_length log
      rw [hpot, hMem]; omega
    set P := (Sg (Kg.reg rDest)).length + (Sg Kg.mem).length + (natToDigits addr).length + 1
      with hP
    have hPpos : 1 ≤ P := by rw [hP]; omega
    have hpotP : scanPotential Sg' ≤ P := by rw [hpot, hP]; omega
    have hn2 : n2 ≤ 16 * P ^ 2 := by
      calc n2 ≤ 16 * (log.length + 1) * scanPotential Sg' := hn2bound
        _ ≤ 16 * scanPotential Sg' * scanPotential Sg' := by
            nlinarith [hloglen, Nat.zero_le (scanPotential Sg')]
        _ ≤ 16 * P * P := by nlinarith [hpotP, Nat.zero_le (scanPotential Sg')]
        _ = 16 * P ^ 2 := by ring
    have hsetup : (Sg (Kg.reg rDest)).length + 1 + (2 * (natToDigits addr).length + 2)
        ≤ 16 * P ^ 2 := by
      nlinarith [hPpos, hP]
    omega

/-- The generalized `load` instruction, realized against an arbitrary site's register pair
    (`rDest`/`rAddr`, possibly equal): starting with register `rAddr` holding `natToDigits addr`,
    `mem` holding exactly `encodeLog log`, and every scratch stack empty, running `loadProg` from
    `copyQuery` for some number of steps reaches `done` with every stack untouched except `rDest`,
    which ends up holding `scanResult addr log` — `natToDigits` of whatever `BitCostRAM.step`'s
    `load` would read at `addr`. Alias-safe for `rDest = rAddr` (module docstring). Combines
    `setup_phase` (drain/restore `rAddr`, clear `rDest`) with `scan_phase` (the scan itself).
    Generalizes `MemoryLoad.realize_load`. -/
lemma realize_load (addr : ℕ) (log : WriteLog) (Sg : ∀ k, List (Γg p k)) (v0 : LoadState)
    (hAddr : Sg (Kg.reg rAddr) = natToDigits addr) (hMem : Sg Kg.mem = encodeLog log)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hQ : Sg (Kg.scratch .query) = ([] : List Digit))
    (hQt : Sg (Kg.scratch .queryTmp) = ([] : List Digit))
    (hLt : Sg (Kg.scratch .logTmp) = ([] : List MemSym)) (heq : v0.equal = true) :
    ∃ n, (flipBindLoad rDest rAddr)^[n]
        (some (⟨some LoadPhase.copyQuery, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadPhase LoadState))
      = some ⟨some LoadPhase.done, {memSym := none, queryDigit := none, equal := true},
          Function.update Sg (Kg.reg rDest) (scanResult addr log)⟩ := by
  obtain ⟨n, hrun, -⟩ := realize_load_bounded rDest rAddr addr log Sg v0 hAddr hMem hSc hQ hQt hLt
    heq
  exact ⟨n, hrun⟩

/-! ## Site dispatcher package

Mirrors `GenericStore.lean`'s `storeCode`/`store_impl_growingBoundedSiteStepSim` pattern: `loadCode` casts the
whole local `LoadPhase`-indexed function once via `cast_apply_phaseOf`, and
`load_impl_growingBoundedSiteStepSim` transports `realize_load`'s local run into the global machine via
`iterate_bind_step_liftStmt` followed by one bridge step. -/

/-- `load`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `loadProg` lifted via `execVia`. -/
def loadCodeBody (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr) : LoadPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = LoadPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getLoad AllInstrState.setLoad
        (loadProg (regAt p pc rDest (by rw [h]; simp [regsOf]))
          (regAt p pc rAddr (by rw [h]; simp [regsOf])) l)

/-- `loadCodeBody`, cast once from `LoadPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def loadCode (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (loadCodeBody p pc rDest rAddr h)

/-- `loadCode` undoes its own cast when applied to a correspondingly-cast `LoadPhase` value. -/
lemma loadCode_apply (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr) (l : LoadPhase) :
    loadCode p pc rDest rAddr h (cast (congrArg PhaseOf h.symm) l) =
      loadCodeBody p pc rDest rAddr h l :=
  cast_apply_phaseOf p pc h (loadCodeBody p pc rDest rAddr h) l

/-- Any dispatcher agreeing with `loadCode` at site `pc` installs the lifted `loadProg` tree at
    every non-`done` label. -/
lemma loadCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadCode p pc rDest rAddr h) M) :
    ∀ l : LoadPhase, l ≠ LoadPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getLoad AllInstrState.setLoad
        (loadProg (regAt p pc rDest (by rw [h]; simp [regsOf]))
          (regAt p pc rAddr (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    loadCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `loadCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `load`'s own `done` label. -/
lemma loadCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadCode p pc rDest rAddr h) M) :
    M (execVia p pc h LoadPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) LoadPhase.done)
  rw [show execVia p pc h LoadPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) LoadPhase.done) from rfl, hone,
    loadCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- A `load` step only rewrites register `rDest`, to the memory word at the address register. -/
lemma load_impl_growing_bounded_step_regs (rDest rAddr : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.load rDest rAddr) :
    (step r).regs = bankWrite r.regs rDest (r.mem (r.regs rAddr)) := by
  simp [step, hcurEq]

/-- The current instruction is `load` at the site's program counter. -/
lemma load_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rDest rAddr : ℕ) (h : p.get pc = .load rDest rAddr) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.load rDest rAddr := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `copyQuery`
    entry. -/
lemma load_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rDest rAddr : ℕ) (h : p.get pc = .load rDest rAddr)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h LoadPhase.copyQuery) := by
  have hstart : startPhaseOpt (Instruction.load rDest rAddr) = some LoadPhase.copyQuery := rfl
  have hentry : entryAt p pc.1 = execVia p pc h LoadPhase.copyQuery :=
    entryAt_eq_execVia p pc h LoadPhase.copyQuery hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `load` site run on the global machine: the `loadProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (only `rDest'`
    rewritten, to the scan result) and a step count bound. -/
lemma load_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rDest rAddr : ℕ) (h : p.get pc = .load rDest rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadCode p pc rDest rAddr h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h LoadPhase.copyQuery))
    (rDest' rAddr' : Fin (regBound p))
    (hrDest' : rDest' = regAt p pc rDest (by rw [h]; simp [regsOf]))
    (hrAddr' : rAddr' = regAt p pc rAddr (by rw [h]; simp [regsOf])) (a : ℕ) (log : WriteLog)
    (hAddr : cfg.stk (Kg.reg rAddr') = natToDigits a) (hMem : cfg.stk Kg.mem = encodeLog log)
    (hCopy : cfg.stk (Kg.scratch ScratchKind.copyScratch) = [])
    (hQ : cfg.stk (Kg.scratch ScratchKind.query) = [])
    (hQt : cfg.stk (Kg.scratch ScratchKind.queryTmp) = [])
    (hLt : cfg.stk (Kg.scratch ScratchKind.logTmp) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ 32 * ((cfg.stk (Kg.reg rDest')).length + (cfg.stk Kg.mem).length
        + (natToDigits a).length + 1) ^ 2 + 1 ∧
      Sgf = Function.update cfg.stk (Kg.reg rDest') (scanResult a log) := by
  have hag := loadCode_agrees_ne_done p pc rDest rAddr h M hAgrees
  rw [← hrDest', ← hrAddr'] at hag
  obtain ⟨N, hLoadRun, hNbound⟩ := realize_load_bounded rDest' rAddr' a log cfg.stk
    ⟨none, none, true⟩ hAddr hMem hCopy hQ hQt hLt rfl
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getLoad AllInstrState.setLoad (loadProg rDest' rAddr') M
      Function.injective_id AllInstrState.getLoad_setLoad AllInstrState.setLoad_setLoad
      AllInstrState.setLoad_getLoad N LoadPhase.copyQuery ⟨none, none, true⟩ cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      LoadPhase.done ⟨none, none, true⟩
      (Function.update cfg.stk (Kg.reg rDest') (scanResult a log))
      rfl hag hLoadRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h LoadPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h LoadPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h LoadPhase.done)) sf Sgf) from rfl,
      loadCode_agrees_done p pc rDest rAddr h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h LoadPhase.copyQuery), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨N + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `load` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma load_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rDest rAddr : ℕ) (rDest' : Fin (regBound p)) (hrDestval : rDest'.1 = rDest)
    (hcurEq : r.current = Instruction.load rDest rAddr)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rDest') (natToDigits (r.mem (r.regs rAddr)))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rDest') _ _⟩
  rw [load_impl_growing_bounded_step_regs rDest rAddr r hcurEq]
  by_cases hi : i = rDest'
  · rw [hi, Function.update_self, ← hrDestval, bankWrite_same]
  · have hid : i.1 ≠ rDest := by rw [← hrDestval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rDest' by simp [hi])]
    exact hregs i

/-- The configuration reached after a `load` run represents the stepped RAM, given the register
    frame and the untouched non-register stacks. -/
lemma load_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rDest rAddr : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.load rDest rAddr)
    (Sgf : ∀ k, List (Γg p k))
    (hreg : ∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    Represents p ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ (step r) := by
  obtain ⟨hprog, -, ⟨log, hmemstk, hmemlookup⟩, -, hscratch, -⟩ := hRep
  have hpcSucc : (step r).pc = pc.1 + 1 := by simp [step, hcurEq]; simpa using hpcEq
  refine ⟨by simp [step, hcurEq, hprog], hreg, ⟨log, ?_, ?_⟩, rfl, ?_, ?_⟩
  · show Sgf Kg.mem = _
    rw [hother _ (by simp)]; exact hmemstk
  · intro a; rw [step, hcurEq]; exact hmemlookup a
  · intro s; show Sgf (Kg.scratch s) = _
    rw [hother _ (by simp)]; exact hscratch s
  · simp only [ControlRep]; exact congrArg some (congrArg (entryAt p) hpcSucc.symm)

/-- Step-count bound: the run's cost is at most `256` times the squared potential, since the
    destination and address lengths are bounded by `regSize` and the memory stack length is part of
    the potential. -/
lemma load_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rAddr : ℕ) (rDest' rAddr' : Fin (regBound p)) (hraddrval : rAddr'.1 = rAddr)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) (n : ℕ)
    (hn : n ≤ 32 * ((cfg.stk (Kg.reg rDest')).length + (cfg.stk Kg.mem).length
      + (natToDigits (r.regs rAddr)).length + 1) ^ 2 + 1) :
    n ≤ 256 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle1 : (cfg.stk (Kg.reg rDest')).length ≤ regSize p r := by
    rw [hregs rDest']; exact natToDigits_length_le_regSize p r rDest'
  have hle2 := natToDigits_length_le_regSize p r rAddr'
  rw [hraddrval] at hle2
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hlin : (cfg.stk (Kg.reg rDest')).length + (cfg.stk Kg.mem).length
      + (natToDigits (r.regs rAddr)).length + 1 ≤ 2 * X := by omega
  have hsq := Nat.pow_le_pow_left hlin 2
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  have h4 : (2 * X) ^ 2 = 4 * X ^ 2 := by ring
  omega

/-- Potential growth: only `rDest` changes, to the loaded word, whose digit length is at most its
    `bitLen` (charged by `instructionCost`), and the memory stack is untouched. -/
lemma load_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rDest rAddr : ℕ)
    (rDest' : Fin (regBound p)) (hrDestval : rDest'.1 = rDest)
    (hcurEq : r.current = Instruction.load rDest rAddr) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := load_impl_growing_bounded_step_regs rDest rAddr r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits (r.mem (r.regs rAddr))).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrDestval]
    exact regSize_bankWrite_le p r rDest' (r.mem (r.regs rAddr)) _ le_rfl
  have hle : (natToDigits (r.mem (r.regs rAddr))).length ≤ bitLen (r.mem (r.regs rAddr)) :=
    natToDigits_length_le_bitLen _
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rAddr) + bitLen (r.mem (r.regs rAddr)) + 1 := by rw [hcurEq]; rfl
  rw [hother _ (by simp)]
  omega

/-- `loadCode`'s growth companion: `mem` is untouched, and the only register that can grow is
    `rDest`, to `natToDigits (r.mem (r.regs rAddr))`'s digit length — bounded by `instructionCost`
    (`bitLen (regs rAddr) + bitLen (mem (regs rAddr)) + 1`) via `natToDigits_length_le_bitLen`. -/
lemma load_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr) :
    GrowingBoundedSiteStepSim p pc (loadCode p pc rDest rAddr h) 256 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  obtain ⟨log, hmemstk, hmemlookup⟩ := hRep.2.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := load_impl_growing_bounded_current p pc rDest rAddr h r hprog hpcEq
  have hcl := load_impl_growing_bounded_label p pc rDest rAddr h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rDest', hrDest'⟩ : ∃ x, x = regAt p pc rDest (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rAddr', hrAddr'⟩ : ∃ x, x = regAt p pc rAddr (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrDestval : rDest'.1 = rDest := by rw [hrDest']; rfl
  have hrAddrval : rAddr'.1 = rAddr := by rw [hrAddr']; rfl
  have hAddr : cfg.stk (Kg.reg rAddr') = natToDigits (r.regs rAddr) := by
    rw [hregs rAddr', hrAddrval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := load_impl_growing_bounded_run p pc rDest rAddr h M hAgrees
    cfg hvar hcl rDest' rAddr' hrDest' hrAddr' _ log hAddr hmemstk (hscratch .copyScratch)
    (hscratch .query) (hscratch .queryTmp) (hscratch .logTmp)
  have hSgf' : Sgf = Function.update cfg.stk (Kg.reg rDest') (natToDigits (r.mem (r.regs rAddr))) := by
    rw [hSgf, scanResult_eq_lookupD, hmemlookup]
  obtain ⟨hreg, hother⟩ := load_impl_growing_bounded_stk cfg.stk r rDest rAddr rDest' hrDestval
    hcurEq hregs Sgf hSgf'
  exact ⟨n, _, hrun,
    load_impl_growing_bounded_represents p pc rDest rAddr cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    load_impl_growing_bounded_time p cfg r rAddr rDest' rAddr' hrAddrval hregs n hn,
    load_impl_growing_bounded_growth p cfg r rDest rAddr rDest' hrDestval hcurEq Sgf hother⟩

/-- `load`'s `GrowingTimedInstrImpl` package. -/
def loadGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rDest rAddr : ℕ)
    (h : p.get pc = .load rDest rAddr) : GrowingTimedInstrImpl p pc where
  code := loadCode p pc rDest rAddr h
  C := 256
  G := 1
  growingSim := load_impl_growingBoundedSiteStepSim p pc rDest rAddr h

module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.MemoryStore2
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `store` realized against an arbitrary register pair

This module defines `storeProg` directly against the program-parameterized stack type `Kg p`. Its
source and address are arbitrary register indices, so the same realization can be dispatched at
any program position without embedding a private stack type. `Store2Phase` supplies the control
states, and the configuration records each stack as a function of its key.

**Alias safety** (`rSrc = rAddr`): `copyValue` and `copyValueRestore` preserve the source before
`copyAddr` reads the address. Thus no case split on register-index equality is needed. The store
operation writes only to `mem`, leaving every register unchanged.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym Store2Phase natToDigits encodeEntry
  liftStmt iterate_bind_step_liftStmt WriteLog lookupD encodeLog)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rSrc rAddr : Fin (regBound p))

/-- `store`'s `Stmt` tree at an arbitrary register pair: push the entry terminator,
    non-destructively copy `rSrc`'s digits onto `mem`, push the address terminator,
    non-destructively copy `rAddr`'s digits onto `mem` — identical combinator to
    `MemoryStore2.store2Prog`, operating on `Kg p` directly instead of `MemoryStore2`'s dedicated
    `Store2K`. -/
def storeProg : Store2Phase → Turing.TM2.Stmt (Γg p) Store2Phase (Option Digit)
  | .pushEntryEnd => push Kg.mem (fun _ => MemSym.entryEnd) (goto (fun _ => .copyValue))
  | .copyValue =>
      pop (Kg.reg rSrc) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Kg.mem (fun s => MemSym.digit (s.getD default))
            (push (Kg.scratch .copyScratch) (fun s => s.getD default)
              (goto (fun _ => .copyValue))))
          (goto (fun _ => .copyValueRestore)))
  | .copyValueRestore =>
      pop (Kg.scratch .copyScratch) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push (Kg.reg rSrc) (fun s => s.getD default) (goto (fun _ => .copyValueRestore)))
          (goto (fun _ => .pushAddrEnd)))
  | .pushAddrEnd => push Kg.mem (fun _ => MemSym.addrEnd) (goto (fun _ => .copyAddr))
  | .copyAddr =>
      pop (Kg.reg rAddr) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Kg.mem (fun s => MemSym.digit (s.getD default))
            (push (Kg.scratch .copyScratch) (fun s => s.getD default)
              (goto (fun _ => .copyAddr))))
          (goto (fun _ => .copyAddrRestore)))
  | .copyAddrRestore =>
      pop (Kg.scratch .copyScratch) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push (Kg.reg rAddr) (fun s => s.getD default) (goto (fun _ => .copyAddrRestore)))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindStore :
    Option (Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) →
      Option (Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) :=
  fun x => x.bind (Turing.TM2.step (storeProg rSrc rAddr))

lemma flipBindStore_pushEntryEnd (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.pushEntryEnd, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyValue, v0,
          Function.update Sg Kg.mem (MemSym.entryEnd :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.pushEntryEnd, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg]

lemma flipBindStore_pushAddrEnd (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.pushAddrEnd, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyAddr, v0,
          Function.update Sg Kg.mem (MemSym.addrEnd :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.pushAddrEnd, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg]

lemma flipBindStore_copyValue_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hSrc : Sg (Kg.reg rSrc) = d :: rest) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyValue, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyValue, some d,
          Function.update (Function.update (Function.update Sg (Kg.reg rSrc) rest)
            Kg.mem (MemSym.digit d :: Sg Kg.mem))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyValue, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSrc]

lemma flipBindStore_copyValue_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hSrc : Sg (Kg.reg rSrc) = ([] : List Digit)) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyValue, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyValueRestore, none, Sg⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyValue, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSrc]

/-- Draining register `rSrc`, prepending its reverse onto `mem` (digit-wrapped) and onto
    `copyScratch` (unwrapped). Generalizes `MemoryStore2.store2_copyValue_loop`. -/
lemma store_copyValue_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSrc : Sg (Kg.reg rSrc) = src) :
    (flipBindStore rSrc rAddr)^[src.length + 1]
        (some (⟨some Store2Phase.copyValue, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyValueRestore, none,
          Function.update (Function.update (Function.update Sg (Kg.reg rSrc) [])
            Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem))
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.map_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rSrc) [])
          Kg.mem (Sg Kg.mem)) (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rSrc
        · subst hk; simp [Function.update, hSrc]
        · by_cases hk2 : k = Kg.mem
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .copyScratch
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindStore_copyValue_nil_exit rSrc rAddr Sg v0 hSrc
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindStore_copyValue_cons rSrc rAddr d src' Sg v0 hSrc,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rSrc) src')
              Kg.mem (MemSym.digit d :: Sg Kg.mem)) (Kg.scratch .copyScratch)
              (d :: Sg (Kg.scratch .copyScratch)))
           (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rSrc
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.mem
        · subst hk2; simp [Function.update]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindStore_copyValueRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyValueRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyValueRestore, some d,
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rSrc) (d :: Sg (Kg.reg rSrc))⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyValueRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSc]

lemma flipBindStore_copyValueRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyValueRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.pushAddrEnd, none, Sg⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyValueRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSc]

/-- The `copyValueRestore` loop: draining `copyScratch` restores `rSrc`, generalizing
    `MemoryStore2.store2_copyValueRestore_loop`. -/
lemma store_copyValueRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k))
    (v0 : Option Digit) (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindStore rSrc rAddr)^[copyScratch.length + 1]
        (some (⟨some Store2Phase.copyValueRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.pushAddrEnd, none,
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.reg rSrc) (copyScratch.reverse ++ Sg (Kg.reg rSrc))⟩ := by
  induction copyScratch generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
          (Kg.reg rSrc) (Sg (Kg.reg rSrc)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .copyScratch
        · subst hk; simp [Function.update, hSc]
        · by_cases hk2 : k = Kg.reg rSrc
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindStore_copyValueRestore_nil_exit rSrc rAddr Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindStore_copyValueRestore_cons rSrc rAddr d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rSrc) (d :: Sg (Kg.reg rSrc))) (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rSrc
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the value-register copy to completion: register `rSrc` is restored exactly, and
    its reverse (digit-wrapped) is prepended onto `mem`. Generalizes
    `MemoryStore2.store2_copyValue_phase`. -/
lemma store_copyValue_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSrc : Sg (Kg.reg rSrc) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindStore rSrc rAddr)^[2 * src.length + 2]
        (some (⟨some Store2Phase.copyValue, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.pushAddrEnd, none,
          Function.update Sg Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem)⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, store_copyValue_loop rSrc rAddr src Sg v0 hSrc]
  simp only [hSc, List.append_nil]
  have h2 := store_copyValueRestore_loop rSrc rAddr src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rSrc) [])
      Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem)) (Kg.scratch .copyScratch) (src.reverse))
    none (by simp)
  rw [h2]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
  funext k
  by_cases hk : k = Kg.reg rSrc
  · subst hk; simp [Function.update, hSrc]
  · by_cases hk2 : k = Kg.mem
    · subst hk2; simp [Function.update, hk]
    · by_cases hk3 : k = Kg.scratch .copyScratch
      · subst hk3; simp [Function.update, hk, hk2, hSc]
      · simp [Function.update, hk, hk2, hk3]

lemma flipBindStore_copyAddr_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hAddr : Sg (Kg.reg rAddr) = d :: rest) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyAddr, some d,
          Function.update (Function.update (Function.update Sg (Kg.reg rAddr) rest)
            Kg.mem (MemSym.digit d :: Sg Kg.mem))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hAddr]

lemma flipBindStore_copyAddr_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hAddr : Sg (Kg.reg rAddr) = ([] : List Digit)) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyAddrRestore, none, Sg⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hAddr]

/-- The `copyAddr` analogue of `store_copyValue_loop`, for register `rAddr`. -/
lemma store_copyAddr_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hAddr : Sg (Kg.reg rAddr) = src) :
    (flipBindStore rSrc rAddr)^[src.length + 1]
        (some (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyAddrRestore, none,
          Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
            Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem))
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.map_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
          Kg.mem (Sg Kg.mem)) (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rAddr
        · subst hk; simp [Function.update, hAddr]
        · by_cases hk2 : k = Kg.mem
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .copyScratch
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindStore_copyAddr_nil_exit rSrc rAddr Sg v0 hAddr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindStore_copyAddr_cons rSrc rAddr d src' Sg v0 hAddr,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rAddr) src')
              Kg.mem (MemSym.digit d :: Sg Kg.mem)) (Kg.scratch .copyScratch)
              (d :: Sg (Kg.scratch .copyScratch)))
           (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rAddr
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.mem
        · subst hk2; simp [Function.update]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindStore_copyAddrRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyAddrRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.copyAddrRestore, some d,
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rAddr) (d :: Sg (Kg.reg rAddr))⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyAddrRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSc]

lemma flipBindStore_copyAddrRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindStore rSrc rAddr
        (some (⟨some Store2Phase.copyAddrRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.done, none, Sg⟩ := by
  show (Turing.TM2.step (storeProg rSrc rAddr))
      (⟨some Store2Phase.copyAddrRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)) = _
  simp [storeProg, hSc]

/-- The `copyAddrRestore` analogue of `store_copyValueRestore_loop`. -/
lemma store_copyAddrRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k))
    (v0 : Option Digit) (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindStore rSrc rAddr)^[copyScratch.length + 1]
        (some (⟨some Store2Phase.copyAddrRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.done, none,
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.reg rAddr) (copyScratch.reverse ++ Sg (Kg.reg rAddr))⟩ := by
  induction copyScratch generalizing Sg v0 with
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
      exact flipBindStore_copyAddrRestore_nil_exit rSrc rAddr Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindStore_copyAddrRestore_cons rSrc rAddr d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rAddr) (d :: Sg (Kg.reg rAddr))) (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rAddr
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the address-register copy to completion: register `rAddr` is restored exactly, and
    its reverse (digit-wrapped) is prepended onto `mem`. Generalizes
    `MemoryStore2.store2_copyAddr_phase`. -/
lemma store_copyAddr_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hAddr : Sg (Kg.reg rAddr) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindStore rSrc rAddr)^[2 * src.length + 2]
        (some (⟨some Store2Phase.copyAddr, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.done, none,
          Function.update Sg Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem)⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, store_copyAddr_loop rSrc rAddr src Sg v0 hAddr]
  simp only [hSc, List.append_nil]
  have h2 := store_copyAddrRestore_loop rSrc rAddr src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rAddr) [])
      Kg.mem ((src.reverse.map MemSym.digit) ++ Sg Kg.mem)) (Kg.scratch .copyScratch) (src.reverse))
    none (by simp)
  rw [h2]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
  funext k
  by_cases hk : k = Kg.reg rAddr
  · subst hk; simp [Function.update, hAddr]
  · by_cases hk2 : k = Kg.mem
    · subst hk2; simp [Function.update, hk]
    · by_cases hk3 : k = Kg.scratch .copyScratch
      · subst hk3; simp [Function.update, hk, hk2, hSc]
      · simp [Function.update, hk, hk2, hk3]

/-- The generalized `store` instruction, realized against an arbitrary site's register pair
    (`rSrc`/`rAddr`, possibly equal): starting from `pushEntryEnd` with `rSrc`/`rAddr` holding
    `natToDigits val`/`natToDigits addr` and `copyScratch` empty, running for
    `(2 * (natToDigits addr).length + 2) + 1 + (2 * (natToDigits val).length + 2) + 1` steps
    reaches `done` with every register untouched (`store` never writes registers, per
    `BitCostRAM.step`'s `.store` case) and `mem` prepended with `encodeEntry addr val` — exactly
    `BitCostRAM.step`'s effect for `store rSrc rAddr`. Generalizes
    `MemoryStore2.realize_store2` over an arbitrary site's register pair; alias-safe
    (see this file's module docstring). -/
lemma realize_store (addr val : ℕ) (Sg : ∀ k, List (Γg p k))
    (hSrc : Sg (Kg.reg rSrc) = natToDigits val) (hAddr : Sg (Kg.reg rAddr) = natToDigits addr)
    (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindStore rSrc rAddr)^[(2 * (natToDigits addr).length + 2) + 1
        + (2 * (natToDigits val).length + 2) + 1]
        (some (⟨some Store2Phase.pushEntryEnd, none, Sg⟩ :
          Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
      = some ⟨some Store2Phase.done, none,
          Function.update Sg Kg.mem (encodeEntry addr val ++ Sg Kg.mem)⟩ := by
  rw [Function.iterate_add_apply, Function.iterate_one,
    flipBindStore_pushEntryEnd rSrc rAddr Sg none, Function.iterate_add_apply]
  set Sg1 := Function.update Sg Kg.mem (MemSym.entryEnd :: Sg Kg.mem) with hSg1
  have hSrc1 : Sg1 (Kg.reg rSrc) = natToDigits val := by
    rw [hSg1, Function.update_of_ne (by simp)]; exact hSrc
  have hSc1 : Sg1 (Kg.scratch .copyScratch) = [] := by
    rw [hSg1, Function.update_of_ne (by simp)]; exact hSc
  rw [store_copyValue_phase rSrc rAddr (natToDigits val) Sg1 none hSrc1 hSc1,
    Function.iterate_add_apply, Function.iterate_one, flipBindStore_pushAddrEnd rSrc rAddr]
  set Sg2 := Function.update Sg1
      (Kg.mem : Kg p) ((List.map MemSym.digit (natToDigits val).reverse) ++ Sg1 Kg.mem) with hSg2
  set Sg3 := Function.update Sg2 Kg.mem (MemSym.addrEnd :: Sg2 Kg.mem) with hSg3
  have hAddr3 : Sg3 (Kg.reg rAddr) = natToDigits addr := by
    rw [hSg3, Function.update_of_ne (by simp), hSg2, Function.update_of_ne (by simp)]; exact hAddr
  have hSc3 : Sg3 (Kg.scratch .copyScratch) = [] := by
    rw [hSg3, Function.update_of_ne (by simp), hSg2, Function.update_of_ne (by simp)]; exact hSc
  rw [store_copyAddr_phase rSrc rAddr (natToDigits addr) Sg3 none hAddr3 hSc3]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.mem
  · subst hk; simp [hSg3, hSg2, hSg1, Function.update, encodeEntry, List.append_assoc]
  · simp [hSg3, hSg2, hSg1, Function.update, hk]

/-! ## Site dispatcher package

Wraps `storeProg`/`realize_store` into an `InstrImpl` for a site `pc` known (via `h`) to hold a
`store rSrc rAddr` instruction — the piece `GenericDispatcher.lean`'s `siteCode`/`Mg p` assembly
consumes. `storeCode` casts the *whole* local `Store2Phase`-indexed function once
(`cast_apply_phaseOf`) rather than casting each phase value where it is used, which is what lets
`storeCode_apply` below unfold by a single rewrite instead of getting stuck on two syntactically
divergent (though propositionally equal) cast subterms. -/

/-- `store`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `storeProg` lifted via `execVia`. -/
def storeCodeBody (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr) : Store2Phase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = Store2Phase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getStore AllInstrState.setStore
        (storeProg (regAt p pc rSrc (by rw [h]; simp [regsOf]))
          (regAt p pc rAddr (by rw [h]; simp [regsOf])) l)

/-- `storeCodeBody`, cast once from `Store2Phase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def storeCode (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (storeCodeBody p pc rSrc rAddr h)

/-- `storeCode` undoes its own cast when applied to a correspondingly-cast `Store2Phase` value. -/
lemma storeCode_apply (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr) (l : Store2Phase) :
    storeCode p pc rSrc rAddr h (cast (congrArg PhaseOf h.symm) l) =
      storeCodeBody p pc rSrc rAddr h l :=
  cast_apply_phaseOf p pc h (storeCodeBody p pc rSrc rAddr h) l

/-- Any dispatcher agreeing with `storeCode` at site `pc` installs the lifted `storeProg` tree at
    every non-`done` label — the `hM` hypothesis `iterate_bind_step_liftStmt` needs to transport
    `realize_store`'s local run into the global machine. -/
lemma storeCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (storeCode p pc rSrc rAddr h) M) :
    ∀ l : Store2Phase, l ≠ Store2Phase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getStore AllInstrState.setStore
        (storeProg (regAt p pc rSrc (by rw [h]; simp [regsOf]))
          (regAt p pc rAddr (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    storeCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `storeCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `store`'s own `done` label — the fact `store_impl_growingBoundedSiteStepSim`'s bridge step needs. -/
lemma storeCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (storeCode p pc rSrc rAddr h) M) :
    M (execVia p pc h Store2Phase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) Store2Phase.done)
  rw [show execVia p pc h Store2Phase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) Store2Phase.done) from rfl, hone,
    storeCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- A `store` step leaves every register untouched. -/
lemma store_impl_growing_bounded_step_regs (rSrc rAddr : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.store rSrc rAddr) :
    (step r).regs = r.regs := by
  simp [step, hcurEq]

/-- The current instruction is `store` at the site's program counter. -/
lemma store_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rSrc rAddr : ℕ) (h : p.get pc = .store rSrc rAddr) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.store rSrc rAddr := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `pushEntryEnd`
    entry. -/
lemma store_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rSrc rAddr : ℕ) (h : p.get pc = .store rSrc rAddr)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h Store2Phase.pushEntryEnd) := by
  have hstart : startPhaseOpt (Instruction.store rSrc rAddr) = some Store2Phase.pushEntryEnd := rfl
  have hentry : entryAt p pc.1 = execVia p pc h Store2Phase.pushEntryEnd :=
    entryAt_eq_execVia p pc h Store2Phase.pushEntryEnd hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `store` site run on the global machine: the `storeProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (`mem`
    prepended with one `encodeEntry`) and a step count bound. -/
lemma store_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rSrc rAddr : ℕ) (h : p.get pc = .store rSrc rAddr)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (storeCode p pc rSrc rAddr h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h Store2Phase.pushEntryEnd))
    (a b : ℕ)
    (hSrcVal : cfg.stk (Kg.reg (regAt p pc rSrc (by rw [h]; simp [regsOf]))) = natToDigits a)
    (hAddrVal : cfg.stk (Kg.reg (regAt p pc rAddr (by rw [h]; simp [regsOf]))) = natToDigits b)
    (hCopyEmpty : cfg.stk (Kg.scratch ScratchKind.copyScratch) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ (2 * (natToDigits b).length + 2) + 1 + (2 * (natToDigits a).length + 2) + 1 + 1 ∧
      Sgf = Function.update cfg.stk Kg.mem (encodeEntry b a ++ cfg.stk Kg.mem) := by
  have hag := storeCode_agrees_ne_done p pc rSrc rAddr h M hAgrees
  obtain ⟨rAddr', hrAddr'⟩ : ∃ x, x = regAt p pc rAddr (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rSrc', hrSrc'⟩ : ∃ x, x = regAt p pc rSrc (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  rw [← hrSrc'] at hSrcVal
  rw [← hrAddr'] at hAddrVal
  have hag' : ∀ l : Store2Phase, l ≠ Store2Phase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getStore AllInstrState.setStore (storeProg rSrc' rAddr' l) := by
    intro l hl
    rw [hrSrc', hrAddr']
    exact hag l hl
  have hStoreRun : (flipBindStore rSrc' rAddr')^[(2 * (natToDigits b).length + 2) + 1
      + (2 * (natToDigits a).length + 2) + 1]
      (some (⟨some Store2Phase.pushEntryEnd, none, cfg.stk⟩ :
        Turing.TM2.Cfg (Γg p) Store2Phase (Option Digit)))
    = some ⟨some Store2Phase.done, none,
        Function.update cfg.stk Kg.mem (encodeEntry b a ++ cfg.stk Kg.mem)⟩ :=
    realize_store (p := p) (rSrc := rSrc') (rAddr := rAddr') b a cfg.stk
      (show cfg.stk (Kg.reg rSrc') = natToDigits a from hSrcVal)
      (show cfg.stk (Kg.reg rAddr') = natToDigits b from hAddrVal) hCopyEmpty
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getStore AllInstrState.setStore (storeProg rSrc' rAddr') M
      Function.injective_id AllInstrState.getStore_setStore AllInstrState.setStore_setStore
      AllInstrState.setStore_getStore _ Store2Phase.pushEntryEnd none cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      Store2Phase.done none
      (Function.update cfg.stk Kg.mem (encodeEntry b a ++ cfg.stk Kg.mem))
      rfl hag' hStoreRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h Store2Phase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h Store2Phase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h Store2Phase.done)) sf Sgf) from rfl,
      storeCode_agrees_done p pc rSrc rAddr h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h Store2Phase.pushEntryEnd), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨(2 * (natToDigits b).length + 2) + 1 + (2 * (natToDigits a).length + 2) + 1 + 1,
    Sgf, ?_, by omega, ?_⟩
  · rw [hcfgEq, Function.iterate_succ_apply',
      show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
    exact hbridgeStep
  · funext k; exact stack_eq_of_map_equiv_refl Sgf _ hstkf k

/-- The final stacks of a `store` run: registers untouched. -/
lemma store_impl_growing_bounded_stk_reg {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (Sgf : ∀ k, List (Γg p k)) (a b : ℕ)
    (hSgf : Sgf = Function.update stk Kg.mem (encodeEntry a b ++ stk Kg.mem))
    (i : Fin (regBound p)) : Sgf (Kg.reg i) = stk (Kg.reg i) := by
  subst hSgf
  rw [Function.update_of_ne (show (Kg.reg i : Kg p) ≠ Kg.mem from fun h => by
    injection h)]

/-- The final stacks of a `store` run: scratch stacks untouched. -/
lemma store_impl_growing_bounded_stk_scratch {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (Sgf : ∀ k, List (Γg p k)) (a b : ℕ)
    (hSgf : Sgf = Function.update stk Kg.mem (encodeEntry a b ++ stk Kg.mem))
    (s : ScratchKind) : Sgf (Kg.scratch s) = stk (Kg.scratch s) := by
  subst hSgf
  rw [Function.update_of_ne (show (Kg.scratch s : Kg p) ≠ Kg.mem from fun h => by
    injection h)]

/-- The final stacks of a `store` run: `io` untouched. -/
lemma store_impl_growing_bounded_stk_io {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (Sgf : ∀ k, List (Γg p k)) (a b : ℕ)
    (hSgf : Sgf = Function.update stk Kg.mem (encodeEntry a b ++ stk Kg.mem)) :
    Sgf Kg.io = stk Kg.io := by
  subst hSgf
  rw [Function.update_of_ne (show (Kg.io : Kg p) ≠ Kg.mem from fun h => by
    injection h)]

/-- The configuration reached after a `store` run represents the stepped RAM: registers
    unchanged, the write-log extended with the stored pair, scratch untouched. -/
lemma store_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rSrc rAddr : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.store rSrc rAddr) (Sgf : ∀ k, List (Γg p k))
    (hMem : Sgf Kg.mem = encodeEntry (r.regs rAddr) (r.regs rSrc) ++ cfg.stk Kg.mem)
    (hReg : ∀ i : Fin (regBound p), Sgf (Kg.reg i) = cfg.stk (Kg.reg i))
    (hScr : ∀ s : ScratchKind, Sgf (Kg.scratch s) = cfg.stk (Kg.scratch s)) :
    Represents p ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ (step r) := by
  obtain ⟨hprog, hregs, ⟨log, hmemstk, hmemlookup⟩, hvar, hscratch, -⟩ := hRep
  have hpcSucc : (step r).pc = pc.1 + 1 := by rw [step, hcurEq]; simpa using hpcEq
  have hvarEq : (Turing.TM2.Cfg.mk (some (entryAt p (pc.1 + 1))) AllInstrState.canonical
      Sgf).var = AllInstrState.canonical := rfl
  refine ⟨by rw [step, hcurEq]; exact hprog, ?_, ⟨(r.regs rAddr, r.regs rSrc) :: log, ?_, ?_⟩,
    hvarEq, ?_, ?_⟩
  · intro i
    show Sgf (Kg.reg i) = _
    rw [hReg, hregs, store_impl_growing_bounded_step_regs rSrc rAddr r hcurEq]
  · show Sgf Kg.mem = _
    rw [hMem, encodeLog, List.map_cons, List.flatten_cons, hmemstk]
    rfl
  · intro a
    show lookupD ((r.regs rAddr, r.regs rSrc) :: log) a 0 = (step r).mem a
    simp only [step, hcurEq]
    by_cases ha : a = r.regs rAddr
    · rw [lookupD_cons_eq _ _ _ _ ha]
      simp only [bankWrite, ite_eq_left ha]
    · rw [lookupD_cons_ne _ _ _ _ ha]
      simp only [bankWrite, ite_eq_right ha, hmemlookup a]
  · intro s
    show Sgf (Kg.scratch s) = []
    rw [hScr]; exact hscratch s
  · simp only [ControlRep, hpcSucc]

/-- Step-count bound: the run's cost is at most the squared potential, since each operand's
    digit length is bounded by its `bitLen` (charged by `instructionCost`). -/
lemma store_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rSrc rAddr : ℕ) (hcurEq : r.current = Instruction.store rSrc rAddr)
    (n : ℕ)
    (hn : n ≤ (2 * (natToDigits (r.regs rAddr)).length + 2) + 1
        + (2 * (natToDigits (r.regs rSrc)).length + 2) + 1 + 1) :
    n ≤ 1 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle_addr := natToDigits_length_le_bitLen (r.regs rAddr)
  have hle_src := natToDigits_length_le_bitLen (r.regs rSrc)
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rAddr) + bitLen (r.regs rSrc) + 1 := by rw [hcurEq]; rfl
  have hA : 1 ≤ bitLen (r.regs rAddr) := Nat.le_add_left 1 _
  have hB : 1 ≤ bitLen (r.regs rSrc) := Nat.le_add_left 1 _
  rw [hcost]
  nlinarith [sq_nonneg (regSize p r + bitLen (r.regs rAddr) + bitLen (r.regs rSrc)),
    Nat.zero_le (regSize p r), Nat.zero_le (cfg.stk Kg.mem).length]

/-- Potential growth: registers are untouched, and the memory stack grows by exactly one
    `encodeEntry`, whose length is bounded by `instructionCost`. -/
lemma store_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rSrc rAddr : ℕ)
    (hcurEq : r.current = Instruction.store rSrc rAddr) (Sgf : ∀ k, List (Γg p k))
    (hMem : Sgf Kg.mem = encodeEntry (r.regs rAddr) (r.regs rSrc) ++ cfg.stk Kg.mem) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hRegsUnchanged : (step r).regs = r.regs := by rw [step, hcurEq]
  have hrs : regSize p (step r) = regSize p r := by unfold regSize; rw [hRegsUnchanged]
  have hlen : (encodeEntry (r.regs rAddr) (r.regs rSrc)).length
      = (natToDigits (r.regs rAddr)).length + 1 + ((natToDigits (r.regs rSrc)).length + 1) := by
    simp [encodeEntry]; ring
  have hle_addr := natToDigits_length_le_bitLen (r.regs rAddr)
  have hle_src := natToDigits_length_le_bitLen (r.regs rSrc)
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rAddr) + bitLen (r.regs rSrc) + 1 := by rw [hcurEq]; rfl
  rw [hMem, List.length_append, hrs, hlen, hcost]
  omega

/-- `storeCode`'s growth companion: `regs` is untouched, and the memory-log grows by exactly one
    `encodeEntry`, whose length is bounded by `instructionCost` via `natToDigits_length_le_bitLen`
    (the same two digit-length terms `store`'s own cost already charges). -/
lemma store_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr) :
    GrowingBoundedSiteStepSim p pc (storeCode p pc rSrc rAddr h) 1 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  obtain ⟨log, hmemstk, hmemlookup⟩ := hRep.2.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := store_impl_growing_bounded_current p pc rSrc rAddr h r hprog hpcEq
  have hcl := store_impl_growing_bounded_label p pc rSrc rAddr h cfg r hpcEq hRep.2.2.2.2.2
  have hSrcVal : cfg.stk (Kg.reg (regAt p pc rSrc (by rw [h]; simp [regsOf])))
      = natToDigits (r.regs rSrc) := hregs _
  have hAddrVal : cfg.stk (Kg.reg (regAt p pc rAddr (by rw [h]; simp [regsOf])))
      = natToDigits (r.regs rAddr) := hregs _
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := store_impl_growing_bounded_run p pc rSrc rAddr h M hAgrees
    cfg hvar hcl _ _ hSrcVal hAddrVal (hscratch .copyScratch)
  have hSgfMem : Sgf Kg.mem = encodeEntry (r.regs rAddr) (r.regs rSrc) ++ cfg.stk Kg.mem := by
    rw [hSgf, Function.update_self]
  refine ⟨n, _, hrun, ?_, ?_,
    store_impl_growing_bounded_time p cfg r rSrc rAddr hcurEq n hn,
    store_impl_growing_bounded_growth p cfg r rSrc rAddr hcurEq Sgf hSgfMem⟩
  · exact store_impl_growing_bounded_represents p pc rSrc rAddr cfg r hRep hpcEq hcurEq Sgf
      hSgfMem (fun i => store_impl_growing_bounded_stk_reg cfg.stk Sgf _ _ hSgf i)
      (fun s => store_impl_growing_bounded_stk_scratch cfg.stk Sgf _ _ hSgf s)
  · exact store_impl_growing_bounded_stk_io cfg.stk Sgf _ _ hSgf

/-- `store`'s `GrowingTimedInstrImpl` package. -/
def storeGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rSrc rAddr : ℕ)
    (h : p.get pc = .store rSrc rAddr) : GrowingTimedInstrImpl p pc where
  code := storeCode p pc rSrc rAddr h
  C := 1
  G := 1
  growingSim := store_impl_growingBoundedSiteStepSim p pc rSrc rAddr h

end NPComplete.RAMToTM.Generic

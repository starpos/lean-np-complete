module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Tactic.DeriveFintype
public import NPComplete.RAMToTM.Generic.Machine.Binary
public import NPComplete.RAMToTM.Generic.Machine.MemoryEncoding

/-!
# Finite-stack implementation of `store 3 1`

The instruction `store 3 1` writes the value in register `r3` to the memory address in register
`r1`. Its implementation pushes an encoded entry onto `mem`, copying the value and address
registers non-destructively through the finite stack alphabet.

`Turing.TM2.Stmt` fixes a stack index in every `push` and `pop`, so the machine uses explicit
phases for these register-specific copies. Since `r1` follows `r0` in the five-register layout,
the address-copy lemmas carry the unchanged `r0` stack as part of their state.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- Ambient stacks: the 5 `BitCostRAM` registers `a b x y t` (indices `0..4`), the memory
    write-log, and one scratch stack reused for every register-preserving read. -/
inductive Store2K
  | r0 | r1 | r2 | r3 | r4
  | mem
  | copyScratch
  deriving DecidableEq

/-- Registers hold `Digit` (number representation); `mem` holds `MemSym` (write-log
    serialization). -/
abbrev Store2Γ : Store2K → Type
  | Store2K.r0 => Digit | Store2K.r1 => Digit | Store2K.r2 => Digit
  | Store2K.r3 => Digit | Store2K.r4 => Digit
  | Store2K.mem => MemSym
  | Store2K.copyScratch => Digit

/-- Phases realizing `store 3 1`: push the entry terminator, non-destructively copy the value
    register (`r3`, i.e. `y`)'s digits onto `mem`, push the address terminator, non-destructively
    copy the address register (`r1`, i.e. `b`)'s digits onto `mem`. -/
inductive Store2Phase
  | pushEntryEnd
  | copyValue | copyValueRestore
  | pushAddrEnd
  | copyAddr | copyAddrRestore
  | done
  deriving DecidableEq

instance : Fintype Store2Phase :=
  Fintype.ofList
    [Store2Phase.pushEntryEnd, Store2Phase.copyValue, Store2Phase.copyValueRestore,
      Store2Phase.pushAddrEnd, Store2Phase.copyAddr, Store2Phase.copyAddrRestore,
      Store2Phase.done]
    (by
      intro x
      cases x <;> simp)

open Turing Turing.TM2.Stmt

def store2Prog : Store2Phase → Turing.TM2.Stmt Store2Γ Store2Phase (Option Digit)
  | Store2Phase.pushEntryEnd =>
      push Store2K.mem (fun _ => MemSym.entryEnd) (goto (fun _ => Store2Phase.copyValue))
  | Store2Phase.copyValue =>
      pop Store2K.r3 (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Store2K.mem (fun s => MemSym.digit (s.getD default))
            (push Store2K.copyScratch (fun s => s.getD default)
              (goto (fun _ => Store2Phase.copyValue))))
          (goto (fun _ => Store2Phase.copyValueRestore)))
  | Store2Phase.copyValueRestore =>
      pop Store2K.copyScratch (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Store2K.r3 (fun s => s.getD default)
            (goto (fun _ => Store2Phase.copyValueRestore)))
          (goto (fun _ => Store2Phase.pushAddrEnd)))
  | Store2Phase.pushAddrEnd =>
      push Store2K.mem (fun _ => MemSym.addrEnd) (goto (fun _ => Store2Phase.copyAddr))
  | Store2Phase.copyAddr =>
      pop Store2K.r1 (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Store2K.mem (fun s => MemSym.digit (s.getD default))
            (push Store2K.copyScratch (fun s => s.getD default)
              (goto (fun _ => Store2Phase.copyAddr))))
          (goto (fun _ => Store2Phase.copyAddrRestore)))
  | Store2Phase.copyAddrRestore =>
      pop Store2K.copyScratch (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push Store2K.r1 (fun s => s.getD default)
            (goto (fun _ => Store2Phase.copyAddrRestore)))
          (goto (fun _ => Store2Phase.done)))
  | Store2Phase.done => halt

def store2CfgAt (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym) (copyScratch : List Digit)
    (lbl : Option Store2Phase) (s : Option Digit) :
    Turing.TM2.Cfg Store2Γ Store2Phase (Option Digit) :=
  ⟨lbl, s, fun k => match k with
    | Store2K.r0 => r0 | Store2K.r1 => r1 | Store2K.r2 => r2 | Store2K.r3 => r3
    | Store2K.r4 => r4 | Store2K.mem => mem | Store2K.copyScratch => copyScratch⟩

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def store2FlipBind :
    Option (Turing.TM2.Cfg Store2Γ Store2Phase (Option Digit)) →
      Option (Turing.TM2.Cfg Store2Γ Store2Phase (Option Digit)) :=
  fun x => x.bind (Turing.TM2.step store2Prog)

lemma store2FlipBind_pushEntryEnd (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 r1 r2 r3 r4 mem [] (some Store2Phase.pushEntryEnd) v0))
      = some (store2CfgAt r0 r1 r2 r3 r4 (MemSym.entryEnd :: mem) []
          (some Store2Phase.copyValue) v0) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 r3 r4 mem [] (some Store2Phase.pushEntryEnd) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_pushAddrEnd (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 r1 r2 r3 r4 mem [] (some Store2Phase.pushAddrEnd) v0))
      = some (store2CfgAt r0 r1 r2 r3 r4 (MemSym.addrEnd :: mem) []
          (some Store2Phase.copyAddr) v0) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 r3 r4 mem [] (some Store2Phase.pushAddrEnd) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_copyValue_cons (d : Digit) (r0 r1 r2 : List Digit) (src' : List Digit)
    (r4 : List Digit) (mem : List MemSym) (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind
        (some (store2CfgAt r0 r1 r2 (d :: src') r4 mem copyScratch
          (some Store2Phase.copyValue) v0))
      = some (store2CfgAt r0 r1 r2 src' r4 (MemSym.digit d :: mem) (d :: copyScratch)
          (some Store2Phase.copyValue) (some d)) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 (d :: src') r4 mem copyScratch (some Store2Phase.copyValue) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_copyValue_nil_exit (r0 r1 r2 r4 : List Digit) (mem : List MemSym)
    (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 r1 r2 [] r4 mem copyScratch
        (some Store2Phase.copyValue) v0))
      = some (store2CfgAt r0 r1 r2 [] r4 mem copyScratch
          (some Store2Phase.copyValueRestore) none) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 [] r4 mem copyScratch (some Store2Phase.copyValue) v0) = _
  simp [store2Prog, store2CfgAt]

/-- The `copyValue` loop: running for `src.length + 1` steps drains register `r3`, prepending
    its reverse (digit-wrapped) onto `mem` and its (unwrapped) reverse onto `copyScratch`. -/
lemma store2_copyValue_loop (r0 r1 r2 : List Digit) (src : List Digit) (r4 : List Digit)
    (mem : List MemSym) (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind^[src.length + 1]
        (some (store2CfgAt r0 r1 r2 src r4 mem copyScratch (some Store2Phase.copyValue) v0))
      = some (store2CfgAt r0 r1 r2 [] r4 ((src.reverse.map MemSym.digit) ++ mem)
          (src.reverse ++ copyScratch) (some Store2Phase.copyValueRestore) none) := by
  induction src generalizing mem copyScratch v0 with
  | nil => simpa using store2FlipBind_copyValue_nil_exit r0 r1 r2 r4 mem copyScratch v0
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        store2FlipBind_copyValue_cons d r0 r1 r2 src' r4 mem copyScratch v0,
        ih (MemSym.digit d :: mem) (d :: copyScratch) (some d)]
      simp [List.reverse_cons, List.append_assoc]

lemma store2FlipBind_copyValueRestore_cons (d : Digit) (r0 r1 r2 : List Digit)
    (src : List Digit) (r4 : List Digit) (mem : List MemSym) (copyScratch' : List Digit)
    (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 r1 r2 src r4 mem (d :: copyScratch')
        (some Store2Phase.copyValueRestore) v0))
      = some (store2CfgAt r0 r1 r2 (d :: src) r4 mem copyScratch'
          (some Store2Phase.copyValueRestore) (some d)) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 src r4 mem (d :: copyScratch')
        (some Store2Phase.copyValueRestore) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_copyValueRestore_nil_exit (r0 r1 r2 : List Digit) (src r4 : List Digit)
    (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 r1 r2 src r4 mem []
        (some Store2Phase.copyValueRestore) v0))
      = some (store2CfgAt r0 r1 r2 src r4 mem [] (some Store2Phase.pushAddrEnd) none) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 r1 r2 src r4 mem [] (some Store2Phase.copyValueRestore) v0) = _
  simp [store2Prog, store2CfgAt]

/-- The `copyValueRestore` loop: running for `copyScratch.length + 1` steps drains
    `copyScratch`, restoring register `r3` to `copyScratch.reverse ++ src` and leaving
    `copyScratch` empty. -/
lemma store2_copyValueRestore_loop (r0 r1 r2 : List Digit) (copyScratch src : List Digit)
    (r4 : List Digit) (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind^[copyScratch.length + 1]
        (some (store2CfgAt r0 r1 r2 src r4 mem copyScratch
          (some Store2Phase.copyValueRestore) v0))
      = some (store2CfgAt r0 r1 r2 (copyScratch.reverse ++ src) r4 mem []
          (some Store2Phase.pushAddrEnd) none) := by
  induction copyScratch generalizing src v0 with
  | nil => simpa using store2FlipBind_copyValueRestore_nil_exit r0 r1 r2 src r4 mem v0
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        store2FlipBind_copyValueRestore_cons d r0 r1 r2 src r4 mem cs' v0, ih (d :: src) (some d)]
      simp [List.reverse_cons, List.append_assoc]

/-- Running the value-register copy to completion: register `r3` (`y`) is restored exactly,
    and its reverse (digit-wrapped) is prepended onto `mem`. -/
lemma store2_copyValue_phase (r0 r1 r2 : List Digit) (src : List Digit) (r4 : List Digit)
    (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind^[2 * src.length + 2]
        (some (store2CfgAt r0 r1 r2 src r4 mem [] (some Store2Phase.copyValue) v0))
      = some (store2CfgAt r0 r1 r2 src r4 ((src.reverse.map MemSym.digit) ++ mem) []
          (some Store2Phase.pushAddrEnd) none) := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, store2_copyValue_loop r0 r1 r2 src r4 mem [] v0,
    List.append_nil]
  have h2 := store2_copyValueRestore_loop r0 r1 r2 src.reverse [] r4
    ((src.reverse.map MemSym.digit) ++ mem) none
  rwa [List.reverse_reverse, List.append_nil] at h2

lemma store2FlipBind_copyAddr_cons (d : Digit) (r0 : List Digit) (src' : List Digit)
    (r2 r3 r4 : List Digit) (mem : List MemSym) (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind
        (some (store2CfgAt r0 (d :: src') r2 r3 r4 mem copyScratch
          (some Store2Phase.copyAddr) v0))
      = some (store2CfgAt r0 src' r2 r3 r4 (MemSym.digit d :: mem) (d :: copyScratch)
          (some Store2Phase.copyAddr) (some d)) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 (d :: src') r2 r3 r4 mem copyScratch (some Store2Phase.copyAddr) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_copyAddr_nil_exit (r0 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 [] r2 r3 r4 mem copyScratch
        (some Store2Phase.copyAddr) v0))
      = some (store2CfgAt r0 [] r2 r3 r4 mem copyScratch
          (some Store2Phase.copyAddrRestore) none) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 [] r2 r3 r4 mem copyScratch (some Store2Phase.copyAddr) v0) = _
  simp [store2Prog, store2CfgAt]

/-- The `copyAddr` analogue of `store2_copyValue_loop`, for register `r1` (`b`). -/
lemma store2_copyAddr_loop (r0 : List Digit) (src : List Digit) (r2 r3 r4 : List Digit)
    (mem : List MemSym) (copyScratch : List Digit) (v0 : Option Digit) :
    store2FlipBind^[src.length + 1]
        (some (store2CfgAt r0 src r2 r3 r4 mem copyScratch (some Store2Phase.copyAddr) v0))
      = some (store2CfgAt r0 [] r2 r3 r4 ((src.reverse.map MemSym.digit) ++ mem)
          (src.reverse ++ copyScratch) (some Store2Phase.copyAddrRestore) none) := by
  induction src generalizing mem copyScratch v0 with
  | nil => simpa using store2FlipBind_copyAddr_nil_exit r0 r2 r3 r4 mem copyScratch v0
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        store2FlipBind_copyAddr_cons d r0 src' r2 r3 r4 mem copyScratch v0,
        ih (MemSym.digit d :: mem) (d :: copyScratch) (some d)]
      simp [List.reverse_cons, List.append_assoc]

lemma store2FlipBind_copyAddrRestore_cons (d : Digit) (r0 : List Digit) (src : List Digit)
    (r2 r3 r4 : List Digit) (mem : List MemSym) (copyScratch' : List Digit) (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 src r2 r3 r4 mem (d :: copyScratch')
        (some Store2Phase.copyAddrRestore) v0))
      = some (store2CfgAt r0 (d :: src) r2 r3 r4 mem copyScratch'
          (some Store2Phase.copyAddrRestore) (some d)) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 src r2 r3 r4 mem (d :: copyScratch')
        (some Store2Phase.copyAddrRestore) v0) = _
  simp [store2Prog, store2CfgAt]
  funext k
  cases k <;> simp

lemma store2FlipBind_copyAddrRestore_nil_exit (r0 : List Digit) (src : List Digit)
    (r2 r3 r4 : List Digit) (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind (some (store2CfgAt r0 src r2 r3 r4 mem []
        (some Store2Phase.copyAddrRestore) v0))
      = some (store2CfgAt r0 src r2 r3 r4 mem [] (some Store2Phase.done) none) := by
  show (Turing.TM2.step store2Prog)
      (store2CfgAt r0 src r2 r3 r4 mem [] (some Store2Phase.copyAddrRestore) v0) = _
  simp [store2Prog, store2CfgAt]

/-- The `copyAddrRestore` analogue of `store2_copyValueRestore_loop`. -/
lemma store2_copyAddrRestore_loop (r0 : List Digit) (copyScratch src : List Digit)
    (r2 r3 r4 : List Digit) (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind^[copyScratch.length + 1]
        (some (store2CfgAt r0 src r2 r3 r4 mem copyScratch
          (some Store2Phase.copyAddrRestore) v0))
      = some (store2CfgAt r0 (copyScratch.reverse ++ src) r2 r3 r4 mem []
          (some Store2Phase.done) none) := by
  induction copyScratch generalizing src v0 with
  | nil => simpa using store2FlipBind_copyAddrRestore_nil_exit r0 src r2 r3 r4 mem v0
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        store2FlipBind_copyAddrRestore_cons d r0 src r2 r3 r4 mem cs' v0, ih (d :: src) (some d)]
      simp [List.reverse_cons, List.append_assoc]

/-- Running the address-register copy to completion: register `r1` (`b`) is restored exactly,
    and its reverse (digit-wrapped) is prepended onto `mem`. -/
lemma store2_copyAddr_phase (r0 : List Digit) (src : List Digit) (r2 r3 r4 : List Digit)
    (mem : List MemSym) (v0 : Option Digit) :
    store2FlipBind^[2 * src.length + 2]
        (some (store2CfgAt r0 src r2 r3 r4 mem [] (some Store2Phase.copyAddr) v0))
      = some (store2CfgAt r0 src r2 r3 r4 ((src.reverse.map MemSym.digit) ++ mem) []
          (some Store2Phase.done) none) := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, store2_copyAddr_loop r0 src r2 r3 r4 mem [] v0,
    List.append_nil]
  have h2 := store2_copyAddrRestore_loop r0 src.reverse [] r2 r3 r4
    ((src.reverse.map MemSym.digit) ++ mem) none
  rwa [List.reverse_reverse, List.append_nil] at h2

/-- Running `store2Prog` from `pushEntryEnd` for the stated number of transitions, with registers
    `r1` and `r3` holding `natToDigits addr` and `natToDigits val`, leaves every register untouched
    and prepends `MemoryEncoding.encodeEntry addr val` to `mem`. This is the effect of `store 3 1`
    at `regs 1 = addr` and `regs 3 = val`. -/
lemma realize_store2 (addr val : ℕ) (r0 r2 r4 : List Digit) (mem0 : List MemSym) :
    store2FlipBind^[(2 * (natToDigits addr).length + 2) + 1 + (2 * (natToDigits val).length + 2)
        + 1]
        (some (store2CfgAt r0 (natToDigits addr) r2 (natToDigits val) r4 mem0 []
          (some Store2Phase.pushEntryEnd) none))
      = some (store2CfgAt r0 (natToDigits addr) r2 (natToDigits val) r4
          (encodeEntry addr val ++ mem0) [] (some Store2Phase.done) none) := by
  rw [Function.iterate_add_apply, Function.iterate_one, store2FlipBind_pushEntryEnd,
    Function.iterate_add_apply, store2_copyValue_phase, Function.iterate_add_apply,
    Function.iterate_one, store2FlipBind_pushAddrEnd, store2_copyAddr_phase]
  simp [encodeEntry, List.append_assoc]

end NPComplete.RAMToTM

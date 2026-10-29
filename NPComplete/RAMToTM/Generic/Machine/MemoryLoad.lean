module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import NPComplete.RAMToTM.Generic.Machine.Binary
public import NPComplete.RAMToTM.Generic.Machine.MemoryEncoding
public import NPComplete.RAMToTM.Generic.Machine.FiniteStore

/-!
# Finite-stack implementation of RAM load

The instruction `load 4 0` reads memory at the address in register `r0` into register `r4`. A
read leaves memory unchanged, so the scan restores every entry it visits, whether or not its
address matches. The newest-first write-log makes the first matching entry the value returned.

After a match, the unscanned suffix remains in `mem`; restoring the popped prefix is therefore
sufficient to recover the complete log. Address comparison checks both digit streams through
their terminators, so addresses with different digit lengths are rejected without extra state.
The fixed `LoadState` record and finite scratch stacks keep the machine state within the finite
alphabet required by `FinTM2`.

`scanResult` specifies the pure newest-first lookup and agrees with `lookupD`. The theorem
`realize_load` connects that specification to the stack program for an arbitrary write-log, while
`realize_load_two` supplies an explicit transition bound for a two-entry log.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- Pure scan spec for `load`: the digit list `regs 4` should end up holding after `load 4 0`
    (`t := mem(a)`), by first-match-wins over the newest-first write-log. -/
def scanResult (q : ℕ) : WriteLog → List Digit
  | [] => []
  | (a, v) :: xs => if a = q then natToDigits v else scanResult q xs

/-- `scanResult` agrees with `FiniteStore.lookupD` (defaulting to `0`, i.e. `natToDigits 0 = []`
    when the address was never written). -/
lemma scanResult_eq_lookupD (q : ℕ) (log : WriteLog) :
    scanResult q log = natToDigits (lookupD log q 0) := by
  induction log with
  | nil => simp [scanResult, lookupD, natToDigits, Nat.digits_zero]
  | cons e xs ih =>
      simp only [scanResult, lookupD, List.find?]
      by_cases h : e.1 = q
      · simp [h]
      · simp [h, ih, lookupD]

/-- Ambient stacks: the 5 registers, `mem`, `copyScratch` (for the initial non-destructive read
    of register `a` into `query`), the search key `query` (a copy of `a`'s digits, MSB-first —
    matching `mem`'s address-field layout, so both can be compared head-to-head), `queryTmp`
    (restores `query` after each entry's comparison), and `logTmp` (restores `mem` once the
    whole scan is done). -/
inductive LK
  | r0 | r1 | r2 | r3 | r4
  | mem
  | copyScratch
  | query | queryTmp | logTmp
  deriving DecidableEq

abbrev LΓ : LK → Type
  | LK.r0 => Digit | LK.r1 => Digit | LK.r2 => Digit | LK.r3 => Digit | LK.r4 => Digit
  | LK.mem => MemSym
  | LK.copyScratch => Digit
  | LK.query => Digit | LK.queryTmp => Digit
  | LK.logTmp => MemSym

/-- Extract the digit if a `MemSym` is a `digit` symbol (used to distinguish it from the two
    markers during a scan). -/
def MemSym.digit? : MemSym → Option Digit
  | MemSym.digit d => some d
  | _ => none

/-- The scan's transient scratch: the last popped `mem` symbol, the last popped/peeked `query`
    digit, and whether the current entry's address still matches so far. `memSym` and `queryDigit`
    are refreshed during each scan step, while `equal` is initialized at each entry boundary, so
    `LoadState` stays a small fixed record (no unbounded data, per `FinTM2`'s `Fintype σ`
    requirement). -/
structure LoadState where
  memSym : Option MemSym
  queryDigit : Option Digit
  equal : Bool
  deriving DecidableEq, Fintype

/-- `copyQuery`/`copyQueryRestore`: non-destructively copy register `a` (`r0`) into `query`
    (a pop-push-push copy loop). `compareAddr`: per-entry address comparison (see module
    docstring). `restoreQuery`: after a mismatch, restore `query` from `queryTmp` for the next
    entry. `skipValue`: after a mismatch, consume the entry's value field into `logTmp` only.
    `readValue`: once matched, consume the value field into both `r4` (MSB-first pops deliver
    LSB-first via `push`'s own prepending) and `logTmp`. `restoreMem`: drain `logTmp` back onto
    `mem`, restoring everything scanned so far (reached either after a match or after
    exhausting the log with none). `drainQuery`/`drainQueryTmp`: whichever of `query`/`queryTmp`
    still holds the (reversed) address digits at this point — a match leaves them on
    `queryTmp` (`query` was fully drained mid-scan), exhausting the log with no match leaves
    them on `query` (never restored, since there is no further entry to compare against) — gets
    discarded here, so both end up empty as every other stack does before the next instruction
    starts. -/
inductive Phase2
  | copyQuery | copyQueryRestore
  | compareAddr
  | restoreQuery
  | skipValue
  | readValue
  | restoreMem
  | drainQuery
  | drainQueryTmp
  | done
  deriving DecidableEq

instance : Fintype Phase2 :=
  Fintype.ofList
    [Phase2.copyQuery, Phase2.copyQueryRestore, Phase2.compareAddr, Phase2.restoreQuery,
      Phase2.skipValue, Phase2.readValue, Phase2.restoreMem, Phase2.drainQuery,
      Phase2.drainQueryTmp, Phase2.done]
    (by
      intro x
      cases x <;> simp)

open Turing Turing.TM2.Stmt

def prog2 : Phase2 → Turing.TM2.Stmt LΓ Phase2 LoadState
  | Phase2.copyQuery =>
      pop LK.r0 (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push LK.query (fun s => s.queryDigit.getD default)
            (push LK.copyScratch (fun s => s.queryDigit.getD default)
              (goto (fun _ => Phase2.copyQuery))))
          (goto (fun _ => Phase2.copyQueryRestore)))
  | Phase2.copyQueryRestore =>
      pop LK.copyScratch (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push LK.r0 (fun s => s.queryDigit.getD default)
            (goto (fun _ => Phase2.copyQueryRestore)))
          (goto (fun _ => Phase2.compareAddr)))
  | Phase2.compareAddr =>
      pop LK.mem (fun s ov => {s with memSym := ov})
        (branch (fun s => s.memSym.isSome)
          (branch (fun s => (s.memSym.bind MemSym.digit?).isSome)
            -- this entry has (at least) one more address digit
            (pop LK.query (fun s ov => {s with queryDigit := ov})
              (push LK.logTmp (fun s => s.memSym.getD MemSym.entryEnd)
                (branch (fun s => s.queryDigit.isSome)
                  (push LK.queryTmp (fun s => s.queryDigit.getD default)
                    (load
                      (fun s => {s with equal :=
                        s.equal && (s.memSym.bind MemSym.digit?) = s.queryDigit})
                      (goto (fun _ => Phase2.compareAddr))))
                  (load (fun s => {s with equal := false})
                    (goto (fun _ => Phase2.compareAddr))))))
            -- this entry's address field just ended
            (peek LK.query (fun s ov => {s with queryDigit := ov})
              (load (fun s => {s with equal := s.equal && s.queryDigit.isNone})
                (push LK.logTmp (fun s => s.memSym.getD MemSym.entryEnd)
                  (branch (fun s => s.equal)
                    (goto (fun _ => Phase2.readValue))
                    (goto (fun _ => Phase2.restoreQuery)))))))
          (goto (fun _ => Phase2.restoreMem)))
  | Phase2.restoreQuery =>
      pop LK.queryTmp (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (push LK.query (fun s => s.queryDigit.getD default)
            (goto (fun _ => Phase2.restoreQuery)))
          (goto (fun _ => Phase2.skipValue)))
  | Phase2.skipValue =>
      pop LK.mem (fun s ov => {s with memSym := ov})
        (push LK.logTmp (fun s => s.memSym.getD MemSym.entryEnd)
          (branch (fun s => decide (s.memSym = some MemSym.entryEnd))
            (load (fun s => {s with equal := true}) (goto (fun _ => Phase2.compareAddr)))
            (goto (fun _ => Phase2.skipValue))))
  | Phase2.readValue =>
      pop LK.mem (fun s ov => {s with memSym := ov})
        (push LK.logTmp (fun s => s.memSym.getD MemSym.entryEnd)
          (branch (fun s => decide (s.memSym = some MemSym.entryEnd))
            (goto (fun _ => Phase2.restoreMem))
            (push LK.r4 (fun s => (s.memSym.bind MemSym.digit?).getD default)
              (goto (fun _ => Phase2.readValue)))))
  | Phase2.restoreMem =>
      pop LK.logTmp (fun s ov => {s with memSym := ov})
        (branch (fun s => s.memSym.isSome)
          (push LK.mem (fun s => s.memSym.getD MemSym.entryEnd)
            (goto (fun _ => Phase2.restoreMem)))
          (goto (fun _ => Phase2.drainQuery)))
  | Phase2.drainQuery =>
      pop LK.query (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (goto (fun _ => Phase2.drainQuery))
          (goto (fun _ => Phase2.drainQueryTmp)))
  | Phase2.drainQueryTmp =>
      pop LK.queryTmp (fun s ov => {s with queryDigit := ov})
        (branch (fun s => s.queryDigit.isSome)
          (goto (fun _ => Phase2.drainQueryTmp))
          (goto (fun _ => Phase2.done)))
  | Phase2.done => halt

def cfgAt2 (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch query queryTmp : List Digit)
    (logTmp : List MemSym) (lbl : Option Phase2) (s : LoadState) :
    Turing.TM2.Cfg LΓ Phase2 LoadState :=
  ⟨lbl, s, fun k => match k with
    | LK.r0 => r0 | LK.r1 => r1 | LK.r2 => r2 | LK.r3 => r3 | LK.r4 => r4
    | LK.mem => mem | LK.copyScratch => copyScratch
    | LK.query => query | LK.queryTmp => queryTmp | LK.logTmp => logTmp⟩

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBind2 :
    Option (Turing.TM2.Cfg LΓ Phase2 LoadState) →
      Option (Turing.TM2.Cfg LΓ Phase2 LoadState) :=
  fun x => x.bind (Turing.TM2.step prog2)

lemma flipBind2_copyQuery_cons (d : Digit) (r1 r2 r3 r4 src' : List Digit) (mem : List MemSym)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 (d :: src') r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
        (some Phase2.copyQuery) s0))
      = some (cfgAt2 src' r1 r2 r3 r4 mem (d :: copyScratch) (d :: query) queryTmp logTmp
          (some Phase2.copyQuery) {s0 with queryDigit := some d}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 (d :: src') r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
        (some Phase2.copyQuery) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_copyQuery_nil_exit (r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 [] r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
        (some Phase2.copyQuery) s0))
      = some (cfgAt2 [] r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
          (some Phase2.copyQueryRestore) {s0 with queryDigit := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 [] r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
        (some Phase2.copyQuery) s0) = _
  simp [prog2, cfgAt2]

lemma flipBind2_copyQueryRestore_cons (d : Digit) (r1 r2 r3 r4 src : List Digit)
    (mem : List MemSym) (cs' query queryTmp : List Digit) (logTmp : List MemSym)
    (s0 : LoadState) :
    flipBind2 (some (cfgAt2 src r1 r2 r3 r4 mem (d :: cs') query queryTmp logTmp
        (some Phase2.copyQueryRestore) s0))
      = some (cfgAt2 (d :: src) r1 r2 r3 r4 mem cs' query queryTmp logTmp
          (some Phase2.copyQueryRestore) {s0 with queryDigit := some d}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 src r1 r2 r3 r4 mem (d :: cs') query queryTmp logTmp
        (some Phase2.copyQueryRestore) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_copyQueryRestore_nil_exit (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem [] query queryTmp logTmp
        (some Phase2.copyQueryRestore) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem [] query queryTmp logTmp
          (some Phase2.compareAddr) {s0 with queryDigit := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem [] query queryTmp logTmp
        (some Phase2.copyQueryRestore) s0) = _
  simp [prog2, cfgAt2]

lemma flipBind2_restoreQuery_cons (d : Digit) (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch q queryTmp' : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q (d :: queryTmp') logTmp
        (some Phase2.restoreQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch (d :: q) queryTmp' logTmp
          (some Phase2.restoreQuery) {s0 with queryDigit := some d}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q (d :: queryTmp') logTmp
        (some Phase2.restoreQuery) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_restoreQuery_nil_exit (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch q : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q [] logTmp
        (some Phase2.restoreQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q [] logTmp
          (some Phase2.skipValue) {s0 with queryDigit := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q [] logTmp
        (some Phase2.restoreQuery) s0) = _
  simp [prog2, cfgAt2]

lemma flipBind2_skipValue_digit (d : Digit) (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.digit d :: rest) copyScratch query queryTmp
        logTmp (some Phase2.skipValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp
          (MemSym.digit d :: logTmp) (some Phase2.skipValue)
          {s0 with memSym := some (MemSym.digit d)}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.digit d :: rest) copyScratch query queryTmp logTmp
        (some Phase2.skipValue) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_skipValue_entryEnd (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.entryEnd :: rest) copyScratch query queryTmp
        logTmp (some Phase2.skipValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp
          (MemSym.entryEnd :: logTmp) (some Phase2.compareAddr)
          {memSym := some MemSym.entryEnd, queryDigit := s0.queryDigit, equal := true}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.entryEnd :: rest) copyScratch query queryTmp logTmp
        (some Phase2.skipValue) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_readValue_digit (d : Digit) (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.digit d :: rest) copyScratch query queryTmp
        logTmp (some Phase2.readValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 (d :: r4) rest copyScratch query queryTmp
          (MemSym.digit d :: logTmp) (some Phase2.readValue)
          {s0 with memSym := some (MemSym.digit d)}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.digit d :: rest) copyScratch query queryTmp logTmp
        (some Phase2.readValue) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?]
  funext k
  cases k <;> simp

lemma flipBind2_readValue_entryEnd (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.entryEnd :: rest) copyScratch query queryTmp
        logTmp (some Phase2.readValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp
          (MemSym.entryEnd :: logTmp) (some Phase2.restoreMem)
          {s0 with memSym := some MemSym.entryEnd}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.entryEnd :: rest) copyScratch query queryTmp logTmp
        (some Phase2.readValue) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?]
  funext k
  cases k <;> simp

/-- Running `readValue` for `vd.length + 1` steps consumes the value field (`vd`, MSB-first,
    as stored) and the `entryEnd` after it: `vd`'s reverse (LSB-first, via the same
    push-reverses-pop-order principle) lands on `r4`, and every
    popped symbol (value digits, then `entryEnd`) is preserved on `logTmp` for the later
    `restoreMem` pass. -/
lemma readValue_loop (vd : List Digit) (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[vd.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 ((vd.map MemSym.digit) ++ (MemSym.entryEnd :: rest))
          copyScratch query queryTmp logTmp (some Phase2.readValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 (vd.reverse ++ r4) rest copyScratch query queryTmp
          (MemSym.entryEnd :: (vd.map MemSym.digit).reverse ++ logTmp)
          (some Phase2.restoreMem) {s0 with memSym := some MemSym.entryEnd}) := by
  induction vd generalizing r4 logTmp s0 with
  | nil =>
      simpa using
        flipBind2_readValue_entryEnd rest r0 r1 r2 r3 r4 copyScratch query queryTmp logTmp s0
  | cons d vd' ih =>
      simp only [List.map_cons, List.cons_append]
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_readValue_digit d (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest)
          r0 r1 r2 r3 r4 copyScratch query queryTmp logTmp s0,
        ih (d :: r4) (MemSym.digit d :: logTmp) {s0 with memSym := some (MemSym.digit d)}]
      simp [List.reverse_cons, List.append_assoc]

lemma flipBind2_restoreMem_cons (m : MemSym) (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (mem : List MemSym) (copyScratch query queryTmp : List Digit) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch query queryTmp (m :: rest)
        (some Phase2.restoreMem) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (m :: mem) copyScratch query queryTmp rest
          (some Phase2.restoreMem) {s0 with memSym := some m}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch query queryTmp (m :: rest)
        (some Phase2.restoreMem) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_restoreMem_nil_exit (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch query queryTmp : List Digit) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch query queryTmp []
        (some Phase2.restoreMem) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch query queryTmp []
          (some Phase2.drainQuery) {s0 with memSym := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch query queryTmp []
        (some Phase2.restoreMem) s0) = _
  simp [prog2, cfgAt2]

lemma flipBind2_drainQuery_cons (d : Digit) (q' : List Digit) (r0 r1 r2 r3 r4 : List Digit)
    (mem : List MemSym) (copyScratch queryTmp : List Digit) (logTmp : List MemSym)
    (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch (d :: q') queryTmp logTmp
        (some Phase2.drainQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q' queryTmp logTmp
          (some Phase2.drainQuery) {s0 with queryDigit := some d}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch (d :: q') queryTmp logTmp
        (some Phase2.drainQuery) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_drainQuery_nil_exit (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] queryTmp logTmp
        (some Phase2.drainQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] queryTmp logTmp
          (some Phase2.drainQueryTmp) {s0 with queryDigit := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] queryTmp logTmp
        (some Phase2.drainQuery) s0) = _
  simp [prog2, cfgAt2]

/-- Draining `query` to empty discards whatever it holds: `Represents` needs every scratch
    stack empty, so its actual content (an artifact of which scan branch was taken, see
    `Phase2`'s docstring) is irrelevant here — only `q.length` (the step count) matters. -/
lemma drainQuery_loop (q : List Digit) (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[q.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q queryTmp logTmp
          (some Phase2.drainQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] queryTmp logTmp
          (some Phase2.drainQueryTmp) {s0 with queryDigit := none}) := by
  induction q generalizing s0 with
  | nil =>
      simpa using
        flipBind2_drainQuery_nil_exit r0 r1 r2 r3 r4 mem copyScratch queryTmp logTmp s0
  | cons d q' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_drainQuery_cons d q' r0 r1 r2 r3 r4 mem copyScratch queryTmp logTmp s0,
        ih {s0 with queryDigit := some d}]

lemma flipBind2_drainQueryTmp_cons (d : Digit) (qt' : List Digit) (r0 r1 r2 r3 r4 : List Digit)
    (mem : List MemSym) (copyScratch : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] (d :: qt') logTmp
        (some Phase2.drainQueryTmp) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] qt' logTmp
          (some Phase2.drainQueryTmp) {s0 with queryDigit := some d}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] (d :: qt') logTmp
        (some Phase2.drainQueryTmp) s0) = _
  simp [prog2, cfgAt2]
  funext k
  cases k <;> simp

lemma flipBind2_drainQueryTmp_nil_exit (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] [] logTmp
        (some Phase2.drainQueryTmp) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] [] logTmp
          (some Phase2.done) {s0 with queryDigit := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] [] logTmp
        (some Phase2.drainQueryTmp) s0) = _
  simp [prog2, cfgAt2]

/-- `drainQuery_loop`'s twin for `queryTmp`. -/
lemma drainQueryTmp_loop (qt : List Digit) (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[qt.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] qt logTmp
          (some Phase2.drainQueryTmp) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch [] [] logTmp
          (some Phase2.done) {s0 with queryDigit := none}) := by
  induction qt generalizing s0 with
  | nil => simpa using flipBind2_drainQueryTmp_nil_exit r0 r1 r2 r3 r4 mem copyScratch logTmp s0
  | cons d qt' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_drainQueryTmp_cons d qt' r0 r1 r2 r3 r4 mem copyScratch logTmp s0,
        ih {s0 with queryDigit := some d}]

/-- Running `restoreQuery` for `qt.length + 1` steps drains `qt` (the digits `compareAddr`
    consumed from `query` during one entry's comparison), pushing them back onto `query` and
    restoring it to `qt.reverse ++ q`. -/
lemma restoreQuery_loop (qt q : List Digit) (r0 r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[qt.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch q qt logTmp
          (some Phase2.restoreQuery) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 mem copyScratch (qt.reverse ++ q) [] logTmp
          (some Phase2.skipValue) {s0 with queryDigit := none}) := by
  induction qt generalizing q s0 with
  | nil => simpa using flipBind2_restoreQuery_nil_exit r0 r1 r2 r3 r4 mem copyScratch q logTmp s0
  | cons d qt' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_restoreQuery_cons d r0 r1 r2 r3 r4 mem copyScratch q qt' logTmp s0,
        ih (d :: q) {s0 with queryDigit := some d}]
      simp [List.reverse_cons, List.append_assoc]

lemma flipBind2_compareAddr_digit_match (a : Digit) (ad' : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (h : s0.equal = true) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (a :: ad') qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch ad' (a :: qt0) (MemSym.digit a :: logTmp0) (some Phase2.compareAddr)
          {memSym := some (MemSym.digit a), queryDigit := some a, equal := true}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (a :: ad') qt0 logTmp0 (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?, h]
  funext k
  cases k <;> simp

lemma flipBind2_compareAddr_addrEnd_match (valTail : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch qt0 : List Digit) (logTmp0 : List MemSym) (s0 : LoadState)
    (h : s0.equal = true) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch [] qt0
        logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 valTail copyScratch [] qt0
          (MemSym.addrEnd :: logTmp0) (some Phase2.readValue)
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := true}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch [] qt0 logTmp0
        (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?, h]
  funext k
  cases k <;> simp

/-- `compareAddr`, on a query that turns out to equal the entry's own (stored) address
    digit-for-digit: running for `ad.length + 1` steps consumes the whole address field
    (`ad`, MSB-first) and the `addrEnd` after it, draining `query` to empty (`ad`'s reverse
    lands on `queryTmp`, since pushing reverses pop order) and
    transitioning straight to `readValue`. The incoming `equal` must already be `true` — this
    is the "still matching so far" invariant a fresh entry starts with and this lemma
    preserves as long as every digit keeps agreeing (`s0`'s `memSym`/`queryDigit` fields are
    irrelevant, overwritten every iteration, hence universally quantified). -/
lemma compareAddr_loop_matched (ad : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (h : s0.equal = true) :
    flipBind2^[ad.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 (ad.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch ad qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 valTail copyScratch [] (ad.reverse ++ qt0)
          (MemSym.addrEnd :: ad.reverse.map MemSym.digit ++ logTmp0)
          (some Phase2.readValue)
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := true}) := by
  induction ad generalizing qt0 logTmp0 s0 with
  | nil =>
      simpa using
        flipBind2_compareAddr_addrEnd_match valTail r0 r1 r2 r3 r4 copyScratch qt0 logTmp0 s0 h
  | cons a ad' ih =>
      simp only [List.map_cons, List.cons_append]
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_compareAddr_digit_match a ad' valTail r0 r1 r2 r3 r4 copyScratch qt0
          logTmp0 s0 h,
        ih (a :: qt0) (MemSym.digit a :: logTmp0)
          {memSym := some (MemSym.digit a), queryDigit := some a, equal := true} rfl]
      simp [List.reverse_cons, List.append_assoc]

lemma flipBind2_compareAddr_digit_qempty (a : Digit) (ad' : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch [] qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch [] qt0 (MemSym.digit a :: logTmp0) (some Phase2.compareAddr)
          {memSym := some (MemSym.digit a), queryDigit := none, equal := false}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch [] qt0 logTmp0 (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?]
  funext k
  cases k <;> simp

lemma flipBind2_compareAddr_digit_neq (a d : Digit) (ad' q' : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (hne : a ≠ d) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (d :: q') qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch q' (d :: qt0) (MemSym.digit a :: logTmp0) (some Phase2.compareAddr)
          {memSym := some (MemSym.digit a), queryDigit := some d, equal := false}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (d :: q') qt0 logTmp0 (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?, hne]
  funext k
  cases k <;> simp

lemma flipBind2_compareAddr_digit_eq (a : Digit) (ad' q' : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (a :: q') qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch q' (a :: qt0) (MemSym.digit a :: logTmp0) (some Phase2.compareAddr)
          {memSym := some (MemSym.digit a), queryDigit := some a, equal := s0.equal}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4
        (MemSym.digit a :: (ad'.map MemSym.digit ++ (MemSym.addrEnd :: valTail)))
        copyScratch (a :: q') qt0 logTmp0 (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?]
  funext k
  cases k <;> simp

lemma flipBind2_compareAddr_addrEnd_qnonempty (d : Digit) (q' : List Digit)
    (valTail : List MemSym) (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit)
    (logTmp0 : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch (d :: q') qt0
        logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 valTail copyScratch (d :: q') qt0
          (MemSym.addrEnd :: logTmp0) (some Phase2.restoreQuery)
          {memSym := some MemSym.addrEnd, queryDigit := some d, equal := false}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch (d :: q') qt0 logTmp0
        (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?]
  funext k
  cases k <;> simp

lemma flipBind2_compareAddr_addrEnd_qempty_false (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (h : s0.equal = false) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch [] qt0
        logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 valTail copyScratch [] qt0
          (MemSym.addrEnd :: logTmp0) (some Phase2.restoreQuery)
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := false}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 (MemSym.addrEnd :: valTail) copyScratch [] qt0 logTmp0
        (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2, MemSym.digit?, h]
  funext k
  cases k <;> simp

/-- `compareAddr`'s mismatch path, combined with the `restoreQuery` drain that necessarily
    follows it: whenever the incoming `equal` is already `false`, or this entry's address
    `ad` differs from `q`, running for `(ad.length + 1) + (min ad.length q.length + qt0.length
    + 1)` steps consumes the address field and `addrEnd`, then fully restores `query` to
    `qt0.reverse ++ q`. The key invariant making this restoration exact is that
    `queryTmp.reverse ++ query` never changes during `compareAddr` itself: each digit moved
    off `query` is moved onto `queryTmp` in the same step, so `restoreQuery_loop` reconstructs
    precisely the pre-`compareAddr` value once it drains whatever ended up in `queryTmp` —
    regardless of *how much* got consumed (which depends on `min ad.length q.length`, i.e.
    whichever of the two digit sequences runs out first). -/
lemma compareAddr_mismatch_then_restore (ad q : List Digit) (valTail : List MemSym)
    (r0 r1 r2 r3 r4 : List Digit) (copyScratch qt0 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (hmis : ¬ (s0.equal = true ∧ ad = q)) :
    flipBind2^[(ad.length + 1) + (min ad.length q.length + qt0.length + 1)]
        (some (cfgAt2 r0 r1 r2 r3 r4 (ad.map MemSym.digit ++ (MemSym.addrEnd :: valTail))
          copyScratch q qt0 logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 valTail copyScratch (qt0.reverse ++ q) []
          (MemSym.addrEnd :: ad.reverse.map MemSym.digit ++ logTmp0)
          (some Phase2.skipValue)
          {memSym := some MemSym.addrEnd, queryDigit := none, equal := false}) := by
  induction ad generalizing q qt0 logTmp0 s0 with
  | nil =>
      rcases q with _ | ⟨d, q'⟩
      · have heq : s0.equal = false := by
          rcases hs : s0.equal with _ | _
          · rfl
          · exact absurd ⟨hs, rfl⟩ hmis
        have hcount : ([] : List Digit).length + 1
            + (min ([] : List Digit).length ([] : List Digit).length + qt0.length + 1)
            = (qt0.length + 1) + 1 := by simp; omega
        rw [hcount, Function.iterate_add_apply, Function.iterate_one]
        simp only [List.map_nil, List.nil_append, List.reverse_nil]
        rw [flipBind2_compareAddr_addrEnd_qempty_false valTail r0 r1 r2 r3 r4 copyScratch qt0
          logTmp0 s0 heq]
        simpa using restoreQuery_loop qt0 [] r0 r1 r2 r3 r4 valTail copyScratch
          (MemSym.addrEnd :: logTmp0)
          ({memSym := some MemSym.addrEnd, queryDigit := none, equal := false} : LoadState)
      · have hcount : ([] : List Digit).length + 1
            + (min ([] : List Digit).length (d :: q').length + qt0.length + 1)
            = (qt0.length + 1) + 1 := by simp; omega
        rw [hcount, Function.iterate_add_apply, Function.iterate_one]
        simp only [List.map_nil, List.nil_append, List.reverse_nil]
        rw [flipBind2_compareAddr_addrEnd_qnonempty d q' valTail r0 r1 r2 r3 r4 copyScratch qt0
          logTmp0 s0]
        simpa using restoreQuery_loop qt0 (d :: q') r0 r1 r2 r3 r4 valTail copyScratch
          (MemSym.addrEnd :: logTmp0)
          ({memSym := some MemSym.addrEnd, queryDigit := some d, equal := false} : LoadState)
  | cons a ad' ih =>
      rcases q with _ | ⟨d, q'⟩
      · have hcount : (a :: ad').length + 1
            + (min (a :: ad').length ([] : List Digit).length + qt0.length + 1)
            = (ad'.length + 1 + (min ad'.length ([] : List Digit).length + qt0.length + 1))
              + 1 := by
          simp; omega
        rw [hcount, Function.iterate_add_apply, Function.iterate_one]
        simp only [List.map_cons, List.cons_append]
        rw [flipBind2_compareAddr_digit_qempty a ad' valTail r0 r1 r2 r3 r4 copyScratch qt0
          logTmp0 s0]
        have := ih ([] : List Digit) qt0 (MemSym.digit a :: logTmp0)
          {memSym := some (MemSym.digit a), queryDigit := none, equal := false} (by simp)
        simpa [List.reverse_cons, List.append_assoc] using this
      · by_cases hne : a = d
        · subst hne
          have hcount : (a :: ad').length + 1 + (min (a :: ad').length (a :: q').length
                + qt0.length + 1)
              = (ad'.length + 1 + (min ad'.length q'.length + (a :: qt0).length + 1)) + 1 := by
            simp; omega
          rw [hcount, Function.iterate_add_apply, Function.iterate_one]
          simp only [List.map_cons, List.cons_append]
          rw [flipBind2_compareAddr_digit_eq a ad' q' valTail r0 r1 r2 r3 r4 copyScratch qt0
            logTmp0 s0]
          have hmis' : ¬ (s0.equal = true ∧ ad' = q') := fun ⟨he, hl⟩ => hmis ⟨he, by rw [hl]⟩
          have := ih q' (a :: qt0) (MemSym.digit a :: logTmp0)
            {memSym := some (MemSym.digit a), queryDigit := some a, equal := s0.equal} hmis'
          simpa [List.reverse_cons, List.append_assoc] using this
        · have hcount : (a :: ad').length + 1 + (min (a :: ad').length (d :: q').length
                + qt0.length + 1)
              = (ad'.length + 1 + (min ad'.length q'.length + (d :: qt0).length + 1)) + 1 := by
            simp; omega
          rw [hcount, Function.iterate_add_apply, Function.iterate_one]
          simp only [List.map_cons, List.cons_append]
          rw [flipBind2_compareAddr_digit_neq a d ad' q' valTail r0 r1 r2 r3 r4 copyScratch qt0
            logTmp0 s0 hne]
          have := ih q' (d :: qt0) (MemSym.digit a :: logTmp0)
            {memSym := some (MemSym.digit a), queryDigit := some d, equal := false} (by simp)
          simpa [List.reverse_cons, List.append_assoc] using this

/-- The `copyQuery` loop: draining register `a` (`r0`) prepends its reverse (MSB-first) onto
    both `query` and `copyScratch`. -/
lemma copyQuery_loop (src : List Digit) (r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[src.length + 1]
        (some (cfgAt2 src r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
          (some Phase2.copyQuery) s0))
      = some (cfgAt2 [] r1 r2 r3 r4 mem (src.reverse ++ copyScratch) (src.reverse ++ query)
          queryTmp logTmp (some Phase2.copyQueryRestore) {s0 with queryDigit := none}) := by
  induction src generalizing copyScratch query s0 with
  | nil =>
      simpa using
        flipBind2_copyQuery_nil_exit r1 r2 r3 r4 mem copyScratch query queryTmp logTmp s0
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_copyQuery_cons d r1 r2 r3 r4 src' mem copyScratch query queryTmp logTmp s0,
        ih (d :: copyScratch) (d :: query) {s0 with queryDigit := some d}]
      simp [List.reverse_cons, List.append_assoc]

/-- The `copyQueryRestore` loop: draining `copyScratch` restores register `a` (`r0`) to
    `copyScratch.reverse ++ src`. -/
lemma copyQueryRestore_loop (copyScratch : List Digit) (src : List Digit)
    (r1 r2 r3 r4 : List Digit) (mem : List MemSym) (query queryTmp : List Digit)
    (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2^[copyScratch.length + 1]
        (some (cfgAt2 src r1 r2 r3 r4 mem copyScratch query queryTmp logTmp
          (some Phase2.copyQueryRestore) s0))
      = some (cfgAt2 (copyScratch.reverse ++ src) r1 r2 r3 r4 mem [] query queryTmp logTmp
          (some Phase2.compareAddr) {s0 with queryDigit := none}) := by
  induction copyScratch generalizing src s0 with
  | nil =>
      simpa using
        flipBind2_copyQueryRestore_nil_exit src r1 r2 r3 r4 mem query queryTmp logTmp s0
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_copyQueryRestore_cons d r1 r2 r3 r4 src mem cs' query queryTmp logTmp s0,
        ih (d :: src) {s0 with queryDigit := some d}]
      simp [List.reverse_cons, List.append_assoc]

/-- Running the initial `query` setup to completion: register `a` (`r0`) is restored exactly,
    and its reverse (MSB-first, matching `mem`'s address-field convention) lands on `query`,
    ready for `compareAddr` to scan against. -/
lemma copyQuery_phase (src : List Digit) (r1 r2 r3 r4 : List Digit) (mem : List MemSym)
    (s0 : LoadState) :
    flipBind2^[2 * src.length + 2]
        (some (cfgAt2 src r1 r2 r3 r4 mem [] [] [] [] (some Phase2.copyQuery) s0))
      = some (cfgAt2 src r1 r2 r3 r4 mem [] src.reverse [] [] (some Phase2.compareAddr)
          {s0 with queryDigit := none}) := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply,
    copyQuery_loop src r1 r2 r3 r4 mem [] [] [] [] s0, List.append_nil]
  have h2 := copyQueryRestore_loop src.reverse [] r1 r2 r3 r4 mem src.reverse []
    ([] : List MemSym) {s0 with queryDigit := (none : Option Digit)}
  simpa using h2

/-- The `skipValue` loop: consumes a mismatched entry's value field (`vd`, MSB-first, as
    stored) and the `entryEnd` after it into `logTmp` only (never touching `r4`), then returns
    to `compareAddr` for the next entry. -/
lemma skipValue_loop (vd : List Digit) (rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp0 : List MemSym) (s0 : LoadState) :
    flipBind2^[vd.length + 1]
        (some (cfgAt2 r0 r1 r2 r3 r4 ((vd.map MemSym.digit) ++ (MemSym.entryEnd :: rest))
          copyScratch query queryTmp logTmp0 (some Phase2.skipValue) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp
          (MemSym.entryEnd :: (vd.map MemSym.digit).reverse ++ logTmp0)
          (some Phase2.compareAddr)
          {memSym := some MemSym.entryEnd, queryDigit := s0.queryDigit, equal := true}) := by
  induction vd generalizing logTmp0 s0 with
  | nil =>
      simpa using
        flipBind2_skipValue_entryEnd rest r0 r1 r2 r3 r4 copyScratch query queryTmp logTmp0 s0
  | cons d vd' ih =>
      simp only [List.map_cons, List.cons_append]
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBind2_skipValue_digit d (List.map MemSym.digit vd' ++ MemSym.entryEnd :: rest)
          r0 r1 r2 r3 r4 copyScratch query queryTmp logTmp0 s0,
        ih (MemSym.digit d :: logTmp0) {s0 with memSym := some (MemSym.digit d)}]
      simp [List.reverse_cons, List.append_assoc]

/-- The `restoreMem` loop: draining the saved log restores `mem` to
    `savedLog.reverse ++ rest`, i.e. exactly what it held before the scan started (whatever
    `rest` was left un-scanned, with the popped-and-preserved prefix glued back on front), then
    (chaining `drainQuery_loop`/`drainQueryTmp_loop`) discards whatever `query`/`queryTmp` still
    hold — exactly one of the two, per `Phase2`'s docstring — so both end up empty, matching
    every other stack `Represents` (`GenericProgramMachine.lean`) requires empty at instruction
    boundaries. -/
lemma restoreMem_loop (savedLog rest : List MemSym) (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (s0 : LoadState) :
    flipBind2^[(queryTmp.length + 1) + (query.length + 1) + (savedLog.length + 1)]
        (some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp savedLog
          (some Phase2.restoreMem) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (savedLog.reverse ++ rest) copyScratch [] [] []
          (some Phase2.done) {s0 with memSym := none, queryDigit := none}) := by
  have hrm : flipBind2^[savedLog.length + 1]
      (some (cfgAt2 r0 r1 r2 r3 r4 rest copyScratch query queryTmp savedLog
        (some Phase2.restoreMem) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 (savedLog.reverse ++ rest) copyScratch query queryTmp []
          (some Phase2.drainQuery) {s0 with memSym := none}) := by
    induction savedLog generalizing rest s0 with
    | nil =>
        simpa using flipBind2_restoreMem_nil_exit r0 r1 r2 r3 r4 rest copyScratch query queryTmp s0
    | cons m saved' ih =>
        rw [List.length_cons, Function.iterate_succ_apply,
          flipBind2_restoreMem_cons m saved' r0 r1 r2 r3 r4 rest copyScratch query queryTmp s0,
          ih (m :: rest) {s0 with memSym := some m}]
        simp [List.reverse_cons, List.append_assoc]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hrm,
    drainQuery_loop query r0 r1 r2 r3 r4 (savedLog.reverse ++ rest) copyScratch queryTmp []
      {s0 with memSym := none},
    drainQueryTmp_loop queryTmp r0 r1 r2 r3 r4 (savedLog.reverse ++ rest) copyScratch []
      {s0 with memSym := none, queryDigit := none}]

lemma flipBind2_compareAddr_nomore (r0 r1 r2 r3 r4 : List Digit)
    (copyScratch query queryTmp : List Digit) (logTmp : List MemSym) (s0 : LoadState) :
    flipBind2 (some (cfgAt2 r0 r1 r2 r3 r4 ([] : List MemSym) copyScratch query queryTmp logTmp
        (some Phase2.compareAddr) s0))
      = some (cfgAt2 r0 r1 r2 r3 r4 [] copyScratch query queryTmp logTmp
          (some Phase2.restoreMem) {s0 with memSym := none}) := by
  show (Turing.TM2.step prog2)
      (cfgAt2 r0 r1 r2 r3 r4 [] copyScratch query queryTmp logTmp
        (some Phase2.compareAddr) s0) = _
  simp [prog2, cfgAt2]

/-- `natToDigits` has a left inverse (`digitsToNat_natToDigits`), hence is injective — needed
    to turn a mismatched RAM address (`a ≠ addr`) into a mismatched MSB-first digit list
    (`compareAddr_mismatch_then_restore`'s own hypothesis shape). -/
lemma natToDigits_injective : Function.Injective natToDigits := by
  intro x y hxy
  have := congrArg digitsToNat hxy
  rwa [digitsToNat_natToDigits, digitsToNat_natToDigits] at this

/-- The scan phase: starting at `compareAddr` with `mem` holding exactly the serialized
    write-log (`encodeLog log`), register `a` restored to `natToDigits addr`, and `query`
    already set to `(natToDigits addr).reverse` (as `copyQuery_phase` leaves it), running for
    some number of steps reaches `done` with register `t` (`r4`) holding `scanResult addr log`,
    `mem` fully restored to `logTmp0.reverse ++ encodeLog log` — i.e. `encodeLog log` itself
    when this is invoked fresh with `logTmp0 := []` — and (via `restoreMem_loop`'s own
    `drainQuery`/`drainQueryTmp` tail) both `query` and `queryTmp` emptied, matching
    `Represents`'s all-scratch-empty requirement. The exact step count isn't pinned down since
    it doesn't affect `load`'s observable effect; only its *existence* is asserted. Proved by
    induction on `log`, mirroring `scanResult`'s own recursion: `compareAddr_loop_matched` +
    `readValue_loop` + `restoreMem_loop` on a match, `compareAddr_mismatch_then_restore` +
    `skipValue_loop` + the inductive hypothesis on a mismatch. -/
lemma scan_phase (addr : ℕ) (log : WriteLog) (r1 r2 r3 : List Digit) (logTmp0 : List MemSym)
    (s0 : LoadState) (heq : s0.equal = true) (hqd : s0.queryDigit = none) :
    ∃ (n : ℕ),
      flipBind2^[n]
          (some (cfgAt2 (natToDigits addr) r1 r2 r3 [] (encodeLog log) []
            ((natToDigits addr).reverse) [] logTmp0 (some Phase2.compareAddr) s0))
        = some (cfgAt2 (natToDigits addr) r1 r2 r3 (scanResult addr log)
            (logTmp0.reverse ++ encodeLog log) [] [] [] []
            (some Phase2.done) {memSym := none, queryDigit := none, equal := true}) := by
  induction log generalizing logTmp0 s0 with
  | nil =>
      have hrm := restoreMem_loop logTmp0 [] (natToDigits addr) r1 r2 r3 [] []
        ((natToDigits addr).reverse) [] {s0 with memSym := none}
      refine ⟨(([] : List Digit).length + 1 + ((natToDigits addr).reverse.length + 1)
        + (logTmp0.length + 1)) + 1, ?_⟩
      simp only [encodeLog, List.map_nil, List.flatten_nil, scanResult, List.append_nil]
      rw [Function.iterate_add_apply, Function.iterate_one,
        flipBind2_compareAddr_nomore (natToDigits addr) r1 r2 r3 [] [] ((natToDigits addr).reverse)
          [] logTmp0 s0, hrm]
      simp [heq]
  | cons e xs ih =>
      obtain ⟨a, v⟩ := e
      by_cases hmatch : a = addr
      · subst hmatch
        have step1 := compareAddr_loop_matched (natToDigits a).reverse
          ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs))
          (natToDigits a) r1 r2 r3 [] [] [] logTmp0 s0 heq
        rw [List.reverse_reverse, List.append_nil] at step1
        have step2 := readValue_loop (natToDigits v).reverse (encodeLog xs) (natToDigits a) r1 r2 r3
          [] [] [] (natToDigits a)
          (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++ logTmp0)
          ({memSym := some MemSym.addrEnd, queryDigit := none, equal := true} : LoadState)
        rw [List.reverse_reverse, List.append_nil] at step2
        conv at step2 => rhs; rw [List.map_reverse, List.reverse_reverse]
        have step3 := restoreMem_loop
          (MemSym.entryEnd :: (natToDigits v).map MemSym.digit ++
            (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++ logTmp0))
          (encodeLog xs) (natToDigits a) r1 r2 r3 (natToDigits v) [] [] (natToDigits a)
          ({memSym := some MemSym.entryEnd, queryDigit := none, equal := true} : LoadState)
        set CA := (natToDigits a).reverse.length + 1 with hCA
        set RV := (natToDigits v).reverse.length + 1 with hRV
        set RM := (natToDigits a).length + 1 + (([] : List Digit).length + 1)
            + ((MemSym.entryEnd :: (natToDigits v).map MemSym.digit ++
              (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++ logTmp0)).length + 1)
            with hRM
        refine ⟨RM + (RV + CA), ?_⟩
        rw [Function.iterate_add_apply flipBind2 RM (RV + CA),
          Function.iterate_add_apply flipBind2 RV CA]
        show flipBind2^[RM] (flipBind2^[RV] (flipBind2^[CA]
            (some (cfgAt2 (natToDigits a) r1 r2 r3 []
              (encodeEntry a v ++ encodeLog xs) [] (natToDigits a).reverse [] logTmp0
              (some Phase2.compareAddr) s0)))) = _
        simp only [encodeEntry, List.append_assoc, List.cons_append, List.nil_append]
        rw [step1, step2, step3]
        congr 1
        simp [encodeLog, encodeEntry, scanResult, List.reverse_append, List.append_assoc,
          List.map_reverse]
      · have hne : (natToDigits a).reverse ≠ (natToDigits addr).reverse :=
          fun h => hmatch (natToDigits_injective (List.reverse_injective h))
        have hmis : ¬ (s0.equal = true ∧ (natToDigits a).reverse = (natToDigits addr).reverse) :=
          fun ⟨_, h⟩ => hne h
        have step1 := compareAddr_mismatch_then_restore (natToDigits a).reverse
          (natToDigits addr).reverse
          ((natToDigits v).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog xs))
          (natToDigits addr) r1 r2 r3 [] [] [] logTmp0 s0 hmis
        simp only [List.reverse_reverse, List.reverse_nil, List.nil_append,
          List.length_nil, Nat.add_zero] at step1
        have step2 := skipValue_loop (natToDigits v).reverse (encodeLog xs) (natToDigits addr)
          r1 r2 r3 [] [] (natToDigits addr).reverse []
          (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++ logTmp0)
          ({memSym := some MemSym.addrEnd, queryDigit := none, equal := false} : LoadState)
        conv at step2 => rhs; rw [List.map_reverse, List.reverse_reverse]
        obtain ⟨n', hstep3⟩ := ih
          (MemSym.entryEnd :: (natToDigits v).map MemSym.digit ++
            (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++ logTmp0))
          ({memSym := some MemSym.entryEnd, queryDigit := none, equal := true} : LoadState) rfl rfl
        set CAM := (natToDigits a).reverse.length + 1
          + (min (natToDigits a).reverse.length (natToDigits addr).reverse.length + 1) with hCAM
        set SV := (natToDigits v).reverse.length + 1 with hSV
        refine ⟨n' + (SV + CAM), ?_⟩
        rw [Function.iterate_add_apply flipBind2 n' (SV + CAM),
          Function.iterate_add_apply flipBind2 SV CAM]
        show flipBind2^[n'] (flipBind2^[SV] (flipBind2^[CAM]
            (some (cfgAt2 (natToDigits addr) r1 r2 r3 []
              (encodeEntry a v ++ encodeLog xs) [] (natToDigits addr).reverse [] logTmp0
              (some Phase2.compareAddr) s0)))) = _
        simp only [encodeEntry, List.append_assoc, List.cons_append, List.nil_append]
        rw [step1, step2, hstep3]
        congr 1
        simp [encodeLog, encodeEntry, scanResult, hmatch, List.reverse_append, List.append_assoc,
          List.map_reverse]

/-- Starting with register `r0` holding `natToDigits addr` and `mem` holding `encodeLog log`,
    running `prog2` from `copyQuery` for some number of steps leaves every register untouched
    except `r4`, which holds `scanResult addr log`, and restores `mem` to `encodeLog log`. The
    pure specification agrees with `lookupD` by `scanResult_eq_lookupD`. Every private scratch
    stack is empty at termination, so the result can be composed with a subsequent machine phase. -/
lemma realize_load (addr : ℕ) (log : WriteLog) (r1 r2 r3 : List Digit) (v0 : LoadState)
    (heq : v0.equal = true) :
    ∃ (n : ℕ),
      flipBind2^[n]
          (some (cfgAt2 (natToDigits addr) r1 r2 r3 [] (encodeLog log) [] [] [] []
            (some Phase2.copyQuery) v0))
        = some (cfgAt2 (natToDigits addr) r1 r2 r3 (scanResult addr log)
            (encodeLog log) [] [] [] []
            (some Phase2.done) {memSym := none, queryDigit := none, equal := true}) := by
  have step1 := copyQuery_phase (natToDigits addr) r1 r2 r3 [] (encodeLog log) v0
  obtain ⟨n', hstep2⟩ := scan_phase addr log r1 r2 r3 []
    {v0 with queryDigit := none} heq rfl
  simp only [List.reverse_nil, List.nil_append] at hstep2
  refine ⟨n' + (2 * (natToDigits addr).length + 2), ?_⟩
  rw [Function.iterate_add_apply, step1, hstep2]

/-- `scan_phase` for the two-entry log `[(b, y), (a, x)]` with `a ≠ b`: the first entry mismatches
    and is skipped, then the second entry matches. The composed step lemmas give an explicit
    transition count, bounded by a linear expression in the four operands' digit lengths. -/
lemma scanPhase_two (a b x y : ℕ) (hab : a ≠ b) (r1 r2 r3 : List Digit)
    (logTmp0 : List MemSym) (s0 : LoadState) :
    ∃ n, flipBind2^[n]
        (some (cfgAt2 (natToDigits a) r1 r2 r3 [] (encodeLog [(b, y), (a, x)]) []
          ((natToDigits a).reverse) [] logTmp0 (some Phase2.compareAddr) s0))
      = some (cfgAt2 (natToDigits a) r1 r2 r3 (scanResult a [(b, y), (a, x)])
          (logTmp0.reverse ++ encodeLog [(b, y), (a, x)]) [] [] [] []
          (some Phase2.done) {memSym := none, queryDigit := none, equal := true})
      ∧ n ≤ 5 * ((natToDigits a).length + (natToDigits b).length + (natToDigits x).length +
          (natToDigits y).length) + logTmp0.length + (natToDigits a).length + 12 := by
  have hne : (natToDigits b).reverse ≠ (natToDigits a).reverse :=
    fun h => hab (natToDigits_injective (List.reverse_injective h.symm))
  have hmis : ¬ (s0.equal = true ∧ (natToDigits b).reverse = (natToDigits a).reverse) :=
    fun ⟨_, h⟩ => hne h
  have hencOne : encodeLog [(b, y), (a, x)] = encodeEntry b y ++ encodeLog [(a, x)] := by
    simp [encodeLog]
  have hencTwo : encodeLog [(a, x)] = encodeEntry a x ++ encodeLog ([] : WriteLog) := by
    simp [encodeLog]
  have step1 := compareAddr_mismatch_then_restore (natToDigits b).reverse (natToDigits a).reverse
    ((natToDigits y).reverse.map MemSym.digit ++
      (MemSym.entryEnd :: (encodeLog [(a, x)])))
    (natToDigits a) r1 r2 r3 [] [] [] logTmp0 s0 hmis
  simp only [List.reverse_reverse, List.reverse_nil, List.nil_append,
    List.length_nil, Nat.add_zero] at step1
  have step2 := skipValue_loop (natToDigits y).reverse (encodeLog [(a, x)]) (natToDigits a)
    r1 r2 r3 [] [] (natToDigits a).reverse []
    (MemSym.addrEnd :: (natToDigits b).map MemSym.digit ++ logTmp0)
    ({memSym := some MemSym.addrEnd, queryDigit := none, equal := false} : LoadState)
  conv at step2 => rhs; rw [List.map_reverse, List.reverse_reverse]
  have step3 := compareAddr_loop_matched (natToDigits a).reverse
    ((natToDigits x).reverse.map MemSym.digit ++ (MemSym.entryEnd :: encodeLog ([] : WriteLog)))
    (natToDigits a) r1 r2 r3 [] [] []
    (MemSym.entryEnd :: (natToDigits y).map MemSym.digit ++
      (MemSym.addrEnd :: (natToDigits b).map MemSym.digit ++ logTmp0))
    ({memSym := some MemSym.entryEnd, queryDigit := none, equal := true} : LoadState) rfl
  rw [List.reverse_reverse, List.append_nil] at step3
  have step4 := readValue_loop (natToDigits x).reverse (encodeLog ([] : WriteLog))
    (natToDigits a) r1 r2 r3 [] [] [] (natToDigits a)
    (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++
      (MemSym.entryEnd :: (natToDigits y).map MemSym.digit ++
        (MemSym.addrEnd :: (natToDigits b).map MemSym.digit ++ logTmp0)))
    ({memSym := some MemSym.addrEnd, queryDigit := none, equal := true} : LoadState)
  rw [List.reverse_reverse, List.append_nil] at step4
  conv at step4 => rhs; rw [List.map_reverse, List.reverse_reverse]
  have step5 := restoreMem_loop
    (MemSym.entryEnd :: (natToDigits x).map MemSym.digit ++
      (MemSym.addrEnd :: (natToDigits a).map MemSym.digit ++
        (MemSym.entryEnd :: (natToDigits y).map MemSym.digit ++
          (MemSym.addrEnd :: (natToDigits b).map MemSym.digit ++ logTmp0))))
    (encodeLog ([] : WriteLog)) (natToDigits a) r1 r2 r3 (natToDigits x) [] [] (natToDigits a)
    ({memSym := some MemSym.entryEnd, queryDigit := none, equal := true} : LoadState)
  simp only [List.cons_append] at step1 step2 step3 step4 step5
  set CAM := (natToDigits b).reverse.length + 1
    + (min (natToDigits b).reverse.length (natToDigits a).reverse.length + 1) with hCAM
  set SV := (natToDigits y).reverse.length + 1 with hSV
  set CA := (natToDigits a).reverse.length + 1 with hCA
  set RV := (natToDigits x).reverse.length + 1 with hRV
  set RM := (natToDigits a).length + 1 + (([] : List Digit).length + 1)
      + ((MemSym.entryEnd :: ((natToDigits x).map MemSym.digit ++
        (MemSym.addrEnd :: ((natToDigits a).map MemSym.digit ++
          (MemSym.entryEnd :: ((natToDigits y).map MemSym.digit ++
            (MemSym.addrEnd :: ((natToDigits b).map MemSym.digit ++ logTmp0)))))))).length + 1)
    with hRM
  refine ⟨RM + (RV + (CA + (SV + CAM))), ?_, ?_⟩
  · rw [Function.iterate_add_apply flipBind2 RM (RV + (CA + (SV + CAM))),
      Function.iterate_add_apply flipBind2 RV (CA + (SV + CAM)),
      Function.iterate_add_apply flipBind2 CA (SV + CAM),
      Function.iterate_add_apply flipBind2 SV CAM]
    show flipBind2^[RM] (flipBind2^[RV] (flipBind2^[CA] (flipBind2^[SV] (flipBind2^[CAM]
        (some (cfgAt2 (natToDigits a) r1 r2 r3 [] (encodeLog [(b, y), (a, x)]) []
          ((natToDigits a).reverse) [] logTmp0 (some Phase2.compareAddr) s0)))))) = _
    rw [hencOne]
    simp only [encodeEntry, List.append_assoc, List.cons_append, List.nil_append]
    rw [step1, step2]
    rw [hencTwo]
    simp only [encodeEntry, List.append_assoc, List.cons_append, List.nil_append]
    rw [step3, step4, step5]
    congr 1
    simp [encodeLog, encodeEntry, scanResult, hab.symm, List.reverse_append, List.append_assoc,
      List.map_reverse]
  · simp only [hRM, hRV, hCA, hSV, hCAM, List.length_cons, List.length_append,
      List.length_map, List.length_reverse, List.length_nil]
    have hmin : min (natToDigits b).length (natToDigits a).length ≤ (natToDigits b).length :=
      min_le_left _ _
    omega

/-- The two-entry instance of `realize_load`, combining `scanPhase_two` with the fixed cost of
    `copyQuery_phase` to give an explicit polynomial bound on the transition count. -/
lemma realize_load_two (a b x y : ℕ) (hab : a ≠ b) (r1 r2 r3 : List Digit) (v0 : LoadState) :
    ∃ n, flipBind2^[n]
        (some (cfgAt2 (natToDigits a) r1 r2 r3 [] (encodeLog [(b, y), (a, x)]) [] [] [] []
          (some Phase2.copyQuery) v0))
      = some (cfgAt2 (natToDigits a) r1 r2 r3 (scanResult a [(b, y), (a, x)])
          (encodeLog [(b, y), (a, x)]) [] [] [] []
          (some Phase2.done) {memSym := none, queryDigit := none, equal := true})
      ∧ n ≤ 5 * ((natToDigits a).length + (natToDigits b).length + (natToDigits x).length +
          (natToDigits y).length) + 3 * (natToDigits a).length + 14 := by
  have step1 := copyQuery_phase (natToDigits a) r1 r2 r3 [] (encodeLog [(b, y), (a, x)]) v0
  obtain ⟨n', hstep2, hbound⟩ := scanPhase_two a b x y hab r1 r2 r3 []
    {v0 with queryDigit := none}
  simp only [List.reverse_nil, List.nil_append, List.length_nil] at hstep2 hbound
  refine ⟨n' + (2 * (natToDigits a).length + 2), ?_, ?_⟩
  · rw [Function.iterate_add_apply, step1, hstep2]
  · omega

end NPComplete.RAMToTM

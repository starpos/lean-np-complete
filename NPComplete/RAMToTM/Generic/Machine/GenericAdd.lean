module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.DigitAdd
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `add` realized against an arbitrary register triple

`addProg` snapshots both source registers before clearing the destination. Each snapshot restores
its source non-destructively, so the operation is safe even when `rd`, `rs`, and `rt` alias. The
scratch stacks are distinct from register stacks, which keeps the read-restore updates independent
of the chosen register indices.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit AddState addDigits addRaw natToDigits addRaw_natToDigits
  liftStmt iterate_bind_step_liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs rt : Fin (regBound p))

/-- `add`'s `Stmt` tree at an arbitrary register triple: non-destructively snapshot `rs` into
    `lhsOperand` (`copyLhs`/`copyLhsRestore`/`reverseLhs`), then `rt` into `rhsOperand`
    (`copyRhs`/`copyRhsRestore`/`reverseRhs`, resetting `AddState` to canonical on exit), drain
    `rd` (`clearDest`), run `DigitAdd`'s ripple-carry loop against `lhsOperand`/`rhsOperand`
    (`addLoop`), then reverse the
    MSB-first sum from `sumScratch` onto the now-empty `rd` (`reverseSum`). -/
def addProg : AddPhase → Turing.TM2.Stmt (Γg p) AddPhase AddState
  | .copyLhs =>
      pop (Kg.reg rs) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.scratch .workRev) (fun s => s.a.getD default)
            (push (Kg.scratch .copyScratch) (fun s => s.a.getD default)
              (goto (fun _ => .copyLhs))))
          (goto (fun _ => .copyLhsRestore)))
  | .copyLhsRestore =>
      pop (Kg.scratch .copyScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rs) (fun s => s.a.getD default)
            (goto (fun _ => .copyLhsRestore)))
          (goto (fun _ => .reverseLhs)))
  | .reverseLhs =>
      pop (Kg.scratch .workRev) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.scratch .lhsOperand) (fun s => s.a.getD default)
            (goto (fun _ => .reverseLhs)))
          (goto (fun _ => .copyRhs)))
  | .copyRhs =>
      pop (Kg.reg rt) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.scratch .workRev) (fun s => s.a.getD default)
            (push (Kg.scratch .copyScratch) (fun s => s.a.getD default)
              (goto (fun _ => .copyRhs))))
          (goto (fun _ => .copyRhsRestore)))
  | .copyRhsRestore =>
      pop (Kg.scratch .copyScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rt) (fun s => s.a.getD default)
            (goto (fun _ => .copyRhsRestore)))
          (goto (fun _ => .reverseRhs)))
  | .reverseRhs =>
      pop (Kg.scratch .workRev) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.scratch .rhsOperand) (fun s => s.a.getD default)
            (goto (fun _ => .reverseRhs)))
          (load (fun _ => (⟨none, none, false⟩ : AddState)) (goto (fun _ => .clearDest))))
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .addLoop)))
  | .addLoop =>
      peek (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
        (peek (Kg.scratch .rhsOperand) (fun s ov => {s with b := ov})
          (branch (fun s => s.a.isSome || s.b.isSome || s.carry)
            (pop (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
              (pop (Kg.scratch .rhsOperand) (fun s ov => {s with b := ov})
                (push (Kg.scratch .sumScratch)
                    (fun s => (addDigits (s.a.getD 0) (s.b.getD 0) s.carry).1)
                  (load (fun s =>
                      {s with carry := (addDigits (s.a.getD 0) (s.b.getD 0) s.carry).2})
                    (goto (fun _ => .addLoop))))))
            (goto (fun _ => .reverseSum))))
  | .reverseSum =>
      pop (Kg.scratch .sumScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rd) (fun s => s.a.getD default)
            (goto (fun _ => .reverseSum)))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindAdd :
    Option (Turing.TM2.Cfg (Γg p) AddPhase AddState) →
      Option (Turing.TM2.Cfg (Γg p) AddPhase AddState) :=
  fun x => x.bind (Turing.TM2.step (addProg rd rs rt))

/-! ## `copyLhs` / `copyLhsRestore`: non-destructively snapshotting `rs` -/

lemma flipBindAdd_copyLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRs : Sg (Kg.reg rs) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyLhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rs) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRs]

lemma flipBindAdd_copyLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRs : Sg (Kg.reg rs) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyLhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRs]

/-- Draining register `rs`, prepending its reverse onto both `workRev` and `copyScratch`. -/
lemma copyLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hRs : Sg (Kg.reg rs) = src) :
    (flipBindAdd rd rs rt)^[src.length + 1]
        (some (⟨some AddPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyLhsRestore, {v0 with a := none},
          Function.update (Function.update (Function.update Sg (Kg.reg rs) [])
            (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rs) [])
          (Kg.scratch .workRev) (Sg (Kg.scratch .workRev)))
          (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rs
        · subst hk; simp [Function.update, hRs]
        · by_cases hk2 : k = Kg.scratch .workRev
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .copyScratch
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindAdd_copyLhs_nil_exit rd rs rt Sg v0 hRs
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_copyLhs_cons rd rs rt d src' Sg v0 hRs,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rs) src')
              (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
              (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
           {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rs
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .workRev
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindAdd_copyLhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyLhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rs) (d :: Sg (Kg.reg rs))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSc]

lemma flipBindAdd_copyLhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseLhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSc]

/-- Draining `copyScratch` restores register `rs` to `copyScratch.reverse ++ src`. -/
lemma copyLhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindAdd rd rs rt)^[copyScratch.length + 1]
        (some (⟨some AddPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseLhs, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.reg rs) (copyScratch.reverse ++ Sg (Kg.reg rs))⟩ := by
  induction copyScratch generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
          (Kg.reg rs) (Sg (Kg.reg rs)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .copyScratch
        · subst hk; simp [Function.update, hSc]
        · by_cases hk2 : k = Kg.reg rs
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindAdd_copyLhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_copyLhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rs) (d :: Sg (Kg.reg rs))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rs
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the `rs` copy to completion: register `rs` is restored exactly, and its reverse is
    prepended onto `workRev`. Generalizes `GenericStore.store_copyValue_phase`'s combinator shape
    (retargeted from `mem` to `workRev`, no destination-alphabet embedding needed). -/
lemma copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hRs : Sg (Kg.reg rs) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindAdd rd rs rt)^[2 * src.length + 2]
        (some (⟨some AddPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseLhs, {v0 with a := none},
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, copyLhs_loop rd rs rt src Sg v0 hRs]
  simp only [hSc, List.append_nil]
  have h2 := copyLhsRestore_loop rd rs rt src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rs) [])
      (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .copyScratch) src.reverse) {v0 with a := none} (by simp)
  rw [h2]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
  funext k
  by_cases hk : k = Kg.reg rs
  · subst hk; simp [Function.update, hRs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hk]
    · by_cases hk3 : k = Kg.scratch .copyScratch
      · subst hk3; simp [Function.update, hk, hk2, hSc]
      · simp [Function.update, hk, hk2, hk3]

/-! ## `reverseLhs`: flipping `workRev` back to LSB-first order onto `lhsOperand` -/

lemma flipBindAdd_reverseLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseLhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hWr]

lemma flipBindAdd_reverseLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hWr]

/-- Draining `workRev`, prepending its reverse onto `lhsOperand` — since `workRev` holds `rs`'s
    digits reversed (`copyLhs_phase`), this rebuilds the original LSB-first `rs`. The state
    reset is deferred to `reverseRhs` (see the module docstring: only one canonical reset is
    needed, right before `addLoop`). -/
lemma reverseLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindAdd rd rs rt)^[src.length + 1]
        (some (⟨some AddPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhs, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .workRev) [])
            (Kg.scratch .lhsOperand) (src.reverse ++ Sg (Kg.scratch .lhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .workRev) [])
          (Kg.scratch .lhsOperand) (Sg (Kg.scratch .lhsOperand)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .workRev
        · subst hk; simp [Function.update, hWr]
        · by_cases hk2 : k = Kg.scratch .lhsOperand
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindAdd_reverseLhs_nil_exit rd rs rt Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_reverseLhs_cons rd rs rt d src' Sg v0 hWr,
        ih (Function.update (Function.update Sg (Kg.scratch .workRev) src')
              (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))) {v0 with a := some d}
           (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .workRev
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .lhsOperand
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-! ## `copyRhs` / `copyRhsRestore`: non-destructively snapshotting `rt` (mirrors `copyLhs`) -/

lemma flipBindAdd_copyRhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRt : Sg (Kg.reg rt) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rt) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRt]

lemma flipBindAdd_copyRhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRt]

/-- Draining register `rt`, prepending its reverse onto both `workRev` and `copyScratch`.
    Mirrors `copyLhs_loop`. -/
lemma copyRhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hRt : Sg (Kg.reg rt) = src) :
    (flipBindAdd rd rs rt)^[src.length + 1]
        (some (⟨some AddPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhsRestore, {v0 with a := none},
          Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
            (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
          (Kg.scratch .workRev) (Sg (Kg.scratch .workRev)))
          (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rt
        · subst hk; simp [Function.update, hRt]
        · by_cases hk2 : k = Kg.scratch .workRev
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .copyScratch
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindAdd_copyRhs_nil_exit rd rs rt Sg v0 hRt
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_copyRhs_cons rd rs rt d src' Sg v0 hRt,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rt) src')
              (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
              (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
           {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rt
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .workRev
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindAdd_copyRhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rt) (d :: Sg (Kg.reg rt))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSc]

lemma flipBindAdd_copyRhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseRhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSc]

/-- Draining `copyScratch` restores register `rt` to `copyScratch.reverse ++ src`. Mirrors
    `copyLhsRestore_loop`. -/
lemma copyRhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindAdd rd rs rt)^[copyScratch.length + 1]
        (some (⟨some AddPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseRhs, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.reg rt) (copyScratch.reverse ++ Sg (Kg.reg rt))⟩ := by
  induction copyScratch generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
          (Kg.reg rt) (Sg (Kg.reg rt)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .copyScratch
        · subst hk; simp [Function.update, hSc]
        · by_cases hk2 : k = Kg.reg rt
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindAdd_copyRhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_copyRhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rt) (d :: Sg (Kg.reg rt))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rt
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the `rt` copy to completion: register `rt` is restored exactly, and its reverse is
    prepended onto `workRev`. Mirrors `copyLhs_phase`. -/
lemma copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hRt : Sg (Kg.reg rt) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindAdd rd rs rt)^[2 * src.length + 2]
        (some (⟨some AddPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseRhs, {v0 with a := none},
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, copyRhs_loop rd rs rt src Sg v0 hRt]
  simp only [hSc, List.append_nil]
  have h2 := copyRhsRestore_loop rd rs rt src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
      (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .copyScratch) src.reverse) {v0 with a := none} (by simp)
  rw [h2]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
  funext k
  by_cases hk : k = Kg.reg rt
  · subst hk; simp [Function.update, hRt]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hk]
    · by_cases hk3 : k = Kg.scratch .copyScratch
      · subst hk3; simp [Function.update, hk, hk2, hSc]
      · simp [Function.update, hk, hk2, hk3]

/-! ## `reverseRhs`: flipping `workRev` onto `rhsOperand`, then resetting state to canonical -/

lemma flipBindAdd_reverseRhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseRhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hWr]

/-- The `reverseRhs` exit resets `AddState` to fully canonical (`⟨none, none, false⟩`), not just
    `carry`: the value fed to `addLoop`'s first iteration must not be whatever stray value an
    earlier, unrelated phase left behind. Every field is reset, since `addLoop` immediately
    `peek`s both `a`/`b` before reading them, so resetting them too costs nothing. -/
lemma flipBindAdd_reverseRhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.clearDest, ⟨none, none, false⟩, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hWr]

/-- Draining `workRev`, prepending its reverse onto `rhsOperand`. Mirrors `reverseLhs_loop`. -/
lemma reverseRhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindAdd rd rs rt)^[src.length + 1]
        (some (⟨some AddPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.clearDest, ⟨none, none, false⟩,
          Function.update (Function.update Sg (Kg.scratch .workRev) [])
            (Kg.scratch .rhsOperand) (src.reverse ++ Sg (Kg.scratch .rhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .workRev) [])
          (Kg.scratch .rhsOperand) (Sg (Kg.scratch .rhsOperand)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .workRev
        · subst hk; simp [Function.update, hWr]
        · by_cases hk2 : k = Kg.scratch .rhsOperand
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindAdd_reverseRhs_nil_exit rd rs rt Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_reverseRhs_cons rd rs rt d src' Sg v0 hWr,
        ih (Function.update (Function.update Sg (Kg.scratch .workRev) src')
              (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand))) {v0 with a := some d}
           (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .workRev
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .rhsOperand
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-! ## `clearDest`: draining `rd`, discarding every digit -/

lemma flipBindAdd_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.clearDest, {v0 with a := some d},
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRd]

lemma flipBindAdd_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.addLoop, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hRd]

/-- Draining register `rd`, discarding every digit: `Represents` only needs it empty afterward
    before `addLoop` writes the sum there via `reverseSum`, whatever content it held is
    irrelevant. Alias-safe regardless of `rd = rs`/`rd = rt` (module docstring): by this point
    both operands are already captured in `lhsOperand`/`rhsOperand`, independent of `rd`'s
    register stack. Mirrors `GenericLoad.load_clearDest_loop`. -/
lemma add_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindAdd rd rs rt)^[dest.length + 1]
        (some (⟨some AddPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.addLoop, {v0 with a := none},
          Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindAdd_clearDest_nil_exit rd rs rt Sg v0 hRd
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_clearDest_cons rd rs rt d ds' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) ds') {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `addLoop`: `DigitAdd`'s ripple-carry loop, retargeted to `lhsOperand`/`rhsOperand` -/

/-- `addLoop` exit: both operands exhausted and no carry pending. -/
lemma addLoop_step_done (Sg : ∀ k, List (Γg p k)) (s0 : AddState) (hc : s0.carry = false)
    (hLhs : Sg (Kg.scratch .lhsOperand) = [])
    (hRhs : Sg (Kg.scratch .rhsOperand) = []) :
    (Turing.TM2.step (addProg rd rs rt))
        (⟨some AddPhase.addLoop, s0, Sg⟩ : Turing.TM2.Cfg (Γg p) AddPhase AddState)
      = some ⟨some AddPhase.reverseSum, ⟨none, none, false⟩, Sg⟩ := by
  have heq : s0 = ⟨s0.a, s0.b, false⟩ := by cases s0; simp_all
  rw [heq]
  simp [addProg, hLhs, hRhs]

/-- `addLoop`'s general step. -/
lemma addLoop_step_general (Sg : ∀ k, List (Γg p k)) (srcA srcB : List Digit) (s0 : AddState)
    (hLhs : Sg (Kg.scratch .lhsOperand) = srcA) (hRhs : Sg (Kg.scratch .rhsOperand) = srcB)
    (hbase : ¬ (srcA = [] ∧ srcB = [] ∧ s0.carry = false)) :
    (Turing.TM2.step (addProg rd rs rt))
        (⟨some AddPhase.addLoop, s0, Sg⟩ : Turing.TM2.Cfg (Γg p) AddPhase AddState)
      = some ⟨some AddPhase.addLoop,
          ⟨srcA.head?, srcB.head?, (addDigits (srcA.headD 0) (srcB.headD 0) s0.carry).2⟩,
          Function.update
            (Function.update
              (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
              (Kg.scratch .rhsOperand) srcB.tail)
            (Kg.scratch .sumScratch)
            ((addDigits (srcA.headD 0) (srcB.headD 0) s0.carry).1 ::
              Sg (Kg.scratch .sumScratch))⟩ := by
  rcases srcA with _ | ⟨da, ta⟩ <;> rcases srcB with _ | ⟨db, tb⟩ <;>
    simp only [List.headD_nil, List.headD_cons, List.head?_nil, List.head?_cons, List.tail_nil,
      List.tail_cons]
  · rcases hs : s0.carry with _ | _
    · exact absurd ⟨rfl, rfl, hs⟩ hbase
    · have heq : s0 = ⟨s0.a, s0.b, true⟩ := by cases s0; simp_all
      rw [heq]
      simp [addProg, hLhs, hRhs]
  · simp [addProg, hLhs, hRhs]
  · simp [addProg, hLhs, hRhs]
  · simp [addProg, hLhs, hRhs]

/-- Running `addLoop` to completion: drains `lhsOperand` (`srcA`) and `rhsOperand` (`srcB`),
    leaving the reverse of the LSB-first sum digits from `DigitAdd.addRaw` prepended onto
    `sumScratch`. -/
lemma addLoop_run (Sg : ∀ k, List (Γg p k)) (srcA srcB : List Digit) (carry : Bool)
    (sa sb : Option Digit) (hLhs : Sg (Kg.scratch .lhsOperand) = srcA)
    (hRhs : Sg (Kg.scratch .rhsOperand) = srcB) :
    (flipBindAdd rd rs rt)^[(addRaw srcA srcB carry).length + 1]
        (some (⟨some AddPhase.addLoop, ⟨sa, sb, carry⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseSum, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) [])
            (Kg.scratch .sumScratch)
            ((addRaw srcA srcB carry).reverse ++ Sg (Kg.scratch .sumScratch))⟩ := by
  induction srcA, srcB, carry using addRaw.induct generalizing Sg sa sb with
  | case1 srcA srcB carry hbase =>
      obtain ⟨hA, hB, hc⟩ := hbase
      subst hA; subst hB; subst hc
      rw [show addRaw ([] : List Digit) [] false = [] by rw [addRaw]; simp]
      simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append]
      show (Turing.TM2.step (addProg rd rs rt))
          (⟨some AddPhase.addLoop, ⟨sa, sb, false⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
      rw [addLoop_step_done rd rs rt Sg ⟨sa, sb, false⟩ rfl hLhs hRhs]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .lhsOperand
      · subst hk; simp [Function.update, hLhs]
      · by_cases hk2 : k = Kg.scratch .rhsOperand
        · subst hk2; simp [Function.update, hRhs]
        · by_cases hk3 : k = Kg.scratch .sumScratch
          · subst hk3; simp [Function.update]
          · simp [Function.update, hk, hk2, hk3]
  | case2 srcA srcB carry hbase dc ih =>
      have hunfold : addRaw srcA srcB carry = dc.1 :: addRaw srcA.tail srcB.tail dc.2 := by
        rw [addRaw]; simp [hbase, dc]
      rw [hunfold, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Function.iterate_succ_apply]
      show (flipBindAdd rd rs rt)^[_]
          (flipBindAdd rd rs rt (some (⟨some AddPhase.addLoop, ⟨sa, sb, carry⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) AddPhase AddState))) = _
      set Sg1 := Function.update
          (Function.update (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
            (Kg.scratch .rhsOperand) srcB.tail)
          (Kg.scratch .sumScratch) (dc.1 :: Sg (Kg.scratch .sumScratch)) with hSg1
      have hstep : flipBindAdd rd rs rt
          (some (⟨some AddPhase.addLoop, ⟨sa, sb, carry⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) AddPhase AddState))
          = some ⟨some AddPhase.addLoop, ⟨srcA.head?, srcB.head?, dc.2⟩, Sg1⟩ := by
        show (Turing.TM2.step (addProg rd rs rt))
            (⟨some AddPhase.addLoop, ⟨sa, sb, carry⟩, Sg⟩ :
              Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
        exact addLoop_step_general rd rs rt Sg srcA srcB ⟨sa, sb, carry⟩ hLhs hRhs hbase
      rw [hstep]
      have hLhs' : Sg1 (Kg.scratch .lhsOperand) = srcA.tail := by rw [hSg1]; simp [Function.update]
      have hRhs' : Sg1 (Kg.scratch .rhsOperand) = srcB.tail := by rw [hSg1]; simp [Function.update]
      rw [ih Sg1 srcA.head? srcB.head? hLhs' hRhs']
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .lhsOperand
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .rhsOperand
        · subst hk2; simp [Function.update]
        · by_cases hk3 : k = Kg.scratch .sumScratch
          · subst hk3; simp [Function.update, hSg1]
          · simp [Function.update, hk, hk2, hk3, hSg1]

/-! ## `reverseSum`: flipping `sumScratch` back onto the now-empty `rd` -/

lemma flipBindAdd_reverseSum_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState) (hSum : Sg (Kg.scratch .sumScratch) = d :: rest) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseSum, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.reverseSum, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .sumScratch) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseSum, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSum]

lemma flipBindAdd_reverseSum_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSum : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    flipBindAdd rd rs rt
        (some (⟨some AddPhase.reverseSum, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.done, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (addProg rd rs rt))
      (⟨some AddPhase.reverseSum, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) AddPhase AddState) = _
  simp [addProg, hSum]

/-- Draining `sumScratch`, prepending its reverse onto register `rd` — since `sumScratch` is the
    MSB-first sum (`addLoop_run`), this restores the LSB-first convention `rd` needs. -/
lemma reverseSum_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : AddState)
    (hSum : Sg (Kg.scratch .sumScratch) = src) :
    (flipBindAdd rd rs rt)^[src.length + 1]
        (some (⟨some AddPhase.reverseSum, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.done, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .sumScratch) [])
            (Kg.reg rd) (src.reverse ++ Sg (Kg.reg rd))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .sumScratch) [])
          (Kg.reg rd) (Sg (Kg.reg rd)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .sumScratch
        · subst hk; simp [Function.update, hSum]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindAdd_reverseSum_nil_exit rd rs rt Sg v0 hSum
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindAdd_reverseSum_cons rd rs rt d src' Sg v0 hSum,
        ih (Function.update (Function.update Sg (Kg.scratch .sumScratch) src')
              (Kg.reg rd) (d :: Sg (Kg.reg rd))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .sumScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rd
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-! ## `realize_add`: composing all seven phases -/

/-- `copyLhs`, `copyLhsRestore` and `reverseLhs` chained: `rs`'s digits end up on `lhsOperand`
    with `rs` itself restored and `workRev` empty again. -/
lemma realize_add_bounded_copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = src) (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit)) :
    (flipBindAdd rd rs rt)^[3 * src.length + 3]
        (some (⟨some AddPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.copyRhs, ⟨none, none, false⟩,
          Function.update Sg (Kg.scratch .lhsOperand) src⟩ := by
  have hcount : 3 * src.length + 3 = (src.reverse.length + 1) + (2 * src.length + 2) := by
    rw [List.length_reverse]; omega
  have hWr : (Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .workRev) = src.reverse := by simp [hWorkRev]
  rw [hcount, Function.iterate_add_apply,
    copyLhs_phase rd rs rt src Sg ⟨none, none, false⟩ hRs hCopyScratch,
    reverseLhs_loop rd rs rt src.reverse _ ⟨none, none, false⟩ hWr]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.scratch .lhsOperand
  · subst hk; simp [Function.update, hLhs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWorkRev]
    · simp [Function.update, hk, hk2]

/-- `copyRhs`, `copyRhsRestore` and `reverseRhs` chained: `rt`'s digits end up on `rhsOperand`
    with `rt` itself restored and `workRev` empty again. -/
lemma realize_add_bounded_copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRt : Sg (Kg.reg rt) = src) (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindAdd rd rs rt)^[3 * src.length + 3]
        (some (⟨some AddPhase.copyRhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.clearDest, ⟨none, none, false⟩,
          Function.update Sg (Kg.scratch .rhsOperand) src⟩ := by
  have hcount : 3 * src.length + 3 = (src.reverse.length + 1) + (2 * src.length + 2) := by
    rw [List.length_reverse]; omega
  have hWr : (Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .workRev) = src.reverse := by simp [hWorkRev]
  rw [hcount, Function.iterate_add_apply,
    copyRhs_phase rd rs rt src Sg ⟨none, none, false⟩ hRt hCopyScratch,
    reverseRhs_loop rd rs rt src.reverse _ ⟨none, none, false⟩ hWr]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.scratch .rhsOperand
  · subst hk; simp [Function.update, hRhs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWorkRev]
    · simp [Function.update, hk, hk2]

/-- The whole non-destructive snapshot prefix of `add`, from `copyLhs` through `clearDest`: both
    operands are captured and `rd` is emptied, with step count
    `(Sg (Kg.reg rd)).length + 1 + (3 * B.length + 3) + (3 * A.length + 3)`. -/
lemma realize_add_bounded_prefix (A B : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = A) (hRt : Sg (Kg.reg rt) = B)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindAdd rd rs rt)^[((Sg (Kg.reg rd)).length + 1)
        + ((3 * B.length + 3) + (3 * A.length + 3))]
        (some (⟨some AddPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.addLoop, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
              (Kg.scratch .rhsOperand) B) (Kg.reg rd) []⟩ := by
  have hrun1 := realize_add_bounded_copyLhs_phase rd rs rt A Sg hRs hWorkRev hCopyScratch hLhs
  have hrun2 := realize_add_bounded_copyRhs_phase rd rs rt B
    (Function.update Sg (Kg.scratch .lhsOperand) A) (by simpa using hRt) (by simpa using hWorkRev)
    (by simpa using hCopyScratch) (by simpa using hRhs)
  have hlen : ((Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
      (Kg.scratch .rhsOperand) B) (Kg.reg rd)).length = (Sg (Kg.reg rd)).length := by simp
  have hrun3 := add_clearDest_loop rd rs rt _
    (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A) (Kg.scratch .rhsOperand) B)
    ⟨none, none, false⟩ rfl
  rw [hlen] at hrun3
  rw [Function.iterate_add_apply (flipBindAdd rd rs rt) ((Sg (Kg.reg rd)).length + 1)
      ((3 * B.length + 3) + (3 * A.length + 3)),
    Function.iterate_add_apply (flipBindAdd rd rs rt) (3 * B.length + 3) (3 * A.length + 3),
    hrun1, hrun2, hrun3]

/-- `addLoop` then `reverseSum`: the ripple-carry sum of the two operands lands on the (empty) `rd`
    as `natToDigits (rsVal + rtVal)`, leaving both operands and `sumScratch` empty. -/
lemma realize_add_bounded_tail (rsVal rtVal : ℕ) (S : ∀ k, List (Γg p k))
    (hLhs : S (Kg.scratch .lhsOperand) = natToDigits rsVal)
    (hRhs : S (Kg.scratch .rhsOperand) = natToDigits rtVal)
    (hSum : S (Kg.scratch .sumScratch) = ([] : List Digit))
    (hRd : S (Kg.reg rd) = ([] : List Digit)) :
    (flipBindAdd rd rs rt)^[((addRaw (natToDigits rsVal) (natToDigits rtVal) false).length + 1)
        + ((addRaw (natToDigits rsVal) (natToDigits rtVal) false).length + 1)]
        (some (⟨some AddPhase.addLoop, ⟨none, none, false⟩, S⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.done, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update (Function.update S (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) [])
            (Kg.reg rd) (natToDigits (rsVal + rtVal))⟩ := by
  have hloop := addLoop_run rd rs rt S (natToDigits rsVal) (natToDigits rtVal) false none none hLhs hRhs
  have hrev := reverseSum_loop rd rs rt
    (addRaw (natToDigits rsVal) (natToDigits rtVal) false).reverse
    (Function.update (Function.update (Function.update S (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch)
      ((addRaw (natToDigits rsVal) (natToDigits rtVal) false).reverse ++ S (Kg.scratch .sumScratch)))
    ⟨none, none, false⟩ (by simp [Function.update, hSum])
  rw [List.length_reverse] at hrev
  rw [Function.iterate_add_apply, hloop, hrev]
  simp [Function.update, hRd, addRaw_natToDigits]


/-- All scratch stacks the prefix and tail touch are back to their initial (empty) contents, so
    only the `rd` update remains. -/
lemma realize_add_bounded_final_stack (Sg : ∀ k, List (Γg p k)) (A B R : List Digit)
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit))
    (hSum : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
        (Kg.scratch .rhsOperand) B) (Kg.reg rd) [])
      (Kg.scratch .lhsOperand) []) (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) [])
      (Kg.reg rd) R
      = Function.update Sg (Kg.reg rd) R := by
  rw [Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .rhsOperand by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .sumScratch by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .rhsOperand : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_idem, Function.update_idem,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .lhsOperand)).2 hLhs.symm,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .rhsOperand)).2 hRhs.symm,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .sumScratch)).2 hSum.symm]

/-- Bound on the witness step count of `realize_add_bounded`: the raw sum has at most
    `bitLen rsVal + bitLen rtVal` digits. -/
lemma realize_add_bounded_count (rsVal rtVal : ℕ) :
    (addRaw (natToDigits rsVal) (natToDigits rtVal) false).length
      ≤ bitLen rsVal + bitLen rtVal := by
  rw [addRaw_natToDigits]
  calc (natToDigits (rsVal + rtVal)).length ≤ bitLen (rsVal + rtVal) :=
        natToDigits_length_le_bitLen _
    _ ≤ bitLen rsVal + bitLen rtVal := bitLen_add_le _ _

/-- Quantitative companion to `realize_add`: same statement, plus a bound on the witness step
    count. Unlike `load`'s `scan_phase`, `add`'s phases are a straight-line chain (no induction),
    so the bound is a direct arithmetic consequence of the already-closed-form step counts;
    `addRaw_natToDigits` + `natToDigits_length_le_bitLen` + `bitLen_add_le` bound the sum's own
    digit length by `bitLen rsVal + bitLen rtVal`, which matches `add`'s `instructionCost`
    verbatim at the `add_impl_growing_bounded` call site. -/
lemma realize_add_bounded (rsVal rtVal : ℕ) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = natToDigits rsVal) (hRt : Sg (Kg.reg rt) = natToDigits rtVal)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = ([] : List Digit))
    (hSumScratch : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    ∃ n, (flipBindAdd rd rs rt)^[n]
        (some (⟨some AddPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.done, ⟨none, none, false⟩,
          Function.update Sg (Kg.reg rd) (natToDigits (rsVal + rtVal))⟩ ∧
        n ≤ 16 * ((Sg (Kg.reg rd)).length + (natToDigits rsVal).length
          + (natToDigits rtVal).length + bitLen rsVal + bitLen rtVal + 1) := by
  have hpre := realize_add_bounded_prefix rd rs rt (natToDigits rsVal) (natToDigits rtVal) Sg
    hRs hRt hWorkRev hCopyScratch hLhsOperand hRhsOperand
  have htail := realize_add_bounded_tail rd rs rt rsVal rtVal
    (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand)
      (natToDigits rsVal)) (Kg.scratch .rhsOperand) (natToDigits rtVal)) (Kg.reg rd) [])
    (by simp) (by simp) (by simpa [Function.update] using hSumScratch) (by simp)
  have hL := realize_add_bounded_count rsVal rtVal
  refine ⟨((addRaw (natToDigits rsVal) (natToDigits rtVal) false).length + 1)
      + ((addRaw (natToDigits rsVal) (natToDigits rtVal) false).length + 1)
      + (((Sg (Kg.reg rd)).length + 1)
        + ((3 * (natToDigits rtVal).length + 3) + (3 * (natToDigits rsVal).length + 3))), ?_, ?_⟩
  · rw [Function.iterate_add_apply, hpre, htail,
      realize_add_bounded_final_stack rd Sg _ _ _ hLhsOperand hRhsOperand hSumScratch]
  · omega

/-- The generalized `add` instruction, realized against an arbitrary site's register triple
    (`rd`/`rs`/`rt`, any alias pattern): starting with `rs`/`rt` holding `natToDigits rsVal`/
    `natToDigits rtVal` and every scratch stack empty, running `addProg` from `copyLhs` reaches
    `done` with `rd` set to `natToDigits (rsVal + rtVal)` and every other register and
    scratch stack unchanged. If `rd` aliases a source, the destination write replaces it too,
    matching `BitCostRAM.step` for `add rd rs rt` (`regs rd := regs rs + regs rt`).
    Existential step count (unlike `realize_store`) since `rd`'s pre-existing content — unlike
    `rs`/`rt`'s — is unconstrained (`add` overwrites it regardless), matching
    `GenericLoad.realize_load`'s precedent for the same reason. -/
lemma realize_add (rsVal rtVal : ℕ) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = natToDigits rsVal) (hRt : Sg (Kg.reg rt) = natToDigits rtVal)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = ([] : List Digit))
    (hSumScratch : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    ∃ n, (flipBindAdd rd rs rt)^[n]
        (some (⟨some AddPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) AddPhase AddState))
      = some ⟨some AddPhase.done, ⟨none, none, false⟩,
          Function.update Sg (Kg.reg rd) (natToDigits (rsVal + rtVal))⟩ := by
  obtain ⟨n, hrun, -⟩ := realize_add_bounded rd rs rt rsVal rtVal Sg hRs hRt hWorkRev hCopyScratch
    hLhsOperand hRhsOperand hSumScratch
  exact ⟨n, hrun⟩

/-! ## Site dispatcher package

Mirrors `GenericStore.lean`'s `storeCode`/`store_impl_growingBoundedSiteStepSim` pattern: `addCode` casts the
whole local `AddPhase`-indexed function once via `cast_apply_phaseOf`, and
`add_impl_growing_bounded` transports `realize_add`'s local run into the global machine via
`iterate_bind_step_liftStmt` followed by one bridge step. -/

/-- `add`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `addProg` lifted via `execVia`. -/
def addCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt) : AddPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = AddPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getAdd AllInstrState.setAdd
        (addProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `addCodeBody`, cast once from `AddPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def addCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (addCodeBody p pc rd rs rt h)

/-- `addCode` undoes its own cast when applied to a correspondingly-cast `AddPhase` value. -/
lemma addCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt) (l : AddPhase) :
    addCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l) = addCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (addCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `addCode` at site `pc` installs the lifted `addProg` tree at
    every non-`done` label. -/
lemma addCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (addCode p pc rd rs rt h) M) :
    ∀ l : AddPhase, l ≠ AddPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getAdd AllInstrState.setAdd
        (addProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    addCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `addCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `add`'s own `done` label. -/
lemma addCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (addCode p pc rd rs rt h) M) :
    M (execVia p pc h AddPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) AddPhase.done)
  rw [show execVia p pc h AddPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) AddPhase.done) from rfl, hone,
    addCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- An `add` step only rewrites register `rd`. -/
lemma add_impl_growing_bounded_step_regs (rd rs rt : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.add rd rs rt) :
    (step r).regs = bankWrite r.regs rd (r.regs rs + r.regs rt) := by
  simp [step, hcurEq]

/-- The current instruction is `add` at the site's program counter. -/
lemma add_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .add rd rs rt) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.add rd rs rt := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `copyLhs` entry. -/
lemma add_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .add rd rs rt)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h AddPhase.copyLhs) := by
  have hstart : startPhaseOpt (Instruction.add rd rs rt) = some AddPhase.copyLhs := rfl
  have hentry : entryAt p pc.1 = execVia p pc h AddPhase.copyLhs :=
    entryAt_eq_execVia p pc h AddPhase.copyLhs hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `add` site run on the global machine: the `addProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (only `rd'`
    rewritten) and a step count bound. -/
lemma add_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .add rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (addCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h AddPhase.copyLhs))
    (rd' rs' rt' : Fin (regBound p))
    (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (hrs' : rs' = regAt p pc rs (by rw [h]; simp [regsOf]))
    (hrt' : rt' = regAt p pc rt (by rw [h]; simp [regsOf])) (a b : ℕ)
    (hRs : cfg.stk (Kg.reg rs') = natToDigits a) (hRt : cfg.stk (Kg.reg rt') = natToDigits b)
    (hWorkRev : cfg.stk (Kg.scratch ScratchKind.workRev) = [])
    (hCopyScratch : cfg.stk (Kg.scratch ScratchKind.copyScratch) = [])
    (hLhs : cfg.stk (Kg.scratch ScratchKind.lhsOperand) = [])
    (hRhs : cfg.stk (Kg.scratch ScratchKind.rhsOperand) = [])
    (hSum : cfg.stk (Kg.scratch ScratchKind.sumScratch) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ 16 * ((cfg.stk (Kg.reg rd')).length + (natToDigits a).length + (natToDigits b).length
        + bitLen a + bitLen b + 1) + 1 ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits (a + b)) := by
  have hag := addCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd', ← hrs', ← hrt'] at hag
  obtain ⟨N, hAddRun, hNbound⟩ := realize_add_bounded rd' rs' rt' a b cfg.stk
    hRs hRt hWorkRev hCopyScratch hLhs hRhs hSum
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getAdd AllInstrState.setAdd (addProg rd' rs' rt') M
      Function.injective_id AllInstrState.getAdd_setAdd AllInstrState.setAdd_setAdd
      AllInstrState.setAdd_getAdd N AddPhase.copyLhs (⟨none, none, false⟩ : AddState)
      cfg.stk AllInstrState.canonical cfg.stk rfl hstkTriv
      AddPhase.done (⟨none, none, false⟩ : AddState)
      (Function.update cfg.stk (Kg.reg rd') (natToDigits (a + b))) rfl hag hAddRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h AddPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h AddPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h AddPhase.done)) sf Sgf) from rfl,
      addCode_agrees_done p pc rd rs rt h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h AddPhase.copyLhs), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨N + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of an `add` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma add_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs rt : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.add rd rs rt)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') (natToDigits (r.regs rs + r.regs rt))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rd') _ _⟩
  rw [add_impl_growing_bounded_step_regs rd rs rt r hcurEq]
  by_cases hi : i = rd'
  · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
  · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
    exact hregs i

/-- The configuration reached after an `add` run represents the stepped RAM, given the register
    frame and the untouched non-register stacks. -/
lemma add_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.add rd rs rt)
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

/-- Step-count bound: the run's cost is at most `64` times the squared potential, since each of
    the three operand lengths is bounded by `regSize` and the `bitLen`s by the instruction cost. -/
lemma add_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rd rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt)
    (hcurEq : r.current = Instruction.add rd rs rt)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) (n : ℕ)
    (hn : n ≤ 16 * ((cfg.stk (Kg.reg rd')).length + (natToDigits (r.regs rs)).length
      + (natToDigits (r.regs rt)).length + bitLen (r.regs rs) + bitLen (r.regs rt) + 1) + 1) :
    n ≤ 64 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle1 : (cfg.stk (Kg.reg rd')).length ≤ regSize p r := by
    rw [hregs rd']; exact natToDigits_length_le_regSize p r rd'
  have hle2 := natToDigits_length_le_regSize p r rs'
  have hle3 := natToDigits_length_le_regSize p r rt'
  rw [hrsval] at hle2
  rw [hrtval] at hle3
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rs) + bitLen (r.regs rt) + 1 := by rw [hcurEq]; rfl
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  omega

/-- Potential growth: only `rd` changes, to at most `bitLen (rs + rt) ≤ bitLen rs + bitLen rt`
    digits, and the memory stack is untouched. -/
lemma add_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs rt : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.add rd rs rt) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := add_impl_growing_bounded_step_regs rd rs rt r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits (r.regs rs + r.regs rt)).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' (r.regs rs + r.regs rt) _ le_rfl
  have hle : (natToDigits (r.regs rs + r.regs rt)).length ≤ bitLen (r.regs rs) + bitLen (r.regs rt) :=
    le_trans (natToDigits_length_le_bitLen _) (bitLen_add_le _ _)
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rs) + bitLen (r.regs rt) + 1 := by rw [hcurEq]; rfl
  rw [hother _ (by simp)]
  omega

/-- `mem` is untouched, and the only register that can grow is
    `rd`, to `bitLen (regs rs + regs rt) ≤ bitLen (regs rs) + bitLen (regs rt)`
    (`bitLen_add_le`) — exactly `add`'s own `instructionCost` minus its `+1`. -/
lemma add_impl_growing_bounded (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt) :
    GrowingBoundedSiteStepSim p pc (addCode p pc rd rs rt h) 64 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := add_impl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := add_impl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rt', hrt'⟩ : ∃ x, x = regAt p pc rt (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hrtval : rt'.1 = rt := by rw [hrt']; rfl
  have hRs : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  have hRt : cfg.stk (Kg.reg rt') = natToDigits (r.regs rt) := by rw [hregs rt', hrtval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := add_impl_growing_bounded_run p pc rd rs rt h M hAgrees
    cfg hvar hcl rd' rs' rt' hrd' hrs' hrt' _ _ hRs hRt (hscratch .workRev) (hscratch .copyScratch)
    (hscratch .lhsOperand) (hscratch .rhsOperand) (hscratch .sumScratch)
  obtain ⟨hreg, hother⟩ := add_impl_growing_bounded_stk cfg.stk r rd rs rt rd' hrdval hcurEq hregs
    Sgf hSgf
  exact ⟨n, _, hrun,
    add_impl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    add_impl_growing_bounded_time p cfg r rd rs rt rd' rs' rt' hrsval hrtval hcurEq hregs n hn,
    add_impl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩

/-- `add`'s `GrowingTimedInstrImpl` package. -/
def addGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .add rd rs rt) : GrowingTimedInstrImpl p pc where
  code := addCode p pc rd rs rt h
  C := 64
  G := 1
  growingSim := add_impl_growing_bounded p pc rd rs rt h

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `move` realized against an arbitrary site's register pair

`move rd rs` must remain correct when `rd = rs`. It snapshots `rs` in `workRev` through
`copySrc`/`copySrcRestore` before draining `rd` with `clearDest`. If the registers alias, `rs` has
already been restored when `rd` is drained, while `workRev` retains an independent copy;
`reverseCopy` then rebuilds `rd` from that snapshot. No case split on `rd = rs` is needed in
`moveProg` or its `realize_move` proof, and the final update formula works in either case.

Proof style: as in `GenericStore.lean`/`GenericAdd.lean`, configs are tracked as a raw
`Sg : ∀ k, List (Γg p k)`; `Function.update` chains are equated via `funext` + `by_cases` on each
relevant key.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits liftStmt iterate_bind_step_liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs : Fin (regBound p))

/-- `move`'s `Stmt` tree at an arbitrary register pair: non-destructively snapshot `rs` into
    `workRev` (`copySrc`/`copySrcRestore`), drain `rd` (`clearDest`), then reverse `workRev` back
    onto `rd` (`reverseCopy`) — no separate `lhsOperand`-style relay scratch is needed since there
    is only one operand to rebuild. -/
def moveProg : MovePhase → Turing.TM2.Stmt (Γg p) MovePhase (Option Digit)
  | .copySrc =>
      pop (Kg.reg rs) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push (Kg.scratch .workRev) (fun s => s.getD default)
            (push (Kg.scratch .copyScratch) (fun s => s.getD default)
              (goto (fun _ => .copySrc))))
          (goto (fun _ => .copySrcRestore)))
  | .copySrcRestore =>
      pop (Kg.scratch .copyScratch) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push (Kg.reg rs) (fun s => s.getD default) (goto (fun _ => .copySrcRestore)))
          (goto (fun _ => .clearDest)))
  | .clearDest =>
      pop (Kg.reg rd) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .reverseCopy)))
  | .reverseCopy =>
      pop (Kg.scratch .workRev) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (push (Kg.reg rd) (fun s => s.getD default) (goto (fun _ => .reverseCopy)))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindMove :
    Option (Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) →
      Option (Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) :=
  fun x => x.bind (Turing.TM2.step (moveProg rd rs))

/-! ## `copySrc` / `copySrcRestore`: non-destructively snapshotting `rs` -/

lemma flipBindMove_copySrc_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRs : Sg (Kg.reg rs) = d :: rest) :
    flipBindMove rd rs
        (some (⟨some MovePhase.copySrc, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.copySrc, some d,
          Function.update (Function.update (Function.update Sg (Kg.reg rs) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.copySrc, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hRs]

lemma flipBindMove_copySrc_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRs : Sg (Kg.reg rs) = ([] : List Digit)) :
    flipBindMove rd rs
        (some (⟨some MovePhase.copySrc, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.copySrcRestore, none, Sg⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.copySrc, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hRs]

/-- Draining register `rs`, prepending its reverse onto both `workRev` and `copyScratch`. -/
lemma copySrc_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hRs : Sg (Kg.reg rs) = src) :
    (flipBindMove rd rs)^[src.length + 1]
        (some (⟨some MovePhase.copySrc, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.copySrcRestore, none,
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
      exact flipBindMove_copySrc_nil_exit rd rs Sg v0 hRs
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMove_copySrc_cons rd rs d src' Sg v0 hRs,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rs) src')
              (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
              (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
           (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rs
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .workRev
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.scratch .copyScratch
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindMove_copySrcRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindMove rd rs
        (some (⟨some MovePhase.copySrcRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.copySrcRestore, some d,
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rs) (d :: Sg (Kg.reg rs))⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.copySrcRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hSc]

lemma flipBindMove_copySrcRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindMove rd rs
        (some (⟨some MovePhase.copySrcRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.clearDest, none, Sg⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.copySrcRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hSc]

/-- Draining `copyScratch` restores register `rs` to `copyScratch.reverse ++ src`. -/
lemma copySrcRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindMove rd rs)^[copyScratch.length + 1]
        (some (⟨some MovePhase.copySrcRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.clearDest, none,
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
      exact flipBindMove_copySrcRestore_nil_exit rd rs Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMove_copySrcRestore_cons rd rs d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rs) (d :: Sg (Kg.reg rs))) (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rs
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the `rs` copy to completion: register `rs` is restored exactly, and its reverse is
    prepended onto `workRev`. -/
lemma copySrc_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hRs : Sg (Kg.reg rs) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindMove rd rs)^[2 * src.length + 2]
        (some (⟨some MovePhase.copySrc, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.clearDest, none,
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, copySrc_loop rd rs src Sg v0 hRs]
  simp only [hSc, List.append_nil]
  have h2 := copySrcRestore_loop rd rs src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rs) [])
      (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .copyScratch) src.reverse) none (by simp)
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

/-! ## `clearDest`: draining whatever `rd` currently holds -/

lemma flipBindMove_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindMove rd rs
        (some (⟨some MovePhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.clearDest, some d, Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hRd]

lemma flipBindMove_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindMove rd rs
        (some (⟨some MovePhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.reverseCopy, none, Sg⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hRd]

/-- Draining register `rd`, discarding its content (no scratch relay needed: no later phase
    reads `rd`'s *old* value). -/
lemma move_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindMove rd rs)^[dest.length + 1]
        (some (⟨some MovePhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.reverseCopy, none, Function.update Sg (Kg.reg rd) []⟩ := by
  induction dest generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.reg rd) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rd
        · subst hk; simp [Function.update, hRd]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindMove_clearDest_nil_exit rd rs Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMove_clearDest_cons rd rs d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `reverseCopy`: flipping `workRev` back to LSB-first order onto `rd` -/

lemma flipBindMove_reverseCopy_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindMove rd rs
        (some (⟨some MovePhase.reverseCopy, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.reverseCopy, some d,
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.reverseCopy, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hWr]

lemma flipBindMove_reverseCopy_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindMove rd rs
        (some (⟨some MovePhase.reverseCopy, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.done, none, Sg⟩ := by
  show (Turing.TM2.step (moveProg rd rs))
      (⟨some MovePhase.reverseCopy, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)) = _
  simp [moveProg, hWr]

/-- Draining `workRev`, prepending its reverse onto `rd` — since `workRev` holds `rs`'s original
    digits reversed (`copySrc_phase`), this rebuilds the original LSB-first `rs` value onto `rd`. -/
lemma reverseCopy_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindMove rd rs)^[src.length + 1]
        (some (⟨some MovePhase.reverseCopy, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.done, none,
          Function.update (Function.update Sg (Kg.scratch .workRev) [])
            (Kg.reg rd) (src.reverse ++ Sg (Kg.reg rd))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .workRev) [])
          (Kg.reg rd) (Sg (Kg.reg rd)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .workRev
        · subst hk; simp [Function.update, hWr]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindMove_reverseCopy_nil_exit rd rs Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMove_reverseCopy_cons rd rs d src' Sg v0 hWr,
        ih (Function.update (Function.update Sg (Kg.scratch .workRev) src')
              (Kg.reg rd) (d :: Sg (Kg.reg rd))) (some d) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .workRev
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rd
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-! ## Assembling `realize_move` -/

/-- The whole `move` run: `rs` ends unchanged, `rd` ends holding `rs`'s original value — correct
    as a single formula even when `rd = rs` (a `Function.update` at the same key the snapshot
    already restored is simply a no-op-equivalent overwrite with the same content). -/
lemma realize_move (srcVal : ℕ) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = natToDigits srcVal)
    (hSc : Sg (Kg.scratch .copyScratch) = []) (hWr0 : Sg (Kg.scratch .workRev) = []) :
    (flipBindMove rd rs)^[((natToDigits srcVal).length + 1)
        + (((Sg (Kg.reg rd)).length + 1) + (2 * (natToDigits srcVal).length + 2))]
        (some (⟨some MovePhase.copySrc, none, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = some ⟨some MovePhase.done, none,
          Function.update Sg (Kg.reg rd) (natToDigits srcVal)⟩ := by
  rw [Function.iterate_add_apply,
    show (flipBindMove rd rs)^[((Sg (Kg.reg rd)).length + 1) + (2 * (natToDigits srcVal).length + 2)]
        (some (⟨some MovePhase.copySrc, none, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
      = (flipBindMove rd rs)^[(Sg (Kg.reg rd)).length + 1]
          ((flipBindMove rd rs)^[2 * (natToDigits srcVal).length + 2]
            (some (⟨some MovePhase.copySrc, none, Sg⟩ :
              Turing.TM2.Cfg (Γg p) MovePhase (Option Digit))))
      from Function.iterate_add_apply _ _ _ _,
    copySrc_phase rd rs (natToDigits srcVal) Sg none hRs hSc]
  set Sg1 := Function.update Sg (Kg.scratch .workRev)
      ((natToDigits srcVal).reverse ++ Sg (Kg.scratch .workRev)) with hSg1
  have hRd1 : Sg1 (Kg.reg rd) = Sg (Kg.reg rd) := by
    rw [hSg1, Function.update_of_ne (by simp)]
  rw [move_clearDest_loop rd rs (Sg (Kg.reg rd)) Sg1 none hRd1]
  set Sg2 := Function.update Sg1 (Kg.reg rd) ([] : List Digit) with hSg2
  have hWr2 : Sg2 (Kg.scratch .workRev) = (natToDigits srcVal).reverse := by
    rw [hSg2, Function.update_of_ne (by simp), hSg1, Function.update_self, hWr0, List.append_nil]
  have hRd2 : Sg2 (Kg.reg rd) = [] := by rw [hSg2, Function.update_self]
  rw [show (natToDigits srcVal).length = (natToDigits srcVal).reverse.length from
        List.length_reverse.symm,
    reverseCopy_loop rd rs ((natToDigits srcVal).reverse) Sg2 none hWr2]
  simp only [List.reverse_reverse, hRd2, List.append_nil, Option.some.injEq,
    Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.reg rd
  · subst hk; simp [Function.update]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWr0]
    · simp [Function.update, hk, hk2, hSg2, hSg1]

/-! ## Site dispatcher package -/

/-- `move`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `moveProg` lifted via `execVia`. -/
def moveCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs) : MovePhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = MovePhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getMove AllInstrState.setMove
        (moveProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) l)

/-- `moveCodeBody`, cast once from `MovePhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def moveCode (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (moveCodeBody p pc rd rs h)

/-- `moveCode` undoes its own cast when applied to a correspondingly-cast `MovePhase` value. -/
lemma moveCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs) (l : MovePhase) :
    moveCode p pc rd rs h (cast (congrArg PhaseOf h.symm) l) = moveCodeBody p pc rd rs h l :=
  cast_apply_phaseOf p pc h (moveCodeBody p pc rd rs h) l

/-- Any dispatcher agreeing with `moveCode` at site `pc` installs the lifted `moveProg` tree at
    every non-`done` label. -/
lemma moveCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (moveCode p pc rd rs h) M) :
    ∀ l : MovePhase, l ≠ MovePhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getMove AllInstrState.setMove
        (moveProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    moveCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `moveCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `move`'s own `done` label. -/
lemma moveCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (moveCode p pc rd rs h) M) :
    M (execVia p pc h MovePhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) MovePhase.done)
  rw [show execVia p pc h MovePhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) MovePhase.done) from rfl, hone,
    moveCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- A `move` step only rewrites register `rd`, to `rs`'s value. -/
lemma move_impl_growing_bounded_step_regs (rd rs : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.move rd rs) :
    (step r).regs = bankWrite r.regs rd (r.regs rs) := by
  simp [step, hcurEq]

/-- The current instruction is `move` at the site's program counter. -/
lemma move_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs : ℕ) (h : p.get pc = .move rd rs) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.move rd rs := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `copySrc`
    entry. -/
lemma move_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs : ℕ) (h : p.get pc = .move rd rs)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h MovePhase.copySrc) := by
  have hstart : startPhaseOpt (Instruction.move rd rs) = some MovePhase.copySrc := rfl
  have hentry : entryAt p pc.1 = execVia p pc h MovePhase.copySrc :=
    entryAt_eq_execVia p pc h MovePhase.copySrc hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `move` site run on the global machine: the `moveProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (only `rd'`
    rewritten) and a step count bound. -/
lemma move_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs : ℕ) (h : p.get pc = .move rd rs)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (moveCode p pc rd rs h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h MovePhase.copySrc))
    (rd' rs' : Fin (regBound p))
    (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (hrs' : rs' = regAt p pc rs (by rw [h]; simp [regsOf])) (a : ℕ)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i))
    (hRs : cfg.stk (Kg.reg rs') = natToDigits a)
    (hCopyEmpty : cfg.stk (Kg.scratch ScratchKind.copyScratch) = [])
    (hWorkRevEmpty : cfg.stk (Kg.scratch ScratchKind.workRev) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ ((natToDigits a).length + 1) +
        ((cfg.stk (Kg.reg rd')).length + 1 + (2 * (natToDigits a).length + 2)) + 1 ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits a) := by
  have hag := moveCode_agrees_ne_done p pc rd rs h M hAgrees
  rw [← hrd', ← hrs'] at hag
  have hMoveRun : (flipBindMove rd' rs')^[((natToDigits a).length + 1)
      + (((cfg.stk (Kg.reg rd')).length + 1) + (2 * (natToDigits a).length + 2))]
      (some (⟨some MovePhase.copySrc, none, cfg.stk⟩ :
        Turing.TM2.Cfg (Γg p) MovePhase (Option Digit)))
    = some ⟨some MovePhase.done, none,
        Function.update cfg.stk (Kg.reg rd') (natToDigits a)⟩ :=
    realize_move (p := p) (rd := rd') (rs := rs') a cfg.stk hRs hCopyEmpty hWorkRevEmpty
  set N := ((natToDigits a).length + 1) +
    (((cfg.stk (Kg.reg rd')).length + 1) + (2 * (natToDigits a).length + 2)) with hNdef
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getMove AllInstrState.setMove (moveProg rd' rs') M
      Function.injective_id AllInstrState.getMove_setMove AllInstrState.setMove_setMove
      AllInstrState.setMove_getMove _ MovePhase.copySrc none cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      MovePhase.done none
      (Function.update cfg.stk (Kg.reg rd') (natToDigits a))
      rfl hag hMoveRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h MovePhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h MovePhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h MovePhase.done)) sf Sgf) from rfl,
      moveCode_agrees_done p pc rd rs h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h MovePhase.copySrc), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨N + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `move` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma move_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.move rd rs)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') (natToDigits (r.regs rs))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rd') _ _⟩
  rw [move_impl_growing_bounded_step_regs rd rs r hcurEq]
  by_cases hi : i = rd'
  · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
  · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
    exact hregs i

/-- The configuration reached after a `move` run represents the stepped RAM, given the register
    frame and the untouched non-register stacks. -/
lemma move_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.move rd rs)
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

/-- Step-count bound: the run's cost is at most the squared potential, since both operand
    lengths are bounded by `regSize` and the cost is charged by `instructionCost`. -/
lemma move_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rd rs : ℕ) (rd' rs' : Fin (regBound p)) (hrsval : rs'.1 = rs)
    (hcurEq : r.current = Instruction.move rd rs)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) (n : ℕ)
    (hn : n ≤ ((natToDigits (r.regs rs)).length + 1) +
      ((cfg.stk (Kg.reg rd')).length + 1 + (2 * (natToDigits (r.regs rs)).length + 2)) + 1) :
    n ≤ 1 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle_rs : (natToDigits (r.regs rs)).length ≤ regSize p r := by
    have h0 : (natToDigits (r.regs rs')).length ≤ regSize p r :=
      natToDigits_length_le_regSize p r rs'
    rwa [show r.regs rs' = r.regs rs by rw [hrsval]] at h0
  have hle_rd : (cfg.stk (Kg.reg rd')).length ≤ regSize p r := by
    rw [hregs rd']; exact natToDigits_length_le_regSize p r rd'
  have hcostge : instructionCost r.regs r.mem r.current ≥ 2 := by
    rw [hcurEq]; simp only [instructionCost, bitLen]; omega
  nlinarith [Nat.zero_le (regSize p r), Nat.zero_le (cfg.stk Kg.mem).length]

/-- Potential growth: only `rd` changes, to `regs rs`'s digits — bounded by `instructionCost`
    since `move`'s own cost charges exactly `bitLen (regs rs) + 1`; the memory stack is
    untouched. -/
lemma move_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.move rd rs) (Sgf : ∀ k, List (Γg p k))
    (hmemEq : Sgf Kg.mem = cfg.stk Kg.mem) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq : (step r).regs = bankWrite r.regs rd (r.regs rs) :=
    move_impl_growing_bounded_step_regs rd rs r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits (r.regs rs)).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' (r.regs rs) _ le_rfl
  have hcostbound : (natToDigits (r.regs rs)).length ≤
      1 * (instructionCost r.regs r.mem r.current + 1) := by
    have hle : (natToDigits (r.regs rs)).length ≤ bitLen (r.regs rs) :=
      natToDigits_length_le_bitLen (r.regs rs)
    rw [hcurEq]; simp only [instructionCost]; omega
  rw [hmemEq]
  omega

/-- `moveCode`'s growth companion: `mem` is untouched (`hSgfMem`), and the only register that can
    grow is `rd`, to `regs rs`'s digit length — bounded by `instructionCost` since `move`'s own
    cost charges exactly `bitLen (regs rs) + 1`. -/
lemma move_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs) :
    GrowingBoundedSiteStepSim p pc (moveCode p pc rd rs h) 1 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := move_impl_growing_bounded_current p pc rd rs h r hprog hpcEq
  have hcl := move_impl_growing_bounded_label p pc rd rs h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hRsVal : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := move_impl_growing_bounded_run p pc rd rs h M hAgrees
    cfg r hvar hcl rd' rs' hrd' hrs' _ hregs hRsVal
    (hscratch .copyScratch) (hscratch .workRev)
  have hSgf' : Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits (r.regs rs)) := hSgf
  obtain ⟨hreg, hother⟩ := move_impl_growing_bounded_stk cfg.stk r rd rs rd' hrdval hcurEq
    hregs Sgf hSgf'
  exact ⟨n, _, hrun,
    move_impl_growing_bounded_represents p pc rd rs cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    move_impl_growing_bounded_time p cfg r rd rs rd' rs' (by rw [hrs']; rfl) hcurEq hregs n hn,
    move_impl_growing_bounded_growth p cfg r rd rs rd' hrdval hcurEq Sgf (hother Kg.mem (by simp))⟩

/-- `move`'s `GrowingTimedInstrImpl` package. -/
def moveGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs : ℕ)
    (h : p.get pc = .move rd rs) : GrowingTimedInstrImpl p pc where
  code := moveCode p pc rd rs h
  C := 1
  G := 1
  growingSim := move_impl_growingBoundedSiteStepSim p pc rd rs h

end NPComplete.RAMToTM.Generic

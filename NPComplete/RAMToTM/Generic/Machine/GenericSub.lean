module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.DigitSub
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `sub` realized against an arbitrary site's register triple

`sub rd rs rt`'s non-destructive snapshot prefix (`copyLhs` through `clearDest`) is verbatim
`GenericAdd.lean`'s `addProg` shape, retargeted from `AddState`/`AddPhase` to `SubState`/`SubPhase`
— both operands are captured into `lhsOperand`/`rhsOperand` (and fully restored) before `clearDest`
drains whatever `rd` currently holds, so alias safety for any `rd = rs`/`rd = rt`/`rs = rt` is free
by the exact same argument as `GenericAdd.lean`'s module docstring: no phase here ever branches on
register-index equality.

What follows `clearDest` differs from `add`'s single `addLoop`/`reverseSum` pair, because `sub`'s
RAM semantics truncates on underflow (`DigitSub.lean`'s module docstring): `subLoop` (mirroring
`addLoop`, but stopping once *both* operands are exhausted regardless of the pending borrow, per
`DigitSub.subRawFull`'s own termination discipline) leaves the raw digits on `diffScratch` plus a
final borrow bit, then branches — `drainDiff` discards the raw digits without ever touching `rd`
when the borrow is live (underflow, RAM truncates to `0`); `skipZeros`/`copyRest` trim a leading run
of zero digits (`100 - 99 = 1`; `DigitSub.dropWhile_zero_reverse_eq_natToDigits` is the pure-math
fact this pair realizes) before relocating the rest onto `rd` when it isn't.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit SubState subDigits subRawFull natToDigits
  sub_result_underflow sub_result_ge natToDigits_ne_nil_iff liftStmt iterate_bind_step_liftStmt
  subRawFull_length_le)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs rt : Fin (regBound p))

/-- `sub`'s `Stmt` tree at an arbitrary register triple. `copyLhs` through `clearDest` are
    `GenericAdd.addProg`'s corresponding phases verbatim (module docstring); `subLoop` replaces
    `addLoop` (peek-continue only while an operand remains, never on the borrow — `DigitSub`'s
    module docstring), branching on exit to `drainDiff` (borrow live) or `skipZeros` (not); `done`
    is `halt` (`StmtTransport`'s fixed-exit requirement, overridden at the site level). -/
def subProg : SubPhase → Turing.TM2.Stmt (Γg p) SubPhase SubState
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
          (load (fun _ => (⟨none, none, false⟩ : SubState)) (goto (fun _ => .clearDest))))
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .subLoop)))
  | .subLoop =>
      peek (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
        (peek (Kg.scratch .rhsOperand) (fun s ov => {s with b := ov})
          (branch (fun s => s.a.isSome || s.b.isSome)
            (pop (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
              (pop (Kg.scratch .rhsOperand) (fun s ov => {s with b := ov})
                (push (Kg.scratch .diffScratch)
                    (fun s => (subDigits (s.a.getD 0) (s.b.getD 0) s.borrow).1)
                  (load (fun s =>
                      {s with borrow := (subDigits (s.a.getD 0) (s.b.getD 0) s.borrow).2})
                    (goto (fun _ => .subLoop))))))
            (branch (fun s => s.borrow)
              (goto (fun _ => .drainDiff))
              (goto (fun _ => .skipZeros)))))
  | .drainDiff =>
      pop (Kg.scratch .diffScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .drainDiff))
          (load (fun _ => (⟨none, none, false⟩ : SubState)) (goto (fun _ => .done))))
  | .skipZeros =>
      pop (Kg.scratch .diffScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (branch (fun s => decide ((s.a.getD default).val = 0))
            (goto (fun _ => .skipZeros))
            (push (Kg.reg rd) (fun s => s.a.getD default) (goto (fun _ => .copyRest))))
          (goto (fun _ => .done)))
  | .copyRest =>
      pop (Kg.scratch .diffScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rd) (fun s => s.a.getD default)
            (goto (fun _ => .copyRest)))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindSub :
    Option (Turing.TM2.Cfg (Γg p) SubPhase SubState) →
      Option (Turing.TM2.Cfg (Γg p) SubPhase SubState) :=
  fun x => x.bind (Turing.TM2.step (subProg rd rs rt))

/-! ## `copyLhs` / `copyLhsRestore`: non-destructively snapshotting `rs` -/

lemma flipBindSub_copyLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRs : Sg (Kg.reg rs) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyLhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rs) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRs]

lemma flipBindSub_copyLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRs : Sg (Kg.reg rs) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyLhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRs]

lemma sub_copyLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hRs : Sg (Kg.reg rs) = src) :
    (flipBindSub rd rs rt)^[src.length + 1]
        (some (⟨some SubPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyLhsRestore, {v0 with a := none},
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
      exact flipBindSub_copyLhs_nil_exit rd rs rt Sg v0 hRs
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_copyLhs_cons rd rs rt d src' Sg v0 hRs,
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

lemma flipBindSub_copyLhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyLhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rs) (d :: Sg (Kg.reg rs))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hSc]

lemma flipBindSub_copyLhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseLhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hSc]

lemma sub_copyLhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindSub rd rs rt)^[copyScratch.length + 1]
        (some (⟨some SubPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseLhs, {v0 with a := none},
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
      exact flipBindSub_copyLhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_copyLhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rs) (d :: Sg (Kg.reg rs))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rs
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma sub_copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hRs : Sg (Kg.reg rs) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindSub rd rs rt)^[2 * src.length + 2]
        (some (⟨some SubPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseLhs, {v0 with a := none},
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, sub_copyLhs_loop rd rs rt src Sg v0 hRs]
  simp only [hSc, List.append_nil]
  have h2 := sub_copyLhsRestore_loop rd rs rt src.reverse
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

lemma flipBindSub_reverseLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseLhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hWr]

lemma flipBindSub_reverseLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hWr]

lemma sub_reverseLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindSub rd rs rt)^[src.length + 1]
        (some (⟨some SubPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhs, {v0 with a := none},
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
      exact flipBindSub_reverseLhs_nil_exit rd rs rt Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_reverseLhs_cons rd rs rt d src' Sg v0 hWr,
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

lemma flipBindSub_copyRhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRt : Sg (Kg.reg rt) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rt) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRt]

lemma flipBindSub_copyRhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRt]

lemma sub_copyRhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hRt : Sg (Kg.reg rt) = src) :
    (flipBindSub rd rs rt)^[src.length + 1]
        (some (⟨some SubPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhsRestore, {v0 with a := none},
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
      exact flipBindSub_copyRhs_nil_exit rd rs rt Sg v0 hRt
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_copyRhs_cons rd rs rt d src' Sg v0 hRt,
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

lemma flipBindSub_copyRhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rt) (d :: Sg (Kg.reg rt))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hSc]

lemma flipBindSub_copyRhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseRhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hSc]

lemma sub_copyRhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindSub rd rs rt)^[copyScratch.length + 1]
        (some (⟨some SubPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseRhs, {v0 with a := none},
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
      exact flipBindSub_copyRhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_copyRhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rt) (d :: Sg (Kg.reg rt))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rt
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma sub_copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hRt : Sg (Kg.reg rt) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindSub rd rs rt)^[2 * src.length + 2]
        (some (⟨some SubPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseRhs, {v0 with a := none},
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, sub_copyRhs_loop rd rs rt src Sg v0 hRt]
  simp only [hSc, List.append_nil]
  have h2 := sub_copyRhsRestore_loop rd rs rt src.reverse
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

lemma flipBindSub_reverseRhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.reverseRhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.reverseRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hWr]

lemma flipBindSub_reverseRhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.clearDest, ⟨none, none, false⟩, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.reverseRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hWr]

lemma sub_reverseRhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindSub rd rs rt)^[src.length + 1]
        (some (⟨some SubPhase.reverseRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.clearDest, ⟨none, none, false⟩,
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
      exact flipBindSub_reverseRhs_nil_exit rd rs rt Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_reverseRhs_cons rd rs rt d src' Sg v0 hWr,
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

lemma flipBindSub_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.clearDest, {v0 with a := some d},
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRd]

lemma flipBindSub_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.subLoop, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hRd]

lemma sub_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindSub rd rs rt)^[dest.length + 1]
        (some (⟨some SubPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.subLoop, {v0 with a := none},
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
      exact flipBindSub_clearDest_nil_exit rd rs rt Sg v0 hRd
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_clearDest_cons rd rs rt d ds' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) ds') {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `subLoop`: `DigitSub`'s ripple-borrow loop, retargeted to `lhsOperand`/`rhsOperand` -/

lemma subLoop_step_done (Sg : ∀ k, List (Γg p k)) (s0 : SubState)
    (hLhs : Sg (Kg.scratch .lhsOperand) = [])
    (hRhs : Sg (Kg.scratch .rhsOperand) = []) :
    (Turing.TM2.step (subProg rd rs rt))
        (⟨some SubPhase.subLoop, s0, Sg⟩ : Turing.TM2.Cfg (Γg p) SubPhase SubState)
      = some ⟨some (if s0.borrow then SubPhase.drainDiff else SubPhase.skipZeros),
          ⟨none, none, s0.borrow⟩, Sg⟩ := by
  have heq : s0 = ⟨s0.a, s0.b, s0.borrow⟩ := by cases s0; simp_all
  rw [heq]
  rcases s0.borrow with _ | _ <;> simp [subProg, hLhs, hRhs]

lemma subLoop_step_general (Sg : ∀ k, List (Γg p k)) (srcA srcB : List Digit) (s0 : SubState)
    (hLhs : Sg (Kg.scratch .lhsOperand) = srcA) (hRhs : Sg (Kg.scratch .rhsOperand) = srcB)
    (hbase : ¬ (srcA = [] ∧ srcB = [])) :
    (Turing.TM2.step (subProg rd rs rt))
        (⟨some SubPhase.subLoop, s0, Sg⟩ : Turing.TM2.Cfg (Γg p) SubPhase SubState)
      = some ⟨some SubPhase.subLoop,
          ⟨srcA.head?, srcB.head?, (subDigits (srcA.headD 0) (srcB.headD 0) s0.borrow).2⟩,
          Function.update
            (Function.update
              (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
              (Kg.scratch .rhsOperand) srcB.tail)
            (Kg.scratch .diffScratch)
            ((subDigits (srcA.headD 0) (srcB.headD 0) s0.borrow).1 ::
              Sg (Kg.scratch .diffScratch))⟩ := by
  rcases srcA with _ | ⟨da, ta⟩ <;> rcases srcB with _ | ⟨db, tb⟩ <;>
    simp only [List.headD_nil, List.headD_cons, List.head?_nil, List.head?_cons, List.tail_nil,
      List.tail_cons]
  · exact absurd ⟨rfl, rfl⟩ hbase
  · simp [subProg, hLhs, hRhs]
  · simp [subProg, hLhs, hRhs]
  · simp [subProg, hLhs, hRhs]

lemma subLoop_run (Sg : ∀ k, List (Γg p k)) (srcA srcB : List Digit) (borrow : Bool)
    (sa sb : Option Digit) (hLhs : Sg (Kg.scratch .lhsOperand) = srcA)
    (hRhs : Sg (Kg.scratch .rhsOperand) = srcB) :
    (flipBindSub rd rs rt)^[(subRawFull srcA srcB borrow).1.length + 1]
        (some (⟨some SubPhase.subLoop, ⟨sa, sb, borrow⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some (if (subRawFull srcA srcB borrow).2 then SubPhase.drainDiff
          else SubPhase.skipZeros),
          ⟨none, none, (subRawFull srcA srcB borrow).2⟩,
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) [])
            (Kg.scratch .diffScratch)
            ((subRawFull srcA srcB borrow).1.reverse ++ Sg (Kg.scratch .diffScratch))⟩ := by
  induction srcA, srcB, borrow using subRawFull.induct generalizing Sg sa sb with
  | case1 srcA srcB borrow hbase =>
      obtain ⟨hA, hB⟩ := hbase
      subst hA; subst hB
      rw [show subRawFull ([] : List Digit) [] borrow = ([], borrow) by rw [subRawFull]; simp]
      simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append]
      show (Turing.TM2.step (subProg rd rs rt))
          (⟨some SubPhase.subLoop, ⟨sa, sb, borrow⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
      rw [subLoop_step_done rd rs rt Sg ⟨sa, sb, borrow⟩ hLhs hRhs]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .lhsOperand
      · subst hk; simp [Function.update, hLhs]
      · by_cases hk2 : k = Kg.scratch .rhsOperand
        · subst hk2; simp [Function.update, hRhs]
        · by_cases hk3 : k = Kg.scratch .diffScratch
          · subst hk3; simp [Function.update]
          · simp [Function.update, hk, hk2, hk3]
  | case2 srcA srcB borrow hbase dc ih =>
      have hunfold : subRawFull srcA srcB borrow
          = (dc.1 :: (subRawFull srcA.tail srcB.tail dc.2).1,
              (subRawFull srcA.tail srcB.tail dc.2).2) := by
        rw [subRawFull]; simp [hbase, dc]
      rw [hunfold]
      dsimp only
      rw [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        Function.iterate_succ_apply]
      show (flipBindSub rd rs rt)^[_]
          (flipBindSub rd rs rt (some (⟨some SubPhase.subLoop, ⟨sa, sb, borrow⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) SubPhase SubState))) = _
      set Sg1 := Function.update
          (Function.update (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
            (Kg.scratch .rhsOperand) srcB.tail)
          (Kg.scratch .diffScratch) (dc.1 :: Sg (Kg.scratch .diffScratch)) with hSg1
      have hstep : flipBindSub rd rs rt
          (some (⟨some SubPhase.subLoop, ⟨sa, sb, borrow⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) SubPhase SubState))
          = some ⟨some SubPhase.subLoop, ⟨srcA.head?, srcB.head?, dc.2⟩, Sg1⟩ := by
        show (Turing.TM2.step (subProg rd rs rt))
            (⟨some SubPhase.subLoop, ⟨sa, sb, borrow⟩, Sg⟩ :
              Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
        exact subLoop_step_general rd rs rt Sg srcA srcB ⟨sa, sb, borrow⟩ hLhs hRhs hbase
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
        · by_cases hk3 : k = Kg.scratch .diffScratch
          · subst hk3; simp [Function.update, hSg1]
          · simp [Function.update, hk, hk2, hk3, hSg1]

/-! ## `drainDiff`: discarding `diffScratch` without touching `rd` (underflow) -/

lemma flipBindSub_drainDiff_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hDf : Sg (Kg.scratch .diffScratch) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.drainDiff, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.drainDiff, {v0 with a := some d},
          Function.update Sg (Kg.scratch .diffScratch) rest⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.drainDiff, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf]

lemma flipBindSub_drainDiff_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hDf : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.drainDiff, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.drainDiff, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf]

lemma drainDiff_loop (diff : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hDf : Sg (Kg.scratch .diffScratch) = diff) :
    (flipBindSub rd rs rt)^[diff.length + 1]
        (some (⟨some SubPhase.drainDiff, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩,
          Function.update Sg (Kg.scratch .diffScratch) []⟩ := by
  induction diff generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.scratch .diffScratch) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .diffScratch
        · subst hk; simp [Function.update, hDf]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindSub_drainDiff_nil_exit rd rs rt Sg v0 hDf
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_drainDiff_cons rd rs rt d ds' Sg v0 hDf,
        ih (Function.update Sg (Kg.scratch .diffScratch) ds') {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .diffScratch
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `skipZeros` / `copyRest`: trimming leading zero digits, then relocating to `rd` -/

lemma flipBindSub_skipZeros_zero (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hDf : Sg (Kg.scratch .diffScratch) = d :: rest)
    (hd : d.val = 0) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.skipZeros, {v0 with a := some d},
          Function.update Sg (Kg.scratch .diffScratch) rest⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf, Fin.val_eq_zero_iff.mp hd]

lemma flipBindSub_skipZeros_nonzero (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hDf : Sg (Kg.scratch .diffScratch) = d :: rest)
    (hd : d.val ≠ 0) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRest, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .diffScratch) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf, Fin.val_eq_zero_iff.not.mp hd]

lemma flipBindSub_skipZeros_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hDf : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf]

lemma flipBindSub_copyRest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState) (hDf : Sg (Kg.scratch .diffScratch) = d :: rest) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRest, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .diffScratch) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf]

lemma flipBindSub_copyRest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hDf : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    flipBindSub rd rs rt
        (some (⟨some SubPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (subProg rd rs rt))
      (⟨some SubPhase.copyRest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) SubPhase SubState) = _
  simp [subProg, hDf]

/-- Draining `diffScratch` from `copyRest`, prepending its reverse onto `rd`. Mirrors
    `GenericAdd.reverseSum_loop`. -/
lemma copyRest_loop (diff : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hDf : Sg (Kg.scratch .diffScratch) = diff) :
    (flipBindSub rd rs rt)^[diff.length + 1]
        (some (⟨some SubPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .diffScratch) [])
            (Kg.reg rd) (diff.reverse ++ Sg (Kg.reg rd))⟩ := by
  induction diff generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .diffScratch) [])
          (Kg.reg rd) (Sg (Kg.reg rd)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .diffScratch
        · subst hk; simp [Function.update, hDf]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindSub_copyRest_nil_exit rd rs rt Sg v0 hDf
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindSub_copyRest_cons rd rs rt d ds' Sg v0 hDf,
        ih (Function.update (Function.update Sg (Kg.scratch .diffScratch) ds')
              (Kg.reg rd) (d :: Sg (Kg.reg rd))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .diffScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rd
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- `skipZeros` fully run: discards a leading (most-significant-first, since `diffScratch` is
    physically MSB-first) run of zero digits, then relocates whatever remains onto `rd`
    (mirroring `copyRest_loop`, chained on after the first nonzero digit is written). Produces
    exactly `DigitSub.dropWhile_zero_reverse_eq_natToDigits`'s `dropWhile`/`reverse` shape prepended
    onto `rd`. -/
lemma skipZeros_phase (diff : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : SubState)
    (hDf : Sg (Kg.scratch .diffScratch) = diff) :
    (flipBindSub rd rs rt)^[diff.length + 1]
        (some (⟨some SubPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .diffScratch) [])
            (Kg.reg rd)
            ((diff.dropWhile (fun d => decide (d.val = 0))).reverse ++ Sg (Kg.reg rd))⟩ := by
  induction diff generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.dropWhile_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .diffScratch) [])
          (Kg.reg rd) (Sg (Kg.reg rd)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .diffScratch
        · subst hk; simp [Function.update, hDf]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindSub_skipZeros_nil_exit rd rs rt Sg v0 hDf
  | cons d ds' ih =>
      by_cases hd : d.val = 0
      · rw [List.dropWhile_cons]
        simp only [hd, decide_true, ite_true]
        rw [List.length_cons, Function.iterate_succ_apply,
          flipBindSub_skipZeros_zero rd rs rt d ds' Sg v0 hDf hd,
          ih (Function.update Sg (Kg.scratch .diffScratch) ds') {v0 with a := some d} (by simp)]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        by_cases hk : k = Kg.scratch .diffScratch
        · subst hk; simp [Function.update]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      · rw [List.dropWhile_cons]
        simp only [hd, decide_false]
        rw [List.length_cons, Function.iterate_succ_apply,
          flipBindSub_skipZeros_nonzero rd rs rt d ds' Sg v0 hDf hd]
        have h2 := copyRest_loop rd rs rt ds'
          (Function.update (Function.update Sg (Kg.scratch .diffScratch) ds')
            (Kg.reg rd) (d :: Sg (Kg.reg rd))) {v0 with a := some d} (by simp)
        rw [h2]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        by_cases hk : k = Kg.scratch .diffScratch
        · subst hk; simp [Function.update]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]

/-! ## `realize_sub_bounded`: composing all phases -/

/-- `copyLhs`, `copyLhsRestore` and `reverseLhs` chained: `rs`'s digits end up on `lhsOperand`
    with `rs` itself restored and `workRev` empty again. -/
lemma realize_sub_bounded_copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = src) (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[3 * src.length + 3]
        (some (⟨some SubPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.copyRhs, ⟨none, none, false⟩,
          Function.update Sg (Kg.scratch .lhsOperand) src⟩ := by
  have hcount : 3 * src.length + 3 = (src.reverse.length + 1) + (2 * src.length + 2) := by
    rw [List.length_reverse]; omega
  have hWr : (Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .workRev) = src.reverse := by simp [hWorkRev]
  rw [hcount, Function.iterate_add_apply,
    sub_copyLhs_phase rd rs rt src Sg ⟨none, none, false⟩ hRs hCopyScratch,
    sub_reverseLhs_loop rd rs rt src.reverse _ ⟨none, none, false⟩ hWr]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.scratch .lhsOperand
  · subst hk; simp [Function.update, hLhs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWorkRev]
    · simp [Function.update, hk, hk2]

/-- `copyRhs`, `copyRhsRestore` and `reverseRhs` chained: `rt`'s digits end up on `rhsOperand`
    with `rt` itself restored and `workRev` empty again. -/
lemma realize_sub_bounded_copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRt : Sg (Kg.reg rt) = src) (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[3 * src.length + 3]
        (some (⟨some SubPhase.copyRhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.clearDest, ⟨none, none, false⟩,
          Function.update Sg (Kg.scratch .rhsOperand) src⟩ := by
  have hcount : 3 * src.length + 3 = (src.reverse.length + 1) + (2 * src.length + 2) := by
    rw [List.length_reverse]; omega
  have hWr : (Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .workRev) = src.reverse := by simp [hWorkRev]
  rw [hcount, Function.iterate_add_apply,
    sub_copyRhs_phase rd rs rt src Sg ⟨none, none, false⟩ hRt hCopyScratch,
    sub_reverseRhs_loop rd rs rt src.reverse _ ⟨none, none, false⟩ hWr]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.scratch .rhsOperand
  · subst hk; simp [Function.update, hRhs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWorkRev]
    · simp [Function.update, hk, hk2]

/-- The whole non-destructive snapshot prefix of `sub`, from `copyLhs` through `clearDest`: both
    operands are captured and `rd` is emptied, with step count `rd + 3|rt| + 3 + 3|rs| + 3`. -/
lemma realize_sub_bounded_prefix (A B : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = A) (hRt : Sg (Kg.reg rt) = B)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[((Sg (Kg.reg rd)).length + 1)
        + ((3 * B.length + 3) + (3 * A.length + 3))]
        (some (⟨some SubPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.subLoop, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
              (Kg.scratch .rhsOperand) B) (Kg.reg rd) []⟩ := by
  have hrun1 := realize_sub_bounded_copyLhs_phase rd rs rt A Sg hRs hWorkRev hCopyScratch hLhs
  have hrun2 := realize_sub_bounded_copyRhs_phase rd rs rt B
    (Function.update Sg (Kg.scratch .lhsOperand) A) (by simpa using hRt) (by simpa using hWorkRev)
    (by simpa using hCopyScratch) (by simpa using hRhs)
  have hlen : ((Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
      (Kg.scratch .rhsOperand) B) (Kg.reg rd)).length = (Sg (Kg.reg rd)).length := by simp
  have hrun3 := sub_clearDest_loop rd rs rt _
    (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A) (Kg.scratch .rhsOperand) B)
    ⟨none, none, false⟩ rfl
  rw [hlen] at hrun3
  rw [Function.iterate_add_apply (flipBindSub rd rs rt) ((Sg (Kg.reg rd)).length + 1)
      ((3 * B.length + 3) + (3 * A.length + 3)),
    Function.iterate_add_apply (flipBindSub rd rs rt) (3 * B.length + 3) (3 * A.length + 3),
    hrun1, hrun2, hrun3]

/-- Underflow tail: `subLoop` then `drainDiff`, leaving `rd` untouched and every scratch empty. -/
lemma realize_sub_bounded_tail_underflow (A B : List Digit) (Sg : ∀ k, List (Γg p k))
    (hborrow : (subRawFull A B false).2 = true)
    (hLhs : Sg (Kg.scratch .lhsOperand) = A) (hRhs : Sg (Kg.scratch .rhsOperand) = B)
    (hDiff : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[((subRawFull A B false).1.length + 1)
        + ((subRawFull A B false).1.length + 1)]
        (some (⟨some SubPhase.subLoop, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch) []⟩ := by
  have hloop := subLoop_run rd rs rt Sg A B false none none hLhs hRhs
  rw [hborrow, ite_eq_left rfl] at hloop
  have hdrain := drainDiff_loop rd rs rt (subRawFull A B false).1.reverse
    (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch)
      ((subRawFull A B false).1.reverse ++ Sg (Kg.scratch .diffScratch)))
    ⟨none, none, true⟩ (by simp [Function.update, hDiff])
  rw [List.length_reverse] at hdrain
  rw [Function.iterate_add_apply, hloop, hdrain]
  simp

/-- No-underflow tail: `subLoop` then `skipZeros`, writing the trimmed difference `R` onto an
    empty `rd`. -/
lemma realize_sub_bounded_tail_ge (A B R : List Digit) (Sg : ∀ k, List (Γg p k))
    (hborrow : (subRawFull A B false).2 = false)
    (htrim : ((subRawFull A B false).1.reverse.dropWhile (fun d => decide (d.val = 0))).reverse = R)
    (hLhs : Sg (Kg.scratch .lhsOperand) = A) (hRhs : Sg (Kg.scratch .rhsOperand) = B)
    (hDiff : Sg (Kg.scratch .diffScratch) = ([] : List Digit))
    (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[((subRawFull A B false).1.length + 1)
        + ((subRawFull A B false).1.length + 1)]
        (some (⟨some SubPhase.subLoop, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch) []) (Kg.reg rd) R⟩ := by
  have hloop := subLoop_run rd rs rt Sg A B false none none hLhs hRhs
  rw [hborrow, ite_eq_right (by simp)] at hloop
  have hskip := skipZeros_phase rd rs rt (subRawFull A B false).1.reverse
    (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch)
      ((subRawFull A B false).1.reverse ++ Sg (Kg.scratch .diffScratch)))
    ⟨none, none, false⟩ (by simp [Function.update, hDiff])
  rw [List.length_reverse] at hskip
  rw [Function.iterate_add_apply, hloop, hskip]
  subst htrim
  simp [Function.update, hRd]

/-- Both tails unified: after the prefix, `subLoop` reaches `done` with `rd` holding
    `natToDigits (rsVal - rtVal)` and all scratch stacks empty. -/
lemma realize_sub_bounded_tail (rsVal rtVal : ℕ) (S : ∀ k, List (Γg p k))
    (hLhs : S (Kg.scratch .lhsOperand) = natToDigits rsVal)
    (hRhs : S (Kg.scratch .rhsOperand) = natToDigits rtVal)
    (hDiff : S (Kg.scratch .diffScratch) = ([] : List Digit))
    (hRd : S (Kg.reg rd) = ([] : List Digit)) :
    (flipBindSub rd rs rt)^[((subRawFull (natToDigits rsVal) (natToDigits rtVal) false).1.length + 1)
        + ((subRawFull (natToDigits rsVal) (natToDigits rtVal) false).1.length + 1)]
        (some (⟨some SubPhase.subLoop, ⟨none, none, false⟩, S⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩,
          Function.update
            (Function.update (Function.update (Function.update S (Kg.scratch .lhsOperand) [])
              (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch) [])
            (Kg.reg rd) (natToDigits (rsVal - rtVal))⟩ := by
  rcases Nat.lt_or_ge rsVal rtVal with hlt | hge
  · have hrsub : rsVal - rtVal = 0 := by omega
    have hnil0 : natToDigits 0 = ([] : List Digit) := by
      simpa using (natToDigits_ne_nil_iff 0)
    rw [hrsub, hnil0, realize_sub_bounded_tail_underflow rd rs rt _ _ S
      (sub_result_underflow rsVal rtVal hlt) hLhs hRhs hDiff]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    by_cases hk : k = Kg.reg rd
    · subst hk; simp [Function.update, hRd]
    · simp [Function.update, hk]
  · obtain ⟨hborrow, htrim⟩ := sub_result_ge rsVal rtVal hge
    exact realize_sub_bounded_tail_ge rd rs rt _ _ _ S hborrow htrim hLhs hRhs hDiff hRd

/-- All scratch stacks the prefix and tail touch are back to their initial (empty) contents, so
    only the `rd` update remains. -/
lemma realize_sub_bounded_final_stack (Sg : ∀ k, List (Γg p k)) (A B R : List Digit)
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit))
    (hDiff : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
        (Kg.scratch .rhsOperand) B) (Kg.reg rd) [])
      (Kg.scratch .lhsOperand) []) (Kg.scratch .rhsOperand) []) (Kg.scratch .diffScratch) [])
      (Kg.reg rd) R
      = Function.update Sg (Kg.reg rd) R := by
  rw [Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .rhsOperand by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .diffScratch by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .rhsOperand : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_idem, Function.update_idem,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .lhsOperand)).2 hLhs.symm,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .rhsOperand)).2 hRhs.symm,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .diffScratch)).2 hDiff.symm]

/-- The generalized `sub` instruction, realized against an arbitrary site's register triple: the
    non-destructive snapshot prefix mirrors `GenericAdd.realize_add` exactly; the
    tail then branches on `rsVal` vs `rtVal` (`DigitSub.sub_result_underflow`/`sub_result_ge`) —
    underflow drains `diffScratch` without ever writing `rd` (`drainDiff_loop`, `rd` stays empty
    from `clearDest`, i.e. `natToDigits 0`), otherwise `skipZeros_phase` trims and relocates the
    true difference. Both branches land on exactly `natToDigits (rsVal - rtVal)` (`ℕ` truncated
    subtraction), matching `BitCostRAM.step`'s `sub rd rs rt` effect uniformly, with no case split
    needed in the *statement* itself.  The witness step count is bounded too. Like `add`, `sub`
    has no induction (a single case split on underflow), so
    `subRawFull_length_le` (`(subRawFull srcA srcB borrow).1.length ≤ max srcA.length
    srcB.length`) bounds the raw-difference digit list directly by `regSize`-shaped quantities —
    unlike `add`'s bound, no `bitLen`/`instructionCost` detour is needed here. -/
lemma realize_sub_bounded (rsVal rtVal : ℕ) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = natToDigits rsVal) (hRt : Sg (Kg.reg rt) = natToDigits rtVal)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = ([] : List Digit))
    (hDiffScratch : Sg (Kg.scratch .diffScratch) = ([] : List Digit)) :
    ∃ n, (flipBindSub rd rs rt)^[n]
        (some (⟨some SubPhase.copyLhs, ⟨none, none, false⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) SubPhase SubState))
      = some ⟨some SubPhase.done, ⟨none, none, false⟩,
          Function.update Sg (Kg.reg rd) (natToDigits (rsVal - rtVal))⟩ ∧
        n ≤ 16 * ((Sg (Kg.reg rd)).length + (natToDigits rsVal).length
          + (natToDigits rtVal).length + 1) := by
  have hpre := realize_sub_bounded_prefix rd rs rt (natToDigits rsVal) (natToDigits rtVal) Sg
    hRs hRt hWorkRev hCopyScratch hLhsOperand hRhsOperand
  have htail := realize_sub_bounded_tail rd rs rt rsVal rtVal
    (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand)
      (natToDigits rsVal)) (Kg.scratch .rhsOperand) (natToDigits rtVal)) (Kg.reg rd) [])
    (by simp) (by simp) (by simpa [Function.update] using hDiffScratch) (by simp)
  have hL := subRawFull_length_le (natToDigits rsVal) (natToDigits rtVal) false
  refine ⟨((subRawFull (natToDigits rsVal) (natToDigits rtVal) false).1.length + 1)
      + ((subRawFull (natToDigits rsVal) (natToDigits rtVal) false).1.length + 1)
      + (((Sg (Kg.reg rd)).length + 1)
        + ((3 * (natToDigits rtVal).length + 3) + (3 * (natToDigits rsVal).length + 3))), ?_, ?_⟩
  · rw [Function.iterate_add_apply, hpre, htail,
      realize_sub_bounded_final_stack rd Sg _ _ _ hLhsOperand hRhsOperand hDiffScratch]
  · omega

/-! ## Site dispatcher package

Mirrors `GenericAdd.lean`'s `addCode`/`add_impl_growing_bounded` pattern: `subCode` casts the whole
local `SubPhase`-indexed function once via `cast_apply_phaseOf`, and `sub_impl_growingBoundedSiteStepSim`
transports `realize_sub_bounded`'s local run into the global machine via `iterate_bind_step_liftStmt` followed by
one bridge step. -/

/-- `sub`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `subProg` lifted via `execVia`. -/
def subCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt) : SubPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = SubPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getSub AllInstrState.setSub
        (subProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `subCodeBody`, cast once from `SubPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def subCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (subCodeBody p pc rd rs rt h)

/-- `subCode` undoes its own cast when applied to a correspondingly-cast `SubPhase` value. -/
lemma subCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt) (l : SubPhase) :
    subCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l) = subCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (subCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `subCode` at site `pc` installs the lifted `subProg` tree at
    every non-`done` label. -/
lemma subCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (subCode p pc rd rs rt h) M) :
    ∀ l : SubPhase, l ≠ SubPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getSub AllInstrState.setSub
        (subProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    subCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `subCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `sub`'s own `done` label. -/
lemma subCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (subCode p pc rd rs rt h) M) :
    M (execVia p pc h SubPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) SubPhase.done)
  rw [show execVia p pc h SubPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) SubPhase.done) from rfl, hone,
    subCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- A `sub` step only rewrites register `rd`. -/
lemma sub_impl_growing_bounded_step_regs (rd rs rt : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.sub rd rs rt) :
    (step r).regs = bankWrite r.regs rd (r.regs rs - r.regs rt) := by
  simp [step, hcurEq]

/-- The current instruction is `sub` at the site's program counter. -/
lemma sub_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .sub rd rs rt) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.sub rd rs rt := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `copyLhs` entry. -/
lemma sub_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .sub rd rs rt)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h SubPhase.copyLhs) := by
  have hstart : startPhaseOpt (Instruction.sub rd rs rt) = some SubPhase.copyLhs := rfl
  have hentry : entryAt p pc.1 = execVia p pc h SubPhase.copyLhs :=
    entryAt_eq_execVia p pc h SubPhase.copyLhs hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `sub` site run on the global machine: the `subProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (only `rd'`
    rewritten) and a step count bound. -/
lemma sub_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .sub rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (subCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h SubPhase.copyLhs))
    (rd' rs' rt' : Fin (regBound p))
    (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (hrs' : rs' = regAt p pc rs (by rw [h]; simp [regsOf]))
    (hrt' : rt' = regAt p pc rt (by rw [h]; simp [regsOf])) (a b : ℕ)
    (hRs : cfg.stk (Kg.reg rs') = natToDigits a) (hRt : cfg.stk (Kg.reg rt') = natToDigits b)
    (hWorkRev : cfg.stk (Kg.scratch ScratchKind.workRev) = [])
    (hCopyScratch : cfg.stk (Kg.scratch ScratchKind.copyScratch) = [])
    (hLhs : cfg.stk (Kg.scratch ScratchKind.lhsOperand) = [])
    (hRhs : cfg.stk (Kg.scratch ScratchKind.rhsOperand) = [])
    (hDiff : cfg.stk (Kg.scratch ScratchKind.diffScratch) = []) :
    ∃ n Sgf, (flipBindG p M)^[n] (some cfg)
        = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      n ≤ 16 * ((cfg.stk (Kg.reg rd')).length + (natToDigits a).length + (natToDigits b).length
        + 1) + 1 ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits (a - b)) := by
  have hag := subCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd', ← hrs', ← hrt'] at hag
  obtain ⟨N, hSubRun, hNbound⟩ := realize_sub_bounded rd' rs' rt' a b cfg.stk
    hRs hRt hWorkRev hCopyScratch hLhs hRhs hDiff
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getSub AllInstrState.setSub (subProg rd' rs' rt') M
      Function.injective_id AllInstrState.getSub_setSub AllInstrState.setSub_setSub
      AllInstrState.setSub_getSub N SubPhase.copyLhs (⟨none, none, false⟩ : SubState)
      cfg.stk AllInstrState.canonical cfg.stk rfl hstkTriv
      SubPhase.done (⟨none, none, false⟩ : SubState)
      (Function.update cfg.stk (Kg.reg rd') (natToDigits (a - b))) rfl hag hSubRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h SubPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h SubPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h SubPhase.done)) sf Sgf) from rfl,
      subCode_agrees_done p pc rd rs rt h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h SubPhase.copyLhs), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨N + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `sub` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma sub_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs rt : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.sub rd rs rt)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') (natToDigits (r.regs rs - r.regs rt))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rd') _ _⟩
  rw [sub_impl_growing_bounded_step_regs rd rs rt r hcurEq]
  by_cases hi : i = rd'
  · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
  · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
    exact hregs i

/-- The configuration reached after a `sub` run represents the stepped RAM, given the register
    frame and the untouched non-register stacks. -/
lemma sub_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.sub rd rs rt)
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
lemma sub_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) (n : ℕ)
    (hn : n ≤ 16 * ((cfg.stk (Kg.reg rd')).length + (natToDigits (r.regs rs)).length
      + (natToDigits (r.regs rt)).length + 1) + 1) :
    n ≤ 64 * (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle1 : (cfg.stk (Kg.reg rd')).length ≤ regSize p r := by
    rw [hregs rd']; exact natToDigits_length_le_regSize p r rd'
  have hle2 := natToDigits_length_le_regSize p r rs'
  have hle3 := natToDigits_length_le_regSize p r rt'
  rw [hrsval] at hle2
  rw [hrtval] at hle3
  set X := regSize p r + (cfg.stk Kg.mem).length + instructionCost r.regs r.mem r.current + 1
    with hX
  have hXpos : 1 ≤ X := by omega
  have hXsq : X ≤ X ^ 2 := by nlinarith [hXpos]
  have hlX : regSize p r + 1 ≤ X ^ 2 := le_trans (by omega : regSize p r + 1 ≤ X) hXsq
  omega

/-- Potential growth: only `rd` changes, to at most `bitLen rs` digits (truncated subtraction only
    shrinks), and the memory stack is untouched. -/
lemma sub_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs rt : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.sub rd rs rt) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := sub_impl_growing_bounded_step_regs rd rs rt r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits (r.regs rs - r.regs rt)).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' (r.regs rs - r.regs rt) _ le_rfl
  have hle : (natToDigits (r.regs rs - r.regs rt)).length ≤ bitLen (r.regs rs) :=
    le_trans (natToDigits_length_le_bitLen _) (bitLen_le_of_le (Nat.sub_le _ _))
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rs) + bitLen (r.regs rt) + 1 := by rw [hcurEq]; rfl
  rw [hother _ (by simp)]
  omega

/-- `subCode`'s growth companion: `mem` is untouched, and the only register that can grow is
    `rd`, to `bitLen (regs rs - regs rt) ≤ bitLen (regs rs)` (truncated subtraction only shrinks),
    itself `≤` `sub`'s own `instructionCost`. -/
lemma sub_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt) :
    GrowingBoundedSiteStepSim p pc (subCode p pc rd rs rt h) 64 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := sub_impl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := sub_impl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rt', hrt'⟩ : ∃ x, x = regAt p pc rt (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hrtval : rt'.1 = rt := by rw [hrt']; rfl
  have hRs : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  have hRt : cfg.stk (Kg.reg rt') = natToDigits (r.regs rt) := by rw [hregs rt', hrtval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := sub_impl_growing_bounded_run p pc rd rs rt h M hAgrees
    cfg hvar hcl rd' rs' rt' hrd' hrs' hrt' _ _ hRs hRt (hscratch .workRev) (hscratch .copyScratch)
    (hscratch .lhsOperand) (hscratch .rhsOperand) (hscratch .diffScratch)
  obtain ⟨hreg, hother⟩ := sub_impl_growing_bounded_stk cfg.stk r rd rs rt rd' hrdval hcurEq hregs
    Sgf hSgf
  exact ⟨n, _, hrun,
    sub_impl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    sub_impl_growing_bounded_time p cfg r rs rt rd' rs' rt' hrsval hrtval hregs n hn,
    sub_impl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩

/-- `sub`'s `GrowingTimedInstrImpl` package. -/
def subGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .sub rd rs rt) : GrowingTimedInstrImpl p pc where
  code := subCode p pc rd rs rt h
  C := 64
  G := 1
  growingSim := sub_impl_growingBoundedSiteStepSim p pc rd rs rt h

end NPComplete.RAMToTM.Generic

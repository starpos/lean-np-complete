module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# Shared multi-digit comparison core for `setIfLt`/`setIfEq`/`branchIfLt`

All three instructions need the same "compare `rs` against `rt`, leaving both registers
unchanged" building block; only what happens *after* the comparison differs (`setIfLt`/`setIfEq`
drain `rd` and push a 0/1 digit, `branchIfLt` picks a bridge target; these are handled in
`GenericSetIfLt.lean`, `GenericSetIfEq.lean`, and `GenericBranchIfLt.lean`). Rather than one
shared phase enum with unreachable labels for instructions that skip some of it, each
instruction gets its own phase type embedding this file's `CompareCorePhase` via a
`compare : CompareCorePhase → ...Phase` constructor matching `GenericProgramMachine.lean`'s
"one `AllInstrState` field per realized instruction" convention: each of the three
instructions gets its own `CompareState` field, not a shared one.

**Lockstep-pop alias hazard**: `scan` pops `rs` and `rt` within the *same* `Stmt` tree evaluation,
unlike every non-destructive read-restore elsewhere in this codebase (`store`/`load`/`add`/`move`),
which read one operand fully before starting the next and are therefore alias-safe "for free".
Popping two operands in lockstep is *not* safe when `rs = rt` (same physical stack): the second
`pop` would consume the digit adjacent to the one the first `pop` just took, not re-read the same
digit. `compareCoreStmt` itself assumes `rs ≠ rt` (baked into its correctness proof via
`Function.update_of_ne`); the alias case is handled entirely at each instruction's site-construction
level via a `by_cases rs = rt` on the raw instruction operands (decidable `ℕ` literals), building a
trivial one-step "`acc := .eq`, no register access" tree instead of instantiating this core.

**`scan`/`drainLeft`/`drainRight` mirror `Binary.compareDigits`'s own recursion exactly**: `scan`
lockstep-pops while *both* operands still have digits (`compareDigits`'s `a :: as, b :: bs` case),
accumulating `Ordering.then`-composed comparisons (`Binary.scanCompare`'s accumulator step) and
stashing each popped digit onto `lhsOperand`/`rhsOperand` (reused from `GenericAdd.lean`, disjoint
from `rs`/`rt` regardless of aliasing, so no case split there); as soon as either operand is found
exhausted (peeked, not yet popped), that side's length trumps unconditionally (`compareDigits`'s
`[], _::_`/`_::_, []` base cases) and `acc` is overwritten with the fixed final result — `drainLeft`/
`drainRight` then simply finish stashing whichever side (if either) still has leftover digits, since
those must still be restored even though they no longer affect the comparison outcome. `restoreLeft`/
`restoreRight` undo the stash (a second reversal, exactly `GenericMove.lean`'s `copySrc`/
`copySrcRestore` round trip, doubled) to leave both registers exactly as they started.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits scanCompare)
open Turing Turing.TM2.Stmt

variable {p : List Instruction}

/-- The comparison core's `Stmt` tree, self-contained against its own `CompareCorePhase`/
    `CompareState` (mirroring `GenericAdd.lean`'s `addProg`), embedded into each of `setIfLt`/
    `setIfEq`/`branchIfLt`'s own local program via `StmtTransport.liftStmt` (module docstring:
    `ιΛ := .compare`, trivial identity state lens since `CompareState` *is* each of those
    programs' own local `σ`). Assumes `rs ≠ rt` (enforced by the caller, not by this tree) for
    lockstep-pop alias safety. -/
def compareCoreProg (rs rt : Fin (regBound p)) :
    CompareCorePhase → Turing.TM2.Stmt (Γg p) CompareCorePhase CompareState
  | .scan =>
      peek (Kg.reg rs) (fun s ov => {s with left := ov})
        (peek (Kg.reg rt) (fun s ov => {s with right := ov})
          (branch (fun s => s.left.isSome && s.right.isSome)
            (pop (Kg.reg rs) (fun s ov => {s with left := ov})
              (pop (Kg.reg rt) (fun s ov => {s with right := ov})
                (push (Kg.scratch .lhsOperand) (fun s => s.left.getD default)
                  (push (Kg.scratch .rhsOperand) (fun s => s.right.getD default)
                    (load (fun s => {s with
                        acc := (compare (s.left.getD default) (s.right.getD default)).then s.acc})
                      (goto (fun _ => .scan)))))))
            (branch (fun s => s.left.isSome)
              (load (fun s => {s with acc := .gt}) (goto (fun _ => .drainLeft)))
              (branch (fun s => s.right.isSome)
                (load (fun s => {s with acc := .lt}) (goto (fun _ => .drainRight)))
                (goto (fun _ => .restoreLeft))))))
  | .drainLeft =>
      pop (Kg.reg rs) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (push (Kg.scratch .lhsOperand) (fun s => s.left.getD default)
            (goto (fun _ => .drainLeft)))
          (goto (fun _ => .restoreLeft)))
  | .drainRight =>
      pop (Kg.reg rt) (fun s ov => {s with right := ov})
        (branch (fun s => s.right.isSome)
          (push (Kg.scratch .rhsOperand) (fun s => s.right.getD default)
            (goto (fun _ => .drainRight)))
          (goto (fun _ => .restoreLeft)))
  | .restoreLeft =>
      pop (Kg.scratch .lhsOperand) (fun s ov => {s with left := ov})
        (branch (fun s => s.left.isSome)
          (push (Kg.reg rs) (fun s => s.left.getD default) (goto (fun _ => .restoreLeft)))
          (goto (fun _ => .restoreRight)))
  | .restoreRight =>
      pop (Kg.scratch .rhsOperand) (fun s ov => {s with right := ov})
        (branch (fun s => s.right.isSome)
          (push (Kg.reg rt) (fun s => s.right.getD default) (goto (fun _ => .restoreRight)))
          (goto (fun _ => .done)))
  | .done => halt

/-- Two `Function.update`s at (possibly equal) keys, each rewriting to a value the underlying
    function already had there, is the identity — reused throughout this file wherever a
    `compareCoreProg` step lemma's own `Function.update` chain re-touches a key that was already
    at its target value (e.g. `Kg.reg rs`/`Kg.reg rt` after `scanRun` has already emptied them),
    without needing to know whether the two keys coincide. -/
lemma update2_self {K : Type} [DecidableEq K] {Γ : K → Type} (Sg : ∀ k, Γ k)
    (k1 k2 : K) (v1 : Γ k1) (v2 : Γ k2) (h1 : Sg k1 = v1) (h2 : Sg k2 = v2) :
    Function.update (Function.update Sg k1 v1) k2 v2 = Sg := by
  funext k
  by_cases e1 : k = k1
  · by_cases e2 : k = k2
    · subst e1; subst e2; simp [Function.update, h2]
    · subst e1; rw [Function.update_of_ne e2, Function.update_self, h1]
  · by_cases e2 : k = k2
    · subst e2; rw [Function.update_self, h2]
    · rw [Function.update_of_ne e2, Function.update_of_ne e1]

variable (rs rt : Fin (regBound p))

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindCompareCore :
    Option (Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) →
      Option (Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) :=
  fun x => x.bind (Turing.TM2.step (compareCoreProg rs rt))

/-! ## `scan`: lockstep pop of `rs`/`rt`, assuming `rs ≠ rt` -/

lemma compare_core_scan_cons_cons (hne : rs ≠ rt) (a : Digit) (as : List Digit)
    (b : Digit) (bs : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRs : Sg (Kg.reg rs) = a :: as) (hRt : Sg (Kg.reg rt) = b :: bs) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.scan,
          ({v0 with left := some a, right := some b, acc := (compare a b).then v0.acc}
            : CompareState),
          Function.update
            (Function.update
              (Function.update (Function.update Sg (Kg.reg rs) as) (Kg.reg rt) bs)
              (Kg.scratch .lhsOperand) (a :: Sg (Kg.scratch .lhsOperand)))
            (Kg.scratch .rhsOperand) (b :: Sg (Kg.scratch .rhsOperand))⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.scan, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  have hrtne : Function.update Sg (Kg.reg rs) as (Kg.reg rt) = Sg (Kg.reg rt) :=
    Function.update_of_ne (fun h => hne (by simpa using h.symm)) _ _
  simp [compareCoreProg, hRs, hRt, hrtne]

lemma compare_core_scan_nil_nil
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRs : Sg (Kg.reg rs) = ([] : List Digit)) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft,
          ({v0 with left := none, right := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.scan, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRs, hRt]

lemma compare_core_scan_nil_cons (b : Digit) (bs : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRs : Sg (Kg.reg rs) = ([] : List Digit)) (hRt : Sg (Kg.reg rt) = b :: bs) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.drainRight,
          ({v0 with left := none, right := some b, acc := .lt} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.scan, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRs, hRt]

lemma compare_core_scan_cons_nil (a : Digit) (as : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRs : Sg (Kg.reg rs) = a :: as) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.drainLeft,
          ({v0 with left := some a, right := none, acc := .gt} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.scan, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRs, hRt]

/-! ## `drainLeft`/`drainRight`: finish stashing the longer side once the shorter is exhausted -/

lemma compare_core_drainLeft_cons (a : Digit) (as : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRs : Sg (Kg.reg rs) = a :: as) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.drainLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.drainLeft, ({v0 with left := some a} : CompareState),
          Function.update (Function.update Sg (Kg.reg rs) as)
            (Kg.scratch .lhsOperand) (a :: Sg (Kg.scratch .lhsOperand))⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.drainLeft, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRs]

lemma compare_core_drainLeft_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRs : Sg (Kg.reg rs) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.drainLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.drainLeft, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRs]

/-- Draining register `rs`'s remaining digits (whatever length), stashing each onto
    `lhsOperand` — used when `rt` was found exhausted first (`compare_core_scan_cons_nil`), since
    `rs` must still be restored even though the comparison outcome (`.gt`) is already fixed. -/
lemma compare_core_drainLeft_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRs : Sg (Kg.reg rs) = src) :
    (flipBindCompareCore rs rt)^[src.length + 1]
        (some (⟨some CompareCorePhase.drainLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft, ({v0 with left := none} : CompareState),
          Function.update (Function.update Sg (Kg.reg rs) [])
            (Kg.scratch .lhsOperand) (src.reverse ++ Sg (Kg.scratch .lhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      rw [update2_self Sg (Kg.reg rs) (Kg.scratch .lhsOperand) [] (Sg (Kg.scratch .lhsOperand))
        hRs rfl]
      exact compare_core_drainLeft_nil_exit rs rt Sg v0 hRs
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        compare_core_drainLeft_cons rs rt d src' Sg v0 hRs,
        ih (Function.update (Function.update Sg (Kg.reg rs) src')
              (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand)))
           ({v0 with left := some d} : CompareState) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rs
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .lhsOperand
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma compare_core_drainRight_cons (b : Digit) (bs : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRt : Sg (Kg.reg rt) = b :: bs) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.drainRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.drainRight, ({v0 with right := some b} : CompareState),
          Function.update (Function.update Sg (Kg.reg rt) bs)
            (Kg.scratch .rhsOperand) (b :: Sg (Kg.scratch .rhsOperand))⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.drainRight, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRt]

lemma compare_core_drainRight_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.drainRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft, ({v0 with right := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.drainRight, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hRt]

/-- Draining register `rt`'s remaining digits, stashing each onto `rhsOperand` — used when `rs`
    was found exhausted first (`compare_core_scan_nil_cons`), mirroring
    `compare_core_drainLeft_loop`. -/
lemma compare_core_drainRight_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hRt : Sg (Kg.reg rt) = src) :
    (flipBindCompareCore rs rt)^[src.length + 1]
        (some (⟨some CompareCorePhase.drainRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft, ({v0 with right := none} : CompareState),
          Function.update (Function.update Sg (Kg.reg rt) [])
            (Kg.scratch .rhsOperand) (src.reverse ++ Sg (Kg.scratch .rhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      rw [update2_self Sg (Kg.reg rt) (Kg.scratch .rhsOperand) [] (Sg (Kg.scratch .rhsOperand))
        hRt rfl]
      exact compare_core_drainRight_nil_exit rs rt Sg v0 hRt
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        compare_core_drainRight_cons rs rt d src' Sg v0 hRt,
        ih (Function.update (Function.update Sg (Kg.reg rt) src')
              (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand)))
           ({v0 with right := some d} : CompareState) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rt
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .rhsOperand
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- The full `scan` phase run (`CompareCorePhase.scan` to `.restoreLeft`), with a bound on the
    witness step count, linear in `xs.length + ys.length` (unlike `load`'s `scan_phase`, this
    induction walks both lists down together and each step costs `O(1)`, so no invariant-potential
    argument is needed — a direct induction closes it). -/
lemma compare_core_scan_run_bounded (hne : rs ≠ rt) (xs ys : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState) (hRs : Sg (Kg.reg rs) = xs)
    (hRt : Sg (Kg.reg rt) = ys) :
    ∃ n, (flipBindCompareCore rs rt)^[n]
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft,
          ({v0 with left := none, right := none, acc := scanCompare v0.acc xs ys} : CompareState),
          Function.update
            (Function.update (Function.update (Function.update Sg (Kg.reg rs) []) (Kg.reg rt) [])
              (Kg.scratch .lhsOperand) (xs.reverse ++ Sg (Kg.scratch .lhsOperand)))
            (Kg.scratch .rhsOperand) (ys.reverse ++ Sg (Kg.scratch .rhsOperand))⟩ ∧
        n ≤ xs.length + ys.length + 3 := by
  induction xs generalizing ys Sg v0 with
  | nil =>
      cases ys with
      | nil =>
          refine ⟨1, ?_, by simp⟩
          rw [Function.iterate_one, compare_core_scan_nil_nil rs rt Sg v0 hRs hRt]
          simp only [scanCompare, List.reverse_nil, List.nil_append, Option.some.injEq,
            Turing.TM2.Cfg.mk.injEq, true_and]
          rw [update2_self Sg (Kg.reg rs) (Kg.reg rt) [] [] hRs hRt]
          funext k
          by_cases hk3 : k = Kg.scratch .lhsOperand
          · subst hk3; simp [Function.update]
          · by_cases hk4 : k = Kg.scratch .rhsOperand
            · subst hk4; simp [Function.update]
            · simp [Function.update, hk3, hk4]
      | cons b bs =>
          refine ⟨bs.length + 3, ?_, by simp⟩
          rw [show bs.length + 3 = (bs.length + 2) + 1 from rfl, Function.iterate_succ_apply,
            compare_core_scan_nil_cons rs rt b bs Sg v0 hRs hRt,
            show bs.length + 2 = (b :: bs).length + 1 from rfl,
            compare_core_drainRight_loop rs rt (b :: bs) Sg _ hRt]
          simp only [scanCompare, List.reverse_nil, List.nil_append, Option.some.injEq,
            Turing.TM2.Cfg.mk.injEq, true_and]
          have hRsNoop : Function.update Sg (Kg.reg rs) [] = Sg := by
            funext k; by_cases hk : k = Kg.reg rs
            · subst hk; simp [Function.update, hRs]
            · simp [Function.update, hk]
          rw [hRsNoop]
          funext k
          by_cases hk3 : k = Kg.scratch .lhsOperand
          · subst hk3; simp [Function.update]
          · simp [Function.update, hk3]
  | cons a as ih =>
      cases ys with
      | nil =>
          refine ⟨as.length + 3, ?_, by simp⟩
          rw [show as.length + 3 = (as.length + 2) + 1 from rfl, Function.iterate_succ_apply,
            compare_core_scan_cons_nil rs rt a as Sg v0 hRs hRt,
            show as.length + 2 = (a :: as).length + 1 from rfl,
            compare_core_drainLeft_loop rs rt (a :: as) Sg _ hRs]
          simp only [scanCompare, List.reverse_nil, List.nil_append, Option.some.injEq,
            Turing.TM2.Cfg.mk.injEq, true_and]
          have hneK : Kg.reg rs ≠ Kg.reg rt := fun h => hne (by injection h)
          funext k
          by_cases hkl : k = Kg.scratch .lhsOperand
          · subst hkl; simp [Function.update]
          by_cases hkr : k = Kg.scratch .rhsOperand
          · subst hkr; simp [Function.update, hkl]
          by_cases hk1 : k = Kg.reg rs
          · subst hk1; simp [Function.update, hkl, hkr, hneK]
          by_cases hk2 : k = Kg.reg rt
          · subst hk2; simp [Function.update, hkl, hkr, hk1, hRt]
          simp [Function.update, hkl, hkr, hk1, hk2]
      | cons b bs =>
          have hSgRs : Function.update (Function.update Sg (Kg.reg rs) as) (Kg.reg rt) bs
              (Kg.reg rs) = as := by
            rw [Function.update_of_ne (fun h => hne (by injection h)), Function.update_self]
          have hSgRt : Function.update (Function.update Sg (Kg.reg rs) as) (Kg.reg rt) bs
              (Kg.reg rt) = bs := by
            rw [Function.update_self]
          obtain ⟨n, hn, hnbound⟩ := ih bs
            (Function.update
              (Function.update
                (Function.update (Function.update Sg (Kg.reg rs) as) (Kg.reg rt) bs)
                (Kg.scratch .lhsOperand) (a :: Sg (Kg.scratch .lhsOperand)))
              (Kg.scratch .rhsOperand) (b :: Sg (Kg.scratch .rhsOperand)))
            ({v0 with left := some a, right := some b, acc := (compare a b).then v0.acc}
              : CompareState)
            (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), hSgRs])
            (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), hSgRt])
          refine ⟨n + 1, ?_, by simp only [List.length_cons]; omega⟩
          rw [Function.iterate_succ_apply,
            compare_core_scan_cons_cons rs rt hne a as b bs Sg v0 hRs hRt, hn]
          simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
          refine ⟨rfl, ?_⟩
          have hneK : Kg.reg rs ≠ Kg.reg rt := fun h => hne (by injection h)
          funext k
          by_cases hkl : k = Kg.scratch .lhsOperand
          · subst hkl; simp [Function.update, List.reverse_cons, List.append_assoc]
          by_cases hkr : k = Kg.scratch .rhsOperand
          · subst hkr; simp [Function.update, List.reverse_cons, List.append_assoc]
          by_cases hk1 : k = Kg.reg rs
          · subst hk1; simp [Function.update, hkl, hkr, hneK]
          by_cases hk2 : k = Kg.reg rt
          · subst hk2; simp [Function.update, hkl, hkr]
          simp [Function.update, hkl, hkr, hk1, hk2]

/-! ## `restoreLeft`/`restoreRight`: undo the stash, restoring `rs`/`rt` exactly -/

lemma compare_core_restoreLeft_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hL : Sg (Kg.scratch .lhsOperand) = d :: rest) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.restoreLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreLeft, ({v0 with left := some d} : CompareState),
          Function.update (Function.update Sg (Kg.scratch .lhsOperand) rest)
            (Kg.reg rs) (d :: Sg (Kg.reg rs))⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.restoreLeft, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hL]

lemma compare_core_restoreLeft_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hL : Sg (Kg.scratch .lhsOperand) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.restoreLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreRight, ({v0 with left := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.restoreLeft, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hL]

/-- Popping `lhsOperand` (which, after `scanRun`, holds `rs`'s original digits reversed) and
    pushing each back onto `rs` reconstructs `rs`'s original LSB-first content exactly, via the
    same double-reversal round trip as `GenericMove.lean`'s `copySrc`/`copySrcRestore`. -/
lemma compare_core_restoreLeft_loop (stash : List Digit) (Sg : ∀ k, List (Γg p k))
    (v0 : CompareState) (hL : Sg (Kg.scratch .lhsOperand) = stash) :
    (flipBindCompareCore rs rt)^[stash.length + 1]
        (some (⟨some CompareCorePhase.restoreLeft, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreRight, ({v0 with left := none} : CompareState),
          Function.update (Function.update Sg (Kg.scratch .lhsOperand) [])
            (Kg.reg rs) (stash.reverse ++ Sg (Kg.reg rs))⟩ := by
  induction stash generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      rw [update2_self Sg (Kg.scratch .lhsOperand) (Kg.reg rs) [] (Sg (Kg.reg rs)) hL rfl]
      exact compare_core_restoreLeft_nil_exit rs rt Sg v0 hL
  | cons d stash' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        compare_core_restoreLeft_cons rs rt d stash' Sg v0 hL,
        ih (Function.update (Function.update Sg (Kg.scratch .lhsOperand) stash')
              (Kg.reg rs) (d :: Sg (Kg.reg rs)))
           ({v0 with left := some d} : CompareState) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .lhsOperand
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rs
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma compare_core_restoreRight_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hR : Sg (Kg.scratch .rhsOperand) = d :: rest) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.restoreRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.restoreRight, ({v0 with right := some d} : CompareState),
          Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
            (Kg.reg rt) (d :: Sg (Kg.reg rt))⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.restoreRight, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hR]

lemma compare_core_restoreRight_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : CompareState)
    (hR : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    flipBindCompareCore rs rt
        (some (⟨some CompareCorePhase.restoreRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.done, ({v0 with right := none} : CompareState), Sg⟩ := by
  show (Turing.TM2.step (compareCoreProg rs rt))
      (⟨some CompareCorePhase.restoreRight, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState) = _
  simp [compareCoreProg, hR]

/-- Mirrors `compare_core_restoreLeft_loop` for `rt`/`rhsOperand`, landing at `done` — the fixed
    exit `compareCoreProg` needs (module docstring), matching `StmtTransport`'s requirement for
    every embedded local program. -/
lemma compare_core_restoreRight_loop (stash : List Digit) (Sg : ∀ k, List (Γg p k))
    (v0 : CompareState) (hR : Sg (Kg.scratch .rhsOperand) = stash) :
    (flipBindCompareCore rs rt)^[stash.length + 1]
        (some (⟨some CompareCorePhase.restoreRight, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.done, ({v0 with right := none} : CompareState),
          Function.update (Function.update Sg (Kg.scratch .rhsOperand) [])
            (Kg.reg rt) (stash.reverse ++ Sg (Kg.reg rt))⟩ := by
  induction stash generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      rw [update2_self Sg (Kg.scratch .rhsOperand) (Kg.reg rt) [] (Sg (Kg.reg rt)) hR rfl]
      exact compare_core_restoreRight_nil_exit rs rt Sg v0 hR
  | cons d stash' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        compare_core_restoreRight_cons rs rt d stash' Sg v0 hR,
        ih (Function.update (Function.update Sg (Kg.scratch .rhsOperand) stash')
              (Kg.reg rt) (d :: Sg (Kg.reg rt)))
           ({v0 with right := some d} : CompareState) (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .rhsOperand
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rt
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- The whole `compareCoreProg` run, `CompareCorePhase.scan` to `.done`, with a bound on the
    witness step count, combining `compare_core_scan_run_bounded` with the already-closed-form
    `restoreLeft`/`restoreRight` loop lengths. -/
lemma compare_core_run_bounded (hne : rs ≠ rt) (xs ys : List Digit) (Sg : ∀ k, List (Γg p k))
    (v0 : CompareState) (hRs : Sg (Kg.reg rs) = xs) (hRt : Sg (Kg.reg rt) = ys)
    (hL : Sg (Kg.scratch .lhsOperand) = []) (hR : Sg (Kg.scratch .rhsOperand) = []) :
    ∃ n, (flipBindCompareCore rs rt)^[n]
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
      = some ⟨some CompareCorePhase.done,
          ({v0 with left := none, right := none, acc := scanCompare v0.acc xs ys} : CompareState),
          Function.update (Function.update Sg (Kg.reg rs) xs) (Kg.reg rt) ys⟩ ∧
        n ≤ 2 * (xs.length + ys.length) + 5 := by
  have hneK : Kg.reg rs ≠ Kg.reg rt := fun h => hne (by injection h)
  obtain ⟨n1, hn1, hn1bound⟩ := compare_core_scan_run_bounded rs rt hne xs ys Sg v0 hRs hRt
  set Sg1 := Function.update
      (Function.update (Function.update (Function.update Sg (Kg.reg rs) []) (Kg.reg rt) [])
        (Kg.scratch .lhsOperand) (xs.reverse ++ Sg (Kg.scratch .lhsOperand)))
      (Kg.scratch .rhsOperand) (ys.reverse ++ Sg (Kg.scratch .rhsOperand)) with hSg1
  have hSg1Rs : Sg1 (Kg.reg rs) = [] := by rw [hSg1]; simp [Function.update, hneK]
  have hSg1Rt : Sg1 (Kg.reg rt) = [] := by rw [hSg1]; simp [Function.update]
  have hLstash : Sg1 (Kg.scratch .lhsOperand) = xs.reverse := by
    rw [hSg1]; simp [Function.update, hL]
  have h2 := compare_core_restoreLeft_loop rs rt xs.reverse Sg1
    ({v0 with left := none, right := none, acc := scanCompare v0.acc xs ys} : CompareState) hLstash
  set Sg2 := Function.update (Function.update Sg1 (Kg.scratch .lhsOperand) [])
      (Kg.reg rs) (xs.reverse.reverse ++ Sg1 (Kg.reg rs)) with hSg2
  have hRsFinal : Sg2 (Kg.reg rs) = xs := by
    rw [hSg2]; simp [Function.update, hSg1Rs]
  have hSg2Rt : Sg2 (Kg.reg rt) = [] := by rw [hSg2]; simp [Function.update, hSg1Rt, hneK.symm]
  have hSg2L : Sg2 (Kg.scratch .lhsOperand) = [] := by rw [hSg2]; simp [Function.update]
  have hRstash : Sg2 (Kg.scratch .rhsOperand) = ys.reverse := by
    rw [hSg2]; simp [Function.update, hSg1, hR]
  have h3 := compare_core_restoreRight_loop rs rt ys.reverse Sg2
    ({v0 with left := none, right := none, acc := scanCompare v0.acc xs ys} : CompareState) hRstash
  refine ⟨(ys.reverse.length + 1) + ((xs.reverse.length + 1) + n1), ?_, ?_⟩
  · have hsplit1 :
        (flipBindCompareCore rs rt)^[(ys.reverse.length + 1) + ((xs.reverse.length + 1) + n1)]
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
        = (flipBindCompareCore rs rt)^[ys.reverse.length + 1]
            ((flipBindCompareCore rs rt)^[(xs.reverse.length + 1) + n1]
              (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
                Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))) :=
      Function.iterate_add_apply _ _ _ _
    have hsplit2 : (flipBindCompareCore rs rt)^[(xs.reverse.length + 1) + n1]
        (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))
        = (flipBindCompareCore rs rt)^[xs.reverse.length + 1]
            ((flipBindCompareCore rs rt)^[n1]
              (some (⟨some CompareCorePhase.scan, v0, Sg⟩ :
                Turing.TM2.Cfg (Γg p) CompareCorePhase CompareState))) :=
      Function.iterate_add_apply _ _ _ _
    rw [hsplit1, hsplit2, hn1, h2, h3]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
    funext k
    by_cases hk1 : k = Kg.reg rs
    · subst hk1; simp [Function.update, hneK, hRsFinal]
    by_cases hk2 : k = Kg.reg rt
    · subst hk2; simp [Function.update, hSg2Rt]
    by_cases hk3 : k = Kg.scratch .lhsOperand
    · subst hk3; simp [Function.update, hk1, hk2, hSg2L, hL]
    by_cases hk4 : k = Kg.scratch .rhsOperand
    · subst hk4; simp [Function.update, hk1, hk2, hR]
    rw [hSg2, hSg1]
    simp [Function.update, hk1, hk2, hk3, hk4]
  · simp only [List.length_reverse]
    omega

end NPComplete.RAMToTM.Generic

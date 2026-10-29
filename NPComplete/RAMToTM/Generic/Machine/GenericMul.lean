module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.DigitMul
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `mul` realized against an arbitrary site's register triple

`mul rd rs rt`'s non-destructive snapshot prefix (`copyLhs`/`copyLhsRestore`/`reverseLhs`) is
verbatim `GenericAdd.lean`'s corresponding phases, retargeted to `MulState`/`MulPhase` — `rs` is
captured LSB-first into `lhsOperand`, exactly as `add`/`sub` do. `copyRhs`/`copyRhsRestore`
differ: only *one* reversal is needed (module docstring on `MulPhase`), since the multiplier must
be read MSB-first for the Horner scheme, and `rt`'s single pop-then-push pass already yields that
order directly on `rhsOperand`.

`clearDest` drains `rd`, which then serves as the *live accumulator* for the rest of the
instruction (no dedicated accumulator scratch is needed): `nextDigit` pops one multiplier digit
off `rhsOperand` into `factor`, shifts `rd` left by one digit-position (`push default`), and
`mulAddLoop` ripples `DigitMul.mulAddDigit` in lockstep over `lhsOperand` and `rd`, pushing the
result onto `sumScratch` while also stashing each popped `lhsOperand` digit onto `copyScratch` (so
`restoreLhs` can replay it back once the loop exits — the same "read-and-restore" trick
`copyLhs`/`copyLhsRestore` use, just run once per outer iteration instead of once total).
`skipZeros`/`copyRest` trim `sumScratch`'s raw MSB-first output and relocate it onto the
now-empty `rd`, mirroring `GenericSub.lean`'s trailing pair exactly, then loop back to
`nextDigit`. Once the multiplier is exhausted, `drainLhs` empties `lhsOperand` (the one scratch
stack left with content) before `done`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit mulAddDigit mulAddRaw mulRaw natToDigits)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd rs rt : Fin (regBound p))

/-- `mul`'s `Stmt` tree at an arbitrary register triple (module docstring). -/
def mulProg : MulPhase → Turing.TM2.Stmt (Γg p) MulPhase MulState
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
          (push (Kg.scratch .copyScratch) (fun s => s.a.getD default)
            (push (Kg.scratch .rhsOperand) (fun s => s.a.getD default)
              (goto (fun _ => .copyRhs))))
          (goto (fun _ => .copyRhsRestore)))
  | .copyRhsRestore =>
      pop (Kg.scratch .copyScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rt) (fun s => s.a.getD default)
            (goto (fun _ => .copyRhsRestore)))
          (load (fun _ => (⟨none, none, default, default⟩ : MulState))
            (goto (fun _ => .clearDest))))
  | .clearDest =>
      pop (Kg.reg rd) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .clearDest))
          (goto (fun _ => .nextDigit)))
  | .nextDigit =>
      peek (Kg.scratch .rhsOperand) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (pop (Kg.scratch .rhsOperand) (fun s ov => {s with a := ov})
            (push (Kg.reg rd) (fun _ => default)
              (load (fun s => {a := none, b := none, factor := s.a.getD default, carry := default})
                (goto (fun _ => .mulAddLoop)))))
          (goto (fun _ => .drainLhs)))
  | .mulAddLoop =>
      peek (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
        (peek (Kg.reg rd) (fun s ov => {s with b := ov})
          (branch (fun s => s.a.isSome || s.b.isSome || decide (s.carry.val ≠ 0))
            (pop (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
              (pop (Kg.reg rd) (fun s ov => {s with b := ov})
                (push (Kg.scratch .copyScratch) (fun s => s.a.getD default)
                  (push (Kg.scratch .sumScratch)
                      (fun s => (mulAddDigit (s.a.getD 0) s.factor (s.b.getD 0) s.carry).1)
                    (load (fun s => {s with
                        carry := (mulAddDigit (s.a.getD 0) s.factor (s.b.getD 0) s.carry).2})
                      (goto (fun _ => .mulAddLoop)))))))
            (goto (fun _ => .restoreLhs))))
  | .restoreLhs =>
      pop (Kg.scratch .copyScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.scratch .lhsOperand) (fun s => s.a.getD default)
            (goto (fun _ => .restoreLhs)))
          (goto (fun _ => .skipZeros)))
  | .skipZeros =>
      pop (Kg.scratch .sumScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (branch (fun s => decide ((s.a.getD default).val = 0))
            (goto (fun _ => .skipZeros))
            (push (Kg.reg rd) (fun s => s.a.getD default) (goto (fun _ => .copyRest))))
          (load (fun _ => (⟨none, none, default, default⟩ : MulState))
            (goto (fun _ => .nextDigit))))
  | .copyRest =>
      pop (Kg.scratch .sumScratch) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (push (Kg.reg rd) (fun s => s.a.getD default)
            (goto (fun _ => .copyRest)))
          (load (fun _ => (⟨none, none, default, default⟩ : MulState))
            (goto (fun _ => .nextDigit))))
  | .drainLhs =>
      pop (Kg.scratch .lhsOperand) (fun s ov => {s with a := ov})
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .drainLhs))
          (goto (fun _ => .done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindMul :
    Option (Turing.TM2.Cfg (Γg p) MulPhase MulState) →
      Option (Turing.TM2.Cfg (Γg p) MulPhase MulState) :=
  fun x => x.bind (Turing.TM2.step (mulProg rd rs rt))

/-! ## `copyLhs` / `copyLhsRestore` / `reverseLhs`: non-destructively snapshotting `rs`

The same shape as `GenericAdd.lean`'s corresponding section, stated for `MulState`/`MulPhase`/
`mulProg`/`flipBindMul`: `mul`'s snapshot prefix is the same as `add`'s (module docstring). -/

lemma flipBindMul_copyLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRs : Sg (Kg.reg rs) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyLhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rs) rest)
            (Kg.scratch .workRev) (d :: Sg (Kg.scratch .workRev)))
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRs]

lemma flipBindMul_copyLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRs : Sg (Kg.reg rs) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyLhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRs]

lemma mul_copyLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRs : Sg (Kg.reg rs) = src) :
    (flipBindMul rd rs rt)^[src.length + 1]
        (some (⟨some MulPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyLhsRestore, {v0 with a := none},
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
      exact flipBindMul_copyLhs_nil_exit rd rs rt Sg v0 hRs
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_copyLhs_cons rd rs rt d src' Sg v0 hRs,
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

lemma flipBindMul_copyLhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyLhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rs) (d :: Sg (Kg.reg rs))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

lemma flipBindMul_copyLhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.reverseLhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyLhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

lemma mul_copyLhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindMul rd rs rt)^[copyScratch.length + 1]
        (some (⟨some MulPhase.copyLhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.reverseLhs, {v0 with a := none},
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
      exact flipBindMul_copyLhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_copyLhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rs) (d :: Sg (Kg.reg rs))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rs
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

lemma mul_copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRs : Sg (Kg.reg rs) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindMul rd rs rt)^[2 * src.length + 2]
        (some (⟨some MulPhase.copyLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.reverseLhs, {v0 with a := none},
          Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, mul_copyLhs_loop rd rs rt src Sg v0 hRs]
  simp only [hSc, List.append_nil]
  have h2 := mul_copyLhsRestore_loop rd rs rt src.reverse
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

lemma flipBindMul_reverseLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hWr : Sg (Kg.scratch .workRev) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.reverseLhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .workRev) rest)
            (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hWr]

lemma flipBindMul_reverseLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hWr : Sg (Kg.scratch .workRev) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.reverseLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hWr]

lemma mul_reverseLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hWr : Sg (Kg.scratch .workRev) = src) :
    (flipBindMul rd rs rt)^[src.length + 1]
        (some (⟨some MulPhase.reverseLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhs, {v0 with a := none},
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
      exact flipBindMul_reverseLhs_nil_exit rd rs rt Sg v0 hWr
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_reverseLhs_cons rd rs rt d src' Sg v0 hWr,
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

/-! ## `copyRhs` / `copyRhsRestore`: non-destructively snapshotting `rt`, MSB-first

Unlike `copyLhs`, only *one* reversal is needed (module docstring on `MulPhase`): `copyRhs`
pushes each popped digit onto `rhsOperand` directly (not a `workRev` intermediate later flipped
back), so `rhsOperand` ends up holding `rt`'s digits MSB-first — exactly the order `nextDigit`
needs to read the multiplier front-to-back via `Horner`'s scheme. -/

lemma flipBindMul_copyRhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRt : Sg (Kg.reg rt) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhs, {v0 with a := some d},
          Function.update (Function.update (Function.update Sg (Kg.reg rt) rest)
            (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
            (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRt]

lemma flipBindMul_copyRhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRt : Sg (Kg.reg rt) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhsRestore, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRt]

/-- Draining register `rt`, prepending its reverse onto both `copyScratch` and `rhsOperand`
    directly (no `workRev` intermediate — module docstring). Mirrors `mul_copyLhs_loop`. -/
lemma mul_copyRhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRt : Sg (Kg.reg rt) = src) :
    (flipBindMul rd rs rt)^[src.length + 1]
        (some (⟨some MulPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhsRestore, {v0 with a := none},
          Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
            (Kg.scratch .copyScratch) (src.reverse ++ Sg (Kg.scratch .copyScratch)))
            (Kg.scratch .rhsOperand) (src.reverse ++ Sg (Kg.scratch .rhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
          (Kg.scratch .copyScratch) (Sg (Kg.scratch .copyScratch)))
          (Kg.scratch .rhsOperand) (Sg (Kg.scratch .rhsOperand)) = Sg := by
        funext k
        by_cases hk : k = Kg.reg rt
        · subst hk; simp [Function.update, hRt]
        · by_cases hk2 : k = Kg.scratch .copyScratch
          · subst hk2; simp [Function.update]
          · by_cases hk3 : k = Kg.scratch .rhsOperand
            · subst hk3; simp [Function.update]
            · simp [Function.update, hk, hk2, hk3]
      rw [hcollapse]
      exact flipBindMul_copyRhs_nil_exit rd rs rt Sg v0 hRt
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_copyRhs_cons rd rs rt d src' Sg v0 hRt,
        ih (Function.update (Function.update (Function.update Sg (Kg.reg rt) src')
              (Kg.scratch .copyScratch) (d :: Sg (Kg.scratch .copyScratch)))
              (Kg.scratch .rhsOperand) (d :: Sg (Kg.scratch .rhsOperand)))
           {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rt
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .copyScratch
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · by_cases hk3 : k = Kg.scratch .rhsOperand
          · subst hk3; simp [Function.update, List.reverse_cons, List.append_assoc]
          · simp [Function.update, hk, hk2, hk3]

lemma flipBindMul_copyRhsRestore_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhsRestore, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.reg rt) (d :: Sg (Kg.reg rt))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

lemma flipBindMul_copyRhsRestore_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.clearDest, (⟨none, none, default, default⟩ : MulState), Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRhsRestore, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

/-- Draining `copyScratch` restores register `rt` to `copyScratch.reverse ++ src`, landing at
    `clearDest` with `MulState` reset to canonical (mirrors `add`/`sub`'s single reset right
    before their main loop). Mirrors `mul_copyLhsRestore_loop`. -/
lemma mul_copyRhsRestore_loop (copyScratch : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = copyScratch) :
    (flipBindMul rd rs rt)^[copyScratch.length + 1]
        (some (⟨some MulPhase.copyRhsRestore, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.clearDest, (⟨none, none, default, default⟩ : MulState),
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
      exact flipBindMul_copyRhsRestore_nil_exit rd rs rt Sg v0 hSc
  | cons d cs' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_copyRhsRestore_cons rd rs rt d cs' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) cs')
              (Kg.reg rt) (d :: Sg (Kg.reg rt))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rt
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- Running the `rt` copy to completion: register `rt` is restored exactly, `rhsOperand` holds
    `rt`'s digits MSB-first, and `MulState` is reset to canonical (ready for `clearDest`).
    Mirrors `mul_copyLhs_phase`. -/
lemma mul_copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRt : Sg (Kg.reg rt) = src) (hSc : Sg (Kg.scratch .copyScratch) = []) :
    (flipBindMul rd rs rt)^[2 * src.length + 2]
        (some (⟨some MulPhase.copyRhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.clearDest, (⟨none, none, default, default⟩ : MulState),
          Function.update Sg (Kg.scratch .rhsOperand) (src.reverse ++ Sg (Kg.scratch .rhsOperand))⟩ := by
  have hcount : 2 * src.length + 2 = (src.reverse.length + 1) + (src.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hcount, Function.iterate_add_apply, mul_copyRhs_loop rd rs rt src Sg v0 hRt]
  simp only [hSc, List.append_nil]
  have h2 := mul_copyRhsRestore_loop rd rs rt src.reverse
    (Function.update (Function.update (Function.update Sg (Kg.reg rt) [])
      (Kg.scratch .copyScratch) src.reverse)
      (Kg.scratch .rhsOperand) (src.reverse ++ Sg (Kg.scratch .rhsOperand)))
    {v0 with a := none} (by simp)
  rw [h2]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, List.reverse_reverse]
  funext k
  by_cases hk : k = Kg.reg rt
  · subst hk; simp [Function.update, hRt]
  · by_cases hk2 : k = Kg.scratch .copyScratch
    · subst hk2; simp [Function.update, hk, hSc]
    · by_cases hk3 : k = Kg.scratch .rhsOperand
      · subst hk3; simp [Function.update, hk, hk2]
      · simp [Function.update, hk, hk2, hk3]

/-! ## `clearDest`: draining `rd` before it becomes the live accumulator -/

lemma flipBindMul_clearDest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.clearDest, {v0 with a := some d},
          Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRd]

lemma flipBindMul_clearDest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.clearDest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRd]

/-- Draining register `rd`, discarding every digit: mirrors `GenericAdd.add_clearDest_loop`. -/
lemma mul_clearDest_loop (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindMul rd rs rt)^[dest.length + 1]
        (some (⟨some MulPhase.clearDest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, {v0 with a := none},
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
      exact flipBindMul_clearDest_nil_exit rd rs rt Sg v0 hRd
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_clearDest_cons rd rs rt d ds' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) ds') {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## `mulAddLoop`: `DigitMul.mulAddRaw`'s fused ripple, retargeted to `lhsOperand`/`rd`

`rd` itself plays `mulAddRaw`'s `acc` role (module docstring): the loop pops it directly, no
separate accumulator scratch. -/

/-- `mulAddLoop` exit: both `lhsOperand` and `rd` exhausted, no carry pending. Mirrors
    `GenericAdd.addLoop_step_done`. -/
lemma mulAddLoop_step_done (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hc : v0.carry.val = 0)
    (hLhs : Sg (Kg.scratch .lhsOperand) = []) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    (Turing.TM2.step (mulProg rd rs rt))
        (⟨some MulPhase.mulAddLoop, v0, Sg⟩ : Turing.TM2.Cfg (Γg p) MulPhase MulState)
      = some ⟨some MulPhase.restoreLhs, {v0 with a := none, b := none}, Sg⟩ := by
  have hc' : v0.carry = (0 : Digit) := Fin.ext (by simpa using hc)
  simp [mulProg, hLhs, hRd, hc']

/-- `mulAddLoop`'s general step, mirroring `GenericAdd.addLoop_step_general`: either operand may
    be exhausted (`.headD`/`.tail` default harmlessly on `[]`), matching `DigitMul.mulAddRaw`'s
    own recursive step exactly. -/
lemma mulAddLoop_step_general (Sg : ∀ k, List (Γg p k)) (srcA accSrc : List Digit)
    (v0 : MulState) (hLhs : Sg (Kg.scratch .lhsOperand) = srcA)
    (hRd : Sg (Kg.reg rd) = accSrc)
    (hbase : ¬ (srcA = [] ∧ accSrc = [] ∧ v0.carry.val = 0)) :
    (Turing.TM2.step (mulProg rd rs rt))
        (⟨some MulPhase.mulAddLoop, v0, Sg⟩ : Turing.TM2.Cfg (Γg p) MulPhase MulState)
      = some ⟨some MulPhase.mulAddLoop,
          {v0 with
            a := srcA.head?, b := accSrc.head?,
            carry := (mulAddDigit (srcA.headD 0) v0.factor (accSrc.headD 0) v0.carry).2},
          Function.update
            (Function.update
              (Function.update (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
                (Kg.reg rd) accSrc.tail)
              (Kg.scratch .copyScratch) (srcA.headD 0 :: Sg (Kg.scratch .copyScratch)))
            (Kg.scratch .sumScratch)
            ((mulAddDigit (srcA.headD 0) v0.factor (accSrc.headD 0) v0.carry).1 ::
              Sg (Kg.scratch .sumScratch))⟩ := by
  rcases srcA with _ | ⟨da, ta⟩ <;> rcases accSrc with _ | ⟨db, tb⟩ <;>
    simp only [List.headD_nil, List.headD_cons, List.head?_nil, List.head?_cons, List.tail_nil,
      List.tail_cons]
  · by_cases hcz : v0.carry.val = 0
    · exact absurd ⟨rfl, rfl, hcz⟩ hbase
    · have hcz' : v0.carry ≠ (0 : Digit) := fun h => hcz (by rw [h]; rfl)
      simp [mulProg, hLhs, hRd, hcz']
  · simp [mulProg, hLhs, hRd]
  · simp [mulProg, hLhs, hRd]
  · simp [mulProg, hLhs, hRd]

/-- Running `mulAddLoop` to completion: drains `lhsOperand` (`srcA`, possibly padded with extra
    zero pops beyond its own length once `accSrc` outlasts it — module docstring on
    `DigitMul.mulAddTraceA`) and register `rd` (`accSrc`), leaving the reverse of the
    `DigitMul.mulAddRaw` result prepended onto `sumScratch` and the reverse of the possibly padded
    `DigitMul.mulAddTraceA` trace prepended onto `copyScratch`. Mirrors `GenericAdd.addLoop_run`. -/
lemma mulAddLoop_run (Sg : ∀ k, List (Γg p k)) (srcA accSrc : List Digit) (factor carry : Digit)
    (sa sb : Option Digit) (hLhs : Sg (Kg.scratch .lhsOperand) = srcA)
    (hRd : Sg (Kg.reg rd) = accSrc) :
    (flipBindMul rd rs rt)^[(mulAddRaw srcA accSrc factor carry).length + 1]
        (some (⟨some MulPhase.mulAddLoop, ⟨sa, sb, factor, carry⟩, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.restoreLhs, ⟨none, none, factor, default⟩,
          Function.update
            (Function.update
              (Function.update (Function.update Sg (Kg.scratch .lhsOperand) []) (Kg.reg rd) [])
              (Kg.scratch .copyScratch)
              ((mulAddTraceA srcA accSrc factor carry).reverse ++ Sg (Kg.scratch .copyScratch)))
            (Kg.scratch .sumScratch)
            ((mulAddRaw srcA accSrc factor carry).reverse ++ Sg (Kg.scratch .sumScratch))⟩ := by
  induction srcA, accSrc, carry using mulAddRaw.induct (d := factor) generalizing Sg sa sb with
  | case1 srcA accSrc carry hbase =>
      obtain ⟨hA, hB, hc⟩ := hbase
      subst hA; subst hB
      have hc0 : carry.val = 0 := hc
      rw [show mulAddRaw ([] : List Digit) [] factor carry = [] by rw [mulAddRaw]; simp [hc0]]
      rw [show mulAddTraceA ([] : List Digit) [] factor carry = [] by
        rw [mulAddTraceA]; simp [hc0]]
      simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append]
      show (Turing.TM2.step (mulProg rd rs rt))
          (⟨some MulPhase.mulAddLoop, ⟨sa, sb, factor, carry⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
      have hdefault : carry = (default : Digit) := by
        have : (default : Digit).val = 0 := rfl
        exact Fin.ext (hc0.trans this.symm)
      rw [mulAddLoop_step_done rd rs rt Sg ⟨sa, sb, factor, carry⟩ hc0 hLhs hRd, hdefault]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      rw [Function.update_comm (show (Kg.scratch .lhsOperand : Kg p) ≠ Kg.reg rd by simp),
        (Function.update_eq_self_iff (f := Sg) (a := Kg.reg rd)).2 hRd.symm,
        (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .lhsOperand)).2 hLhs.symm,
        (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .copyScratch)).2 rfl,
        (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .sumScratch)).2 rfl]
  | case2 srcA accSrc carry hbase dc ih =>
      have hunfoldR : mulAddRaw srcA accSrc factor carry = dc.1 :: mulAddRaw srcA.tail accSrc.tail
          factor dc.2 := by rw [mulAddRaw, dite_eq_right hbase]
      have hunfoldT : mulAddTraceA srcA accSrc factor carry
          = srcA.headD 0 :: mulAddTraceA srcA.tail accSrc.tail factor dc.2 := by
        rw [mulAddTraceA, dite_eq_right hbase]
      rw [hunfoldR, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Function.iterate_succ_apply]
      show (flipBindMul rd rs rt)^[_]
          (flipBindMul rd rs rt (some (⟨some MulPhase.mulAddLoop, ⟨sa, sb, factor, carry⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) MulPhase MulState))) = _
      set Sg1 := Function.update
          (Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) srcA.tail)
              (Kg.reg rd) accSrc.tail)
            (Kg.scratch .copyScratch) (srcA.headD 0 :: Sg (Kg.scratch .copyScratch)))
          (Kg.scratch .sumScratch) (dc.1 :: Sg (Kg.scratch .sumScratch)) with hSg1
      have hstep : flipBindMul rd rs rt
          (some (⟨some MulPhase.mulAddLoop, ⟨sa, sb, factor, carry⟩, Sg⟩ :
            Turing.TM2.Cfg (Γg p) MulPhase MulState))
          = some ⟨some MulPhase.mulAddLoop, ⟨srcA.head?, accSrc.head?, factor, dc.2⟩, Sg1⟩ := by
        show (Turing.TM2.step (mulProg rd rs rt))
            (⟨some MulPhase.mulAddLoop, ⟨sa, sb, factor, carry⟩, Sg⟩ :
              Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
        exact mulAddLoop_step_general rd rs rt Sg srcA accSrc ⟨sa, sb, factor, carry⟩ hLhs hRd
          hbase
      rw [hstep]
      have hLhs' : Sg1 (Kg.scratch .lhsOperand) = srcA.tail := by rw [hSg1]; simp [Function.update]
      have hRd' : Sg1 (Kg.reg rd) = accSrc.tail := by rw [hSg1]; simp [Function.update]
      have hCopy1 : Sg1 (Kg.scratch .copyScratch)
          = srcA.headD 0 :: Sg (Kg.scratch .copyScratch) := by
        rw [hSg1]
        simp [Function.update]
      have hSum1 : Sg1 (Kg.scratch .sumScratch)
          = dc.1 :: Sg (Kg.scratch .sumScratch) := by
        rw [hSg1]
        simp [Function.update]
      rw [ih Sg1 srcA.head? accSrc.head? hLhs' hRd']
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      rw [hunfoldT, hCopy1, hSum1, hSg1]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [Function.update_comm (show (Kg.scratch ScratchKind.sumScratch : Kg p) ≠ Kg.scratch .lhsOperand by simp),
        Function.update_comm (show (Kg.scratch ScratchKind.copyScratch : Kg p) ≠ Kg.scratch .lhsOperand by simp),
        Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .lhsOperand by simp),
        Function.update_idem,
        Function.update_comm (show (Kg.scratch ScratchKind.sumScratch : Kg p) ≠ Kg.reg rd by simp),
        Function.update_comm (show (Kg.scratch ScratchKind.copyScratch : Kg p) ≠ Kg.reg rd by simp),
        Function.update_idem,
        Function.update_comm (show (Kg.scratch ScratchKind.sumScratch : Kg p) ≠ Kg.scratch .copyScratch by simp),
        Function.update_idem, Function.update_idem]

/-! ## `restoreLhs`: replaying `copyScratch` back onto `lhsOperand` -/

lemma flipBindMul_restoreLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hSc : Sg (Kg.scratch .copyScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.restoreLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.restoreLhs, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) rest)
            (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.restoreLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

lemma flipBindMul_restoreLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.restoreLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.skipZeros, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.restoreLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSc]

/-- Draining `copyScratch`, prepending its reverse onto `lhsOperand`. Mirrors
    `mul_reverseLhs_loop`. -/
lemma mul_restoreLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSc : Sg (Kg.scratch .copyScratch) = src) :
    (flipBindMul rd rs rt)^[src.length + 1]
        (some (⟨some MulPhase.restoreLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.skipZeros, {v0 with a := none},
          Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
            (Kg.scratch .lhsOperand) (src.reverse ++ Sg (Kg.scratch .lhsOperand))⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
          (Kg.scratch .lhsOperand) (Sg (Kg.scratch .lhsOperand)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .copyScratch
        · subst hk; simp [Function.update, hSc]
        · by_cases hk2 : k = Kg.scratch .lhsOperand
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindMul_restoreLhs_nil_exit rd rs rt Sg v0 hSc
  | cons d src' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_restoreLhs_cons rd rs rt d src' Sg v0 hSc,
        ih (Function.update (Function.update Sg (Kg.scratch .copyScratch) src')
              (Kg.scratch .lhsOperand) (d :: Sg (Kg.scratch .lhsOperand))) {v0 with a := some d}
           (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .copyScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.scratch .lhsOperand
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-! ## `skipZeros` / `copyRest`: trimming `sumScratch`'s MSB-first output onto `rd`

Verbatim `GenericSub.lean`'s trailing pair, except the exit (both here and at `copyRest`'s own
drain-to-empty) is `nextDigit` (loop back for the next multiplier digit) rather than `done`. -/

lemma flipBindMul_skipZeros_zero (d : Digit) (rest : List Digit) (hd : d.val = 0)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hSum : Sg (Kg.scratch .sumScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.skipZeros, {v0 with a := some d},
          Function.update Sg (Kg.scratch .sumScratch) rest⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  have hd' : d = (0 : Digit) := Fin.ext hd
  simp [mulProg, hSum, hd']

lemma flipBindMul_skipZeros_nonzero (d : Digit) (rest : List Digit) (hd : d.val ≠ 0)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hSum : Sg (Kg.scratch .sumScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRest, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .sumScratch) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  have hd' : d ≠ (0 : Digit) := fun h => hd (by rw [h]; rfl)
  simp [mulProg, hSum, hd']

lemma flipBindMul_skipZeros_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSum : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.skipZeros, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSum]

lemma flipBindMul_copyRest_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hSum : Sg (Kg.scratch .sumScratch) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRest, {v0 with a := some d},
          Function.update (Function.update Sg (Kg.scratch .sumScratch) rest)
            (Kg.reg rd) (d :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSum]

lemma flipBindMul_copyRest_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSum : Sg (Kg.scratch .sumScratch) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.copyRest, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hSum]

/-- Draining `sumScratch` from `copyRest`, prepending its reverse onto `rd`. Mirrors
    `GenericSub.copyRest_loop`. -/
lemma mul_copyRest_loop (sumS : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSum : Sg (Kg.scratch .sumScratch) = sumS) :
    (flipBindMul rd rs rt)^[sumS.length + 1]
        (some (⟨some MulPhase.copyRest, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState),
          Function.update (Function.update Sg (Kg.scratch .sumScratch) [])
            (Kg.reg rd) (sumS.reverse ++ Sg (Kg.reg rd))⟩ := by
  induction sumS generalizing Sg v0 with
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
      exact flipBindMul_copyRest_nil_exit rd rs rt Sg v0 hSum
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_copyRest_cons rd rs rt d ds' Sg v0 hSum,
        ih (Function.update (Function.update Sg (Kg.scratch .sumScratch) ds')
              (Kg.reg rd) (d :: Sg (Kg.reg rd))) {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .sumScratch
      · subst hk; simp [Function.update]
      · by_cases hk2 : k = Kg.reg rd
        · subst hk2; simp [Function.update, List.reverse_cons, List.append_assoc]
        · simp [Function.update, hk, hk2]

/-- `skipZeros` fully run: discards a leading (most-significant-first) run of zero digits, then
    relocates whatever remains onto `rd` (mirroring `mul_copyRest_loop`). Produces exactly
    `dropWhile`/`reverse` of `sumScratch`, prepended onto `rd`. Mirrors
    `GenericSub.skipZeros_phase`. -/
lemma mul_skipZeros_phase (sumS : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hSum : Sg (Kg.scratch .sumScratch) = sumS) :
    (flipBindMul rd rs rt)^[sumS.length + 1]
        (some (⟨some MulPhase.skipZeros, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState),
          Function.update (Function.update Sg (Kg.scratch .sumScratch) [])
            (Kg.reg rd)
            ((sumS.dropWhile (fun d => decide (d.val = 0))).reverse ++ Sg (Kg.reg rd))⟩ := by
  induction sumS generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil, List.dropWhile_nil, List.reverse_nil, List.nil_append]
      have hcollapse : Function.update (Function.update Sg (Kg.scratch .sumScratch) [])
          (Kg.reg rd) (Sg (Kg.reg rd)) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .sumScratch
        · subst hk; simp [Function.update, hSum]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      rw [hcollapse]
      exact flipBindMul_skipZeros_nil_exit rd rs rt Sg v0 hSum
  | cons d ds' ih =>
      by_cases hd : d.val = 0
      · rw [List.dropWhile_cons]
        simp only [hd, decide_true, ite_true]
        rw [List.length_cons, Function.iterate_succ_apply,
          flipBindMul_skipZeros_zero rd rs rt d ds' hd Sg v0 hSum,
          ih (Function.update Sg (Kg.scratch .sumScratch) ds') {v0 with a := some d} (by simp)]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        by_cases hk : k = Kg.scratch .sumScratch
        · subst hk; simp [Function.update]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]
      · rw [List.dropWhile_cons]
        simp only [hd, decide_false]
        rw [List.length_cons, Function.iterate_succ_apply,
          flipBindMul_skipZeros_nonzero rd rs rt d ds' hd Sg v0 hSum]
        have h2 := mul_copyRest_loop rd rs rt ds'
          (Function.update (Function.update Sg (Kg.scratch .sumScratch) ds')
            (Kg.reg rd) (d :: Sg (Kg.reg rd))) {v0 with a := some d} (by simp)
        rw [h2]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        by_cases hk : k = Kg.scratch .sumScratch
        · subst hk; simp [Function.update]
        · by_cases hk2 : k = Kg.reg rd
          · subst hk2; simp [Function.update]
          · simp [Function.update, hk, hk2]

/-! ## `nextDigit`: pop one multiplier digit, shift the live accumulator -/

lemma flipBindMul_nextDigit_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hRhs : Sg (Kg.scratch .rhsOperand) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.nextDigit, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.mulAddLoop, ⟨none, none, d, default⟩,
          Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
            (Kg.reg rd) (default :: Sg (Kg.reg rd))⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.nextDigit, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRhs]

lemma flipBindMul_nextDigit_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.nextDigit, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.drainLhs, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.nextDigit, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hRhs]

/-! ## `drainLhs`: emptying `lhsOperand` once the multiplier is exhausted -/

lemma flipBindMul_drainLhs_cons (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hLhs : Sg (Kg.scratch .lhsOperand) = d :: rest) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.drainLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.drainLhs, {v0 with a := some d},
          Function.update Sg (Kg.scratch .lhsOperand) rest⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.drainLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hLhs]

lemma flipBindMul_drainLhs_nil_exit
    (Sg : ∀ k, List (Γg p k)) (v0 : MulState) (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit)) :
    flipBindMul rd rs rt
        (some (⟨some MulPhase.drainLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.done, {v0 with a := none}, Sg⟩ := by
  show (Turing.TM2.step (mulProg rd rs rt))
      (⟨some MulPhase.drainLhs, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState) = _
  simp [mulProg, hLhs]

/-- Draining `lhsOperand`, discarding every digit. Mirrors `mul_clearDest_loop`. -/
lemma mul_drainLhs_loop (src : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : MulState)
    (hLhs : Sg (Kg.scratch .lhsOperand) = src) :
    (flipBindMul rd rs rt)^[src.length + 1]
        (some (⟨some MulPhase.drainLhs, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.done, {v0 with a := none},
          Function.update Sg (Kg.scratch .lhsOperand) []⟩ := by
  induction src generalizing Sg v0 with
  | nil =>
      simp only [List.length_nil]
      have hcollapse : Function.update Sg (Kg.scratch .lhsOperand) ([] : List Digit) = Sg := by
        funext k
        by_cases hk : k = Kg.scratch .lhsOperand
        · subst hk; simp [Function.update, hLhs]
        · simp [Function.update, hk]
      rw [hcollapse]
      exact flipBindMul_drainLhs_nil_exit rd rs rt Sg v0 hLhs
  | cons d ds' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindMul_drainLhs_cons rd rs rt d ds' Sg v0 hLhs,
        ih (Function.update Sg (Kg.scratch .lhsOperand) ds') {v0 with a := some d} (by simp)]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
      funext k
      by_cases hk : k = Kg.scratch .lhsOperand
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]

/-! ## One full outer iteration: `nextDigit` through back to `nextDigit` -/

/-- One full outer iteration, from a clean `MulState` back to a clean `MulState`: pops one
    multiplier digit `d` off `rhsOperand`, runs the fused multiply-accumulate ripple
    (`mulAddLoop_run`), restores `lhsOperand` (`mul_restoreLhs_loop`), and trims/relocates the result
    onto `rd` (`mul_skipZeros_phase`) — landing exactly on `DigitMul.mulOuterStep`'s own Horner
    step. `lhsOperand`'s content afterward is `DigitMul.mulAddTraceA`'s (possibly zero-padded,
    module docstring there) trace, not necessarily `L` itself — only its *value* is preserved
    (`digitsToNat_mulAddTraceA`), which is all `mul_outer_loop_run_bounded`'s own induction needs. -/
lemma mul_one_outer_iter_run (Sg : ∀ k, List (Γg p k)) (L rest : List Digit) (d : Digit)
    (accVal : ℕ) (hLhs : Sg (Kg.scratch .lhsOperand) = L)
    (hRd : Sg (Kg.reg rd) = natToDigits accVal) (hRhs : Sg (Kg.scratch .rhsOperand) = d :: rest)
    (hCopy : Sg (Kg.scratch .copyScratch) = []) (hSum : Sg (Kg.scratch .sumScratch) = []) :
    (flipBindMul rd rs rt)^[
        ((mulAddRaw L (default :: natToDigits accVal) d default).length + 1)
          + (((mulAddTraceA L (default :: natToDigits accVal) d default).length + 1)
            + (((mulAddRaw L (default :: natToDigits accVal) d default).length + 1) + 1))]
        (some (⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState),
          Function.update
            (Function.update
              (Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
                (Kg.reg rd) (mulOuterStep L d (natToDigits accVal)))
              (Kg.scratch .lhsOperand)
              (mulAddTraceA L (default :: natToDigits accVal) d default))
            (Kg.scratch .copyScratch) []⟩ := by
  have run0 : (flipBindMul rd rs rt)^[1]
      (some (⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
        Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.mulAddLoop, (⟨none, none, d, default⟩ : MulState),
          Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
            (Kg.reg rd) (default :: Sg (Kg.reg rd))⟩ := by
    rw [Function.iterate_one]
    exact flipBindMul_nextDigit_cons rd rs rt d rest Sg (⟨none, none, default, default⟩ : MulState)
      hRhs
  set Sg1 := Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
      (Kg.reg rd) (default :: Sg (Kg.reg rd)) with hSg1
  have hLhs1 : Sg1 (Kg.scratch .lhsOperand) = L := by
    rw [hSg1]; simp [Function.update, hLhs]
  have hRd1 : Sg1 (Kg.reg rd) = default :: natToDigits accVal := by
    rw [hSg1, hRd]; simp [Function.update]
  have hCopy1 : Sg1 (Kg.scratch .copyScratch) = [] := by
    rw [hSg1]
    simp [Function.update, hCopy]
  have hSum1 : Sg1 (Kg.scratch .sumScratch) = [] := by
    rw [hSg1]
    simp [Function.update, hSum]
  have run1 := mulAddLoop_run rd rs rt Sg1 L (default :: natToDigits accVal) d default none none
    hLhs1 hRd1
  set Sg2 := Function.update
      (Function.update
        (Function.update (Function.update Sg1 (Kg.scratch .lhsOperand) []) (Kg.reg rd) [])
        (Kg.scratch .copyScratch)
        ((mulAddTraceA L (default :: natToDigits accVal) d default).reverse ++
          Sg1 (Kg.scratch .copyScratch)))
      (Kg.scratch .sumScratch)
      ((mulAddRaw L (default :: natToDigits accVal) d default).reverse ++
        Sg1 (Kg.scratch .sumScratch)) with hSg2
  have hCopy2 : Sg2 (Kg.scratch .copyScratch)
      = (mulAddTraceA L (default :: natToDigits accVal) d default).reverse := by
    rw [hSg2]; simp [Function.update, hSg1, hCopy]
  have run2 := mul_restoreLhs_loop rd rs rt
    (mulAddTraceA L (default :: natToDigits accVal) d default).reverse Sg2
    (⟨none, none, d, default⟩ : MulState) hCopy2
  set Sg3 := Function.update
      (Function.update Sg2 (Kg.scratch .copyScratch) [])
      (Kg.scratch .lhsOperand)
      ((mulAddTraceA L (default :: natToDigits accVal) d default).reverse.reverse ++
        Sg2 (Kg.scratch .lhsOperand)) with hSg3
  have hSum3 : Sg3 (Kg.scratch .sumScratch)
      = (mulAddRaw L (default :: natToDigits accVal) d default).reverse := by
    rw [hSg3]; simp [Function.update, hSg2, hSg1, hSum]
  have run3 := mul_skipZeros_phase rd rs rt
    (mulAddRaw L (default :: natToDigits accVal) d default).reverse Sg3
    (⟨none, none, d, default⟩ : MulState) hSum3
  rw [List.length_reverse] at run2 run3
  set NR := (mulAddRaw L (default :: natToDigits accVal) d default).length with hNR
  set NT := (mulAddTraceA L (default :: natToDigits accVal) d default).length with hNT
  rw [Function.iterate_add_apply (flipBindMul rd rs rt) (NR + 1) ((NT + 1) + ((NR + 1) + 1)),
    Function.iterate_add_apply (flipBindMul rd rs rt) (NT + 1) ((NR + 1) + 1),
    Function.iterate_add_apply (flipBindMul rd rs rt) (NR + 1) 1,
    run0, run1, run2, run3]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and, mulOuterStep]
  have hLhs2 : Sg2 (Kg.scratch .lhsOperand) = [] := by
    rw [hSg2]
    simp [Function.update]
  have hRd3 : Sg3 (Kg.reg rd) = [] := by
    rw [hSg3, hSg2]
    simp [Function.update]
  rw [hRd3, List.append_nil]
  rw [hSg3, hLhs2, hSg2, hCopy1, hSum1, hSg1]
  simp only [List.append_nil, List.reverse_reverse]
  rw [Function.update_comm (show (Kg.scratch .sumScratch : Kg p) ≠ Kg.reg rd by simp),
    Function.update_comm (show (Kg.scratch .lhsOperand : Kg p) ≠ Kg.reg rd by simp),
    Function.update_comm (show (Kg.scratch .copyScratch : Kg p) ≠ Kg.reg rd by simp),
    Function.update_comm (show (Kg.scratch .sumScratch : Kg p) ≠ Kg.reg rd by simp),
    Function.update_comm (show (Kg.scratch .copyScratch : Kg p) ≠ Kg.reg rd by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .lhsOperand : Kg p) ≠ Kg.reg rd by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .copyScratch : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_comm (show (Kg.scratch .sumScratch : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_comm (show (Kg.scratch .copyScratch : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .sumScratch : Kg p) ≠ Kg.scratch .copyScratch by simp),
    Function.update_idem,
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .copyScratch : Kg p) ≠ Kg.scratch .sumScratch by simp)]
  rw [Function.update_comm (show (Kg.scratch .lhsOperand : Kg p) ≠ Kg.scratch .sumScratch by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .sumScratch by simp),
    Function.update_comm (show (Kg.scratch .rhsOperand : Kg p) ≠ Kg.scratch .sumScratch by simp),
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .sumScratch)).2 hSum.symm]

/-! ## The outer loop: consuming the whole multiplier -/

/-- The outer loop's run, with a step-count bound. Unlike `add`/`sub`/the compare core, `mul` is
    genuinely `O(n^2)`: the fused multiply-accumulate ripple's own cost grows every outer
    iteration as the Horner accumulator grows. Two invariants make this tractable: (1)
    `totalVal` — the recursive invariant keeps
    `rsVal * digitsToNat srcBmsb.reverse + accVal * 16 ^ srcBmsb.length`
    equal to `totalVal` at every midpoint (`totalVal` is fixed at the call site), so
    `accVal ≤ totalVal` follows (both summands are nonnegative and `16^n ≥ 1`); (2)
    `L.length + srcBmsb.length ≤ B` — `L`'s
    length only grows via `mulAddRaw_length_le`'s `max(·,·)+1` shape, which telescopes to a
    bound linear in `bitLen totalVal` plus the *remaining* iteration count (`fullLen` is the
    iteration count at the outermost call; `B` must have `bitLen totalVal + 1 + fullLen` of
    slack for the invariant to survive every step). -/
lemma mul_outer_loop_run_bounded (Sg : ∀ k, List (Γg p k)) (rsVal accVal totalVal fullLen B : ℕ)
    (L : List Digit) (hLval : digitsToNat L = rsVal) (srcBmsb : List Digit)
    (hInv : totalVal = rsVal * digitsToNat srcBmsb.reverse + accVal * 16 ^ srcBmsb.length)
    (hSrcLen : srcBmsb.length ≤ fullLen) (hLBound : L.length + srcBmsb.length ≤ B)
    (hBF : bitLen totalVal + 1 + fullLen ≤ B)
    (hLhs : Sg (Kg.scratch .lhsOperand) = L) (hRd : Sg (Kg.reg rd) = natToDigits accVal)
    (hRhs : Sg (Kg.scratch .rhsOperand) = srcBmsb) (hCopy : Sg (Kg.scratch .copyScratch) = [])
    (hSum : Sg (Kg.scratch .sumScratch) = []) :
    ∃ N Sg', (flipBindMul rd rs rt)^[N]
        (some (⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), Sg'⟩
      ∧ Sg' (Kg.scratch .rhsOperand) = []
      ∧ Sg' (Kg.reg rd) = mulRawAux (natToDigits rsVal) (natToDigits accVal) srcBmsb
      ∧ (∃ L', digitsToNat L' = rsVal ∧ Sg' (Kg.scratch .lhsOperand) = L' ∧ L'.length ≤ B)
      ∧ Sg' (Kg.scratch .copyScratch) = []
      ∧ Sg' (Kg.scratch .sumScratch) = []
      ∧ (∀ k, k ≠ Kg.reg rd → k ≠ Kg.scratch .rhsOperand → k ≠ Kg.scratch .lhsOperand →
          k ≠ Kg.scratch .copyScratch → k ≠ Kg.scratch .sumScratch → Sg' k = Sg k)
      ∧ N ≤ (srcBmsb.length + 1) * (3 * (B + 2) + 1) := by
  induction srcBmsb generalizing Sg L accVal with
  | nil =>
      refine ⟨0, Sg, rfl, ?_, ?_, ⟨L, hLval, hLhs, by simpa using hLBound⟩, hCopy, hSum,
        fun k _ _ _ _ _ => rfl, by simp⟩
      · rw [hRhs]
      · rw [hRd, mulRawAux]
  | cons d rest ih =>
      have hiter := mul_one_outer_iter_run rd rs rt Sg L rest d accVal hLhs hRd hRhs hCopy hSum
      set Sg1 := Function.update
          (Function.update
            (Function.update (Function.update Sg (Kg.scratch .rhsOperand) rest)
              (Kg.reg rd) (mulOuterStep L d (natToDigits accVal)))
            (Kg.scratch .lhsOperand)
            (mulAddTraceA L (default :: natToDigits accVal) d default))
          (Kg.scratch .copyScratch) [] with hSg1
      have hRhs1 : Sg1 (Kg.scratch .rhsOperand) = rest := by rw [hSg1]; simp [Function.update]
      have hCopy1 : Sg1 (Kg.scratch .copyScratch) = [] := by rw [hSg1]; simp [Function.update]
      have hSum1 : Sg1 (Kg.scratch .sumScratch) = [] := by rw [hSg1]; simp [Function.update, hSum]
      have hLhs1 : Sg1 (Kg.scratch .lhsOperand)
          = mulAddTraceA L (default :: natToDigits accVal) d default := by
        rw [hSg1]; simp [Function.update]
      have hLval1 : digitsToNat (mulAddTraceA L (default :: natToDigits accVal) d default) = rsVal := by
        rw [digitsToNat_mulAddTraceA]; exact hLval
      obtain ⟨accVal', hAccVal'⟩ : ∃ accVal', mulOuterStep L d (natToDigits accVal) = natToDigits accVal' :=
        ⟨digitsToNat L * d.val + 16 * digitsToNat (natToDigits accVal),
          mulOuterStep_eq_natToDigits L d (natToDigits accVal)⟩
      have hRd1 : Sg1 (Kg.reg rd) = natToDigits accVal' := by rw [hSg1]; simp [Function.update, hAccVal']
      have haccVal'eq : accVal' = rsVal * d.val + 16 * accVal := by
        have := hAccVal'
        rw [mulOuterStep_eq_natToDigits, hLval, digitsToNat_natToDigits] at this
        exact natToDigits_injective this.symm
      have hInv1 : totalVal = rsVal * digitsToNat rest.reverse + accVal' * 16 ^ rest.length := by
        have hrev : digitsToNat (d :: rest).reverse
            = digitsToNat rest.reverse + d.val * 16 ^ rest.length := by
          rw [List.reverse_cons, digitsToNat_append_singleton, List.length_reverse]
        have hpow : (16:ℕ) ^ (rest.length + 1) = 16 ^ rest.length * 16 := by ring
        rw [hInv, List.length_cons, haccVal'eq, hrev, hpow]; ring
      have hSrcLen1 : rest.length ≤ fullLen := by
        have : rest.length + 1 ≤ fullLen := by simpa [List.length_cons] using hSrcLen
        omega
      have haccValLe : accVal ≤ totalVal := by
        have hpow1 : (1:ℕ) ≤ 16 ^ (d :: rest).length := Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith [hInv, hpow1, Nat.zero_le (rsVal * digitsToNat (d :: rest).reverse)]
      have hFbound : bitLen accVal ≤ bitLen totalVal := bitLen_le_of_le haccValLe
      have hNRle : (mulAddRaw L (default :: natToDigits accVal) d default).length
          ≤ max L.length (bitLen totalVal + 1) + 1 := by
        have h1 := mulAddRaw_length_le L (default :: natToDigits accVal) d default
        have h2 : (default :: natToDigits accVal).length ≤ bitLen totalVal + 1 := by
          simp only [List.length_cons]
          have := natToDigits_length_le_bitLen accVal
          omega
        omega
      have hL1len : (mulAddTraceA L (default :: natToDigits accVal) d default).length
          = (mulAddRaw L (default :: natToDigits accVal) d default).length :=
        mulAddTraceA_length L (default :: natToDigits accVal) d default
      have hLBound1 : (mulAddTraceA L (default :: natToDigits accVal) d default).length
          + rest.length ≤ B := by
        rw [hL1len]
        have hsrc : (d :: rest).length = rest.length + 1 := rfl
        omega
      obtain ⟨N2, Sg2, hrun2, hRhs2, hRd2, hLhs2, hCopy2, hSum2, hframe2, hN2bound⟩ :=
        ih Sg1 accVal' (mulAddTraceA L (default :: natToDigits accVal) d default) hLval1
          hInv1 hSrcLen1 hLBound1 hLhs1 hRd1 hRhs1 hCopy1 hSum1
      set M := (mulAddRaw L (default :: natToDigits accVal) d default).length + 1 +
          ((mulAddTraceA L (default :: natToDigits accVal) d default).length + 1 +
            ((mulAddRaw L (default :: natToDigits accVal) d default).length + 1 + 1)) with hM
      have hMbound : M ≤ 3 * (B + 2) + 1 := by
        rw [hM, hL1len]
        have hLleB : L.length ≤ B := by
          have hsrc : (d :: rest).length = rest.length + 1 := rfl
          omega
        have hbF : bitLen totalVal + 1 ≤ B := by omega
        omega
      have hEq : mulOuterStep L d (natToDigits accVal)
          = mulOuterStep (natToDigits rsVal) d (natToDigits accVal) := by
        rw [mulOuterStep_eq_natToDigits, mulOuterStep_eq_natToDigits, hLval,
          digitsToNat_natToDigits rsVal]
      refine ⟨N2 + M, Sg2, ?_, hRhs2, ?_, hLhs2, hCopy2, hSum2, ?_, ?_⟩
      · rw [Function.iterate_add_apply (flipBindMul rd rs rt) N2 M, hiter, hrun2]
      · rw [hRd2, mulRawAux, ← hAccVal', hEq]
      · intro k hk1 hk2 hk3 hk4 hk5
        rw [hframe2 k hk1 hk2 hk3 hk4 hk5, hSg1]
        simp [Function.update, hk1, hk2, hk3, hk4]
      · have hsrc : (d :: rest).length = rest.length + 1 := rfl
        calc N2 + M ≤ (rest.length + 1) * (3 * (B + 2) + 1) + (3 * (B + 2) + 1) := by omega
          _ = (rest.length + 2) * (3 * (B + 2) + 1) := by ring
          _ = ((d :: rest).length + 1) * (3 * (B + 2) + 1) := by rw [hsrc]

/-! ## `realize_mul_bounded`: composing all phases -/

/-- `copyLhs`, `copyLhsRestore` and `reverseLhs` chained: `rs`'s digits end up on `lhsOperand`
    with `rs` itself restored and `workRev` empty again. -/
lemma realize_mul_bounded_copyLhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = src) (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit)) :
    (flipBindMul rd rs rt)^[3 * src.length + 3]
        (some (⟨some MulPhase.copyLhs, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.copyRhs, (⟨none, none, default, default⟩ : MulState),
          Function.update Sg (Kg.scratch .lhsOperand) src⟩ := by
  have hcount : 3 * src.length + 3 = (src.reverse.length + 1) + (2 * src.length + 2) := by
    rw [List.length_reverse]; omega
  have hWr : (Function.update Sg (Kg.scratch .workRev) (src.reverse ++ Sg (Kg.scratch .workRev)))
      (Kg.scratch .workRev) = src.reverse := by simp [hWorkRev]
  rw [hcount, Function.iterate_add_apply,
    mul_copyLhs_phase rd rs rt src Sg _ hRs hCopyScratch,
    mul_reverseLhs_loop rd rs rt src.reverse _ _ hWr]
  simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = Kg.scratch .lhsOperand
  · subst hk; simp [Function.update, hLhs]
  · by_cases hk2 : k = Kg.scratch .workRev
    · subst hk2; simp [Function.update, hWorkRev]
    · simp [Function.update, hk, hk2]

/-- `copyRhs` and `copyRhsRestore` chained: `rt`'s digits end up on `rhsOperand` MSB-first with
    `rt` itself restored. -/
lemma realize_mul_bounded_copyRhs_phase (src : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRt : Sg (Kg.reg rt) = src) (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindMul rd rs rt)^[2 * src.length + 2]
        (some (⟨some MulPhase.copyRhs, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.clearDest, (⟨none, none, default, default⟩ : MulState),
          Function.update Sg (Kg.scratch .rhsOperand) src.reverse⟩ := by
  rw [mul_copyRhs_phase rd rs rt src Sg _ hRt hCopyScratch, hRhs, List.append_nil]

/-- The whole non-destructive snapshot prefix of `mul`, from `copyLhs` through `clearDest`: both
    operands are captured (the multiplier MSB-first) and `rd` is emptied. -/
lemma realize_mul_bounded_prefix (A B : List Digit) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = A) (hRt : Sg (Kg.reg rt) = B)
    (hWorkRev : Sg (Kg.scratch .workRev) = ([] : List Digit))
    (hCopyScratch : Sg (Kg.scratch .copyScratch) = ([] : List Digit))
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    (flipBindMul rd rs rt)^[((Sg (Kg.reg rd)).length + 1)
        + ((2 * B.length + 2) + (3 * A.length + 3))]
        (some (⟨some MulPhase.copyLhs, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState),
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
              (Kg.scratch .rhsOperand) B.reverse) (Kg.reg rd) []⟩ := by
  have hrun1 := realize_mul_bounded_copyLhs_phase rd rs rt A Sg hRs hWorkRev hCopyScratch hLhs
  have hrun2 := realize_mul_bounded_copyRhs_phase rd rs rt B
    (Function.update Sg (Kg.scratch .lhsOperand) A) (by simpa using hRt)
    (by simpa using hCopyScratch) (by simpa using hRhs)
  have hlen : ((Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
      (Kg.scratch .rhsOperand) B.reverse) (Kg.reg rd)).length = (Sg (Kg.reg rd)).length := by simp
  have hrun3 := mul_clearDest_loop rd rs rt _
    (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
      (Kg.scratch .rhsOperand) B.reverse)
    (⟨none, none, default, default⟩ : MulState) rfl
  rw [hlen] at hrun3
  rw [Function.iterate_add_apply (flipBindMul rd rs rt) ((Sg (Kg.reg rd)).length + 1)
      ((2 * B.length + 2) + (3 * A.length + 3)),
    Function.iterate_add_apply (flipBindMul rd rs rt) (2 * B.length + 2) (3 * A.length + 3),
    hrun1, hrun2, hrun3]

/-- After the outer loop and the `drainLhs` pass, the stack is the initial one with `lhsOperand` and
    `rhsOperand` emptied and `rd` holding the product. -/
lemma realize_mul_bounded_tail_stack (S Sg5 : ∀ k, List (Γg p k)) (R : List Digit)
    (hRhs5 : Sg5 (Kg.scratch .rhsOperand) = []) (hRd5 : Sg5 (Kg.reg rd) = R)
    (hCopy5 : Sg5 (Kg.scratch .copyScratch) = []) (hSum5 : Sg5 (Kg.scratch .sumScratch) = [])
    (hCopy : S (Kg.scratch .copyScratch) = []) (hSum : S (Kg.scratch .sumScratch) = [])
    (hframe5 : ∀ k, k ≠ Kg.reg rd → k ≠ Kg.scratch .rhsOperand → k ≠ Kg.scratch .lhsOperand →
      k ≠ Kg.scratch .copyScratch → k ≠ Kg.scratch .sumScratch → Sg5 k = S k) :
    Function.update Sg5 (Kg.scratch .lhsOperand) []
      = Function.update (Function.update (Function.update S (Kg.scratch .lhsOperand) [])
          (Kg.scratch .rhsOperand) []) (Kg.reg rd) R := by
  funext k
  by_cases hk : k = Kg.reg rd
  · subst hk; simp [Function.update, hRd5]
  by_cases hk2 : k = Kg.scratch .lhsOperand
  · subst hk2; simp [Function.update]
  by_cases hk3 : k = Kg.scratch .rhsOperand
  · subst hk3; simp [Function.update, hRhs5]
  by_cases hk4 : k = Kg.scratch .copyScratch
  · subst hk4; simp [Function.update, hCopy5, hCopy]
  by_cases hk5 : k = Kg.scratch .sumScratch
  · subst hk5; simp [Function.update, hSum5, hSum]
  rw [Function.update_of_ne hk2, hframe5 k hk hk3 hk2 hk4 hk5]
  simp [Function.update, hk, hk2, hk3]

/-- Arithmetic behind the tail's step bound: the outer loop's quadratic bound plus the closing
    `nextDigit` exit and `drainLhs` pass fit in `13 * Y ^ 2`. -/
lemma realize_mul_bounded_tail_count (N5 L Bout Y nrt : ℕ) (hL : L ≤ Bout) (hB : Bout ≤ Y)
    (hrt : nrt + 1 ≤ Y) (hN5 : N5 ≤ (nrt + 1) * (3 * (Bout + 2) + 1)) :
    (L + 1) + (1 + N5) ≤ 13 * Y ^ 2 := by
  have h1 : N5 ≤ Y * (3 * Y + 7) :=
    hN5.trans (Nat.mul_le_mul hrt (by omega))
  have hY : 1 ≤ Y := by omega
  nlinarith [h1, hY]

/-- From `nextDigit` with the multiplier on `rhsOperand` (MSB-first), the multiplicand on
    `lhsOperand` and everything else empty: the outer loop and `drainLhs` reach `done` with the
    product in `rd`. -/
lemma realize_mul_bounded_tail (rsVal rtVal Y : ℕ) (S : ∀ k, List (Γg p k))
    (hLhs : S (Kg.scratch .lhsOperand) = natToDigits rsVal)
    (hRhs : S (Kg.scratch .rhsOperand) = (natToDigits rtVal).reverse)
    (hRd : S (Kg.reg rd) = ([] : List Digit))
    (hCopy : S (Kg.scratch .copyScratch) = ([] : List Digit))
    (hSum : S (Kg.scratch .sumScratch) = ([] : List Digit))
    (hY : (natToDigits rsVal).length + (natToDigits rtVal).length + bitLen rsVal + bitLen rtVal + 1
      ≤ Y) :
    ∃ N, (flipBindMul rd rs rt)^[N]
        (some (⟨some MulPhase.nextDigit, (⟨none, none, default, default⟩ : MulState), S⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.done, (⟨none, none, default, default⟩ : MulState),
          Function.update (Function.update (Function.update S (Kg.scratch .lhsOperand) [])
            (Kg.scratch .rhsOperand) []) (Kg.reg rd) (natToDigits (rsVal * rtVal))⟩
      ∧ N ≤ 13 * Y ^ 2 := by
  have hnil0 : (natToDigits (0 : ℕ) : List Digit) = [] := natToDigits_zero
  have hInv : rsVal * rtVal = rsVal * digitsToNat (natToDigits rtVal).reverse.reverse
      + 0 * 16 ^ (natToDigits rtVal).reverse.length := by
    rw [List.reverse_reverse, digitsToNat_natToDigits]; ring
  have hbit : bitLen (rsVal * rtVal) ≤ bitLen rsVal + bitLen rtVal := bitLen_mul_le rsVal rtVal
  have hrev : (natToDigits rtVal).reverse.length = (natToDigits rtVal).length := List.length_reverse
  obtain ⟨N5, Sg5, hrun5, hRhs5, hRd5, ⟨L5, hLval5, hLhs5, hL5len⟩, hCopy5, hSum5, hframe5, hN5⟩ :=
    mul_outer_loop_run_bounded rd rs rt S rsVal 0 (rsVal * rtVal) (natToDigits rtVal).reverse.length
      (max ((natToDigits rsVal).length + (natToDigits rtVal).reverse.length)
        (bitLen (rsVal * rtVal) + 1 + (natToDigits rtVal).reverse.length))
      (natToDigits rsVal) (digitsToNat_natToDigits rsVal) (natToDigits rtVal).reverse
      hInv le_rfl (le_max_left _ _) (le_max_right _ _) hLhs (by rw [hRd, hnil0]) hRhs hCopy hSum
  have hRd5' : Sg5 (Kg.reg rd) = natToDigits (rsVal * rtVal) := by
    rw [hRd5, hnil0]; exact mulRaw_natToDigits rsVal rtVal
  have hstep := flipBindMul_nextDigit_nil_exit rd rs rt Sg5
    (⟨none, none, default, default⟩ : MulState) hRhs5
  have run7 := mul_drainLhs_loop rd rs rt L5 Sg5 (⟨none, none, default, default⟩ : MulState) hLhs5
  refine ⟨(L5.length + 1) + (1 + N5), ?_, ?_⟩
  · rw [Function.iterate_add_apply (flipBindMul rd rs rt) (L5.length + 1) (1 + N5),
      Function.iterate_add_apply (flipBindMul rd rs rt) 1 N5, hrun5, Function.iterate_one,
      hstep, run7, realize_mul_bounded_tail_stack rd S Sg5 _ hRhs5 hRd5' hCopy5 hSum5 hCopy hSum
        hframe5]
  · exact realize_mul_bounded_tail_count N5 L5.length _ Y _ hL5len (by omega) (by omega) hN5

/-- All scratch stacks the prefix and tail touch are back to their initial (empty) contents, so
    only the `rd` update remains. -/
lemma realize_mul_bounded_final_stack (Sg : ∀ k, List (Γg p k)) (A B R : List Digit)
    (hLhs : Sg (Kg.scratch .lhsOperand) = ([] : List Digit))
    (hRhs : Sg (Kg.scratch .rhsOperand) = ([] : List Digit)) :
    Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand) A)
        (Kg.scratch .rhsOperand) B) (Kg.reg rd) [])
      (Kg.scratch .lhsOperand) []) (Kg.scratch .rhsOperand) [])
      (Kg.reg rd) R
      = Function.update Sg (Kg.reg rd) R := by
  rw [Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_comm (show (Kg.reg rd : Kg p) ≠ Kg.scratch .rhsOperand by simp),
    Function.update_idem,
    Function.update_comm (show (Kg.scratch .rhsOperand : Kg p) ≠ Kg.scratch .lhsOperand by simp),
    Function.update_idem, Function.update_idem,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .lhsOperand)).2 hLhs.symm,
    (Function.update_eq_self_iff (f := Sg) (a := Kg.scratch .rhsOperand)).2 hRhs.symm]

/-- Arithmetic behind `realize_mul_bounded`'s step bound: the straight-line prefix is linear and is
    dominated by the quadratic tail. -/
lemma realize_mul_bounded_count (N rdLen a b c d Y : ℕ) (hY : rdLen + a + b + c + d + 1 = Y)
    (hN : N ≤ 13 * Y ^ 2) :
    N + ((rdLen + 1) + ((2 * b + 2) + (3 * a + 3))) ≤ 64 * Y ^ 2 := by
  have hYsq : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  nlinarith [hN, hYsq]

/-- Composes all phases into the full `mul` run, with a step-count bound. Unlike
    `add`/`sub`, `mul`'s outer loop (`mul_outer_loop_run_bounded`) is genuinely quadratic in its own
    charged cost; the six straight-line phases around it
    (`copyLhs` through `clearDest`, then `drainLhs`) stay linear and are dominated by it. -/
lemma realize_mul_bounded (rsVal rtVal : ℕ) (Sg : ∀ k, List (Γg p k))
    (hRs : Sg (Kg.reg rs) = natToDigits rsVal) (hRt : Sg (Kg.reg rt) = natToDigits rtVal)
    (hWorkRev : Sg (Kg.scratch .workRev) = []) (hCopyScratch : Sg (Kg.scratch .copyScratch) = [])
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = [])
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = [])
    (hSumScratch : Sg (Kg.scratch .sumScratch) = []) :
    ∃ N, (flipBindMul rd rs rt)^[N]
        (some (⟨some MulPhase.copyLhs, (⟨none, none, default, default⟩ : MulState), Sg⟩ :
          Turing.TM2.Cfg (Γg p) MulPhase MulState))
      = some ⟨some MulPhase.done, (⟨none, none, default, default⟩ : MulState),
          Function.update Sg (Kg.reg rd) (natToDigits (rsVal * rtVal))⟩ ∧
      N ≤ 64 * ((Sg (Kg.reg rd)).length + (natToDigits rsVal).length + (natToDigits rtVal).length
        + bitLen rsVal + bitLen rtVal + 1) ^ 2 := by
  have hpre := realize_mul_bounded_prefix rd rs rt (natToDigits rsVal) (natToDigits rtVal) Sg
    hRs hRt hWorkRev hCopyScratch hLhsOperand hRhsOperand
  obtain ⟨N, htail, hN⟩ := realize_mul_bounded_tail rd rs rt rsVal rtVal
    ((Sg (Kg.reg rd)).length + (natToDigits rsVal).length + (natToDigits rtVal).length
        + bitLen rsVal + bitLen rtVal + 1)
    (Function.update (Function.update (Function.update Sg (Kg.scratch .lhsOperand)
      (natToDigits rsVal)) (Kg.scratch .rhsOperand) (natToDigits rtVal).reverse) (Kg.reg rd) [])
    (by simp) (by simp) (by simp) (by simpa [Function.update] using hCopyScratch)
    (by simpa [Function.update] using hSumScratch) (by omega)
  refine ⟨N + (((Sg (Kg.reg rd)).length + 1)
      + ((2 * (natToDigits rtVal).length + 2) + (3 * (natToDigits rsVal).length + 3))), ?_, ?_⟩
  · rw [Function.iterate_add_apply, hpre, htail,
      realize_mul_bounded_final_stack rd Sg _ _ _ hLhsOperand hRhsOperand]
  · exact realize_mul_bounded_count _ _ _ _ _ _ _ rfl hN

/-! ## Site dispatcher package

Mirrors `GenericSub.lean`'s `subCode`/`sub_impl_growingBoundedSiteStepSim` pattern. -/

/-- `mul`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the next
    instruction (`pc.1 + 1`), every other phase is `mulProg` lifted via `execVia`. -/
def mulCodeBody (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt) : MulPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = MulPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getMul AllInstrState.setMul
        (mulProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l)

/-- `mulCodeBody`, cast once from `MulPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def mulCode (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (mulCodeBody p pc rd rs rt h)

/-- `mulCode` undoes its own cast when applied to a correspondingly-cast `MulPhase` value. -/
lemma mulCode_apply (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt) (l : MulPhase) :
    mulCode p pc rd rs rt h (cast (congrArg PhaseOf h.symm) l) = mulCodeBody p pc rd rs rt h l :=
  cast_apply_phaseOf p pc h (mulCodeBody p pc rd rs rt h) l

/-- Any dispatcher agreeing with `mulCode` at site `pc` installs the lifted `mulProg` tree at
    every non-`done` label. -/
lemma mulCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (mulCode p pc rd rs rt h) M) :
    ∀ l : MulPhase, l ≠ MulPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getMul AllInstrState.setMul
        (mulProg (regAt p pc rd (by rw [h]; simp [regsOf]))
          (regAt p pc rs (by rw [h]; simp [regsOf]))
          (regAt p pc rt (by rw [h]; simp [regsOf])) l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    mulCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `mulCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `mul`'s own `done` label. -/
lemma mulCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (mulCode p pc rd rs rt h) M) :
    M (execVia p pc h MulPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) MulPhase.done)
  rw [show execVia p pc h MulPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) MulPhase.done) from rfl, hone,
    mulCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- A `mul` step only rewrites register `rd`. -/
lemma mul_impl_growing_bounded_step_regs (rd rs rt : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.mul rd rs rt) :
    (step r).regs = bankWrite r.regs rd (r.regs rs * r.regs rt) := by
  simp [step, hcurEq]

/-- The current instruction is `mul` at the site's program counter. -/
lemma mul_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .mul rd rs rt) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.mul rd rs rt := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]; exact h

/-- The control label at the start of a represented configuration is the site's `copyLhs` entry. -/
lemma mul_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .mul rd rs rt)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h MulPhase.copyLhs) := by
  have hstart : startPhaseOpt (Instruction.mul rd rs rt) = some MulPhase.copyLhs := rfl
  have hentry : entryAt p pc.1 = execVia p pc h MulPhase.copyLhs :=
    entryAt_eq_execVia p pc h MulPhase.copyLhs hstart
  rw [ControlRep] at hctrl; rw [hpcEq] at hctrl; rw [hctrl, hentry]

/-- The whole `mul` site run on the global machine: the `mulProg` run transported via
    `iterate_bind_step_liftStmt`, then the bridge to the next entry, with the final stacks (only `rd'`
    rewritten) and a step count bound. -/
lemma mul_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (h : p.get pc = .mul rd rs rt)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (mulCode p pc rd rs rt h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h MulPhase.copyLhs))
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
      n ≤ 64 * ((cfg.stk (Kg.reg rd')).length + (natToDigits a).length + (natToDigits b).length
        + bitLen a + bitLen b + 1) ^ 2 + 1 ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits (a * b)) := by
  have hag := mulCode_agrees_ne_done p pc rd rs rt h M hAgrees
  rw [← hrd', ← hrs', ← hrt'] at hag
  obtain ⟨N, hMulRun, hNbound⟩ := realize_mul_bounded rd' rs' rt' a b cfg.stk
    hRs hRt hWorkRev hCopyScratch hLhs hRhs hSum
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k; simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getMul AllInstrState.setMul (mulProg rd' rs' rt') M
      Function.injective_id AllInstrState.getMul_setMul AllInstrState.setMul_setMul
      AllInstrState.setMul_getMul N MulPhase.copyLhs (⟨none, none, default, default⟩ : MulState)
      cfg.stk AllInstrState.canonical cfg.stk rfl hstkTriv
      MulPhase.done (⟨none, none, default, default⟩ : MulState)
      (Function.update cfg.stk (Kg.reg rd') (natToDigits (a * b))) rfl hag hMulRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h MulPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
      = some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h MulPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
        = some (Turing.TM2.stepAux (M (execVia p pc h MulPhase.done)) sf Sgf) from rfl,
      mulCode_agrees_done p pc rd rs rt h M hAgrees, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg = (⟨some (execVia p pc h MulPhase.copyLhs), AllInstrState.canonical,
      cfg.stk⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨N + 1, Sgf, ?_, by omega,
    funext fun k => stack_eq_of_map_equiv_refl Sgf _ hstkf k⟩
  rw [hcfgEq, Function.iterate_succ_apply',
    show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
  exact hbridgeStep

/-- The final stacks of a `mul` run encode the stepped registers on every register stack and
    agree with the initial stacks everywhere else. -/
lemma mul_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd rs rt : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.mul rd rs rt)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') (natToDigits (r.regs rs * r.regs rt))) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rd') _ _⟩
  rw [mul_impl_growing_bounded_step_regs rd rs rt r hcurEq]
  by_cases hi : i = rd'
  · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
  · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
    exact hregs i

/-- The configuration reached after a `mul` run represents the stepped RAM, given the register
    frame and the untouched non-register stacks. -/
lemma mul_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd rs rt : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.mul rd rs rt)
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

/-- Step-count bound: the run's cost is at most `4096` times the squared potential, since each of
    the three operand lengths is bounded by `regSize` and the costs `bitLen`s by the instruction
    cost. -/
lemma mul_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (r : RAM) (rd rs rt : ℕ) (rd' rs' rt' : Fin (regBound p))
    (hrsval : rs'.1 = rs) (hrtval : rt'.1 = rt)
    (hcurEq : r.current = Instruction.mul rd rs rt)
    (hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i)) (n : ℕ)
    (hn : n ≤ 64 * ((cfg.stk (Kg.reg rd')).length + (natToDigits (r.regs rs)).length
      + (natToDigits (r.regs rt)).length + bitLen (r.regs rs) + bitLen (r.regs rt) + 1) ^ 2
      + 1) :
    n ≤ 4096 * (regSize p r + (cfg.stk Kg.mem).length +
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
  have hYleX : (cfg.stk (Kg.reg rd')).length + (natToDigits (r.regs rs)).length
      + (natToDigits (r.regs rt)).length + bitLen (r.regs rs) + bitLen (r.regs rt) + 1
      ≤ 6 * X := by omega
  have hYsqleXsq : ((cfg.stk (Kg.reg rd')).length + (natToDigits (r.regs rs)).length
      + (natToDigits (r.regs rt)).length + bitLen (r.regs rs) + bitLen (r.regs rt) + 1) ^ 2
      ≤ (6 * X) ^ 2 := Nat.pow_le_pow_left hYleX 2
  have hXsqeq : (6 * X) ^ 2 = 36 * X ^ 2 := by ring
  omega

/-- Potential growth: only `rd` changes, to at most `bitLen (rs * rt) ≤ bitLen rs + bitLen rt`
    digits, and the memory stack is untouched. -/
lemma mul_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd rs rt : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.mul rd rs rt) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := mul_impl_growing_bounded_step_regs rd rs rt r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits (r.regs rs * r.regs rt)).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' (r.regs rs * r.regs rt) _ le_rfl
  have hle : (natToDigits (r.regs rs * r.regs rt)).length ≤ bitLen (r.regs rs) + bitLen (r.regs rt) :=
    le_trans (natToDigits_length_le_bitLen _) (bitLen_mul_le _ _)
  have hcost : instructionCost r.regs r.mem r.current
      = bitLen (r.regs rs) + bitLen (r.regs rt) + 1 := by rw [hcurEq]; rfl
  rw [hother _ (by simp)]
  omega

/-- `mulCode`'s growth companion: `mem` is untouched, and the only register that can grow is
    `rd`, to `bitLen (regs rs * regs rt) ≤ bitLen (regs rs) + bitLen (regs rt)`
    (`bitLen_mul_le`) — exactly `mul`'s own `instructionCost` minus its `+1`. -/
lemma mul_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt) :
    GrowingBoundedSiteStepSim p pc (mulCode p pc rd rs rt h) 4096 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hprog : r.program = p := hRep.1
  have hregs : ∀ i : Fin (regBound p), cfg.stk (Kg.reg i) = natToDigits (r.regs i) := hRep.2.1
  have hvar : cfg.var = AllInstrState.canonical := hRep.2.2.2.1
  have hscratch : ∀ s : ScratchKind, cfg.stk (Kg.scratch s) = [] := hRep.2.2.2.2.1
  have hcurEq := mul_impl_growing_bounded_current p pc rd rs rt h r hprog hpcEq
  have hcl := mul_impl_growing_bounded_label p pc rd rs rt h cfg r hpcEq hRep.2.2.2.2.2
  obtain ⟨rd', hrd'⟩ : ∃ x, x = regAt p pc rd (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rs', hrs'⟩ : ∃ x, x = regAt p pc rs (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  obtain ⟨rt', hrt'⟩ : ∃ x, x = regAt p pc rt (by rw [h]; simp [regsOf]) := ⟨_, rfl⟩
  have hrdval : rd'.1 = rd := by rw [hrd']; rfl
  have hrsval : rs'.1 = rs := by rw [hrs']; rfl
  have hrtval : rt'.1 = rt := by rw [hrt']; rfl
  have hRs : cfg.stk (Kg.reg rs') = natToDigits (r.regs rs) := by rw [hregs rs', hrsval]
  have hRt : cfg.stk (Kg.reg rt') = natToDigits (r.regs rt) := by rw [hregs rt', hrtval]
  obtain ⟨n, Sgf, hrun, hn, hSgf⟩ := mul_impl_growing_bounded_run p pc rd rs rt h M hAgrees
    cfg hvar hcl rd' rs' rt' hrd' hrs' hrt' _ _ hRs hRt (hscratch .workRev) (hscratch .copyScratch)
    (hscratch .lhsOperand) (hscratch .rhsOperand) (hscratch .sumScratch)
  obtain ⟨hreg, hother⟩ := mul_impl_growing_bounded_stk cfg.stk r rd rs rt rd' hrdval hcurEq hregs
    Sgf hSgf
  exact ⟨n, _, hrun,
    mul_impl_growing_bounded_represents p pc rd rs rt cfg r hRep hpcEq hcurEq Sgf hreg hother,
    hother Kg.io (by simp),
    mul_impl_growing_bounded_time p cfg r rd rs rt rd' rs' rt' hrsval hrtval hcurEq hregs n hn,
    mul_impl_growing_bounded_growth p cfg r rd rs rt rd' hrdval hcurEq Sgf hother⟩

/-- `mul`'s `GrowingTimedInstrImpl` package. -/
def mulGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd rs rt : ℕ)
    (h : p.get pc = .mul rd rs rt) : GrowingTimedInstrImpl p pc where
  code := mulCode p pc rd rs rt h
  C := 4096
  G := 1
  growingSim := mul_impl_growingBoundedSiteStepSim p pc rd rs rt h

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmit
public import NPComplete.RAMToTM.Generic.Machine.GenericPrologue
public import Mathlib.Tactic.FinCases

/-!
# Draining every stack but `out` before halt

`GenericEmit.emit_run_length_bounded` (and `GenericEmitPrep.prep_run_length_bounded` before it)
leave every
`EmitK p` stack except `EmitK.out` populated with leftover working state (drained registers
aside, `Kg.io`/`Kg.mem`/scratch all still hold whatever the RAM computation and the emit loop
left behind). `GenericCleanup.cleanupProg` cannot be reused here — it *reads* a register as the
answer and pushes a single bit onto `Kg.io`, exactly the single-bit-decision convention being
replaced with the multi-bit `EmitK.out` stream (module docstring). This file is `cleanupProg`'s
drain-loop machinery (its
`drainReg`/`drainMem`/`drainScratch` phases, mirrored one-for-one) retargeted at `EmitK p`, plus
two new phases draining `Kg.io` (now unused) and `EmitK.countdown` (the prep loop's spent
markers) — `EmitK.out` alone is left untouched, so the final `halt` config's output stack holds
exactly what `emit_run_length_bounded` proved it holds. Written as its own small concrete machine (own
local `Λ`/`σ`, no `CleanupAgrees`/dispatcher abstraction) since — like `GenericEmitPrep`'s prep
loop — it is not inserted at many `pc` sites inside a shared dispatcher: the master machine's
`cleanup` component embeds it once via `liftLocalStmt` (`GenericEmitMasterProg.lean`).
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym natToDigits)
open Turing Turing.TM2.Stmt

variable {p : List Instruction}

/-- The cleanup chain's phases: `drainReg`/`drainMem`/`drainScratch` mirror
    `GenericCleanup.CleanupPhase` verbatim; `drainIo`/`drainCountdown` are new, draining the two
    stacks `GenericEmit`'s stack space adds that `CleanupPhase` never had to know about. -/
inductive EmitCleanupPhase (p : List Instruction)
  | drainReg (cursor : Fin (regBound p + 1))
  | drainMem
  | drainScratch (sk : ScratchKind)
  | drainIo
  | drainCountdown
  | done
  deriving DecidableEq, Fintype

/-- The cleanup loop's only local state: whether the last pop found an element (loop-continue
    flag), mirroring `AllInstrState.decision`'s role in `GenericCleanup.cleanupProg`. -/
structure CleanupState where
  decision : Bool
  deriving DecidableEq, Fintype

/-- The cleanup chain's `Stmt` tree: `drainReg` walks every register via `cursor`, `drainMem`
    drains the write-log, `drainScratch` walks the fixed `ScratchKind` chain
    (`GenericProgramMachine.nextScratchKind`), `drainIo`/`drainCountdown` drain the two stacks
    `EmitK p` alone has — `EmitK.out` never appears in any phase here. -/
def emitCleanupProg : EmitCleanupPhase p → Turing.TM2.Stmt (EmitΓ p) (EmitCleanupPhase p) CleanupState
  | .drainReg cursor =>
      if h : cursor.val < regBound p then
        pop (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) (fun s ov => { s with decision := ov.isSome })
          (branch (fun s => s.decision)
            (goto (fun _ => EmitCleanupPhase.drainReg cursor))
            (goto (fun _ => EmitCleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩)))
      else
        goto (fun _ => EmitCleanupPhase.drainMem)
  | .drainMem =>
      pop (EmitK.base Kg.mem) (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => EmitCleanupPhase.drainMem))
          (goto (fun _ => EmitCleanupPhase.drainScratch ScratchKind.copyScratch)))
  | .drainScratch sk =>
      pop (EmitK.base (Kg.scratch sk)) (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => EmitCleanupPhase.drainScratch sk))
          (goto (fun _ => match nextScratchKind sk with
            | some sk' => EmitCleanupPhase.drainScratch sk'
            | none => EmitCleanupPhase.drainIo)))
  | .drainIo =>
      pop (EmitK.base Kg.io) (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => EmitCleanupPhase.drainIo))
          (goto (fun _ => EmitCleanupPhase.drainCountdown)))
  | .drainCountdown =>
      pop EmitK.countdown (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => EmitCleanupPhase.drainCountdown))
          (goto (fun _ => EmitCleanupPhase.done)))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindEmitCleanup : Option (Turing.TM2.Cfg (EmitΓ p) (EmitCleanupPhase p) CleanupState) →
    Option (Turing.TM2.Cfg (EmitΓ p) (EmitCleanupPhase p) CleanupState) :=
  fun x => x.bind (Turing.TM2.step (emitCleanupProg (p := p)))

/-! ## `drainReg`: mirrors `GenericCleanup.cleanup_step_drainReg_{cons,nil,sentinel}` verbatim,
    retargeted at `EmitK.base (Kg.reg _)`. -/

lemma flipBindEmitCleanup_step_drainReg_cons (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p)
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k)) (d : Digit) (rest : List Digit)
    (hReg : Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) = d :: rest) :
    flipBindEmitCleanup (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainReg cursor), { var with decision := true },
          Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) rest⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩ = _
  simp [emitCleanupProg, h, hReg]

lemma flipBindEmitCleanup_step_drainReg_nil (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p)
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hReg : Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) = ([] : List Digit)) :
    flipBindEmitCleanup (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩),
          { var with decision := false },
          Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩ = _
  simp [emitCleanupProg, h, hReg, update_self_of_eq Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) [] hReg]

lemma flipBindEmitCleanup_step_drainReg_sentinel (cursor : Fin (regBound p + 1))
    (h : cursor.val = regBound p) (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k)) :
    flipBindEmitCleanup (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainMem, var, Sg⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩ = _
  simp [emitCleanupProg, Nat.not_lt.mpr (le_of_eq h.symm)]

/-- `drainReg cursor`'s aggregate effect on the *one* register `cursor` names (in range):
    `content.length + 1` steps drain it to `[]`, advancing to `cursor + 1`. Mirrors
    `GenericCleanup.cleanup_drain_one_reg_run`. -/
lemma flipBindEmitCleanup_drainReg_one_run (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p)
    (content : List Digit) (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hReg : Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) = content) :
    (flipBindEmitCleanup (p := p))^[content.length + 1]
        (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩),
          { var with decision := false },
          Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []⟩ := by
  induction content generalizing var Sg with
  | nil => simpa using flipBindEmitCleanup_step_drainReg_nil cursor h var Sg hReg
  | cons d rest ih =>
    have hstep := flipBindEmitCleanup_step_drainReg_cons cursor h var Sg d rest hReg
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩))
        rest) (by simp)]
    simp [Function.update_idem]

/-- `drainReg cursor`'s full run: `flipBindEmitCleanup_drainReg_one_run` chained over every register from
    `cursor` up to `regBound p` (generalized over the *remaining count* `k`). -/
lemma flipBindEmitCleanup_drainReg_run (k : ℕ) (cursor : Fin (regBound p + 1))
    (hk : cursor.val + k = regBound p) (content : Fin (regBound p) → List Digit)
    (var : CleanupState) (Sg : ∀ k', List (EmitΓ p k'))
    (hReg : ∀ i : Fin (regBound p), cursor.val ≤ i.val →
      Sg (EmitK.base (Kg.reg i)) = content i) :
    ∃ n var' Sg', (flipBindEmitCleanup (p := p))^[n]
        (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainMem, var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), cursor.val ≤ i.val → Sg' (EmitK.base (Kg.reg i)) = []) ∧
        (∀ k' : EmitK p, (∀ i : Fin (regBound p), cursor.val ≤ i.val → k' ≠ EmitK.base (Kg.reg i)) →
          Sg' k' = Sg k') := by
  induction k generalizing cursor var Sg with
  | zero =>
    refine ⟨1, var, Sg, ?_, ?_, fun _ _ => rfl⟩
    · simpa using flipBindEmitCleanup_step_drainReg_sentinel cursor (by omega) var Sg
    · intro i hi
      omega
  | succ k ih =>
    have h : cursor.val < regBound p := by omega
    have hltp1 : cursor.val + 1 < regBound p + 1 := by omega
    have hcv : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val = cursor.val + 1 := rfl
    have hrun1 := flipBindEmitCleanup_drainReg_one_run cursor h (content ⟨cursor.val, h⟩) var Sg
      (hReg ⟨cursor.val, h⟩ le_rfl)
    have hk' : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val + k = regBound p := by
      rw [hcv]; omega
    have hReg2 : ∀ i : Fin (regBound p),
        (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val ≤ i.val →
        Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []
          (EmitK.base (Kg.reg i)) = content i := by
      intro i hi
      rw [hcv] at hi
      have hne : EmitK.base (Kg.reg i) ≠ EmitK.base (Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p))) := by
        simp only [ne_eq, EmitK.base.injEq, Kg.reg.injEq]
        intro heqi
        have hival : i.val = cursor.val := congrArg Fin.val heqi
        omega
      rw [Function.update_of_ne hne]
      exact hReg i (by omega)
    obtain ⟨n2, var2, Sg2, hrun2, hdrained2, hunchanged2⟩ :=
      ih ⟨cursor.val + 1, hltp1⟩ hk' { var with decision := false }
        (Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []) hReg2
    refine ⟨n2 + ((content ⟨cursor.val, h⟩).length + 1), var2, Sg2, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hrun1, hrun2]
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hlt
      · have hi' : i = ⟨cursor.val, h⟩ := Fin.ext heq.symm
        have hstep := hunchanged2 (EmitK.base (Kg.reg i)) (by
          intro j hj
          rw [hcv] at hj
          simp only [ne_eq, EmitK.base.injEq, Kg.reg.injEq]
          intro heqij
          have hval : i.val = j.val := congrArg Fin.val heqij
          rw [hi'] at hval
          omega)
        rw [hstep, hi']
        simp
      · exact hdrained2 i (by rw [hcv]; omega)
    · intro k' hk'2
      have hne2 : k' ≠ EmitK.base (Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p))) :=
        hk'2 ⟨cursor.val, h⟩ le_rfl
      rw [hunchanged2 k' (fun i hi => hk'2 i (by rw [hcv] at hi; omega)),
        Function.update_of_ne hne2]

/-- Quantitative companion to `flipBindEmitCleanup_drainReg_run`: same statement, plus a bound on the
    witness step count in terms of a uniform per-register cap `M` (rather than the exact
    register-by-register sum, which would need `Finset` sum-splitting machinery this file
    otherwise has no use for) — `k` registers drained at cost `≤ M + 1` each, plus the final
    sentinel step. -/
lemma flipBindEmitCleanup_drainReg_run_bound (k : ℕ) (cursor : Fin (regBound p + 1))
    (hk : cursor.val + k = regBound p) (content : Fin (regBound p) → List Digit) (M : ℕ)
    (hBound : ∀ i : Fin (regBound p), cursor.val ≤ i.val → (content i).length ≤ M)
    (var : CleanupState) (Sg : ∀ k', List (EmitΓ p k'))
    (hReg : ∀ i : Fin (regBound p), cursor.val ≤ i.val →
      Sg (EmitK.base (Kg.reg i)) = content i) :
    ∃ n var' Sg', (flipBindEmitCleanup (p := p))^[n]
        (some ⟨some (EmitCleanupPhase.drainReg cursor), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainMem, var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), cursor.val ≤ i.val → Sg' (EmitK.base (Kg.reg i)) = []) ∧
        (∀ k' : EmitK p, (∀ i : Fin (regBound p), cursor.val ≤ i.val → k' ≠ EmitK.base (Kg.reg i)) →
          Sg' k' = Sg k') ∧
        n ≤ k * (M + 1) + 1 := by
  induction k generalizing cursor var Sg with
  | zero =>
    refine ⟨1, var, Sg, ?_, ?_, fun _ _ => rfl, by omega⟩
    · simpa using flipBindEmitCleanup_step_drainReg_sentinel cursor (by omega) var Sg
    · intro i hi
      omega
  | succ k ih =>
    have h : cursor.val < regBound p := by omega
    have hltp1 : cursor.val + 1 < regBound p + 1 := by omega
    have hcv : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val = cursor.val + 1 := rfl
    have hrun1 := flipBindEmitCleanup_drainReg_one_run cursor h (content ⟨cursor.val, h⟩) var Sg
      (hReg ⟨cursor.val, h⟩ le_rfl)
    have hCLen : (content ⟨cursor.val, h⟩).length ≤ M := hBound ⟨cursor.val, h⟩ le_rfl
    have hk' : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val + k = regBound p := by
      rw [hcv]; omega
    have hBound2 : ∀ i : Fin (regBound p),
        (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val ≤ i.val → (content i).length ≤ M := by
      intro i hi
      rw [hcv] at hi
      exact hBound i (by omega)
    have hReg2 : ∀ i : Fin (regBound p),
        (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val ≤ i.val →
        Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []
          (EmitK.base (Kg.reg i)) = content i := by
      intro i hi
      rw [hcv] at hi
      have hne : EmitK.base (Kg.reg i) ≠ EmitK.base (Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p))) := by
        simp only [ne_eq, EmitK.base.injEq, Kg.reg.injEq]
        intro heqi
        have hival : i.val = cursor.val := congrArg Fin.val heqi
        omega
      rw [Function.update_of_ne hne]
      exact hReg i (by omega)
    obtain ⟨n2, var2, Sg2, hrun2, hdrained2, hunchanged2, hn2bound⟩ :=
      ih ⟨cursor.val + 1, hltp1⟩ hk' hBound2 { var with decision := false }
        (Function.update Sg (EmitK.base (Kg.reg ⟨cursor.val, h⟩)) []) hReg2
    have hdist : (k + 1) * (M + 1) = k * (M + 1) + (M + 1) := by ring
    refine ⟨n2 + ((content ⟨cursor.val, h⟩).length + 1), var2, Sg2, ?_, ?_, ?_, by omega⟩
    · rw [Function.iterate_add_apply, hrun1, hrun2]
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hlt
      · have hi' : i = ⟨cursor.val, h⟩ := Fin.ext heq.symm
        have hstep := hunchanged2 (EmitK.base (Kg.reg i)) (by
          intro j hj
          rw [hcv] at hj
          simp only [ne_eq, EmitK.base.injEq, Kg.reg.injEq]
          intro heqij
          have hval : i.val = j.val := congrArg Fin.val heqij
          rw [hi'] at hval
          omega)
        rw [hstep, hi']
        simp
      · exact hdrained2 i (by rw [hcv]; omega)
    · intro k' hk'2
      have hne2 : k' ≠ EmitK.base (Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p))) :=
        hk'2 ⟨cursor.val, h⟩ le_rfl
      rw [hunchanged2 k' (fun i hi => hk'2 i (by rw [hcv] at hi; omega)),
        Function.update_of_ne hne2]

/-! ## `drainMem`: mirrors `GenericCleanup.cleanup_step_drainMem_{cons,nil}` and
    `cleanup_drainMem_run` verbatim, retargeted at `EmitK.base Kg.mem`. -/

lemma flipBindEmitCleanup_step_drainMem_cons (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (d : MemSym) (rest : List MemSym) (hMem : Sg (EmitK.base Kg.mem) = d :: rest) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainMem, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainMem, { var with decision := true },
          Function.update Sg (EmitK.base Kg.mem) rest⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p))) ⟨some EmitCleanupPhase.drainMem, var, Sg⟩ = _
  simp [emitCleanupProg, hMem]

lemma flipBindEmitCleanup_step_drainMem_nil (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hMem : Sg (EmitK.base Kg.mem) = ([] : List MemSym)) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainMem, var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainScratch ScratchKind.copyScratch),
          { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p))) ⟨some EmitCleanupPhase.drainMem, var, Sg⟩ = _
  simp [emitCleanupProg, hMem, update_self_of_eq Sg (EmitK.base Kg.mem) [] hMem]

lemma flipBindEmitCleanup_drainMem_run (content : List MemSym) (var : CleanupState)
    (Sg : ∀ k, List (EmitΓ p k)) (hMem : Sg (EmitK.base Kg.mem) = content) :
    (flipBindEmitCleanup (p := p))^[content.length + 1]
        (some ⟨some EmitCleanupPhase.drainMem, var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainScratch ScratchKind.copyScratch),
          { var with decision := false }, Function.update Sg (EmitK.base Kg.mem) []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg (EmitK.base Kg.mem) [] hMem]
    simpa using flipBindEmitCleanup_step_drainMem_nil var Sg hMem
  | cons d rest ih =>
    have hstep := flipBindEmitCleanup_step_drainMem_cons var Sg d rest hMem
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (EmitK.base Kg.mem) rest) (by simp)]
    simp [Function.update_idem]

/-! ## `drainScratch`: mirrors `GenericCleanup.cleanup_step_drainScratch_{cons,nil}` verbatim,
    retargeted at `EmitK.base (Kg.scratch _)`, ending at `drainIo` (instead of `done`) once every
    `ScratchKind` is drained. -/

lemma flipBindEmitCleanup_step_drainScratch_cons (sk : ScratchKind) (var : CleanupState)
    (Sg : ∀ k, List (EmitΓ p k)) (d : ScratchΓ sk) (rest : List (ScratchΓ sk))
    (hSk : Sg (EmitK.base (Kg.scratch sk)) = d :: rest) :
    flipBindEmitCleanup (some ⟨some (EmitCleanupPhase.drainScratch sk), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainScratch sk), { var with decision := true },
          Function.update Sg (EmitK.base (Kg.scratch sk)) rest⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some (EmitCleanupPhase.drainScratch sk), var, Sg⟩ = _
  simp [emitCleanupProg, hSk]

lemma flipBindEmitCleanup_step_drainScratch_nil (sk : ScratchKind) (var : CleanupState)
    (Sg : ∀ k, List (EmitΓ p k)) (hSk : Sg (EmitK.base (Kg.scratch sk)) = ([] : List (ScratchΓ sk))) :
    flipBindEmitCleanup (some ⟨some (EmitCleanupPhase.drainScratch sk), var, Sg⟩)
      = some ⟨some (match nextScratchKind sk with
          | some sk' => EmitCleanupPhase.drainScratch sk'
          | none => EmitCleanupPhase.drainIo),
          { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some (EmitCleanupPhase.drainScratch sk), var, Sg⟩ = _
  simp [emitCleanupProg, hSk, update_self_of_eq Sg (EmitK.base (Kg.scratch sk)) [] hSk]

lemma flipBindEmitCleanup_drainScratch_one_run (sk : ScratchKind) (content : List (ScratchΓ sk))
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hSk : Sg (EmitK.base (Kg.scratch sk)) = content) :
    (flipBindEmitCleanup (p := p))^[content.length + 1]
        (some ⟨some (EmitCleanupPhase.drainScratch sk), var, Sg⟩)
      = some ⟨some (match nextScratchKind sk with
          | some sk' => EmitCleanupPhase.drainScratch sk'
          | none => EmitCleanupPhase.drainIo),
          { var with decision := false }, Function.update Sg (EmitK.base (Kg.scratch sk)) []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg (EmitK.base (Kg.scratch sk)) [] hSk]
    simpa using flipBindEmitCleanup_step_drainScratch_nil sk var Sg hSk
  | cons d rest ih =>
    have hstep := flipBindEmitCleanup_step_drainScratch_cons sk var Sg d rest hSk
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (EmitK.base (Kg.scratch sk)) rest)
        (by simp)]
    simp [Function.update_idem]

lemma flipBindEmitCleanup_drainScratch_run
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit)
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hCopy : Sg (EmitK.base (Kg.scratch .copyScratch)) = copyc)
    (hQuery : Sg (EmitK.base (Kg.scratch .query)) = queryc)
    (hQueryTmp : Sg (EmitK.base (Kg.scratch .queryTmp)) = queryTmpc)
    (hLogTmp : Sg (EmitK.base (Kg.scratch .logTmp)) = logTmpc)
    (hWorkRev : Sg (EmitK.base (Kg.scratch .workRev)) = workRevc)
    (hLhsOperand : Sg (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc)
    (hRhsOperand : Sg (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc)
    (hSumScratch : Sg (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc)
    (hDiffScratch : Sg (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc)
    (hPrologueCounter : Sg (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc)
    (hPrologueWork : Sg (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc) :
    (flipBindEmitCleanup (p := p))^[prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
        (diffScratchc.length + 1) + (sumScratchc.length + 1) + (rhsOperandc.length + 1) +
        (lhsOperandc.length + 1) + (workRevc.length + 1) + (logTmpc.length + 1) +
        (queryTmpc.length + 1) + (queryc.length + 1) + (copyc.length + 1)]
        (some ⟨some (EmitCleanupPhase.drainScratch .copyScratch), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainIo, { var with decision := false },
          Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update Sg
                (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
                (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
              (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
            (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
          (EmitK.base (Kg.scratch .diffScratch)) []) (EmitK.base (Kg.scratch .prologueCounter)) [])
        (EmitK.base (Kg.scratch .prologueWork)) []⟩ := by
  have h1 := flipBindEmitCleanup_drainScratch_one_run .copyScratch copyc var Sg hCopy
  have h2 := flipBindEmitCleanup_drainScratch_one_run .query queryc { var with decision := false }
    (Function.update Sg (EmitK.base (Kg.scratch .copyScratch)) []) (by simp [hQuery])
  have h3 := flipBindEmitCleanup_drainScratch_one_run .queryTmp queryTmpc { var with decision := false }
    (Function.update (Function.update Sg (EmitK.base (Kg.scratch .copyScratch)) [])
      (EmitK.base (Kg.scratch .query)) []) (by simp [hQueryTmp])
  have h4 := flipBindEmitCleanup_drainScratch_one_run .logTmp logTmpc { var with decision := false }
    (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (by simp [hLogTmp])
  have h5 := flipBindEmitCleanup_drainScratch_one_run .workRev workRevc { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
    (by simp [hWorkRev])
  have h6 := flipBindEmitCleanup_drainScratch_one_run .lhsOperand lhsOperandc { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (by simp [hLhsOperand])
  have h7 := flipBindEmitCleanup_drainScratch_one_run .rhsOperand rhsOperandc { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update Sg (EmitK.base (Kg.scratch .copyScratch)) [])
      (EmitK.base (Kg.scratch .query)) []) (EmitK.base (Kg.scratch .queryTmp)) [])
      (EmitK.base (Kg.scratch .logTmp)) []) (EmitK.base (Kg.scratch .workRev)) [])
      (EmitK.base (Kg.scratch .lhsOperand)) []) (by simp [hRhsOperand])
  have h8 := flipBindEmitCleanup_drainScratch_one_run .sumScratch sumScratchc { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update Sg (EmitK.base (Kg.scratch .copyScratch)) [])
      (EmitK.base (Kg.scratch .query)) []) (EmitK.base (Kg.scratch .queryTmp)) [])
      (EmitK.base (Kg.scratch .logTmp)) []) (EmitK.base (Kg.scratch .workRev)) [])
      (EmitK.base (Kg.scratch .lhsOperand)) []) (EmitK.base (Kg.scratch .rhsOperand)) [])
    (by simp [hSumScratch])
  have h9 := flipBindEmitCleanup_drainScratch_one_run .diffScratch diffScratchc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
      (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
    (by simp [hDiffScratch])
  have h10 := flipBindEmitCleanup_drainScratch_one_run .prologueCounter prologueCounterc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
      (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
      (EmitK.base (Kg.scratch .diffScratch)) []) (by simp [hPrologueCounter])
  have h11 := flipBindEmitCleanup_drainScratch_one_run .prologueWork prologueWorkc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update Sg
      (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
      (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
      (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
      (EmitK.base (Kg.scratch .diffScratch)) []) (EmitK.base (Kg.scratch .prologueCounter)) [])
      (by simp [hPrologueWork])
  simp only [nextScratchKind] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [Function.iterate_add_apply, h1,
    Function.iterate_add_apply, h2,
    Function.iterate_add_apply, h3,
    Function.iterate_add_apply, h4,
    Function.iterate_add_apply, h5,
    Function.iterate_add_apply, h6,
    Function.iterate_add_apply, h7,
    Function.iterate_add_apply, h8,
    Function.iterate_add_apply, h9,
    Function.iterate_add_apply, h10, h11]

/-! ## `drainIo`/`drainCountdown`: the two stacks `CleanupPhase` never had, draining the same
    way every other single-stack drain here does. `EmitK.out` never appears. -/

lemma flipBindEmitCleanup_step_drainIo_cons (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (d : Bool) (rest : List Bool) (hIo : Sg (EmitK.base Kg.io) = d :: rest) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainIo, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainIo, { var with decision := true },
          Function.update Sg (EmitK.base Kg.io) rest⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p))) ⟨some EmitCleanupPhase.drainIo, var, Sg⟩ = _
  simp [emitCleanupProg, hIo]

lemma flipBindEmitCleanup_step_drainIo_nil (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hIo : Sg (EmitK.base Kg.io) = ([] : List Bool)) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainIo, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainCountdown, { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p))) ⟨some EmitCleanupPhase.drainIo, var, Sg⟩ = _
  simp [emitCleanupProg, hIo, update_self_of_eq Sg (EmitK.base Kg.io) [] hIo]

lemma flipBindEmitCleanup_drainIo_run (content : List Bool) (var : CleanupState)
    (Sg : ∀ k, List (EmitΓ p k)) (hIo : Sg (EmitK.base Kg.io) = content) :
    (flipBindEmitCleanup (p := p))^[content.length + 1]
        (some ⟨some EmitCleanupPhase.drainIo, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainCountdown, { var with decision := false },
          Function.update Sg (EmitK.base Kg.io) []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg (EmitK.base Kg.io) [] hIo]
    simpa using flipBindEmitCleanup_step_drainIo_nil var Sg hIo
  | cons d rest ih =>
    have hstep := flipBindEmitCleanup_step_drainIo_cons var Sg d rest hIo
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (EmitK.base Kg.io) rest) (by simp)]
    simp [Function.update_idem]

lemma flipBindEmitCleanup_step_drainCountdown_cons (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (rest : List Unit) (hCd : Sg EmitK.countdown = () :: rest) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainCountdown, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainCountdown, { var with decision := true },
          Function.update Sg EmitK.countdown rest⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some EmitCleanupPhase.drainCountdown, var, Sg⟩ = _
  simp [emitCleanupProg, hCd]

lemma flipBindEmitCleanup_step_drainCountdown_nil (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hCd : Sg EmitK.countdown = ([] : List Unit)) :
    flipBindEmitCleanup (some ⟨some EmitCleanupPhase.drainCountdown, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step (emitCleanupProg (p := p)))
      ⟨some EmitCleanupPhase.drainCountdown, var, Sg⟩ = _
  simp [emitCleanupProg, hCd, update_self_of_eq Sg EmitK.countdown [] hCd]

lemma flipBindEmitCleanup_drainCountdown_run (content : List Unit) (var : CleanupState)
    (Sg : ∀ k, List (EmitΓ p k)) (hCd : Sg EmitK.countdown = content) :
    (flipBindEmitCleanup (p := p))^[content.length + 1]
        (some ⟨some EmitCleanupPhase.drainCountdown, var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, { var with decision := false },
          Function.update Sg EmitK.countdown []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg EmitK.countdown [] hCd]
    simpa using flipBindEmitCleanup_step_drainCountdown_nil var Sg hCd
  | cons _ rest ih =>
    have hstep := flipBindEmitCleanup_step_drainCountdown_cons var Sg rest hCd
    rw [show (() :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg EmitK.countdown rest) (by simp)]
    simp [Function.update_idem]

/-! ## Full chain: `drainReg` → `drainMem` → `drainScratch` → `drainIo` → `drainCountdown` →
    `done` → halt (minus the `checkHead`/`checkTail`/`pushAnswer` prefix this design has no use
    for, since `EmitK.out` already holds the answer `emit_run_length_bounded` produced — nothing needs
    extracting from a register). `EmitK.out` is untouched start to finish. -/

/-- The full drain chain's composition, stopped one step short (at `EmitCleanupPhase.done` rather
    than the genuine `halt` `l = none`) — the shape `StmtTransport.iterate_bind_step_liftStmt` needs to
    transport this run into a bigger machine (`Ml lf = halt` for the *label* `lf` it stops at,
    the global transport theorem), since that theorem's own conclusion is stated at a label, never at `none`
    itself. -/
lemma flipBindEmitCleanup_run_to_done (regs : Fin (regBound p) → ℕ) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit) (io0 : List Bool) (cd0 : List Unit)
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hReg : ∀ i : Fin (regBound p), Sg (EmitK.base (Kg.reg i)) = natToDigits (regs i))
    (hMem : Sg (EmitK.base Kg.mem) = m0)
    (hCopy : Sg (EmitK.base (Kg.scratch .copyScratch)) = copyc)
    (hQuery : Sg (EmitK.base (Kg.scratch .query)) = queryc)
    (hQueryTmp : Sg (EmitK.base (Kg.scratch .queryTmp)) = queryTmpc)
    (hLogTmp : Sg (EmitK.base (Kg.scratch .logTmp)) = logTmpc)
    (hWorkRev : Sg (EmitK.base (Kg.scratch .workRev)) = workRevc)
    (hLhsOperand : Sg (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc)
    (hRhsOperand : Sg (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc)
    (hSumScratch : Sg (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc)
    (hDiffScratch : Sg (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc)
    (hPrologueCounter : Sg (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc)
    (hPrologueWork : Sg (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc)
    (hIo : Sg (EmitK.base Kg.io) = io0) (hCd : Sg EmitK.countdown = cd0) :
    ∃ n var' Sg', (flipBindEmitCleanup (p := p))^[n]
        (some ⟨some (EmitCleanupPhase.drainReg ⟨0, by omega⟩), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), Sg' (EmitK.base (Kg.reg i)) = []) ∧
        Sg' (EmitK.base Kg.mem) = [] ∧
        (∀ sk : ScratchKind, Sg' (EmitK.base (Kg.scratch sk)) = []) ∧
        Sg' (EmitK.base Kg.io) = [] ∧ Sg' EmitK.countdown = [] ∧ Sg' EmitK.out = Sg EmitK.out := by
  obtain ⟨n1, var1, Sg1, hrun1, hdrained1, hunchanged1⟩ :=
    flipBindEmitCleanup_drainReg_run (regBound p) ⟨0, by omega⟩ (by simp) (fun i => natToDigits (regs i))
      var Sg (fun i _ => hReg i)
  have hMem1 : Sg1 (EmitK.base Kg.mem) = m0 := by
    rw [hunchanged1 (EmitK.base Kg.mem) (fun i _ => by simp), hMem]
  have hScratch1 : ∀ sk : ScratchKind,
      Sg1 (EmitK.base (Kg.scratch sk)) = Sg (EmitK.base (Kg.scratch sk)) :=
    fun sk => hunchanged1 (EmitK.base (Kg.scratch sk)) (fun i _ => by simp)
  have hIo1 : Sg1 (EmitK.base Kg.io) = io0 := by
    rw [hunchanged1 (EmitK.base Kg.io) (fun i _ => by simp), hIo]
  have hCd1 : Sg1 EmitK.countdown = cd0 := by
    rw [hunchanged1 EmitK.countdown (fun i _ => by simp), hCd]
  have hOut1 : Sg1 EmitK.out = Sg EmitK.out :=
    hunchanged1 EmitK.out (fun i _ => by simp)
  have hrun2 := flipBindEmitCleanup_drainMem_run m0 var1 Sg1 hMem1
  have hCopy2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .copyScratch))
      = copyc := by simp [hScratch1 .copyScratch, hCopy]
  have hQuery2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .query))
      = queryc := by simp [hScratch1 .query, hQuery]
  have hQueryTmp2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .queryTmp))
      = queryTmpc := by simp [hScratch1 .queryTmp, hQueryTmp]
  have hLogTmp2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .logTmp))
      = logTmpc := by simp [hScratch1 .logTmp, hLogTmp]
  have hWorkRev2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .workRev))
      = workRevc := by simp [hScratch1 .workRev, hWorkRev]
  have hLhsOperand2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc := by
    simp [hScratch1 .lhsOperand, hLhsOperand]
  have hRhsOperand2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc := by
    simp [hScratch1 .rhsOperand, hRhsOperand]
  have hSumScratch2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc := by
    simp [hScratch1 .sumScratch, hSumScratch]
  have hDiffScratch2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc := by
    simp [hScratch1 .diffScratch, hDiffScratch]
  have hPrologueCounter2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc := by
    simp [hScratch1 .prologueCounter, hPrologueCounter]
  have hPrologueWork2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc := by
    simp [hScratch1 .prologueWork, hPrologueWork]
  have hrun3 := flipBindEmitCleanup_drainScratch_run copyc queryc queryTmpc logTmpc workRevc lhsOperandc
    rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc
    { var1 with decision := false } (Function.update Sg1 (EmitK.base Kg.mem) []) hCopy2 hQuery2
    hQueryTmp2 hLogTmp2 hWorkRev2 hLhsOperand2 hRhsOperand2 hSumScratch2 hDiffScratch2
    hPrologueCounter2 hPrologueWork2
  set Sg3 := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update
          (Function.update Sg1 (EmitK.base Kg.mem) [])
          (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
        (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
    (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
    (EmitK.base (Kg.scratch .diffScratch)) []) (EmitK.base (Kg.scratch .prologueCounter)) [])
    (EmitK.base (Kg.scratch .prologueWork)) [] with hSg3
  have hIo3 : Sg3 (EmitK.base Kg.io) = io0 := by simp [hSg3, Function.update, hIo1]
  have hCd3 : Sg3 EmitK.countdown = cd0 := by simp [hSg3, Function.update, hCd1]
  have hrun4 := flipBindEmitCleanup_drainIo_run io0 { var1 with decision := false } Sg3 hIo3
  set Sg4 := Function.update Sg3 (EmitK.base Kg.io) [] with hSg4
  have hCd4 : Sg4 EmitK.countdown = cd0 := by simp [hSg4, hCd3]
  have hrun5 := flipBindEmitCleanup_drainCountdown_run cd0 { var1 with decision := false } Sg4 hCd4
  set Sg5 := Function.update Sg4 EmitK.countdown [] with hSg5
  have s2 : (flipBindEmitCleanup (p := p))^[(m0.length + 1) + n1]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainScratch ScratchKind.copyScratch),
          { var1 with decision := false }, Function.update Sg1 (EmitK.base Kg.mem) []⟩ := by
    rw [Function.iterate_add_apply, hrun1]; exact hrun2
  set scratchTotal := prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
      (diffScratchc.length + 1) + (sumScratchc.length + 1) + (rhsOperandc.length + 1) +
      (lhsOperandc.length + 1) + (workRevc.length + 1) + (logTmpc.length + 1) +
      (queryTmpc.length + 1) + (queryc.length + 1) + (copyc.length + 1) with hScratchTotal
  have s3 : (flipBindEmitCleanup (p := p))^[scratchTotal + ((m0.length + 1) + n1)]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainIo, { var1 with decision := false }, Sg3⟩ := by
    rw [Function.iterate_add_apply, s2]; exact hrun3
  have s4 : (flipBindEmitCleanup (p := p))^[(io0.length + 1) +
      (scratchTotal + ((m0.length + 1) + n1))]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainCountdown, { var1 with decision := false }, Sg4⟩ := by
    rw [Function.iterate_add_apply, s3]; exact hrun4
  have s5 : (flipBindEmitCleanup (p := p))^[(cd0.length + 1) + ((io0.length + 1) +
      (scratchTotal + ((m0.length + 1) + n1)))]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, { var1 with decision := false }, Sg5⟩ := by
    rw [Function.iterate_add_apply, s4]; exact hrun5
  refine ⟨_, { var1 with decision := false }, Sg5, s5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => by simp [hSg5, hSg4, hSg3, hdrained1 i (Nat.zero_le _)]
  · simp [hSg5, hSg4, hSg3]
  · intro sk; fin_cases sk <;> simp [hSg5, hSg4, hSg3]
  · simp [hSg5, hSg4]
  · simp [hSg5]
  · simp [hSg5, hSg4, hSg3, hOut1]

/-- Quantitative companion to `flipBindEmitCleanup_run_to_done`: same statement, plus a bound on the
    witness step count. Every cleanup operation except `drainReg` has an exact closed-form step
    count; register draining uses the explicit digit-length cap `M` supplied by the caller. -/
lemma flipBindEmitCleanup_run_to_done_bound (regs : Fin (regBound p) → ℕ) (M : ℕ)
    (hM : ∀ i : Fin (regBound p), (natToDigits (regs i)).length ≤ M) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit) (io0 : List Bool) (cd0 : List Unit)
    (var : CleanupState) (Sg : ∀ k, List (EmitΓ p k))
    (hReg : ∀ i : Fin (regBound p), Sg (EmitK.base (Kg.reg i)) = natToDigits (regs i))
    (hMem : Sg (EmitK.base Kg.mem) = m0)
    (hCopy : Sg (EmitK.base (Kg.scratch .copyScratch)) = copyc)
    (hQuery : Sg (EmitK.base (Kg.scratch .query)) = queryc)
    (hQueryTmp : Sg (EmitK.base (Kg.scratch .queryTmp)) = queryTmpc)
    (hLogTmp : Sg (EmitK.base (Kg.scratch .logTmp)) = logTmpc)
    (hWorkRev : Sg (EmitK.base (Kg.scratch .workRev)) = workRevc)
    (hLhsOperand : Sg (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc)
    (hRhsOperand : Sg (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc)
    (hSumScratch : Sg (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc)
    (hDiffScratch : Sg (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc)
    (hPrologueCounter : Sg (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc)
    (hPrologueWork : Sg (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc)
    (hIo : Sg (EmitK.base Kg.io) = io0) (hCd : Sg EmitK.countdown = cd0) :
    ∃ n var' Sg', (flipBindEmitCleanup (p := p))^[n]
        (some ⟨some (EmitCleanupPhase.drainReg ⟨0, by omega⟩), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), Sg' (EmitK.base (Kg.reg i)) = []) ∧
        Sg' (EmitK.base Kg.mem) = [] ∧
        (∀ sk : ScratchKind, Sg' (EmitK.base (Kg.scratch sk)) = []) ∧
        Sg' (EmitK.base Kg.io) = [] ∧ Sg' EmitK.countdown = [] ∧ Sg' EmitK.out = Sg EmitK.out ∧
        n ≤ (cd0.length + 1) + ((io0.length + 1) +
            ((prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
                (diffScratchc.length + 1) + (sumScratchc.length + 1) +
                (rhsOperandc.length + 1) + (lhsOperandc.length + 1) + (workRevc.length + 1) +
                (logTmpc.length + 1) + (queryTmpc.length + 1) + (queryc.length + 1) +
                (copyc.length + 1)) +
              ((m0.length + 1) + (regBound p * (M + 1) + 1)))) := by
  obtain ⟨n1, var1, Sg1, hrun1, hdrained1, hunchanged1, hn1bound⟩ :=
    flipBindEmitCleanup_drainReg_run_bound (regBound p) ⟨0, by omega⟩ (by simp)
      (fun i => natToDigits (regs i)) M (fun i _ => hM i) var Sg (fun i _ => hReg i)
  have hMem1 : Sg1 (EmitK.base Kg.mem) = m0 := by
    rw [hunchanged1 (EmitK.base Kg.mem) (fun i _ => by simp), hMem]
  have hScratch1 : ∀ sk : ScratchKind,
      Sg1 (EmitK.base (Kg.scratch sk)) = Sg (EmitK.base (Kg.scratch sk)) :=
    fun sk => hunchanged1 (EmitK.base (Kg.scratch sk)) (fun i _ => by simp)
  have hIo1 : Sg1 (EmitK.base Kg.io) = io0 := by
    rw [hunchanged1 (EmitK.base Kg.io) (fun i _ => by simp), hIo]
  have hCd1 : Sg1 EmitK.countdown = cd0 := by
    rw [hunchanged1 EmitK.countdown (fun i _ => by simp), hCd]
  have hOut1 : Sg1 EmitK.out = Sg EmitK.out :=
    hunchanged1 EmitK.out (fun i _ => by simp)
  have hrun2 := flipBindEmitCleanup_drainMem_run m0 var1 Sg1 hMem1
  have hCopy2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .copyScratch))
      = copyc := by simp [hScratch1 .copyScratch, hCopy]
  have hQuery2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .query))
      = queryc := by simp [hScratch1 .query, hQuery]
  have hQueryTmp2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .queryTmp))
      = queryTmpc := by simp [hScratch1 .queryTmp, hQueryTmp]
  have hLogTmp2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .logTmp))
      = logTmpc := by simp [hScratch1 .logTmp, hLogTmp]
  have hWorkRev2 : Function.update Sg1 (EmitK.base Kg.mem) [] (EmitK.base (Kg.scratch .workRev))
      = workRevc := by simp [hScratch1 .workRev, hWorkRev]
  have hLhsOperand2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc := by
    simp [hScratch1 .lhsOperand, hLhsOperand]
  have hRhsOperand2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc := by
    simp [hScratch1 .rhsOperand, hRhsOperand]
  have hSumScratch2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc := by
    simp [hScratch1 .sumScratch, hSumScratch]
  have hDiffScratch2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc := by
    simp [hScratch1 .diffScratch, hDiffScratch]
  have hPrologueCounter2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc := by
    simp [hScratch1 .prologueCounter, hPrologueCounter]
  have hPrologueWork2 : Function.update Sg1 (EmitK.base Kg.mem) []
      (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc := by
    simp [hScratch1 .prologueWork, hPrologueWork]
  have hrun3 := flipBindEmitCleanup_drainScratch_run copyc queryc queryTmpc logTmpc workRevc lhsOperandc
    rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc
    { var1 with decision := false } (Function.update Sg1 (EmitK.base Kg.mem) []) hCopy2 hQuery2
    hQueryTmp2 hLogTmp2 hWorkRev2 hLhsOperand2 hRhsOperand2 hSumScratch2 hDiffScratch2
    hPrologueCounter2 hPrologueWork2
  set Sg3 := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update
          (Function.update Sg1 (EmitK.base Kg.mem) [])
          (EmitK.base (Kg.scratch .copyScratch)) []) (EmitK.base (Kg.scratch .query)) [])
        (EmitK.base (Kg.scratch .queryTmp)) []) (EmitK.base (Kg.scratch .logTmp)) [])
      (EmitK.base (Kg.scratch .workRev)) []) (EmitK.base (Kg.scratch .lhsOperand)) [])
    (EmitK.base (Kg.scratch .rhsOperand)) []) (EmitK.base (Kg.scratch .sumScratch)) [])
    (EmitK.base (Kg.scratch .diffScratch)) []) (EmitK.base (Kg.scratch .prologueCounter)) [])
    (EmitK.base (Kg.scratch .prologueWork)) [] with hSg3
  have hIo3 : Sg3 (EmitK.base Kg.io) = io0 := by simp [hSg3, Function.update, hIo1]
  have hCd3 : Sg3 EmitK.countdown = cd0 := by simp [hSg3, Function.update, hCd1]
  have hrun4 := flipBindEmitCleanup_drainIo_run io0 { var1 with decision := false } Sg3 hIo3
  set Sg4 := Function.update Sg3 (EmitK.base Kg.io) [] with hSg4
  have hCd4 : Sg4 EmitK.countdown = cd0 := by simp [hSg4, hCd3]
  have hrun5 := flipBindEmitCleanup_drainCountdown_run cd0 { var1 with decision := false } Sg4 hCd4
  set Sg5 := Function.update Sg4 EmitK.countdown [] with hSg5
  have s2 : (flipBindEmitCleanup (p := p))^[(m0.length + 1) + n1]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some (EmitCleanupPhase.drainScratch ScratchKind.copyScratch),
          { var1 with decision := false }, Function.update Sg1 (EmitK.base Kg.mem) []⟩ := by
    rw [Function.iterate_add_apply, hrun1]; exact hrun2
  set scratchTotal := prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
      (diffScratchc.length + 1) + (sumScratchc.length + 1) + (rhsOperandc.length + 1) +
      (lhsOperandc.length + 1) + (workRevc.length + 1) + (logTmpc.length + 1) +
      (queryTmpc.length + 1) + (queryc.length + 1) + (copyc.length + 1) with hScratchTotal
  have s3 : (flipBindEmitCleanup (p := p))^[scratchTotal + ((m0.length + 1) + n1)]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainIo, { var1 with decision := false }, Sg3⟩ := by
    rw [Function.iterate_add_apply, s2]; exact hrun3
  have s4 : (flipBindEmitCleanup (p := p))^[(io0.length + 1) +
      (scratchTotal + ((m0.length + 1) + n1))]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.drainCountdown, { var1 with decision := false }, Sg4⟩ := by
    rw [Function.iterate_add_apply, s3]; exact hrun4
  have s5 : (flipBindEmitCleanup (p := p))^[(cd0.length + 1) + ((io0.length + 1) +
      (scratchTotal + ((m0.length + 1) + n1)))]
      (some ⟨some (EmitCleanupPhase.drainReg (⟨0, by omega⟩ : Fin (regBound p + 1))), var, Sg⟩)
      = some ⟨some EmitCleanupPhase.done, { var1 with decision := false }, Sg5⟩ := by
    rw [Function.iterate_add_apply, s4]; exact hrun5
  refine ⟨_, { var1 with decision := false }, Sg5, s5, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · exact fun i => by simp [hSg5, hSg4, hSg3, hdrained1 i (Nat.zero_le _)]
  · simp [hSg5, hSg4, hSg3]
  · intro sk; fin_cases sk <;> simp [hSg5, hSg4, hSg3]
  · simp [hSg5, hSg4]
  · simp [hSg5]
  · simp [hSg5, hSg4, hSg3, hOut1]

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.GenericPrologue
public import Mathlib.Tactic.FinCases

/-!
# Cleanup: extracting the decider's answer bit and draining every stack before `halt`

`Represents` states every checkpoint's `AllInstrState`/scratch-emptiness invariant only while the
RAM is still executing; nothing forces the *last* configuration (RAM halted) into a genuine TM2
`halt`. `entryAt`'s out-of-range-PC branch already routes every `done`-bridge there to
`Λg.cleanup CleanupPhase.checkHead` (`GenericProgramMachine.lean`), but that label had no `Stmt`
tree until this file: cleanup must (1) read the decider's answer out of register `outReg` (a
`Bool`, encoded the same way every register is — `natToDigits`, so `1` or nothing at all),
(2) push that bit onto `Kg.io` (empty before cleanup in the full execution), making this the
sole output bit; then (3) drain every other stack to `[]` so the final
`Turing.TM2.Stmt.halt` leaves a config that `TM2OutputsInTime`-style theorems can read the output
off of. `outReg` is deliberately *not* threaded into `Λg`/`entryAt`/`bridgeTo`/`Represents`
(`CleanupPhase`'s own docstring) — it is a parameter of `cleanupProg` alone, which keeps the
existing `bridgeTo` call sites independent of the selected output register.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (MemSym)
open Turing Turing.TM2.Stmt

variable (p : List Instruction)

/-- The cleanup phase's realization (`CleanupPhase`'s own docstring spells out each phase's
    role). `outReg` is an explicit parameter (not baked into `CleanupPhase p`, which stays
    `p`-only) so `Λg p`/`entryAt`/`bridgeTo`/`Represents` never need to know which register a
    particular decider instance answers through. -/
def cleanupProg (outReg : Fin (regBound p)) :
    CleanupPhase p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState
  | .checkHead =>
      pop (Kg.reg outReg) (fun s ov => { s with decision := decide (ov = some (1 : Digit)) })
        (goto (fun _ => Λg.cleanup CleanupPhase.checkTail))
  | .checkTail =>
      pop (Kg.reg outReg) (fun s ov => { s with decision := s.decision && decide (ov = none) })
        (goto (fun _ => Λg.cleanup CleanupPhase.pushAnswer))
  | .pushAnswer =>
      push Kg.io (fun s => s.decision)
        (goto (fun _ => Λg.cleanup (CleanupPhase.drainReg ⟨0, by omega⟩)))
  | .drainReg cursor =>
      if h : cursor.val < regBound p then
        pop (Kg.reg ⟨cursor.val, h⟩) (fun s ov => { s with decision := ov.isSome })
          (branch (fun s => s.decision)
            (goto (fun _ => Λg.cleanup (CleanupPhase.drainReg cursor)))
            (goto (fun _ => Λg.cleanup (CleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩))))
      else
        goto (fun _ => Λg.cleanup CleanupPhase.drainMem)
  | .drainMem =>
      pop Kg.mem (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => Λg.cleanup CleanupPhase.drainMem))
          (goto (fun _ => Λg.cleanup (CleanupPhase.drainScratch ScratchKind.copyScratch))))
  | .drainScratch sk =>
      pop (Kg.scratch sk) (fun s ov => { s with decision := ov.isSome })
        (branch (fun s => s.decision)
          (goto (fun _ => Λg.cleanup (CleanupPhase.drainScratch sk)))
          (goto (fun _ => match nextScratchKind sk with
            | some sk' => Λg.cleanup (CleanupPhase.drainScratch sk')
            | none => Λg.cleanup CleanupPhase.done)))
  | .done => load (fun _ => AllInstrState.canonical) halt

/-- Any dispatcher `M` that installs `cleanupProg p outReg` at every cleanup label — abstracting
    over `M` the same way `PrologueAgrees` does for the prologue. -/
def CleanupAgrees (p : List Instruction) (outReg : Fin (regBound p))
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) : Prop :=
  ∀ ph, M (Λg.cleanup ph) = cleanupProg p outReg ph

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate` — identical shape to
    `flipBindPrologue`, kept as its own definition since `CleanupAgrees` (not `PrologueAgrees`) is
    the hypothesis its step lemmas carry. -/
def flipBindCleanup (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) :
    Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) →
      Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) :=
  fun x => x.bind (Turing.TM2.step M)

variable {p : List Instruction} {outReg : Fin (regBound p)}
  {M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState}

/-- `checkHead` pops `outReg`'s first digit: `decision` becomes `true` exactly when that digit is
    `1` (the start of checking `outReg = natToDigits 1`). -/
lemma cleanup_step_checkHead (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (d : List Digit) (hReg : Sg (Kg.reg outReg) = d) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.checkTail),
          { var with decision := decide (d.head? = some (1 : Digit)) },
          Function.update Sg (Kg.reg outReg) d.tail⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩ = _
  cases d with
  | nil => simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .checkHead, cleanupProg, hReg]
  | cons d0 rest =>
    simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .checkHead, cleanupProg, hReg]

/-- `checkTail` pops `outReg`'s second digit: `decision` (already `true` iff the first digit was
    `1`) becomes `&&`-ed with "no second digit" — together `checkHead`+`checkTail` decide
    `outReg`'s stack was exactly the singleton `[1]`. -/
lemma cleanup_step_checkTail (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (d : List Digit) (hReg : Sg (Kg.reg outReg) = d) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.checkTail), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.pushAnswer),
          { var with decision := var.decision && decide (d = []) },
          Function.update Sg (Kg.reg outReg) d.tail⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.checkTail), var, Sg⟩ = _
  cases d with
  | nil => simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .checkTail, cleanupProg, hReg]
  | cons d0 rest =>
    simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .checkTail, cleanupProg, hReg]

/-- `pushAnswer` pushes `decision` onto `Kg.io`. -/
lemma cleanup_step_pushAnswer (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.pushAnswer), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainReg ⟨0, by omega⟩)), var,
          Function.update Sg Kg.io (var.decision :: Sg Kg.io)⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.pushAnswer), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .pushAnswer, cleanupProg]

/-- `drainReg cursor` (`cursor` in range) on a nonempty register: pop one digit, loop back on the
    same `cursor`. -/
lemma cleanup_step_drainReg_cons (hAgrees : CleanupAgrees p outReg M)
    (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (d : Digit) (rest : List Digit)
    (hReg : Sg (Kg.reg ⟨cursor.val, h⟩) = d :: rest) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), { var with decision := true },
          Function.update Sg (Kg.reg ⟨cursor.val, h⟩) rest⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees (.drainReg cursor), cleanupProg, h, hReg]

/-- `drainReg cursor` (`cursor` in range) on an exhausted register: advance to `cursor + 1`. -/
lemma cleanup_step_drainReg_nil (hAgrees : CleanupAgrees p outReg M)
    (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hReg : Sg (Kg.reg ⟨cursor.val, h⟩) = ([] : List Digit)) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩)),
          { var with decision := false },
          Function.update Sg (Kg.reg ⟨cursor.val, h⟩) []⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees (.drainReg cursor), cleanupProg, h, hReg,
    update_self_of_eq Sg (Kg.reg ⟨cursor.val, h⟩) [] hReg]

/-- `drainReg cursor` at the sentinel (`cursor.val = regBound p`): every register drained, move
    to `drainMem`. -/
lemma cleanup_step_drainReg_sentinel (hAgrees : CleanupAgrees p outReg M)
    (cursor : Fin (regBound p + 1)) (h : cursor.val = regBound p) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees (.drainReg cursor), cleanupProg,
    Nat.not_lt.mpr (le_of_eq h.symm)]

/-- `drainMem` on a nonempty write-log: pop one symbol, loop back. -/
lemma cleanup_step_drainMem_cons (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (d : MemSym) (rest : List MemSym) (hMem : Sg Kg.mem = d :: rest) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.drainMem), { var with decision := true },
          Function.update Sg Kg.mem rest⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .drainMem, cleanupProg, hMem]

/-- `drainMem` on an exhausted write-log: move to `drainScratch`, starting at
    `ScratchKind.copyScratch`. -/
lemma cleanup_step_drainMem_nil (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hMem : Sg Kg.mem = ([] : List MemSym)) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainScratch ScratchKind.copyScratch)),
          { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .drainMem, cleanupProg, hMem,
    update_self_of_eq Sg Kg.mem [] hMem]

/-- `drainScratch sk` on a nonempty scratch stack: pop one digit, loop back on the same `sk`. -/
lemma cleanup_step_drainScratch_cons (hAgrees : CleanupAgrees p outReg M) (sk : ScratchKind)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k)) (d : ScratchΓ sk) (rest : List (ScratchΓ sk))
    (hSk : Sg (Kg.scratch sk) = d :: rest) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), { var with decision := true },
          Function.update Sg (Kg.scratch sk) rest⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees (.drainScratch sk), cleanupProg, hSk]

/-- `drainScratch sk` on an exhausted stack: advance via `nextScratchKind`, or move to `done` at
    the chain's end. -/
lemma cleanup_step_drainScratch_nil (hAgrees : CleanupAgrees p outReg M) (sk : ScratchKind)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k)) (hSk : Sg (Kg.scratch sk) = ([] : List (ScratchΓ sk))) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), var, Sg⟩)
      = some ⟨some (match nextScratchKind sk with
          | some sk' => Λg.cleanup (CleanupPhase.drainScratch sk')
          | none => Λg.cleanup CleanupPhase.done),
          { var with decision := false }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees (.drainScratch sk), cleanupProg, hSk,
    update_self_of_eq Sg (Kg.scratch sk) [] hSk]

/-- `drainReg cursor`'s aggregate effect on the *one* register `cursor` names (in range):
    `content.length + 1` steps drain it to `[]`, advancing to `cursor + 1`. Mirrors
    `GenericPrologue.lean`'s `prologue_incCopyRest_run` shape (destructive single-stack drain,
    no restore needed). -/
lemma cleanup_drain_one_reg_run (hAgrees : CleanupAgrees p outReg M)
    (cursor : Fin (regBound p + 1)) (h : cursor.val < regBound p) (content : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hReg : Sg (Kg.reg ⟨cursor.val, h⟩) = content) :
    (flipBindCleanup p M)^[content.length + 1]
        (some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainReg ⟨cursor.val + 1, by omega⟩)),
          { var with decision := false },
          Function.update Sg (Kg.reg ⟨cursor.val, h⟩) []⟩ := by
  induction content generalizing var Sg with
  | nil => simpa using cleanup_step_drainReg_nil hAgrees cursor h var Sg hReg
  | cons d rest ih =>
    have hstep := cleanup_step_drainReg_cons hAgrees cursor h var Sg d rest hReg
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (Kg.reg ⟨cursor.val, h⟩) rest)
        (by simp)]
    simp [Function.update_idem]

/-- The register-draining loop's run, plus the fact that the TM
    step count `n` is bounded by the total digit length of every register from `cursor` onward
    (`content`'s own sum, `regSize`'s per-register unit) plus one "+1" overhead step per register
    plus the final sentinel step. Kept as a separate lemma from the plain drain facts above since
    only `cleanup_run_bound` needs the step count. -/
lemma cleanup_drainReg_run_bound (hAgrees : CleanupAgrees p outReg M) (k : ℕ)
    (cursor : Fin (regBound p + 1)) (hk : cursor.val + k = regBound p)
    (content : Fin (regBound p) → List Digit) (var : AllInstrState) (Sg : ∀ k', List (Γg p k'))
    (hReg : ∀ i : Fin (regBound p), cursor.val ≤ i.val → Sg (Kg.reg i) = content i) :
    ∃ n var' Sg', (flipBindCleanup p M)^[n]
        (some ⟨some (Λg.cleanup (CleanupPhase.drainReg cursor)), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.drainMem), var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), cursor.val ≤ i.val → Sg' (Kg.reg i) = []) ∧
        (∀ k' : Kg p, (∀ i : Fin (regBound p), cursor.val ≤ i.val → k' ≠ Kg.reg i) →
          Sg' k' = Sg k') ∧
        n ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin (regBound p) => cursor.val ≤ i.val),
              (content i).length) + k + 1 := by
  induction k generalizing cursor var Sg with
  | zero =>
    refine ⟨1, var, Sg, ?_, ?_, fun _ _ => rfl, ?_⟩
    · simpa using cleanup_step_drainReg_sentinel hAgrees cursor (by omega) var Sg
    · intro i hi
      omega
    · have hz : (0:ℕ) ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin (regBound p) => cursor.val ≤ i.val),
            (content i).length := Nat.zero_le _
      omega
  | succ k ih =>
    have h : cursor.val < regBound p := by omega
    have hltp1 : cursor.val + 1 < regBound p + 1 := by omega
    have hcv : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val = cursor.val + 1 := rfl
    have hrun1 := cleanup_drain_one_reg_run hAgrees cursor h (content ⟨cursor.val, h⟩) var Sg
      (hReg ⟨cursor.val, h⟩ le_rfl)
    have hk' : (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val + k = regBound p := by
      rw [hcv]; omega
    have hReg2 : ∀ i : Fin (regBound p),
        (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val ≤ i.val →
        Function.update Sg (Kg.reg ⟨cursor.val, h⟩) [] (Kg.reg i) = content i := by
      intro i hi
      rw [hcv] at hi
      have hne : Kg.reg i ≠ Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p)) := by
        simp only [ne_eq, Kg.reg.injEq]
        intro heqi
        have hival : i.val = cursor.val := congrArg Fin.val heqi
        omega
      rw [Function.update_of_ne hne]
      exact hReg i (by omega)
    obtain ⟨n2, var2, Sg2, hrun2, hdrained2, hunchanged2, hbound2⟩ :=
      ih ⟨cursor.val + 1, hltp1⟩ hk' { var with decision := false }
        (Function.update Sg (Kg.reg ⟨cursor.val, h⟩) []) hReg2
    refine ⟨n2 + ((content ⟨cursor.val, h⟩).length + 1), var2, Sg2, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hrun1, hrun2]
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hlt
      · have hi' : i = ⟨cursor.val, h⟩ := Fin.ext heq.symm
        have hstep := hunchanged2 (Kg.reg i) (by
          intro j hj
          rw [hcv] at hj
          simp only [ne_eq, Kg.reg.injEq]
          intro heqij
          have hval : i.val = j.val := congrArg Fin.val heqij
          rw [hi'] at hval
          omega)
        rw [hstep, hi']
        simp
      · exact hdrained2 i (by rw [hcv]; omega)
    · intro k' hk'2
      have hne2 : k' ≠ Kg.reg (⟨cursor.val, h⟩ : Fin (regBound p)) := hk'2 ⟨cursor.val, h⟩ le_rfl
      rw [hunchanged2 k' (fun i hi => hk'2 i (by rw [hcv] at hi; omega)),
        Function.update_of_ne hne2]
    · have hsplit : Finset.univ.filter (fun i : Fin (regBound p) => cursor.val ≤ i.val) =
          insert (⟨cursor.val, h⟩ : Fin (regBound p))
            (Finset.univ.filter (fun i : Fin (regBound p) =>
              (⟨cursor.val + 1, hltp1⟩ : Fin (regBound p + 1)).val ≤ i.val)) := by
        rw [hcv]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          rcases eq_or_lt_of_le hi with heq | hlt
          · left; exact Fin.ext heq.symm
          · right; omega
        · rintro (heq | hi)
          · rw [heq]
          · omega
      rw [hsplit, Finset.sum_insert (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega)]
      omega

/-- `drainMem`'s aggregate effect: `content.length + 1` steps drain `Kg.mem` to `[]`, moving to
    `drainScratch ScratchKind.copyScratch`. -/
lemma cleanup_drainMem_run (hAgrees : CleanupAgrees p outReg M) (content : List MemSym)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k)) (hMem : Sg Kg.mem = content) :
    (flipBindCleanup p M)^[content.length + 1]
        (some ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainScratch ScratchKind.copyScratch)),
          { var with decision := false }, Function.update Sg Kg.mem []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg Kg.mem [] hMem]
    simpa using cleanup_step_drainMem_nil hAgrees var Sg hMem
  | cons d rest ih =>
    have hstep := cleanup_step_drainMem_cons hAgrees var Sg d rest hMem
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg Kg.mem rest) (by simp)]
    simp [Function.update_idem]

/-- `drainScratch sk`'s aggregate effect on the *one* stack `sk` names: `content.length + 1`
    steps drain it to `[]`, advancing via `nextScratchKind` (or `done` at the chain's end). -/
lemma cleanup_drain_one_scratch_run (hAgrees : CleanupAgrees p outReg M) (sk : ScratchKind)
    (content : List (ScratchΓ sk)) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hSk : Sg (Kg.scratch sk) = content) :
    (flipBindCleanup p M)^[content.length + 1]
        (some ⟨some (Λg.cleanup (CleanupPhase.drainScratch sk)), var, Sg⟩)
      = some ⟨some (match nextScratchKind sk with
          | some sk' => Λg.cleanup (CleanupPhase.drainScratch sk')
          | none => Λg.cleanup CleanupPhase.done),
          { var with decision := false }, Function.update Sg (Kg.scratch sk) []⟩ := by
  induction content generalizing var Sg with
  | nil =>
    rw [update_self_of_eq Sg (Kg.scratch sk) [] hSk]
    simpa using cleanup_step_drainScratch_nil hAgrees sk var Sg hSk
  | cons d rest ih =>
    have hstep := cleanup_step_drainScratch_cons hAgrees sk var Sg d rest hSk
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih { var with decision := true } (Function.update Sg (Kg.scratch sk) rest) (by simp)]
    simp [Function.update_idem]

/-- `done` resets `var` to canonical and reaches a genuine `halt` (`l = none`). -/
lemma cleanup_step_done (hAgrees : CleanupAgrees p outReg M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindCleanup p M (some ⟨some (Λg.cleanup CleanupPhase.done), var, Sg⟩)
      = some ⟨none, AllInstrState.canonical, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.cleanup CleanupPhase.done), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .done, cleanupProg]

/-- `drainScratch`'s full run: `cleanup_drain_one_scratch_run` chained across every `ScratchKind`
    (`nextScratchKind`'s fixed order), from `copyScratch` all the way to `done`.
    Each stack's current contents are read from the preceding `Function.update`; this empties
    each scratch stack exactly once in the fixed order. -/
lemma cleanup_drainScratch_run (hAgrees : CleanupAgrees p outReg M)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCopy : Sg (Kg.scratch .copyScratch) = copyc) (hQuery : Sg (Kg.scratch .query) = queryc)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = queryTmpc)
    (hLogTmp : Sg (Kg.scratch .logTmp) = logTmpc)
    (hWorkRev : Sg (Kg.scratch .workRev) = workRevc)
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = lhsOperandc)
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = rhsOperandc)
    (hSumScratch : Sg (Kg.scratch .sumScratch) = sumScratchc)
    (hDiffScratch : Sg (Kg.scratch .diffScratch) = diffScratchc)
    (hPrologueCounter : Sg (Kg.scratch .prologueCounter) = prologueCounterc)
    (hPrologueWork : Sg (Kg.scratch .prologueWork) = prologueWorkc) :
    (flipBindCleanup p M)^[prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
        (diffScratchc.length + 1) + (sumScratchc.length + 1) + (rhsOperandc.length + 1) +
        (lhsOperandc.length + 1) + (workRevc.length + 1) + (logTmpc.length + 1) +
        (queryTmpc.length + 1) + (queryc.length + 1) + (copyc.length + 1)]
        (some ⟨some (Λg.cleanup (CleanupPhase.drainScratch .copyScratch)), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.done), { var with decision := false },
          Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update Sg
                (Kg.scratch .copyScratch) []) (Kg.scratch .query) [])
                (Kg.scratch .queryTmp) []) (Kg.scratch .logTmp) [])
              (Kg.scratch .workRev) []) (Kg.scratch .lhsOperand) [])
            (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) [])
          (Kg.scratch .diffScratch) []) (Kg.scratch .prologueCounter) [])
        (Kg.scratch .prologueWork) []⟩ := by
  have h1 := cleanup_drain_one_scratch_run hAgrees .copyScratch copyc var Sg hCopy
  have h2 := cleanup_drain_one_scratch_run hAgrees .query queryc { var with decision := false }
    (Function.update Sg (Kg.scratch .copyScratch) []) (by simp [hQuery])
  have h3 := cleanup_drain_one_scratch_run hAgrees .queryTmp queryTmpc { var with decision := false }
    (Function.update (Function.update Sg (Kg.scratch .copyScratch) []) (Kg.scratch .query) [])
    (by simp [hQueryTmp])
  have h4 := cleanup_drain_one_scratch_run hAgrees .logTmp logTmpc { var with decision := false }
    (Function.update (Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
      (Kg.scratch .query) []) (Kg.scratch .queryTmp) []) (by simp [hLogTmp])
  have h5 := cleanup_drain_one_scratch_run hAgrees .workRev workRevc { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update Sg
      (Kg.scratch .copyScratch) []) (Kg.scratch .query) []) (Kg.scratch .queryTmp) [])
      (Kg.scratch .logTmp) []) (by simp [hWorkRev])
  have h6 := cleanup_drain_one_scratch_run hAgrees .lhsOperand lhsOperandc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update Sg
      (Kg.scratch .copyScratch) []) (Kg.scratch .query) []) (Kg.scratch .queryTmp) [])
      (Kg.scratch .logTmp) []) (Kg.scratch .workRev) []) (by simp [hLhsOperand])
  have h7 := cleanup_drain_one_scratch_run hAgrees .rhsOperand rhsOperandc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update Sg (Kg.scratch .copyScratch) []) (Kg.scratch .query) [])
      (Kg.scratch .queryTmp) []) (Kg.scratch .logTmp) []) (Kg.scratch .workRev) [])
      (Kg.scratch .lhsOperand) []) (by simp [hRhsOperand])
  have h8 := cleanup_drain_one_scratch_run hAgrees .sumScratch sumScratchc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update Sg (Kg.scratch .copyScratch) []) (Kg.scratch .query) [])
      (Kg.scratch .queryTmp) []) (Kg.scratch .logTmp) []) (Kg.scratch .workRev) [])
      (Kg.scratch .lhsOperand) []) (Kg.scratch .rhsOperand) []) (by simp [hSumScratch])
  have h9 := cleanup_drain_one_scratch_run hAgrees .diffScratch diffScratchc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update Sg (Kg.scratch .copyScratch) [])
      (Kg.scratch .query) []) (Kg.scratch .queryTmp) []) (Kg.scratch .logTmp) [])
      (Kg.scratch .workRev) []) (Kg.scratch .lhsOperand) []) (Kg.scratch .rhsOperand) [])
      (Kg.scratch .sumScratch) []) (by simp [hDiffScratch])
  have h10 := cleanup_drain_one_scratch_run hAgrees .prologueCounter prologueCounterc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update Sg
      (Kg.scratch .copyScratch) []) (Kg.scratch .query) []) (Kg.scratch .queryTmp) [])
      (Kg.scratch .logTmp) []) (Kg.scratch .workRev) []) (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) []) (Kg.scratch .diffScratch) [])
    (by simp [hPrologueCounter])
  have h11 := cleanup_drain_one_scratch_run hAgrees .prologueWork prologueWorkc
    { var with decision := false }
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update Sg
      (Kg.scratch .copyScratch) []) (Kg.scratch .query) []) (Kg.scratch .queryTmp) [])
      (Kg.scratch .logTmp) []) (Kg.scratch .workRev) []) (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) []) (Kg.scratch .diffScratch) [])
      (Kg.scratch .prologueCounter) []) (by simp [hPrologueWork])
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

/-- The two-digit check of `checkHead`/`checkTail` decides exactly `n = 1`: the digit list of `n`
    is `[1]` iff its head is `1` and its tail is empty. -/
lemma cleanup_run_bound_decision (n : ℕ) :
    (decide ((natToDigits n).head? = some (1 : Digit)) &&
      decide ((natToDigits n).tail = ([] : List Digit))) = decide (n = 1) := by
  have hchar : ∀ l : List Digit, (l.head? = some (1 : Digit) ∧ l.tail = []) ↔ l = [1] := by
    intro l
    cases l with
    | nil => simp
    | cons d rest =>
      cases rest with
      | nil => simp [List.head?_cons]
      | cons _ _ => simp
  by_cases hans : n = 1
  · rw [hans]
    have h1 : natToDigits 1 = [(1 : Digit)] := by decide
    simp [h1]
  · have hne : natToDigits n ≠ [(1 : Digit)] := by
      intro heq
      apply hans
      have hval := congrArg digitsToNat heq
      rwa [digitsToNat_natToDigits, show digitsToNat [(1 : Digit)] = 1 from by decide] at hval
    have hne2 : ¬ ((natToDigits n).head? = some (1 : Digit) ∧ (natToDigits n).tail = []) :=
      fun h => hne ((hchar _).mp h)
    rw [not_and_or] at hne2
    simp only [hans, decide_false]
    rcases hne2 with h | h
    · simp [h]
    · simp [h]

/-- `cleanup_run_bound`'s opening: `checkHead`, `checkTail`, `pushAnswer` take three steps, pop
    the (at most two) answer digits off `outReg`, and push the decision `regs outReg = 1` onto
    `io`; every other stack is untouched. -/
lemma cleanup_run_bound_head (hAgrees : CleanupAgrees p outReg M) (regs : Fin (regBound p) → ℕ)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hReg : ∀ i : Fin (regBound p), Sg (Kg.reg i) = natToDigits (regs i)) :
    ∃ Sg3, (flipBindCleanup p M)^[1 + (1 + 1)]
        (some ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩)
      = some ⟨some (Λg.cleanup (CleanupPhase.drainReg ⟨0, by omega⟩)),
          { var with decision := decide (regs outReg = 1) }, Sg3⟩ ∧
      (∀ i : Fin (regBound p), Sg3 (Kg.reg i) =
        (if i = outReg then (natToDigits (regs outReg)).tail.tail else natToDigits (regs i))) ∧
      Sg3 Kg.io = decide (regs outReg = 1) :: Sg Kg.io ∧
      (∀ k : Kg p, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → k ≠ Kg.io → Sg3 k = Sg k) := by
  have hstep1 := cleanup_step_checkHead hAgrees var Sg (natToDigits (regs outReg)) (hReg outReg)
  have hstep2 := cleanup_step_checkTail hAgrees
    { var with decision := decide ((natToDigits (regs outReg)).head? = some (1 : Digit)) }
    (Function.update Sg (Kg.reg outReg) (natToDigits (regs outReg)).tail)
    (natToDigits (regs outReg)).tail (by simp)
  rw [cleanup_run_bound_decision] at hstep2
  have hstep3 := cleanup_step_pushAnswer hAgrees
    { var with decision := decide (regs outReg = 1) }
    (Function.update (Function.update Sg (Kg.reg outReg) (natToDigits (regs outReg)).tail)
      (Kg.reg outReg) (natToDigits (regs outReg)).tail.tail)
  have t2 : (flipBindCleanup p M)^[1 + 1]
      (some ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.pushAnswer),
          { var with decision := decide (regs outReg = 1) },
          Function.update (Function.update Sg (Kg.reg outReg) (natToDigits (regs outReg)).tail)
            (Kg.reg outReg) (natToDigits (regs outReg)).tail.tail⟩ := by
    rw [Function.iterate_add_apply, Function.iterate_one, hstep1]
    exact hstep2
  refine ⟨Function.update
      (Function.update (Function.update Sg (Kg.reg outReg) (natToDigits (regs outReg)).tail)
        (Kg.reg outReg) (natToDigits (regs outReg)).tail.tail)
      Kg.io (decide (regs outReg = 1) :: Sg Kg.io), ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, t2, Function.iterate_one]; exact hstep3
  · intro i
    by_cases hi : i = outReg
    · subst hi; simp [Function.update]
    · simp [Function.update, hi, hReg i]
  · simp [Function.update]
  · intro k hk hio
    have hk' : k ≠ Kg.reg outReg := hk outReg
    simp [Function.update, hk', hio]

/-- The register-draining phase of `cleanup_run_bound`: once the answer digits are popped, every
    register is emptied within `∑ lengths + regBound p + 1` steps and every non-register stack is
    untouched. -/
lemma cleanup_run_bound_regs (hAgrees : CleanupAgrees p outReg M) (regs : Fin (regBound p) → ℕ)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hReg : ∀ i : Fin (regBound p), Sg (Kg.reg i) =
      (if i = outReg then (natToDigits (regs outReg)).tail.tail else natToDigits (regs i))) :
    ∃ n var' Sg', (flipBindCleanup p M)^[n]
        (some ⟨some (Λg.cleanup (CleanupPhase.drainReg ⟨0, by omega⟩)), var, Sg⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.drainMem), var', Sg'⟩ ∧
        (∀ i : Fin (regBound p), Sg' (Kg.reg i) = []) ∧
        (∀ k : Kg p, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sg' k = Sg k) ∧
        n ≤ (∑ i : Fin (regBound p), (natToDigits (regs i)).length) + regBound p + 1 := by
  obtain ⟨n, var', Sg', hrun, hdrained, hunchanged, hbound⟩ :=
    cleanup_drainReg_run_bound hAgrees (regBound p) ⟨0, by omega⟩ (by simp)
      (fun i => if i = outReg then (natToDigits (regs outReg)).tail.tail else natToDigits (regs i))
      var Sg (fun i _ => hReg i)
  have hcontentLe : ∀ i : Fin (regBound p),
      ((fun i => if i = outReg then (natToDigits (regs outReg)).tail.tail
        else natToDigits (regs i)) i).length ≤ (natToDigits (regs i)).length := by
    intro i
    by_cases hi : i = outReg
    · simp only [hi]
      have h1 : (natToDigits (regs outReg)).tail.tail.length ≤
          (natToDigits (regs outReg)).tail.length := by
        cases (natToDigits (regs outReg)).tail <;> simp
      have h2 : (natToDigits (regs outReg)).tail.length ≤ (natToDigits (regs outReg)).length := by
        cases natToDigits (regs outReg) <;> simp
      exact le_trans h1 h2
    · simp [hi]
  have hfilterUniv : Finset.univ.filter
      (fun i : Fin (regBound p) => (⟨0, by omega⟩ : Fin (regBound p + 1)).val ≤ i.val) =
      Finset.univ := Finset.filter_true_of_mem (fun i _ => Nat.zero_le _)
  refine ⟨n, var', Sg', hrun, fun i => hdrained i (Nat.zero_le _),
    fun k hk => hunchanged k (fun i _ => hk i), ?_⟩
  rw [hfilterUniv] at hbound
  have hsum : (∑ i : Fin (regBound p), ((fun i => if i = outReg then
        (natToDigits (regs outReg)).tail.tail else natToDigits (regs i)) i).length) ≤
      ∑ i : Fin (regBound p), (natToDigits (regs i)).length :=
    Finset.sum_le_sum (fun i _ => hcontentLe i)
  beta_reduce at hbound hsum
  omega

/-- `cleanup_run_bound`'s closing: `drainMem`, the eleven `drainScratch` stages, and `done` empty
    the write-log and every scratch stack and reach `halt`, leaving all other stacks untouched. -/
lemma cleanup_run_bound_tail (hAgrees : CleanupAgrees p outReg M) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hMem : Sg Kg.mem = m0)
    (hCopy : Sg (Kg.scratch .copyScratch) = copyc) (hQuery : Sg (Kg.scratch .query) = queryc)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = queryTmpc)
    (hLogTmp : Sg (Kg.scratch .logTmp) = logTmpc)
    (hWorkRev : Sg (Kg.scratch .workRev) = workRevc)
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = lhsOperandc)
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = rhsOperandc)
    (hSumScratch : Sg (Kg.scratch .sumScratch) = sumScratchc)
    (hDiffScratch : Sg (Kg.scratch .diffScratch) = diffScratchc)
    (hPrologueCounter : Sg (Kg.scratch .prologueCounter) = prologueCounterc)
    (hPrologueWork : Sg (Kg.scratch .prologueWork) = prologueWorkc) :
    ∃ n Sg', (flipBindCleanup p M)^[n]
        (some ⟨some (Λg.cleanup CleanupPhase.drainMem), var, Sg⟩)
      = some ⟨none, AllInstrState.canonical, Sg'⟩ ∧
        Sg' Kg.mem = [] ∧ (∀ sk : ScratchKind, Sg' (Kg.scratch sk) = []) ∧
        (∀ k : Kg p, k ≠ Kg.mem → (∀ sk : ScratchKind, k ≠ Kg.scratch sk) → Sg' k = Sg k) ∧
        n ≤ m0.length + copyc.length + queryc.length + queryTmpc.length + logTmpc.length +
          workRevc.length + lhsOperandc.length + rhsOperandc.length + sumScratchc.length +
          diffScratchc.length + prologueCounterc.length + prologueWorkc.length + 13 := by
  have hrun5 := cleanup_drainMem_run hAgrees m0 var Sg hMem
  have hrun6 := cleanup_drainScratch_run hAgrees copyc queryc queryTmpc logTmpc workRevc
    lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc
    { var with decision := false } (Function.update Sg Kg.mem [])
    (by simp [hCopy]) (by simp [hQuery]) (by simp [hQueryTmp]) (by simp [hLogTmp])
    (by simp [hWorkRev]) (by simp [hLhsOperand]) (by simp [hRhsOperand])
    (by simp [hSumScratch]) (by simp [hDiffScratch]) (by simp [hPrologueCounter])
    (by simp [hPrologueWork])
  refine ⟨1 + (prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
      (diffScratchc.length + 1) + (sumScratchc.length + 1) + (rhsOperandc.length + 1) +
      (lhsOperandc.length + 1) + (workRevc.length + 1) + (logTmpc.length + 1) +
      (queryTmpc.length + 1) + (queryc.length + 1) + (copyc.length + 1) + (m0.length + 1)),
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update Sg Kg.mem [])
          (Kg.scratch .copyScratch) []) (Kg.scratch .query) [])
          (Kg.scratch .queryTmp) []) (Kg.scratch .logTmp) [])
        (Kg.scratch .workRev) []) (Kg.scratch .lhsOperand) [])
      (Kg.scratch .rhsOperand) []) (Kg.scratch .sumScratch) [])
    (Kg.scratch .diffScratch) []) (Kg.scratch .prologueCounter) [])
  (Kg.scratch .prologueWork) [], ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, hrun5, hrun6,
      Function.iterate_one]
    exact cleanup_step_done hAgrees _ _
  · simp
  · intro sk
    fin_cases sk <;> simp
  · intro k hk hsk
    simp only [Function.update_of_ne hk, Function.update_of_ne (hsk _)]
  · omega
/-- The cleanup phase's full run: `checkHead` through `done`,
    draining every register/memory/scratch cell, plus a bound on the total TM step count `n` —
    linear in the total register digit length (`regSize`'s per-register unit, summed) plus every
    scratch/mem stack's length, plus a fixed per-stack overhead (`regBound p` "+1"s for the
    drained registers, `17` for the remaining fixed-count phases:
    `checkHead`/`checkTail`/`pushAnswer`/`done` (4) + `drainMem`'s own "+1" (1) + the 11
    `ScratchKind` drains' own "+1"s (11) + `drainReg`'s own sentinel step (1)). Used directly by
    `GenericDispatcher.lean`'s `cleanup_run_of_Mg_bound`, which needs the step bound. -/
lemma cleanup_run_bound (hAgrees : CleanupAgrees p outReg M) (regs : Fin (regBound p) → ℕ)
    (m0 : List MemSym) (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hReg : ∀ i : Fin (regBound p), Sg (Kg.reg i) = natToDigits (regs i)) (hMem : Sg Kg.mem = m0)
    (hCopy : Sg (Kg.scratch .copyScratch) = copyc) (hQuery : Sg (Kg.scratch .query) = queryc)
    (hQueryTmp : Sg (Kg.scratch .queryTmp) = queryTmpc)
    (hLogTmp : Sg (Kg.scratch .logTmp) = logTmpc)
    (hWorkRev : Sg (Kg.scratch .workRev) = workRevc)
    (hLhsOperand : Sg (Kg.scratch .lhsOperand) = lhsOperandc)
    (hRhsOperand : Sg (Kg.scratch .rhsOperand) = rhsOperandc)
    (hSumScratch : Sg (Kg.scratch .sumScratch) = sumScratchc)
    (hDiffScratch : Sg (Kg.scratch .diffScratch) = diffScratchc)
    (hPrologueCounter : Sg (Kg.scratch .prologueCounter) = prologueCounterc)
    (hPrologueWork : Sg (Kg.scratch .prologueWork) = prologueWorkc) :
    ∃ n Sg', (flipBindCleanup p M)^[n]
        (some ⟨some (Λg.cleanup CleanupPhase.checkHead), var, Sg⟩)
      = some ⟨none, AllInstrState.canonical, Sg'⟩ ∧
        (∀ i : Fin (regBound p), Sg' (Kg.reg i) = []) ∧ Sg' Kg.mem = [] ∧
        (∀ sk : ScratchKind, Sg' (Kg.scratch sk) = []) ∧
        Sg' Kg.io = decide (regs outReg = 1) :: Sg Kg.io ∧
        n ≤ (∑ i : Fin (regBound p), (natToDigits (regs i)).length) + regBound p +
          m0.length + copyc.length + queryc.length + queryTmpc.length + logTmpc.length +
          workRevc.length + lhsOperandc.length + rhsOperandc.length + sumScratchc.length +
          diffScratchc.length + prologueCounterc.length + prologueWorkc.length + 17 := by
  obtain ⟨Sg3, h3, hr3, hio3, hk3⟩ := cleanup_run_bound_head hAgrees regs var Sg hReg
  obtain ⟨n4, var4, Sg4, hrun4, hdrained4, hunch4, hbound4⟩ :=
    cleanup_run_bound_regs hAgrees regs _ Sg3 hr3
  have hMem4 : Sg4 Kg.mem = m0 := by
    rw [hunch4 _ (by simp), hk3 _ (by simp) (by simp), hMem]
  have hScratch4 : ∀ sk : ScratchKind, Sg4 (Kg.scratch sk) = Sg (Kg.scratch sk) := fun sk => by
    rw [hunch4 _ (by simp), hk3 _ (by simp) (by simp)]
  obtain ⟨nT, SgF, hT, hFmem, hFsc, hFother, hTb⟩ :=
    cleanup_run_bound_tail hAgrees m0 copyc queryc queryTmpc logTmpc workRevc lhsOperandc
      rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc var4 Sg4 hMem4
      (by rw [hScratch4, hCopy]) (by rw [hScratch4, hQuery]) (by rw [hScratch4, hQueryTmp])
      (by rw [hScratch4, hLogTmp]) (by rw [hScratch4, hWorkRev]) (by rw [hScratch4, hLhsOperand])
      (by rw [hScratch4, hRhsOperand]) (by rw [hScratch4, hSumScratch])
      (by rw [hScratch4, hDiffScratch]) (by rw [hScratch4, hPrologueCounter])
      (by rw [hScratch4, hPrologueWork])
  refine ⟨nT + (n4 + (1 + (1 + 1))), SgF, ?_, ?_, hFmem, hFsc, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, h3, hrun4]
    exact hT
  · intro i
    rw [hFother _ (by simp) (fun sk => by simp)]
    exact hdrained4 i
  · rw [hFother _ (by simp) (fun sk => by simp), hunch4 _ (by simp), hio3]
  · omega

end NPComplete.RAMToTM.Generic

module

public import NPComplete.RAMToTM.Generic.Machine.GenericLoad
public import NPComplete.RAMToTM.Generic.Machine.GenericAdd
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# Emitting `base + i` for `i < length` from the write-log onto a fresh output stream

`answerMachine`'s `Kg.io` is committed end to end to a single decision bit (`GenericCleanup.lean`'s
`checkHead`/`checkTail`/`pushAnswer`), so it cannot serve as a variable-length output channel for
an encoded `List Bool`. Extending the
shared ISA/`Kg p` itself (a new RAM instruction, a `Represents` invariant over unboundedly many
output cells) would force every existing `PhaseOf`/`GenericDispatcher`/`compile_exec` case
analysis to account for output state that the RAM model has never had, rippling through the
existing compiler and machine infrastructure. This file instead keeps `Kg p`/`answerMachine`
untouched and builds a
free-standing loop machine over a strictly larger stack space `EmitK p := Kg p ⊕ {out, countdown}`:
the two genuinely new stacks are a fresh `out : Bool` output stream and a `countdown` stack whose
*length* alone (never its content — its alphabet is `Unit`) drives "how many more addresses remain",
so the loop terminates by popping `countdown` to empty exactly the way every existing scan in this
development terminates by popping a stack to empty (`GenericLoad.copyQuery_loop` et al.), without
needing to decode a runtime length value at all.

`GenericLoad.loadProg` and `GenericAdd.addProg` are proved once over `Kg p` and reused via
`StmtTransport.liftStmt` and `iterate_bind_step_liftStmt` in this output loop. This avoids duplicating their
read and addition phase proofs for the larger output program.

One loop iteration: `checkMore` (pop `countdown`; stop at `done` once it is empty) → `load` (the
embedded `loadProg`, reading `lookupD log addr default` into `rDest`) → `boolify0`/`boolify1`
(mirrors `GenericCleanup`'s own `checkHead`/`checkTail`: `rDest` is assumed to hold exactly `[]` or
`[1]`, i.e. a genuine bit, per the `OutputSlice` cell convention) → `push` (write that bit onto
`out`) → `add` (the embedded `addProg`, `rAddr := rAddr + rOne` — the loop's whole "read `base + i`"
arithmetic, reusing `GenericAdd` rather than a bespoke increment) → back to `checkMore`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym LoadState WriteLog lookupD encodeLog
  natToDigits liftStmt iterate_bind_step_liftStmt iterate_bind_step_liftStmt_getO scanResult AddState)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rAddr rDest rOne : Fin (regBound p))

/-- The emitter's stacks: every stack `Kg p` already has (embedded verbatim via `.base`), plus a
    fresh output stream and a length-only loop counter. `countdown`'s alphabet is `Unit` since
    only its *length* is ever inspected (`emitProg.checkMore`'s `pop`/`branch`), never its
    content. -/
inductive EmitK (p : List Instruction)
  | base : Kg p → EmitK p
  | out : EmitK p
  | countdown : EmitK p
  deriving DecidableEq, Fintype

/-- `EmitK`'s alphabet: `Kg p`'s own per-stack alphabet under `.base`, `Bool` for `out`, `Unit`
    for `countdown`. -/
abbrev EmitΓ (p : List Instruction) : EmitK p → Type
  | .base k => Γg p k
  | .out => Bool
  | .countdown => Unit

instance (k : EmitK p) : Fintype (EmitΓ p k) := by cases k <;> dsimp [EmitΓ] <;> infer_instance
instance (k : EmitK p) : DecidableEq (EmitΓ p k) := by cases k <;> dsimp [EmitΓ] <;> infer_instance

lemma emitK_inj : Function.Injective (EmitK.base (p := p)) :=
  fun _ _ h => by injection h

/-- `EmitΓ p (.base k)` unfolds to exactly `Γg p k`, so the alphabet transport across `.base` is
    the identity `Equiv` — no value re-encoding, matching `GenericLoad.loadCodeBody`'s own
    `eΓ := fun k => Equiv.refl (Γg p k)` (there embedding into a bigger `Λg p` with `Kg p`
    unchanged; here embedding `Kg p` itself into a bigger `EmitK p`). -/
def emitΓEquiv : ∀ k : Kg p, Γg p k ≃ EmitΓ p (EmitK.base k) := fun _ => Equiv.refl _

/-- The emitter's internal state: the embedded `loadProg`'s own `LoadState`, the embedded
    `addProg`'s own `AddState`, the last popped `countdown` marker (`checkMore`'s loop-continue
    flag), and the boolified bit in progress (`boolify0`/`boolify1`/`push`) — one field per
    sub-machine/phase-family, mirroring `AllInstrState`'s "one field per realized instruction"
    convention. -/
structure AllEmitState where
  load : LoadState
  add : AddState
  more : Option Unit
  decision : Bool
  deriving DecidableEq, Fintype

/-- The state every loop iteration starts and ends at, apart from `decision`'s freshly written
    value: no embedded sub-machine is mid-computation between iterations. `load.equal := true`
    (not `false`) matches `GenericLoad.lean`'s "ready to load" convention (`⟨none, none, true⟩`,
    as at each `realize_load` call site), satisfying `emit_run_load_bounded`'s `heq` precondition for a
    fresh sub-machine. -/
def AllEmitState.canonical : AllEmitState :=
  ⟨⟨none, none, true⟩, ⟨none, none, false⟩, none, false⟩

def AllEmitState.getLoad : AllEmitState → LoadState := (·.load)
def AllEmitState.setLoad : AllEmitState → LoadState → AllEmitState := fun s v => { s with load := v }
def AllEmitState.getAdd : AllEmitState → AddState := (·.add)
def AllEmitState.setAdd : AllEmitState → AddState → AllEmitState := fun s v => { s with add := v }

/-- One loop iteration's phases (module docstring spells out the flow); `load`/`add` each wrap a
    whole embedded sub-machine's own phase space rather than adding a case per sub-phase. -/
inductive EmitPhase
  | checkMore
  | load : LoadPhase → EmitPhase
  | boolify0
  | boolify1
  | push
  | add : AddPhase → EmitPhase
  | done
  deriving DecidableEq, Fintype

/-- The loop's `Stmt` tree. `load`/`add`'s own local `done` label is intercepted (matching
    `GenericLoad.loadCodeBody`'s `if l = LoadPhase.done then bridgeTo ... else liftStmt ...`
    pattern) and redirected into the next phase of *this* loop instead of running the embedded
    sub-machine's literal `halt` — the sub-machine's `realize_load`/`realize_add` chains stop one
    step short of that `halt` for exactly this reason. -/
def emitProg : EmitPhase → Turing.TM2.Stmt (EmitΓ p) EmitPhase AllEmitState
  | .checkMore =>
      pop EmitK.countdown (fun s ov => { s with more := ov })
        (branch (fun s => s.more.isSome)
          (goto (fun _ => EmitPhase.load LoadPhase.copyQuery))
          (goto (fun _ => EmitPhase.done)))
  | .load l =>
      if l = LoadPhase.done then
        goto (fun _ => EmitPhase.boolify0)
      else
        liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPhase.load)
          AllEmitState.getLoad AllEmitState.setLoad (loadProg rDest rAddr l)
  | .boolify0 =>
      pop (EmitK.base (Kg.reg rDest))
        (fun s ov => { s with decision := decide (ov = some (1 : Digit)) })
        (goto (fun _ => EmitPhase.boolify1))
  | .boolify1 =>
      pop (EmitK.base (Kg.reg rDest)) (fun s ov => { s with decision := s.decision && decide (ov = none) })
        (goto (fun _ => EmitPhase.push))
  | .push =>
      push EmitK.out (fun s => s.decision)
        (goto (fun _ => EmitPhase.add AddPhase.copyLhs))
  | .add l =>
      if l = AddPhase.done then
        goto (fun _ => EmitPhase.checkMore)
      else
        liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPhase.add)
          AllEmitState.getAdd AllEmitState.setAdd (addProg rAddr rAddr rOne l)
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindEmit : Option (Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) →
    Option (Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) :=
  fun x => x.bind (Turing.TM2.step (emitProg rAddr rDest rOne))

lemma getLoad_setLoad (s : AllEmitState) (v : LoadState) :
    AllEmitState.getLoad (AllEmitState.setLoad s v) = v := rfl
lemma setLoad_setLoad (s : AllEmitState) (v w : LoadState) :
    AllEmitState.setLoad (AllEmitState.setLoad s v) w = AllEmitState.setLoad s w := rfl
lemma setLoad_getLoad (s : AllEmitState) :
    AllEmitState.setLoad s (AllEmitState.getLoad s) = s := by cases s; rfl

lemma getAdd_setAdd (s : AllEmitState) (v : AddState) :
    AllEmitState.getAdd (AllEmitState.setAdd s v) = v := rfl
lemma setAdd_setAdd (s : AllEmitState) (v w : AddState) :
    AllEmitState.setAdd (AllEmitState.setAdd s v) w = AllEmitState.setAdd s w := rfl
lemma setAdd_getAdd (s : AllEmitState) :
    AllEmitState.setAdd s (AllEmitState.getAdd s) = s := by cases s; rfl

/-! ## `checkMore`: the loop-continue test, driven by `countdown`'s length alone -/

lemma flipBindEmit_checkMore_cons (rest : List Unit) (Sg : ∀ k, List (EmitΓ p k))
    (s0 : AllEmitState) (hCd : Sg EmitK.countdown = () :: rest) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some EmitPhase.checkMore, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some (EmitPhase.load LoadPhase.copyQuery), { s0 with more := some () },
          Function.update Sg EmitK.countdown rest⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some EmitPhase.checkMore, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg, hCd]

lemma flipBindEmit_checkMore_nil (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hCd : Sg EmitK.countdown = ([] : List Unit)) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some EmitPhase.checkMore, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.done, { s0 with more := none }, Sg⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some EmitPhase.checkMore, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg, hCd]

/-! ## `boolify0`/`boolify1`/`push`: `GenericCleanup.cleanupProg`'s `checkHead`/`checkTail`/
    `pushAnswer` convention, retargeted at `rDest`/`out` instead of `outReg`/`Kg.io` -/

lemma flipBindEmit_boolify0 (rest : List Digit) (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hDest : Sg (EmitK.base (Kg.reg rDest)) = rest) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some EmitPhase.boolify0, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.boolify1,
          { s0 with decision := decide (rest.head? = some (1 : Digit)) },
          Function.update Sg (EmitK.base (Kg.reg rDest)) rest.tail⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some EmitPhase.boolify0, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg, hDest]

lemma flipBindEmit_boolify1 (rest : List Digit) (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hDest : Sg (EmitK.base (Kg.reg rDest)) = rest) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some EmitPhase.boolify1, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.push,
          { s0 with decision := s0.decision && decide (rest = ([] : List Digit)) },
          Function.update Sg (EmitK.base (Kg.reg rDest)) rest.tail⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some EmitPhase.boolify1, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg, hDest]

lemma flipBindEmit_push (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some EmitPhase.push, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some (EmitPhase.add AddPhase.copyLhs), s0,
          Function.update Sg EmitK.out (s0.decision :: Sg EmitK.out)⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some EmitPhase.push, s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg]

/-! ## `load`: transporting `GenericLoad.realize_load` via `StmtTransport.iterate_bind_step_liftStmt`,
    instead of re-deriving the scan loop against `EmitK p`/`EmitPhase` a second time (module
    docstring). -/

lemma emitProg_load_agrees (l : LoadPhase) (hl : l ≠ LoadPhase.done) :
    emitProg rAddr rDest rOne (EmitPhase.load l) =
      liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPhase.load)
        AllEmitState.getLoad AllEmitState.setLoad (loadProg rDest rAddr l) := by
  simp [emitProg, hl]

/-- Running the embedded `loadProg rDest rAddr` to completion inside the emitter: `rDest` ends up
    holding `scanResult addr log` (`GenericLoad.realize_load`, transported verbatim), every other
    `Kg p`-side stack except `rDest` is untouched, and `out`/`countdown` (the two stacks `Kg p`
    knows nothing about) are untouched too — the "frame" half of `iterate_bind_step_liftStmt`'s conclusion,
    needed since `boolify0`/`checkMore` read exactly those two stacks across this call.  The
    witness step count is bounded, transported unchanged from `realize_load_bounded`. -/
lemma emit_run_load_bounded (addr : ℕ) (log : WriteLog) (Sg0 : ∀ k, List (EmitΓ p k))
    (s0 : AllEmitState)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hMem : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hSc : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hQ : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQt : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLt : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (heq : s0.load.equal = true) :
    ∃ n sf Sgf, (flipBindEmit rAddr rDest rOne)^[n]
        (some (⟨some (EmitPhase.load LoadPhase.copyQuery), s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some (EmitPhase.load LoadPhase.done), sf, Sgf⟩
      ∧ sf = { s0 with load := { memSym := none, queryDigit := none, equal := true } }
      ∧ Sgf (EmitK.base (Kg.reg rDest)) = scanResult addr log
      ∧ (∀ k : Kg p, k ≠ Kg.reg rDest → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ Sgf EmitK.countdown = Sg0 EmitK.countdown
      ∧ n ≤ 32 * ((Sg0 (EmitK.base (Kg.reg rDest))).length + (Sg0 (EmitK.base Kg.mem)).length
          + (natToDigits addr).length + 1) ^ 2 := by
  obtain ⟨n, hrun, hnbound⟩ := realize_load_bounded rDest rAddr addr log
    (fun k => Sg0 (EmitK.base k)) s0.load hAddr hMem hSc hQ hQt hLt heq
  obtain ⟨sf, Sgf, hrunG, hsetf, hstkf, hfrf⟩ :=
    iterate_bind_step_liftStmt EmitK.base emitΓEquiv EmitPhase.load AllEmitState.getLoad AllEmitState.setLoad
      (loadProg rDest rAddr) (emitProg rAddr rDest rOne) emitK_inj getLoad_setLoad setLoad_setLoad
      setLoad_getLoad n LoadPhase.copyQuery s0.load (fun k => Sg0 (EmitK.base k)) s0 Sg0 rfl
      (fun k => by simp [emitΓEquiv, Equiv.coe_refl, List.map_id]) LoadPhase.done
      {memSym := none, queryDigit := none, equal := true}
      (Function.update (fun k => Sg0 (EmitK.base k)) (Kg.reg rDest) (scanResult addr log)) rfl
      (fun l hl => emitProg_load_agrees rAddr rDest rOne l hl) hrun
  refine ⟨n, sf, Sgf, hrunG, hsetf, ?_, ?_, ?_, ?_, hnbound⟩
  · have := hstkf (Kg.reg rDest)
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id] using this
  · intro k hk
    have := hstkf k
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id, Function.update_of_ne hk] using this
  · exact hfrf EmitK.out (fun kl h => by cases h)
  · exact hfrf EmitK.countdown (fun kl h => by cases h)

lemma emitProg_add_agrees (l : AddPhase) (hl : l ≠ AddPhase.done) :
    emitProg rAddr rDest rOne (EmitPhase.add l) =
      liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := EmitPhase.add)
        AllEmitState.getAdd AllEmitState.setAdd (addProg rAddr rAddr rOne l) := by
  simp [emitProg, hl]

/-- The `add`-phase analogue of `emit_run_load_bounded`: running the embedded
    `addProg rAddr rAddr rOne` (self-referential `rd = rs = rAddr`, alias-safe per `GenericAdd`'s
    own docstring) increments `rAddr` by whatever `rOne` holds, leaving every other `Kg p`-side
    stack (in particular `rDest`, freshly drained by the *next* iteration's `loadProg.clearDest`)
    and `out`/`countdown` untouched.  The witness step count is bounded, transported unchanged
    from `realize_add_bounded`. -/
lemma emit_run_add_bounded (addrVal oneVal : ℕ) (Sg0 : ∀ k, List (EmitΓ p k))
    (s0 : AllEmitState)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addrVal)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits oneVal)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (hAddCanon : s0.add = ⟨none, none, false⟩) :
    ∃ n sf Sgf, (flipBindEmit rAddr rDest rOne)^[n]
        (some (⟨some (EmitPhase.add AddPhase.copyLhs), s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some (EmitPhase.add AddPhase.done), sf, Sgf⟩
      ∧ sf = { s0 with add := ⟨none, none, false⟩ }
      ∧ Sgf (EmitK.base (Kg.reg rAddr)) = natToDigits (addrVal + oneVal)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rAddr → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ Sgf EmitK.countdown = Sg0 EmitK.countdown
      ∧ n ≤ 16 * ((natToDigits addrVal).length + (natToDigits addrVal).length
          + (natToDigits oneVal).length + bitLen addrVal + bitLen oneVal + 1) := by
  obtain ⟨n, hrun, hnbound⟩ := realize_add_bounded rAddr rAddr rOne addrVal oneVal
    (fun k => Sg0 (EmitK.base k)) hAddr hOne hWorkRev hCopyScratch hLhsOperand hRhsOperand
    hSumScratch
  rw [hAddr] at hnbound
  obtain ⟨sf, Sgf, hrunG, hsetf, hstkf, hfrf⟩ :=
    iterate_bind_step_liftStmt EmitK.base emitΓEquiv EmitPhase.add AllEmitState.getAdd AllEmitState.setAdd
      (addProg rAddr rAddr rOne) (emitProg rAddr rDest rOne) emitK_inj getAdd_setAdd setAdd_setAdd
      setAdd_getAdd n AddPhase.copyLhs (⟨none, none, false⟩ : AddState) (fun k => Sg0 (EmitK.base k))
      s0 Sg0 hAddCanon
      (fun k => by simp [emitΓEquiv, Equiv.coe_refl, List.map_id]) AddPhase.done
      (⟨none, none, false⟩ : AddState)
      (Function.update (fun k => Sg0 (EmitK.base k)) (Kg.reg rAddr) (natToDigits (addrVal + oneVal)))
      rfl (fun l hl => emitProg_add_agrees rAddr rDest rOne l hl) hrun
  refine ⟨n, sf, Sgf, hrunG, hsetf, ?_, ?_, ?_, ?_, hnbound⟩
  · have := hstkf (Kg.reg rAddr)
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id] using this
  · intro k hk
    have := hstkf k
    simpa [emitΓEquiv, Equiv.coe_refl, List.map_id, Function.update_of_ne hk] using this
  · exact hfrf EmitK.out (fun kl h => by cases h)
  · exact hfrf EmitK.countdown (fun kl h => by cases h)

/-! ## Chaining one iteration: `checkMore` → `load` → `boolify0`/`boolify1`/`push` → `add` →
    `checkMore`, driven by `countdown`'s length alone (module docstring). The two `_done` labels
    are bridges installed by `emitProg` itself (its `if l = ... then goto ... else liftStmt ...`
    branches), not part of the embedded `loadProg`/`addProg` trees, so each needs its own
    one-step lemma before `emit_run_load_bounded`/`emit_run_add_bounded`'s local-machine runs can be chained. -/

lemma flipBindEmit_load_done (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some (EmitPhase.load LoadPhase.done), s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.boolify0, s0, Sg⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some (EmitPhase.load LoadPhase.done), s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg]

lemma flipBindEmit_add_done (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState) :
    flipBindEmit rAddr rDest rOne
        (some (⟨some (EmitPhase.add AddPhase.done), s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.checkMore, s0, Sg⟩ := by
  show (Turing.TM2.step (emitProg rAddr rDest rOne))
      (⟨some (EmitPhase.add AddPhase.done), s0, Sg⟩ :
        Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState) = _
  simp [emitProg]

/-- Splicing two known-length runs: `k1` steps from `x` to `y`, then `k2` more from `y` to `z`,
    is `k2 + k1` steps from `x` to `z` (`Function.iterate_add_apply`'s argument order puts the
    *later*-applied run on the left). The uniform building block every multi-stage run below
    composes with. -/
lemma flipBindEmit_trans {k1 k2 : ℕ}
    {x y z : Option (Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState)}
    (h1 : (flipBindEmit rAddr rDest rOne)^[k1] x = y)
    (h2 : (flipBindEmit rAddr rDest rOne)^[k2] y = z) :
    (flipBindEmit rAddr rDest rOne)^[k2 + k1] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

/-- A bare one-step equation, promoted to `^[1]` so `flipBindEmit_trans` can splice it onto a
    known-length run. -/
lemma flipBindEmit_one {x y : Option (Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState)}
    (h : flipBindEmit rAddr rDest rOne x = y) : (flipBindEmit rAddr rDest rOne)^[1] x = y := by
  rw [Function.iterate_one]; exact h

/-- `boolify0`+`boolify1`+`push` in one packaged 3-step run, specialized to `rDest` holding a
    genuine bit (`[]` or `[1]`, the `OutputSlice` cell convention `emit_run_iteration_bounded` assumes):
    drains `rDest` to `[]` and pushes the corresponding `Bool` onto `out`, landing at the `add`
    call. Packaging these three phases together (rather than chaining their individual step
    lemmas symbolically) sidesteps tracking `rDest`'s two-`Function.update` intermediate content
    across `boolify0`→`boolify1`, since case-splitting on the concrete bit collapses both pops to
    plain list literals. -/
lemma emit_run_boolify_push (bitVal : Bool) (Sg : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hDest : Sg (EmitK.base (Kg.reg rDest)) = if bitVal then [(1 : Digit)] else []) :
    (flipBindEmit rAddr rDest rOne)^[3]
        (some (⟨some EmitPhase.boolify0, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some (EmitPhase.add AddPhase.copyLhs), { s0 with decision := bitVal },
          Function.update (Function.update Sg (EmitK.base (Kg.reg rDest)) ([] : List Digit))
            EmitK.out (bitVal :: Sg EmitK.out)⟩ := by
  show flipBindEmit rAddr rDest rOne
      (flipBindEmit rAddr rDest rOne
        (flipBindEmit rAddr rDest rOne (some (⟨some EmitPhase.boolify0, s0, Sg⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState)))) = _
  cases bitVal with
  | false =>
    simp at hDest
    rw [flipBindEmit_boolify0 rAddr rDest rOne [] Sg s0 hDest]
    rw [flipBindEmit_boolify1 rAddr rDest rOne [] _ _ (by simp)]
    rw [flipBindEmit_push rAddr rDest rOne _ _]
    simp
  | true =>
    simp at hDest
    rw [flipBindEmit_boolify0 rAddr rDest rOne [(1:Digit)] Sg s0 hDest]
    rw [flipBindEmit_boolify1 rAddr rDest rOne [] _ _ (by simp)]
    rw [flipBindEmit_push rAddr rDest rOne _ _]
    simp

/-- One full loop iteration: consumes one `countdown` marker, loads
    `lookupD log addr 0` (assumed a genuine bit, `hBit`) from the write-log at `addr`, pushes it
    onto `out`, and increments `rAddr` by `1` — landing back at `checkMore` with every other
    stack unchanged.  The witness step count is bounded by `emit_run_load_bounded`'s bound, plus
    `emit_run_add_bounded`'s bound (at `addrVal := addr`, `oneVal := 1`), plus the 6
    bridge/packaged steps (`checkMore`'s pop, `load.done`'s return, the 3-step
    `emit_run_boolify_push`, `add.done`'s return). -/
lemma emit_run_iteration_bounded (addr : ℕ) (log : WriteLog) (rest : List Unit)
    (Sg0 : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (hCd : Sg0 EmitK.countdown = () :: rest)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hMem : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hSc : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hQ : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQt : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLt : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (heq : s0.load.equal = true) (hAddCanon : s0.add = ⟨none, none, false⟩)
    (hBit : lookupD log addr 0 = 0 ∨ lookupD log addr 0 = 1) :
    ∃ n sf Sgf, (flipBindEmit rAddr rDest rOne)^[n]
        (some (⟨some EmitPhase.checkMore, s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.checkMore, sf, Sgf⟩
      ∧ Sgf EmitK.countdown = rest
      ∧ Sgf (EmitK.base (Kg.reg rAddr)) = natToDigits (addr + 1)
      ∧ Sgf EmitK.out = decide (lookupD log addr 0 = 1) :: Sg0 EmitK.out
      ∧ sf.load.equal = true ∧ sf.add = ⟨none, none, false⟩
      ∧ Sgf (EmitK.base Kg.mem) = encodeLog log
      ∧ Sgf (EmitK.base (Kg.reg rOne)) = natToDigits 1
      ∧ Sgf (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .query)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym)
      ∧ Sgf (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf (EmitK.base (Kg.reg rDest)) = ([] : List Digit)
      ∧ n ≤ 32 * ((Sg0 (EmitK.base (Kg.reg rDest))).length + (Sg0 (EmitK.base Kg.mem)).length
            + (natToDigits addr).length + 1) ^ 2
          + 16 * ((natToDigits addr).length + (natToDigits addr).length + (natToDigits 1).length
              + bitLen addr + bitLen 1 + 1)
          + 6 := by
  have hbase1 : ∀ k : Kg p, (Function.update Sg0 EmitK.countdown rest) (EmitK.base k) = Sg0 (EmitK.base k) :=
    fun k => Function.update_of_ne (by simp) _ _
  have hA := flipBindEmit_one rAddr rDest rOne (flipBindEmit_checkMore_cons rAddr rDest rOne rest Sg0 s0 hCd)
  have hres1 := emit_run_load_bounded rAddr rDest rOne addr log
      (Function.update Sg0 EmitK.countdown rest)
      { s0 with more := some () } (by rw [hbase1]; exact hAddr) (by rw [hbase1]; exact hMem)
      (by rw [hbase1]; exact hSc) (by rw [hbase1]; exact hQ) (by rw [hbase1]; exact hQt)
      (by rw [hbase1]; exact hLt) heq
  obtain ⟨n1, sf1, Sgf1, hbody1⟩ := hres1
  obtain ⟨hrun1, hsf1, hRDest1, hFrame1, hOut1, hCd1, hn1bound⟩ := hbody1
  simp only [hbase1] at hn1bound
  have hStep2 := flipBindEmit_trans rAddr rDest rOne hA hrun1
  have hStep3 := flipBindEmit_trans rAddr rDest rOne hStep2
    (flipBindEmit_one rAddr rDest rOne (flipBindEmit_load_done rAddr rDest rOne Sgf1 sf1))
  have hbitVal : Sgf1 (EmitK.base (Kg.reg rDest))
      = if decide (lookupD log addr 0 = 1) then [(1 : Digit)] else [] := by
    rcases hBit with h | h
    · rw [hRDest1, scanResult_eq_lookupD, h, natToDigits_zero]; simp
    · rw [hRDest1, scanResult_eq_lookupD, h]
      simp; exact (by decide : natToDigits 1 = [(1 : Digit)])
  have hBP := emit_run_boolify_push rAddr rDest rOne (decide (lookupD log addr 0 = 1)) Sgf1 sf1 hbitVal
  have hStep4 := flipBindEmit_trans rAddr rDest rOne hStep3 hBP
  have hbase2 : ∀ k : Kg p, k ≠ Kg.reg rDest →
      (Function.update (Function.update Sgf1 (EmitK.base (Kg.reg rDest)) ([] : List Digit))
        EmitK.out (decide (lookupD log addr 0 = 1) :: Sgf1 EmitK.out)) (EmitK.base k) = Sgf1 (EmitK.base k) := by
    intro k hk
    rw [Function.update_of_ne (show EmitK.base k ≠ (EmitK.out : EmitK p) by simp),
      Function.update_of_ne (show EmitK.base k ≠ EmitK.base (Kg.reg rDest) from fun h => hk (by injection h))]
  have hres2 := emit_run_add_bounded rAddr rDest rOne addr 1
      (Function.update (Function.update Sgf1 (EmitK.base (Kg.reg rDest)) ([] : List Digit))
        EmitK.out (decide (lookupD log addr 0 = 1) :: Sgf1 EmitK.out))
      { sf1 with decision := decide (lookupD log addr 0 = 1) }
      (by rw [hbase2 (Kg.reg rAddr) (fun h => hDD.symm (by injection h)),
          hFrame1 (Kg.reg rAddr) (fun h => hDD.symm (by injection h)), hbase1]; exact hAddr)
      (by rw [hbase2 (Kg.reg rOne) (fun h => hOD (by injection h)),
          hFrame1 (Kg.reg rOne) (fun h => hOD (by injection h)), hbase1]; exact hOne)
      (by rw [hbase2 (Kg.scratch .workRev) (by simp), hFrame1 (Kg.scratch .workRev) (by simp)]; rw [hbase1]; exact hWorkRev)
      (by rw [hbase2 (Kg.scratch .copyScratch) (by simp), hFrame1 (Kg.scratch .copyScratch) (by simp)]; rw [hbase1]; exact hSc)
      (by rw [hbase2 (Kg.scratch .lhsOperand) (by simp), hFrame1 (Kg.scratch .lhsOperand) (by simp)]; rw [hbase1]; exact hLhsOperand)
      (by rw [hbase2 (Kg.scratch .rhsOperand) (by simp), hFrame1 (Kg.scratch .rhsOperand) (by simp)]; rw [hbase1]; exact hRhsOperand)
      (by rw [hbase2 (Kg.scratch .sumScratch) (by simp), hFrame1 (Kg.scratch .sumScratch) (by simp)]; rw [hbase1]; exact hSumScratch)
      (by rw [hsf1]; exact hAddCanon)
  obtain ⟨n2, sf2, Sgf2, hbody2⟩ := hres2
  obtain ⟨hrun2, hsf2, hRAddr2, hFrame2, hOut2, hCd2, hn2bound⟩ := hbody2
  have hStep5 := flipBindEmit_trans rAddr rDest rOne hStep4 hrun2
  have hStep6 := flipBindEmit_trans rAddr rDest rOne hStep5
    (flipBindEmit_one rAddr rDest rOne (flipBindEmit_add_done rAddr rDest rOne Sgf2 sf2))
  have hchain : ∀ k : Kg p, k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest → Sgf2 (EmitK.base k) = Sg0 (EmitK.base k) := by
    intro k hkA hkD
    rw [hFrame2 k hkA, hbase2 k hkD, hFrame1 k hkD, hbase1]
  have hCdChain : Sgf2 EmitK.countdown = rest := by
    rw [hCd2, Function.update_of_ne (by simp), Function.update_of_ne (by simp), hCd1,
      Function.update_self]
  have hOutChain : Sgf2 EmitK.out = decide (lookupD log addr 0 = 1) :: Sg0 EmitK.out := by
    rw [hOut2, Function.update_self, hOut1, Function.update_of_ne (by simp)]
  have hRDest2 : Sgf2 (EmitK.base (Kg.reg rDest)) = ([] : List Digit) := by
    rw [hFrame2 (Kg.reg rDest) (fun h => hDD (by injection h)),
      Function.update_of_ne (show EmitK.base (Kg.reg rDest) ≠ (EmitK.out : EmitK p) by simp),
      Function.update_self]
  refine ⟨_, sf2, Sgf2, hStep6, hCdChain, hRAddr2, hOutChain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hRDest2, by omega⟩
  · rw [hsf2, hsf1]
  · rw [hsf2]
  · exact (hchain Kg.mem (by simp) (by simp)).trans hMem
  · exact (hchain (Kg.reg rOne) (fun h => hOA (by injection h)) (fun h => hOD (by injection h))).trans hOne
  · exact (hchain (Kg.scratch .copyScratch) (by simp) (by simp)).trans hSc
  · exact (hchain (Kg.scratch .query) (by simp) (by simp)).trans hQ
  · exact (hchain (Kg.scratch .queryTmp) (by simp) (by simp)).trans hQt
  · exact (hchain (Kg.scratch .logTmp) (by simp) (by simp)).trans hLt
  · exact (hchain (Kg.scratch .workRev) (by simp) (by simp)).trans hWorkRev
  · exact (hchain (Kg.scratch .lhsOperand) (by simp) (by simp)).trans hLhsOperand
  · exact (hchain (Kg.scratch .rhsOperand) (by simp) (by simp)).trans hRhsOperand
  · exact (hchain (Kg.scratch .sumScratch) (by simp) (by simp)).trans hSumScratch
  · exact hchain

/-- The full sequence of bits `emit_run_length_bounded` writes to `out`, in the order the loop
    reads them (`addr`, `addr+1`, ...) — reversed by `emit_run_length_bounded` itself to match
    `push`'s prepend semantics, exactly like `emit_run_iteration_bounded`'s single-bit `push`. -/
def bitsFor (log : WriteLog) : ℕ → List Unit → List Bool
  | _, [] => []
  | addr, () :: rest => decide (lookupD log addr 0 = 1) :: bitsFor log (addr + 1) rest

/-- Closing the whole loop by induction on `rest0`'s length: repeat `emit_run_iteration_bounded` once
    per remaining `countdown` marker until it empties, landing at `done`, with a polynomial bound
    on the witness step count. `addr` only ever *grows* across the loop (unlike `prep`'s shrinking
    `rLen`), so `natToDigits_length_mono`/`bitLen_le_of_le` bound every iteration's cost by the
    *final* address `addr + rest0.length` instead of the initial one. -/
lemma emit_run_length_bounded (addr : ℕ) (log : WriteLog) (rest0 : List Unit)
    (Sg0 : ∀ k, List (EmitΓ p k)) (s0 : AllEmitState)
    (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (hCd : Sg0 EmitK.countdown = rest0)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hMem : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hSc : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hQ : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQt : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLt : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (hDest0 : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (heq : s0.load.equal = true) (hAddCanon : s0.add = ⟨none, none, false⟩)
    (hBit : ∀ i < rest0.length, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1) :
    ∃ n sf Sgf, (flipBindEmit rAddr rDest rOne)^[n]
        (some (⟨some EmitPhase.checkMore, s0, Sg0⟩ :
          Turing.TM2.Cfg (EmitΓ p) EmitPhase AllEmitState))
      = some ⟨some EmitPhase.done, sf, Sgf⟩
      ∧ Sgf EmitK.out = (bitsFor log addr rest0).reverse ++ Sg0 EmitK.out
      ∧ Sgf (EmitK.base (Kg.reg rAddr)) = natToDigits (addr + rest0.length)
      ∧ Sgf (EmitK.base Kg.mem) = encodeLog log
      ∧ Sgf (EmitK.base (Kg.reg rOne)) = natToDigits 1
      ∧ Sgf (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .query)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym)
      ∧ Sgf (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf (EmitK.base (Kg.reg rDest)) = ([] : List Digit)
      ∧ Sgf EmitK.countdown = ([] : List Unit)
      ∧ n ≤ rest0.length *
          (32 * ((encodeLog log).length + (natToDigits (addr + rest0.length)).length + 1) ^ 2
            + 16 * (2 * (natToDigits (addr + rest0.length)).length + (natToDigits 1).length
                + bitLen (addr + rest0.length) + bitLen 1 + 1)
            + 6) + 1 := by
  induction rest0 generalizing addr Sg0 s0 with
  | nil =>
    refine ⟨1, { s0 with more := none }, Sg0, ?_, ?_, ?_, hMem, hOne, hSc, hQ, hQt, hLt, hWorkRev,
      hLhsOperand, hRhsOperand, hSumScratch, fun _ _ _ => rfl, hDest0, hCd, by omega⟩
    · exact flipBindEmit_one rAddr rDest rOne (flipBindEmit_checkMore_nil rAddr rDest rOne Sg0 s0 hCd)
    · simp [bitsFor]
    · simpa using hAddr
  | cons hd rest' ih =>
    have hBit0 : lookupD log addr 0 = 0 ∨ lookupD log addr 0 = 1 := by
      have h := hBit 0 (by simp)
      simpa using h
    obtain ⟨n1, sf1, Sgf1, hbody1⟩ :=
      emit_run_iteration_bounded rAddr rDest rOne addr log rest' Sg0 s0 hDD hOA hOD hCd hAddr hMem
        hOne hSc hQ hQt hLt hWorkRev hLhsOperand hRhsOperand hSumScratch heq hAddCanon hBit0
    obtain ⟨hrun1, hCd1, hRAddr1, hOut1, hEq1, hAddCanon1, hMem1, hOne1, hSc1, hQ1, hQt1, hLt1,
      hWorkRev1, hLhsOperand1, hRhsOperand1, hSumScratch1, hFrame1, hDest1, hn1bound⟩ := hbody1
    simp only [hDest0, hMem, List.length_nil, zero_add] at hn1bound
    have hBit' : ∀ i < rest'.length, lookupD log (addr + 1 + i) 0 = 0 ∨
        lookupD log (addr + 1 + i) 0 = 1 := by
      intro i hi
      have h := hBit (i + 1) (by simp; omega)
      have hidx : addr + 1 + i = addr + (i + 1) := by omega
      rwa [hidx]
    obtain ⟨n2, sf2, Sgf2, hbody2⟩ :=
      ih (addr + 1) Sgf1 sf1 hCd1 hRAddr1 hMem1 hOne1 hSc1 hQ1 hQt1 hLt1 hWorkRev1 hLhsOperand1
        hRhsOperand1 hSumScratch1 hDest1 hEq1 hAddCanon1 hBit'
    obtain ⟨hrun2, hOut2, hRAddr2, hMem2, hOne2, hSc2, hQ2, hQt2, hLt2, hWorkRev2, hLhsOperand2,
      hRhsOperand2, hSumScratch2, hFrame2, hDest2, hCdF2, hn2bound⟩ := hbody2
    have hlen : (hd :: rest').length = rest'.length + 1 := List.length_cons
    have hAeq : addr + 1 + rest'.length = addr + (hd :: rest').length := by omega
    rw [hAeq] at hn2bound
    have hLmono : (natToDigits addr).length ≤ (natToDigits (addr + (hd :: rest').length)).length :=
      natToDigits_length_mono (Nat.le_add_right addr _)
    have hBmono : bitLen addr ≤ bitLen (addr + (hd :: rest').length) :=
      bitLen_le_of_le (Nat.le_add_right addr _)
    have hSqLe : ((encodeLog log).length + (natToDigits addr).length + 1) ^ 2 ≤
        ((encodeLog log).length + (natToDigits (addr + (hd :: rest').length)).length + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hBsum : 2 * (natToDigits addr).length + (natToDigits 1).length + bitLen addr + bitLen 1
        + 1 ≤ 2 * (natToDigits (addr + (hd :: rest').length)).length + (natToDigits 1).length
          + bitLen (addr + (hd :: rest').length) + bitLen 1 + 1 := by omega
    have hCiter : (32 * ((encodeLog log).length + (natToDigits addr).length + 1) ^ 2
          + 16 * (2 * (natToDigits addr).length + (natToDigits 1).length + bitLen addr + bitLen 1
              + 1) + 6) ≤
        (32 * ((encodeLog log).length + (natToDigits (addr + (hd :: rest').length)).length + 1) ^ 2
          + 16 * (2 * (natToDigits (addr + (hd :: rest').length)).length + (natToDigits 1).length
              + bitLen (addr + (hd :: rest').length) + bitLen 1 + 1) + 6) := by omega
    have hdist : (hd :: rest').length *
        (32 * ((encodeLog log).length + (natToDigits (addr + (hd :: rest').length)).length + 1) ^ 2
          + 16 * (2 * (natToDigits (addr + (hd :: rest').length)).length + (natToDigits 1).length
              + bitLen (addr + (hd :: rest').length) + bitLen 1 + 1) + 6) =
        rest'.length *
          (32 * ((encodeLog log).length
              + (natToDigits (addr + (hd :: rest').length)).length + 1) ^ 2
            + 16 * (2 * (natToDigits (addr + (hd :: rest').length)).length + (natToDigits 1).length
                + bitLen (addr + (hd :: rest').length) + bitLen 1 + 1) + 6)
          + (32 * ((encodeLog log).length + (natToDigits (addr + (hd :: rest').length)).length
              + 1) ^ 2
            + 16 * (2 * (natToDigits (addr + (hd :: rest').length)).length + (natToDigits 1).length
                + bitLen (addr + (hd :: rest').length) + bitLen 1 + 1) + 6) := by
      rw [hlen]; ring
    refine ⟨n2 + n1, sf2, Sgf2, flipBindEmit_trans rAddr rDest rOne hrun1 hrun2, ?_, ?_, hMem2,
      hOne2, hSc2, hQ2, hQt2, hLt2, hWorkRev2, hLhsOperand2, hRhsOperand2, hSumScratch2,
      fun k hkA hkD => (hFrame2 k hkA hkD).trans (hFrame1 k hkA hkD), hDest2, hCdF2, by omega⟩
    · rw [hOut2, hOut1]; simp [bitsFor, List.reverse_cons, List.append_assoc]
    · rw [hRAddr2]; congr 1

end NPComplete.RAMToTM.Generic

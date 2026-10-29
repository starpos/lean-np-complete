module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmit
public import NPComplete.RAMToTM.Generic.Machine.GenericEmitPrep
public import NPComplete.RAMToTM.Generic.Machine.GenericEmitCleanup

/-!
# The master label/state type unifying RAM simulation, prep, emit, cleanup

`GenericEmit.emitProg`/`GenericEmitPrep.prepProg`/`GenericEmitCleanup.emitCleanupProg` each run
against the *same* stack alphabet `EmitK p`/`EmitΓ p` but three mutually distinct label/state
pairs (`EmitPhase`/`AllEmitState`, `EmitPrepPhase`/`PrepState`, `EmitCleanupPhase p`/
`CleanupState`) — and the RAM simulation itself (`GenericProgramMachine.Λg p`/`AllInstrState`)
is a fourth, running on the *smaller* alphabet `Kg p`/`Γg p` embedded into `EmitK p`/`EmitΓ p` via
`.base` (exactly `GenericEmit.lean`'s own `emitΓEquiv`/`emitK_inj`). `MasterΛ`/`MasterState`
package all four into one label/state pair a single `Turing.TM2.Stmt` can be built over. The
machine that chains prologue → RAM → prep → emit → cleanup is assembled by installing, at each
local machine's labels, a lifted copy of its already-proved `Stmt` tree.

`liftLocalStmt` specializes `StmtTransport.liftStmt` to the case every one of prep/emit/cleanup
needs: `K`/`Γ` unchanged (`ιK := id`, `eΓ k := Equiv.refl (EmitΓ p k)`), only `Λ`/`σ` embedded —
the RAM component alone needs the *other* shape of `liftStmt` call (`ιK := EmitK.base`), since it
is the one local machine whose own `K := Kg p` is strictly smaller than the shared `EmitK p`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction}

/-- The master label type: one variant per local machine this construction unifies, each embedding that
    machine's own label type unchanged. -/
inductive MasterΛ (p : List Instruction)
  | ram : Λg p → MasterΛ p
  | prep : EmitPrepPhase → MasterΛ p
  | emit : EmitPhase → MasterΛ p
  | cleanup : EmitCleanupPhase p → MasterΛ p
  deriving DecidableEq, Fintype

/-- The master state: the product of every local machine's own state, one field per machine
    (mirrors `AllInstrState`'s own "one field per realized instruction" convention, now one level
    up — one field per local machine). -/
structure MasterState (p : List Instruction) where
  ram : AllInstrState
  prep : PrepState
  emit : AllEmitState
  cleanup : CleanupState
  deriving DecidableEq, Fintype

/-- The state every local machine starts with before its own turn: every field canonical. -/
def MasterState.canonical : MasterState p :=
  ⟨AllInstrState.canonical, PrepState.canonical, AllEmitState.canonical, ⟨false⟩⟩

/-! ## Per-component lenses, one per field, each satisfying the three standard lens laws
    (`StmtTransport.liftStmt`'s `get`/`set` requirement). -/

def MasterState.getRam : MasterState p → AllInstrState := (·.ram)
def MasterState.setRam : MasterState p → AllInstrState → MasterState p := fun s v => { s with ram := v }
lemma getRam_setRam (s : MasterState p) (v : AllInstrState) :
    MasterState.getRam (MasterState.setRam s v) = v := rfl
lemma setRam_setRam (s : MasterState p) (v w : AllInstrState) :
    MasterState.setRam (MasterState.setRam s v) w = MasterState.setRam s w := rfl
lemma setRam_getRam (s : MasterState p) : MasterState.setRam s (MasterState.getRam s) = s := by
  cases s; rfl

def MasterState.getPrep : MasterState p → PrepState := (·.prep)
def MasterState.setPrep : MasterState p → PrepState → MasterState p := fun s v => { s with prep := v }
lemma getPrep_setPrep (s : MasterState p) (v : PrepState) :
    MasterState.getPrep (MasterState.setPrep s v) = v := rfl
lemma setPrep_setPrep (s : MasterState p) (v w : PrepState) :
    MasterState.setPrep (MasterState.setPrep s v) w = MasterState.setPrep s w := rfl
lemma setPrep_getPrep (s : MasterState p) : MasterState.setPrep s (MasterState.getPrep s) = s := by
  cases s; rfl

def MasterState.getEmit : MasterState p → AllEmitState := (·.emit)
def MasterState.setEmit : MasterState p → AllEmitState → MasterState p := fun s v => { s with emit := v }
lemma getEmit_setEmit (s : MasterState p) (v : AllEmitState) :
    MasterState.getEmit (MasterState.setEmit s v) = v := rfl
lemma setEmit_setEmit (s : MasterState p) (v w : AllEmitState) :
    MasterState.setEmit (MasterState.setEmit s v) w = MasterState.setEmit s w := rfl
lemma setEmit_getEmit (s : MasterState p) : MasterState.setEmit s (MasterState.getEmit s) = s := by
  cases s; rfl

def MasterState.getCleanup : MasterState p → CleanupState := (·.cleanup)
def MasterState.setCleanup : MasterState p → CleanupState → MasterState p :=
  fun s v => { s with cleanup := v }
lemma getCleanup_setCleanup (s : MasterState p) (v : CleanupState) :
    MasterState.getCleanup (MasterState.setCleanup s v) = v := rfl
lemma setCleanup_setCleanup (s : MasterState p) (v w : CleanupState) :
    MasterState.setCleanup (MasterState.setCleanup s v) w = MasterState.setCleanup s w := rfl
lemma setCleanup_getCleanup (s : MasterState p) :
    MasterState.setCleanup s (MasterState.getCleanup s) = s := by cases s; rfl

/-- The identity-`K` embedding every one of prep/emit/cleanup needs (`K`/`Γ` already
    `EmitK p`/`EmitΓ p`, only the label/state change). Named and `@[reducible]` rather than
    passing bare `id`/`Equiv.refl` at each call site: `StmtTransport.iterate_bind_step_liftStmt`'s own
    embedding-condition hypothesis (`Sg₀ (ιK k) = (Sl₀ k).map (eΓ k)`) type-checks `eΓ k` against
    `Γl k ≃ Γg (ιK k)` at the stricter `instances` transparency, which does not reduce a bare
    `id k` to `k` — a genuine (if surprising) `iterate_bind_step_liftStmt` gotcha `liftLocalStmt` itself
    (a `Stmt`-only construction, checked at ordinary transparency) never hits. -/
@[reducible] def emitKId : EmitK p → EmitK p := id

/-- `emitKId`'s trivial alphabet equivalence, `iterate_bind_step_liftStmt`'s `eΓ` argument. -/
def emitKIdEquiv : ∀ k : EmitK p, EmitΓ p k ≃ EmitΓ p (emitKId k) := fun _ => Equiv.refl _

/-- `StmtTransport.liftStmt` specialized to the identity-`K` case every one of prep/emit/cleanup
    needs: `K`/`Γ` unchanged (already `EmitK p`/`EmitΓ p`), only the label (`ιΛ`) and state
    (`get`/`set`) embed. -/
def liftLocalStmt {Λl σl : Type} (ιΛ : Λl → MasterΛ p) (get : MasterState p → σl)
    (set : MasterState p → σl → MasterState p) :
    Turing.TM2.Stmt (EmitΓ p) Λl σl → Turing.TM2.Stmt (EmitΓ p) (MasterΛ p) (MasterState p) :=
  liftStmt (ιK := emitKId) (eΓ := emitKIdEquiv) ιΛ get set

end NPComplete.RAMToTM.Generic

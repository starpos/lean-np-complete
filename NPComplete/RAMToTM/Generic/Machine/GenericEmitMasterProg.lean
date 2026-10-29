module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmitMaster
public import NPComplete.RAMToTM.Generic.Machine.GenericDispatcher

/-!
# Wiring the master dispatcher: RAM → prep → emit → cleanup

`GenericEmitMaster.lean` built the label/state pair `MasterΛ`/`MasterState`; this file
installs the actual `Turing.TM2.Stmt` at every label. Three of the four components
(`prep`/`emit`/`cleanup`) simply lift their own already-proved `Stmt` tree via `liftLocalStmt`,
unchanged. The RAM component almost does the same (`liftStmt (ιK := EmitK.base) (eΓ :=
emitΓEquiv) ...` over `Mg`, exactly as `GenericEmit.lean`'s own `emit_run_load_bounded`/`emit_run_add_bounded`
already transport `GenericLoad`/`GenericAdd`) — except at exactly one label,
`Λg.cleanup CleanupPhase.checkHead`, the single point `GenericProgramMachine.entryAt`/`bridgeTo`
route every "RAM instruction stream exhausted" transition to (`entryAt`'s docstring). There,
instead of lifting `Mg`'s own `cleanupProg` (the single-bit-decision cleanup that the multi-bit
output replaces), the master dispatcher installs a `goto` into `prep`'s entry — `entryAt`/`Mg`/`bridgeTo`
themselves are untouched, so every existing RAM-simulation proof (`Represents`,
`instrStepSim_of_programSupported`, the prologue) keeps working unmodified against `Mg` as a
free-standing fact; only the *master* dispatcher's own `.ram (Λg.cleanup CleanupPhase.checkHead)`
case differs from a plain lift of it. `ramStop` is the plain-`Λg p`-level (pre-lift) form of that
same substitution — installing `halt` instead of the redirect — kept separate for the RAM-prefix
theorem that the run reaches exactly this point, which has no use for `prep`/`emit`/`cleanup`.

Each of the two *other* boundary transitions this file also has to wire by hand (not a plain
`liftStmt`/`liftLocalStmt` lift) is a `prep`/`emit`'s own `done` label, exactly like
`GenericEmit.emitProg`'s `load`/`add` sub-machines already intercept their own `done` and bridge
elsewhere (the docstring of `emitProg` in `GenericEmit.lean`: "`load`/`add`'s own local `done`
label is intercepted") — `prep`'s `done` bridges into `emit.checkMore`, `emit`'s `done`
bridges into `cleanup.drainReg 0`, both resetting the next local machine's state to canonical
first (mirroring `bridgeTo`'s own `load (fun _ => AllInstrState.canonical)` convention).
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (hSup : ProgramSupported p)
  (outReg rAddr rDest rOne rLen : Fin (regBound p))

/-- The plain-`Λg p`-level substitution needed by the RAM-prefix theorem: `Mg`, except `Λg.cleanup
    CleanupPhase.checkHead` (`entryAt`'s sole "RAM instruction stream exhausted" target) is an
    immediate `halt` instead of running `cleanupProg`. Lets a "the RAM run reaches exactly this
    point" theorem be stated without needing to know what happens beyond it. -/
def ramStop : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l => if l = Λg.cleanup CleanupPhase.checkHead then halt else Mg p hSup outReg l

/-- `ramStop` away from the one substituted label is exactly `Mg` — the fact that the RAM-only
    reasoning (`instrStepSim_of_programSupported` et al., all stated against `Mg`) transports
    across for as long as the run has not yet reached `checkHead`. -/
lemma ramStop_agrees (l : Λg p) (hl : l ≠ Λg.cleanup CleanupPhase.checkHead) :
    ramStop hSup outReg l = Mg p hSup outReg l := by
  simp [ramStop, hl]

/-- The master dispatcher: `ram`/`prep`/`emit`/`cleanup` each lift their own already-proved
    `Stmt` tree, except at the three boundary labels (module docstring) where a `goto` into the
    next local machine (with its local state reset to canonical) is installed by hand. -/
def masterProg : MasterΛ p → Turing.TM2.Stmt (EmitΓ p) (MasterΛ p) (MasterState p)
  | .ram l =>
      if l = Λg.cleanup CleanupPhase.checkHead then
        load (fun s => MasterState.setPrep s PrepState.canonical)
          (goto (fun _ => MasterΛ.prep EmitPrepPhase.checkLen))
      else
        liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := MasterΛ.ram)
          MasterState.getRam MasterState.setRam (Mg p hSup outReg l)
  | .prep l =>
      if l = EmitPrepPhase.done then
        load (fun s => MasterState.setEmit s AllEmitState.canonical)
          (goto (fun _ => MasterΛ.emit EmitPhase.checkMore))
      else
        liftLocalStmt MasterΛ.prep MasterState.getPrep MasterState.setPrep (prepProg rLen rOne l)
  | .emit l =>
      if l = EmitPhase.done then
        load (fun s => MasterState.setCleanup s ⟨false⟩)
          (goto (fun _ => MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)))
      else
        liftLocalStmt MasterΛ.emit MasterState.getEmit MasterState.setEmit
          (emitProg rAddr rDest rOne l)
  | .cleanup l =>
      if l = EmitCleanupPhase.done then
        load (fun _ => MasterState.canonical) halt
      else
        liftLocalStmt MasterΛ.cleanup MasterState.getCleanup MasterState.setCleanup
          (emitCleanupProg l)

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def master_flipBind : Option (Turing.TM2.Cfg (EmitΓ p) (MasterΛ p) (MasterState p)) →
    Option (Turing.TM2.Cfg (EmitΓ p) (MasterΛ p) (MasterState p)) :=
  fun x => x.bind (Turing.TM2.step (masterProg hSup outReg rAddr rDest rOne rLen))

/-! ## `.ram`: lifting `Mg` verbatim away from the one redirected label -/

lemma masterProg_ram_agrees (l : Λg p) (hl : l ≠ Λg.cleanup CleanupPhase.checkHead) :
    masterProg hSup outReg rAddr rDest rOne rLen (MasterΛ.ram l) =
      liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := MasterΛ.ram)
        MasterState.getRam MasterState.setRam (Mg p hSup outReg l) := by
  simp [masterProg, hl]

lemma master_flipBind_ram_checkHead (var : MasterState p) (Sg : ∀ k, List (EmitΓ p k)) :
    master_flipBind hSup outReg rAddr rDest rOne rLen
        (some ⟨some (MasterΛ.ram (Λg.cleanup CleanupPhase.checkHead)), var, Sg⟩)
      = some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen),
          MasterState.setPrep var PrepState.canonical, Sg⟩ := by
  show (Turing.TM2.step (masterProg hSup outReg rAddr rDest rOne rLen))
      ⟨some (MasterΛ.ram (Λg.cleanup CleanupPhase.checkHead)), var, Sg⟩ = _
  simp [masterProg]

/-! ## `.prep`: lifting `prepProg` verbatim away from its own `done` -/

lemma masterProg_prep_agrees (l : EmitPrepPhase) (hl : l ≠ EmitPrepPhase.done) :
    masterProg hSup outReg rAddr rDest rOne rLen (MasterΛ.prep l) =
      liftLocalStmt MasterΛ.prep MasterState.getPrep MasterState.setPrep (prepProg rLen rOne l) := by
  simp [masterProg, hl]

lemma master_flipBind_prep_done (var : MasterState p) (Sg : ∀ k, List (EmitΓ p k)) :
    master_flipBind hSup outReg rAddr rDest rOne rLen
        (some ⟨some (MasterΛ.prep EmitPrepPhase.done), var, Sg⟩)
      = some ⟨some (MasterΛ.emit EmitPhase.checkMore),
          MasterState.setEmit var AllEmitState.canonical, Sg⟩ := by
  show (Turing.TM2.step (masterProg hSup outReg rAddr rDest rOne rLen))
      ⟨some (MasterΛ.prep EmitPrepPhase.done), var, Sg⟩ = _
  simp [masterProg]

/-! ## `.emit`: lifting `emitProg` verbatim away from its own `done` -/

lemma masterProg_emit_agrees (l : EmitPhase) (hl : l ≠ EmitPhase.done) :
    masterProg hSup outReg rAddr rDest rOne rLen (MasterΛ.emit l) =
      liftLocalStmt MasterΛ.emit MasterState.getEmit MasterState.setEmit
        (emitProg rAddr rDest rOne l) := by
  simp [masterProg, hl]

lemma master_flipBind_emit_done (var : MasterState p) (Sg : ∀ k, List (EmitΓ p k)) :
    master_flipBind hSup outReg rAddr rDest rOne rLen
        (some ⟨some (MasterΛ.emit EmitPhase.done), var, Sg⟩)
      = some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)),
          MasterState.setCleanup var ⟨false⟩, Sg⟩ := by
  show (Turing.TM2.step (masterProg hSup outReg rAddr rDest rOne rLen))
      ⟨some (MasterΛ.emit EmitPhase.done), var, Sg⟩ = _
  simp [masterProg]

/-! ## `.cleanup`: lifting `emitCleanupProg` verbatim throughout (no boundary override — its own
    `.done` is already a genuine `halt`). -/

lemma masterProg_cleanup_agrees (l : EmitCleanupPhase p) (hl : l ≠ EmitCleanupPhase.done) :
    masterProg hSup outReg rAddr rDest rOne rLen (MasterΛ.cleanup l) =
      liftLocalStmt MasterΛ.cleanup MasterState.getCleanup MasterState.setCleanup
        (emitCleanupProg l) := by
  simp [masterProg, hl]

end NPComplete.RAMToTM.Generic

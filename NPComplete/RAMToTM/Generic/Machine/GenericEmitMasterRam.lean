module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmitMasterProg

/-!
# RAM prefix transport: the RAM run reaches `Λg.cleanup CleanupPhase.checkHead`

`GenericDispatcher.answer_run_full_bound_of_boundedWhileDecider` gets a `Mg`-driven RAM run within
two more `outputLoad_exec_cost` steps of `Λg.cleanup CleanupPhase.checkHead` (its own main-run/
`outputLoad_exec_cost`/`ControlRep` composition, via `boundedRunSimWithGrowth_of_programSupported`).
Transporting that run into `master_flipBind`'s space via `StmtTransport.iterate_bind_step_liftStmt` needs
the *local* dispatcher to have a genuine `halt` at the label it stops at — but `Mg`'s own
`Λg.cleanup CleanupPhase.checkHead` case is `cleanupProg`'s real pop-based logic, not `halt`
(`answer_run_full_bound_of_boundedWhileDecider` keeps stepping through it for exactly this reason,
reaching the single-bit decision path's cleanup that the multi-bit composition bypasses).
`GenericEmitMasterProg.ramStop` agrees with `Mg` except at that label, where it is `halt` literally
— but swapping `Mg` for `ramStop` over a run is only sound if that run never *visits*
`Λg.cleanup CleanupPhase.checkHead` before its very last step (otherwise the two dispatchers'
behavior has already diverged there).

`Represents`/`ControlRep`/`BoundedRunSim` don't rule this out on their own (they only witness
individual checkpoints, not every intermediate label pointwise) — but the fact is true for a
reason independent of RAM semantics entirely: inspecting `GenericCleanup.cleanupProg`'s `Stmt`
tree shows `Λg.cleanup CleanupPhase.checkHead` is a *source-only* label — no `goto` anywhere in
`checkTail`/`pushAnswer`/`drainReg`/`drainMem`/`drainScratch`/`done`'s own trees ever targets it
again, regardless of which branch a `pop`/`branch` step takes, and no phase's `goto` ever leaves
the `.cleanup` namespace either. `mg_cleanup_step_classify` makes that precise (one step,
case-split on every non-`checkHead` phase, landing either at `none` or at another
non-`checkHead` cleanup phase); `mg_cleanup_ne_checkHead_iterate` lifts it to "any number of
`Mg`-steps from a non-`checkHead` cleanup phase never lands on `checkHead`" (induction on step
count, using `StmtTransport.iterate_bind_step_stuck_at_none` once the run has collapsed to `none`);
`ramStop_iterate_eq_of_mg_landing` is the main composition needed by the dispatcher-swap theorem.
It closes the loop by contradiction against `mg_cleanup_ne_checkHead_iterate` whenever a
one-step-early landing on `checkHead` would force a second visit.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (iterate_bind_step_stuck_at_none)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (hSup : ProgramSupported p) (outReg : Fin (regBound p))

/-- One `Mg`-step from any cleanup phase other than `checkHead` lands either at `none` (only from
    `done`, `cleanupProg`'s own `halt`) or at another cleanup phase different from `checkHead`. -/
lemma mg_cleanup_step_classify (ph : CleanupPhase p) (hph : ph ≠ CleanupPhase.checkHead)
    (v : AllInstrState) (S : ∀ k, List (Γg p k)) :
    (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S).l = none ∨
    ∃ ph', ph' ≠ CleanupPhase.checkHead ∧
      (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S).l = some (Λg.cleanup ph') := by
  cases ph with
  | checkHead => exact absurd rfl hph
  | checkTail =>
    right
    refine ⟨CleanupPhase.pushAnswer, by simp, ?_⟩
    simp [Mg, cleanupProg, Turing.TM2.stepAux]
  | pushAnswer =>
    right
    refine ⟨CleanupPhase.drainReg ⟨0, by omega⟩, by simp, ?_⟩
    simp [Mg, cleanupProg, Turing.TM2.stepAux]
  | done => left; simp [Mg, cleanupProg, Turing.TM2.stepAux]
  | drainReg cursor =>
    right
    simp only [Mg, cleanupProg]
    split_ifs with h
    · simp only [Turing.TM2.stepAux]
      cases (S (Kg.reg ⟨cursor, h⟩)).head?.isSome
      · exact ⟨CleanupPhase.drainReg ⟨cursor + 1, by omega⟩, by simp, by simp⟩
      · exact ⟨CleanupPhase.drainReg cursor, by simp, by simp⟩
    · exact ⟨CleanupPhase.drainMem, by simp, by simp [Turing.TM2.stepAux]⟩
  | drainMem =>
    right
    simp only [Mg, cleanupProg, Turing.TM2.stepAux]
    cases (S Kg.mem).head?.isSome
    · exact ⟨CleanupPhase.drainScratch ScratchKind.copyScratch, by simp, by simp⟩
    · exact ⟨CleanupPhase.drainMem, by simp, by simp⟩
  | drainScratch sk =>
    right
    simp only [Mg, cleanupProg, Turing.TM2.stepAux]
    cases (S (Kg.scratch sk)).head?.isSome
    · cases hnext : nextScratchKind sk with
      | none => exact ⟨CleanupPhase.done, by simp, by simp⟩
      | some sk' => exact ⟨CleanupPhase.drainScratch sk', by simp, by simp⟩
    · exact ⟨CleanupPhase.drainScratch sk, by simp, by simp⟩

/-- Any number of `Mg`-steps from a non-`checkHead` cleanup phase never lands back on
    `checkHead`: chains `mg_cleanup_step_classify` one step at a time, using
    `iterate_bind_step_stuck_at_none` once the run has collapsed to `none` (only possible from `done`). -/
lemma mg_cleanup_ne_checkHead_iterate (m : ℕ) (ph : CleanupPhase p) (hph : ph ≠ CleanupPhase.checkHead)
    (v : AllInstrState) (S : ∀ k, List (Γg p k)) :
    ((flipBindCleanup p (Mg p hSup outReg))^[m] (some ⟨some (Λg.cleanup ph), v, S⟩)).bind
        (fun cfg => cfg.l)
      ≠ some (Λg.cleanup CleanupPhase.checkHead) := by
  induction m generalizing ph v S with
  | zero => simpa using hph
  | succ m ih =>
    have hstep : flipBindCleanup p (Mg p hSup outReg)
        (some (⟨some (Λg.cleanup ph), v, S⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState))
        = some (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S) := by
      show (Turing.TM2.step (Mg p hSup outReg)) ⟨some (Λg.cleanup ph), v, S⟩ = _
      simp [Turing.TM2.step]
    rw [Function.iterate_succ_apply, hstep]
    obtain hnone | ⟨ph', hph', heq⟩ := mg_cleanup_step_classify hSup outReg ph hph v S
    · have h2 := iterate_bind_step_stuck_at_none (Mg p hSup outReg) m
        (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S) hnone
      rw [show (flipBindCleanup p (Mg p hSup outReg))^[m]
          = (fun x => x.bind (Turing.TM2.step (Mg p hSup outReg)))^[m] from rfl]
      rcases h2 with h | h <;> simp [h, hnone]
    · have heta : Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S
          = ⟨(Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S).l,
              (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S).var,
              (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup ph)) v S).stk⟩ := rfl
      rw [heq] at heta
      rw [heta]
      exact ih ph' hph' _ _

/-- Once a `Mg`-driven cleanup run has collapsed to `none`, it stays `none` forever
    (`iterate_bind_step_stuck_at_none`'s own conclusion, specialized away from its "or unmoved" branch by
    starting from `none` itself). -/
lemma flipBindCleanup_iterate_none (n : ℕ) :
    (flipBindCleanup p (Mg p hSup outReg))^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- A positive-length cleanup run starting at the source-only `checkHead` phase advances to
    `checkTail` and cannot return to `checkHead`. -/
lemma mg_cleanup_checkHead_not_return (m : ℕ) (v : AllInstrState)
    (S : ∀ k, List (Γg p k)) :
    ((flipBindCleanup p (Mg p hSup outReg))^[m]
      (flipBindCleanup p (Mg p hSup outReg)
        (some ⟨some (Λg.cleanup CleanupPhase.checkHead), v, S⟩))).bind (fun cfg => cfg.l)
      ≠ some (Λg.cleanup CleanupPhase.checkHead) := by
  have hstep : flipBindCleanup p (Mg p hSup outReg)
      (some (⟨some (Λg.cleanup CleanupPhase.checkHead), v, S⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)) =
      some (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S) := by
    show Turing.TM2.step (Mg p hSup outReg)
      ⟨some (Λg.cleanup CleanupPhase.checkHead), v, S⟩ = _
    simp [Turing.TM2.step]
  have heta : Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S =
      ⟨(Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).l,
        (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).var,
        (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).stk⟩ := rfl
  have hlabel : (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).l =
      some (Λg.cleanup CleanupPhase.checkTail) := by
    simp [Mg, cleanupProg]
  rw [hstep, heta, hlabel]
  exact mg_cleanup_ne_checkHead_iterate hSup outReg m CleanupPhase.checkTail (by simp)
    (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).var
    (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead)) v S).stk

/-- The dispatcher-swap theorem's main composition needs: if a `Mg`-driven run of `n` steps
    from a non-`checkHead` label lands on `checkHead`, the same `n` steps driven by `ramStop`
    (agreeing with `Mg` everywhere except `checkHead` itself, `ramStop_agrees`) land on the exact
    same config — `checkHead` is visited at most once (module docstring), so the swap never
    crosses the one point the two dispatchers actually disagree at. -/
lemma ramStop_iterate_eq_of_mg_landing (n : ℕ) (l₀ : Λg p)
    (hl₀ : l₀ ≠ Λg.cleanup CleanupPhase.checkHead)
    (v : AllInstrState) (S : ∀ k, List (Γg p k)) (cfg' : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (heq : (flipBindCleanup p (Mg p hSup outReg))^[n] (some ⟨some l₀, v, S⟩) = some cfg')
    (hfinal : cfg'.l = some (Λg.cleanup CleanupPhase.checkHead)) :
    (flipBindCleanup p (ramStop hSup outReg))^[n] (some ⟨some l₀, v, S⟩) = some cfg' := by
  induction n generalizing l₀ v S with
  | zero =>
    exfalso; apply hl₀
    have heq' : cfg' = ⟨some l₀, v, S⟩ := by simpa using heq.symm
    have hl : cfg'.l = some l₀ := by rw [heq']
    rw [hl] at hfinal
    exact Option.some.inj hfinal
  | succ n ih =>
    have hMstep : flipBindCleanup p (Mg p hSup outReg)
        (some (⟨some l₀, v, S⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState))
        = flipBindCleanup p (ramStop hSup outReg)
          (some (⟨some l₀, v, S⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)) := by
      show Turing.TM2.step (Mg p hSup outReg) ⟨some l₀, v, S⟩
          = Turing.TM2.step (ramStop hSup outReg) ⟨some l₀, v, S⟩
      simp only [Turing.TM2.step]
      rw [show ramStop hSup outReg l₀ = Mg p hSup outReg l₀ from ramStop_agrees hSup outReg l₀ hl₀]
    rw [Function.iterate_succ_apply] at heq
    rw [Function.iterate_succ_apply, ← hMstep]
    rcases hX : flipBindCleanup p (Mg p hSup outReg)
        (some (⟨some l₀, v, S⟩ : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)) with _ | c1
    · rw [hX] at heq
      rw [flipBindCleanup_iterate_none] at heq
      exact absurd heq (by simp)
    · rw [hX] at heq
      have hraw : (flipBindCleanup p (Mg p hSup outReg))^[n]
          = (fun x => x.bind (Turing.TM2.step (Mg p hSup outReg)))^[n] := rfl
      by_cases hc1 : c1.l = some (Λg.cleanup CleanupPhase.checkHead)
      · have hc1eta : c1 = ⟨some (Λg.cleanup CleanupPhase.checkHead), c1.var, c1.stk⟩ := by
          cases c1 with | mk l var stk => simp_all
        have hn0 : n = 0 := by
          by_contra hn0
          have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)
          have hstepc1 : flipBindCleanup p (Mg p hSup outReg) (some c1)
              = some (Turing.TM2.stepAux (Mg p hSup outReg (Λg.cleanup CleanupPhase.checkHead))
                  c1.var c1.stk) := by
            show (Turing.TM2.step (Mg p hSup outReg)) c1 = _
            rw [hc1eta]
            rfl
          rw [← hn1, Function.iterate_succ_apply, hstepc1] at heq
          have hcontra := mg_cleanup_checkHead_not_return hSup outReg (n - 1) c1.var c1.stk
          apply hcontra
          rw [← hc1eta, hstepc1, heq]
          simpa using hfinal
        subst hn0
        simpa using heq
      · have hcl_ne_none : c1.l ≠ none := by
          intro hcl2
          rw [hraw] at heq
          rcases iterate_bind_step_stuck_at_none (Mg p hSup outReg) n c1 hcl2 with h | h
          · rw [h] at heq
            have hceq : cfg' = c1 := by simpa using heq.symm
            rw [hceq, hcl2] at hfinal
            exact absurd hfinal (by simp)
          · rw [h] at heq; exact absurd heq (by simp)
        obtain ⟨l₁, hcl⟩ := Option.ne_none_iff_exists'.mp hcl_ne_none
        have hl₁ : l₁ ≠ Λg.cleanup CleanupPhase.checkHead := by
          intro heql; apply hc1; rw [hcl, heql]
        have hc1eta : c1 = ⟨some l₁, c1.var, c1.stk⟩ := by
          cases c1 with | mk l var stk => simp_all
        rw [hc1eta] at heq
        rw [hc1eta]
        exact ih l₁ hl₁ c1.var c1.stk heq

/-! ## Transporting the `ramStop`-driven run into `master_flipBind`'s space, then stepping once
    more into `prep` -/

/-- The `EmitK p`-level state a RAM-only stack `Sl` embeds to before any prep/emit/cleanup work
    has run: the RAM portion unchanged (via `.base`), `out`/`countdown` empty (nothing streamed,
    no length prepared yet). -/
def initialMasterSg (Sl : ∀ k, List (Γg p k)) : ∀ k, List (EmitΓ p k)
  | .base k => Sl k
  | .out => []
  | .countdown => []

/-- Transporting a `ramStop`-driven run (`ramStop`'s halt at `checkHead` makes
    `StmtTransport.iterate_bind_step_liftStmt` applicable) into `master_flipBind`'s space: `masterProg`'s
    `.ram` case agrees with the lifted `ramStop` everywhere except `checkHead` itself
    (`masterProg_ram_agrees` + `ramStop_agrees`, composed), so the whole run transports verbatim,
    landing at `MasterΛ.ram (Λg.cleanup CleanupPhase.checkHead)` with the RAM-side stack matching
    the local run's final stack and every non-RAM stack (`out`/`countdown`) untouched. -/
lemma master_ram_run_of_ramStop (hSup : ProgramSupported p)
    (oReg rAddr rDest rOne rLen : Fin (regBound p)) (l₀ : Λg p) (Sl₀ : ∀ k, List (Γg p k))
    (n : ℕ) (vf : AllInstrState) (Slf : ∀ k, List (Γg p k))
    (heq : (flipBindCleanup p (ramStop hSup oReg))^[n]
        (some ⟨some l₀, AllInstrState.canonical, Sl₀⟩)
      = some ⟨some (Λg.cleanup CleanupPhase.checkHead), vf, Slf⟩) :
    ∃ sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
        (some ⟨some (MasterΛ.ram l₀), MasterState.canonical, initialMasterSg Sl₀⟩)
      = some ⟨some (MasterΛ.ram (Λg.cleanup CleanupPhase.checkHead)), sf, Sgf⟩
      ∧ sf = MasterState.setRam MasterState.canonical vf
      ∧ (∀ k, Sgf (EmitK.base k) = (Slf k).map (emitΓEquiv k))
      ∧ (∀ kg, (∀ kl, EmitK.base kl ≠ kg) → Sgf kg = initialMasterSg Sl₀ kg) := by
  exact iterate_bind_step_liftStmt EmitK.base emitΓEquiv MasterΛ.ram MasterState.getRam MasterState.setRam
    (ramStop hSup oReg) (masterProg hSup oReg rAddr rDest rOne rLen) emitK_inj
    getRam_setRam setRam_setRam setRam_getRam n l₀ AllInstrState.canonical Sl₀
    MasterState.canonical (initialMasterSg Sl₀) rfl
    (fun k => by simp [initialMasterSg, emitΓEquiv, Equiv.coe_refl, List.map_id])
    (Λg.cleanup CleanupPhase.checkHead) vf Slf (by simp [ramStop])
    (fun l hl => (masterProg_ram_agrees hSup oReg rAddr rDest rOne rLen l hl).trans
      (congrArg (liftStmt (ιK := EmitK.base) (eΓ := emitΓEquiv) (ιΛ := MasterΛ.ram)
          MasterState.getRam MasterState.setRam) (ramStop_agrees hSup oReg l hl).symm))
    heq

end NPComplete.RAMToTM.Generic

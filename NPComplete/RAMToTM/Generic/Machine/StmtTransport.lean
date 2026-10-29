module

public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Transporting a `Stmt`/`stepAux` computation across an embedding

This module proves a generic simulation for a local `Stmt` universe embedded in a larger one. The
stack-index map, alphabet equivalences, label map, and state lens let the lifted `stepAux` compute
the embedded image of the local result. Iterating this one-step theorem transports complete local
runs without repeating their per-phase transition analysis.

The stack-index map and label map are injective, each local stack alphabet is translated by an
`Equiv`, and the state lens embeds local state in the ambient state. Callers choose how private
scratch stacks and shared register or memory stacks map into the ambient machine.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open Turing Turing.TM2 Turing.TM2.Stmt

variable {Kl Kg : Type} [DecidableEq Kl] [DecidableEq Kg]
variable {Γl : Kl → Type} {Γg : Kg → Type}
variable {Λl Λg : Type} {σl σg : Type}
variable (ιK : Kl → Kg) (eΓ : ∀ k, Γl k ≃ Γg (ιK k))
variable (ιΛ : Λl → Λg)
variable (get : σg → σl) (set : σg → σl → σg)

/-- Lift a local `Stmt` into the global `K`/`Γ`/`Λ`/`σ`: `eΓ` transports alphabet values across
    the embedded stack index, `get`/`set` thread the local state through the ambient global
    state, `ιΛ` embeds jump targets. Structural recursion mirrors `Stmt` exactly, one
    constructor at a time. -/
def liftStmt : Turing.TM2.Stmt Γl Λl σl → Turing.TM2.Stmt Γg Λg σg
  | push k f q => push (ιK k) (fun s => (eΓ k) (f (get s))) (liftStmt q)
  | peek k f q => peek (ιK k) (fun s ov => set s (f (get s) (ov.map (eΓ k).symm))) (liftStmt q)
  | pop k f q => pop (ιK k) (fun s ov => set s (f (get s) (ov.map (eΓ k).symm))) (liftStmt q)
  | load a q => load (fun s => set s (a (get s))) (liftStmt q)
  | branch p q1 q2 => branch (fun s => p (get s)) (liftStmt q1) (liftStmt q2)
  | goto f => goto (fun s => ιΛ (f (get s)))
  | halt => halt

/-- The transport theorem: running `stepAux` on the lifted `Stmt` against a "glued" global
    state (stacks related to the local ones via `eΓ` on the embedded slice) gives exactly the
    embedded image of the local `stepAux` result — same next label (via `ιΛ`), the local final
    state written back through `set`, the embedded stacks updated to match the local final
    stacks (via `eΓ`), and every non-embedded stack left untouched (the "frame" clause, needed
    since private scratch used by other lifted instructions shares this global `Kg`). -/
lemma stepAux_liftStmt (ιK_inj : Function.Injective ιK) (hget : ∀ s a, get (set s a) = a)
    (hset : ∀ s a b, set (set s a) b = set s b) (hsetget : ∀ s, set s (get s) = s) :
    ∀ (stmt : Turing.TM2.Stmt Γl Λl σl) (s : σg) (Sg : ∀ k, List (Γg k)) (Sl : ∀ k, List (Γl k)),
    (∀ k, Sg (ιK k) = (Sl k).map (eΓ k)) →
    (stepAux (liftStmt ιK eΓ ιΛ get set stmt) s Sg).l
        = Option.map ιΛ (stepAux stmt (get s) Sl).l
      ∧ (stepAux (liftStmt ιK eΓ ιΛ get set stmt) s Sg).var
        = set s (stepAux stmt (get s) Sl).var
      ∧ (∀ k, (stepAux (liftStmt ιK eΓ ιΛ get set stmt) s Sg).stk (ιK k)
          = ((stepAux stmt (get s) Sl).stk k).map (eΓ k))
      ∧ (∀ kg, (∀ kl, ιK kl ≠ kg) →
          (stepAux (liftStmt ιK eΓ ιΛ get set stmt) s Sg).stk kg = Sg kg) := by
  intro stmt
  induction stmt with
  | push k f q ih =>
    intro s Sg Sl hstk
    have hupd : ∀ k' : Kl, Function.update Sg (ιK k) ((eΓ k) (f (get s)) :: Sg (ιK k)) (ιK k')
        = (Function.update Sl k (f (get s) :: Sl k) k').map (eΓ k') := by
      intro k'
      by_cases hk : k' = k
      · subst hk; simp [hstk]
      · rw [Function.update_of_ne (fun h => hk (ιK_inj h)), Function.update_of_ne hk, hstk]
    have hframe : ∀ kg, (∀ kl, ιK kl ≠ kg) →
        Function.update Sg (ιK k) ((eΓ k) (f (get s)) :: Sg (ιK k)) kg = Sg kg := by
      intro kg hkg
      exact Function.update_of_ne (Ne.symm (hkg k)) _ _
    obtain ⟨hl, hvar, hstk', hfr'⟩ := ih s
      (Function.update Sg (ιK k) ((eΓ k) (f (get s)) :: Sg (ιK k)))
      (Function.update Sl k (f (get s) :: Sl k)) hupd
    simp only [liftStmt, stepAux]
    refine ⟨hl, hvar, hstk', fun kg hkg => ?_⟩
    rw [hfr' kg hkg, hframe kg hkg]
  | peek k f q ih =>
    intro s Sg Sl hstk
    have hhead : (Sg (ιK k)).head?.map (eΓ k).symm = (Sl k).head? := by
      rw [hstk]; simp
    obtain ⟨hl, hvar, hstk', hfr'⟩ := ih (set s (f (get s) (Sl k).head?)) Sg Sl hstk
    simp only [liftStmt, stepAux, hget, hhead] at hl hvar hstk' hfr' ⊢
    refine ⟨hl, ?_, hstk', hfr'⟩
    rw [hvar, hset]
  | pop k f q ih =>
    intro s Sg Sl hstk
    have hhead : (Sg (ιK k)).head?.map (eΓ k).symm = (Sl k).head? := by
      rw [hstk]; simp
    have hupd : ∀ k' : Kl, Function.update Sg (ιK k) (Sg (ιK k)).tail (ιK k')
        = (Function.update Sl k (Sl k).tail k').map (eΓ k') := by
      intro k'
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self, Function.update_self, hstk]; simp
      · rw [Function.update_of_ne (fun h => hk (ιK_inj h)), Function.update_of_ne hk, hstk]
    have hframe : ∀ kg, (∀ kl, ιK kl ≠ kg) →
        Function.update Sg (ιK k) (Sg (ιK k)).tail kg = Sg kg := by
      intro kg hkg
      exact Function.update_of_ne (Ne.symm (hkg k)) _ _
    obtain ⟨hl, hvar, hstk', hfr'⟩ := ih (set s (f (get s) (Sl k).head?))
      (Function.update Sg (ιK k) (Sg (ιK k)).tail) (Function.update Sl k (Sl k).tail) hupd
    simp only [liftStmt, stepAux, hget, hhead] at hl hvar hstk' hfr' ⊢
    refine ⟨hl, ?_, hstk', fun kg hkg => ?_⟩
    · rw [hvar, hset]
    · rw [hfr' kg hkg, hframe kg hkg]
  | load a q ih =>
    intro s Sg Sl hstk
    obtain ⟨hl, hvar, hstk', hfr'⟩ := ih (set s (a (get s))) Sg Sl hstk
    simp only [liftStmt, stepAux, hget] at hl hvar hstk' hfr' ⊢
    refine ⟨hl, ?_, hstk', hfr'⟩
    rw [hvar, hset]
  | branch p q1 q2 ih1 ih2 =>
    intro s Sg Sl hstk
    simp only [liftStmt, stepAux]
    by_cases hp : p (get s)
    · simp only [hp, Bool.cond_true]
      exact ih1 s Sg Sl hstk
    · simp only [hp, Bool.cond_false]
      exact ih2 s Sg Sl hstk
  | goto f =>
    intro s Sg Sl hstk
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show s = set s (get s); exact (hsetget s).symm
    · exact fun k => hstk k
    · exact fun kg _ => rfl
  | halt =>
    intro s Sg Sl hstk
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show s = set s (get s); exact (hsetget s).symm
    · exact fun k => hstk k
    · exact fun kg _ => rfl

/-- Once a configuration's label is `none`, `flipBind` is stuck: it either hasn't moved yet
    (`m = 0`) or has collapsed to `none` (any `m ≥ 1`, since `step` on a `none`-labeled config
    is itself `none`, and `Option.bind none _ = none` from then on). Used to rule out a chain
    "completing" partway through a halted sub-machine. -/
lemma iterate_bind_step_stuck_at_none {K' : Type} [DecidableEq K'] {Γ' : K' → Type}
    (M : Λl → Turing.TM2.Stmt Γ' Λl σl) :
    ∀ (m : ℕ) (cfg : Turing.TM2.Cfg Γ' Λl σl), cfg.l = none →
    (fun x => Option.bind x (Turing.TM2.step M))^[m] (some cfg) = some cfg
      ∨ (fun x => Option.bind x (Turing.TM2.step M))^[m] (some cfg) = none := by
  intro m
  induction m with
  | zero => intro cfg _; left; rfl
  | succ m ih =>
    intro cfg hcfg
    right
    rw [Function.iterate_succ_apply]
    have hstep : Turing.TM2.step M cfg = none := by
      cases cfg with | mk l v S => simp_all [Turing.TM2.step]
    show (fun x => Option.bind x (Turing.TM2.step M))^[m]
        (Option.bind (some cfg) (Turing.TM2.step M)) = none
    rw [show Option.bind (some cfg) (Turing.TM2.step M) = none from hstep]
    clear ih hcfg hstep
    induction m with
    | zero => rfl
    | succ m ih2 => rw [Function.iterate_succ_apply]; simpa using ih2

variable (Ml : Λl → Turing.TM2.Stmt Γl Λl σl) (Mg : Λg → Turing.TM2.Stmt Γg Λg σg)

/-- Iterated transport, allowing the ambient machine to use a continuation at the local run's
    final label `lf` instead of executing the local halt there. The hypothesis `hMlf : Ml lf = halt`
    lets the proof rule out `l₀ = lf` while steps remain, without constraining the ambient machine
    at `ιΛ lf`. The strong conclusion `sf = set s₀ vf` follows by collapsing intermediate state
    updates with the lens's `PutPut` law. It also lets `iterate_bind_step_liftStmt_getO` show that every
    orthogonal ambient-state component remains unchanged. -/
lemma iterate_bind_step_liftStmt (ιK_inj : Function.Injective ιK) (hget : ∀ s a, get (set s a) = a)
    (hset : ∀ s a b, set (set s a) b = set s b) (hsetget : ∀ s, set s (get s) = s) :
    ∀ (n : ℕ) (l₀ : Λl) (v₀ : σl) (Sl₀ : ∀ k, List (Γl k)) (s₀ : σg) (Sg₀ : ∀ k, List (Γg k)),
    get s₀ = v₀ → (∀ k, Sg₀ (ιK k) = (Sl₀ k).map (eΓ k)) →
    ∀ lf vf Slf, Ml lf = Turing.TM2.Stmt.halt →
    (∀ l, l ≠ lf → Mg (ιΛ l) = liftStmt ιK eΓ ιΛ get set (Ml l)) →
    (fun x => Option.bind x (Turing.TM2.step Ml))^[n]
        (some (⟨some l₀, v₀, Sl₀⟩ : Cfg Γl Λl σl)) = some ⟨some lf, vf, Slf⟩ →
    ∃ sf Sgf, (fun x => Option.bind x (Turing.TM2.step Mg))^[n]
        (some (⟨some (ιΛ l₀), s₀, Sg₀⟩ : Cfg Γg Λg σg)) = some ⟨some (ιΛ lf), sf, Sgf⟩
      ∧ sf = set s₀ vf ∧ (∀ k, Sgf (ιK k) = (Slf k).map (eΓ k))
      ∧ (∀ kg, (∀ kl, ιK kl ≠ kg) → Sgf kg = Sg₀ kg) := by
  intro n
  induction n with
  | zero =>
    intro l₀ v₀ Sl₀ s₀ Sg₀ hv hstk lf vf Slf _ _ heq
    simp only [Function.iterate_zero, id_eq, Option.some.injEq, Cfg.mk.injEq] at heq
    obtain ⟨hl, hv', hs'⟩ := heq
    subst hl; subst hv'; subst hs'
    refine ⟨s₀, Sg₀, by simp, ?_, hstk, fun _ _ => rfl⟩
    rw [← hv]; exact (hsetget s₀).symm
  | succ n ih =>
    intro l₀ v₀ Sl₀ s₀ Sg₀ hv hstk lf vf Slf hMlf hM heq
    by_cases hlf : l₀ = lf
    · exfalso
      subst hlf
      rw [Function.iterate_succ_apply] at heq
      have hstep_l : (Option.bind (some (⟨some l₀, v₀, Sl₀⟩ : Cfg Γl Λl σl))
          (Turing.TM2.step Ml)) = some (⟨none, v₀, Sl₀⟩ : Cfg Γl Λl σl) := by
        show Turing.TM2.step Ml ⟨some l₀, v₀, Sl₀⟩ = _
        rw [show Turing.TM2.step Ml (⟨some l₀, v₀, Sl₀⟩ : Cfg Γl Λl σl)
            = some (stepAux (Ml l₀) v₀ Sl₀) from rfl, hMlf]
        rfl
      rw [hstep_l] at heq
      rcases iterate_bind_step_stuck_at_none Ml n (⟨none, v₀, Sl₀⟩ : Cfg Γl Λl σl) rfl with h | h <;>
        rw [h] at heq <;> simp at heq
    · rw [Function.iterate_succ_apply] at heq
      have hstep_l : (Option.bind (some (⟨some l₀, v₀, Sl₀⟩ : Cfg Γl Λl σl)) (Turing.TM2.step Ml))
          = some (stepAux (Ml l₀) v₀ Sl₀) := rfl
      rw [hstep_l] at heq
      obtain ⟨hl1, hvar1, hstk1, hfr1⟩ :=
        stepAux_liftStmt ιK eΓ ιΛ get set ιK_inj hget hset hsetget (Ml l₀) s₀ Sg₀ Sl₀ hstk
      rw [hv] at hl1 hvar1 hstk1
      have hstep_g : (Option.bind (some (⟨some (ιΛ l₀), s₀, Sg₀⟩ : Cfg Γg Λg σg))
          (Turing.TM2.step Mg)) = some (stepAux (liftStmt ιK eΓ ιΛ get set (Ml l₀)) s₀ Sg₀) := by
        show Turing.TM2.step Mg ⟨some (ιΛ l₀), s₀, Sg₀⟩ = _
        rw [show Turing.TM2.step Mg (⟨some (ιΛ l₀), s₀, Sg₀⟩ : Cfg Γg Λg σg)
            = some (stepAux (Mg (ιΛ l₀)) s₀ Sg₀) from rfl, hM l₀ hlf]
      rcases hc1 : stepAux (Ml l₀) v₀ Sl₀ with ⟨cl, cvar, cstk⟩
      rw [hc1] at hl1 hvar1 hstk1
      rcases hc1g : stepAux (liftStmt ιK eΓ ιΛ get set (Ml l₀)) s₀ Sg₀ with ⟨c1gl, c1gvar, c1gstk⟩
      rw [hc1g] at hl1 hvar1 hstk1 hfr1
      rw [hc1] at heq
      simp only at hl1 hvar1 hstk1 hfr1
      rcases cl with _ | l1
      · exfalso
        rcases iterate_bind_step_stuck_at_none Ml n ⟨none, cvar, cstk⟩ rfl with h | h <;> rw [h] at heq <;>
          simp at heq
      · subst hl1
        rw [hc1g] at hstep_g
        rw [Function.iterate_succ_apply]
        have hget1 : get c1gvar = cvar := by rw [hvar1, hget]
        obtain ⟨sf, Sgf, hrun, hsetf, hstkf, hfrf⟩ :=
          ih l1 cvar cstk c1gvar c1gstk hget1 hstk1 lf vf Slf hMlf hM heq
        refine ⟨sf, Sgf, ?_, ?_, hstkf, fun kg hkg => ?_⟩
        · show (fun x => Option.bind x (Turing.TM2.step Mg))^[n]
              (Option.bind (some (⟨some (ιΛ l₀), s₀, Sg₀⟩ : Cfg Γg Λg σg)) (Turing.TM2.step Mg))
              = _
          rw [hstep_g]
          exact hrun
        · rw [hsetf, hvar1, hset]
        · rw [hfrf kg hkg, hfr1 kg hkg]

/-- A companion to `iterate_bind_step_liftStmt`: any projection `getO` that `set` leaves untouched
    survives the transported run unchanged. This follows from `iterate_bind_step_liftStmt`'s strong state
    conclusion `sf = set s₀ vf` and the preservation hypothesis `hO`. -/
lemma iterate_bind_step_liftStmt_getO {τ : Type} (getO : σg → τ) (hO : ∀ s a, getO (set s a) = getO s)
    (ιK_inj : Function.Injective ιK) (hget : ∀ s a, get (set s a) = a)
    (hset : ∀ s a b, set (set s a) b = set s b) (hsetget : ∀ s, set s (get s) = s)
    (n : ℕ) (l₀ : Λl) (v₀ : σl) (Sl₀ : ∀ k, List (Γl k)) (s₀ : σg) (Sg₀ : ∀ k, List (Γg k))
    (hv : get s₀ = v₀) (hstk : ∀ k, Sg₀ (ιK k) = (Sl₀ k).map (eΓ k))
    (lf : Λl) (vf : σl) (Slf : ∀ k, List (Γl k)) (hMlf : Ml lf = Turing.TM2.Stmt.halt)
    (hM : ∀ l, l ≠ lf → Mg (ιΛ l) = liftStmt ιK eΓ ιΛ get set (Ml l))
    (heq : (fun x => Option.bind x (Turing.TM2.step Ml))^[n]
        (some (⟨some l₀, v₀, Sl₀⟩ : Cfg Γl Λl σl)) = some ⟨some lf, vf, Slf⟩)
    (sf : σg) (Sgf : ∀ k, List (Γg k))
    (heqg : (fun x => Option.bind x (Turing.TM2.step Mg))^[n]
        (some (⟨some (ιΛ l₀), s₀, Sg₀⟩ : Cfg Γg Λg σg)) = some ⟨some (ιΛ lf), sf, Sgf⟩) :
    getO sf = getO s₀ := by
  obtain ⟨sf', Sgf', hrun', hsetf', _, _⟩ :=
    iterate_bind_step_liftStmt ιK eΓ ιΛ get set Ml Mg ιK_inj hget hset hsetget
      n l₀ v₀ Sl₀ s₀ Sg₀ hv hstk lf vf Slf hMlf hM heq
  have heq2 := heqg.symm.trans hrun'
  simp only [Option.some.injEq, Cfg.mk.injEq] at heq2
  obtain ⟨_, hsf, _⟩ := heq2
  rw [hsf, hsetf', hO]

end NPComplete.RAMToTM

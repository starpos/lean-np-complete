module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Machine.StmtTransport

/-!
# `loadImm` realized against an arbitrary site's register

`loadImm rd n` materializes a *literal* digit list (`natToDigits n`) that isn't already sitting in
any register — unlike `store`/`load`/`add`/`move`, which only ever copy an existing runtime
register's content. `n` is fixed once a site `pc` is fixed, so `natToDigits n` is a concrete
Lean list (its length is the digit count of `n`); `pushDigits` builds a `Turing.TM2.Stmt` `push`
chain over it via plain `List.foldr`-style recursion, with **no internal `goto`**
(`Turing.TM2.stepAux` evaluates an arbitrarily long `push` chain in one `Cfg → Cfg` step, exactly like `GenericBranch.lean`'s
`jumpCode`). The only genuine TM-level loop is draining whatever `rd` already holds (`drain`,
unbounded at proof time since it depends on runtime register content) — mirroring `store`/`move`'s
"pop, discard, loop" shape.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit natToDigits liftStmt iterate_bind_step_liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (rd : Fin (regBound p))

/-- Push `ds`'s elements in order onto register `rd` (each `push` prepends, so pushing `ds` in
    list order builds `ds.reverse` on top of whatever was already there) before continuing with
    `cont` — used with `ds := (natToDigits n).reverse` so the net effect is `natToDigits n`. -/
def pushDigits (rd : Fin (regBound p)) : List Digit →
    Turing.TM2.Stmt (Γg p) LoadImmPhase (Option Digit) →
    Turing.TM2.Stmt (Γg p) LoadImmPhase (Option Digit)
  | [], cont => cont
  | d :: ds, cont => push (Kg.reg rd) (fun _ => d) (pushDigits rd ds cont)

/-- Evaluating a `pushDigits` chain in one `stepAux` call is exactly `cont`'s own evaluation
    against a stack with `ds.reverse` prepended onto `rd`'s slot — the whole chain, however long,
    contributes no extra `TM2.step`s (only `goto`/`halt` end a step), matching `jumpCode`'s
    "static tree = one step" principle. -/
lemma stepAux_pushDigits (ds : List Digit)
    (cont : Turing.TM2.Stmt (Γg p) LoadImmPhase (Option Digit))
    (v : Option Digit) (S : ∀ k, List (Γg p k)) :
    Turing.TM2.stepAux (pushDigits rd ds cont) v S
      = Turing.TM2.stepAux cont v (Function.update S (Kg.reg rd) (ds.reverse ++ S (Kg.reg rd))) := by
  induction ds generalizing S with
  | nil =>
      simp only [pushDigits, List.reverse_nil, List.nil_append]
      congr 1
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update]
      · simp [Function.update, hk]
  | cons d ds' ih =>
      show Turing.TM2.stepAux (pushDigits rd (d :: ds') cont) v S = _
      rw [pushDigits, Turing.TM2.stepAux, ih]
      congr 1
      funext k
      by_cases hk : k = Kg.reg rd
      · subst hk; simp [Function.update, List.reverse_cons, List.append_assoc]
      · simp [Function.update, hk]

/-- `loadImm rd n`'s `Stmt` tree: `drain` pops `rd` until empty (self-`goto`), then pushes
    `natToDigits n`'s digits (reversed, so the net push rebuilds `natToDigits n` exactly) and
    `goto`s `done`. -/
def loadImmProg (rd : Fin (regBound p)) (n : ℕ) :
    LoadImmPhase → Turing.TM2.Stmt (Γg p) LoadImmPhase (Option Digit)
  | .drain =>
      pop (Kg.reg rd) (fun _ ov => ov)
        (branch (fun s => s.isSome)
          (goto (fun _ => .drain))
          (pushDigits rd (natToDigits n).reverse (goto (fun _ => .done))))
  | .done => halt

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindLoadImm (rd : Fin (regBound p)) (n : ℕ) :
    Option (Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)) →
      Option (Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)) :=
  fun x => x.bind (Turing.TM2.step (loadImmProg rd n))

lemma flipBindLoadImm_drain_cons (n : ℕ) (d : Digit) (rest : List Digit)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRd : Sg (Kg.reg rd) = d :: rest) :
    flipBindLoadImm rd n
        (some (⟨some LoadImmPhase.drain, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)))
      = some ⟨some LoadImmPhase.drain, some d, Function.update Sg (Kg.reg rd) rest⟩ := by
  show (Turing.TM2.step (loadImmProg rd n))
      (⟨some LoadImmPhase.drain, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)) = _
  simp [loadImmProg, hRd]

/-- Draining register `rd`, discarding its content, then rebuilding it as `natToDigits n` — the
    empty-check that ends the loop and the whole `pushDigits` chain both fire within this one
    `stepAux` call (`stepAux_pushDigits`). -/
lemma flipBindLoadImm_drain_nil_exit (n : ℕ)
    (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit) (hRd : Sg (Kg.reg rd) = ([] : List Digit)) :
    flipBindLoadImm rd n
        (some (⟨some LoadImmPhase.drain, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)))
      = some ⟨some LoadImmPhase.done, none,
          Function.update Sg (Kg.reg rd) (natToDigits n)⟩ := by
  show (Turing.TM2.step (loadImmProg rd n))
      (⟨some LoadImmPhase.drain, v0, Sg⟩ :
        Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)) = _
  show some (Turing.TM2.stepAux (loadImmProg rd n LoadImmPhase.drain) v0 Sg) = _
  rw [loadImmProg, Turing.TM2.stepAux, hRd]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, stepAux_pushDigits,
    Turing.TM2.stepAux, List.reverse_reverse]
  congr 2
  funext k
  by_cases hk : k = Kg.reg rd
  · subst hk; simp [Function.update]
  · simp [Function.update, hk]

/-- Draining register `rd`'s existing content (whatever length) and rebuilding it as
    `natToDigits n`, in `dest.length + 1` steps — the whole `loadImm` run, since draining is the
    only genuine loop (the literal push chain is one more step, folded into the last iteration's
    empty-check, `flipBindLoadImm_drain_nil_exit`). -/
lemma drain_loop (n : ℕ) (dest : List Digit) (Sg : ∀ k, List (Γg p k)) (v0 : Option Digit)
    (hRd : Sg (Kg.reg rd) = dest) :
    (flipBindLoadImm rd n)^[dest.length + 1]
        (some (⟨some LoadImmPhase.drain, v0, Sg⟩ :
          Turing.TM2.Cfg (Γg p) LoadImmPhase (Option Digit)))
      = some ⟨some LoadImmPhase.done, none,
          Function.update Sg (Kg.reg rd) (natToDigits n)⟩ := by
  induction dest generalizing Sg v0 with
  | nil => exact flipBindLoadImm_drain_nil_exit rd n Sg v0 hRd
  | cons d dest' ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        flipBindLoadImm_drain_cons rd n d dest' Sg v0 hRd,
        ih (Function.update Sg (Kg.reg rd) dest') (some d) (by simp)]
      simp only [Function.update_idem]

/-! ## Site dispatcher package -/

/-- `loadImm`'s `Stmt` tree at site `pc`, before embedding into `Λg p`: `done` bridges to the
    next instruction (`pc.1 + 1`), every other phase is `loadImmProg` lifted via `execVia`. -/
def loadImmCodeBody (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n) : LoadImmPhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState :=
  fun l =>
    if l = LoadImmPhase.done then bridgeTo p (pc.1 + 1)
    else liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
        AllInstrState.getLoadImm AllInstrState.setLoadImm
        (loadImmProg (regAt p pc rd (by rw [h]; simp [regsOf])) n l)

/-- `loadImmCodeBody`, cast once from `LoadImmPhase → _` to the `SiteCode p pc` shape
    `PhaseOf (p.get pc) → _` that `InstrImpl.code` requires. -/
def loadImmCode (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n) : SiteCode p pc :=
  cast (congrArg (fun j => PhaseOf j → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) h.symm)
    (loadImmCodeBody p pc rd n h)

/-- `loadImmCode` undoes its own cast when applied to a correspondingly-cast `LoadImmPhase`
    value. -/
lemma loadImmCode_apply (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n) (l : LoadImmPhase) :
    loadImmCode p pc rd n h (cast (congrArg PhaseOf h.symm) l) = loadImmCodeBody p pc rd n h l :=
  cast_apply_phaseOf p pc h (loadImmCodeBody p pc rd n h) l

/-- Any dispatcher agreeing with `loadImmCode` at site `pc` installs the lifted `loadImmProg`
    tree at every non-`done` label. -/
lemma loadImmCode_agrees_ne_done (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadImmCode p pc rd n h) M) :
    ∀ l : LoadImmPhase, l ≠ LoadImmPhase.done →
      M (execVia p pc h l) = liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k))
        (execVia p pc h) AllInstrState.getLoadImm AllInstrState.setLoadImm
        (loadImmProg (regAt p pc rd (by rw [h]; simp [regsOf])) n l) := by
  intro l hl
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) l)
  rw [show execVia p pc h l = Λg.exec pc (cast (congrArg PhaseOf h.symm) l) from rfl, hone,
    loadImmCode_apply]
  exact ite_eq_right hl

/-- Any dispatcher agreeing with `loadImmCode` at site `pc` installs `bridgeTo p (pc.1+1)` at
    `loadImm`'s own `done` label. -/
lemma loadImmCode_agrees_done (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadImmCode p pc rd n h) M) :
    M (execVia p pc h LoadImmPhase.done) = bridgeTo p (pc.1 + 1) := by
  have hone := hAgrees (cast (congrArg PhaseOf h.symm) LoadImmPhase.done)
  rw [show execVia p pc h LoadImmPhase.done
      = Λg.exec pc (cast (congrArg PhaseOf h.symm) LoadImmPhase.done) from rfl, hone,
    loadImmCode_apply]
  rfl

/-! ## Growth-aware companion (run_sim aggregation stage) -/

/-- The register effect isolates the RAM-side update used by the stack-frame proof. -/
lemma loadImm_impl_growing_bounded_step_regs (rd imm : ℕ) (r : RAM)
    (hcurEq : r.current = Instruction.loadImm rd imm) :
    (step r).regs = bankWrite r.regs rd imm := by
  simp [step, hcurEq]

/-- The representation fixes the instruction at the selected program counter. -/
lemma loadImm_impl_growing_bounded_current (p : List Instruction) (pc : Fin p.length)
    (rd imm : ℕ) (h : p.get pc = .loadImm rd imm) (r : RAM) (hprog : r.program = p)
    (hpcEq : r.pc = pc.1) : r.current = Instruction.loadImm rd imm := by
  rw [RAM.current, hprog, hpcEq, List.getD_eq_getElem p Instruction.halt pc.2]
  exact h

/-- The site begins at the drain label, so the run helper need not unfold control representation. -/
lemma loadImm_impl_growing_bounded_label (p : List Instruction) (pc : Fin p.length)
    (rd imm : ℕ) (h : p.get pc = .loadImm rd imm)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (hpcEq : r.pc = pc.1)
    (hctrl : ControlRep p r.pc cfg.l) :
    cfg.l = some (execVia p pc h LoadImmPhase.drain) := by
  have hstart : startPhaseOpt (Instruction.loadImm rd imm) = some LoadImmPhase.drain := rfl
  have hentry : entryAt p pc.1 = execVia p pc h LoadImmPhase.drain :=
    entryAt_eq_execVia p pc h LoadImmPhase.drain hstart
  rw [ControlRep] at hctrl
  rw [hpcEq] at hctrl
  rw [hctrl, hentry]

/-- The drain run and bridge determine the complete one-site stack update. -/
lemma loadImm_impl_growing_bounded_run (p : List Instruction) (pc : Fin p.length)
    (rd imm old : ℕ) (h : p.get pc = .loadImm rd imm)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState)
    (hAgrees : SiteAgrees p pc (loadImmCode p pc rd imm h) M)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState)
    (hvar : cfg.var = AllInstrState.canonical)
    (hcl : cfg.l = some (execVia p pc h LoadImmPhase.drain))
    (rd' : Fin (regBound p))
    (hrd' : rd' = regAt p pc rd (by rw [h]; simp [regsOf]))
    (hRdVal : cfg.stk (Kg.reg rd') = natToDigits old) :
    ∃ Sgf,
      (flipBindG p M)^[(natToDigits old).length + 1 + 1] (some cfg) =
        some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ ∧
      Sgf = Function.update cfg.stk (Kg.reg rd') (natToDigits imm) := by
  rw [hrd'] at hRdVal
  have hDrainRun := drain_loop
    (regAt p pc rd (by rw [h]; simp [regsOf])) imm (natToDigits old) cfg.stk none hRdVal
  have hstkTriv : ∀ k, cfg.stk (id k) = List.map (⇑(Equiv.refl (Γg p k))) (cfg.stk k) := by
    intro k
    simp
  obtain ⟨sf, Sgf, hrun, hsetf, hstkf, _hframef⟩ :=
    iterate_bind_step_liftStmt (ιK := id) (eΓ := fun k => Equiv.refl (Γg p k)) (execVia p pc h)
      AllInstrState.getLoadImm AllInstrState.setLoadImm
      (loadImmProg (regAt p pc rd (by rw [h]; simp [regsOf])) imm) M
      Function.injective_id AllInstrState.getLoadImm_setLoadImm
      AllInstrState.setLoadImm_setLoadImm AllInstrState.setLoadImm_getLoadImm
      _ LoadImmPhase.drain none cfg.stk
      AllInstrState.canonical cfg.stk rfl hstkTriv
      LoadImmPhase.done none
      (Function.update cfg.stk
        (Kg.reg (regAt p pc rd (by rw [h]; simp [regsOf]))) (natToDigits imm))
      rfl (loadImmCode_agrees_ne_done p pc rd imm h M hAgrees) hDrainRun
  have hsfCanon : sf = AllInstrState.canonical := by rw [hsetf]; rfl
  have hbridgeStep : Turing.TM2.step M
      (⟨some (execVia p pc h LoadImmPhase.done), sf, Sgf⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) =
      some ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ := by
    have hMdone := loadImmCode_agrees_done p pc rd imm h M hAgrees
    rw [show Turing.TM2.step M
        (⟨some (execVia p pc h LoadImmPhase.done), sf, Sgf⟩ :
          Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) =
          some (Turing.TM2.stepAux (M (execVia p pc h LoadImmPhase.done)) sf Sgf) from rfl,
      hMdone, hsfCanon, bridgeTo]
    rfl
  have hcfgEq : cfg =
      (⟨some (execVia p pc h LoadImmPhase.drain), AllInstrState.canonical, cfg.stk⟩ :
        Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) := by
    have heta : cfg = ⟨cfg.l, cfg.var, cfg.stk⟩ := by cases cfg; rfl
    rw [heta, hcl, hvar]
  refine ⟨Sgf, ?_, ?_⟩
  · rw [hcfgEq, Function.iterate_succ_apply',
      show flipBindG p M = fun x => Option.bind x (Turing.TM2.step M) from rfl, hrun]
    exact hbridgeStep
  · funext k
    rw [hrd']
    exact stack_eq_of_map_equiv_refl Sgf _ hstkf k

/-- The final stacks encode the register update and preserve all non-register stacks. -/
lemma loadImm_impl_growing_bounded_stk {p : List Instruction} (stk : ∀ k, List (Γg p k))
    (r : RAM) (rd imm : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.loadImm rd imm)
    (hregs : ∀ i : Fin (regBound p), stk (Kg.reg i) = natToDigits (r.regs i))
    (Sgf : ∀ k, List (Γg p k))
    (hSgf : Sgf = Function.update stk (Kg.reg rd') (natToDigits imm)) :
    (∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i)) ∧
    (∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = stk k) := by
  subst hSgf
  refine ⟨fun i => ?_, fun k hk => Function.update_of_ne (hk rd') _ _⟩
  rw [loadImm_impl_growing_bounded_step_regs rd imm r hcurEq]
  by_cases hi : i = rd'
  · rw [hi, Function.update_self, ← hrdval, bankWrite_same]
  · have hid : i.1 ≠ rd := by rw [← hrdval]; exact fun heq => hi (Fin.ext heq)
    rw [bankWrite_diff _ _ _ _ hid,
      Function.update_of_ne (show Kg.reg i ≠ Kg.reg rd' by simp [hi])]
    exact hregs i

/-- The post-run configuration represents the corresponding RAM step. -/
lemma loadImm_impl_growing_bounded_represents (p : List Instruction) (pc : Fin p.length)
    (rd imm : ℕ) (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (hRep : Represents p cfg r) (hpcEq : r.pc = pc.1)
    (hcurEq : r.current = Instruction.loadImm rd imm)
    (Sgf : ∀ k, List (Γg p k))
    (hreg : ∀ i : Fin (regBound p), Sgf (Kg.reg i) = natToDigits ((step r).regs i))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    Represents p ⟨some (entryAt p (pc.1 + 1)), AllInstrState.canonical, Sgf⟩ (step r) := by
  obtain ⟨hprog, -, ⟨log, hmemstk, hmemlookup⟩, -, hscratch, -⟩ := hRep
  have hpcSucc : (step r).pc = pc.1 + 1 := by simp [step, hcurEq]; simpa using hpcEq
  refine ⟨by simp [step, hcurEq, hprog], hreg, ⟨log, ?_, ?_⟩, rfl, ?_, ?_⟩
  · show Sgf Kg.mem = _
    rw [hother _ (by simp)]
    exact hmemstk
  · intro a
    rw [step, hcurEq]
    exact hmemlookup a
  · intro s
    show Sgf (Kg.scratch s) = _
    rw [hother _ (by simp)]
    exact hscratch s
  · simp only [ControlRep]
    exact congrArg some (congrArg (entryAt p) hpcSucc.symm)

/-- Bound the drain's iterations by the site potential. -/
lemma loadImm_impl_growing_bounded_time (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM) (rd imm : ℕ)
    (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.loadImm rd imm) (steps : ℕ)
    (hsteps : steps ≤ (natToDigits (r.regs rd)).length + 2) :
    steps ≤ (regSize p r + (cfg.stk Kg.mem).length +
      instructionCost r.regs r.mem r.current + 1) ^ 2 := by
  have hle := natToDigits_length_le_regSize p r rd'
  rw [hrdval] at hle
  rw [hcurEq]
  simp only [instructionCost]
  nlinarith [Nat.zero_le (bitLen imm), Nat.zero_le (cfg.stk Kg.mem).length]

/-- Bound the register and memory potential growth of the immediate write. -/
lemma loadImm_impl_growing_bounded_growth (p : List Instruction)
    (cfg : Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) (r : RAM)
    (rd imm : ℕ) (rd' : Fin (regBound p)) (hrdval : rd'.1 = rd)
    (hcurEq : r.current = Instruction.loadImm rd imm) (Sgf : ∀ k, List (Γg p k))
    (hother : ∀ k, (∀ i : Fin (regBound p), k ≠ Kg.reg i) → Sgf k = cfg.stk k) :
    regSize p (step r) + (Sgf Kg.mem).length ≤
      regSize p r + (cfg.stk Kg.mem).length + 1 * (instructionCost r.regs r.mem r.current + 1) := by
  have hregseq := loadImm_impl_growing_bounded_step_regs rd imm r hcurEq
  have hgrow : regSize p (step r) ≤ regSize p r + (natToDigits imm).length := by
    show (∑ j : Fin (regBound p), (natToDigits ((step r).regs j)).length) ≤ _
    rw [hregseq, ← hrdval]
    exact regSize_bankWrite_le p r rd' imm _ le_rfl
  have hle : (natToDigits imm).length ≤ bitLen imm := natToDigits_length_le_bitLen imm
  rw [hother Kg.mem (by simp), hcurEq]
  simp only [instructionCost, one_mul]
  omega

/-- `loadImmCode`'s growth companion: `mem` is untouched, and the only register that can grow is
    `rd`, to the immediate `n`'s digit length — bounded by `instructionCost` since `loadImm`'s own
    cost charges exactly `bitLen n + 1`. -/
lemma loadImm_impl_growingBoundedSiteStepSim (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n) :
    GrowingBoundedSiteStepSim p pc (loadImmCode p pc rd n h) 1 1 := by
  intro M hAgrees cfg r hRep hpcEq _hcur
  have hRep' := hRep
  obtain ⟨hprog, hregs, ⟨log, hmemstk, hmemlookup⟩, hvar, hscratch, hctrl⟩ := hRep
  have hcurEq := loadImm_impl_growing_bounded_current p pc rd n h r hprog hpcEq
  have hcl := loadImm_impl_growing_bounded_label p pc rd n h cfg r hpcEq hctrl
  set rd' := regAt p pc rd (by rw [h]; simp [regsOf]) with hrd'Def
  have hrdval : rd'.1 = rd := by rw [hrd'Def]; rfl
  have hRdVal : cfg.stk (Kg.reg rd') = natToDigits (r.regs rd) := hregs rd'
  obtain ⟨Sgf, hrun, hSgf⟩ := loadImm_impl_growing_bounded_run p pc rd n (r.regs rd) h
    M hAgrees cfg hvar hcl rd' hrd'Def hRdVal
  obtain ⟨hreg, hother⟩ := loadImm_impl_growing_bounded_stk cfg.stk r rd n rd' hrdval
    hcurEq hregs Sgf hSgf
  refine ⟨(natToDigits (r.regs rd)).length + 1 + 1, _, hrun, ?_, ?_, ?_, ?_⟩
  · exact loadImm_impl_growing_bounded_represents p pc rd n cfg r hRep' hpcEq hcurEq
      Sgf hreg hother
  · exact hother Kg.io (by simp)
  · simpa only [one_mul] using
      loadImm_impl_growing_bounded_time p cfg r rd n rd' hrdval hcurEq
        ((natToDigits (r.regs rd)).length + 1 + 1) (by omega)
  · exact loadImm_impl_growing_bounded_growth p cfg r rd n rd' hrdval hcurEq Sgf hother

/-- `loadImm`'s `GrowingTimedInstrImpl` package. -/
def loadImmGrowingTimedImpl (p : List Instruction) (pc : Fin p.length) (rd n : ℕ)
    (h : p.get pc = .loadImm rd n) : GrowingTimedInstrImpl p pc where
  code := loadImmCode p pc rd n h
  C := 1
  G := 1
  growingSim := loadImm_impl_growingBoundedSiteStepSim p pc rd n h

end NPComplete.RAMToTM.Generic

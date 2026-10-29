module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Machines.TM1to0
public import NPComplete.CookLevin.Machines.TM2to1
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Data.List.ReduceOption

/-!
Mathlib TM2 already has a poly-time function layer, but the Cook-Levin
implication composes on the standard single-tape model. Time must be a
`Polynomial ℕ` at the input-list length of a bundled finite-support TM0;
an abstract `∃ S, size : S → ℕ` spec would be vacuous. The tape alphabet
is `Option Γ` so that `none` is the unique blank: a raw `Bool` tape would
quotient away trailing `false` bits and could not host `List Bool`
encodings.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)
open Polynomial
open scoped Polynomial

variable {Γ Λ : Type*}

/-- Encoding symbols as non-blank tape cells. -/
@[stable_api] def tapeSymbols (l : List Γ) : List (Option Γ) :=
  l.map some

/-- Halt on a tape that is exactly the output list, head at its first cell. -/
def MachineOutputs [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input output : List Γ) : Prop :=
  ∃ (q : Λ) (t : ℕ),
    StepsTo (step M) (init input) ⟨q, Tape.mk₁ output⟩ t ∧
    step M ⟨q, Tape.mk₁ output⟩ = none

/-- Same as `MachineOutputs`, with an explicit step budget. -/
@[stable_api] def MachineOutputsInTime [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input output : List Γ) (m : ℕ) : Prop :=
  ∃ (q : Λ) (t : ℕ),
    t ≤ m ∧
    StepsTo (step M) (init input) ⟨q, Tape.mk₁ output⟩ t ∧
    step M ⟨q, Tape.mk₁ output⟩ = none

/-- FinTM0 wrapper: output is the concrete list sitting at the halt tape. -/
def TM0Outputs (tm : FinTM0) (input output : List tm.Γ) : Prop :=
  MachineOutputs tm.M input output

/-- FinTM0 wrapper with a step budget. -/
def TM0OutputsInTime (tm : FinTM0) (input output : List tm.Γ) (m : ℕ) : Prop :=
  MachineOutputsInTime tm.M input output m

lemma TM0OutputsInTime.to_tm0Outputs {tm : FinTM0} {input output : List tm.Γ}
    {m : ℕ} (h : TM0OutputsInTime tm input output m) :
    TM0Outputs tm input output := by
  obtain ⟨q, t, _, hsteps, hhalt⟩ := h
  exact ⟨q, t, hsteps, hhalt⟩

lemma machineOutputsInTime_to_outputs [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {input output : List Γ} {m : ℕ}
    (h : MachineOutputsInTime M input output m) :
    MachineOutputs M input output := by
  obtain ⟨q, t, _, hsteps, hhalt⟩ := h
  exact ⟨q, t, hsteps, hhalt⟩

lemma step_eq_none_iff [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {q : Λ} {T : Tape Γ} : step M ⟨q, T⟩ = none ↔ M q T.head = none := by
  simp [step, Option.map_eq_none_iff]

/-- Bundled finite-support TM0 whose tape alphabet is `Option Γ`. -/
@[stable_api] structure TM0ComputableAux (Γ : Type) [Fintype Γ] where
  Λ : Type
  [ΛInhabited : Inhabited Λ]
  [ΛDecidableEq : DecidableEq Λ]
  M : Machine (Option Γ) Λ
  S : Finset Λ
  supports : Supports M ↑S

attribute [instance] TM0ComputableAux.ΛInhabited TM0ComputableAux.ΛDecidableEq

def TM0ComputableAux.toFinTM0 {Γ : Type} [Fintype Γ] (tm : TM0ComputableAux Γ) :
    FinTM0 where
  Γ := Option Γ
  Λ := tm.Λ
  M := tm.M
  S := tm.S
  supports := tm.supports

/-- A TM0 plus a proof it computes `f` under the given encodings. -/
structure TM0Computable {α β Γ : Type} [Fintype Γ]
    (ea : α → List Γ) (eb : β → List Γ) (f : α → β) extends TM0ComputableAux Γ where
  outputsFun : ∀ a, MachineOutputs M (tapeSymbols (ea a)) (tapeSymbols (eb (f a)))

/-- A TM0 plus a time function bounding the number of steps. -/
structure TM0ComputableInTime {α β Γ : Type} [Fintype Γ]
    (ea : α → List Γ) (eb : β → List Γ) (f : α → β) extends TM0ComputableAux Γ where
  time : ℕ → ℕ
  outputsFun : ∀ a,
    MachineOutputsInTime M (tapeSymbols (ea a)) (tapeSymbols (eb (f a)))
      (time (ea a).length)

/-- A TM0 plus a polynomial bound at the input-list length. -/
@[stable_api] structure TM0ComputableInPolyTime {α β Γ : Type} [Fintype Γ]
    (ea : α → List Γ) (eb : β → List Γ) (f : α → β) extends TM0ComputableAux Γ where
  time : Polynomial ℕ
  outputsFun : ∀ a,
    MachineOutputsInTime M (tapeSymbols (ea a)) (tapeSymbols (eb (f a)))
      (time.eval (ea a).length)

def TM0ComputableInTime.toTM0Computable {α β Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {f : α → β}
    (h : TM0ComputableInTime ea eb f) : TM0Computable ea eb f where
  toTM0ComputableAux := h.toTM0ComputableAux
  outputsFun a := machineOutputsInTime_to_outputs (h.outputsFun a)

def TM0ComputableInPolyTime.toTM0ComputableInTime {α β Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {f : α → β}
    (h : TM0ComputableInPolyTime ea eb f) : TM0ComputableInTime ea eb f where
  toTM0ComputableAux := h.toTM0ComputableAux
  time := fun n => h.time.eval n
  outputsFun := h.outputsFun

def TM0ComputableInPolyTime.toTM0Computable {α β Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {f : α → β}
    (h : TM0ComputableInPolyTime ea eb f) : TM0Computable ea eb f :=
  h.toTM0ComputableInTime.toTM0Computable

lemma TM0ComputableInTime.tm_outputs_in_time {α β Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {f : α → β}
    (h : TM0ComputableInTime ea eb f) (a : α) :
    TM0OutputsInTime h.toFinTM0 (tapeSymbols (ea a)) (tapeSymbols (eb (f a)))
      (h.time (ea a).length) :=
  h.outputsFun a

/-! ## Identity computer -/

def idMachine (Γ : Type*) : Machine (Option Γ) Unit :=
  fun _ _ => none

lemma idMachine_supports (Γ : Type*) :
    Supports (idMachine Γ) ↑({()} : Finset Unit) :=
  ⟨Finset.mem_singleton_self _, fun h _ => by simp [idMachine] at h⟩

lemma idMachine_outputs_in_time (l : List Γ) :
    MachineOutputsInTime (idMachine Γ) (tapeSymbols l) (tapeSymbols l) 0 :=
  ⟨(), 0, le_rfl, stepsTo_zero _ _, by simp [step_eq_none_iff, idMachine]⟩

noncomputable def idComputableInPolyTime {α Γ : Type} [Fintype Γ] (ea : α → List Γ) :
    TM0ComputableInPolyTime ea ea id where
  Λ := Unit
  M := idMachine Γ
  S := {()}
  supports := idMachine_supports Γ
  time := 0
  outputsFun a := by
    simpa [id, Polynomial.eval_zero] using idMachine_outputs_in_time (ea a)

/-! ## Concatenated machine (run `f`, then `g`) -/

/-- States of the sequential composition: first `f`, then `g`. -/
inductive CompState (Λf Λg : Type*)
  | runF : Λf → CompState Λf Λg
  | runG : Λg → CompState Λf Λg
  deriving DecidableEq

instance {Λf Λg : Type*} [Inhabited Λf] : Inhabited (CompState Λf Λg) :=
  ⟨CompState.runF default⟩

section Comp
set_option linter.unusedSectionVars false
variable {Λf Λg : Type*} [Inhabited Λf] [Inhabited Λg]

/-- Run `Mf` until it would halt, no-op-write into `Mg`, then run `Mg`. -/
def compMachine (Mf : Machine (Option Γ) Λf) (Mg : Machine (Option Γ) Λg) :
    Machine (Option Γ) (CompState Λf Λg)
  | CompState.runF q, a =>
    match Mf q a with
    | some (q', s) => some (CompState.runF q', s)
    | none => some (CompState.runG default, .write a)
  | CompState.runG q, a =>
    match Mg q a with
    | some (q', s) => some (CompState.runG q', s)
    | none => none

def liftF (c : Cfg (Option Γ) Λf) : Cfg (Option Γ) (CompState Λf Λg) :=
  ⟨CompState.runF c.q, c.Tape⟩

def liftG (c : Cfg (Option Γ) Λg) : Cfg (Option Γ) (CompState Λf Λg) :=
  ⟨CompState.runG c.q, c.Tape⟩

lemma liftF_init (input : List (Option Γ)) :
    liftF (init (Λ := Λf) input) = init (Λ := CompState Λf Λg) input :=
  rfl

lemma comp_step_runF {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c c' : Cfg (Option Γ) Λf}
    (h : step Mf c = some c') :
    step (compMachine Mf Mg) (liftF c) = some (liftF c') := by
  rcases c with ⟨q, T⟩
  rcases c' with ⟨q', T'⟩
  simp only [step, liftF] at h ⊢
  cases hMf : Mf q T.head with
  | none => simp [hMf] at h
  | some qs =>
    rcases qs with ⟨q₂, s⟩
    simp only [hMf, Option.map_some, Option.some.injEq] at h
    cases s <;> simp [compMachine, hMf] at h ⊢ <;> exact h

lemma comp_step_switch {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c : Cfg (Option Γ) Λf}
    (h : step Mf c = none) :
    step (compMachine Mf Mg) (liftF c) = some (liftG ⟨default, c.Tape⟩) := by
  rcases c with ⟨q, T⟩
  have hnone : Mf q T.head = none := step_eq_none_iff.mp h
  simp [step, liftF, liftG, compMachine, hnone, Tape.write_self]

lemma comp_step_runG {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c c' : Cfg (Option Γ) Λg}
    (h : step Mg c = some c') :
    step (compMachine Mf Mg) (liftG c) = some (liftG c') := by
  rcases c with ⟨q, T⟩
  rcases c' with ⟨q', T'⟩
  simp only [step, liftG] at h ⊢
  cases hMg : Mg q T.head with
  | none => simp [hMg] at h
  | some qs =>
    rcases qs with ⟨q₂, s⟩
    simp only [hMg, Option.map_some, Option.some.injEq] at h
    cases s <;> simp [compMachine, hMg] at h ⊢ <;> exact h

lemma comp_step_halt_g {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c : Cfg (Option Γ) Λg}
    (h : step Mg c = none) :
    step (compMachine Mf Mg) (liftG c) = none := by
  rcases c with ⟨q, T⟩
  have hnone : Mg q T.head = none := step_eq_none_iff.mp h
  simp [step, liftG, compMachine, hnone]

lemma stepsTo_liftF {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c c' : Cfg (Option Γ) Λf} {t : ℕ}
    (h : StepsTo (step Mf) c c' t) :
    StepsTo (step (compMachine Mf Mg)) (liftF c) (liftF c') t := by
  induction t generalizing c' with
  | zero =>
    simp only [StepsTo] at h
    cases h
    exact stepsTo_zero _ _
  | succ t ih =>
    obtain ⟨b, hb, hstep⟩ := (TM1to0.stepsTo_succ_iff).1 h
    exact stepsTo_succ _ (ih hb) (comp_step_runF hstep)

lemma stepsTo_liftG {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {c c' : Cfg (Option Γ) Λg} {t : ℕ}
    (h : StepsTo (step Mg) c c' t) :
    StepsTo (step (compMachine Mf Mg)) (liftG c) (liftG c') t := by
  induction t generalizing c' with
  | zero =>
    simp only [StepsTo] at h
    cases h
    exact stepsTo_zero _ _
  | succ t ih =>
    obtain ⟨b, hb, hstep⟩ := (TM1to0.stepsTo_succ_iff).1 h
    exact stepsTo_succ _ (ih hb) (comp_step_runG hstep)

lemma machineOutputsInTime_comp {Mf : Machine (Option Γ) Λf}
    {Mg : Machine (Option Γ) Λg} {input mid output : List (Option Γ)} {mf mg : ℕ}
    (hf : MachineOutputsInTime Mf input mid mf)
    (hg : MachineOutputsInTime Mg mid output mg) :
    MachineOutputsInTime (compMachine Mf Mg) input output (mg + 1 + mf) := by
  obtain ⟨qf, tf, htf, hfsteps, hfhalt⟩ := hf
  obtain ⟨qg, tg, htg, hgsteps, hghalt⟩ := hg
  refine ⟨CompState.runG qg, tg + (tf + 1), ?_, ?_, ?_⟩
  · omega
  · have hF : StepsTo (step (compMachine Mf Mg)) (init input)
        (liftF ⟨qf, Tape.mk₁ mid⟩) tf := by
      simpa [liftF_init] using stepsTo_liftF (Mg := Mg) hfsteps
    have hSw : step (compMachine Mf Mg) (liftF ⟨qf, Tape.mk₁ mid⟩) =
        some (liftG ⟨default, Tape.mk₁ mid⟩) :=
      comp_step_switch hfhalt
    have hG : StepsTo (step (compMachine Mf Mg))
        (liftG ⟨default, Tape.mk₁ mid⟩) (liftG ⟨qg, Tape.mk₁ output⟩) tg := by
      simpa [liftG, init] using stepsTo_liftG (Mf := Mf) hgsteps
    simpa [liftG] using
      stepsTo_trans (step (compMachine Mf Mg)) (stepsTo_succ _ hF hSw) hG
  · simpa [liftG] using comp_step_halt_g (Mf := Mf) hghalt

def compSupport [DecidableEq Λf] [DecidableEq Λg] (Sf : Finset Λf) (Sg : Finset Λg) :
    Finset (CompState Λf Λg) :=
  Sf.image CompState.runF ∪ Sg.image CompState.runG

lemma mem_support_runF [DecidableEq Λf] [DecidableEq Λg]
    {Sf : Finset Λf} {Sg : Finset Λg} {qf : Λf}
    (hq : CompState.runF qf ∈ compSupport Sf Sg) : qf ∈ Sf := by
  rw [compSupport, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hq
  rcases hq with ⟨x, hx, hxeq⟩ | ⟨_, _, hxeq⟩
  · cases hxeq; exact hx
  · cases hxeq

lemma mem_support_runG [DecidableEq Λf] [DecidableEq Λg]
    {Sf : Finset Λf} {Sg : Finset Λg} {qg : Λg}
    (hq : CompState.runG qg ∈ compSupport Sf Sg) : qg ∈ Sg := by
  rw [compSupport, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hq
  rcases hq with ⟨_, _, hxeq⟩ | ⟨x, hx, hxeq⟩
  · cases hxeq
  · cases hxeq; exact hx

lemma compMachine_supports [DecidableEq Λf] [DecidableEq Λg]
    {Mf : Machine (Option Γ) Λf} {Mg : Machine (Option Γ) Λg}
    {Sf : Finset Λf} {Sg : Finset Λg}
    (hf : Supports Mf ↑Sf) (hg : Supports Mg ↑Sg) :
    Supports (compMachine Mf Mg) ↑(compSupport Sf Sg) := by
  refine ⟨?_, ?_⟩
  · have hdef : (default : CompState Λf Λg) = CompState.runF default := rfl
    rw [hdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf.1)
  · intro q a q' s hstep hq
    cases q with
    | runF qf =>
      simp only [compMachine] at hstep
      cases hMf : Mf qf a with
      | none =>
        simp only [hMf] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg.1)
      | some qs =>
        rcases qs with ⟨qf', s'⟩
        simp only [hMf] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        have hqf : qf ∈ Sf := mem_support_runF hq
        have hqf' : qf' ∈ Sf := hf.2 hMf hqf
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hqf')
    | runG qg =>
      simp only [compMachine] at hstep
      cases hMg : Mg qg a with
      | none =>
        simp [hMg] at hstep
      | some qs =>
        rcases qs with ⟨qg', s'⟩
        simp only [hMg] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        have hqg : qg ∈ Sg := mem_support_runG hq
        have hqg' : qg' ∈ Sg := hg.2 hMg hqg
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hqg')

end Comp

def TM0ComputableAux.comp {Γ : Type} [Fintype Γ]
    (tmf tmg : TM0ComputableAux Γ) : TM0ComputableAux Γ where
  Λ := CompState tmf.Λ tmg.Λ
  M := compMachine tmf.M tmg.M
  S := compSupport tmf.S tmg.S
  supports := compMachine_supports tmf.supports tmg.supports

/-! ## Output-length bound and polynomial monotonicity -/

def optionListDataCount {Γ : Type*} : List (Option Γ) → ℕ :=
  fun l => l.reduceOption.length

lemma optionListDataCount_blank_extends {Γ : Type*} {xs ys : List (Option Γ)}
    (h : BlankExtends xs ys) : optionListDataCount xs = optionListDataCount ys := by
  obtain ⟨n, rfl⟩ := h
  simp [optionListDataCount, List.reduceOption_append, default,
    List.reduceOption_replicate_none]

def listBlankDataCount {Γ : Type*} (l : ListBlank (Option Γ)) : ℕ :=
  l.liftOn optionListDataCount fun _ _ h => optionListDataCount_blank_extends h

def optionBit (a : Option Γ) : ℕ :=
  if a.isSome then 1 else 0

lemma optionBit_le_one (a : Option Γ) : optionBit a ≤ 1 := by
  cases a <;> simp [optionBit]

def tapeDataCount {Γ : Type*} (T : Tape (Option Γ)) : ℕ :=
  listBlankDataCount T.left + optionBit T.head + listBlankDataCount T.right

lemma listBlankDataCount_mk {Γ : Type*} (l : List (Option Γ)) :
    listBlankDataCount (ListBlank.mk l) = optionListDataCount l :=
  rfl

lemma listBlankDataCount_cons {Γ : Type*} (a : Option Γ) (l : ListBlank (Option Γ)) :
    listBlankDataCount (l.cons a) = optionBit a + listBlankDataCount l := by
  refine l.induction_on fun xs => ?_
  rw [ListBlank.cons_mk, listBlankDataCount_mk, listBlankDataCount_mk]
  cases a <;> simp [optionListDataCount, optionBit, List.reduceOption, Nat.add_comm]

lemma listBlankDataCount_head_tail {Γ : Type*} (l : ListBlank (Option Γ)) :
    listBlankDataCount l = optionBit l.head + listBlankDataCount l.tail := by
  rw [← listBlankDataCount_cons l.head l.tail, ListBlank.cons_head_tail]

lemma tapeDataCount_move {Γ : Type*} (d : Dir) (T : Tape (Option Γ)) :
    tapeDataCount (T.move d) = tapeDataCount T := by
  cases d
  · rcases T with ⟨head, left, right⟩
    simp only [Tape.move, tapeDataCount, listBlankDataCount_cons]
    rw [listBlankDataCount_head_tail (l := left)]
    omega
  · rcases T with ⟨head, left, right⟩
    simp only [Tape.move, tapeDataCount, listBlankDataCount_cons]
    rw [listBlankDataCount_head_tail (l := right)]
    omega

lemma tapeDataCount_write {Γ : Type*} (b : Option Γ) (T : Tape (Option Γ)) :
    tapeDataCount (T.write b) ≤ tapeDataCount T + 1 := by
  simp [tapeDataCount, Tape.write]
  have := optionBit_le_one b
  omega

lemma tapeDataCount_step {Λ' : Type*} [Inhabited Λ'] {M : Machine (Option Γ) Λ'}
    {c c' : Cfg (Option Γ) Λ'} (h : step M c = some c') :
    tapeDataCount c'.Tape ≤ tapeDataCount c.Tape + 1 := by
  rcases c with ⟨q, T⟩
  rcases c' with ⟨q', T'⟩
  simp only [step] at h
  cases hM : M q T.head with
  | none => simp [hM] at h
  | some qs =>
    rcases qs with ⟨_, s⟩
    simp only [hM, Option.map_some, Option.some.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    cases s with
    | move d =>
      exact (tapeDataCount_move d T).le.trans (Nat.le_add_right _ 1)
    | write b =>
      exact tapeDataCount_write b T

lemma tapeDataCount_stepsTo {Λ' : Type*} [Inhabited Λ'] {M : Machine (Option Γ) Λ'}
    {c c' : Cfg (Option Γ) Λ'} {t : ℕ} (h : StepsTo (step M) c c' t) :
    tapeDataCount c'.Tape ≤ tapeDataCount c.Tape + t := by
  induction t generalizing c' with
  | zero =>
    simp only [StepsTo] at h
    cases h
    omega
  | succ t ih =>
    obtain ⟨b, hb, hstep⟩ := (TM1to0.stepsTo_succ_iff).1 h
    have := tapeDataCount_step hstep
    have := ih hb
    omega

lemma optionListDataCount_map_some (l : List Γ) :
    optionListDataCount (l.map some) = l.length := by
  simp [optionListDataCount, List.reduceOption, List.filterMap_map]

lemma tapeDataCount_mk₁ (l : List (Option Γ)) :
    tapeDataCount (Tape.mk₁ l) = optionListDataCount l := by
  simp [tapeDataCount, Tape.mk₁, Tape.mk₂, Tape.mk', listBlankDataCount_mk]
  cases l with
  | nil => simp [optionListDataCount, optionBit, default]
  | cons a xs =>
    cases a <;> simp [optionListDataCount, optionBit, List.reduceOption, Nat.add_comm]

lemma tapeDataCount_mk₁_map_some (l : List Γ) :
    tapeDataCount (Tape.mk₁ (tapeSymbols l)) = l.length := by
  simp [tapeSymbols, tapeDataCount_mk₁, optionListDataCount_map_some]

lemma machineOutputs_output_length {Λ' : Type*} [Inhabited Λ']
    {M : Machine (Option Γ) Λ'} {input output : List Γ} {m : ℕ}
    (h : MachineOutputsInTime M (tapeSymbols input) (tapeSymbols output) m) :
    output.length ≤ input.length + m := by
  obtain ⟨q, t, ht, hsteps, _⟩ := h
  have hcount := tapeDataCount_stepsTo (Λ' := Λ') hsteps
  have hinit : tapeDataCount (Tape.mk₁ (tapeSymbols input)) = input.length :=
    tapeDataCount_mk₁_map_some input
  have hfinal : tapeDataCount (Tape.mk₁ (tapeSymbols output)) = output.length :=
    tapeDataCount_mk₁_map_some output
  simp only [init] at hcount
  omega

lemma eval_mono_nat (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  refine p.induction_on' (fun p q hp hq => ?_) (fun k a => ?_)
  · simp [eval_add]
    exact add_le_add hp hq
  · simp [eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

/-- Sequential composition of TM0 poly-time computers. -/
noncomputable def TM0ComputableInPolyTime.comp {α β γ Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {ec : γ → List Γ}
    {f : α → β} {g : β → γ}
    (hf : TM0ComputableInPolyTime ea eb f)
    (hg : TM0ComputableInPolyTime eb ec g) :
    TM0ComputableInPolyTime ea ec (g ∘ f) where
  toTM0ComputableAux := hf.toTM0ComputableAux.comp hg.toTM0ComputableAux
  time := hf.time + 1 + hg.time.comp (X + hf.time)
  outputsFun a := by
    have hf' := hf.outputsFun a
    have hg' := hg.outputsFun (f a)
    have hlen : (eb (f a)).length ≤ (ea a).length + hf.time.eval (ea a).length :=
      machineOutputs_output_length hf'
    obtain ⟨q, t, ht, hsteps, hhalt⟩ := machineOutputsInTime_comp hf' hg'
    refine ⟨q, t, ?_, hsteps, hhalt⟩
    have hmono : hg.time.eval (eb (f a)).length ≤
        hg.time.eval ((ea a).length + hf.time.eval (ea a).length) :=
      eval_mono_nat hg.time hlen
    simp [eval_add, eval_one, eval_comp, eval_X] at ht hmono ⊢
    omega

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.SATRun

/-!
# Step-count bridge

The library's `StepsTo` relation counts exact steps, while tableau snapshots may stutter after
halting. This module reconciles those conventions and converts the resulting run facts into
acceptance clauses.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Bridging the stutter-free `StepsTo` count with the stuttering `runCfg` -/

/-- Peel the *last* step off a `StepsTo` chain (`stepsTo_cons_inv` peels the
first). Needed to match `runCfg`'s own `t + 1 = stepOrStay (runCfg t)`
recursion, which advances at the end, not the front. -/
lemma stepsTo_succ_inv {α : Type*} (f : α → Option α) {a c : α} {t : ℕ}
    (h : StepsTo f a c (t + 1)) : ∃ b, StepsTo f a b t ∧ f b = some c := by
  simp only [StepsTo, Function.iterate_succ_apply'] at h
  rcases hx : (fun s : Option α => s.bind f)^[t] (some a) with _ | b
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only [Option.bind_some] at h
    exact ⟨b, hx, h⟩

/-- `MachineOutputsInTime`'s witness, reached in exactly `t` clean steps, is
what `runCfg` reaches at time `t` too: `step` is a function, so the `t`-step
trace is unique. -/
lemma runCfg_eq_of_stepsTo [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {input : List Γ} {c : Cfg Γ Λ} {t : ℕ}
    (h : StepsTo (step M) (init input) c t) : runCfg M input t = c := by
  induction t generalizing c with
  | zero =>
    have heq : init input = c := by
      simp only [StepsTo, Function.iterate_zero, id_eq] at h
      exact Option.some.inj h
    rw [runCfg_zero]; exact heq
  | succ t ih =>
    obtain ⟨b, hb, hstep⟩ := stepsTo_succ_inv (step M) h
    have hbeq : runCfg M input t = b := ih hb
    show stepOrStay M (runCfg M input t) = c
    rw [hbeq]
    simp only [stepOrStay, hstep]

/-- Either `runCfg` at time `t` is reached in exactly `t` genuine steps, or the
machine already halted (and hence stopped changing) strictly before `t`. -/
lemma stepsTo_runCfg_or_halted_before [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (input : List Γ) (t : ℕ) :
    StepsTo (step M) (init input) (runCfg M input t) t ∨
      ∃ t' < t, step M (runCfg M input t') = none := by
  induction t with
  | zero => exact Or.inl (stepsTo_zero _ _)
  | succ t ih =>
    rcases ih with hclean | ⟨t', ht', hhalt⟩
    · rcases hstep : step M (runCfg M input t) with _ | c'
      · exact Or.inr ⟨t, lt_add_one t, hstep⟩
      · refine Or.inl ?_
        have hc : runCfg M input (t + 1) = c' := by
          show stepOrStay M (runCfg M input t) = c'
          simp [stepOrStay, hstep]
        rw [hc]
        exact stepsTo_succ (step M) hclean hstep
    · exact Or.inr ⟨t', ht'.trans (lt_add_one t), hhalt⟩

/-- Once halted, `runCfg` stays at the same configuration forever after. -/
lemma runCfg_stays_of_halted [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {input : List Γ} {t' : ℕ} (hhalt : step M (runCfg M input t') = none) :
    ∀ t, t' ≤ t → runCfg M input t = runCfg M input t' := by
  intro t ht
  induction t with
  | zero => rw [Nat.le_zero.mp ht]
  | succ t ih =>
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [← heq]
    · have hprev := ih (by omega)
      show stepOrStay M (runCfg M input t) = runCfg M input t'
      rw [hprev]; simp [stepOrStay, hhalt]

/-- Assemble the halted `Cfg` that `MachineOutputsInTime` promises into a
statement about `runCfg` at the full budget `T`: the converse of
`machineOutputsInTime_of_halted`, needed for `.mpr`. -/
lemma runCfg_of_machineOutputsInTime [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {input output : List Γ} {T : ℕ} (hRun : MachineOutputsInTime M input output T) :
    (runCfg M input T).Tape = Tape.mk₁ output ∧ step M (runCfg M input T) = none := by
  obtain ⟨q, t, htT, hsteps, hhalt⟩ := hRun
  have heq : runCfg M input t = ⟨q, Tape.mk₁ output⟩ := runCfg_eq_of_stepsTo hsteps
  have hhalt' : step M (runCfg M input t) = none := by rw [heq]; exact hhalt
  have hstay : runCfg M input T = runCfg M input t :=
    runCfg_stays_of_halted hhalt' T htT
  rw [hstay, heq]
  exact ⟨rfl, hhalt⟩

/-- Assemble `MachineOutputsInTime` from a halted configuration at time `T`
whose tape has the shape `Tape.mk₁ output`. -/
lemma machineOutputsInTime_of_halted [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ}
    {input output : List Γ} {T : ℕ}
    (hshape : (runCfg M input T).Tape = Tape.mk₁ output)
    (hhalt : step M (runCfg M input T) = none) :
    MachineOutputsInTime M input output T := by
  classical
  have hex : ∃ k, step M (runCfg M input k) = none := ⟨T, hhalt⟩
  set t₀ := Nat.find hex with ht₀def
  have ht₀halt : step M (runCfg M input t₀) = none := Nat.find_spec hex
  have ht₀le : t₀ ≤ T := Nat.find_le hhalt
  have hstay : runCfg M input T = runCfg M input t₀ :=
    runCfg_stays_of_halted ht₀halt T ht₀le
  have hCfgEq : (⟨(runCfg M input T).q, Tape.mk₁ output⟩ : Cfg Γ Λ) =
      runCfg M input t₀ := by rw [← hshape, hstay]
  rcases stepsTo_runCfg_or_halted_before M input t₀ with hclean | ⟨t'', ht'', hhalt''⟩
  · refine ⟨(runCfg M input T).q, t₀, ht₀le, ?_, ?_⟩
    · rw [hCfgEq]; exact hclean
    · rw [hCfgEq, ← hstay]; exact hhalt
  · exact absurd hhalt'' (Nat.find_min hex ht'')

/-- The real run's halting snapshot witnesses the accept clauses: `runAssign`
satisfies `acceptClauses` whenever the machine actually outputs `output`
within `T` steps. This is the key step of `.mpr`: it needs no absolute head
position, only that `output`'s content is read relative to wherever the head
in fact stops (`acceptClauses`'s `implyPos` family), plus the halt-state
clause shared with the other acceptance conditions. -/
lemma acceptClauses_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T : ℕ}
    (hS : Supports M ↑S) (hRun : MachineOutputsInTime M input output T) :
    ∀ c ∈ acceptClauses M S output (windowSize input.length output.length T) T,
      c.Satisfied (runAssign M S input output T) := by
  set τ := runAssign M S input output T with hτdef
  set W := windowSize input.length output.length T with hWdef
  obtain ⟨hshape, hhalt⟩ := runCfg_of_machineOutputsInTime hRun
  intro c hc
  simp only [acceptClauses, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_singleton] at hc
  rcases hc with ⟨pHead, _, p, hpmem, rfl⟩ | rfl
  · have hpW : p < W := List.mem_range.mp hpmem
    refine satisfied_implyPos (fun hhd => ?_)
    have hpeq : runHead M input T = idxToPos T pHead := (runAssign_head_inv hhd).2
    refine runAssign_cell (le_refl T) hpW ?_
    show absNth (runCfg M input T) (runHead M input T) (idxToPos T p) =
      initSymbol output ((p : ℤ) - (pHead : ℤ))
    simp only [absNth, hshape, tape_mk₁_nth]
    congr 1
    rw [hpeq]
    simp only [idxToPos]
    ring
  · have hheadeq : (runCfg M input T).Tape.head = initSymbol output 0 := by
      rw [hshape, ← Tape.nth_zero, tape_mk₁_nth]
    have hMhalt : M (runCfg M input T).q (initSymbol output 0) = none := by
      rw [← hheadeq]; exact step_eq_none_iff.mp hhalt
    have hqinS : (runCfg M input T).q ∈ S := runCfg_state_mem hS input T
    have hqinHalt : (runCfg M input T).q ∈ haltStates M S (initSymbol output 0) := by
      simp only [haltStates, List.mem_filter, Finset.mem_toList]
      exact ⟨hqinS, by rw [hMhalt]⟩
    exact satisfied_atLeastOne
      (List.mem_map.mpr ⟨(runCfg M input T).q, hqinHalt, rfl⟩)
      (runAssign_state (le_refl T) hqinS)

end NPComplete.CookLevin

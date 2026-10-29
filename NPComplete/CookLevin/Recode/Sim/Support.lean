module

public import NPComplete.CookLevin.Recode.Sim.CleanMachine

/-!
# Finite simulator support

The simulator's counter and vector phases must stay within an explicit finite
state support to form a finite-machine computation. This module describes that
support and proves membership for the phase states used by the simulation.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

/-- The terminal state, together with all phases whose simulated control state lies in `S`. -/
noncomputable def simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ] (S : Finset Λ) :
    Finset (SimPhase n Λ) :=
  {SimPhase.done} ∪
    S.biUnion fun q =>
      {SimPhase.ready q} ∪
        (Finset.univ : Finset (Fin n.succ)).biUnion (fun i =>
          (Finset.univ : Finset (List.Vector Bool i.val)).image
            (SimPhase.read q i)) ∪
        (Finset.univ : Finset (Fin n.succ)).biUnion (fun left =>
          (Finset.univ : Finset (List.Vector Bool n)).image
            (SimPhase.rewind q left)) ∪
         (Finset.univ : Finset (Fin n.succ)).biUnion (fun i =>
         (Finset.univ : Finset (List.Vector Bool n)).image
             (SimPhase.write q i)) ∪
        (Finset.univ : Finset (Fin n.succ)).biUnion (fun i =>
         (Finset.univ : Finset (List.Vector Bool n)).image
            (SimPhase.writeMove q i)) ∪
          (Finset.univ : Finset (Fin n.succ)).image (SimPhase.writeBack q) ∪
         ({Dir.left, Dir.right} : Finset Dir).biUnion (fun d =>
          (Finset.univ : Finset (Fin n.succ)).image
            (SimPhase.move q d))

lemma mem_simSupport_ready {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) :
    SimPhase.ready (n := n) q ∈ simSupport S := by
  simp [simSupport, hq]

lemma mem_simSupport_done {n : ℕ} {Λ : Type} [DecidableEq Λ]
    (S : Finset Λ) : SimPhase.done (n := n) ∈ simSupport S := by
  simp [simSupport]

lemma mem_simSupport_read {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (i : Fin n.succ)
    (acc : List.Vector Bool i.val) :
    SimPhase.read q i acc ∈ simSupport S := by
  simp [simSupport, hq]

lemma mem_simSupport_rewind {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (left : Fin n.succ)
    (bits : List.Vector Bool n) :
    SimPhase.rewind q left bits ∈ simSupport S := by
  simp [simSupport, hq]

lemma mem_simSupport_write {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (i : Fin n.succ)
    (bits : List.Vector Bool n) :
    SimPhase.write q i bits ∈ simSupport S := by
  simp [simSupport, hq]

lemma mem_simSupport_writeMove {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (i : Fin n.succ)
    (bits : List.Vector Bool n) :
    SimPhase.writeMove q i bits ∈ simSupport S := by
  simp [simSupport, hq]

lemma mem_simSupport_writeBack {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (left : Fin n.succ) :
    SimPhase.writeBack q left ∈ simSupport S := by
  simp [simSupport, hq]

lemma writeBack_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {left : Fin n.succ}
    (h : SimPhase.writeBack q left ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  exact h

lemma mem_simSupport_move {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (hq : q ∈ S) (d : Dir) (left : Fin n.succ)
    (hd : d = .left ∨ d = .right) :
    SimPhase.move q d left ∈ simSupport S := by
  simp [simSupport]
  refine ⟨q, hq, ?_⟩
  rcases hd with rfl | rfl <;> simp

lemma ready_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} (h : SimPhase.ready (n := n) q ∈ simSupport S) :
    q ∈ S := by
  simp [simSupport] at h
  exact h

lemma read_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {i : Fin n.succ} {acc : List.Vector Bool i.val}
    (h : SimPhase.read q i acc ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  exact h

lemma rewind_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {left : Fin n.succ} {bits : List.Vector Bool n}
    (h : SimPhase.rewind q left bits ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  exact h

lemma write_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {i : Fin n.succ} {bits : List.Vector Bool n}
    (h : SimPhase.write q i bits ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  exact h

lemma writeMove_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {i : Fin n.succ} {bits : List.Vector Bool n}
    (h : SimPhase.writeMove q i bits ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  exact h

lemma move_mem_simSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {q : Λ} {d : Dir} {left : Fin n.succ}
    (h : SimPhase.move q d left ∈ simSupport S) : q ∈ S := by
  simp [simSupport] at h
  obtain ⟨q', hq', h'⟩ := h
  rcases h' with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hq'
  · exact hq'

lemma simMachine_supports_ready {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ}
    {S : Finset Λ} {q0 : Λ} {a : Option Bool} {q' : SimPhase e.n Λ}
    {s : TM0.Stmt (Option Bool)} (hq0 : q0 ∈ S)
    (hstep : simMachine M e (.ready q0) a = some (q', s)) :
    q' ∈ simSupport S := by
  simp [simMachine] at hstep
  rcases hstep with ⟨rfl, rfl⟩
  exact mem_simSupport_read hq0 _ _

lemma simMachine_supports {Γ Λ : Type} [Inhabited Γ] [Finite Γ] [Inhabited Λ]
    [DecidableEq Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ) (S : Finset Λ)
    (hS : TM0.Supports M ↑S) :
    TM0.Supports (simMachine M e) ↑(simSupport (n := e.n) S) := by
  refine ⟨mem_simSupport_ready hS.1, ?_⟩
  intro q a q' s hstep hq
  cases q with
  | ready q0 =>
    exact simMachine_supports_ready (ready_mem_simSupport hq) hstep
  | read q0 i acc =>
    have hq0 : q0 ∈ S := read_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep <;> rcases hstep with ⟨rfl, rfl⟩
    · exact mem_simSupport_read hq0 _ _
    · exact mem_simSupport_rewind hq0 _ _
    · exact mem_simSupport_done S
  | rewind q0 left bits =>
    have hq0 : q0 ∈ S := rewind_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep with hlt
    · rcases hstep with ⟨rfl, rfl⟩
      exact mem_simSupport_rewind hq0 _ _
    · revert hstep
      cases hM : M q0 (e.dec bits) with
      | none =>
        intro hstep
        simp at hstep
        rcases hstep with ⟨rfl, rfl⟩
        exact mem_simSupport_done S
      | some qs =>
        intro hstep
        rcases qs with ⟨q1, stmt⟩
        have hq1 : q1 ∈ S := hS.2 hM hq0
        cases stmt
        · simp at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact mem_simSupport_move hq1 _ _ (by cases ‹Dir› <;> simp)
        · simp at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact mem_simSupport_write hq1 _ _
  | write q0 i bits =>
    have hq0 : q0 ∈ S := write_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep <;> rcases hstep with ⟨rfl, rfl⟩
    · exact mem_simSupport_writeMove hq0 _ _
    · exact mem_simSupport_ready hq0
  | writeMove q0 i bits =>
    have hq0 : q0 ∈ S := writeMove_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep <;> rcases hstep with ⟨rfl, rfl⟩
    · exact mem_simSupport_write hq0 _ _
    · exact mem_simSupport_writeBack hq0 _
    · exact mem_simSupport_ready hq0
  | writeBack q0 left =>
    have hq0 : q0 ∈ S := writeBack_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep <;> rcases hstep with ⟨rfl, rfl⟩
    · exact mem_simSupport_writeBack hq0 _
    · exact mem_simSupport_ready hq0
  | move q0 d left =>
    have hq0 : q0 ∈ S := move_mem_simSupport hq
    simp [simMachine] at hstep
    split_ifs at hstep <;> rcases hstep with ⟨rfl, rfl⟩
    · exact mem_simSupport_move hq0 _ _ (by cases d <;> simp)
    · exact mem_simSupport_ready hq0
  | done =>
    simp [simMachine] at hstep

noncomputable def simCleanSupport {n : ℕ} {Λ : Type} [DecidableEq Λ]
    (S : Finset Λ) : Finset (SimCleanPhase n Λ) :=
  {SimCleanPhase.rewindLeft, SimCleanPhase.eraseLeft,
      SimCleanPhase.eraseLeftMove, SimCleanPhase.returnMarker,
      SimCleanPhase.final} ∪
    ((simSupport S).image SimCleanPhase.run ∪
    (simSupport S).biUnion (fun p =>
      ({SimCleanPhase.markMove p Dir.left, SimCleanPhase.markMove p Dir.right} :
        Finset (SimCleanPhase n Λ))))

lemma mem_simCleanSupport_run {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {p : SimPhase n Λ} (hp : p ∈ simSupport S) :
    SimCleanPhase.run p ∈ simCleanSupport (n := n) S := by
  simp [simCleanSupport, hp]

lemma mem_simCleanSupport_markMove {n : ℕ} {Λ : Type} [DecidableEq Λ]
    {S : Finset Λ} {p : SimPhase n Λ} (hp : p ∈ simSupport S) (d : Dir) :
    SimCleanPhase.markMove p d ∈ simCleanSupport (n := n) S := by
  cases d <;> simp [simCleanSupport, hp]

lemma mem_simCleanSupport_returnMarker {n : ℕ} {Λ : Type} [DecidableEq Λ]
    (S : Finset Λ) :
    SimCleanPhase.returnMarker (n := n) ∈ simCleanSupport S := by
  simp [simCleanSupport]

/-- A `run` phase stays in the support: the source step lands in `simSupport`. -/
lemma simCleanMachine_supports_run_some {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ}
    {S : Finset Λ} {p p' : SimPhase e.n Λ}
    {a : Option Bool} {stmt : TM0.Stmt (Option Bool)}
    {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hp' : p' ∈ simSupport S) (hm : simMachine M e p a = some (p', stmt))
    (hstep : simCleanMachine M e (.run p) a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  cases stmt with
  | move d =>
    cases p <;> simp [simCleanMachine, hm] at hstep <;>
      rcases hstep with ⟨rfl, rfl⟩
    case read => exact mem_simCleanSupport_markMove hp' d
    all_goals exact mem_simCleanSupport_run hp'
  | write x =>
    simp [simCleanMachine, hm] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact mem_simCleanSupport_run hp'

/-- Support closure of the wrapped source step, from the support of the source machine. -/
lemma simCleanMachine_supports_run {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ}
    {S : Finset Λ} (hS : TM0.Supports M ↑S)
    {p : SimPhase e.n Λ} {a : Option Bool}
    {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hq : SimCleanPhase.run p ∈ simCleanSupport (n := e.n) S)
    (hstep : simCleanMachine M e (.run p) a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  cases hm : simMachine M e p a with
  | none =>
    simp [simCleanMachine, hm] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp [simCleanSupport]
  | some ps =>
    have hp : p ∈ simSupport S := by
      by_contra hp
      exact (by simp [simCleanSupport, hp] :
        SimCleanPhase.run p ∉ simCleanSupport (n := e.n) S) hq
    exact simCleanMachine_supports_run_some
      ((simMachine_supports M e S hS).2 hm hp) hm hstep

/-- A `markMove` phase returns to `run`, and its support membership gives the inner phase. -/
lemma simCleanMachine_supports_markMove {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ}
    {S : Finset Λ} {p : SimPhase e.n Λ} {d : Dir}
    {a : Option Bool} {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hq : SimCleanPhase.markMove p d ∈ simCleanSupport (n := e.n) S)
    (hstep : simCleanMachine M e (.markMove p d) a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  simp [simCleanMachine] at hstep
  rcases hstep with ⟨rfl, rfl⟩
  have hp : p ∈ simSupport S := by
    by_contra hp
    exact (by cases d <;> simp [simCleanSupport, hp] :
      SimCleanPhase.markMove p d ∉ simCleanSupport (n := e.n) S) hq
  exact mem_simCleanSupport_run hp

/-- Support closure of the `rewindLeft` cleanup phase. -/
lemma simCleanMachine_supports_rewindLeft {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ} (S : Finset Λ)
    {a : Option Bool} {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hstep : simCleanMachine M e .rewindLeft a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  simp only [simCleanMachine] at hstep
  by_cases hc : a.isSome
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp [simCleanSupport]
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact mem_simCleanSupport_returnMarker S

/-- Support closure of the `eraseLeft` cleanup phase. -/
lemma simCleanMachine_supports_eraseLeft {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ} (S : Finset Λ)
    {a : Option Bool} {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hstep : simCleanMachine M e .eraseLeft a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  simp only [simCleanMachine] at hstep
  by_cases hc : a.isSome
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp [simCleanSupport]
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact mem_simCleanSupport_returnMarker S

/-- Support closure of the `returnMarker` cleanup phase. -/
lemma simCleanMachine_supports_returnMarker {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] {M : TM0.Machine Γ Λ} {e : BlockEnc Γ}
    (S : Finset Λ)
    {a : Option Bool} {q' : SimCleanPhase e.n Λ} {s : TM0.Stmt (Option Bool)}
    (hstep : simCleanMachine M e .returnMarker a = some (q', s)) :
    q' ∈ simCleanSupport (n := e.n) S := by
  simp [simCleanMachine] at hstep
  by_cases hc : a.isSome
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp [simCleanSupport]
  · simp [hc] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact mem_simCleanSupport_returnMarker S

lemma simCleanMachine_supports {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (S : Finset Λ) (hS : TM0.Supports M ↑S) :
    TM0.Supports (simCleanMachine M e)
      ↑(simCleanSupport (n := e.n) S) := by
  refine ⟨mem_simCleanSupport_run (mem_simSupport_ready hS.1), ?_⟩
  intro q a q' s hstep hq
  cases q with
  | run p => exact simCleanMachine_supports_run hS hq hstep
  | markMove p d => exact simCleanMachine_supports_markMove hq hstep
  | returnMarker => exact simCleanMachine_supports_returnMarker S hstep
  | rewindLeft => exact simCleanMachine_supports_rewindLeft S hstep
  | eraseLeft => exact simCleanMachine_supports_eraseLeft S hstep
  | eraseLeftMove =>
    simp only [simCleanMachine] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    simp [simCleanSupport]
  | final => simp [simCleanMachine] at hstep

end NPComplete.CookLevin

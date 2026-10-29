module

public import NPComplete.CookLevin.Tableau.NextIndex

/-!
# Transition clause witnesses

Concrete machine steps must satisfy each local transition clause, including the distinct move,
write, and stutter cases. This module constructs those witnesses from a real run, separating
run-to-clause reasoning from the converse SAT decoding.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## The real run witnesses `transOne`'s clauses -/

/-- Simultaneous true state, head, and cell selectors identify the real run row. -/
lemma transOne_of_run_real_antecedents [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input : List Γ}
    {T t p : ℕ} {q : Λ} {a : Γ} {τ : Literal.Assignment}
    (hstateInv : τ (stateVar t (stateIdx S q)) = true →
      (runCfg M input t).q = q)
    (hheadInv : τ (headVar t p) = true →
      runHead M input t = idxToPos T p)
    (hcellInv : τ (cellVar t p (letterIdx a)) = true →
      absNth (runCfg M input t) (runHead M input t) (idxToPos T p) = a)
    (hst : τ (stateVar t (stateIdx S q)) = true)
    (hhd : τ (headVar t p) = true)
    (hcl : τ (cellVar t p (letterIdx a)) = true) :
    q = (runCfg M input t).q ∧
      p = posToIdx T (runHead M input t) ∧
      a = (runCfg M input t).Tape.head := by
  have hheadcontent : (runCfg M input t).Tape.head = a := by
    have hcopy := hcellInv hcl
    rw [hheadInv hhd] at hcopy
    simpa [absNth, Tape.nth_zero] using hcopy
  have hpreal : p = posToIdx T (runHead M input t) := by
    rw [hheadInv hhd]
    exact (posToIdx_idxToPos T p).symm
  exact ⟨(hstateInv hst).symm, hpreal, hheadcontent.symm⟩

/-- The run's next head index agrees with the encoded move at every wide enough window. -/
lemma nextIdx_of_run_move_successor [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (input output : List Γ)
    {T t W : ℕ} {q' : Λ} (d : Dir) (ht : t < T)
    (hW : windowSize input.length output.length T ≤ W)
    (hM : M (runCfg M input t).q (runCfg M input t).Tape.head =
      some (q', Stmt.move d)) :
    nextIdx W (posToIdx T (runHead M input t)) d =
      some (posToIdx T (runHead M input (t + 1))) := by
  have hb0 : -(T : ℤ) ≤ runHead M input t := runHead_abs_le_of_le M input (by omega)
  have hb1 : -(T : ℤ) ≤ runHead M input (t + 1) :=
    runHead_abs_le_of_le M input (by omega)
  have hpW' : posToIdx T (runHead M input (t + 1)) < W :=
    lt_of_lt_of_le (runHead_posToIdx_lt_window M input (by omega)) hW
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  rcases d with _ | _
  · have hd1 : runHead M input (t + 1) = runHead M input t - 1 := by
      rw [hheadc, stepHead, hM]
      simp only [dirDelta]
      ring
    have hlo : -(T : ℤ) ≤ runHead M input t - 1 := by
      rw [← hd1]
      exact hb1
    rw [nextIdx_left_eq hlo, hd1]
  · have hd1 : runHead M input (t + 1) = runHead M input t + 1 := by
      rw [hheadc, stepHead, hM]
      simp only [dirDelta]
    have hhi : posToIdx T (runHead M input t + 1) < W := by
      rw [← hd1]
      exact hpW'
    rw [nextIdx_right_eq hb0 hhi, hd1]

/-- A halted run preserves its next row in any assignment that records real rows. -/
lemma transOne_of_run_none_successor [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t W p : ℕ} {q : Λ} {a : Γ} {τ : Literal.Assignment}
    (hS : Supports M ↑S) (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = none) (ht : t < T)
    (hq : q = (runCfg M input t).q)
    (hp : p = posToIdx T (runHead M input t))
    (ha : a = (runCfg M input t).Tape.head)
    (stateAt : ∀ {s : ℕ}, s ≤ T → (runCfg M input s).q ∈ S →
      τ (stateVar s (stateIdx S (runCfg M input s).q)) = true)
    (headAt : ∀ {s r : ℕ}, s ≤ T → r < W →
      runHead M input s = idxToPos T r → τ (headVar s r) = true)
    (cellAt : ∀ {s r : ℕ} {b : Γ}, s ≤ T → r < W →
      absNth (runCfg M input s) (runHead M input s) (idxToPos T r) = b →
        τ (cellVar s r (letterIdx b)) = true) :
    τ (stateVar (t + 1) (stateIdx S q)) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx a)) = true := by
  have hMrun : M (runCfg M input t).q (runCfg M input t).Tape.head = none := by
    rw [← hq, ← ha]
    exact hM
  have hstepnone : step M (runCfg M input t) = none := by simp [step, hMrun]
  have hstay : runCfg M input (t + 1) = runCfg M input t := by
    show stepOrStay M (runCfg M input t) = runCfg M input t
    simp [stepOrStay, hstepnone]
  have hheadstay : runHead M input (t + 1) = runHead M input t := by
    show stepHead M (runCfg M input t) (runHead M input t) = runHead M input t
    simp [stepHead, hMrun]
  have hb0 : -(T : ℤ) ≤ runHead M input t := runHead_abs_le_of_le M input (by omega)
  have hpW : p < W := by
    rw [hp]
    exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input (by omega)) hW
  have hheadreal : runHead M input t = idxToPos T p := by
    rw [hp]
    exact (idxToPos_posToIdx hb0).symm
  refine ⟨?_, ?_, ?_⟩
  · have hq1 : (runCfg M input (t + 1)).q = q := by
      rw [hstay]
      exact hq.symm
    rw [← hq1]
    exact stateAt (by omega) (runCfg_state_mem hS input (t + 1))
  · exact headAt (by omega) hpW (hheadstay.trans hheadreal)
  · apply cellAt (by omega) hpW
    rw [hp, idxToPos_posToIdx hb0, hstay, hheadstay]
    simpa [absNth] using ha.symm

/-- A writing run updates the state and scanned symbol while keeping its head index. -/
lemma transOne_of_run_write_successor [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t W p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {b : Γ}
    {τ : Literal.Assignment}
    (hS : Supports M ↑S) (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = some (q', Stmt.write b)) (ht : t < T)
    (hq : q = (runCfg M input t).q)
    (hp : p = posToIdx T (runHead M input t))
    (ha : a = (runCfg M input t).Tape.head)
    (stateAt : ∀ {s : ℕ}, s ≤ T → (runCfg M input s).q ∈ S →
      τ (stateVar s (stateIdx S (runCfg M input s).q)) = true)
    (headAt : ∀ {s r : ℕ}, s ≤ T → r < W →
      runHead M input s = idxToPos T r → τ (headVar s r) = true)
    (cellAt : ∀ {s r : ℕ} {x : Γ}, s ≤ T → r < W →
      absNth (runCfg M input s) (runHead M input s) (idxToPos T r) = x →
        τ (cellVar s r (letterIdx x)) = true) :
    τ (stateVar (t + 1) (stateIdx S q')) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx b)) = true := by
  have hMrun : M (runCfg M input t).q (runCfg M input t).Tape.head =
      some (q', Stmt.write b) := by
    rw [← hq, ← ha]
    exact hM
  have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  have hheadstay : runHead M input (t + 1) = runHead M input t := by
    rw [hheadc]
    simp [stepHead, hMrun]
  have hb0 : -(T : ℤ) ≤ runHead M input t := runHead_abs_le_of_le M input (by omega)
  have hpW : p < W := by
    rw [hp]
    exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input (by omega)) hW
  have hheadreal : runHead M input t = idxToPos T p := by
    rw [hp]
    exact (idxToPos_posToIdx hb0).symm
  have hq1 : (runCfg M input (t + 1)).q = q' := by
    rw [hstepc]
    simp [stepOrStay, step, hMrun]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hq1]
    exact stateAt (by omega) (runCfg_state_mem hS input (t + 1))
  · exact headAt (by omega) hpW (hheadstay.trans hheadreal)
  · apply cellAt (by omega) hpW
    rw [hp, idxToPos_posToIdx hb0, hstepc, hheadc]
    exact absNth_stepOrStay_write hMrun

/-- A moving run advances the encoded head and preserves the old cell. -/
lemma transOne_of_run_move_successor [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t W p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {d : Dir} {p' : ℕ}
    {τ : Literal.Assignment}
    (hS : Supports M ↑S) (hW : windowSize input.length output.length T ≤ W)
    (hM : M q a = some (q', Stmt.move d)) (ht : t < T)
    (hq : q = (runCfg M input t).q)
    (hp : p = posToIdx T (runHead M input t))
    (ha : a = (runCfg M input t).Tape.head)
    (hnext : nextIdx W p d = some p')
    (stateAt : ∀ {s : ℕ}, s ≤ T → (runCfg M input s).q ∈ S →
      τ (stateVar s (stateIdx S (runCfg M input s).q)) = true)
    (headAt : ∀ {s r : ℕ}, s ≤ T → r < W →
      runHead M input s = idxToPos T r → τ (headVar s r) = true)
    (cellAt : ∀ {s r : ℕ} {x : Γ}, s ≤ T → r < W →
      absNth (runCfg M input s) (runHead M input s) (idxToPos T r) = x →
        τ (cellVar s r (letterIdx x)) = true) :
    τ (stateVar (t + 1) (stateIdx S q')) = true ∧
      τ (headVar (t + 1) p') = true ∧
      τ (cellVar (t + 1) p (letterIdx a)) = true := by
  have hMrun : M (runCfg M input t).q (runCfg M input t).Tape.head =
      some (q', Stmt.move d) := by
    rw [← hq, ← ha]
    exact hM
  have hstepc : runCfg M input (t + 1) = stepOrStay M (runCfg M input t) := rfl
  have hheadc : runHead M input (t + 1) =
      stepHead M (runCfg M input t) (runHead M input t) := rfl
  have hb0 : -(T : ℤ) ≤ runHead M input t := runHead_abs_le_of_le M input (by omega)
  have hb1 : -(T : ℤ) ≤ runHead M input (t + 1) :=
    runHead_abs_le_of_le M input (by omega)
  have hpW : p < W := by
    rw [hp]
    exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input (by omega)) hW
  have hnext' := nextIdx_of_run_move_successor M input output d ht hW hMrun
  have hp'eq : p' = posToIdx T (runHead M input (t + 1)) := by
    rw [← hp, hnext] at hnext'
    exact Option.some.inj hnext'
  have hpW' : p' < W := by
    rw [hp'eq]
    exact lt_of_lt_of_le (runHead_posToIdx_lt_window M input (by omega)) hW
  have hq1 : (runCfg M input (t + 1)).q = q' := by
    rw [hstepc]
    simp [stepOrStay, step, hMrun]
  have hnw : ∀ q'' x, M (runCfg M input t).q (runCfg M input t).Tape.head ≠
      some (q'', Stmt.write x) := by
    intro q'' x hcontra
    rw [hMrun] at hcontra
    cases hcontra
  have hheadreal : runHead M input (t + 1) = idxToPos T p' := by
    rw [hp'eq]
    exact (idxToPos_posToIdx hb1).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hq1]
    exact stateAt (by omega) (runCfg_state_mem hS input (t + 1))
  · exact headAt (by omega) hpW' hheadreal
  · apply cellAt (by omega) hpW
    rw [hp, idxToPos_posToIdx hb0, hstepc, hheadc,
      absNth_stepOrStay_not_write hnw]
    simpa [absNth] using ha.symm

/-- Constructive analogue of `sat_run_step_move`: when `.move d` is the real
transition at time `t`, `runAssign` satisfies `transOne`'s clauses for *every*
`(p, q, a)` triple, including the ones that don't describe the real run
(handled vacuously) and the window-edge `forbid3` case (shown impossible). -/
lemma transOne_of_run_move [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {d : Dir} (hS : Supports M ↑S)
    (hM : M q a = some (q', Stmt.move d)) (ht : t < T) (hq'S : q' ∈ S) :
    ∀ c ∈ transOne M S (windowSize input.length output.length T) t p q a,
      c.Satisfied (runAssign M S input output T) := by
  set τ := runAssign M S input output T with hτdef
  set W := windowSize input.length output.length T with hWdef
  rcases hnextval : nextIdx W p d with _ | p'
  · -- forbid3
    intro c hc
    simp only [transOne, hM, ite_eq_left hq'S, hnextval, List.mem_singleton] at hc
    subst hc
    refine satisfied_forbid3 (fun _ hhd => ?_)
    obtain ⟨p'', hp'eq, _⟩ := nextIdx_move_isSome_of_real M input
      (inputLen := input.length) (outputLen := output.length) d ht
      (runAssign_head_inv hhd).2
    rw [hnextval] at hp'eq
    exact absurd hp'eq (by simp)
  · intro c hc
    simp only [transOne, hM, ite_eq_left hq'S, hnextval, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
        τ (cellVar t p (letterIdx a)) = true →
        τ (stateVar (t + 1) (stateIdx S q')) = true ∧
        τ (headVar (t + 1) p') = true ∧
        τ (cellVar (t + 1) p (letterIdx a)) = true := by
      intro hst hhd hcl
      obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
        (τ := τ)
        (fun h => (runAssign_state_inv h).2.2)
        (fun h => (runAssign_head_inv h).2)
        (fun h => (runAssign_cell_inv h).2)
        hst hhd hcl
      exact transOne_of_run_move_successor (input := input) (output := output)
        (W := W) hS (by rw [hWdef]) hM ht
        hqreal hpreal hareal hnextval
        (fun hu hq => runAssign_state hu hq)
        (fun hu hp hhead => runAssign_head hu hp hhead)
        (fun hu hp hcell => runAssign_cell hu hp hcell)
    rcases hc with rfl | rfl | rfl
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
    · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- Constructive analogue of the halted branch of `sat_run_step`: when `M`
halts at time `t`, `runAssign` satisfies `transOne`'s (stuttering) clauses,
for every `(p, q, a)` triple, not only the real one. -/
lemma transOne_of_run_none [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} {q : Λ} {a : Γ} (hS : Supports M ↑S)
    (hM : M q a = none) (ht : t < T) :
    ∀ c ∈ transOne M S (windowSize input.length output.length T) t p q a,
      c.Satisfied (runAssign M S input output T) := by
  set τ := runAssign M S input output T with hτdef
  set W := windowSize input.length output.length T with hWdef
  intro c hc
  simp only [transOne, hM, List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
      τ (cellVar t p (letterIdx a)) = true →
      τ (stateVar (t + 1) (stateIdx S q)) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx a)) = true := by
    intro hst hhd hcl
    obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
      (τ := τ)
      (fun h => (runAssign_state_inv h).2.2)
      (fun h => (runAssign_head_inv h).2)
      (fun h => (runAssign_cell_inv h).2)
      hst hhd hcl
    exact transOne_of_run_none_successor (input := input) (output := output)
      (W := W) hS (by rw [hWdef]) hM ht hqreal hpreal hareal
      (fun hu hq => runAssign_state hu hq)
      (fun hu hp hhead => runAssign_head hu hp hhead)
      (fun hu hp hcell => runAssign_cell hu hp hcell)
  rcases hc with rfl | rfl | rfl
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- Constructive analogue of the `.write b` branch of `sat_run_step`. -/
lemma transOne_of_run_write [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} {q : Λ} {a : Γ} {q' : Λ} {b : Γ} (hS : Supports M ↑S)
    (hM : M q a = some (q', Stmt.write b)) (ht : t < T) (hq'S : q' ∈ S) :
    ∀ c ∈ transOne M S (windowSize input.length output.length T) t p q a,
      c.Satisfied (runAssign M S input output T) := by
  set τ := runAssign M S input output T with hτdef
  set W := windowSize input.length output.length T with hWdef
  intro c hc
  simp only [transOne, hM, ite_eq_left hq'S, List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcombined : τ (stateVar t (stateIdx S q)) = true → τ (headVar t p) = true →
      τ (cellVar t p (letterIdx a)) = true →
      τ (stateVar (t + 1) (stateIdx S q')) = true ∧
      τ (headVar (t + 1) p) = true ∧
      τ (cellVar (t + 1) p (letterIdx b)) = true := by
    intro hst hhd hcl
    obtain ⟨hqreal, hpreal, hareal⟩ := transOne_of_run_real_antecedents
      (τ := τ)
      (fun h => (runAssign_state_inv h).2.2)
      (fun h => (runAssign_head_inv h).2)
      (fun h => (runAssign_cell_inv h).2)
      hst hhd hcl
    exact transOne_of_run_write_successor (input := input) (output := output)
      (W := W) hS (by rw [hWdef]) hM ht hqreal hpreal hareal
      (fun hu hq => runAssign_state hu hq)
      (fun hu hp hhead => runAssign_head hu hp hhead)
      (fun hu hp hcell => runAssign_cell hu hp hcell)
  rcases hc with rfl | rfl | rfl
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.1)
  · exact satisfied_imply3 (fun hst hhd hcl => (hcombined hst hhd hcl).2.2)

/-- The real run witnesses every `transOne` clause, for every `(t,p,q,a)`
combination — not just the one describing the real run at time `t`, whose
triple of antecedents is the only one all three of which can be true. -/
lemma transOne_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T t p : ℕ} {q : Λ} {a : Γ} (hS : Supports M ↑S) (hq : q ∈ S) (ht : t < T) :
    ∀ c ∈ transOne M S (windowSize input.length output.length T) t p q a,
      c.Satisfied (runAssign M S input output T) := by
  rcases hM : M q a with _ | ⟨q', stmt⟩
  · exact transOne_of_run_none hS hM ht
  · have hq'S : q' ∈ S := hS.2 (Option.mem_def.mpr hM) hq
    rcases stmt with d | b
    · exact transOne_of_run_move hS hM ht hq'S
    · exact transOne_of_run_write hS hM ht hq'S

/-- The real run's state / head / cell snapshot witnesses its own transition
clauses: `runAssign` satisfies `transClauses`. -/
lemma transClauses_of_run [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ]
    [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ}
    {T : ℕ} (hS : Supports M ↑S) :
    ∀ c ∈ transClauses M S (windowSize input.length output.length T) T,
      c.Satisfied (runAssign M S input output T) := by
  intro c hc
  simp only [transClauses, List.mem_flatMap] at hc
  obtain ⟨t, ht, p, hp, q, hq, a, ha, hc⟩ := hc
  exact transOne_of_run hS (Finset.mem_toList.mp hq) (List.mem_range.mp ht) c hc

end NPComplete.CookLevin

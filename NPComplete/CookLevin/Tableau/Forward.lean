module

public import NPComplete.CookLevin.Tableau.TapeEquality

/-!
# Tableau and run equivalence

To connect the SAT instance to machine acceptance, local tableau constraints must recover a
complete run, and a run must satisfy those constraints. This module assembles both global
implications from the local clause and tape lemmas.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Assembling the forward (SAT ⟹ run) direction -/

/-- Cells beyond the final window retain the initial blank symbol. -/
lemma tableauMachine_sat_imp_machineOutputsInTime_outside_window
    [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (input output : List Γ) (T : ℕ) (p : ℤ)
    (hlo : -(T : ℤ) ≤ runHead M input T) (hhi : runHead M input T ≤ T)
    (hout : ¬ (-(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1)) :
    absNth (runCfg M input T) (runHead M input T) (runHead M input T + p) =
      initSymbol output p := by
  have huntouched : runHead M input T + p < -(T : ℤ) ∨
      (T : ℤ) < runHead M input T + p := by omega
  rw [absNth_eq_initSymbol_of_untouched M input T _ huntouched]
  rcases (by omega : runHead M input T + p < -(T : ℤ) ∨
      (max input.length output.length + T : ℤ) + 1 ≤ runHead M input T + p) with hneg | hpos
  · rw [initSymbol_eq_default_of_neg (by omega), initSymbol_eq_default_of_neg (by omega)]
  · have hm1 := le_max_left input.length output.length
    have hm2 := le_max_right input.length output.length
    rw [initSymbol_eq_default_of_ge (by omega), initSymbol_eq_default_of_ge (by omega)]

/-- Accept clauses and uniqueness pin each in-window output cell to the output word. -/
lemma tableauMachine_sat_imp_machineOutputsInTime_inside_window
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment}
    (hW : windowSize input.length output.length T ≤ W)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hhdT : τ (headVar T (posToIdx T (runHead M input T))) = true)
    (hWpos : posToIdx T (runHead M input T) < W)
    (hclT : ∀ p, p < W → τ (cellVar T p (letterIdx (absNth (runCfg M input T)
      (runHead M input T) (idxToPos T p)))) = true)
    (hlo : -(T : ℤ) ≤ runHead M input T) (p : ℤ)
    (hin : -(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1) :
    absNth (runCfg M input T) (runHead M input T) (runHead M input T + p) =
      initSymbol output p := by
  have hpW : posToIdx T (runHead M input T + p) < W :=
    lt_of_lt_of_le (posToIdx_lt_window hin.2) hW
  have hcellT := hclT _ hpW
  rw [idxToPos_posToIdx hin.1] at hcellT
  have hmem : implyPos (headVar T (posToIdx T (runHead M input T)))
      (cellVar T (posToIdx T (runHead M input T + p))
        (letterIdx (initSymbol output ((posToIdx T (runHead M input T + p) : ℤ) -
          (posToIdx T (runHead M input T) : ℤ))))) ∈ acceptClauses M S output W T := by
    simp only [acceptClauses, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inl ⟨_, List.mem_range.mpr hWpos, _, List.mem_range.mpr hpW, rfl⟩
  rw [atMostOne_cell_of_sat (le_refl T) hUniq hpW hcellT
    (eval_implyPos (hAccept _ hmem) hhdT)]
  have hc1 : (posToIdx T (runHead M input T + p) : ℤ) = runHead M input T + p + T :=
    Int.toNat_of_nonneg (by omega)
  have hc2 : (posToIdx T (runHead M input T) : ℤ) = runHead M input T + T :=
    Int.toNat_of_nonneg (by omega)
  congr 1
  rw [hc1, hc2]
  ring

/-- Combine the in-window and untouched-cell equations into equality of tapes. -/
lemma tableauMachine_sat_imp_machineOutputsInTime_tape
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment}
    (hW : windowSize input.length output.length T ≤ W)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hhdT : τ (headVar T (posToIdx T (runHead M input T))) = true)
    (hclT : ∀ p, p < W → τ (cellVar T p (letterIdx (absNth (runCfg M input T)
      (runHead M input T) (idxToPos T p)))) = true) :
    (runCfg M input T).Tape = Tape.mk₁ output := by
  have hlo : -(T : ℤ) ≤ runHead M input T := by
    have := (runHead_abs_le M input T).1
    omega
  have hhi : runHead M input T ≤ (T : ℤ) := by
    have := (runHead_abs_le M input T).2
    omega
  have hWpos : posToIdx T (runHead M input T) < W :=
    lt_of_lt_of_le (runHead_posToIdx_lt_window M input (le_refl T)) hW
  apply tape_ext_of_nth
  intro p
  rw [tape_mk₁_nth, ← show absNth (runCfg M input T) (runHead M input T)
      (runHead M input T + p) = (runCfg M input T).Tape.nth p by simp [absNth]]
  by_cases hpw : -(T : ℤ) ≤ runHead M input T + p ∧
      runHead M input T + p < (max input.length output.length + T : ℤ) + 1
  · exact tableauMachine_sat_imp_machineOutputsInTime_inside_window hW hUniq
      hAccept hhdT hWpos hclT hlo p hpw
  · exact tableauMachine_sat_imp_machineOutputsInTime_outside_window M input output
      T p hlo hhi hpw

/-- The satisfied accept clause forces a halt at the output head symbol. -/
lemma tableauMachine_sat_imp_machineOutputsInTime_halt
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T W : ℕ}
    {τ : Literal.Assignment} (hS : Supports M ↑S)
    (hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ)
    (hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ)
    (hstT : τ (stateVar T (stateIdx S (runCfg M input T).q)) = true)
    (hshape : (runCfg M input T).Tape = Tape.mk₁ output) :
    step M (runCfg M input T) = none := by
  have hhaltClause : atLeastOne
      ((haltStates M S (initSymbol output 0)).map
        fun q => stateVar T (stateIdx S q)) ∈ acceptClauses M S output W T := by
    simp [acceptClauses]
  obtain ⟨qv, hqvmem, hqvtrue⟩ := atLeastOne_exists (hAccept _ hhaltClause)
  simp only [List.mem_map] at hqvmem
  obtain ⟨q, hqmem, hqeq⟩ := hqvmem
  rw [← hqeq] at hqvtrue
  have hqeqReal : q = (runCfg M input T).q :=
    atMostOne_state_of_sat (S := S) (le_refl T) hUniq
      (Finset.mem_toList.mp (List.mem_of_mem_filter hqmem))
      (runCfg_state_mem hS input T) hqvtrue hstT
  have hmatch := (List.mem_filter.mp (hqeqReal ▸ hqmem)).2
  have hMeq : M (runCfg M input T).q (initSymbol output 0) = none := by
    rcases hMM : M (runCfg M input T).q (initSymbol output 0) with _ | _
    · rfl
    · simp [hMM] at hmatch
  rw [step_eq_none_iff, show (runCfg M input T).Tape.head = initSymbol output 0 by
    rw [hshape, ← Tape.nth_zero, tape_mk₁_nth]]
  exact hMeq

/-- If the standard tableau is satisfiable, the machine actually produces
`output` within `T` steps. This is the `→` direction of
`tableauMachine_sat_iff`. -/
lemma tableauMachine_sat_imp_machineOutputsInTime [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ] {M : Machine Γ Λ} {S : Finset Λ}
    {input output : List Γ} {T : ℕ} (hS : Supports M ↑S)
    (hSAT : SAT (tableauMachine M S input output T)) :
    MachineOutputsInTime M input output T := by
  obtain ⟨τ, hτ⟩ := hSAT
  set W := windowSize input.length output.length T with hWdef
  have hUniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ := by
    intro c hc; apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]; tauto
  have hInit : ∀ c ∈ initClauses S input W T, c.Satisfied τ := by
    intro c hc; apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]; tauto
  have hTrans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc; apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]; tauto
  have hPersist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ := by
    intro c hc; apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]; tauto
  have hAccept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ := by
    intro c hc; apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]; tauto
  obtain ⟨hstT, hhdT, hclAllT⟩ := sat_run hS hInit hTrans hPersist T (le_refl T)
  have hW : windowSize input.length output.length T ≤ W := by rw [hWdef]
  have hshape := tableauMachine_sat_imp_machineOutputsInTime_tape
    hW hUniq hAccept hhdT hclAllT
  exact machineOutputsInTime_of_halted hshape
    (tableauMachine_sat_imp_machineOutputsInTime_halt hS hUniq hAccept hstT hshape)

/--
The `→` direction (`SAT ⟹ MachineOutputsInTime`) follows from
`tableauMachine_sat_imp_machineOutputsInTime`, whose central induction `sat_run`
shows that satisfying assignments reproduce the run's state, head, and cell
snapshot at every time.

For the `←` direction (`MachineOutputsInTime ⟹ SAT`), tapes carry no absolute
position.  The acceptance clauses therefore state the output relative to a
head position selected by the uniqueness clauses.  Given a run, `.mpr` builds
`runAssign` and verifies each clause family; `acceptClauses_of_run` supplies
the acceptance clauses from the halting snapshot.
-/
lemma tableauMachine_sat_iff [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Inhabited Λ] [DecidableEq Λ] (M : Machine Γ Λ) (S : Finset Λ)
    (input output : List Γ) (T : ℕ) (hS : Supports M ↑S) :
    SAT (tableauMachine M S input output T) ↔
    MachineOutputsInTime M input output T := by
  constructor
  · exact tableauMachine_sat_imp_machineOutputsInTime hS
  · intro hRun
    have hUniq := uniquenessClauses_of_run (M := M) (S := S) (input := input)
      (output := output) (T := T) hS
    have hInit := initClauses_of_run (M := M) (S := S) (input := input)
      (output := output) (T := T) hS
    have hTrans := transClauses_of_run (M := M) (S := S) (input := input)
      (output := output) (T := T) hS
    have hPersist := persistClauses_of_run (M := M) (S := S) (input := input)
      (output := output) (T := T)
    have hAccept := acceptClauses_of_run (M := M) (S := S) (input := input)
      (output := output) (T := T) hS hRun
    refine ⟨runAssign M S input output T, ?_⟩
    intro c hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append] at hc
    aesop

lemma boundedPrefixInitClauses_of_standard_sat [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ}
    {input pref output : List Γ} {freeLen W T k : ℕ}
    {allowed : List Γ} {blank : Γ} {τ : Literal.Assignment}
    (hW : W = windowSize input.length output.length T)
    (hspan : T + pref.length + freeLen + 1 ≤ W)
    (hstd : ∀ c ∈ (tableauMachine M S input output T).clauses,
      c.Satisfied τ)
    (hprefix : ∀ p, p < T + pref.length →
      initSymbol input (idxToPos T p) = initSymbol pref (idxToPos T p))
    (hfree : ∀ i, i < freeLen →
      ∃ a ∈ blank :: allowed, initSymbol input
          (idxToPos T (T + pref.length + i)) = a ∧
        ((i < k ∧ a ≠ blank) ∨ (k ≤ i ∧ a = blank)))
    (htail : ∀ p, T + pref.length + freeLen ≤ p →
      initSymbol input (idxToPos T p) = blank) :
    ∀ c ∈ boundedPrefixInitClauses S pref freeLen allowed blank W T,
      c.Satisfied τ := by
  have huniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied τ := by
    intro c hc
    apply hstd
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    have hW' : W = windowSize input.length output.length T := hW
    aesop
  have hstdInit : ∀ c ∈ initClauses S input W T,
      c.Satisfied τ := by
    intro c hc
    apply hstd
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    have hW' : W = windowSize input.length output.length T := hW
    aesop
  have hstdCell : ∀ p, p < W →
      τ (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p)))) = true := by
    intro p hp
    apply eval_unitPos
    apply hstdInit
    simp only [initClauses, List.mem_cons, List.mem_map]
    exact Or.inr (Or.inr ⟨p, List.mem_range.mpr hp, rfl⟩)
  intro c hc
  unfold boundedPrefixInitClauses at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
    have hpW : p < W := List.mem_range.mp hp
    by_cases hfix : p < T + pref.length
    · rw [ite_eq_left hfix]
      refine satisfied_unitPos ?_
      simpa [hprefix p hfix] using hstdCell p hpW
    · by_cases hfree' : p < T + pref.length + freeLen
      · rw [ite_eq_right hfix, ite_eq_left hfree']
        let i := p - (T + pref.length)
        have hi : i < freeLen := by
          dsimp [i]
          omega
        have hpEq : p = T + pref.length + i := by
          dsimp [i]
          omega
        obtain ⟨a, ha, hEq, hcase⟩ := hfree i hi
        refine satisfied_atLeastOne
          (List.mem_map.mpr ⟨a, ha, rfl⟩) ?_
        have hcell := hstdCell p hpW
        rw [hpEq] at hcell
        rw [hEq] at hcell
        rw [hpEq]
        exact hcell
      · rw [ite_eq_right hfix, ite_eq_right hfree']
        refine satisfied_unitPos ?_
        simpa [htail p (by omega)] using hstdCell p hpW
  · rcases List.mem_map.mp hc with ⟨i, hi, rfl⟩
    have hi' : i < freeLen := List.mem_range.mp hi
    have hp : T + pref.length + i < W := by omega
    have hpNext : T + pref.length + i + 1 < W := by omega
    obtain ⟨a, ha, hEq, hcase⟩ := hfree i hi'
    by_cases hik : i < k
    · have hne : a ≠ blank := by
        rcases hcase with ⟨_, hne⟩ | hblank
        · exact hne
        · omega
      have hcell := hstdCell (T + pref.length + i) hp
      have hcell' : τ (cellVar 0 (T + pref.length + i)
          (letterIdx a)) = true := by
        simpa [hEq] using hcell
      have hfalse := cell_value_false_of_uniqueness huniq hp hcell' hne
      refine ⟨Literal.neg
        (cellVar 0 (T + pref.length + i) (letterIdx blank)), by
          simp [implyPos], ?_⟩
      simp [Literal.eval, hfalse]
    · have hblank : a = blank := by
        rcases hcase with htrue | ⟨hge, hblank⟩
        · omega
        · exact hblank
      by_cases hinext : i + 1 < freeLen
      · obtain ⟨a', ha', hEq', hcase'⟩ := hfree (i + 1) hinext
        have hblank' : a' = blank := by
          rcases hcase' with htrue | ⟨hge, hblank'⟩
          · omega
          · exact hblank'
        refine ⟨Literal.pos
          (cellVar 0 (T + pref.length + i + 1) (letterIdx blank)), by
            simp [implyPos], ?_⟩
        have hnext := hstdCell (T + pref.length + i + 1) hpNext
        have hEq'' : initSymbol input
            (idxToPos T (T + pref.length + i + 1)) = a' := by
          simpa only [Nat.add_assoc] using hEq'
        rw [hEq'', hblank'] at hnext
        simpa [Literal.eval] using hnext
      · refine ⟨Literal.pos
          (cellVar 0 (T + pref.length + i + 1) (letterIdx blank)), by
            simp [implyPos], ?_⟩
        have hnext := hstdCell (T + pref.length + i + 1) hpNext
        rw [htail (T + pref.length + i + 1) (by omega)] at hnext
        simpa [Literal.eval] using hnext

lemma tableauMachineWithInit_sat_of_run [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ}
    {input output pref : List Γ} {freeLen : ℕ} {allowed : List Γ} {T : ℕ}
    (hS : Supports M ↑S)
    (hRun : MachineOutputsInTime M input output T)
    (hprefix : ∀ p, p < T + pref.length →
      initSymbol input (idxToPos T p) = initSymbol pref (idxToPos T p))
    (hallowed : ∀ p, T + pref.length ≤ p →
      p < T + pref.length + freeLen →
      ∃ a ∈ allowed, initSymbol input (idxToPos T p) = a)
    (hblank : ∀ p, T + pref.length + freeLen ≤ p →
      initSymbol input (idxToPos T p) = (default : Γ)) :
    SAT (tableauMachineWithInit M S input output T
      (prefixInitClauses S pref freeLen allowed
        (windowSize input.length output.length T) T)) := by
  obtain ⟨τ, hτ⟩ := (tableauMachine_sat_iff M S input output T hS).mpr hRun
  let W := windowSize input.length output.length T
  have hstdInit : ∀ c ∈ initClauses S input W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    have hc' : c ∈ initClauses S input
        (windowSize input.length output.length T) T := by
      simpa [W] using hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have hstdCell : ∀ p, p < W →
      τ (cellVar 0 p (letterIdx (initSymbol input (idxToPos T p)))) = true := by
    intro p hp
    apply eval_unitPos
    apply hstdInit
    simp only [initClauses, List.mem_cons, List.mem_map]
    exact Or.inr (Or.inr ⟨p, List.mem_range.mpr hp, rfl⟩)
  have hcustom : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ := by
    intro c hc
    simp only [prefixInitClauses, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    rcases hc with rfl | hc
    · exact hstdInit _ (by simp [initClauses])
    simp only [List.mem_map] at hc
    rcases hc with ⟨p, hp, rfl⟩
    have hpW : p < W := List.mem_range.mp hp
    by_cases hfix : p < T + pref.length
    · rw [ite_eq_left hfix]
      refine satisfied_unitPos ?_
      simpa [hprefix p hfix] using hstdCell p hpW
    · by_cases hfree : p < T + pref.length + freeLen
      · rw [ite_eq_right hfix, ite_eq_left hfree]
        obtain ⟨a, ha, hEq⟩ := hallowed p (by omega) hfree
        refine satisfied_atLeastOne (List.mem_map.mpr ⟨a, ha, rfl⟩) ?_
        have haτ := hstdCell p hpW
        simpa [hEq] using haτ
      · rw [ite_eq_right hfix, ite_eq_right hfree]
        refine satisfied_unitPos ?_
        simpa [hblank p (by omega)] using hstdCell p hpW
  have hτ_unique : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    have hc' : c ∈ uniquenessClauses (Γ := Γ) S
        (windowSize input.length output.length T) T := by
      simpa [W] using hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have hτ_trans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    have hc' : c ∈ transClauses M S
        (windowSize input.length output.length T) T := by
      simpa [W] using hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have hτ_persist : ∀ c ∈ persistClauses (Γ := Γ) W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    have hc' : c ∈ persistClauses (Γ := Γ)
        (windowSize input.length output.length T) T := by
      simpa [W] using hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have hτ_accept : ∀ c ∈ acceptClauses M S output W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    have hc' : c ∈ acceptClauses M S output
        (windowSize input.length output.length T) T := by
      simpa [W] using hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  refine ⟨τ, ?_⟩
  intro c hc
  simp only [tableauMachineWithInit, List.mem_append] at hc
  have hW' : W = windowSize input.length output.length T := rfl
  aesop

lemma tableauMachineWithInit_sat_of_run_of_initial [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ} {input output : List Γ} {T : ℕ}
    {initial : List Clause} (hS : Supports M ↑S)
    (hRun : MachineOutputsInTime M input output T)
    (hInit : ∀ τ : Literal.Assignment,
      (∀ c ∈ (tableauMachine M S input output T).clauses,
        c.Satisfied τ) →
      ∀ c ∈ initial, c.Satisfied τ) :
    SAT (tableauMachineWithInit M S input output T initial) := by
  obtain ⟨τ, hτ⟩ := (tableauMachine_sat_iff M S input output T hS).mpr hRun
  have hinitial := hInit τ hτ
  have huniq : ∀ c ∈ uniquenessClauses (Γ := Γ) S
      (windowSize input.length output.length T) T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have htrans : ∀ c ∈ transClauses M S
      (windowSize input.length output.length T) T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have hpersist : ∀ c ∈ persistClauses (Γ := Γ)
      (windowSize input.length output.length T) T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  have haccept : ∀ c ∈ acceptClauses M S output
      (windowSize input.length output.length T) T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append]
    aesop
  refine ⟨τ, ?_⟩
  intro c hc
  simp only [tableauMachineWithInit, List.mem_append] at hc
  aesop

/-- Prefix constraints and supplied free cells determine every standard initial clause. -/
lemma prefixInitClauses_satisfied_implies_initClauses
    [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {S : Finset Λ} {pref suffix : List Γ}
    {freeLen W T : ℕ} {allowed : List Γ} {τ : Literal.Assignment}
    (hsuffixLen : suffix.length = freeLen)
    (hcustom : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ)
    (hfree : ∀ i, i < freeLen →
      τ (cellVar 0 (T + pref.length + i) (letterIdx (suffix.getI i))) = true) :
    ∀ c ∈ initClauses S (pref ++ suffix) W T, c.Satisfied τ := by
  intro c hc
  simp only [initClauses, List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | hc
  · exact hcustom _ (by simp [prefixInitClauses])
  rcases hc with rfl | hc
  · exact hcustom _ (by simp [prefixInitClauses])
  rcases hc with ⟨p, hp, rfl⟩
  have hpW : p < W := List.mem_range.mp hp
  by_cases hfix : p < T + pref.length
  · have hτcell := fixed_cell_of_prefixInitClauses
      (S := S) (pref := pref) (freeLen := freeLen) (allowed := allowed)
      (W := W) (T := T) hcustom hpW hfix
    refine satisfied_unitPos ?_
    simpa [initSymbol_append_idxToPos_prefix pref suffix T p hfix] using hτcell
  · by_cases hfree' : p < T + pref.length + suffix.length
    · let i := p - (T + pref.length)
      have hi : i < freeLen := by
        dsimp [i]
        omega
      have hpEq : p = T + pref.length + i := by
        dsimp [i]
        omega
      have hτcell := hfree i hi
      refine satisfied_unitPos ?_
      rw [initSymbol_append_idxToPos_suffix pref suffix T p (by omega) hfree']
      rw [hpEq]
      have hsub : T + pref.length + i - (T + pref.length) = i := by omega
      rw [hsub]
      exact hτcell
    · have hblank : T + pref.length + suffix.length ≤ p := by omega
      have hτcell := blank_cell_of_prefixInitClauses
        (S := S) (pref := pref) (freeLen := freeLen)
        (allowed := allowed) (W := W) (T := T) hcustom hpW (by omega)
      refine satisfied_unitPos ?_
      simpa [initSymbol_append_idxToPos_default pref suffix T p hblank] using hτcell

lemma machineOutputs_of_prefixInitClauses_sat [Inhabited Γ] [Fintype Γ]
    [DecidableEq Γ] [Inhabited Λ] [DecidableEq Λ]
    {M : Machine Γ Λ} {S : Finset Λ}
    {pref suffix output : List Γ} {freeLen : ℕ} {allowed : List Γ} {T : ℕ}
    {τ : Literal.Assignment}
    (hS : Supports M ↑S)
    (hsuffixLen : suffix.length = freeLen)
    (hτ : ∀ c ∈ (tableauMachineWithInit M S (pref ++ suffix) output T
      (prefixInitClauses S pref freeLen allowed
        (windowSize (pref ++ suffix).length output.length T) T)).clauses,
      c.Satisfied τ)
    (hfree : ∀ i, i < freeLen →
        τ (cellVar 0 (T + pref.length + i)
          (letterIdx (suffix.getI i))) = true) :
    MachineOutputsInTime M (pref ++ suffix) output T := by
  let W := windowSize (pref ++ suffix).length output.length T
  have hcustom : ∀ c ∈ prefixInitClauses S pref freeLen allowed W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInit, List.mem_append]
    have hc' : c ∈ prefixInitClauses S pref freeLen allowed
        (windowSize (pref ++ suffix).length output.length T) T := by
      simpa [W] using hc
    tauto
  have hstdInit :=
    prefixInitClauses_satisfied_implies_initClauses hsuffixLen hcustom hfree
  have hτ_unique : ∀ c ∈ uniquenessClauses (Γ := Γ) S W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInit, List.mem_append]
    tauto
  have hτ_trans : ∀ c ∈ transClauses M S W T, c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInit, List.mem_append]
    tauto
  have hτ_persist : ∀ c ∈ persistClauses (Γ := Γ) W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInit, List.mem_append]
    tauto
  have hτ_accept : ∀ c ∈ acceptClauses M S output W T,
      c.Satisfied τ := by
    intro c hc
    apply hτ
    simp only [tableauMachineWithInit, List.mem_append]
    tauto
  have hstdSat : SAT (tableauMachine M S (pref ++ suffix) output T) := by
    refine ⟨τ, ?_⟩
    intro c hc
    simp only [tableauMachine, tableauMachineWithInit, List.mem_append] at hc
    aesop
  exact (tableauMachine_sat_iff M S (pref ++ suffix) output T hS).mp hstdSat

lemma tableau_sat_iff [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : Finset Λ) (x : List Bool) (T : ℕ)
    (hS : Supports M ↑S) :
    SAT (tableau M S x T) ↔
      MachineOutputsInTime M (tapeSymbols x) (tapeSymbols [true]) T :=
  tableauMachine_sat_iff M S (tapeSymbols x) (tapeSymbols [true]) T hS

lemma TM0ComputableAux.tableau_sat_iff (tm : TM0ComputableAux Bool)
    (x : List Bool) (T : ℕ) :
    SAT (tm.tableau x T) ↔
      MachineOutputsInTime tm.M (tapeSymbols x) (tapeSymbols [true]) T :=
  CookLevin.tableau_sat_iff tm.M tm.S x T tm.supports

lemma tableauFin_sat_iff (tm : FinTM0) [DecidableEq tm.Γ] [DecidableEq tm.Λ]
    (input output : List tm.Γ) (T : ℕ) :
    SAT (tableauFin tm input output T) ↔ TM0OutputsInTime tm input output T :=
  tableauMachine_sat_iff tm.M tm.S input output T tm.supports

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Generate.ClauseShape
public import NPComplete.CookLevin.Tableau.TableauAtWindow

/-!
# Shared bounded-certificate proofs

The tight and explicit-window encodings share the same extraction and padding
arguments. This module isolates those arguments so each public correctness result
can specialize them without repeating tableau reasoning.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

/-- Shared certificate extraction for tight and explicitly supplied windows. -/
lemma bounded_sat_implies_certificate_core
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (pref shape output : List (Option Bool))
    (certificateBound T W : ℕ)
    (tableauWithInit :
      List (Option Bool) → List (Option Bool) → ℕ → ℕ →
        List Clause → CNF)
    (boundInitial : List Clause)
    (exactInitial : List (Option Bool) → List Clause)
    (τ : Literal.Assignment)
    (hpref : pref = (pairBits x []).map some)
    (houtput : output = tapeSymbols [true])
    (hτBound : ∀ c ∈
      (tableauWithInit shape output T W boundInitial).clauses,
      c.Satisfied τ)
    (hBoundedInitialMem : ∀ c ∈ boundedPrefixInitClauses tm.S pref
      certificateBound [some false, some true] none W T,
      c ∈ (tableauWithInit shape output T W
        boundInitial).clauses)
    (hWfree : ∀ i, i < certificateBound →
      T + pref.length + i < W)
    (hExactMem : ∀ suffix, suffix.length = certificateBound → ∀ c ∈
      (tableauWithInit (pref ++ suffix) output T W
        (exactInitial suffix)).clauses,
      c ∈ (tableauWithInit shape output T W
        boundInitial).clauses)
    (hOutput : ∀ suffix, suffix.length = certificateBound →
      (∀ c ∈ (tableauWithInit (pref ++ suffix) output T W
        (exactInitial suffix)).clauses, c.Satisfied τ) →
      (∀ i, i < certificateBound →
        τ (cellVar 0 (T + pref.length + i)
          (letterIdx (suffix.getI i))) = true) →
      MachineOutputsInTime tm.M (pref ++ suffix) output T) :
    ∃ w : List Bool, w.length ≤ certificateBound ∧
      MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
        output T := by
  have hInitBound : ∀ c ∈ boundedPrefixInitClauses tm.S pref
      certificateBound [some false, some true] none W T, c.Satisfied τ := by
    intro c hc
    exact hτBound c (hBoundedInitialMem c hc)
  have hfree : ∀ i, i < certificateBound →
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (none : Option Bool))) = true ∨
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (some false))) = true ∨
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (some true))) = true := by
    intro i hi
    obtain ⟨a, ha, hval⟩ := bounded_free_cell_of_clauses
      (S := tm.S) (pref := pref) (freeLen := certificateBound)
      (allowed := [some false, some true]) (blank := (none : Option Bool))
      (W := W) (T := T) hInitBound (hWfree i hi)
      (by omega) (by omega)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | hlast
    · exact Or.inl hval
    · exact Or.inr (Or.inl hval)
    · rcases hlast with rfl | hnil
      · exact Or.inr (Or.inr hval)
      · cases hnil
  have hNoHole : ∀ i, i < certificateBound →
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (none : Option Bool))) = true →
      τ (cellVar 0 (T + pref.length + i + 1)
        (letterIdx (none : Option Bool))) = true := by
    intro i hi hnone
    exact bounded_no_hole_of_clauses (S := tm.S) (pref := pref)
      (freeLen := certificateBound) (allowed := [some false, some true])
      (blank := (none : Option Bool)) (W := W) (T := T)
      hInitBound hi hnone
  obtain ⟨w, hwlen, hwassign, hwblank⟩ :=
    bounded_suffix_extract (τ := τ) (base := T + pref.length)
      certificateBound hfree hNoHole
  let fullSuffix : List (Option Bool) :=
    (w.map some) ++ List.replicate (certificateBound - w.length) none
  have hfullLen : fullSuffix.length = certificateBound := by
    simp [fullSuffix]
    omega
  have hfullFree : ∀ i, i < certificateBound →
      τ (cellVar 0 (T + pref.length + i)
        (letterIdx (fullSuffix.getI i))) = true := by
    intro i hi
    by_cases hwi : i < w.length
    · have hassign := hwassign i hwi
      have hget : fullSuffix.getI i = some (w.getI i) := by
        rw [show fullSuffix = w.map some ++
          List.replicate (certificateBound - w.length) none by rfl]
        rw [List.getI_append _ _ _ (by simpa using hwi)]
        exact getI_map_some w i hwi
      simpa [hget] using hassign
    · have hblank := hwblank i (by omega) hi
      have hget : fullSuffix.getI i = none := by
        rw [show fullSuffix = w.map some ++
          List.replicate (certificateBound - w.length) none by rfl]
        have hprefix : (w.map some).length ≤ i := by simp; omega
        rw [List.getI_append_right _ _ _ hprefix]
        have hoff : i - (w.map some).length = i - w.length := by simp
        rw [hoff]
        have hrep : i - w.length < (List.replicate
            (certificateBound - w.length) (none : Option Bool)).length := by
          simp only [List.length_replicate]
          omega
        rw [List.getI_eq_getElem _ hrep]
        simp
      simpa [hget] using hblank
  have hτFull : ∀ c ∈
      (tableauWithInit (pref ++ fullSuffix) output T W
        (exactInitial fullSuffix)).clauses, c.Satisfied τ := by
    intro c hc
    exact hτBound c (hExactMem fullSuffix hfullLen c hc)
  have hout := hOutput fullSuffix hfullLen hτFull hfullFree
  have hshape : pref ++ fullSuffix =
      (pairBits x w).map some ++ List.replicate
        (certificateBound - w.length) none := by
    rw [hpref]
    simp [fullSuffix, pairBits, List.map_append]
  have hout' : MachineOutputsInTime tm.M
      ((pairBits x w).map some ++ List.replicate
        (certificateBound - w.length) none) output T := by
    simpa [hshape] using hout
  have hout'' := machineOutputsInTime_of_append_blank hout'
  refine ⟨w, hwlen, ?_⟩
  simpa [houtput, tapeSymbols] using hout''

/-- Shared initial-clause contract for a padded certificate input. -/
lemma bounded_prefix_init_sat_core
    (pref fullSuffix output : List (Option Bool))
    (certificateBound T W : ℕ) (w : List Bool)
    (baseTableau :
      List (Option Bool) → List (Option Bool) → ℕ → ℕ → CNF)
    (boundInitial : List Clause)
    (hfullSuffix : fullSuffix =
      w.map some ++ List.replicate (certificateBound - w.length) none)
    (hfullLen : fullSuffix.length = certificateBound)
    (hw : w.length ≤ certificateBound)
    (hInitialMode : ∀ (τ : Literal.Assignment),
      (∀ c ∈ (baseTableau (pref ++ fullSuffix) output T W).clauses,
        c.Satisfied τ) →
      (∀ p, p < T + pref.length →
        initSymbol (pref ++ fullSuffix) (idxToPos T p) =
          initSymbol pref (idxToPos T p)) →
      (∀ i, i < certificateBound →
        ∃ a ∈ ((none : Option Bool) :: [some false, some true]),
          initSymbol (pref ++ fullSuffix)
              (idxToPos T (T + pref.length + i)) = a ∧
            ((i < w.length ∧ a ≠ none) ∨
              (w.length ≤ i ∧ a = none))) →
      (∀ p, T + pref.length + certificateBound ≤ p →
        initSymbol (pref ++ fullSuffix) (idxToPos T p) = none) →
      (w.length ≤ certificateBound) →
      ∀ c ∈ boundInitial, c.Satisfied τ) :
    ∀ τ : Literal.Assignment,
      (∀ c ∈ (baseTableau (pref ++ fullSuffix) output T W).clauses,
        c.Satisfied τ) →
      ∀ c ∈ boundInitial, c.Satisfied τ := by
  have hprefix : ∀ p, p < T + pref.length →
      initSymbol (pref ++ fullSuffix) (idxToPos T p) =
        initSymbol pref (idxToPos T p) := by
    intro p hp
    exact initSymbol_append_idxToPos_prefix pref fullSuffix T p hp
  have hfree : ∀ i, i < certificateBound →
      ∃ a ∈ ((none : Option Bool) :: [some false, some true]),
        initSymbol (pref ++ fullSuffix)
            (idxToPos T (T + pref.length + i)) = a ∧
          ((i < w.length ∧ a ≠ none) ∨
            (w.length ≤ i ∧ a = none)) := by
    intro i hi
    by_cases hwi : i < w.length
    · have hget : fullSuffix.getI i = some (w.getI i) := by
        rw [hfullSuffix]
        rw [List.getI_append _ _ _ (by simpa using hwi)]
        exact getI_map_some w i hwi
      have hsym : initSymbol (pref ++ fullSuffix)
          (idxToPos T (T + pref.length + i)) = some (w.getI i) := by
        rw [initSymbol_append_idxToPos_suffix pref fullSuffix T
          (T + pref.length + i) (by omega) (by omega)]
        simp [hget]
      refine ⟨some (w.getI i), ?_, hsym, Or.inl ⟨hwi, ?_⟩⟩
      · simp
      · simp
    · have hget : fullSuffix.getI i = none := by
        rw [hfullSuffix]
        have hprefix : (w.map some).length ≤ i := by simp; omega
        rw [List.getI_append_right _ _ _ hprefix]
        have hoff : i - (w.map some).length = i - w.length := by simp
        rw [hoff]
        have hrep : i - w.length <
            (List.replicate (certificateBound - w.length)
              (none : Option Bool)).length := by
          simp only [List.length_replicate]
          omega
        rw [List.getI_eq_getElem _ hrep]
        simp
      have hsym : initSymbol (pref ++ fullSuffix)
          (idxToPos T (T + pref.length + i)) = none := by
        rw [initSymbol_append_idxToPos_suffix pref fullSuffix T
          (T + pref.length + i) (by omega) (by omega)]
        simp [hget]
      refine ⟨none, by simp, hsym, Or.inr ⟨by omega, rfl⟩⟩
  have htail : ∀ p, T + pref.length + certificateBound ≤ p →
      initSymbol (pref ++ fullSuffix) (idxToPos T p) = none := by
    intro p hp
    exact initSymbol_append_idxToPos_default pref fullSuffix T p
      (by rw [hfullLen]; omega)
  intro τ hstd c hc
  exact hInitialMode τ hstd hprefix hfree htail hw c hc

/-- Shared witness-to-assignment padding for tight and windowed tableaux. -/
lemma bounded_sat_of_certificate_core
    (tm : TM0ComputableAux Bool) (x : List Bool)
    (pref fullSuffix output : List (Option Bool))
    (certificateBound T W : ℕ) (w : List Bool)
    (tableauWithInit :
      List (Option Bool) → List (Option Bool) → ℕ → ℕ →
        List Clause → CNF)
    (baseTableau :
      List (Option Bool) → List (Option Bool) → ℕ → ℕ → CNF)
    (boundInitial : List Clause)
    (hpref : pref = (pairBits x []).map some)
    (houtput : output = tapeSymbols [true])
    (hfullSuffix : fullSuffix =
      w.map some ++ List.replicate (certificateBound - w.length) none)
    (hRun : MachineOutputsInTime tm.M (tapeSymbols (pairBits x w))
      (tapeSymbols [true]) T)
    (hInit : ∀ τ : Literal.Assignment,
      (∀ c ∈ (baseTableau (pref ++ fullSuffix) output T W).clauses,
        c.Satisfied τ) →
      ∀ c ∈ boundInitial, c.Satisfied τ)
    (hSatOfRun :
      MachineOutputsInTime tm.M (pref ++ fullSuffix) output T →
      (∀ τ : Literal.Assignment,
        (∀ c ∈ (baseTableau (pref ++ fullSuffix) output T W).clauses,
          c.Satisfied τ) →
        ∀ c ∈ boundInitial, c.Satisfied τ) →
      SAT (tableauWithInit (pref ++ fullSuffix) output T W boundInitial)) :
    SAT (tableauWithInit (pref ++ fullSuffix) output T W boundInitial) := by
  have hinputRun : MachineOutputsInTime tm.M (pref ++ fullSuffix) output T := by
    have hpad := machineOutputsInTime_append_blank
      (M := tm.M) (input := tapeSymbols (pairBits x w))
      (output := tapeSymbols [true]) (T := T)
      (n := certificateBound - w.length) hRun
    simpa [hpref, houtput, hfullSuffix, tapeSymbols, pairBits,
      List.map_append] using hpad
  exact hSatOfRun hinputRun hInit

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Recode.Sim.Certificate

/-!
# Initial tape correspondence

Simulation starts from a source tape and a packed Boolean tape with different
representations. These lemmas establish their clean, content, and occupancy
relations so execution begins with the invariants preserved by later steps.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma sim_initial_rawTapeCleanRel (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    RawTapeCleanRel e
      (Tape.mk₁ (e.decodeList (encodePackedInput tm inp l)))
      (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  have hinput : e.decodeList (encodePackedInput tm inp l) =
      TM2to1.trInit tm.k₀
        (TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)) := by
    exact sim_decode_packed_input tm inp l
  have hsrc :
      TM2to1.trInit tm.k₀
        (TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)) ≠ [] := by
    unfold TM2to1.trInit
    simp
  obtain ⟨z, r, hz⟩ := List.exists_cons_of_ne_nil hsrc
  have hrel := rawTapeCleanRel_mk₁_encodeList e z r
  change RawTapeCleanRel e
    (Tape.mk₁ (e.decodeList (encodePackedInput tm inp l)))
    (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l)))
  rw [hinput, hz]
  have hsymbols : tapeSymbols (encodePackedInput tm inp l) =
      (z :: r).flatMap (rawEncodeBlock e) := by
    rw [sim_encodePackedInput (tm := tm) inp l, hz]
    have hraw : rawEncodeBlock e =
        (fun a => List.map some (e.enc a).toList) := by
      rfl
    rw [hraw]
    simp [tapeSymbols, BlockEnc.encodeList, e, List.map_flatMap]
  rw [hsymbols]
  exact hrel

lemma sim_initial_rawTapeCleanContentRel (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    RawTapeCleanContentRel e
      (Tape.mk₁ (e.decodeList (encodePackedInput tm inp l)))
      (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  have hinput : e.decodeList (encodePackedInput tm inp l) =
      TM2to1.trInit tm.k₀
        (TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)) := by
    exact sim_decode_packed_input tm inp l
  have hsrc :
      TM2to1.trInit tm.k₀
        (TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)) ≠ [] := by
    unfold TM2to1.trInit
    simp
  obtain ⟨z, r, hz⟩ := List.exists_cons_of_ne_nil hsrc
  have hrel := rawTapeCleanContentRel_mk₁_encodeList e z r
  change RawTapeCleanContentRel e
    (Tape.mk₁ (e.decodeList (encodePackedInput tm inp l)))
    (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l)))
  rw [hinput, hz]
  have hsymbols : tapeSymbols (encodePackedInput tm inp l) =
      (z :: r).flatMap (rawEncodeBlock e) := by
    rw [sim_encodePackedInput (tm := tm) inp l, hz]
    have hraw : rawEncodeBlock e =
        (fun a => List.map some (e.enc a).toList) := by
      rfl
    rw [hraw]
    simp [tapeSymbols, BlockEnc.encodeList, e, List.map_flatMap]
  rw [hsymbols]
  exact hrel

lemma sim_initial_simCleanRightTailOccupied (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    SimCleanRightTailOccupied e
      (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  apply simCleanRightTailOccupied_mk₁ e
  intro x hx
  simp only [tapeSymbols, List.mem_map] at hx
  rcases hx with ⟨b, hb, rfl⟩
  simp

lemma sim_initial_rawTapeCleanOccupiedRel (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    RawTapeCleanOccupiedRel e
      (Tape.mk₁ (e.decodeList (encodePackedInput tm inp l)))
      (Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  exact ⟨sim_initial_rawTapeCleanRel tm inp l, sim_initial_simCleanRightTailOccupied tm inp l⟩


end NPComplete.CookLevin

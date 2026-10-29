module

public import NPComplete.CookLevin.Recode.Sim.Reachability

/-!
# Packed input correspondence

The simulator receives Boolean input blocks, while the packed source machine
expects its translated initial tape. This module proves the encode/decode
correspondence that starts the simulation from the external bit list.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)


lemma sim_decode_packed_input (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).decodeList
        (encodePackedInput tm inp l) =
      TM2to1.trInit tm.k₀
        (TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let cell (isBottom b : Bool) :
      TM2to1.Γ' tm.K (TM2to1.PackΓ tm) :=
    (isBottom, Function.update (fun _ => none) tm.k₀
      (some ⟨inp.symm b, TM2to1.mem_usedSymbols_k₀ tm _⟩))
  have hn : 0 < e.n := by simpa [e] using encN_pos tm
  have henc :
      encodePackedInput tm inp l =
        e.encodeList (TM2to1.trInit tm.k₀
          (TM2to1.packList tm tm.k₀ (l.map inp.symm)
            (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x))) := by
    cases hrev : l.reverse with
    | nil =>
      have hl : l = [] := (List.reverse_eq_nil_iff).mp hrev
      subst l
      simp only [List.map_nil, TM2to1.packList]
      rw [encodePackedInput_nil]
      rw [trInit_nil]
      change (e.enc ((true, fun _ => none))).toList =
        e.encodeList [(true, fun _ => none)]
      simp only [BlockEnc.encodeList]
      exact (List.flatMap_singleton _ _).symm
    | cons b rest =>
      have hl : l = rest.reverse ++ [b] := by
        apply List.reverse_injective
        simp [hrev]
      subst l
      rw [encodePackedInput_snoc, trInit_packList_snoc]
      simp only [List.reverse_reverse]
      change (e.enc (cell true b)).toList ++
          rest.flatMap (fun x => (e.enc (cell false x)).toList) =
        List.flatMap (fun a => (e.enc a).toList)
          (cell true b :: rest.map (cell false))
      rw [List.flatMap_cons, List.flatMap_map]
  rw [henc]
  exact BlockEnc.decode_encodeList e hn _

lemma sim_encodePackedInput {tm : FinTM2} (inp : tm.Γ tm.k₀ ≃ Bool)
    (l : List Bool) :
    encodePackedInput tm inp l =
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).encodeList
        (TM2to1.trInit tm.k₀
          (TM2to1.packList tm tm.k₀ (l.map inp.symm)
            (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x))) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let cell (isBottom b : Bool) :
      TM2to1.Γ' tm.K (TM2to1.PackΓ tm) :=
    (isBottom, Function.update (fun _ => none) tm.k₀
      (some ⟨inp.symm b, TM2to1.mem_usedSymbols_k₀ tm _⟩))
  cases hrev : l.reverse with
  | nil =>
      have hl : l = [] := (List.reverse_eq_nil_iff).mp hrev
      subst l
      simp only [List.map_nil, TM2to1.packList]
      rw [encodePackedInput_nil, trInit_nil]
      change (e.enc ((true, fun _ => none))).toList =
        e.encodeList [(true, fun _ => none)]
      simp only [BlockEnc.encodeList]
      exact (List.flatMap_singleton _ _).symm
  | cons b rest =>
      have hl : l = rest.reverse ++ [b] := by
        apply List.reverse_injective
        simp [hrev]
      subst l
      rw [encodePackedInput_snoc, trInit_packList_snoc]
      simp only [List.reverse_reverse]
      change (e.enc (cell true b)).toList ++
          rest.flatMap (fun x => (e.enc (cell false x)).toList) =
        List.flatMap (fun a => (e.enc a).toList)
          (cell true b :: rest.map (cell false))
      rw [List.flatMap_cons, List.flatMap_map]


end NPComplete.CookLevin

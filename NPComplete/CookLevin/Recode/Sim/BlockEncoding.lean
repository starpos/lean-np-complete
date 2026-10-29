module

public import NPComplete.CookLevin.Recode.Sim.Time

/-!
# Block-Level Simulation Semantics

Simulation must compare a block's decoded symbol without fixing a unique physical representation of
its bits. This module isolates that observation together with the occupancy markers needed by cleanup,
so global tape relations and machine-step macros can share the same local block semantics.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

noncomputable def BlockEnc.decodeFirst {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (l : List Bool) : Γ :=
  let bits := (l ++ List.replicate e.n false).take e.n
  if h : bits.length = e.n then
    e.dec ⟨bits, h⟩
  else
    default

lemma BlockEnc.decodeFirst_encodeList_head {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) (l : List Γ) :
    e.decodeFirst (e.encodeList (a :: l)) = a := by
  unfold decodeFirst
  rw [BlockEnc.encodeList_cons]
  have htake :
      (((e.enc a).toList ++ e.encodeList l ++ List.replicate e.n false).take e.n) =
        (e.enc a).toList := by
    rw [List.append_assoc,
      List.take_left' (List.Vector.toList_length (e.enc a))]
  rw [htake]
  simp [List.Vector.toList_length, e.dec_enc]

lemma BlockEnc.decodeFirst_of_blockDecodes {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (old rest : List (Option Bool))
    (a : Γ) (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a) :
    e.decodeFirst ((old ++ rest).map (Option.getD · false)) = a := by
  unfold BlockEnc.decodeFirst
  rw [List.map_append]
  rw [List.take_append_of_le_length]
  · simpa [hold] using hdec
  · simp [hold]

lemma BlockEnc.n_pos_of_ne_default {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) {a : Γ} (ha : a ≠ default) : 0 < e.n := by
  classical
  by_contra hn
  have hn0 : e.n = 0 := by omega
  have henc : e.enc a = e.enc default := by
    let : Subsingleton (List.Vector Bool e.n) :=
      ⟨fun x y => by
        apply Subtype.ext
        have hx := x.property
        have hy := y.property
        have hx0 : x.val.length = 0 := by omega
        have hy0 : y.val.length = 0 := by omega
        rw [List.length_eq_zero_iff] at hx0 hy0
        exact hx0.trans hy0.symm⟩
    exact Subsingleton.elim _ _
  have haeq : a = default := by
    simpa [e.dec_enc] using congrArg e.dec henc
  exact ha haeq

/-! A raw target block may contain `none` or `some false` in positions whose
decoded bit is false.  The simulation invariant therefore observes blocks
through `Option.getD`, rather than requiring a particular representative. -/

def BlockDecodes {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (b : List (Option Bool)) (a : Γ) : Prop :=
  ∃ h : b.length = e.n,
    e.dec ⟨b.map (Option.getD · false), by simp [h]⟩ = a

def BlockMarked (b : List (Option Bool)) : Prop :=
  ∀ x ∈ b, x.isSome

/-! Physical occupancy of a finite target-tape span.  This is kept separate from the
block-level semantic relation `BlockDecodes`, which intentionally quotients away trailing blanks,
whereas cleanup needs to know which finite cells have actually been visited. -/

def BlocksMarked : List (List (Option Bool)) → Prop
  | [] => True
  | b :: bs => BlockMarked b ∧ BlocksMarked bs

lemma blocksMarked_nil : BlocksMarked ([] : List (List (Option Bool))) := by
  simp [BlocksMarked]

lemma blocksMarked_cons {b : List (Option Bool)} {bs : List (List (Option Bool))} :
    BlocksMarked (b :: bs) ↔ BlockMarked b ∧ BlocksMarked bs := by
  rfl

def simMarkBlock (b : List (Option Bool)) : List (Option Bool) :=
  b.map simMarkCell

lemma simMarkCell_idem (x : Option Bool) :
    simMarkCell (simMarkCell x) = simMarkCell x := by
  cases x <;> simp [simMarkCell]

lemma blockDecodes_length {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {b : List (Option Bool)} {a : Γ}
    (h : BlockDecodes e b a) : b.length = e.n := by
  rcases h with ⟨h, _⟩
  exact h

lemma blockDecodes_congr {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {b b' : List (Option Bool)} {a : Γ}
    (h : BlockDecodes e b a) (hlen : b'.length = b.length)
    (hobs : b'.map (Option.getD · false) = b.map (Option.getD · false)) :
    BlockDecodes e b' a := by
  rcases h with ⟨hb, ha⟩
  have hb' : b'.length = e.n := hlen.trans hb
  refine ⟨hb', ?_⟩
  have hv :
      (⟨b'.map (Option.getD · false), by simp [hb']⟩ : List.Vector Bool e.n) =
        ⟨b.map (Option.getD · false), by simp [hb]⟩ := by
    apply List.Vector.eq
    exact hobs
  rw [hv]
  exact ha

lemma blockDecodes_default {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) : BlockDecodes e (List.replicate e.n none) default := by
  have hlen : (List.replicate e.n (none : Option Bool)).length = e.n := by simp
  refine ⟨hlen, ?_⟩
  have hmaplen :
      ((List.replicate e.n (none : Option Bool)).map (Option.getD · false)).length =
        e.n := by simp
  have hv :
      (⟨(List.replicate e.n (none : Option Bool)).map (Option.getD · false), hmaplen⟩ :
        List.Vector Bool e.n) = e.enc default := by
    apply List.Vector.eq
    rw [e.enc_default]
    rw [List.Vector.toList_mk]
    have hrep : (List.Vector.replicate e.n false).toList =
        List.replicate e.n false := by
      rfl
    rw [hrep]
    simp
  rw [hv]
  exact e.dec_enc default

lemma blockDecodes_enc {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) :
    BlockDecodes e ((e.enc a).toList.map some) a := by
  have hlen : ((e.enc a).toList.map some).length = e.n := by
    simp [List.Vector.toList_length]
  refine ⟨hlen, ?_⟩
  have hmaplen :
      (((e.enc a).toList.map some).map (Option.getD · false)).length = e.n := by
    simp [List.Vector.toList_length]
  have hv :
      (⟨((e.enc a).toList.map some).map (Option.getD · false), hmaplen⟩ :
        List.Vector Bool e.n) = e.enc a := by
    apply List.Vector.eq
    rw [List.Vector.toList_mk]
    simp
  rw [hv]
  exact e.dec_enc a

lemma simMarkBlock_length (b : List (Option Bool)) :
    (simMarkBlock b).length = b.length := by
  simp [simMarkBlock]

lemma simMarkBlock_getD (b : List (Option Bool)) :
    (simMarkBlock b).map (Option.getD · false) =
      b.map (Option.getD · false) := by
  simp [simMarkBlock, simMarkCell_getD]

lemma simMarkBlock_marked (b : List (Option Bool)) :
    BlockMarked (simMarkBlock b) := by
  intro x hx
  simp only [simMarkBlock, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  cases h : y with
  | none => simp [simMarkCell]
  | some b => simp [simMarkCell]

lemma blockDecodes_mark {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {b : List (Option Bool)} {a : Γ}
    (h : BlockDecodes e b a) :
    BlockDecodes e (simMarkBlock b) a := by
  rcases h with ⟨hb, ha⟩
  have hlen : (simMarkBlock b).length = e.n := by simp [simMarkBlock, hb]
  refine ⟨hlen, ?_⟩
  have hblen : (b.map (Option.getD · false)).length = e.n := by
    simp [hb]
  have hmlen : ((simMarkBlock b).map (Option.getD · false)).length = e.n := by
    simp [simMarkBlock, hb]
  have hv :
      (⟨(simMarkBlock b).map (Option.getD · false), hmlen⟩ :
        List.Vector Bool e.n) =
      ⟨b.map (Option.getD · false), hblen⟩ := by
    apply List.Vector.eq
    exact simMarkBlock_getD b
  rw [hv]
  exact ha


end NPComplete.CookLevin

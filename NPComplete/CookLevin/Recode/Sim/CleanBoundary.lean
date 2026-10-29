module

public import NPComplete.CookLevin.Recode.Sim.CleanPhases

/-! The clean move macro has a deterministic endpoint tape, including the marker
written at the destination.  Making that tape explicit lets the tape relation
track the exact result of the macro and preserve its destination-marker
invariant. -/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

def simCleanPartialMoveTarget {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (old : List (Option Bool))
    (L R : ListBlank (Option Bool)) (d : Dir) : Tape (Option Bool) :=
  let oldM := simMarkBlock old
  let T₂ :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  let Trew := (Tape.move Dir.left)^[e.n] T₂
  let Tdest := (Tape.move d)^[e.n] Trew
  Tdest.write (simMarkCell Tdest.head)

def simCleanPartialWriteTail {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (old : List (Option Bool))
    (L R : ListBlank (Option Bool)) : ListBlank (Option Bool) :=
  let oldM := simMarkBlock old
  let T₂ :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  T₂.right₀

lemma simCleanPartialWriteTail_eq {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (old : List (Option Bool))
    (L R : ListBlank (Option Bool)) (hold : old.length = e.n) :
    simCleanPartialWriteTail e old L R =
      R.tail.cons (simMarkCell R.head) := by
  let oldM : List (Option Bool) := simMarkBlock old
  have holdM : oldM.length = e.n := by
    simp [oldM, simMarkBlock_length, hold]
  change
    (((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)).right₀ =
      R.tail.cons (simMarkCell R.head)
  rw [← holdM, tape_move_right_block oldM L R]
  simp [Tape.write_mk']

lemma simCleanPartialWriteTail_blank {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} (old : List (Option Bool))
    (L : ListBlank (Option Bool)) (hold : old.length = e.n)
    (hn : 0 < e.n) :
    simCleanPartialWriteTail e old L
        (ListBlank.mk (List.replicate e.n none)) =
      ListBlank.mk [some false] := by
  rw [simCleanPartialWriteTail_eq e old L
    (ListBlank.mk (List.replicate e.n none)) hold]
  rw [ListBlank.tail_mk, ListBlank.head_mk, ListBlank.cons_mk]
  have hhead : (List.replicate e.n (none : Option Bool)).headI = none := by
    cases hN : e.n with
    | zero => omega
    | succ n => simp [List.replicate_succ, List.headI]
  rw [hhead]
  rw [show simMarkCell (none : Option Bool) = some false by
    simp [simMarkCell]]
  have htail := listBlank_mk_append_all_none
    ([some false] : List (Option Bool))
    (List.replicate (e.n - 1) none) (by
      intro x hx
      simp at hx
      exact hx.2)
  simpa using htail

lemma simCleanPartialMoveTarget_right_eq {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (old : List (Option Bool))
    (L R : ListBlank (Option Bool)) (hold : old.length = e.n) :
    simCleanPartialMoveTarget e old L R Dir.right =
      Tape.mk' (ListBlank.append (simMarkBlock old).reverse L)
        (simCleanPartialWriteTail e old L R) := by
  let oldM : List (Option Bool) := simMarkBlock old
  have holdM : oldM.length = e.n := by
    simp [oldM, simMarkBlock_length, hold]
  let T₂ : Tape (Option Bool) :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  let R' : ListBlank (Option Bool) := T₂.right₀
  let Trew : Tape (Option Bool) := (Tape.move Dir.left)^[e.n] T₂
  have hT₂ : T₂ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
    calc
      T₂ = Tape.mk' T₂.left T₂.right₀ := (Tape.mk'_left_right₀ T₂).symm
      _ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
        congr 1
        simp [T₂, ← holdM, tape_move_right_block oldM L R]
  have hshape : Trew = Tape.mk' L (ListBlank.append oldM R') := by
    calc
      Trew = (Tape.move Dir.left)^[e.n] T₂ := rfl
      _ = (Tape.move Dir.left)^[e.n]
          (Tape.mk' (ListBlank.append oldM.reverse L) R') := by rw [hT₂]
      _ = Tape.mk' L (ListBlank.append oldM R') := by
        rw [← holdM, tape_move_left_block]
  change
    ((Tape.move Dir.right)^[e.n] Trew).write
        (simMarkCell ((Tape.move Dir.right)^[e.n] Trew).head) =
      Tape.mk' (ListBlank.append oldM.reverse L) R'
  rw [hshape, ← holdM, tape_move_right_block]
  rw [Tape.write_mk']
  have hR' : R' = R.tail.cons (simMarkCell R.head) := by
    change simCleanPartialWriteTail e old L R = _
    exact simCleanPartialWriteTail_eq e old L R hold
  rw [hR']
  simp [simMarkCell_idem]

lemma simCleanPartialMoveTarget_left_eq {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (old : List (Option Bool))
    (L₀ : ListBlank (Option Bool)) (b₀ : List (Option Bool))
    (L : ListBlank (Option Bool)) (R : ListBlank (Option Bool))
    (hb₀ : b₀.length = e.n)
    (hL : L = ListBlank.append b₀.reverse L₀)
    (hold : old.length = e.n) (hn : 0 < e.n) :
    simCleanPartialMoveTarget e old L R Dir.left =
      Tape.mk' L₀
        (ListBlank.append (simMarkCell b₀.headI :: b₀.tail)
            (ListBlank.append (simMarkBlock old)
            (simCleanPartialWriteTail e old L R))) := by
  have hb₀ne : b₀ ≠ [] := by
    intro hnil
    simp [hnil] at hb₀
    exact (by omega)
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₀ne
  let oldM : List (Option Bool) := simMarkBlock old
  have holdM : oldM.length = e.n := by
    simp [oldM, simMarkBlock_length, hold]
  let T₂ : Tape (Option Bool) :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  let R' : ListBlank (Option Bool) := T₂.right₀
  let Trew : Tape (Option Bool) := (Tape.move Dir.left)^[e.n] T₂
  have hT₂ : T₂ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
    calc
      T₂ = Tape.mk' T₂.left T₂.right₀ := (Tape.mk'_left_right₀ T₂).symm
      _ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
        congr 1
        simp [T₂, ← holdM, tape_move_right_block oldM L R]
  have hshape : Trew = Tape.mk' L (ListBlank.append oldM R') := by
    calc
      Trew = (Tape.move Dir.left)^[e.n] T₂ := rfl
      _ = (Tape.move Dir.left)^[e.n]
          (Tape.mk' (ListBlank.append oldM.reverse L) R') := by rw [hT₂]
      _ = Tape.mk' L (ListBlank.append oldM R') := by
        rw [← holdM, tape_move_left_block]
  change
    ((Tape.move Dir.left)^[e.n] Trew).write
        (simMarkCell ((Tape.move Dir.left)^[e.n] Trew).head) = _
  rw [hshape, hL, ← hb₀, tape_move_left_block]
  rw [Tape.write_mk']
  have hR'eq : R' = simCleanPartialWriteTail e old L R := by
    rfl
  rw [hR'eq]
  have htail := simCleanPartialWriteTail_eq e old L R hold
  rw [htail]
  have htail' := simCleanPartialWriteTail_eq e old
    (ListBlank.append (z :: zs).reverse L₀) R hold
  rw [htail']
  simp [oldM, ListBlank.append]

lemma simCleanPartialMoveTarget_left_blank_eq {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (old : List (Option Bool))
    (L : ListBlank (Option Bool)) (R : ListBlank (Option Bool))
    (hL : L = ListBlank.mk []) (hold : old.length = e.n)
    (hn : 0 < e.n) :
    simCleanPartialMoveTarget e old L R Dir.left =
      Tape.mk' (ListBlank.mk [])
        (ListBlank.append
          (some false :: List.replicate (e.n - 1) none)
          (ListBlank.append (simMarkBlock old)
            (simCleanPartialWriteTail e old L R))) := by
  let b₀ : List (Option Bool) := List.replicate e.n none
  have hb₀ : b₀.length = e.n := by simp [b₀]
  have hLb : L = ListBlank.append b₀.reverse (ListBlank.mk []) := by
    rw [hL]
    have hblank : ListBlank.mk b₀.reverse = ListBlank.mk [] := by
      apply listBlank_mk_append_all_none [] b₀.reverse
      intro z hz
      simp [b₀] at hz
      exact hz.2
    simpa [ListBlank.append] using hblank.symm
  have h := simCleanPartialMoveTarget_left_eq e old (ListBlank.mk []) b₀ L R
    hb₀ hLb hold hn
  rw [h]
  have hhead : b₀.headI = none := by
    cases hN : e.n with
    | zero => omega
    | succ n => simp [b₀, hN, List.headI, List.replicate_succ]
  have hmark : simMarkCell b₀.headI = some false := by
    rw [hhead]
    simp [simMarkCell]
  rw [hmark]
  simp [b₀, ListBlank.append]


end NPComplete.CookLevin

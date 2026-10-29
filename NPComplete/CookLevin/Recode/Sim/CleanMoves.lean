module

public import NPComplete.CookLevin.Recode.Sim.CleanPartialMacros

/-!
# Clean Simulation Moves

The local move macro is independent of whether adjacent source regions are represented by data or
quotient blanks, but tape invariants must account for both cases. This module supplies clean-relation
wrappers for those endpoints, allowing statement-level simulation to use a uniform move result.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_move_right_rawTapeCleanRel {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a x : Γ)
    (l r : List Γ) (bl br : List (List (Option Bool)))
    (old b₂ : List (Option Bool))
    (L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l)
      (ListBlank.mk (a :: x :: r)))
    (hU : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight br))))
    (hL : L = ListBlank.mk (rawBlocksLeft bl))
    (hbl : RawBlocksRel e bl l) (hbr : RawBlocksRel e br r)
    (hblm : BlocksMarked bl)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hb₂ : BlockDecodes e b₂ x)
    (hm : M q a = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.right) U' := by
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (z :: zs ++ rawBlocksRight br)
  obtain ⟨bits, U', hbits, hsteps, hU'⟩ :=
    simCleanMachine_partial_move_macro M e q q' a old L R
      Dir.right hold hdec hm hn
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) := by
    simpa [R, hU, ListBlank.append] using hsteps
  have htarget := simCleanPartialMoveTarget_right_eq e old L R hold
  have hRtail : simCleanPartialWriteTail e old L R =
      ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br) := by
    rw [simCleanPartialWriteTail_eq e old L R hold]
    simp [R]
  have hUshape : U' = Tape.mk'
      (ListBlank.append (simMarkBlock old).reverse L)
      (ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br)) := by
    rw [hU', htarget, hRtail]
  have holdDec : BlockDecodes e old a := ⟨hold, hdec⟩
  have hnext : BlockDecodes e ([simMarkCell z] ++ zs) x := by
    apply blockDecodes_congr hb₂
    · simp only [List.length_cons, List.length_append,
        List.length_nil, Nat.zero_add]
      omega
    · simp [simMarkCell_getD]
  refine ⟨bits, U', hbits, hsteps', ?_⟩
  refine ⟨a :: l, r, simMarkBlock old :: bl, br, x,
    [simMarkCell z] ++ zs, ?_, ?_, ?_, hbr, hnext, ?_⟩
  · rw [hT]
    simp [Tape.move, Tape.mk']
  · rw [hUshape, hL]
    simp [rawBlocksLeft]
  · exact RawBlocksRel.cons (blockDecodes_mark holdDec) hbl
  · exact blocksMarked_cons.mpr ⟨simMarkBlock_marked old, hblm⟩

lemma simCleanMachine_move_right_rawTapeCleanRel_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (l : List Γ) (bl : List (List (Option Bool)))
    (old : List (Option Bool))
    (L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk [a]))
    (hU : U = Tape.mk' L (ListBlank.append old (ListBlank.mk [])))
    (hL : L = ListBlank.mk (rawBlocksLeft bl))
    (hbl : RawBlocksRel e bl l) (hblm : BlocksMarked bl)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.right) U' := by
  let b₂ : List (Option Bool) := List.replicate e.n none
  have hb₂ : BlockDecodes e b₂ (default : Γ) := by
    simpa [b₂] using blockDecodes_default e
  have hTfull : T = Tape.mk' (ListBlank.mk l)
      (ListBlank.mk (a :: (default : Γ) :: [])) := by
    rw [hT]
    have htail : ListBlank.mk ([a] : List Γ) =
        ListBlank.mk [a, default] := by
      symm
      apply listBlank_mk_append_all_none [a] [default]
      intro z hz
      simp at hz
      exact hz
    simpa using congrArg (fun R => Tape.mk' (ListBlank.mk l) R) htail
  have hUfull : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight []))) := by
    rw [hU]
    have hblank : ListBlank.mk (old ++ b₂) = ListBlank.mk old := by
      apply listBlank_mk_append_all_none old b₂
      intro z hz
      simp [b₂] at hz
      exact hz.2
    simp [b₂, rawBlocksRight, hblank]
  exact simCleanMachine_move_right_rawTapeCleanRel M e q q' a default l [] bl []
    old b₂ L T U hTfull hUfull hL hbl RawBlocksRel.nil hblm
    hold hdec hb₂ hm hn

lemma simCleanMachine_move_left_rawTapeCleanRel_nonempty {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a x y : Γ)
    (xs r : List Γ) (bl br : List (List (Option Bool)))
    (b₀ b₂ old : List (Option Bool))
    (L₀ L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk (x :: xs))
      (ListBlank.mk (a :: y :: r)))
    (hL₀ : L₀ = ListBlank.mk (rawBlocksLeft bl))
    (hL : L = ListBlank.append b₀.reverse L₀)
    (hU : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight br))))
    (hbl : RawBlocksRel e bl xs) (hbr : RawBlocksRel e br r)
    (hb₀ : BlockDecodes e b₀ x) (hb₀m : BlockMarked b₀)
    (hblm : BlocksMarked bl)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hb₂ : BlockDecodes e b₂ y)
    (hm : M q a = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.left) U' := by
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (z :: zs ++ rawBlocksRight br)
  obtain ⟨bits, U', hbits, hsteps, hU'⟩ :=
    simCleanMachine_partial_move_macro M e q q' a old L R
      Dir.left hold hdec hm hn
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) := by
    simpa [R, hU, ListBlank.append] using hsteps
  have htarget := simCleanPartialMoveTarget_left_eq e old L₀ b₀ L R
    (blockDecodes_length hb₀) hL hold hn
  have hRtail : simCleanPartialWriteTail e old L R =
      ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br) := by
    rw [simCleanPartialWriteTail_eq e old L R hold]
    simp [R]
  have hUshape : U' = Tape.mk' L₀
      (ListBlank.append (simMarkCell b₀.headI :: b₀.tail)
        (ListBlank.append (simMarkBlock old)
          (ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br)))) := by
    rw [hU', htarget, hRtail]
  have hcur : BlockDecodes e
      (simMarkCell b₀.headI :: b₀.tail) x := by
    cases b₀ with
    | nil =>
        have hb₀len := blockDecodes_length hb₀
        simp at hb₀len
        omega
    | cons y ys =>
        apply blockDecodes_congr hb₀
        · simp
        · simp [simMarkCell_getD]
  have hright : RawBlocksRel e
      (simMarkBlock old :: (simMarkCell z :: zs) :: br) (a :: y :: r) := by
    exact RawBlocksRel.cons (blockDecodes_mark ⟨hold, hdec⟩)
      (RawBlocksRel.cons (blockDecodes_congr hb₂
        (by simp) (by simp [simMarkCell_getD])) hbr)
  refine ⟨bits, U', hbits, hsteps', ?_⟩
  let bcur : List (Option Bool) := simMarkCell b₀.headI :: b₀.tail
  have hbcur : BlockDecodes e bcur x := by
    exact hcur
  refine ⟨xs, a :: y :: r, bl,
    simMarkBlock old :: (simMarkCell z :: zs) :: br, x, bcur,
    ?_, ?_, hbl, hright, hbcur, hblm⟩
  · rw [hT]
    simp [Tape.move, Tape.mk']
  · rw [hUshape, hL₀]
    simp [bcur, rawBlocksLeft, rawBlocksRight_cons, ListBlank.append]

/-! Moving left from the first source cell creates a quotient-blank block on
    the target's left.  The first cell of that block is still the physical
    marker, so the ordinary clean relation uses a marked prefix of length one
    and an unmarked default suffix. -/

lemma simCleanMachine_move_left_rawTapeCleanRel_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a y : Γ)
    (r : List Γ) (br : List (List (Option Bool)))
    (b₂ old : List (Option Bool))
    (L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (a :: y :: r)))
    (hL : L = ListBlank.mk [])
    (hU : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight br))))
    (hbr : RawBlocksRel e br r)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hb₂ : BlockDecodes e b₂ y)
    (hm : M q a = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.left) U' := by
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (z :: zs ++ rawBlocksRight br)
  have hU' : U = Tape.mk' L (ListBlank.append old R) := by
    simp [R, hU]
  obtain ⟨bits, U', hbits, hsteps, htarget⟩ :=
    simCleanMachine_partial_move_macro M e q q' a old L R
      Dir.left hold hdec hm hn
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) := by
    rw [hU']
    exact hsteps
  have htarget' := simCleanPartialMoveTarget_left_blank_eq e old L R hL
    hold hn
  have hRtail : simCleanPartialWriteTail e old L R =
      ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br) := by
    rw [simCleanPartialWriteTail_eq e old L R hold]
    simp [R]
  have hshape : U' = Tape.mk' (ListBlank.mk [])
      (ListBlank.append
        (some false :: List.replicate (e.n - 1) none)
        (ListBlank.append (simMarkBlock old)
          (ListBlank.mk (simMarkCell z :: zs ++ rawBlocksRight br)))) := by
    rw [htarget, htarget', hRtail]
  let blank : List (Option Bool) :=
    some false :: List.replicate (e.n - 1) none
  have hblankLen : blank.length = e.n := by
    have hne : 1 ≤ e.n := by omega
    simpa [blank] using (Nat.sub_add_cancel hne)
  have hblankDec : BlockDecodes e blank (default : Γ) := by
    apply blockDecodes_congr (blockDecodes_default e)
    · simpa using hblankLen
    · have hn' : e.n = (e.n - 1) + 1 := by omega
      rw [hn']
      simp [blank, List.replicate_succ]
  have hbr' : RawBlocksRel e
      (simMarkBlock old :: (simMarkCell z :: zs) :: br) (a :: y :: r) := by
    exact RawBlocksRel.cons (blockDecodes_mark ⟨hold, hdec⟩)
      (RawBlocksRel.cons (blockDecodes_congr hb₂ (by simp) (by
        simp [simMarkCell_getD])) hbr)
  have hsource : T.move Dir.left = Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (default :: a :: y :: r)) := by
    rw [hT]
    simp [Tape.move, Tape.mk']
  refine ⟨bits, U', hbits, hsteps', ?_⟩
  rw [hsource, hshape]
  refine ⟨[], a :: y :: r, [],
    simMarkBlock old :: (simMarkCell z :: zs) :: br,
    default, blank, ?_, ?_, RawBlocksRel.nil, hbr', hblankDec,
    blocksMarked_nil⟩
  · simp
  · simp [blank, rawBlocksLeft, rawBlocksRight, ListBlank.append]

/-! A trailing default source cell supplies the right-neighbour block needed
    by the nonempty left-move macro.  It is only a representative change: the
    source tape and the target tape are unchanged as `ListBlank` quotients. -/

lemma simCleanMachine_move_left_rawTapeCleanRel_right_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a x : Γ)
    (xs : List Γ) (bl : List (List (Option Bool)))
    (b₀ old : List (Option Bool))
    (L₀ L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk (x :: xs))
      (ListBlank.mk [a]))
    (hL₀ : L₀ = ListBlank.mk (rawBlocksLeft bl))
    (hL : L = ListBlank.append b₀.reverse L₀)
    (hU : U = Tape.mk' L (ListBlank.append old (ListBlank.mk [])))
    (hbl : RawBlocksRel e bl xs)
    (hb₀ : BlockDecodes e b₀ x) (hb₀m : BlockMarked b₀)
    (hblm : BlocksMarked bl)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.left) U' := by
  let b₂ : List (Option Bool) := List.replicate e.n none
  have hb₂ : BlockDecodes e b₂ (default : Γ) := by
    simpa [b₂] using blockDecodes_default e
  have hTfull : T = Tape.mk' (ListBlank.mk (x :: xs))
      (ListBlank.mk (a :: (default : Γ) :: [])) := by
    rw [hT]
    have htail : ListBlank.mk ([a] : List Γ) =
        ListBlank.mk [a, default] := by
      symm
      apply listBlank_mk_append_all_none [a] [default]
      intro z hz
      simp at hz
      exact hz
    simpa using congrArg (fun R => Tape.mk' (ListBlank.mk (x :: xs)) R) htail
  have hUfull : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight []))) := by
    rw [hU]
    have hblank : ListBlank.mk (old ++ b₂) = ListBlank.mk old := by
      apply listBlank_mk_append_all_none old b₂
      intro z hz
      simp [b₂] at hz
      exact hz.2
    simp [b₂, rawBlocksRight, hblank]
  exact simCleanMachine_move_left_rawTapeCleanRel_nonempty M e q q' a x default
    xs [] bl [] b₀ b₂ old L₀ L T U hTfull hL₀ hL hUfull
    hbl RawBlocksRel.nil hb₀ hb₀m hblm hold hdec hb₂ hm hn

/-! The completely empty source neighbourhood is the same representative
    argument with a quotient-blank block on the left as well. -/

lemma simCleanMachine_move_left_rawTapeCleanRel_both_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (old : List (Option Bool))
    (L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk []) (ListBlank.mk [a]))
    (hU : U = Tape.mk' L (ListBlank.append old (ListBlank.mk [])))
    (hL : L = ListBlank.mk [])
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      RawTapeCleanRel e (T.move Dir.left) U' := by
  let b₂ : List (Option Bool) := List.replicate e.n none
  have hb₂ : BlockDecodes e b₂ (default : Γ) := by
    simpa [b₂] using blockDecodes_default e
  have hTfull : T = Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (a :: (default : Γ) :: [])) := by
    rw [hT]
    have htail : ListBlank.mk ([a] : List Γ) =
        ListBlank.mk [a, default] := by
      symm
      apply listBlank_mk_append_all_none [a] [default]
      intro z hz
      simp at hz
      exact hz
    simpa using congrArg (fun R => Tape.mk' (ListBlank.mk []) R) htail
  have hUfull : U = Tape.mk' L
      (ListBlank.append old (ListBlank.mk (b₂ ++ rawBlocksRight []))) := by
    rw [hU]
    have hblank : ListBlank.mk (old ++ b₂) = ListBlank.mk old := by
      apply listBlank_mk_append_all_none old b₂
      intro z hz
      simp [b₂] at hz
      exact hz.2
    simp [b₂, rawBlocksRight, hblank]
  exact simCleanMachine_move_left_rawTapeCleanRel_blank M e q q' a default [] []
    b₂ old L T U hTfull hL hUfull RawBlocksRel.nil
    hold hdec hb₂ hm hn


end NPComplete.CookLevin

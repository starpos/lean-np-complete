module

public import NPComplete.CookLevin.Recode.Sim.CleanBoundary

/-!
# Clean Partial-Block Macros

Cleaning a raw tape requires preserving the decoded symbol while marking each cell of the current
block before writing or moving. This module proves the shared partial-block macros and occupancy
variants, leaving endpoint-specific tape layouts to the wrapper lemmas.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_partial_write_macro {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s a : Γ)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.write s)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ R' : ListBlank (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'),
          Tape.mk' L (ListBlank.append ((e.enc s).toList.map some) R')⟩
        (6 * e.n + 4) ∧
      R' = simCleanPartialWriteTail e old L R := by
  obtain ⟨bits, hbits, hread⟩ := simCleanMachine_read_rewind_any M e q
    old L R hold hn
  let oldM : List (Option Bool) := simMarkBlock old
  have holdM : oldM.length = e.n := by
    simp [oldM, simMarkBlock_length, hold]
  let T₂ : Tape (Option Bool) :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  let R' : ListBlank (Option Bool) := simCleanPartialWriteTail e old L R
  let Trew : Tape (Option Bool) := (Tape.move Dir.left)^[e.n] T₂
  have hread' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      (3 * e.n + 2) := by
    simpa [Trew, T₂, oldM] using hread
  have hshape : Trew = Tape.mk' L (ListBlank.append oldM R') := by
    have hT₂ : T₂ = Tape.mk'
        (ListBlank.append oldM.reverse L) R' := by
      calc
        T₂ = Tape.mk' T₂.left T₂.right₀ :=
          (Tape.mk'_left_right₀ T₂).symm
        _ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
          congr 1
          simp [T₂, ← holdM, tape_move_right_block oldM L R]
    calc
      Trew = (Tape.move Dir.left)^[e.n] T₂ := rfl
      _ = (Tape.move Dir.left)^[e.n]
          (Tape.mk' (ListBlank.append oldM.reverse L) R') := by rw [hT₂]
      _ = Tape.mk' L (ListBlank.append oldM R') := by
        rw [← holdM, tape_move_left_block]
  have hhead : (Tape.mk' L (ListBlank.append oldM R')).head.isSome := by
    rw [Tape.mk'_head]
    cases old with
    | nil => simp at hold; omega
    | cons x xs =>
        have hmem : (ListBlank.append oldM R').head ∈ oldM := by
          simp [oldM, simMarkBlock, ListBlank.append]
        exact simMarkBlock_marked (x :: xs) _ hmem
  have hbits_eq : e.dec bits = a := by
    have hv : bits =
        (⟨old.map (Option.getD · false), by simp [hold]⟩ :
          List.Vector Bool e.n) := by
      apply List.Vector.eq
      exact hbits
    rw [hv]
    exact hdec
  have hzero := simCleanMachine_rewind_zero_write_step M e q q' bits s
    (Tape.mk' L (ListBlank.append oldM R')) hn hhead
    (by simpa [hbits_eq] using hm)
  have hzero' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      ⟨.run (.write q' ⟨0, Nat.zero_lt_succ _⟩ (e.enc s)), Trew⟩ 1 := by
    rw [← hshape] at hzero
    exact stepsTo_cons _ hzero (stepsTo_zero _ _)
  have hwrite := simCleanMachine_write_phase M e q' (e.enc s)
    oldM L R' holdM hn
  have hfirst := stepsTo_trans (t₁ := 3 * e.n + 2) (t₂ := 1) _ hread' hzero'
  rw [hshape] at hfirst
  have htotal := stepsTo_trans (t₁ := 1 + (3 * e.n + 2))
    (t₂ := 3 * e.n + 1) _ hfirst hwrite
  refine ⟨bits, R', hbits, ?_, rfl⟩
  convert htotal using 1
  all_goals omega

lemma simCleanMachine_partial_write_macro_occupied {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s a : Γ)
    (old : List (Option Bool))
    (L R : ListBlank (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.write s)) (hn : 0 < e.n)
    (hocc : SimCleanRightTailOccupied e
      (Tape.mk' L (ListBlank.append old R))) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'), U'⟩ (6 * e.n + 4) ∧
      SimCleanRightTailOccupied e U' := by
  obtain ⟨bits, R', hbits, hsteps, hR'eq⟩ :=
    simCleanMachine_partial_write_macro M e q q' s a old L R
      hold hdec hm hn
  have hRocc := simCleanRightTailOccupied_split e L old R
    (Tape.mk' L (ListBlank.append old R)) hold rfl hocc
  have hRtail := simCleanPartialWriteTail_eq e old L R hold
  have hmark : (simMarkCell R.head).isSome := by
    cases R.head <;> simp [simMarkCell]
  have hR'form : R' = R.tail.cons (simMarkCell R.head) := by
    calc
      R' = simCleanPartialWriteTail e old L R := hR'eq
      _ = R.tail.cons (simMarkCell R.head) := hRtail
  have hR'Occ : SimCleanTailOccupied R' := by
    rw [hR'form]
    exact simCleanTailOccupied_append_mark R hRocc (simMarkCell R.head) hmark
  let U' : Tape (Option Bool) :=
    Tape.mk' L (ListBlank.append (rawEncodeBlock e s) R')
  have hnew : (rawEncodeBlock e s).length = e.n := by
    simp [rawEncodeBlock]
  have hshape : U' = Tape.mk' L
      (ListBlank.append (rawEncodeBlock e s) R') := rfl
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.ready q'), U'⟩ (6 * e.n + 4) := by
    rw [hshape]
    simpa [rawEncodeBlock] using hsteps
  have hocc' := simCleanRightTailOccupied_of_split e L
    (rawEncodeBlock e s) R' U' hnew hshape hR'Occ
  exact ⟨bits, U', hbits, hsteps', hocc'⟩

lemma simCleanMachine_write_boundary_nonempty {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s a x : Γ)
    (l r : List Γ) (bl br : List (List (Option Bool)))
    (b₂ old : List (Option Bool))
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
    (hm : M q a = some (q', TM0.Stmt.write s)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (6 * e.n + 4) ∧
      RawTapeCleanBoundaryRel e (T.write s) U' := by
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (z :: zs ++ rawBlocksRight br)
  obtain ⟨bits, R', hbits, hsteps, hR'⟩ :=
    simCleanMachine_partial_write_macro M e q q' s a old L R
      hold hdec hm hn
  have hRtail := simCleanPartialWriteTail_eq e old L R hold
  have hR'form : R' = ListBlank.mk
      (simMarkCell z :: zs ++ rawBlocksRight br) := by
    rw [hR', hRtail]
    simp [R]
  let U' : Tape (Option Bool) :=
    Tape.mk' L (ListBlank.append (rawEncodeBlock e s) R')
  refine ⟨bits, U', hbits, ?_, ?_⟩
  · simpa [rawEncodeBlock, U', R, hU, ListBlank.append] using hsteps
  · have hb₂len' : (z :: zs).length = e.n := hb₂len
    have hdec₂ : BlockDecodes e
        ([simMarkCell z] ++ zs) x := by
      apply blockDecodes_congr hb₂
      · simp only [List.length_cons, List.length_append,
          List.length_nil, Nat.zero_add]
        omega
      · simp [simMarkCell_getD]
    have hmark₂ : BlockMarked [simMarkCell z] := by
      intro y hy
      simp at hy
      subst y
      cases z <;> simp [simMarkCell]
    have hpref_len : 0 < [simMarkCell z].length := by simp
    have hsplit : [simMarkCell z].length + zs.length = e.n := by
      have hlen' : 1 + zs.length = e.n := by
        have h := hb₂len'
        simp only [List.length_cons] at h
        omega
      simp only [List.length_cons,
        List.length_nil, Nat.zero_add]
      exact hlen'
    refine ⟨l, r, bl, br, s, x, rawEncodeBlock e s,
      [simMarkCell z], zs, ?_, ?_, hbl, hbr,
      rawEncodeBlock_decodes e s, blockMarked_rawEncodeBlock e s,
      hblm, hdec₂, hpref_len, hsplit, hmark₂⟩
    · rw [hT]
      simp [Tape.mk']
    · dsimp [U']
      rw [hL, hR'form]
      simp [rawBlocksLeft, rawBlocksRight, List.append_assoc]

/-! The blank-right write case is obtained by exposing one quotient-trailing
    default block.  This keeps the machine macro unchanged while giving the
    clean relation the boundary cell it records. -/

lemma simCleanMachine_write_boundary_blank_general {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s a : Γ)
    (l : List Γ) (bl : List (List (Option Bool)))
    (old : List (Option Bool))
    (L : ListBlank (Option Bool)) (T : Tape Γ) (U : Tape (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk [a]))
    (hU : U = Tape.mk' L (ListBlank.append old (ListBlank.mk [])))
    (hL : L = ListBlank.mk (rawBlocksLeft bl))
    (hbl : RawBlocksRel e bl l) (hblm : BlocksMarked bl)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.write s)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (6 * e.n + 4) ∧
      RawTapeCleanBoundaryRel e (T.write s) U' := by
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
  exact simCleanMachine_write_boundary_nonempty M e q q' s a default l [] bl []
    b₂ old L T U hTfull hUfull hL hbl RawBlocksRel.nil hblm
    hold hdec hb₂ hm hn

lemma simCleanMachine_partial_move_macro {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool)) (d : Dir)
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move d)) (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      U' = simCleanPartialMoveTarget e old L R d := by
  obtain ⟨bits, hbits, hread⟩ := simCleanMachine_read_rewind_any M e q
    old L R hold hn
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
  have hread' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      (3 * e.n + 2) := by
    simpa [Trew, T₂, oldM] using hread
  have hshape : Trew = Tape.mk' L (ListBlank.append oldM R') := by
    have hT₂ : T₂ = Tape.mk'
        (ListBlank.append oldM.reverse L) R' := by
      calc
        T₂ = Tape.mk' T₂.left T₂.right₀ :=
          (Tape.mk'_left_right₀ T₂).symm
        _ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
          congr 1
          simp [T₂, ← holdM, tape_move_right_block oldM L R]
    calc
      Trew = (Tape.move Dir.left)^[e.n] T₂ := rfl
      _ = (Tape.move Dir.left)^[e.n]
          (Tape.mk' (ListBlank.append oldM.reverse L) R') := by rw [hT₂]
      _ = Tape.mk' L (ListBlank.append oldM R') := by
        rw [← holdM, tape_move_left_block]
  have hhead : (Tape.mk' L (ListBlank.append oldM R')).head.isSome := by
    rw [Tape.mk'_head]
    cases old with
    | nil => simp at hold; omega
    | cons x xs =>
        have hmem : (ListBlank.append oldM R').head ∈ oldM := by
          simp [oldM, simMarkBlock, ListBlank.append]
        exact simMarkBlock_marked (x :: xs) _ hmem
  have hbits_eq : e.dec bits = a := by
    have hv : bits =
        (⟨old.map (Option.getD · false), by simp [hold]⟩ :
          List.Vector Bool e.n) := by
      apply List.Vector.eq
      exact hbits
    rw [hv]
    exact hdec
  have hzero := simCleanMachine_rewind_zero_move_step M e q q' bits d
    (Tape.mk' L (ListBlank.append oldM R')) hn hhead
    (by simpa [hbits_eq] using hm)
  have hzero' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      ⟨.run (.move q' d ⟨e.n, Nat.lt_succ_self _⟩), Trew⟩ 1 := by
    rw [← hshape] at hzero
    exact stepsTo_cons _ hzero (stepsTo_zero _ _)
  have hmove := simCleanMachine_move_walk M e q' d Trew e.n
    (Nat.lt_succ_self _)
  let Tdest : Tape (Option Bool) := (Tape.move d)^[e.n] Trew
  have hmove' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.move q' d ⟨e.n, Nat.lt_succ_self _⟩), Trew⟩
      ⟨.run (.move q' d ⟨0, Nat.zero_lt_succ _⟩), Tdest⟩ e.n := by
    simpa [Tdest] using hmove
  have hzero2 := simCleanMachine_move_zero_mark_step M e q' d Tdest
  let U' : Tape (Option Bool) := simCleanPartialMoveTarget e old L R d
  have hzero2' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.move q' d ⟨0, Nat.zero_lt_succ _⟩), Tdest⟩
      ⟨.run (.ready q'), U'⟩ 1 := by
    simpa [U', simCleanPartialMoveTarget, Tdest, T₂, Trew, oldM] using
      (stepsTo_cons _ hzero2 (stepsTo_zero _ _))
  have hfirst := stepsTo_trans (t₁ := 3 * e.n + 2) (t₂ := 1) _ hread' hzero'
  have hsecond := stepsTo_trans (t₁ := 1 + (3 * e.n + 2)) (t₂ := e.n) _ hfirst hmove'
  have htotal := stepsTo_trans (t₁ := e.n + (1 + (3 * e.n + 2))) (t₂ := 1) _
    hsecond hzero2'
  refine ⟨bits, U', hbits, ?_, rfl⟩
  convert htotal using 1
  all_goals omega

lemma simCleanMachine_partial_move_right_macro_occupied {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (old : List (Option Bool))
    (L R : ListBlank (Option Bool)) (b₂ Rtail : List (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n)
    (hb₂ : b₂.length = e.n)
    (hR : R = ListBlank.append b₂ (ListBlank.mk Rtail))
    (hRtail : ∀ x ∈ Rtail, x.isSome) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      SimCleanRightTailOccupied e U' := by
  obtain ⟨bits, U', hbits, hsteps, hU'⟩ :=
    simCleanMachine_partial_move_macro M e q q' a old L R
      Dir.right hold hdec hm hn
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  have htarget := simCleanPartialMoveTarget_right_eq e old L R hold
  have hRtail' := simCleanPartialWriteTail_eq e old L R hold
  have hR'form : simCleanPartialWriteTail e old L R =
      ListBlank.append (simMarkCell z :: zs) (ListBlank.mk Rtail) := by
    rw [hRtail']
    rw [hR]
    simp [ListBlank.append]
  have hbnew : (simMarkCell z :: zs).length = e.n := by
    simpa [simMarkCell] using hb₂
  let U'' : Tape (Option Bool) :=
    Tape.mk' (ListBlank.append (simMarkBlock old).reverse L)
      (ListBlank.append (simMarkCell z :: zs) (ListBlank.mk Rtail))
  have hU'' : U' = U'' := by
    rw [hU', htarget, hR'form]
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.ready q'), U''⟩ (4 * e.n + 4) := by
    rw [← hU'']
    exact hsteps
  have hocc' := simCleanRightTailOccupied_of_split e
    (ListBlank.append (simMarkBlock old).reverse L)
    (simMarkCell z :: zs) (ListBlank.mk Rtail) U'' hbnew rfl
    (simCleanTailOccupied_mk Rtail hRtail)
  exact ⟨bits, U'', hbits, hsteps', hocc'⟩

lemma simCleanMachine_partial_move_right_macro_occupied_of_tail
    {Γ Λ : Type} [Inhabited Γ] [Finite Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (old : List (Option Bool))
    (L R : ListBlank (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n)
    (hR : SimCleanTailOccupied R) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      SimCleanRightTailOccupied e U' := by
  obtain ⟨b₂, Rtail, hb₂, hR', hRtail⟩ :=
    simCleanTailOccupied_split_block R hR
  exact simCleanMachine_partial_move_right_macro_occupied M e q q' a
    old L R b₂ Rtail hold hdec hm hn hb₂ hR' hRtail

lemma simCleanMachine_partial_move_left_macro_occupied {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (a : Γ)
    (old : List (Option Bool))
    (b₀ : List (Option Bool))
    (L₀ L R : ListBlank (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n)
    (hb₀ : b₀.length = e.n)
    (hL : L = ListBlank.append b₀.reverse L₀)
    (hR : SimCleanTailOccupied R) :
    ∃ bits : List.Vector Bool e.n, ∃ U' : Tape (Option Bool),
      bits.toList = old.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.ready q'), U'⟩ (4 * e.n + 4) ∧
      SimCleanRightTailOccupied e U' := by
  cases b₀ with
  | nil =>
      simp at hb₀
      omega
  | cons z zs =>
      have hbcur : (simMarkCell z :: zs).length = e.n := by
        simpa [simMarkCell] using hb₀
      obtain ⟨bits, U', hbits, hsteps, htarget⟩ :=
        simCleanMachine_partial_move_macro M e q q' a old L R
          Dir.left hold hdec hm hn
      have htarget' := simCleanPartialMoveTarget_left_eq e old L₀ (z :: zs) L R
        hb₀ hL hold hn
      have hRtail := simCleanPartialWriteTail_eq e old L R hold
      have hR' : SimCleanTailOccupied
          (simCleanPartialWriteTail e old L R) := by
        rw [hRtail]
        exact simCleanTailOccupied_append_mark R hR
          (simMarkCell R.head) (by cases R.head <;> simp [simMarkCell])
      have htail : SimCleanTailOccupied
          (ListBlank.append (simMarkBlock old)
            (simCleanPartialWriteTail e old L R)) := by
        apply simCleanTailOccupied_append_prefix
        · exact simMarkBlock_marked old
        · exact hR'
      let U'' : Tape (Option Bool) :=
        Tape.mk' L₀
          (ListBlank.append (simMarkCell z :: zs)
            (ListBlank.append (simMarkBlock old)
              (simCleanPartialWriteTail e old L R)))
      have hU'' : U' = U'' := by
        rw [htarget, htarget']
        simp [U'', List.headI]
      have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
          ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
          ⟨.run (.ready q'), U''⟩ (4 * e.n + 4) := by
        rw [← hU'']
        exact hsteps
      have hocc' := simCleanRightTailOccupied_of_split e L₀
        (simMarkCell z :: zs)
        (ListBlank.append (simMarkBlock old)
          (simCleanPartialWriteTail e old L R)) U'' hbcur rfl htail
      exact ⟨bits, U'', hbits, hsteps', hocc'⟩


end NPComplete.CookLevin

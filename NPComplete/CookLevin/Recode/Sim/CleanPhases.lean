module

public import NPComplete.CookLevin.Recode.Sim.CleanMicrosteps

/-!
# Clean simulator phases

A clean block operation consists of read, rewind, write, and cleanup phases,
each with its own step count and tape effect. This layer proves the phase runs
needed to compose complete simulated steps without exposing the machine's full
transition definition to later arguments.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_read_finish_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (acc : List.Vector Bool e.n)
    (T : Tape (Option Bool)) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.read q ⟨e.n, Nat.lt_succ_self _⟩ acc), T⟩ =
      some ⟨.run (.rewind q ⟨e.n, Nat.lt_succ_self _⟩
          ⟨acc.toList.reverse, by simp [List.Vector.toList_length]⟩),
        T.write (simMarkCell T.head)⟩ := by
  simp [TM0.step, simCleanMachine, simMachine]

lemma simCleanMachine_rewind_pos_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (left : Fin e.n.succ)
    (bits : List.Vector Bool e.n) (T : Tape (Option Bool))
    (h : 0 < left.val) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.rewind q left bits), T⟩ =
      some ⟨.run (.rewind q ⟨left.val - 1, by omega⟩ bits),
        T.move Dir.left⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, h]

lemma simCleanMachine_rewind_walk {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (T : Tape (Option Bool)) :
    ∀ (k : ℕ) (hk : k < e.n.succ),
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.rewind q ⟨k, hk⟩ bits), T⟩
        ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits),
          (Tape.move Dir.left)^[k] T⟩ k := by
  intro k
  induction k generalizing T with
  | zero =>
      intro _
      exact stepsTo_zero _ _
  | succ k ih =>
      intro hk
      have hstep := simCleanMachine_rewind_pos_step M e q
        ⟨k + 1, by omega⟩ bits T (Nat.succ_pos _)
      have hrest := ih (T.move Dir.left) (Nat.lt_of_succ_lt hk)
      refine stepsTo_cons _ hstep ?_
      simpa [Function.iterate_succ_apply] using hrest

lemma simCleanMachine_rewind_zero_write_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (bits : List.Vector Bool e.n)
    (s : Γ) (T : Tape (Option Bool)) (hn : 0 < e.n)
    (hhead : T.head.isSome)
    (hm : M q (e.dec bits) = some (q', TM0.Stmt.write s)) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), T⟩ =
      some ⟨.run (.write q' ⟨0, Nat.zero_lt_succ _⟩ (e.enc s)), T⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, hn, hm, hhead,
    simMarkCell, Tape.write_self]

lemma simCleanMachine_rewind_zero_move_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (bits : List.Vector Bool e.n)
    (d : Dir) (T : Tape (Option Bool)) (hn : 0 < e.n)
    (hhead : T.head.isSome)
    (hm : M q (e.dec bits) = some (q', TM0.Stmt.move d)) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), T⟩ =
      some ⟨.run (.move q' d ⟨e.n, Nat.lt_succ_self _⟩), T⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, hn, hm, hhead,
    simMarkCell, Tape.write_self]

lemma simCleanMachine_rewind_zero_halt_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (T : Tape (Option Bool)) (hhead : T.head.isSome)
    (hm : M q (e.dec bits) = none) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), T⟩ =
      some ⟨.run .done, T⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, hm, hhead,
    simMarkCell, Tape.write_self]

lemma simCleanMachine_write_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (i : Fin e.n.succ)
    (bits : List.Vector Bool e.n) (T : Tape (Option Bool))
    (h : i.val < e.n) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.write q i bits), T⟩ =
      some ⟨.run (.writeMove q i bits),
        T.write (some (bits.get ⟨i.val, h⟩))⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, h, simMarkCell]

lemma simCleanMachine_write_move_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (i : Fin e.n.succ)
    (bits : List.Vector Bool e.n) (T : Tape (Option Bool))
    (h : i.val < e.n) (hi : i.val + 1 < e.n) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.writeMove q i bits), T⟩ =
      some ⟨.run (.write q ⟨i.val + 1, by omega⟩ bits), T.move Dir.right⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, h, hi]

lemma simCleanMachine_write_move_last_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (i : Fin e.n.succ)
    (bits : List.Vector Bool e.n) (T : Tape (Option Bool))
    (h : i.val < e.n) (hi : i.val + 1 = e.n) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.writeMove q i bits), T⟩ =
      some ⟨.run (.writeBack q ⟨e.n, Nat.lt_succ_self _⟩), T.move Dir.right⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, h, hi]

lemma simCleanMachine_writeBack_pos_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (left : Fin e.n.succ)
    (T : Tape (Option Bool)) (h : 0 < left.val) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.writeBack q left), T⟩ =
      some ⟨.run (.writeBack q ⟨left.val - 1, by omega⟩),
        T.move Dir.left⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, h]

lemma simCleanMachine_writeBack_zero_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (T : Tape (Option Bool))
    (hhead : T.head.isSome) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.writeBack q ⟨0, Nat.zero_lt_succ _⟩), T⟩ =
      some ⟨.run (.ready q), T⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, hhead,
    simMarkCell, Tape.write_self]

lemma simCleanMachine_writeBack_walk {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (T : Tape (Option Bool)) :
    ∀ (k : ℕ) (hk : k < e.n.succ),
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.writeBack q ⟨k, hk⟩), T⟩
        ⟨.run (.writeBack q ⟨0, Nat.zero_lt_succ _⟩),
          (Tape.move Dir.left)^[k] T⟩ k := by
  intro k
  induction k generalizing T with
  | zero =>
      intro _
      exact stepsTo_zero _ _
  | succ k ih =>
      intro hk
      have hstep := simCleanMachine_writeBack_pos_step M e q
        ⟨k + 1, by omega⟩ T (Nat.succ_pos _)
      have hrest := ih (T.move Dir.left) (Nat.lt_of_succ_lt hk)
      refine stepsTo_cons _ hstep ?_
      simpa [Function.iterate_succ_apply] using hrest

lemma simCleanMachine_move_walk {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (d : Dir) (T : Tape (Option Bool)) :
    ∀ (k : ℕ) (hk : k < e.n.succ),
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.move q d ⟨k, hk⟩), T⟩
        ⟨.run (.move q d ⟨0, Nat.zero_lt_succ _⟩),
          (Tape.move d)^[k] T⟩ k := by
  intro k
  induction k generalizing T with
  | zero =>
      intro _
      exact stepsTo_zero _ _
  | succ k ih =>
      intro hk
      have hstep : TM0.step (simCleanMachine M e)
          ⟨.run (.move q d ⟨k + 1, by omega⟩), T⟩ =
          some ⟨.run (.move q d ⟨k, by omega⟩), T.move d⟩ := by
        simp [TM0.step, simCleanMachine, simMachine]
      have hrest := ih (T.move d) (Nat.lt_of_succ_lt hk)
      refine stepsTo_cons _ hstep ?_
      simpa [Function.iterate_succ_apply] using hrest

lemma simCleanMachine_move_zero_mark_step {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (d : Dir) (T : Tape (Option Bool)) :
    TM0.step (simCleanMachine M e)
      ⟨.run (.move q d ⟨0, Nat.zero_lt_succ _⟩), T⟩ =
      some ⟨.run (.ready q), T.write (simMarkCell T.head)⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, simMarkCell]

lemma sim_clean_list_drop_exists_cons {Γ : Type} (old : List Γ) (n i : ℕ)
    (hold : old.length = n) (hi : i < n) :
    ∃ x rest, old.drop i = x :: rest := by
  have hlen : 0 < (old.drop i).length := by
    simp [List.length_drop, hold]
    omega
  exact List.exists_cons_of_ne_nil (by
    intro hnil
    simp [hnil] at hlen)

lemma sim_clean_tape_write_move_right_head {Γ : Type} [Inhabited Γ]
    (x y : Γ) (rest : List Γ) (L R : ListBlank Γ) :
    ((Tape.mk' L (ListBlank.append (x :: rest) R)).write y).move Dir.right =
      Tape.mk' (ListBlank.append [y] L) (ListBlank.append rest R) := by
  simp [Tape.write_mk', Tape.move_right_mk', ListBlank.append,
    ListBlank.head_cons, ListBlank.tail_cons]

lemma sim_clean_vector_get_toList {n : ℕ} (bits : List.Vector Bool n) (i : Fin n) :
    bits.toList.getI i.val = bits.get i := by
  rw [List.getI_eq_getElem _ (by simp [List.Vector.toList_length])]
  exact List.Vector.toList_getElem bits i.val

lemma simCleanMachine_write_prefix {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (hold : old.length = e.n) :
    ∀ (i : ℕ), ∀ hi : i < e.n,
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.write q ⟨0, Nat.zero_lt_succ _⟩ bits),
          Tape.mk' L (ListBlank.append old R)⟩
        ⟨.run (.write q ⟨i, Nat.lt_succ_of_lt hi⟩ bits),
          Tape.mk'
            (ListBlank.append ((bits.toList.take i).reverse.map some) L)
            (ListBlank.append (old.drop i) R)⟩ (2 * i) := by
  intro i
  induction i with
  | zero =>
      intro _
      exact stepsTo_zero _ _
  | succ i ih =>
      intro hi
      have hi0 : i < e.n := Nat.lt_of_succ_lt hi
      obtain ⟨x, rest, hdrop⟩ :=
        sim_clean_list_drop_exists_cons old e.n i hold hi0
      have hpref := ih hi0
      have hstep₁ := simCleanMachine_write_step M e q
        ⟨i, by omega⟩ bits
        (Tape.mk'
          (ListBlank.append ((bits.toList.take i).reverse.map some) L)
          (ListBlank.append (old.drop i) R)) (by omega)
      have hstep₂ := simCleanMachine_write_move_step M e q
        ⟨i, by omega⟩ bits
        ((Tape.mk'
          (ListBlank.append ((bits.toList.take i).reverse.map some) L)
          (ListBlank.append (old.drop i) R)).write
            (some (bits.get ⟨i, by omega⟩))) (by omega) (by omega)
      have hpair := stepsTo_cons _ hstep₁
        (stepsTo_cons _ hstep₂ (stepsTo_zero _ _))
      rw [hdrop] at hpair
      rw [hdrop] at hpref
      have hdrop_succ : old.drop (i + 1) = rest := by
        have ht := congrArg List.tail hdrop
        simpa using ht
      have hT :
          ((Tape.mk'
            (ListBlank.append ((bits.toList.take i).reverse.map some) L)
            (ListBlank.append (x :: rest) R)).write
              (some (bits.get ⟨i, by omega⟩))).move Dir.right =
            Tape.mk'
              (ListBlank.append ((bits.toList.take (i + 1)).reverse.map some) L)
              (ListBlank.append (old.drop (i + 1)) R) := by
        rw [sim_clean_tape_write_move_right_head]
        have htake : bits.toList.take (i + 1) =
            bits.toList.take i ++ [bits.toList.getI i] := by
          exact tape_take_succ_getI bits.toList i
            (by simpa using (Nat.lt_of_succ_lt hi))
        rw [htake, ← sim_clean_vector_get_toList bits ⟨i, hi0⟩]
        rw [hdrop_succ]
        simp [List.reverse_append]
      rw [hT] at hpair
      have htotal := stepsTo_trans (t₁ := 2 * i) (t₂ := 2) _ hpref hpair
      convert htotal using 1
      all_goals omega

/-- The final write-and-move restores the full encoded block. -/
lemma sim_clean_write_phase_tape {n : ℕ} (bits : List.Vector Bool n)
    (L R : ListBlank (Option Bool)) (x : Option Bool) (hn : 0 < n) :
    ((Tape.mk'
      (ListBlank.append ((bits.toList.take (n - 1)).reverse.map some) L)
      (ListBlank.append [x] R)).write (some (bits.get ⟨n - 1, by omega⟩))).move Dir.right =
      Tape.mk' (ListBlank.append (bits.toList.reverse.map some) L) R := by
  rw [sim_clean_tape_write_move_right_head]
  rw [← sim_clean_vector_get_toList bits ⟨n - 1, by omega⟩]
  have hpred : n - 1 < n := Nat.sub_one_lt_of_lt hn
  have htake : bits.toList.take n =
      bits.toList.take (n - 1) ++ [bits.toList.getI (n - 1)] := by
    simpa [Nat.sub_add_cancel hn] using
      (tape_take_succ_getI bits.toList (n - 1)
        (by simpa [List.Vector.toList_length] using hpred))
  have hsplit : bits.toList =
      bits.toList.take (n - 1) ++ [bits.toList.getI (n - 1)] := by
    rw [← htake]
    simp [List.Vector.toList_length]
  rw [hsplit]
  have hget :
      (bits.toList.take (n - 1) ++ [bits.toList.getI (n - 1)]).getI
          (n - 1) = bits.toList.getI (n - 1) := by
    rw [List.getI_append_right]
    · simp
    · simp
  rw [hget]
  simp [List.reverse_append]

/-- Reach the final write-back phase after emitting every encoded bit. -/
lemma simCleanMachine_write_phase_prefix {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (hold : old.length = e.n) (hn : 0 < e.n) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.write q ⟨0, Nat.zero_lt_succ _⟩ bits),
        Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.writeBack q ⟨e.n, Nat.lt_succ_self _⟩),
        Tape.mk' (ListBlank.append (bits.toList.reverse.map some) L) R⟩
      (2 * e.n) := by
  have hpred : e.n - 1 < e.n := Nat.sub_one_lt_of_lt hn
  have hp := simCleanMachine_write_prefix M e q bits old L R hold (e.n - 1) hpred
  obtain ⟨x, rest, hdrop⟩ :=
    sim_clean_list_drop_exists_cons old e.n (e.n - 1) hold hpred
  have hlen_drop : (old.drop (e.n - 1)).length = 1 := by
    simp [List.length_drop, hold]
    omega
  have hrest : rest = [] := by
    rw [hdrop] at hlen_drop
    simp at hlen_drop
    exact hlen_drop
  subst rest
  rw [hdrop] at hp
  have hlast : e.n - 1 + 1 = e.n := Nat.sub_add_cancel hn
  have hstep₁ := simCleanMachine_write_step M e q
    ⟨e.n - 1, by omega⟩ bits
    (Tape.mk'
      (ListBlank.append ((bits.toList.take (e.n - 1)).reverse.map some) L)
      (ListBlank.append [x] R)) (by omega)
  have hstep₂ := simCleanMachine_write_move_last_step M e q
    ⟨e.n - 1, by omega⟩ bits
    ((Tape.mk'
      (ListBlank.append ((bits.toList.take (e.n - 1)).reverse.map some) L)
      (ListBlank.append [x] R)).write
        (some (bits.get ⟨e.n - 1, by omega⟩))) (by omega) hlast
  have hpair := stepsTo_cons _ hstep₁
    (stepsTo_cons _ hstep₂ (stepsTo_zero _ _))
  have hT := sim_clean_write_phase_tape bits L R x hn
  rw [hT] at hpair
  have hforward := stepsTo_trans (t₁ := 2 * (e.n - 1)) (t₂ := 2) _ hp hpair
  convert hforward using 1
  all_goals omega

/-- Finish write-back by restoring the input head and marking its first cell. -/
lemma simCleanMachine_write_phase_finish {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (L R : ListBlank (Option Bool)) (hn : 0 < e.n) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.writeBack q ⟨e.n, Nat.lt_succ_self _⟩),
        Tape.mk' (ListBlank.append (bits.toList.reverse.map some) L) R⟩
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append (bits.toList.map some) R)⟩
      (e.n + 1) := by
  have hback := simCleanMachine_writeBack_walk M e q
    (Tape.mk' (ListBlank.append (bits.toList.reverse.map some) L) R)
    e.n (Nat.lt_succ_self _)
  have hbackT :
      (Tape.move Dir.left)^[e.n]
        (Tape.mk' (ListBlank.append (bits.toList.reverse.map some) L) R) =
        Tape.mk' L (ListBlank.append (bits.toList.map some) R) := by
    simpa [List.map_reverse] using
      (tape_move_left_block (bits.toList.map some) L R)
  rw [hbackT] at hback
  have hhead :
      (Tape.mk' L (ListBlank.append (bits.toList.map some) R)).head.isSome := by
    rw [Tape.mk'_head]
    have hbits : bits.toList ≠ [] := by
      intro hnil
      have hlen := List.Vector.toList_length bits
      simp [hnil] at hlen
      omega
    cases h : bits.toList with
    | nil => exact (hbits h).elim
    | cons z zs => simp [ListBlank.append]
  have hzero := simCleanMachine_writeBack_zero_step M e q
    (Tape.mk' L (ListBlank.append (bits.toList.map some) R)) hhead
  have hone := stepsTo_cons _ hzero (stepsTo_zero _ _)
  have htotal := stepsTo_trans (t₁ := e.n) (t₂ := 1) _ hback hone
  convert htotal using 1
  all_goals omega

lemma simCleanMachine_write_phase {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (bits : List.Vector Bool e.n)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (hold : old.length = e.n) (hn : 0 < e.n) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.write q ⟨0, Nat.zero_lt_succ _⟩ bits),
        Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.ready q),
        Tape.mk' L (ListBlank.append (bits.toList.map some) R)⟩
      (3 * e.n + 1) := by
  have hforward := simCleanMachine_write_phase_prefix M e q bits old L R hold hn
  have hfinish := simCleanMachine_write_phase_finish M e q bits L R hn
  have htotal := stepsTo_trans (t₁ := 2 * e.n) (t₂ := e.n + 1) _ hforward hfinish
  convert htotal using 1
  all_goals omega

lemma simCleanMachine_ready_mark_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (T : Tape (Option Bool))
    (hn : 0 < e.n) :
    TM0.step (simCleanMachine M e) ⟨.run (.ready q), T⟩ =
      some ⟨.run (.read q ⟨0, Nat.zero_lt_succ _⟩ .nil),
        T.write (simMarkCell T.head)⟩ := by
  simp [TM0.step, simCleanMachine, simMachine, hn]

lemma simCleanMachine_read_continue_mark_steps {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (i : Fin e.n.succ)
    (acc : List.Vector Bool i.val) (T : Tape (Option Bool))
    (h : i.val + 1 ≤ e.n) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.read q i acc), T⟩
      ⟨.run (.read q ⟨i.val + 1, by omega⟩
        (acc.cons (Option.getD T.head false))),
        (T.write (simMarkCell T.head)).move Dir.right⟩ 2 := by
  have hs : i.val + 1 < e.n.succ := by omega
  have h1 : TM0.step (simCleanMachine M e)
      ⟨.run (.read q i acc), T⟩ =
      some ⟨.markMove (.read q ⟨i.val + 1, by omega⟩
          (acc.cons (Option.getD T.head false))) Dir.right,
        T.write (simMarkCell T.head)⟩ := by
    simp [TM0.step, simCleanMachine, simMachine, hs, simMarkCell]
  have h2 := simCleanMachine_markMove_step M e
    (.read q ⟨i.val + 1, by omega⟩
      (acc.cons (Option.getD T.head false))) Dir.right
    (T.write (simMarkCell T.head))
  exact stepsTo_cons _ h1 (stepsTo_cons _ h2 (stepsTo_zero _ _))

lemma simCleanMachine_read_prefix_mark {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (b : List (Option Bool))
    (L R : ListBlank (Option Bool)) (hb : b.length = e.n) :
    ∀ k, ∀ hk : k ≤ e.n, ∃ acc : List.Vector Bool k,
      acc.toList.reverse =
        (b.map (Option.getD · false)).take k ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.read q ⟨0, Nat.zero_lt_succ _⟩ .nil),
          Tape.mk' L (ListBlank.append b R)⟩
        ⟨.run (.read q ⟨k, Nat.lt_succ_of_le hk⟩ acc),
          Tape.mk'
            (ListBlank.append
              ((b.take k).reverse.map simMarkCell) L)
            (ListBlank.append (b.drop k) R)⟩ (2 * k) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨.nil, rfl, stepsTo_zero _ _⟩
  | succ k ih =>
      intro hk
      have hk' : k ≤ e.n := by omega
      obtain ⟨acc, hacc, hsteps⟩ := ih hk'
      have hlt : k < b.length := by rw [hb]; omega
      have hlt' : k < e.n := by omega
      obtain ⟨x, rest, hdrop⟩ :=
        sim_clean_list_drop_exists_cons b e.n k hb hlt'
      have hdrop' : b.drop k = x :: rest := hdrop
      have hx : x = b[k] := by
        have htake1 := List.take_one_drop_eq_of_lt_length hlt
        have hheadtake := congrArg List.headI htake1
        rw [hdrop'] at hheadtake
        simpa using hheadtake
      have hget_elem : b[k] = x := hx.symm
      have hget : b.getI k = x := by
        rw [List.getI_eq_getElem _ hlt]
        exact hget_elem
      have hhead :
          ((Tape.mk'
            (ListBlank.append ((b.take k).reverse.map simMarkCell) L)
            (ListBlank.append (b.drop k) R))).head = x := by
        rw [hdrop']
        simp [ListBlank.append]
      have hstep := simCleanMachine_read_continue_mark_steps M e q
        ⟨k, by omega⟩ acc
        (Tape.mk'
          (ListBlank.append ((b.take k).reverse.map simMarkCell) L)
          (ListBlank.append (b.drop k) R)) (by omega)
      have hhead' :
          (Tape.mk'
            (ListBlank.append ((b.take k).reverse.map simMarkCell) L)
            (ListBlank.append (b.drop k) R)).head.getD false =
            (b.map (Option.getD · false)).getI k := by
        rw [hdrop']
        simp [ListBlank.append]
        rw [← hget]
        exact (map_option_getI_getD b k).symm
      rw [hhead'] at hstep
      have htake : b.take (k + 1) = b.take k ++ [x] := by
        rw [List.take_succ_eq_append_getElem hlt]
        rw [hget_elem]
      have hdrop_succ : b.drop (k + 1) = rest := by
        have ht := congrArg List.tail hdrop'
        simpa using ht
      have hT :
          ((Tape.mk'
            (ListBlank.append ((b.take k).reverse.map simMarkCell) L)
            (ListBlank.append (x :: rest) R)).write
              (simMarkCell x)).move Dir.right =
            Tape.mk'
              (ListBlank.append ((b.take (k + 1)).reverse.map simMarkCell) L)
              (ListBlank.append (b.drop (k + 1)) R) := by
        rw [sim_clean_tape_write_move_right_head]
        rw [htake, hdrop_succ]
        simp [List.reverse_append]
      rw [hdrop'] at hsteps
      rw [hhead] at hstep
      rw [hdrop'] at hstep
      rw [hT] at hstep
      have htotal := stepsTo_trans (t₁ := 2 * k) (t₂ := 2) _ hsteps hstep
      refine ⟨acc.cons ((b.map (Option.getD · false)).getI k), ?_, ?_⟩
      · rw [vector_cons_reverse, hacc]
        have hmap : k < (b.map (Option.getD · false)).length := by
          simpa using hlt
        exact (tape_take_succ_getI (b.map (Option.getD · false)) k hmap).symm
      · convert htotal using 1
        all_goals omega

lemma simCleanMachine_read_rewind_any {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (b : List (Option Bool))
    (L R : ListBlank (Option Bool)) (hb : b.length = e.n)
    (hn : 0 < e.n) :
    ∃ bits : List.Vector Bool e.n,
      bits.toList = b.map (Option.getD · false) ∧
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q),
          Tape.mk' L (ListBlank.append b R)⟩
        ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits),
          (Tape.move Dir.left)^[e.n]
            (((Tape.move Dir.right)^[e.n]
              (Tape.mk' L (ListBlank.append (simMarkBlock b) R))).write
                (simMarkCell ((Tape.move Dir.right)^[e.n]
                  (Tape.mk' L (ListBlank.append (simMarkBlock b) R))).head))⟩
        (3 * e.n + 2) := by
  have hne : b ≠ [] := by
    intro hnil
    have hz : (0 : Nat) = e.n := by simpa [hnil] using hb
    have hp := hn
    omega
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  let b' : List (Option Bool) := simMarkCell x :: xs
  have hb' : b'.length = e.n := by simpa [b', hb]
  have hmark : (Tape.mk' L (ListBlank.append (x :: xs) R)).write
      (simMarkCell (Tape.mk' L (ListBlank.append (x :: xs) R)).head) =
      Tape.mk' L (ListBlank.append b' R) := by
    simp [b', Tape.write_mk', ListBlank.append]
  have hready := simCleanMachine_ready_mark_step M e q
    (Tape.mk' L (ListBlank.append (x :: xs) R)) hn
  have hready' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append (x :: xs) R)⟩
      ⟨.run (.read q ⟨0, Nat.zero_lt_succ _⟩ .nil),
        Tape.mk' L (ListBlank.append b' R)⟩ 1 := by
    rw [← hmark]
    exact stepsTo_cons _ hready (stepsTo_zero _ _)
  obtain ⟨acc, hacc, hprefix⟩ := simCleanMachine_read_prefix_mark M e q
    b' L R hb' e.n le_rfl
  let bm : List (Option Bool) := simMarkBlock (x :: xs)
  have hlen : xs.length + 1 = e.n := by simpa [List.length_cons] using hb
  have hbm : bm.length = e.n := by simp [bm, simMarkBlock, hlen]
  have htake : b'.take e.n = b' := by simp [b', hlen]
  have hdrop : b'.drop e.n = [] := by simp [hb']
  have hmap : b'.map simMarkCell = bm := by
    simp [b', bm, simMarkBlock, simMarkCell_idem]
  have hrev : b'.reverse.map simMarkCell = bm.reverse := by
    have := congrArg List.reverse hmap
    simpa [List.map_reverse] using this
  have hprefix' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.read q ⟨0, Nat.zero_lt_succ _⟩ .nil),
        Tape.mk' L (ListBlank.append b' R)⟩
      ⟨.run (.read q ⟨e.n, Nat.lt_succ_self _⟩ acc),
        Tape.mk' (ListBlank.append bm.reverse L) R⟩ (2 * e.n) := by
    rw [htake, hdrop, hrev] at hprefix
    exact hprefix
  let bits : List.Vector Bool e.n :=
    ⟨acc.toList.reverse, by simp [List.Vector.toList_length]⟩
  let Tread : Tape (Option Bool) :=
    Tape.mk' (ListBlank.append bm.reverse L) R
  have hfinish := simCleanMachine_read_finish_step M e q acc Tread
  have hfinish' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.read q ⟨e.n, Nat.lt_succ_self _⟩ acc),
        Tread⟩
      ⟨.run (.rewind q ⟨e.n, Nat.lt_succ_self _⟩ bits),
        Tread.write (simMarkCell Tread.head)⟩ 1 := by
    have hone := stepsTo_cons _ hfinish (stepsTo_zero _ _)
    simpa [bits, Tape.write_self] using hone
  have hmove : (Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append bm R)) = Tread := by
    simpa [Tread, hbm] using tape_move_right_block bm L R
  let T₂ : Tape (Option Bool) := Tread.write (simMarkCell Tread.head)
  have hrew := simCleanMachine_rewind_walk M e q bits T₂
    e.n (Nat.lt_succ_self _)
  have hread' := stepsTo_trans (t₁ := 1) (t₂ := 2 * e.n) _
    hready' hprefix'
  have hfirst := stepsTo_trans (t₁ := 2 * e.n + 1) (t₂ := 1) _
    hread' hfinish'
  have htotal := stepsTo_trans
    (t₁ := 1 + (2 * e.n + 1)) (t₂ := e.n) _ hfirst hrew
  have hbits : bits.toList = (x :: xs).map (Option.getD · false) := by
    have htake :
        (b'.map (Option.getD · false)).take e.n =
          b'.map (Option.getD · false) := by simp [hb']
    rw [htake] at hacc
    simpa [bits, b', simMarkCell_getD] using hacc
  refine ⟨bits, hbits, ?_⟩
  have htarget : (Tape.move Dir.left)^[e.n] T₂ =
      (Tape.move Dir.left)^[e.n]
        (((Tape.move Dir.right)^[e.n]
          (Tape.mk' L (ListBlank.append (simMarkBlock (x :: xs)) R))).write
            (simMarkCell ((Tape.move Dir.right)^[e.n]
              (Tape.mk' L (ListBlank.append (simMarkBlock (x :: xs)) R))).head)) := by
    rw [hmove]
  rw [htarget] at htotal
  have htime : e.n + (1 + (2 * e.n + 1)) = 3 * e.n + 2 := by omega
  rw [htime] at htotal
  exact htotal


end NPComplete.CookLevin

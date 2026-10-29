module

public import NPComplete.CookLevin.Recode.Enc

/-!
Encoding finite-alphabet input on a Boolean tape requires writing one fixed-width
block per input symbol and returning to the next source position. This module
proves the block-writing runs, output layout, and time bounds for empty and
nonempty inputs, supporting the input side of the recoding.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

variable (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)

lemma encMachine_done_none (cell : Option Bool) :
    encMachine tm inp .done cell = none :=
  rfl

lemma enc_done_halt (T : Tape (Option Bool)) :
    TM0.step (encMachine tm inp) ⟨.done, T⟩ = none := by
  simp [step_eq_none_iff, encMachine_done_none]

lemma enc_toEnd_none (T : Tape (Option Bool)) (h : T.head = none)
    (hn : 0 < encN tm) :
    TM0.step (encMachine tm inp) ⟨.toEnd, T⟩ =
      some ⟨.writeBlank ⟨0, hn⟩,
        T.write (some ((encBottomBlank tm).getD 0 false))⟩ := by
  simp [TM0.step, encMachine, h, hn]

lemma enc_checkLast (hasOutput b : Bool) (T : Tape (Option Bool)) :
    TM0.step (encMachine tm inp) ⟨.checkLast hasOutput b, T⟩ =
      some ⟨.lookAhead hasOutput b, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine]

lemma enc_lookAhead_some (hasOutput : Bool) (b : Bool)
    (T : Tape (Option Bool)) {x : Bool} (h : T.head = some x) :
    TM0.step (encMachine tm inp) ⟨.lookAhead hasOutput b, T⟩ =
      some ⟨.seekOutLeft hasOutput false b, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_lookAhead_none (hasOutput : Bool) (b : Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.lookAhead hasOutput b, T⟩ =
      some ⟨.seekOutLeft hasOutput true b, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_seekOutLeft_false (isBottom : Bool) (b : Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.seekOutLeft false isBottom b, T⟩ =
      some ⟨.writeLeft isBottom b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, encN, h, encN_pos tm]

lemma enc_seekOutLeft_true_none (isBottom : Bool) (b : Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.seekOutLeft true isBottom b, T⟩ =
      some ⟨.seekOutLeft true isBottom b, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_seekOutLeft_true_some (isBottom : Bool) (b : Bool)
    (T : Tape (Option Bool)) {x : Bool} (h : T.head = some x) :
    TM0.step (encMachine tm inp) ⟨.seekOutLeft true isBottom b, T⟩ =
      some ⟨.seekOutBlock isBottom b, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_seekOutBlock_some (isBottom : Bool) (b : Bool)
    (T : Tape (Option Bool)) {x : Bool} (h : T.head = some x) :
    TM0.step (encMachine tm inp) ⟨.seekOutBlock isBottom b, T⟩ =
      some ⟨.seekOutBlock isBottom b, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_seekOutBlock_none_nonbottom (b : Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.seekOutBlock false b, T⟩ =
      some ⟨.writeLeftMove false b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        T.write (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩ := by
  simp [TM0.step, encMachine, encN, h, encN_pos tm]

lemma enc_writeLeft_zero (isBottom : Bool) (b : Bool)
    (i : Fin (encN tm)) (T : Tape (Option Bool)) (hi : i.val = 0) :
    TM0.step (encMachine tm inp) ⟨.writeLeft isBottom b i, T⟩ =
      if isBottom then
        some ⟨.done, T.write (some ((encBlock tm inp isBottom b).getD i.val false))⟩
      else
        some ⟨.writeLeftMove isBottom b i,
          T.write (some ((encBlock tm inp isBottom b).getD i.val false))⟩ := by
  cases isBottom <;> simp [TM0.step, encMachine, hi]

lemma enc_writeLeft_succ (isBottom : Bool) (b : Bool)
    (i : Fin (encN tm)) (T : Tape (Option Bool)) (hi : i.val ≠ 0) :
    TM0.step (encMachine tm inp) ⟨.writeLeft isBottom b i, T⟩ =
      some ⟨.writeLeftMove isBottom b i,
        T.write (some ((encBlock tm inp isBottom b).getD i.val false))⟩ := by
  simp [TM0.step, encMachine, hi]

lemma enc_writeLeftMove_zero (isBottom : Bool) (b : Bool)
    (i : Fin (encN tm)) (T : Tape (Option Bool)) (hi : i.val = 0) :
    TM0.step (encMachine tm inp) ⟨.writeLeftMove isBottom b i, T⟩ =
      some ⟨.returnRight, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, hi]

lemma enc_writeLeftMove_succ (isBottom : Bool) (b : Bool)
    (i : Fin (encN tm)) (T : Tape (Option Bool)) (hi : i.val ≠ 0) :
    TM0.step (encMachine tm inp) ⟨.writeLeftMove isBottom b i, T⟩ =
      some ⟨.writeLeft isBottom b
          ⟨i.val - 1,
            lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hi) (by omega)) i.isLt⟩,
        T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, hi]

lemma enc_returnRight_some (T : Tape (Option Bool)) {b : Bool}
    (h : T.head = some b) :
    TM0.step (encMachine tm inp) ⟨.returnRight, T⟩ =
      some ⟨.returnRight, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_returnRight_none (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.returnRight, T⟩ =
      some ⟨.returnGap, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_returnGap_none (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.returnGap, T⟩ =
      some ⟨.returnGap, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_returnGap_some (T : Tape (Option Bool)) {b : Bool}
    (h : T.head = some b) :
    TM0.step (encMachine tm inp) ⟨.returnGap, T⟩ =
      some ⟨.checkLast true b, T.write none⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_writeBlank_mid (i : Fin (encN tm)) (T : Tape (Option Bool))
    (h : i.val + 1 < encN tm) :
    TM0.step (encMachine tm inp) ⟨.writeBlank i, T⟩ =
      some ⟨.writeBlankMove i, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_writeBlank_last (i : Fin (encN tm)) (T : Tape (Option Bool))
    (h : ¬ i.val + 1 < encN tm) :
    TM0.step (encMachine tm inp) ⟨.writeBlank i, T⟩ =
      some ⟨.shiftHome, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_writeBlankMove_mid (i : Fin (encN tm)) (T : Tape (Option Bool))
    (h : i.val + 1 < encN tm) :
    TM0.step (encMachine tm inp) ⟨.writeBlankMove i, T⟩ =
      some ⟨.writeBlank ⟨i.val + 1, h⟩,
        T.write (some ((encBottomBlank tm).getD (i.val + 1) false))⟩ := by
  simp [TM0.step, encMachine, encN, h]

lemma enc_shiftHome_some (T : Tape (Option Bool)) {b : Bool}
    (h : T.head = some b) :
    TM0.step (encMachine tm inp) ⟨.shiftHome, T⟩ =
      some ⟨.shiftHome, T.move Dir.left⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_shiftHome_none (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (encMachine tm inp) ⟨.shiftHome, T⟩ =
      some ⟨.done, T.move Dir.right⟩ := by
  simp [TM0.step, encMachine, h]

lemma enc_seekOutLeft_walk (isBottom b : Bool) (T : Tape (Option Bool)) :
    ∀ k, (∀ i, i < k → ((Tape.move Dir.left)^[i] T).head = none) →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.seekOutLeft true isBottom b, T⟩
        ⟨.seekOutLeft true isBottom b, (Tape.move Dir.left)^[k] T⟩ k
  | 0, _ => stepsTo_zero _ _
  | k + 1, hk => by
      have h0 := hk 0 (Nat.succ_pos _)
      have hstep := enc_seekOutLeft_true_none tm inp isBottom b T h0
      refine stepsTo_cons _ hstep ?_
      have ih := enc_seekOutLeft_walk isBottom b (T.move Dir.left) k fun i hi => by
        have := hk (i + 1) (Nat.succ_lt_succ hi)
        simpa [Function.iterate_succ_apply] using this
      simpa [Function.iterate_succ_apply] using ih

lemma enc_seekOutBlock_walk (isBottom b : Bool) (T : Tape (Option Bool)) :
    ∀ k, (∀ i, i < k → ((Tape.move Dir.left)^[i] T).head.isSome = true) →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.seekOutBlock isBottom b, T⟩
        ⟨.seekOutBlock isBottom b, (Tape.move Dir.left)^[k] T⟩ k
  | 0, _ => stepsTo_zero _ _
  | k + 1, hk => by
      have ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hk 0 (Nat.succ_pos _))
      have hstep := enc_seekOutBlock_some tm inp isBottom b T hx
      refine stepsTo_cons _ hstep ?_
      have ih := enc_seekOutBlock_walk isBottom b (T.move Dir.left) k fun i hi => by
        have := hk (i + 1) (Nat.succ_lt_succ hi)
        simpa [Function.iterate_succ_apply] using this
      simpa [Function.iterate_succ_apply] using ih

lemma enc_returnRight_walk (T : Tape (Option Bool)) :
    ∀ k, (∀ i, i < k → ((Tape.move Dir.right)^[i] T).head.isSome = true) →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.returnRight, T⟩
        ⟨.returnRight, (Tape.move Dir.right)^[k] T⟩ k
  | 0, _ => stepsTo_zero _ _
  | k + 1, hk => by
      have ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hk 0 (Nat.succ_pos _))
      have hstep := enc_returnRight_some tm inp T hx
      refine stepsTo_cons _ hstep ?_
      have ih := enc_returnRight_walk (T.move Dir.right) k fun i hi => by
        have := hk (i + 1) (Nat.succ_lt_succ hi)
        simpa [Function.iterate_succ_apply] using this
      simpa [Function.iterate_succ_apply] using ih

lemma enc_returnGap_walk (T : Tape (Option Bool)) :
    ∀ k, (∀ i, i < k → ((Tape.move Dir.right)^[i] T).head = none) →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.returnGap, T⟩
        ⟨.returnGap, (Tape.move Dir.right)^[k] T⟩ k
  | 0, _ => stepsTo_zero _ _
  | k + 1, hk => by
      have hstep := enc_returnGap_none tm inp T (hk 0 (Nat.succ_pos _))
      refine stepsTo_cons _ hstep ?_
      have ih := enc_returnGap_walk (T.move Dir.right) k fun i hi => by
        have := hk (i + 1) (Nat.succ_lt_succ hi)
        simpa [Function.iterate_succ_apply] using this
      simpa [Function.iterate_succ_apply] using ih

lemma tape_move_left_head' (L : List (Option Bool)) (R : ListBlank (Option Bool)) :
    ∀ i, ((Tape.move Dir.left)^[i + 1]
      (Tape.mk' (ListBlank.mk L) R)).head = L.getD i none
  | 0 => by
      cases L <;> simp [Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, List.getD, default]
  | i + 1 => by
      have ih := tape_move_left_head' L.tail
        (ListBlank.cons (ListBlank.mk L).head R) i
      simpa [Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk, List.getD, default] using ih

lemma enc_gap_heads (k : ℕ) (out : List Bool) (R : List (Option Bool)) :
    ∀ j, j < k + 1 →
      ((Tape.move Dir.left)^[j]
        (Tape.mk' (ListBlank.mk (List.replicate k none ++
          (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))).head = none
  | 0, _ => by simp [tapeSymbols]
  | j + 1, hj => by
      have hj' : j < k := by omega
      have hh := tape_move_left_head' (List.replicate k none ++
        (tapeSymbols out).reverse) (ListBlank.mk (none :: R)) j
      rw [hh]
      rw [List.getD_append _ _ _ j (by simp; omega), List.getD_replicate none hj']

lemma enc_output_head_some (k : ℕ) (out : List Bool) (R : List (Option Bool))
    (j : ℕ) (hj : j < out.length - 1) :
    ((Tape.move Dir.left)^[k + 2 + j]
      (Tape.mk' (ListBlank.mk (List.replicate k none ++
        (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))).head.isSome = true := by
  have hidx : j + 1 < out.length := by omega
  have hh := tape_move_left_head' (List.replicate k none ++
    (tapeSymbols out).reverse) (ListBlank.mk (none :: R)) (k + 1 + j)
  have hget : ((List.replicate k (none : Option Bool) ++
      (tapeSymbols out).reverse).getD (k + 1 + j) none).isSome = true := by
    have hk : (List.replicate k (none : Option Bool)).length ≤ k + 1 + j := by
      simp
      omega
    rw [List.getD_append_right _ _ _ _ hk]
    simp only [List.length_replicate]
    rw [show k + 1 + j - k = j + 1 by omega]
    have hrev : j + 1 < (tapeSymbols out).reverse.length := by
      simp [tapeSymbols]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrev]
    simp [tapeSymbols]
  rw [show k + 2 + j = (k + 1 + j) + 1 by omega, hh, hget]

lemma tape_move_right_head' (L : ListBlank (Option Bool))
    (R : List (Option Bool)) :
    ∀ i, ((Tape.move Dir.right)^[i]
      (Tape.mk' L (ListBlank.mk R))).head = R.getD i none
  | 0 => by
      cases R <;> simp [Tape.mk', ListBlank.head_mk, List.getD, default]
  | i + 1 => by
      have ih := tape_move_right_head'
        (ListBlank.cons (ListBlank.mk R).head L) R.tail i
      simpa [Tape.move_right_mk', ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk, List.getD, default] using ih

def encPref (bits : List Bool) (k : ℕ) : List (Option Bool) :=
  (bits.take k).reverse.map some

def tapeOnBit (bits : List Bool) (k : ℕ) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (encPref bits k))
    (ListBlank.mk [some (bits.getD k false)])

lemma encPref_succ (bits : List Bool) (k : ℕ) (hk : k < bits.length) :
    encPref bits (k + 1) = some (bits.getD k false) :: encPref bits k := by
  have htk : bits.take (k + 1) = bits.take k ++ [bits[k]] :=
    List.take_succ_eq_append_getElem hk
  unfold encPref
  rw [htk, List.reverse_append]
  simp [List.getD, hk]

lemma tapeOnBit_move_right (bits : List Bool) (k : ℕ) :
    (tapeOnBit bits k).move Dir.right =
      Tape.mk' (ListBlank.mk (some (bits.getD k false) :: encPref bits k))
        (ListBlank.mk []) := by
  simp [tapeOnBit, Tape.move_right_mk', ListBlank.head_mk,
    ListBlank.tail_mk, ListBlank.cons_mk]

lemma tapeOnBit_succ (bits : List Bool) (k : ℕ) (hk : k < bits.length) :
    (Tape.mk' (ListBlank.mk (some (bits.getD k false) :: encPref bits k))
        (ListBlank.mk [])).write (some (bits.getD (k + 1) false)) =
      tapeOnBit bits (k + 1) := by
  unfold tapeOnBit
  simp [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]
  rw [encPref_succ bits k hk]
  simp [List.getD_eq_getElem?_getD]

lemma enc_shiftHome_walk (T : Tape (Option Bool)) :
    ∀ k, (∀ i, i < k → ((Tape.move Dir.left)^[i] T).head.isSome = true) →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.shiftHome, T⟩
        ⟨.shiftHome, (Tape.move Dir.left)^[k] T⟩ k
  | 0, _ => stepsTo_zero _ _
  | k + 1, hk => by
      have ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hk 0 (Nat.succ_pos _))
      have hstep := enc_shiftHome_some tm inp T hb
      refine stepsTo_cons _ hstep ?_
      have ih := enc_shiftHome_walk (T.move Dir.left) k fun i hi => by
        have := hk (i + 1) (Nat.succ_lt_succ hi)
        simpa [Function.iterate_succ_apply] using this
      simpa [Function.iterate_succ_apply] using ih

lemma enc_writeBlank_on_bit :
    ∀ i (hi : i < encN tm),
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.writeBlank ⟨i, hi⟩, tapeOnBit (encBottomBlank tm) i⟩
        ⟨.shiftHome,
          (tapeOnBit (encBottomBlank tm) (encN tm - 1)).move Dir.left⟩
        (2 * (encN tm - 1 - i) + 1) := by
  intro i hi
  have hmain : ∀ d : ℕ, ∀ j (hj : j < encN tm),
      d = encN tm - 1 - j →
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.writeBlank ⟨j, hj⟩, tapeOnBit (encBottomBlank tm) j⟩
        ⟨.shiftHome,
          (tapeOnBit (encBottomBlank tm) (encN tm - 1)).move Dir.left⟩
        (2 * (encN tm - 1 - j) + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro j hj hd
        by_cases hnext : j + 1 < encN tm
        · have hstep := enc_writeBlank_mid tm inp ⟨j, hj⟩
            (tapeOnBit (encBottomBlank tm) j) hnext
          have hstep' := enc_writeBlankMove_mid tm inp ⟨j, hj⟩
            ((tapeOnBit (encBottomBlank tm) j).move Dir.right) hnext
          have hjbits : j < (encBottomBlank tm).length := by
            rw [encBottomBlank_length]
            omega
          have hsucc := tapeOnBit_succ (encBottomBlank tm) j hjbits
          rw [tapeOnBit_move_right, hsucc] at hstep'
          have hrun := ih (encN tm - 1 - (j + 1)) (by omega) (j + 1)
            hnext rfl
          have htail := stepsTo_cons _ hstep' hrun
          have hrest : StepsTo (TM0.step (encMachine tm inp))
              ⟨.writeBlankMove ⟨j, hj⟩,
                (tapeOnBit (encBottomBlank tm) j).move Dir.right⟩
              ⟨.shiftHome,
                (tapeOnBit (encBottomBlank tm) (encN tm - 1)).move Dir.left⟩
              (2 * (encN tm - 1 - j)) := by
            rw [tapeOnBit_move_right]
            convert htail using 1; omega
          have hall := stepsTo_cons _ hstep hrest
          simpa using hall
        · have hjlast : j = encN tm - 1 := by omega
          subst j
          have hs := enc_writeBlank_last tm inp ⟨encN tm - 1,
            Nat.sub_lt (encN_pos tm) (by omega)⟩
            (tapeOnBit (encBottomBlank tm) (encN tm - 1)) hnext
          simpa using (stepsTo_cons _ hs (stepsTo_zero _ _))
  exact hmain (encN tm - 1 - i) i hi rfl

noncomputable def encOut (xs : List Bool) : List Bool :=
  xs.reverse.flatMap (encBlock tm inp false)

lemma encOut_length (xs : List Bool) :
    (encOut tm inp xs).length = xs.length * encN tm := by
  induction xs with
  | nil => simp [encOut]
  | cons b xs ih =>
      simp [encOut, List.reverse_cons, List.flatMap_append,
        encBlock_length, Nat.succ_mul]

noncomputable def encLeft (xs : List Bool) : List (Option Bool) :=
  List.replicate xs.length none ++ (tapeSymbols (encOut tm inp xs)).reverse

noncomputable def encSource (xs rest : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (encLeft tm inp xs))
    (ListBlank.mk (tapeSymbols rest))

noncomputable def encCheck (xs rest : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (encLeft tm inp xs))
    (ListBlank.mk (none :: tapeSymbols rest))

lemma enc_to_check (xs rest : List Bool) (b : Bool) :
    TM0.step (encMachine tm inp) ⟨.toEnd, encSource tm inp xs (b :: rest)⟩ =
      some ⟨.checkLast false b, encCheck tm inp xs rest⟩ := by
  simp [encSource, encCheck, encLeft, encOut, tapeSymbols,
    TM0.step, encMachine, Tape.write_mk', ListBlank.tail_mk,
    ListBlank.cons_mk]

lemma enc_drop_cons (bits : List Bool) (i : ℕ) (hi : i < bits.length) :
    bits.drop i = bits.getD i false :: bits.drop (i + 1) := by
  induction bits generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => simp [List.getD]
      | succ i =>
          simp [List.drop, List.getD]
          exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- The `writeLeft` phase of `enc_block_write_nonbottom`: from bit `i` down to bit 0,
    it writes each bit while moving left; after bit 0, it moves one step right into
    `returnRight`. -/
lemma enc_block_write_nonbottom_left (R : List (Option Bool)) (b : Bool) :
    ∀ i (hi : i < encN tm),
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.writeLeft false b ⟨i, hi⟩,
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (none ::
              ((encBlock tm inp false b).drop (i + 1)).map some ++ R))⟩
        ⟨.returnRight,
          Tape.mk' (ListBlank.mk [some ((encBlock tm inp false b).getD 0 false)])
            (ListBlank.mk (((encBlock tm inp false b).drop 1).map some ++ R))⟩
        (2 * i + 2) := by
  intro i
  induction i with
  | zero =>
      intro hi
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none ::
          ((encBlock tm inp false b).drop 1).map some ++ R))
      have hs : TM0.step (encMachine tm inp)
          ⟨.writeLeft false b ⟨0, hi⟩, T⟩ =
          some ⟨.writeLeftMove false b ⟨0, hi⟩,
            T.write (some ((encBlock tm inp false b).getD 0 false))⟩ := by
        simp [T, TM0.step, encMachine]
      have hm : TM0.step (encMachine tm inp)
          ⟨.writeLeftMove false b ⟨0, hi⟩,
            T.write (some ((encBlock tm inp false b).getD 0 false))⟩ =
          some ⟨.returnRight,
            (T.write (some ((encBlock tm inp false b).getD 0 false))).move
              Dir.right⟩ := by
        simp [TM0.step, encMachine]
      refine stepsTo_cons _ hs (stepsTo_cons _ hm ?_)
      exact stepsTo_zero _ _
  | succ i ih =>
      intro hi
      let bits := encBlock tm inp false b
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: (bits.drop (i + 2)).map some ++ R))
      have htail : i < encN tm :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi)
      have hdrop' : bits.drop (i + 1) =
          bits.getD (i + 1) false :: bits.drop (i + 2) := by
        exact enc_drop_cons bits (i + 1) (by rw [encBlock_length]; exact hi)
      have hs : TM0.step (encMachine tm inp)
          ⟨.writeLeft false b ⟨i + 1, hi⟩, T⟩ =
          some ⟨.writeLeftMove false b ⟨i + 1, hi⟩,
            T.write (some (bits.getD (i + 1) false))⟩ := by
        simp [T, bits, TM0.step, encMachine]
      have hm : TM0.step (encMachine tm inp)
          ⟨.writeLeftMove false b ⟨i + 1, hi⟩,
            T.write (some (bits.getD (i + 1) false))⟩ =
          some ⟨.writeLeft false b ⟨i, htail⟩,
            (T.write (some (bits.getD (i + 1) false))).move Dir.left⟩ := by
        simp [T, bits, TM0.step, encMachine]
      refine stepsTo_cons _ hs (stepsTo_cons _ hm ?_)
      have ih' := ih htail
      convert ih' using 1; try simp [T, bits, hdrop', Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, default]

/-- The writeLeftMove phase of `enc_block_write_nonbottom`: from bit `i`, it moves left
    to bit 0, entering `writeLeft` at each lower bit, then moves right once into
    `returnRight`. -/
lemma enc_block_write_nonbottom_move (R : List (Option Bool)) (b : Bool) :
    ∀ i (hi : i < encN tm),
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.writeLeftMove false b ⟨i, hi⟩,
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (some ((encBlock tm inp false b).getD i false) ::
              ((encBlock tm inp false b).drop (i + 1)).map some ++ R))⟩
        ⟨.returnRight,
          Tape.mk' (ListBlank.mk [some ((encBlock tm inp false b).getD 0 false)])
            (ListBlank.mk (((encBlock tm inp false b).drop 1).map some ++ R))⟩
        (2 * i + 1) := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hs := enc_writeLeftMove_zero tm inp false b ⟨0, hi⟩
        (Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (some ((encBlock tm inp false b).getD 0 false) ::
            ((encBlock tm inp false b).drop 1).map some ++ R))) rfl
      refine stepsTo_cons _ hs (stepsTo_zero _ _)
  | succ i ih =>
      intro hi
      have htail' : i < encN tm :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi)
      let bits := encBlock tm inp false b
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (some (bits.getD (i + 1) false) ::
          (bits.drop (i + 2)).map some ++ R))
      have hs := enc_writeLeftMove_succ tm inp false b ⟨i + 1, hi⟩ T
        (Nat.succ_ne_zero _)
      refine stepsTo_cons _ hs ?_
      have hdrop := enc_drop_cons bits (i + 1)
        (by rw [encBlock_length]; exact hi)
      have hmid := enc_block_write_nonbottom_left tm inp R b i htail'
      convert hmid using 1; try simp [T, bits, hdrop, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, default, Nat.add_assoc]

lemma enc_block_write_nonbottom (R : List (Option Bool)) (b : Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.writeLeftMove false b
        ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))).write
          (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩
      ⟨.returnRight,
        Tape.mk' (ListBlank.mk [some ((encBlock tm inp false b).getD 0 false)])
          (ListBlank.mk (((encBlock tm inp false b).drop 1).map some ++ R))⟩
      (2 * encN tm - 1) := by
  have hrun := enc_block_write_nonbottom_move tm inp R b (encN tm - 1)
    (Nat.sub_lt (encN_pos tm) (by omega))
  have hn := encN_pos tm
  have hidx : encN tm - 1 + 1 = encN tm := by omega
  have htime : 2 * encN tm - 1 = 2 * (encN tm - 1) + 1 := by omega
  have hdropnil :
      (List.map some (encBlock tm inp false b)).drop (encN tm) = [] := by
    apply List.drop_eq_nil_of_le
    simp [encBlock_length]
  simpa [hidx, hdropnil, htime, Tape.write_mk', ListBlank.tail_mk,
    ListBlank.cons_mk] using hrun

lemma enc_block_write_bottom_left (R : List (Option Bool)) (b : Bool) :
    ∀ i (hi : i < encN tm),
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.writeLeft true b ⟨i, hi⟩,
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (none ::
              ((encBlock tm inp true b).drop (i + 1)).map some ++ R))⟩
      ⟨.done,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk ((encBlock tm inp true b).map some ++ R))⟩
      (2 * i + 1) := by
  intro i
  induction i with
  | zero =>
      intro hi
      let bits := encBlock tm inp true b
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: (bits.drop 1).map some ++ R))
      have hs : TM0.step (encMachine tm inp)
          ⟨.writeLeft true b ⟨0, hi⟩, T⟩ =
          some ⟨.done, T.write (some (bits.getD 0 false))⟩ := by
        simp [T, bits, TM0.step, encMachine]
      have hbits : bits = bits.getD 0 false :: bits.drop 1 :=
        enc_drop_cons bits 0 (by rw [encBlock_length]; exact hi)
      refine stepsTo_cons _ hs ?_
      have hT : T.write (some (bits.getD 0 false)) =
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (bits.map some ++ R)) := by
        unfold T
        rw [Tape.write_mk']
        simp only [ListBlank.tail_mk, ListBlank.cons_mk]
        rw [hbits]
        simp [List.map_cons]
      rw [hT]
      exact stepsTo_zero _ _
  | succ i ih =>
      intro hi
      let bits := encBlock tm inp true b
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: (bits.drop (i + 2)).map some ++ R))
      have htail : i < encN tm :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi)
      have hdrop : bits.drop (i + 1) =
          bits.getD (i + 1) false :: bits.drop (i + 2) :=
        enc_drop_cons bits (i + 1) (by rw [encBlock_length]; exact hi)
      have hs : TM0.step (encMachine tm inp)
          ⟨.writeLeft true b ⟨i + 1, hi⟩, T⟩ =
          some ⟨.writeLeftMove true b ⟨i + 1, hi⟩,
            T.write (some (bits.getD (i + 1) false))⟩ := by
        simp [T, bits, TM0.step, encMachine]
      have hm : TM0.step (encMachine tm inp)
          ⟨.writeLeftMove true b ⟨i + 1, hi⟩,
            T.write (some (bits.getD (i + 1) false))⟩ =
          some ⟨.writeLeft true b ⟨i, htail⟩,
            (T.write (some (bits.getD (i + 1) false))).move Dir.left⟩ := by
        simp [T, bits, TM0.step, encMachine]
      refine stepsTo_cons _ hs (stepsTo_cons _ hm ?_)
      have ih' := ih htail
      convert ih' using 1; try simp [T, bits, hdrop, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, default]

lemma enc_block_write_bottom (R : List (Option Bool)) (b : Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.writeLeft true b
        ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))⟩
      ⟨.done,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk ((encBlock tm inp true b).map some ++ R))⟩
      (2 * encN tm - 1) := by
  have hrun := enc_block_write_bottom_left tm inp R b (encN tm - 1)
    (Nat.sub_lt (encN_pos tm) (by omega))
  have hn := encN_pos tm
  have hidx : encN tm - 1 + 1 = encN tm := by omega
  have htime : 2 * (encN tm - 1) + 1 = 2 * encN tm - 1 := by omega
  have hdropnil :
      (List.map some (encBlock tm inp true b)).drop (encN tm) = [] := by
    apply List.drop_eq_nil_of_le
    simp [encBlock_length]
  simpa [hidx, hdropnil, htime] using hrun

lemma tape_move_left_past (L R : List (Option Bool)) :
    (Tape.move Dir.left)^[L.length + 1]
      (Tape.mk' (ListBlank.mk L) (ListBlank.mk R)) =
      Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: L.reverse ++ R)) := by
  induction L generalizing R with
  | nil =>
      simp [Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk, default]
  | cons a L ih =>
      simp only [List.length_cons, Nat.add_assoc]
      rw [Function.iterate_succ_apply, Tape.move_left_mk']
      have h := ih (a :: R)
      simpa [List.reverse_cons, ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk] using h

lemma tape_move_right_prefix (L xs R : List (Option Bool)) :
    (Tape.move Dir.right)^[xs.length]
      (Tape.mk' (ListBlank.mk L) (ListBlank.mk (xs ++ R))) =
      Tape.mk' (ListBlank.mk (xs.reverse ++ L)) (ListBlank.mk R) := by
  induction xs generalizing L with
  | nil => simp
  | cons a xs ih =>
      rw [show (a :: xs).length = xs.length + 1 by simp,
        Function.iterate_succ_apply, Tape.move_right_mk']
      have h := ih (a :: L)
      simpa [List.reverse_cons, ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk] using h

lemma map_some_getD_some (bits : List Bool) (i : ℕ) (hi : i < bits.length) :
    ((bits.map some).getD i none).isSome = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  simp

lemma enc_right_output_heads (bits : List Bool) (R : List (Option Bool)) :
    ∀ j, j < bits.length - 1 →
      ((Tape.move Dir.right)^[j]
        (Tape.mk' (ListBlank.mk [some (bits.getD 0 false)])
          (ListBlank.mk (((bits.drop 1).map some) ++ R)))).head.isSome = true
  | j, hj => by
      have hright := tape_move_right_head'
        (ListBlank.mk [some (bits.getD 0 false)])
        (((bits.drop 1).map some) ++ R) j
      have hi : j < (bits.drop 1).length := by
        simp
        omega
      have hget : ((((bits.drop 1).map some) ++ R).getD j none).isSome = true := by
        have hi' : j < ((bits.drop 1).map some).length := by simpa using hi
        rw [List.getD_append ((bits.drop 1).map some) R none j hi']
        apply map_some_getD_some
        exact hi
      rw [hright, hget]

lemma enc_output_first_head (k : ℕ) (out : List Bool) (R : List (Option Bool))
    (hout : 0 < out.length) :
    ((Tape.move Dir.left)^[k + 1]
      (Tape.mk' (ListBlank.mk (List.replicate k none ++
        (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))).head.isSome = true := by
  have hh := tape_move_left_head' (List.replicate k none ++
    (tapeSymbols out).reverse) (ListBlank.mk (none :: R)) k
  have hget : ((List.replicate k (none : Option Bool) ++
      (tapeSymbols out).reverse).getD k none).isSome = true := by
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_replicate]
    have hrev : 0 < (tapeSymbols out).reverse.length := by
      simp [tapeSymbols]
      omega
    rw [show k - k = 0 by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hrev]
    simp [tapeSymbols]
  rw [hh, hget]

noncomputable def encWriteStart (xs rest : List Bool) : Tape (Option Bool) :=
  match xs with
  | [] =>
      Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: none :: tapeSymbols rest))
  | _ :: _ =>
      Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: tapeSymbols (encOut tm inp xs) ++
          List.replicate xs.length none ++ none :: tapeSymbols rest))

/-- Gap phase of `enc_seek_to_write`: skip the blank gap and the first output cell,
generic in the remaining tape `R`. -/
lemma enc_seek_to_write_gap (isBottom b : Bool) (k : ℕ) (out : List Bool)
    (R : List (Option Bool)) (hout : 0 < out.length) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutLeft true isBottom b,
        Tape.mk' (ListBlank.mk (List.replicate k none ++
          (tapeSymbols out).reverse)) (ListBlank.mk (none :: R))⟩
      ⟨.seekOutBlock isBottom b,
        (Tape.move Dir.left)^[k + 2]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))⟩
      (k + 1 + 1) := by
  have hwalk := enc_seekOutLeft_walk tm inp isBottom b _ (k + 1)
    (enc_gap_heads k out R)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (enc_output_first_head k out R hout)
  have hstep := enc_seekOutLeft_true_some tm inp isBottom b _ hx
  have h := stepsTo_trans _ hwalk (stepsTo_cons _ hstep (stepsTo_zero _ _))
  rw [Function.iterate_succ_apply']
  rwa [show k + 1 + 1 = 0 + 1 + (k + 1) by omega]

/-- Output phase of `enc_seek_to_write`: walk over the written output cells. -/
lemma enc_seek_to_write_block (isBottom b : Bool) (k : ℕ) (out : List Bool)
    (R : List (Option Bool)) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutBlock isBottom b,
        (Tape.move Dir.left)^[k + 2]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))⟩
      ⟨.seekOutBlock isBottom b,
        (Tape.move Dir.left)^[k + 2 + (out.length - 1)]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk (none :: R)))⟩
      (out.length - 1) := by
  have h := enc_seekOutBlock_walk tm inp isBottom b _ (out.length - 1)
    (fun i hi => by
      rw [← Function.iterate_add_apply, Nat.add_comm]
      exact enc_output_head_some k out R i hi)
  rwa [← Function.iterate_add_apply, Nat.add_comm (out.length - 1)] at h

/-- The head position reached after the output walk, as an explicit tape. -/
lemma enc_seek_to_write_tape (k : ℕ) (out : List Bool)
    (R : List (Option Bool)) (hout : 0 < out.length) :
    (Tape.move Dir.left)^[k + 2 + (out.length - 1)]
      (Tape.mk' (ListBlank.mk (List.replicate k none ++
        (tapeSymbols out).reverse)) (ListBlank.mk (none :: R))) =
      Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: tapeSymbols out ++ List.replicate k none ++
          none :: R)) := by
  have hlen : (List.replicate k none ++ (tapeSymbols out).reverse).length + 1 =
      k + 2 + (out.length - 1) := by
    simp [tapeSymbols]
    omega
  rw [← hlen, tape_move_left_past]
  simp [tapeSymbols]

lemma enc_seek_to_write (xs : List Bool) (b c : Bool) (ys : List Bool)
    (hxs : xs ≠ []) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutLeft true false b, encCheck tm inp xs (c :: ys)⟩
      ⟨.writeLeftMove false b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        (encWriteStart tm inp xs (c :: ys)).write
          (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩
      (xs.length + (encOut tm inp xs).length + 2) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons a xs =>
      have hout : 0 < (encOut tm inp (a :: xs)).length := by
        rw [encOut_length]
        have hn := encN_pos tm
        simp
        omega
      have h₁ := enc_seek_to_write_gap tm inp false b (a :: xs).length
        (encOut tm inp (a :: xs)) (tapeSymbols (c :: ys)) hout
      have h₂ := enc_seek_to_write_block tm inp false b (a :: xs).length
        (encOut tm inp (a :: xs)) (tapeSymbols (c :: ys))
      have hT := enc_seek_to_write_tape (a :: xs).length
        (encOut tm inp (a :: xs)) (tapeSymbols (c :: ys)) hout
      rw [hT] at h₂
      have h₃ := enc_seekOutBlock_none_nonbottom tm inp b
        (Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (none :: tapeSymbols (encOut tm inp (a :: xs)) ++
            List.replicate (a :: xs).length none ++
              none :: tapeSymbols (c :: ys)))) (by simp)
      have h := stepsTo_trans _ (stepsTo_trans _ h₁ h₂)
        (stepsTo_cons _ h₃ (stepsTo_zero _ _))
      have hcheck : encCheck tm inp (a :: xs) (c :: ys) =
          Tape.mk' (ListBlank.mk (List.replicate (a :: xs).length none ++
            (tapeSymbols (encOut tm inp (a :: xs))).reverse))
            (ListBlank.mk (none :: tapeSymbols (c :: ys))) := rfl
      have htime : (a :: xs).length + (encOut tm inp (a :: xs)).length + 2 =
          0 + 1 + ((encOut tm inp (a :: xs)).length - 1 +
            ((a :: xs).length + 1 + 1)) := by omega
      rw [hcheck, htime]
      exact h

lemma enc_return_to_check (out : List Bool) (k : ℕ) (c : Bool)
    (ys : List Bool) (hout : 0 < out.length) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.returnRight,
        Tape.mk' (ListBlank.mk [some (out.getD 0 false)])
          (ListBlank.mk (((out.drop 1).map some ++
            List.replicate (k + 1) none ++ some c :: tapeSymbols ys)))⟩
      ⟨.checkLast true c,
        Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++
          (tapeSymbols out).reverse))
          (ListBlank.mk (none :: tapeSymbols ys))⟩
      (out.length - 1 + 1 + k + 1) := by
  cases out with
  | nil => simp at hout
  | cons a out =>
      have hshift : ∀ (xs : List (Option Bool)),
          List.replicate k none ++ (none :: xs) =
            none :: (List.replicate k none ++ xs) := by
        intro xs
        induction k with
        | zero => simp
        | succ k ih => simp [List.replicate_succ, ih]
      let R := List.replicate (k + 1) none ++ some c :: tapeSymbols ys
      let T := Tape.mk' (ListBlank.mk [some a])
        (ListBlank.mk ((out.map some) ++ R))
      have hwalk := enc_returnRight_walk tm inp T out.length
        (by
          intro i hi
          exact enc_right_output_heads (a :: out) R i (by simp; omega))
      have hhead : ((Tape.move Dir.right)^[out.length] T).head = none := by
        have hh := tape_move_right_head' (ListBlank.mk [some a])
          (out.map some ++ R) out.length
        rw [hh]
        have happend : (out.map some).length ≤ out.length := by simp
        rw [List.getD_append_right _ _ _ _ happend]
        simp [R, List.replicate_succ]
      have hstep := enc_returnRight_none tm inp
        ((Tape.move Dir.right)^[out.length] T) hhead
      have hmove : ((Tape.move Dir.right)^[out.length] T).move Dir.right =
          Tape.mk' (ListBlank.mk (none :: (out.map some).reverse ++ [some a]))
            (ListBlank.mk (List.replicate k none ++ some c :: tapeSymbols ys)) := by
        have hp := tape_move_right_prefix [some a]
          (out.map some) R
        rw [show (out.map some).length = out.length by simp] at hp
        rw [hp]
        simp [R, List.replicate_succ, List.headI, Tape.move_right_mk',
          ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
      have hgap := enc_returnGap_walk tm inp
        (Tape.mk' (ListBlank.mk (none :: (out.map some).reverse ++ [some a]))
          (ListBlank.mk (List.replicate k none ++ some c :: tapeSymbols ys))) k
        (by
          intro i hi
          have hh := tape_move_right_head'
            (ListBlank.mk (none :: (out.map some).reverse ++ [some a]))
            (List.replicate k none ++ some c :: tapeSymbols ys) i
          rw [hh]
          have hi' : i < (List.replicate k (none : Option Bool)).length := by simpa
          rw [List.getD_append (List.replicate k none)
            (some c :: tapeSymbols ys) none i hi', List.getD_replicate none hi])
      have hgap_tape : (Tape.move Dir.right)^[k]
          (Tape.mk' (ListBlank.mk (none :: (out.map some).reverse ++ [some a]))
            (ListBlank.mk (List.replicate k none ++ some c :: tapeSymbols ys))) =
          Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++
            (tapeSymbols (a :: out)).reverse))
            (ListBlank.mk (some c :: tapeSymbols ys)) := by
        have hp := tape_move_right_prefix
          (none :: (out.map some).reverse ++ [some a])
          (List.replicate k none) (some c :: tapeSymbols ys)
        rw [show (List.replicate k none).length = k by simp] at hp
        rw [hp]
        rw [List.reverse_replicate]
        rw [← List.append_assoc]
        rw [hshift (out.map some).reverse]
        simp [List.replicate_succ, tapeSymbols, List.reverse_cons]
      have hlast := enc_returnGap_some tm inp
        (Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++
          (tapeSymbols (a :: out)).reverse))
          (ListBlank.mk (some c :: tapeSymbols ys))) (b := c) (by simp)
      rw [hmove] at hstep
      rw [hgap_tape] at hgap
      have h₁ := stepsTo_trans _ hwalk (stepsTo_cons _ hstep (stepsTo_zero _ _))
      have h₂ := stepsTo_trans _ h₁
        (stepsTo_trans _ hgap (stepsTo_cons _ hlast (stepsTo_zero _ _)))
      convert h₂ using 1 <;> try simp [T, R, tapeSymbols]
      all_goals omega

/-- Seek phase of `enc_nonbottom_run_nil`: check the flag, look ahead, position the head,
    and write the block's top bit. -/
lemma enc_nonbottom_run_nil_seek (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (([] : List Bool) ≠ []) b, encCheck tm inp [] (c :: ys)⟩
      ⟨.writeLeftMove false b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none ::
          (none :: tapeSymbols (c :: ys))))).write
          (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩
      (1 + 1 + 1 + 1) := by
  let T0 := encCheck tm inp [] (c :: ys)
  let Ti := ((T0.move Dir.right).move Dir.left).move Dir.left
  have hc := enc_checkLast tm inp false b T0
  have hl := enc_lookAhead_some tm inp false b (T0.move Dir.right) (x := c)
    (by simp [T0, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk])
  have hs := enc_seekOutLeft_false tm inp false b
    ((T0.move Dir.right).move Dir.left)
    (by simp [T0, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk])
  have hw : TM0.step (encMachine tm inp)
      ⟨.writeLeft false b ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩, Ti⟩ =
      some ⟨.writeLeftMove false b
        ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        Ti.write (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩ := by
    by_cases hz : encN tm - 1 = 0
    · simpa using enc_writeLeft_zero tm inp false b
        ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩ Ti hz
    · exact enc_writeLeft_succ tm inp false b
        ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩ Ti hz
  have hTi : Ti = Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (none :: none :: tapeSymbols (c :: ys))) := by
    simp [Ti, T0, encCheck, encLeft, encOut, tapeSymbols, default,
      Tape.move_right_mk', Tape.move_left_mk', ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]
  rw [hTi] at hw
  exact stepsTo_cons _ hc (stepsTo_cons _ hl (stepsTo_cons _ hs
    (stepsTo_cons _ hw (stepsTo_zero _ _))))

/-- Return phase of `enc_nonbottom_run_nil`: after the block is written, walk back to the check cell. -/
lemma enc_nonbottom_run_nil_return (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.returnRight,
        Tape.mk' (ListBlank.mk [some ((encBlock tm inp false b).getD 0 false)])
          (ListBlank.mk (((encBlock tm inp false b).drop 1).map some ++
            none :: some c :: tapeSymbols ys))⟩
      ⟨.checkLast true c, encCheck tm inp [b] ys⟩
      ((encBlock tm inp false b).length - 1 + 1 + 0 + 1) := by
  have hret := enc_return_to_check tm inp (encBlock tm inp false b) 0 c ys
    (by rw [encBlock_length]; exact encN_pos tm)
  simpa [encCheck, encLeft, encOut, tapeSymbols, List.replicate_succ,
    List.reverse_cons] using hret

/-- Empty-prefix case of `enc_nonbottom_run`: write the first (non-bottom) block, then return to the check cell. -/
lemma enc_nonbottom_run_nil (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (([] : List Bool) ≠ []) b, encCheck tm inp [] (c :: ys)⟩
      ⟨.checkLast true c, encCheck tm inp ([] ++ [b]) ys⟩
      (3 * encN tm + 2 * ([] : List Bool).length * encN tm + 2 * ([] : List Bool).length + 4) := by
  have hs := enc_nonbottom_run_nil_seek tm inp b c ys
  have hb := enc_block_write_nonbottom tm inp (none :: tapeSymbols (c :: ys)) b
  have hr := enc_nonbottom_run_nil_return tm inp b c ys
  have h := stepsTo_trans _ (stepsTo_trans _ hs hb) hr
  have hn := encN_pos tm
  have hlen := encBlock_length tm inp false b
  convert h using 1
  all_goals first
    | rfl
    | (simp only [List.length_nil]; omega)

/-- Seek phase of `enc_nonbottom_run_cons`: check the flag, look ahead, walk to the write
    position, and write the block's top bit. -/
lemma enc_nonbottom_run_cons_seek (a : Bool) (xs : List Bool) (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (a :: xs ≠ []) b, encCheck tm inp (a :: xs) (c :: ys)⟩
      ⟨.writeLeftMove false b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none ::
          (tapeSymbols (encOut tm inp (a :: xs)) ++
            List.replicate (a :: xs).length none ++
              none :: tapeSymbols (c :: ys))))).write
          (some ((encBlock tm inp false b).getD (encN tm - 1) false))⟩
      ((a :: xs).length + (encOut tm inp (a :: xs)).length + 2 + 1 + 1) := by
  let pref := a :: xs
  let T := encCheck tm inp pref (c :: ys)
  have hc := enc_checkLast tm inp true b T
  have hl := enc_lookAhead_some tm inp true b (T.move Dir.right) (x := c)
    (by simp [T, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk])
  have hs := enc_seek_to_write tm inp pref b c ys (by simp [pref])
  have hd : decide (a :: xs ≠ []) = true := by simp
  have hpre := stepsTo_cons _ hc (stepsTo_cons _ hl hs)
  rw [hd]
  exact hpre

/-- Return phase of `enc_nonbottom_run_cons`: after the block is written, walk back to the check cell. -/
lemma enc_nonbottom_run_cons_return (a : Bool) (xs : List Bool) (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.returnRight,
        Tape.mk' (ListBlank.mk [some ((encBlock tm inp false b).getD 0 false)])
          (ListBlank.mk (((encBlock tm inp false b).drop 1).map some ++
            (tapeSymbols (encOut tm inp (a :: xs)) ++
              List.replicate (a :: xs).length none ++
                none :: tapeSymbols (c :: ys))))⟩
      ⟨.checkLast true c, encCheck tm inp ((a :: xs) ++ [b]) ys⟩
      ((encBlock tm inp false b ++ encOut tm inp (a :: xs)).length - 1 + 1 +
        (a :: xs).length + 1) := by
  have hshift : ∀ (n : ℕ) (z : List (Option Bool)),
      List.replicate n none ++ (none :: z) =
        none :: (List.replicate n none ++ z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih => intro z; simp [List.replicate_succ, ih]
  have hR : tapeSymbols (encOut tm inp (a :: xs)) ++
      List.replicate (a :: xs).length none ++ none :: tapeSymbols (c :: ys) =
        tapeSymbols (encOut tm inp (a :: xs)) ++ none :: none ::
          (List.replicate xs.length none ++ some c :: tapeSymbols ys) := by
    simp [List.replicate_succ, List.append_assoc, tapeSymbols]
    rw [hshift xs.length]
  have hblockne : (encBlock tm inp false b).map some ≠ [] := by
    intro h
    have hz : (encBlock tm inp false b).length = 0 := by
      calc
        _ = ((encBlock tm inp false b).map some).length := by simp
        _ = [].length := congrArg List.length h
        _ = 0 := rfl
    rw [encBlock_length] at hz
    exact (Nat.ne_of_gt (encN_pos tm)) hz
  have hret := enc_return_to_check tm inp (encBlock tm inp false b ++ encOut tm inp (a :: xs))
    (a :: xs).length c ys
    (by
      have hn := encN_pos tm
      simp [encBlock_length, encOut_length]
      omega)
  have hget : (encBlock tm inp false b ++ encOut tm inp (a :: xs)).getD 0 false = (encBlock tm inp false b).getD 0 false := by
    have hpos : 0 < (encBlock tm inp false b).length := by
      rw [encBlock_length]
      exact encN_pos tm
    rw [List.getD_append (encBlock tm inp false b) (encOut tm inp (a :: xs))
      false 0 hpos]
  have hdrop : ((encBlock tm inp false b ++ encOut tm inp (a :: xs)).drop 1).map some =
      ((encBlock tm inp false b).drop 1).map some ++
        tapeSymbols (encOut tm inp (a :: xs)) := by
    rw [List.drop_one, List.map_tail]
    rw [show (encBlock tm inp false b ++ encOut tm inp (a :: xs)).map some =
        (encBlock tm inp false b).map some ++
          (encOut tm inp (a :: xs)).map some by simp [List.map_append]]
    rw [List.tail_append_of_ne_nil hblockne]
    rw [← List.map_tail, List.drop_one]
    rfl
  rw [hget, hdrop] at hret
  rw [hR]
  simpa [encCheck, encLeft, encOut, tapeSymbols,
    List.replicate_succ, List.reverse_append, List.append_assoc,
    List.reverse_cons] using hret

/-- Non-empty-prefix case of `enc_nonbottom_run`: seek to the write position, write a block, return. -/
lemma enc_nonbottom_run_cons (a : Bool) (xs : List Bool) (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (a :: xs ≠ []) b, encCheck tm inp (a :: xs) (c :: ys)⟩
      ⟨.checkLast true c, encCheck tm inp ((a :: xs) ++ [b]) ys⟩
      (3 * encN tm + 2 * (a :: xs).length * encN tm + 2 * (a :: xs).length + 4) := by
  have hs := enc_nonbottom_run_cons_seek tm inp a xs b c ys
  have hb := enc_block_write_nonbottom tm inp
    (tapeSymbols (encOut tm inp (a :: xs)) ++
      List.replicate (a :: xs).length none ++ none :: tapeSymbols (c :: ys)) b
  have hr := enc_nonbottom_run_cons_return tm inp a xs b c ys
  have h := stepsTo_trans _ (stepsTo_trans _ hs hb) hr
  have hn := encN_pos tm
  convert h using 1
  simp only [List.length_append, encBlock_length, encOut_length, List.length_cons]
  obtain ⟨k, hk⟩ : ∃ k, encN tm = k + 1 := ⟨encN tm - 1, by omega⟩
  rw [hk]
  have h2 : 2 * (xs.length + 1) * (k + 1) = 2 * ((xs.length + 1) * (k + 1)) := by ring
  generalize (xs.length + 1) * (k + 1) = z at h2 ⊢
  omega

lemma enc_nonbottom_run (xs : List Bool) (b c : Bool) (ys : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (xs ≠ []) b, encCheck tm inp xs (c :: ys)⟩
      ⟨.checkLast true c, encCheck tm inp (xs ++ [b]) ys⟩
      (3 * encN tm + 2 * xs.length * encN tm + 2 * xs.length + 4) := by
  cases xs with
  | nil => exact enc_nonbottom_run_nil tm inp b c ys
  | cons a xs => exact enc_nonbottom_run_cons tm inp a xs b c ys

/-- Gap phase of `enc_seek_to_bottom`: skip the blank gap and the first output cell. -/
lemma enc_seek_to_bottom_gap (b : Bool) (k : ℕ) (out : List Bool)
    (hout : 0 < out.length) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutLeft true true b,
        Tape.mk' (ListBlank.mk (List.replicate k none ++
          (tapeSymbols out).reverse)) (ListBlank.mk [none])⟩
      ⟨.seekOutBlock true b,
        (Tape.move Dir.left)^[k + 2]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk [none]))⟩
      (k + 1 + 1) :=
  enc_seek_to_write_gap tm inp true b k out [] hout

/-- Output phase of `enc_seek_to_bottom`: walk over the written output cells. -/
lemma enc_seek_to_bottom_block (b : Bool) (k : ℕ) (out : List Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutBlock true b,
        (Tape.move Dir.left)^[k + 2]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk [none]))⟩
      ⟨.seekOutBlock true b,
        (Tape.move Dir.left)^[k + 2 + (out.length - 1)]
          (Tape.mk' (ListBlank.mk (List.replicate k none ++
            (tapeSymbols out).reverse)) (ListBlank.mk [none]))⟩
      (out.length - 1) :=
  enc_seek_to_write_block tm inp true b k out []

/-- The head position reached after the output walk, as an explicit tape. -/
lemma enc_seek_to_bottom_tape (k : ℕ) (out : List Bool)
    (hout : 0 < out.length) :
    (Tape.move Dir.left)^[k + 2 + (out.length - 1)]
      (Tape.mk' (ListBlank.mk (List.replicate k none ++
        (tapeSymbols out).reverse)) (ListBlank.mk [none])) =
      Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: tapeSymbols out ++ List.replicate k none ++
          [none])) :=
  enc_seek_to_write_tape (R := []) (hout := hout) k out

/-- `encCheck` on an empty right side is the generic gap tape with `R = []`. -/
lemma enc_seek_to_bottom_check (pref out : List Bool)
    (h : encOut tm inp pref = out) :
    encCheck tm inp pref [] =
      Tape.mk' (ListBlank.mk (List.replicate pref.length none ++
        (tapeSymbols out).reverse)) (ListBlank.mk [none]) := by
  subst h
  simp [encCheck, encLeft, tapeSymbols]

lemma enc_seek_to_bottom (xs : List Bool) (b : Bool) (hxs : xs ≠ []) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutLeft true true b, encCheck tm inp xs []⟩
      ⟨.seekOutBlock true b, encWriteStart tm inp xs []⟩
      (xs.length + (encOut tm inp xs).length + 1) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons a xs =>
      let pref := a :: xs
      let out := encOut tm inp pref
      have hout : 0 < out.length := by
        rw [encOut_length]
        have hn := encN_pos tm
        simp [pref]
        omega
      have hcheck := enc_seek_to_bottom_check tm inp pref out rfl
      have hgap := enc_seek_to_bottom_gap tm inp b pref.length out hout
      rw [← hcheck] at hgap
      have hblock := enc_seek_to_bottom_block tm inp b pref.length out
      have hT := enc_seek_to_bottom_tape pref.length out hout
      have hstart : encWriteStart tm inp pref [] =
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (none :: tapeSymbols out ++
              List.replicate pref.length none ++ [none])) := by
        simp [encWriteStart, pref, out, tapeSymbols]
      have hfinish := hblock
      rw [hT] at hfinish
      rw [← hstart] at hfinish
      have htime : pref.length + out.length + 1 =
          out.length - 1 + (pref.length + 1 + 1) := by omega
      rw [htime]
      exact stepsTo_trans (TM0.step (encMachine tm inp)) hgap hfinish

lemma enc_block_write_bottom_tail (R : List (Option Bool)) (b : Bool)
    (i : ℕ) (hi : i < encN tm) (hzero : i ≠ 0) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.writeLeftMove true b ⟨i, hi⟩,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (some ((encBlock tm inp true b).getD i false) ::
            ((encBlock tm inp true b).drop (i + 1)).map some ++ R))⟩
      ⟨.done,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk ((encBlock tm inp true b).map some ++ R))⟩
      (2 * i) := by
  let bits := encBlock tm inp true b
  let T := Tape.mk' (ListBlank.mk [])
    (ListBlank.mk (some (bits.getD i false) ::
      (bits.drop (i + 1)).map some ++ R))
  have hstep := enc_writeLeftMove_succ tm inp true b ⟨i, hi⟩ T hzero
  have himinus : i - 1 < encN tm :=
    lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hzero) (by omega)) hi
  have hleft := enc_block_write_bottom_left tm inp R b (i - 1) himinus
  have hdrop := enc_drop_cons bits i (by rw [encBlock_length]; exact hi)
  have hipos : 0 < i := Nat.pos_of_ne_zero hzero
  have hidx : i - 1 + 1 = i :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
  change StepsTo (TM0.step (encMachine tm inp))
    ⟨.writeLeftMove true b ⟨i, hi⟩, T⟩ _ (2 * i)
  have hmid : StepsTo (TM0.step (encMachine tm inp))
      ⟨.writeLeft true b ⟨i - 1, himinus⟩, T.move Dir.left⟩
      ⟨.done, Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (bits.map some ++ R))⟩ (2 * i - 1) := by
    convert hleft using 1 <;>
      try simp [T, bits, hdrop, hidx, List.map_drop, Tape.move_left_mk',
        ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, default]
    all_goals omega
  have htime : 2 * i - 1 + 1 = 2 * i := by omega
  simpa [bits, htime] using (stepsTo_cons _ hstep hmid)

lemma enc_seekOutBlock_bottom_one (R : List (Option Bool)) (b : Bool)
    (hN : encN tm = 1) :
    TM0.step (encMachine tm inp)
      ⟨.seekOutBlock true b,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))⟩ =
      some ⟨.done,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (some ((encBlock tm inp true b).getD 0 false) :: R))⟩ := by
  simp [TM0.step, encMachine, hN]

lemma enc_seekOutBlock_bottom_succ (R : List (Option Bool)) (b : Bool)
    (hN : encN tm ≠ 1) :
    TM0.step (encMachine tm inp)
      ⟨.seekOutBlock true b,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))⟩ =
      some ⟨.writeLeftMove true b
          ⟨encN tm - 1, Nat.sub_lt (encN_pos tm) (by omega)⟩,
        (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))).write
          (some ((encBlock tm inp true b).getD (encN tm - 1) false))⟩ := by
  have hpos := encN_pos tm
  have hsub : encN tm - 1 ≠ 0 := by omega
  have hsub' :
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n - 1 ≠ 0 := by
    simpa [encN] using hsub
  simp [TM0.step, encMachine, encN, hpos, hsub]

/-- Empty-prefix case of `enc_bottom_run`: the single bottom block is written with no output. -/
lemma enc_bottom_run_nil (b : Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (([] : List Bool) ≠ []) b, encCheck tm inp [] []⟩
      ⟨.done, Tape.mk₁ (tapeSymbols (encBlock tm inp true b ++ encOut tm inp []))⟩
      (2 * encN tm + ([] : List Bool).length * encN tm + ([] : List Bool).length + 2) := by
  let T0 := encCheck tm inp [] []
  have hc := enc_checkLast tm inp false b T0
  have hl := enc_lookAhead_none tm inp false b (T0.move Dir.right)
    (by simp [T0, encCheck, encLeft, tapeSymbols, default, Tape.move_right_mk',
      ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk])
  have hs := enc_seekOutLeft_false tm inp true b
    ((T0.move Dir.right).move Dir.left)
    (by simp [T0, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk])
  have hb := enc_block_write_bottom tm inp [] b
  have hq : ListBlank.mk ([none, none] : List (Option Bool)) =
      ListBlank.mk ([none] : List (Option Bool)) := by
    apply Quotient.sound'
    exact Or.inr ⟨1, by simp [default]⟩
  have hTi : ((T0.move Dir.right).move Dir.left).move Dir.left =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk [none]) := by
    have hraw : ((T0.move Dir.right).move Dir.left).move Dir.left =
        Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none]) := by
      simp [T0, encCheck, encLeft, encOut, tapeSymbols, default,
        Tape.move_right_mk', Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk]
    exact hraw.trans (congrArg (fun R => Tape.mk' (ListBlank.mk []) R) hq)
  have hpre := stepsTo_cons _ hc
    (stepsTo_cons _ hl (stepsTo_cons _ hs (stepsTo_zero _ _)))
  rw [hTi] at hpre
  have hrun := stepsTo_trans _ hpre hb
  have hn := encN_pos tm
  convert hrun using 1 <;>
    simp [T0, encCheck, encLeft, encOut, tapeSymbols, Tape.mk₁, Tape.mk₂]
  all_goals omega

/-- Non-empty case of `enc_bottom_run`: check the last flag, then seek to the bottom block. -/
lemma enc_bottom_run_cons_seek (a : Bool) (xs : List Bool) (b : Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (a :: xs ≠ []) b, encCheck tm inp (a :: xs) []⟩
      ⟨.seekOutBlock true b,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none ::
          (tapeSymbols (encOut tm inp (a :: xs)) ++
            List.replicate (xs.length + 1) none ++ [none])))⟩
      (xs.length + 1 + (encOut tm inp (a :: xs)).length + 1 + 2) := by
  let pref := a :: xs
  let out := encOut tm inp pref
  let R := tapeSymbols out ++ List.replicate pref.length none ++ [none]
  let T := encCheck tm inp pref []
  have hc := enc_checkLast tm inp true b T
  have hl := enc_lookAhead_none tm inp true b (T.move Dir.right)
    (by simp [T, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, default])
  have hT : (T.move Dir.right).move Dir.left = T := by
    simp [T, encCheck, encLeft, tapeSymbols, Tape.move_right_mk',
      Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk]
  rw [hT] at hl
  have hs := enc_seek_to_bottom tm inp pref b (by simp [pref])
  have hstart : encWriteStart tm inp pref [] =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R)) := by
    simp [encWriteStart, R, out, pref, tapeSymbols]
  rw [hstart] at hs
  exact stepsTo_trans _ (stepsTo_cons _ hc (stepsTo_cons _ hl (stepsTo_zero _ _))) hs

/-- Final step of `enc_bottom_run` when blocks have length one. -/
lemma enc_bottom_run_cons_finish_one (a : Bool) (xs : List Bool) (b : Bool)
    (hN : encN tm = 1) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutBlock true b,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none ::
          (tapeSymbols (encOut tm inp (a :: xs)) ++
            List.replicate (xs.length + 1) none ++ [none])))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols (encBlock tm inp true b ++ encOut tm inp (a :: xs)))⟩
      1 := by
  let R := tapeSymbols (encOut tm inp (a :: xs)) ++
    List.replicate (xs.length + 1) none ++ [none]
  have hlen : (encBlock tm inp true b).length = 1 := by
    rw [encBlock_length, hN]
  have hB : encBlock tm inp true b = [(encBlock tm inp true b).getD 0 false] := by
    cases hlist : encBlock tm inp true b with
    | nil => simp [hlist] at hlen
    | cons x l =>
        cases l with
        | nil => simp [List.getD]
        | cons y l => simp [hlist] at hlen
  have hstep := enc_seekOutBlock_bottom_one tm inp R b hN
  have hrun := stepsTo_cons _ hstep (stepsTo_zero _ _)
  convert hrun using 2
  simp only [Tape.mk₁, Tape.mk₂]
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  apply Quotient.sound'
  apply Or.inl
  refine ⟨xs.length + 2, ?_⟩
  rw [hB]
  simp [tapeSymbols, R, default, List.replicate_succ', List.append_assoc]

/-- Final step of `enc_bottom_run` when blocks have length above one. -/
lemma enc_bottom_run_cons_finish_succ (a : Bool) (xs : List Bool) (b : Bool)
    (hN : encN tm ≠ 1) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.seekOutBlock true b,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none ::
          (tapeSymbols (encOut tm inp (a :: xs)) ++
            List.replicate (xs.length + 1) none ++ [none])))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols (encBlock tm inp true b ++ encOut tm inp (a :: xs)))⟩
      (2 * (encN tm - 1) + 1) := by
  let R := tapeSymbols (encOut tm inp (a :: xs)) ++
    List.replicate (xs.length + 1) none ++ [none]
  have hstep := enc_seekOutBlock_bottom_succ tm inp R b hN
  have htail : (encBlock tm inp true b).drop (encN tm) = [] := by
    apply List.drop_eq_nil_of_le
    simp [encBlock_length tm inp true b]
  have htailrun := enc_block_write_bottom_tail tm inp R b (encN tm - 1)
    (Nat.sub_lt (encN_pos tm) (by omega)) (by have := encN_pos tm; omega)
  have hidx : encN tm - 1 + 1 = encN tm := by have := encN_pos tm; omega
  rw [hidx, htail] at htailrun
  have hwrite : (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))).write
      (some ((encBlock tm inp true b).getD (encN tm - 1) false)) =
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (some ((encBlock tm inp true b).getD (encN tm - 1) false) :: R)) := by
    simp [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]
  rw [hwrite] at hstep
  have hrun := stepsTo_cons _ hstep htailrun
  convert hrun using 2
  simp only [Tape.mk₁, Tape.mk₂]
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  apply Quotient.sound'
  apply Or.inl
  refine ⟨xs.length + 2, ?_⟩
  simp [tapeSymbols, R, default, List.replicate_succ', List.append_assoc]

lemma enc_bottom_run (xs : List Bool) (b : Bool) :
    StepsTo (TM0.step (encMachine tm inp))
      ⟨.checkLast (xs ≠ []) b, encCheck tm inp xs []⟩
      ⟨.done, Tape.mk₁ (tapeSymbols (encBlock tm inp true b ++ encOut tm inp xs))⟩
      (2 * encN tm + xs.length * encN tm + xs.length + 2) := by
  cases xs with
  | nil => exact enc_bottom_run_nil tm inp b
  | cons a xs =>
      have hseek := enc_bottom_run_cons_seek tm inp a xs b
      have hlen : (encOut tm inp (a :: xs)).length = (xs.length + 1) * encN tm := by
        rw [encOut_length]
        simp
      obtain ⟨k, hk⟩ : ∃ k, encN tm = k + 1 := ⟨encN tm - 1, by have := encN_pos tm; omega⟩
      by_cases hN : encN tm = 1
      · have hrun := stepsTo_trans _ hseek (enc_bottom_run_cons_finish_one tm inp a xs b hN)
        convert hrun using 1
        simp only [List.length_cons, hlen, hN]
        omega
      · have hrun := stepsTo_trans _ hseek (enc_bottom_run_cons_finish_succ tm inp a xs b hN)
        convert hrun using 1
        simp only [List.length_cons, hlen, hk, Nat.add_sub_cancel]
        ring

lemma enc_check_run (pref : List Bool) (b : Bool) (rest : List Bool) :
    ∃ q t,
      t ≤ (rest.length + 1) *
          (3 * encN tm + 2 * (pref.length + rest.length + 1) * encN tm +
            2 * (pref.length + rest.length + 1) + 4) ∧
      StepsTo (TM0.step (encMachine tm inp))
        ⟨.checkLast (pref ≠ []) b, encCheck tm inp pref rest⟩
        ⟨q, Tape.mk₁ (tapeSymbols
          (encodePackedInput tm inp (pref ++ b :: rest)))⟩ t ∧
      TM0.step (encMachine tm inp)
        ⟨q, Tape.mk₁ (tapeSymbols
          (encodePackedInput tm inp (pref ++ b :: rest)))⟩ = none := by
  cases rest with
  | nil =>
      have hrun := enc_bottom_run tm inp pref b
      refine ⟨.done, 2 * encN tm + pref.length * encN tm + pref.length + 2,
        ?_, ?_, enc_done_halt tm inp _⟩
      · have hn := encN_pos tm
        have hp : pref.length ≤ pref.length + 1 := by omega
        have hpn : pref.length * encN tm ≤ (pref.length + 1) * encN tm :=
          Nat.mul_le_mul_right _ hp
        have hpn2 : 2 * pref.length * encN tm ≤
            2 * (pref.length + 1) * encN tm := by
          exact Nat.mul_le_mul_right _ (by omega)
        have hpnE : pref.length * encN tm ≤ 2 * pref.length * encN tm := by
          exact Nat.mul_le_mul_right _ (by omega)
        simpa only [Nat.one_mul, List.length_nil, Nat.add_zero, Nat.zero_add] using show
          2 * encN tm + pref.length * encN tm + pref.length + 2 ≤
            3 * encN tm + 2 * (pref.length + 1) * encN tm +
              2 * (pref.length + 1) + 4 by omega
      · have henc := encodePackedInput_snoc tm inp pref b
        rw [henc]
        simpa [encOut] using hrun
  | cons c rest =>
      obtain ⟨q, t, ht, hsteps, hhalt⟩ :=
        enc_check_run (pref ++ [b]) c rest
      have hnb := enc_nonbottom_run tm inp pref b c rest
      have hsteps' : StepsTo (TM0.step (encMachine tm inp))
          ⟨.checkLast true c, encCheck tm inp (pref ++ [b]) rest⟩
          ⟨q, Tape.mk₁ (tapeSymbols
            (encodePackedInput tm inp (pref ++ [b] ++ c :: rest)))⟩ t := by
        simpa using hsteps
      have htrans := stepsTo_trans _ hnb hsteps'
      let A := 3 * encN tm + 2 * pref.length * encN tm + 2 * pref.length + 4
      let C := 3 * encN tm + 2 * (pref.length + rest.length + 2) * encN tm +
        2 * (pref.length + rest.length + 2) + 4
      refine ⟨q, t + A, ?_, ?_, ?_⟩
      · have hn := encN_pos tm
        have hp : pref.length ≤ pref.length + rest.length + 2 := by omega
        have hpn : pref.length * encN tm ≤
            (pref.length + rest.length + 2) * encN tm :=
          Nat.mul_le_mul_right _ hp
        have hpn2 : 2 * pref.length * encN tm ≤
            2 * (pref.length + rest.length + 2) * encN tm := by
          exact Nat.mul_le_mul_right _ (by omega)
        have hA : A ≤ C := by
          dsimp [A, C]
          omega
        have ht' : t ≤ (rest.length + 1) * C := by
          simpa [C, List.length_append, List.length_cons, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using ht
        have hmul : (rest.length + 1) * C + C = (rest.length + 2) * C := by
          ring
        change t + A ≤ (rest.length + 2) * C
        omega
      · simpa [A, List.append_assoc] using htrans
      · simpa [List.append_assoc] using hhalt

lemma tapeOnBit_shiftHome_heads (bits : List Bool) (N i : ℕ)
    (hbits : N ≤ bits.length) (hi : i < N - 1) :
    ((Tape.move Dir.left)^[i]
      ((tapeOnBit bits (N - 1)).move Dir.left)).head.isSome = true := by
  have hiter : (Tape.move Dir.left)^[i]
      ((tapeOnBit bits (N - 1)).move Dir.left) =
      (Tape.move Dir.left)^[i + 1] (tapeOnBit bits (N - 1)) := by
    exact (Function.iterate_add_apply (Tape.move Dir.left) i 1
      (tapeOnBit bits (N - 1))).symm
  rw [hiter]
  have hh := tape_move_left_head' (encPref bits (N - 1))
    (ListBlank.mk [some (bits.getD (N - 1) false)]) i
  have hh' : ((Tape.move Dir.left)^[i + 1]
      (tapeOnBit bits (N - 1))).head =
      (encPref bits (N - 1)).getD i none := by
    simpa [tapeOnBit] using hh
  rw [hh']
  have hL : (encPref bits (N - 1)).length = N - 1 := by
    simp [encPref, List.length_map, List.length_take]
    omega
  have hiL : i < (encPref bits (N - 1)).length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL,
    Option.getD_some]
  simp [encPref]

lemma tapeOnBit_shiftHome_none (bits : List Bool) (N : ℕ)
    (hN : 0 < N) (hbits : bits.length = N) :
    ((Tape.move Dir.left)^[N - 1]
      ((tapeOnBit bits (N - 1)).move Dir.left)).head = none := by
  have hiter : (Tape.move Dir.left)^[N]
      (tapeOnBit bits (N - 1)) =
      (Tape.move Dir.left)^[N - 1]
        ((tapeOnBit bits (N - 1)).move Dir.left) := by
    rw [show N = N - 1 + 1 by omega]
    exact Function.iterate_add_apply _ _ _ _
  rw [← hiter]
  have hh := tape_move_left_head' (encPref bits (N - 1))
    (ListBlank.mk [some (bits.getD (N - 1) false)]) (N - 1)
  have hh' : ((Tape.move Dir.left)^[N]
      (tapeOnBit bits (N - 1))).head =
      (encPref bits (N - 1)).getD (N - 1) none := by
    rw [show N = N - 1 + 1 by omega]
    exact hh
  rw [hh']
  have hL : (encPref bits (N - 1)).length = N - 1 := by
    simp [encPref, List.length_map, List.length_take]
    omega
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega :
    (encPref bits (N - 1)).length ≤ N - 1)]
  simp

lemma tapeOnBit_shiftHome_tape (bits : List Bool) (N : ℕ)
    (hN : 0 < N) (hbits : bits.length = N) :
    ((Tape.move Dir.left)^[N - 1]
      ((tapeOnBit bits (N - 1)).move Dir.left)).move Dir.right =
      Tape.mk₁ (tapeSymbols bits) := by
  let L := encPref bits (N - 1)
  have hLlen : L.length = N - 1 := by
    simp [L, encPref, List.length_map, List.length_take]
    omega
  have hiter : (Tape.move Dir.left)^[N]
      (tapeOnBit bits (N - 1)) =
      (Tape.move Dir.left)^[N - 1]
        ((tapeOnBit bits (N - 1)).move Dir.left) := by
    rw [show N = N - 1 + 1 by omega]
    exact Function.iterate_add_apply _ _ _ _
  have hpast := tape_move_left_past (encPref bits (N - 1))
    [some (bits.getD (N - 1) false)]
  rw [hLlen, show N - 1 + 1 = N by omega] at hpast
  rw [← hiter]
  change Tape.move Dir.right ((Tape.move Dir.left)^[N]
    (Tape.mk' (ListBlank.mk (encPref bits (N - 1)))
      (ListBlank.mk [some (bits.getD (N - 1) false)]))) = _
  rw [hpast]
  have hLrev : (encPref bits (N - 1)).reverse =
      (List.take (N - 1) bits).map some := by
    simp [encPref]
  rw [hLrev, List.map_take]
  change Tape.move Dir.right
      (Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (none :: List.take (N - 1) (List.map some bits) ++
          [some (bits.getD (N - 1) false)]))) =
    Tape.mk' (ListBlank.mk []) (ListBlank.mk (List.map some bits))
  have hi : N - 1 < bits.length := by omega
  have ht := List.take_succ_eq_append_getElem hi
  have ht' : bits = bits.take (N - 1) ++ [bits[N - 1]] := by
    calc
      bits = bits.take bits.length := (List.take_length).symm
      _ = bits.take N := by rw [hbits]
      _ = bits.take (N - 1) ++ [bits[N - 1]] := by
        simpa only [show N - 1 + 1 = N by omega] using ht
  have hm : List.map some bits =
      List.map some (bits.take (N - 1) ++ [bits[N - 1]]) :=
    congrArg (List.map some) ht'
  rw [List.map_append, List.map_take] at hm
  have hA : List.take (N - 1) (List.map some bits) ++
      [some (bits[N - 1])] = List.map some bits := by
    simpa using hm.symm
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  change Tape.mk' (ListBlank.mk [none])
      (ListBlank.mk (List.take (N - 1) (List.map some bits) ++
        [some (bits[N - 1])])) =
    Tape.mk' (ListBlank.mk []) (ListBlank.mk (List.map some bits))
  rw [hA]
  apply congrArg (fun L => Tape.mk' L (ListBlank.mk (List.map some bits)))
  apply Quotient.sound'
  exact Or.inr ⟨1, by simp [default]⟩

lemma enc_empty_time_bound (N : ℕ) (hN : 0 < N) :
    3 * N ≤ (recodeTime (X + 1) N).eval 0 := by
  simp [recodeTime, recodeTimeG_eval, eval_add, eval_X]
  have hN1 : 1 ≤ N := by omega
  have h₁ : 2 * N ≤ (2 * N + 4) * N :=
    Nat.mul_le_mul_right _ (by omega)
  have h₂ : (2 * N + 4) * N ≤ N * (2 * N + 4) * N := by
    have h := Nat.mul_le_mul_left ((2 * N + 4) * N) hN1
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  omega

lemma enc_nonempty_time_bound (N m : ℕ) (hN : 0 < N) :
    m * (3 * N + 2 * m * N + 2 * m + 4) + 1 ≤
      (recodeTime (X + 1) N).eval m := by
  simp [recodeTime, recodeTimeG_eval, eval_add, eval_X]
  let K := 2 * (m + (m + 1) * N) + 4
  change m * (3 * N + 2 * m * N + 2 * m + 4) + 1 ≤
    (m + 1) * N * K * N + m * N + N
  have hN1 : 1 ≤ N := by omega
  have hsmall : m ≤ (m + 1) * N := by
    have h₁ : m ≤ m + 1 := by omega
    have h₂ := Nat.mul_le_mul_left (m + 1) hN1
    omega
  have hlarge : (m + 1) * N ≤ (m + 1) * N * N := by
    have h := Nat.mul_le_mul_left ((m + 1) * N) hN1
    simpa [Nat.mul_assoc] using h
  have hfactor : m ≤ (m + 1) * N * N := hsmall.trans hlarge
  have hprod : m * K ≤ (m + 1) * N * K * N := by
    have hmul := Nat.mul_le_mul_right K hfactor
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hgap : m * (3 * N + 2 * m * N + 2 * m + 4) =
      m * K + m * N := by
    dsimp [K]
    ring
  calc
    m * (3 * N + 2 * m * N + 2 * m + 4) + 1 = m * K + m * N + 1 := by
      rw [hgap]
    _ ≤ m * K + m * N + N := by omega
    _ ≤ (m + 1) * N * K * N + m * N + N := by omega

lemma enc_nonempty_run (l : List Bool) :
    ∃ q t,
      t ≤ (recodeTime (X + 1) (encN tm)).eval l.length ∧
      StepsTo (TM0.step (encMachine tm inp))
        (TM0.init (tapeSymbols l)) ⟨q, Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))⟩ t ∧
      TM0.step (encMachine tm inp) ⟨q, Tape.mk₁ (tapeSymbols (encodePackedInput tm inp l))⟩ = none := by
  cases l with
  | nil =>
      let T0 := Tape.mk₁ (tapeSymbols ([] : List Bool))
      let bits := encBottomBlank tm
      have hN := encN_pos tm
      have hhead : T0.head = none := by
        simp [T0, tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', default]
      have hfirst := enc_toEnd_none tm inp T0 hhead hN
      have hwrite : T0.write (some (bits.getD 0 false)) = tapeOnBit bits 0 := by
        simp [T0, bits, tapeSymbols, tapeOnBit, encPref, Tape.mk₁, Tape.mk₂,
          Tape.mk', Tape.write, ListBlank.head_mk, ListBlank.tail_mk]
      rw [hwrite] at hfirst
      have hblank : StepsTo (TM0.step (encMachine tm inp))
          ⟨.writeBlank ⟨0, hN⟩, tapeOnBit bits 0⟩
          ⟨.shiftHome, (tapeOnBit bits (encN tm - 1)).move Dir.left⟩
          (2 * (encN tm - 1 - 0) + 1) := by
        simpa [bits] using enc_writeBlank_on_bit tm inp 0 hN
      have hheads := enc_shiftHome_walk tm inp
          ((tapeOnBit bits (encN tm - 1)).move Dir.left) (encN tm - 1)
        (fun i hi => tapeOnBit_shiftHome_heads bits (encN tm) i
          (by simp [bits, encBottomBlank_length]) hi)
      have hnone := enc_shiftHome_none tm inp
          ((Tape.move Dir.left)^[encN tm - 1]
            ((tapeOnBit bits (encN tm - 1)).move Dir.left))
          (tapeOnBit_shiftHome_none bits (encN tm) hN
            (by simp [bits, encBottomBlank_length]))
      have hfirst' := stepsTo_cons _ hfirst (stepsTo_zero _ _)
      have hpre := stepsTo_trans _ hfirst' hblank
      have hrun := stepsTo_trans _ hpre hheads
      have hrun' := stepsTo_trans _ hrun
        (stepsTo_cons _ hnone (stepsTo_zero _ _))
      have htape := tapeOnBit_shiftHome_tape bits (encN tm) hN
        (by simp [bits, encBottomBlank_length])
      rw [htape] at hrun'
      refine ⟨.done, 3 * encN tm, ?_, ?_, enc_done_halt tm inp _⟩
      · simpa using enc_empty_time_bound (encN tm) hN
      · have htime : 1 + (encN tm - 1 + (2 * (encN tm - 1) + 1 + 1)) =
            3 * encN tm := by omega
        simpa [T0, TM0.init, default, encodePackedInput_nil, bits, htime] using hrun'
  | cons b rest =>
      have hfirst : TM0.step (encMachine tm inp)
          ⟨.toEnd, Tape.mk₁ (tapeSymbols (b :: rest))⟩ =
          some ⟨.checkLast false b, encCheck tm inp [] rest⟩ := by
        simpa [encSource, encCheck, encLeft, encOut, tapeSymbols,
          Tape.mk₁, Tape.mk₂, Tape.mk'] using
          (enc_to_check tm inp [] rest b)
      obtain ⟨q, t, ht, hsteps, hhalt⟩ := enc_check_run tm inp [] b rest
      have hfirst' := stepsTo_cons _ hfirst (stepsTo_zero _ _)
      have htotal := stepsTo_trans _ hfirst' hsteps
      have ht' : t ≤ (rest.length + 1) *
          (3 * encN tm + 2 * (rest.length + 1) * encN tm +
            2 * (rest.length + 1) + 4) := by
        simpa [List.length_nil, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
      have hbound := enc_nonempty_time_bound (encN tm) (rest.length + 1)
        (encN_pos tm)
      have htime : t + 1 ≤
          (recodeTime (X + 1) (encN tm)).eval (rest.length + 1) := by
        omega
      refine ⟨q, t + 1, ?_, ?_, ?_⟩
      · simpa using htime
      · simpa [TM0.init, default, List.length_cons, List.append_assoc] using htotal
      · simpa [List.append_assoc] using hhalt

noncomputable def encComputable {α : Type} (tm : FinTM2)
    (inp : tm.Γ tm.k₀ ≃ Bool) (ea : α → List Bool) :
    TM0ComputableInPolyTime ea (fun l : List Bool => l)
      (fun a => encodePackedInput tm inp (ea a)) where
  toTM0ComputableAux := encAux tm inp
  time := recodeTime (X + 1) (encN tm)
  outputsFun a := by
    obtain ⟨q, t, ht, hsteps, hhalt⟩ := enc_nonempty_run tm inp (ea a)
    exact ⟨q, t, ht, hsteps, hhalt⟩

end NPComplete.CookLevin

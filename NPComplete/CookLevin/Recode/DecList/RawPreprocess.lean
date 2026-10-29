module

public import NPComplete.CookLevin.Recode.DecList.BlockEncoding

/-!
# Raw input preprocessing

An arbitrary raw bit list need not end on a symbol boundary, so the machine first
trims incomplete trailing blocks and aligns its tape for decoding. These local
transition lemmas isolate that normalization from the later block simulation.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

lemma dec_list_raw_write_blank (L : List (Option Bool)) :
    (decListForwardTape [] L).write none = decListForwardTape [] L := by
  simp only [decListForwardTape, tapeSymbols, Tape.write_mk']
  apply congrArg (fun R => Tape.mk' (ListBlank.mk L) R)
  apply Quotient.sound'
  exact Or.inr ⟨1, rfl⟩

lemma decListRawMachine_seekFirst_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) {b : Bool} (hhead : T.head = some b) :
    TM0.step (decListRawMachine tm out)
        ⟨.seekFirst, T⟩ =
      some ⟨.scanRight (decListFinNext (decN_pos tm) ⟨0, decN_pos tm⟩),
        T.move Dir.right⟩ := by
  simp [TM0.step, decListRawMachine, hhead, decListFinNext]

lemma decListRawMachine_scanRight_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (i : Fin (decListN tm)) (T : Tape (Option Bool)) {b : Bool}
    (hhead : T.head = some b) :
    TM0.step (decListRawMachine tm out)
        ⟨.scanRight i, T⟩ =
      some ⟨.scanRight (decListFinNext (decN_pos tm) i),
        T.move Dir.right⟩ := by
  simp [TM0.step, decListRawMachine, hhead, decListFinNext]

lemma decListRawMachine_scanRight_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (i : Fin (decListN tm)) (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (decListRawMachine tm out)
        ⟨.scanRight i, T⟩ =
      some ⟨.trimRight i, T.write none⟩ := by
  simp [TM0.step, decListRawMachine, hhead]

lemma decListRawMachine_trimRight_zero (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) :
    TM0.step (decListRawMachine tm out)
        ⟨.trimRight ⟨0, decN_pos tm⟩, T⟩ =
      some ⟨.rewindStart, T.write none⟩ := by
  simp [TM0.step, decListRawMachine]

lemma decListRawMachine_trimRight_pos (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (i : Fin (decListN tm)) (T : Tape (Option Bool)) (hi : 0 < i.val) :
    TM0.step (decListRawMachine tm out)
        ⟨.trimRight i, T⟩ =
      some ⟨.trimErase i, T.move Dir.left⟩ := by
  have hne : ¬ i.val = 0 := by omega
  simp [TM0.step, decListRawMachine, hne]

lemma decListRawMachine_trimErase_one (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (i : Fin (decListN tm)) (hi : i.val = 1) (T : Tape (Option Bool)) :
    TM0.step (decListRawMachine tm out)
        ⟨.trimErase i, T⟩ =
      some ⟨.rewindStart, T.write none⟩ := by
  have hzero : ¬ i.val = 0 := by omega
  simp [TM0.step, decListRawMachine, hi]

lemma decListRawMachine_trimErase_succ (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (i : Fin (decListN tm)) (hi : 1 < i.val) (T : Tape (Option Bool)) :
    TM0.step (decListRawMachine tm out)
        ⟨.trimErase i, T⟩ =
      some ⟨.trimRight (decListFinPred i (by omega)), T.write none⟩ := by
  have hzero : ¬ i.val = 0 := by omega
  have hone : ¬ i.val = 1 := by omega
  simp [TM0.step, decListRawMachine, hzero, hone]

lemma decListRawMachine_scanRight (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (raw : List Bool) (i : Fin (decListN tm)) (L : List (Option Bool)) :
    StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.scanRight i, decListForwardTape raw L⟩
      ⟨.trimRight
          (decListRawCount (decN_pos tm) raw i),
        decListForwardTape [] (raw.reverse.map some ++ L)⟩
      (raw.length + 1) := by
  induction raw generalizing i L with
  | nil =>
      have hs := decListRawMachine_scanRight_none tm out i
        (decListForwardTape [] L) (by rfl)
      have hblank := dec_list_raw_write_blank L
      rw [hblank] at hs
      simpa [decListRawCount] using
        (stepsTo_cons _ hs (stepsTo_zero _ _))
  | cons b raw ih =>
      have hs := decListRawMachine_scanRight_some tm out i
        (decListForwardTape (b :: raw) L) (b := b) (by rfl)
      rw [decListForwardTape_move_right] at hs
      have hi := ih (decListFinNext (decN_pos tm) i) (some b :: L)
      have hchain := stepsTo_cons _ hs hi
      simpa [decListRawCount, List.reverse_cons, List.map_append,
        List.append_assoc, Nat.add_assoc] using hchain

lemma decListRawMachine_startup (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (raw : List Bool) :
    StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.seekFirst, Tape.mk₁ (tapeSymbols (b :: raw))⟩
      ⟨.scanRight (decListFinNext (decN_pos tm) ⟨0, decN_pos tm⟩),
        decListForwardTape raw [some b]⟩ 1 := by
  let T : Tape (Option Bool) := Tape.mk₁ (tapeSymbols (b :: raw))
  have hhead : T.head = some b := by
    simp [T, Tape.mk₁, Tape.mk₂, tapeSymbols]
  have hs := decListRawMachine_seekFirst_some tm out T (b := b) hhead
  have hinit : T = decListForwardTape (b :: raw) [] := by
    simp [T, Tape.mk₁, Tape.mk₂, decListForwardTape]
  rw [hinit, decListForwardTape_move_right] at hs
  exact stepsTo_cons _ hs (stepsTo_zero _ _)

lemma decListRawCount_initial (tm : FinTM2) (b : Bool) (raw : List Bool) :
    decListRawCount (decN_pos tm) raw
        (decListFinNext (decN_pos tm) ⟨0, decN_pos tm⟩) =
      ⟨(b :: raw).length % decListN tm,
        Nat.mod_lt _ (decN_pos tm)⟩ := by
  apply Fin.ext
  rw [decListRawCount_val]
  rw [decListFinNext_val]
  simp [List.length_cons, Nat.add_mod, Nat.add_comm]

def decListRawTrimTape (left : List (Option Bool)) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk left) (ListBlank.mk [])

lemma decListRawTrimTape_trim_move_write (x : Option Bool)
    (left : List (Option Bool)) :
    ((decListRawTrimTape (x :: left)).move Dir.left).write none =
      Tape.mk' (ListBlank.mk left) (ListBlank.mk [none]) := by
  simp [decListRawTrimTape, Tape.move_left_mk', Tape.write_mk',
    ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListRawTrimTape_trim_blank_right (left : List (Option Bool)) :
    decListRawTrimTape left =
      Tape.mk' (ListBlank.mk left) (ListBlank.mk [none]) := by
  apply congrArg (fun R => Tape.mk' (ListBlank.mk left) R)
  apply Quotient.sound'
  exact Or.inl ⟨1, rfl⟩

lemma decListRawMachine_trim_macro_aux (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (j : ℕ) (hj : j < decListN tm) (left : List (Option Bool))
    (hleft : j ≤ left.length) :
    ∃ k : ℕ, k ≤ 2 * j + 1 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.trimRight ⟨j, hj⟩, decListRawTrimTape left⟩
        ⟨.rewindStart,
          Tape.mk' (ListBlank.mk (left.drop j))
            (ListBlank.mk [none])⟩ k := by
  induction j generalizing left with
  | zero =>
      have hs := decListRawMachine_trimRight_zero tm out
        (decListRawTrimTape left)
      refine ⟨1, by simp, ?_⟩
      have hsteps := stepsTo_cons _ hs (stepsTo_zero _ _)
      simpa [decListRawTrimTape, Tape.write_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk] using hsteps
  | succ j ih =>
      have hpos : 0 < left.length := by omega
      obtain ⟨x, tail, hleftEq⟩ :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hpos)
      subst left
      let i : Fin (decListN tm) := ⟨j + 1, hj⟩
      have htr := decListRawMachine_trimRight_pos tm out i
        (decListRawTrimTape (x :: tail)) (by simp [i])
      have hmove := decListRawTrimTape_trim_move_write x tail
      by_cases hzero : j = 0
      · have hte := decListRawMachine_trimErase_one tm out i (by simp [i, hzero])
          ((decListRawTrimTape (x :: tail)).move Dir.left)
        rw [hmove] at hte
        refine ⟨2, by simp [hzero], ?_⟩
        have hchain := stepsTo_cons _ htr
          (stepsTo_cons _ hte (stepsTo_zero _ _))
        simpa [i, hzero, decListRawTrimTape] using hchain
      · have hsucc : 1 < i.val := by simp [i]; omega
        have hte := decListRawMachine_trimErase_succ tm out i hsucc
          ((decListRawTrimTape (x :: tail)).move Dir.left)
        rw [hmove] at hte
        have hpred : decListFinPred i (by omega) = ⟨j, by omega⟩ := by
          apply Fin.ext
          simp [i, decListFinPred]
        rw [hpred] at hte
        have htail : j ≤ tail.length := by
          simpa using hleft
        have hih := ih (left := tail) (hj := by omega) (hleft := htail)
        have hblank := decListRawTrimTape_trim_blank_right tail
        rw [hblank] at hih
        obtain ⟨k, hk, hik⟩ := hih
        have hchain := stepsTo_cons _ htr
          (stepsTo_cons _ hte hik)
        refine ⟨k + 2, ?_, ?_⟩
        · omega
        · simpa [i, decListRawTrimTape, hzero] using hchain

lemma decListRawMachine_rewindLeft_some (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (T : Tape (Option Bool))
    {b : Bool} (hhead : T.head = some b) :
    TM0.step (decListRawMachine tm out) ⟨.rewindLeft, T⟩ =
      some ⟨.rewindLeft, T.move Dir.left⟩ := by
  simp [TM0.step, decListRawMachine, hhead]

lemma decListRawMachine_rewindLeft_none (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (decListRawMachine tm out) ⟨.rewindLeft, T⟩ =
      some ⟨.run (.seekEnd false), T.move Dir.right⟩ := by
  simp [TM0.step, decListRawMachine, hhead]

lemma dec_list_raw_blank_move_right :
    (Tape.mk' (ListBlank.mk []) (ListBlank.mk [none]) : Tape (Option Bool)).move Dir.right =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk [none]) := by
  rw [Tape.move_right_mk']
  apply congrArg₂ Tape.mk'
  · apply Quotient.sound'
    exact Or.inr ⟨1, rfl⟩
  · apply Quotient.sound'
    exact Or.inl ⟨1, rfl⟩

lemma dec_list_raw_blank_left (R : List (Option Bool)) :
    Tape.mk' (ListBlank.mk [none]) (ListBlank.mk R) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk R) := by
  apply congrArg (fun L => Tape.mk' L (ListBlank.mk R))
  apply Quotient.sound'
  exact Or.inr ⟨1, rfl⟩

lemma dec_list_raw_blank_right :
    (Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none]) :
      Tape (Option Bool)) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk [none]) := by
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  apply Quotient.sound'
  exact Or.inr ⟨1, rfl⟩

lemma decListRawMachine_rewind_aux (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (left R : List Bool)
    (hcond : left = [] ∨ R ≠ []) :
    ∃ k : ℕ, k ≤ 2 * left.length + R.length + 2 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.rewindLeft,
          Tape.mk' (ListBlank.mk (left.map some))
            (ListBlank.mk (R.map some ++ [none]))⟩
        ⟨.run (.seekEnd false),
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk ((left.reverse ++ R).map some ++ [none]))⟩ k := by
  induction left generalizing R with
  | nil =>
      cases R with
      | nil =>
          have hs := decListRawMachine_rewindLeft_none tm out
            (Tape.mk' (ListBlank.mk []) (ListBlank.mk [none])) (by rfl)
          refine ⟨1, by simp, ?_⟩
          rw [dec_list_raw_blank_move_right] at hs
          simpa [Tape.mk', Tape.move_right_mk', ListBlank.head_mk,
            ListBlank.tail_mk, ListBlank.cons_mk] using
            (stepsTo_cons _ hs (stepsTo_zero _ _))
      | cons b R =>
          let T : Tape (Option Bool) :=
            Tape.mk' (ListBlank.mk [])
              (ListBlank.mk (some b :: R.map some ++ [none]))
          have hs := decListRawMachine_rewindLeft_some tm out T
            (by rfl)
          let T₁ := T.move Dir.left
          have hn := decListRawMachine_rewindLeft_none tm out T₁
            (by simp [T₁, T, Tape.move_left_mk', ListBlank.head_mk,
              ListBlank.tail_mk, ListBlank.cons_mk, default])
          have hchain := stepsTo_cons _ hs
            (stepsTo_cons _ hn (stepsTo_zero _ _))
          refine ⟨2, by simp, ?_⟩
          simpa [T, T₁, Tape.move_left_mk', Tape.move_right_mk',
            ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk,
            List.map_append, List.append_assoc, default,
            dec_list_raw_blank_left] using hchain
  | cons x left ih =>
      have hR : R ≠ [] := by
        intro hR
        rcases hcond with hleft | hRcond
        · simp at hleft
        · exact hRcond hR
      obtain ⟨y, rest, hR⟩ := List.exists_cons_of_ne_nil hR
      subst R
      have hs := decListRawMachine_rewindLeft_some tm out
        (Tape.mk' (ListBlank.mk ((x :: left).map some))
          (ListBlank.mk ((y :: rest).map some ++ [none])))
        (by rfl)
      obtain ⟨k, hk, hih⟩ := ih (R := x :: y :: rest)
        (Or.inr (by simp))
      have hchain := stepsTo_cons _ hs hih
      refine ⟨k + 1, ?_, ?_⟩
      · have hk' : k ≤ 2 * left.length + (x :: y :: rest).length + 2 := by
          simpa using hk
        simp only [List.length_cons] at hk' ⊢
        omega
      · simpa [Tape.move_left_mk', ListBlank.head_mk,
          ListBlank.tail_mk, ListBlank.cons_mk, List.map_append,
          List.reverse_cons, List.append_assoc] using hchain

lemma decListRawMachine_rewind_start (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (left : List Bool) :
    ∃ k : ℕ, k ≤ 2 * left.length + 4 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.rewindStart,
          Tape.mk' (ListBlank.mk (left.map some))
            (ListBlank.mk [none])⟩
        ⟨.run (.seekEnd false),
          Tape.mk' (ListBlank.mk [])
            (ListBlank.mk (left.reverse.map some ++ [none]))⟩ k := by
  cases left with
  | nil =>
      have hs :
          TM0.step (decListRawMachine tm out)
              ⟨.rewindStart,
                Tape.mk' (ListBlank.mk []) (ListBlank.mk [none])⟩ =
            some ⟨.rewindLeft,
              Tape.mk' (ListBlank.mk []) (ListBlank.mk [none])⟩ := by
        simp [TM0.step, decListRawMachine, Tape.move_left_mk',
          ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk,
          dec_list_raw_blank_right, default]
      obtain ⟨k, hk, haux⟩ := decListRawMachine_rewind_aux tm out [] [] (Or.inl rfl)
      have hchain := stepsTo_cons _ hs haux
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hk ⊢
        omega
      · simpa [Tape.move_left_mk', ListBlank.head_mk,
          ListBlank.tail_mk, ListBlank.cons_mk, List.reverse_nil,
          List.map_nil, List.append_nil, default] using hchain
  | cons x left =>
      have hs :
          TM0.step (decListRawMachine tm out)
              ⟨.rewindStart,
                Tape.mk' (ListBlank.mk ((x :: left).map some))
                  (ListBlank.mk [none])⟩ =
            some ⟨.rewindLeft,
              (Tape.mk' (ListBlank.mk ((x :: left).map some))
                (ListBlank.mk [none])).move Dir.left⟩ := by
        simp [TM0.step, decListRawMachine]
      obtain ⟨k, hk, haux⟩ := decListRawMachine_rewind_aux tm out left [x]
        (Or.inr (by simp))
      have hchain := stepsTo_cons _ hs haux
      refine ⟨k + 1, ?_, ?_⟩
      · have hk' : k ≤ 2 * left.length + 3 := by
          simpa using hk
        simp only [List.length_cons] at hk' ⊢
        omega
      · simpa [Tape.move_left_mk', ListBlank.head_mk,
          ListBlank.tail_mk, ListBlank.cons_mk, List.map_append,
          List.reverse_cons, List.append_assoc, default] using hchain

lemma dec_list_raw_canonical_tape (left : List Bool) :
      (Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (left.reverse.map some ++ [none])) : Tape (Option Bool)) =
      Tape.mk₁ (tapeSymbols left.reverse) := by
  simp only [Tape.mk₁, Tape.mk₂, tapeSymbols]
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  apply Quotient.sound'
  refine Or.inr ⟨1, ?_⟩
  simp only [List.replicate_succ, List.replicate_zero]
  exact congrArg (fun z => List.map some left.reverse ++ [z]) rfl

lemma decListRawMachine_rewind_start_mk₁ (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (left : List Bool) :
    ∃ k : ℕ, k ≤ 2 * left.length + 4 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.rewindStart,
          Tape.mk' (ListBlank.mk (left.map some))
            (ListBlank.mk [none])⟩
        ⟨.run (.seekEnd false), Tape.mk₁ (tapeSymbols left.reverse)⟩ k := by
  obtain ⟨k, hk, hrun⟩ := decListRawMachine_rewind_start tm out left
  refine ⟨k, hk, ?_⟩
  rw [dec_list_raw_canonical_tape] at hrun
  exact hrun

lemma decListRawMachine_preprocess_nonempty (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (raw : List Bool) :
    ∃ k : ℕ, k ≤ 3 * (b :: raw).length + 4 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.seekFirst, Tape.mk₁ (tapeSymbols (b :: raw))⟩
        ⟨.rewindStart,
          Tape.mk' (ListBlank.mk
            (((b :: raw).reverse.map some).drop
              ((b :: raw).length % decListN tm)))
            (ListBlank.mk [none])⟩ k := by
  let hn : 0 < decListN tm := decN_pos tm
  let rem : ℕ := (b :: raw).length % decListN tm
  let left : List (Option Bool) := (b :: raw).reverse.map some
  have hrem : rem < decListN tm := by
    exact Nat.mod_lt _ hn
  have hleft : rem ≤ left.length := by
    dsimp [rem, left]
    simp
    exact Nat.mod_le _ _
  have hstart := decListRawMachine_startup tm out b raw
  have hscan := decListRawMachine_scanRight tm out raw
    (decListFinNext hn ⟨0, hn⟩) [some b]
  have hcount := decListRawCount_initial tm b raw
  rw [hcount] at hscan
  have hscan' :
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.scanRight (decListFinNext hn ⟨0, hn⟩),
          decListForwardTape raw [some b]⟩
        ⟨.trimRight ⟨rem, hrem⟩, decListRawTrimTape left⟩
        (raw.length + 1) := by
    simpa [rem, left, decListRawTrimTape, decListForwardTape, tapeSymbols,
      List.reverse_cons, List.map_append, List.append_assoc] using hscan
  obtain ⟨kt, hkt, htrim⟩ :=
    decListRawMachine_trim_macro_aux tm out rem hrem left hleft
  have hchain := stepsTo_trans _ hstart
    (stepsTo_trans _ hscan' htrim)
  refine ⟨kt + raw.length + 2, ?_, ?_⟩
  · dsimp [rem] at hkt
    have hmod : (b :: raw).length % decListN tm ≤ (b :: raw).length :=
      Nat.mod_le _ _
    have hlen : raw.length + 1 = (b :: raw).length := by simp
    have hmod' : (raw.length + 1) % decListN tm ≤ raw.length + 1 :=
      Nat.mod_le _ _
    omega
  · simpa [rem, left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchain

lemma dec_list_raw_preprocess_canonical_nonempty (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (raw : List Bool) :
    let rem := (b :: raw).length % decListN tm
    let left := (b :: raw).reverse.drop rem
    ∃ k : ℕ, k ≤ 3 * (b :: raw).length + 4 + (2 * left.length + 4) ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.seekFirst, Tape.mk₁ (tapeSymbols (b :: raw))⟩
        ⟨.run (.seekEnd false), Tape.mk₁ (tapeSymbols left.reverse)⟩ k := by
  dsimp
  let rem : ℕ := (b :: raw).length % decListN tm
  let left : List Bool := (b :: raw).reverse.drop rem
  obtain ⟨k₀, hk₀, hpre⟩ := decListRawMachine_preprocess_nonempty tm out b raw
  have hpre' :
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.seekFirst, Tape.mk₁ (tapeSymbols (b :: raw))⟩
        ⟨.rewindStart,
          Tape.mk' (ListBlank.mk (left.map some))
            (ListBlank.mk [none])⟩ k₀ := by
    simpa [rem, left, List.map_drop] using hpre
  obtain ⟨k₁, hk₁, hrew⟩ := decListRawMachine_rewind_start_mk₁ tm out left
  refine ⟨k₁ + k₀, ?_, stepsTo_trans _ hpre' hrew⟩
  have hlen : left.length =
      (List.drop ((raw.length + 1) % decListN tm)
        (b :: raw).reverse).length := by
    simp [left, rem]
  rw [← hlen]
  have hsum := Nat.add_le_add hk₀ hk₁
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    List.length_cons] using hsum

end NPComplete.CookLevin

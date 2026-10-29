module

public import NPComplete.CookLevin.Recode.DecList.Run

/-!
# List Decoder Tape Steps

The decoder's correctness depends on exact tape movement through the packed output and its separator,
not just on the final decoded list. This module isolates the scan-to-output step proofs and their costs
from the transition table so larger execution arguments can compose precise `StepsTo` segments.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

noncomputable def decListSepStart (bits : List Bool)
    (L R : List (Option Bool)) : Tape (Option Bool) :=
  match bits with
  | [] => Tape.mk' (ListBlank.mk L.tail)
      (ListBlank.mk (L.headI :: R))
  | b :: rest => Tape.mk' (ListBlank.mk (rest.map some ++ L))
      (ListBlank.mk (some b :: R))

lemma decListReadTape_move_left_sep (n : ℕ) (bits : List Bool)
    (L R : List (Option Bool)) :
    (decListReadTape n [] (bits.map some ++ L) R).move Dir.left =
      decListSepStart bits L (List.replicate n none ++ R) := by
  cases bits with
  | nil =>
      simp [decListReadTape, decListSepStart, Tape.move_left_mk',
        ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
  | cons b bits =>
      simp [decListReadTape, decListSepStart, Tape.move_left_mk',
        ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListSepStart_cons_move_left (b : Bool) (bits : List Bool)
    (L R : List (Option Bool)) :
    (decListSepStart (b :: bits) L R).move Dir.left =
      decListSepStart bits L (some b :: R) := by
  cases bits with
  | nil =>
      simp [decListSepStart, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk]
  | cons c bits =>
      simp [decListSepStart, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListMachine_seekSep_scan (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (bits : List Bool) (L R : List (Option Bool))
    (hL : L.headI = none) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekSep b, decListSepStart bits L R⟩
      ⟨.seekOut b,
        (decListSepStart [] L (bits.reverse.map some ++ R)).move Dir.left⟩
      (bits.length + 1) := by
  induction bits generalizing L R with
  | nil =>
      have hs := decListMachine_seekSep_none tm out b (decListSepStart [] L R) (by
        simp [decListSepStart, hL])
      simpa [decListSepStart] using
        (stepsTo_cons _ hs (stepsTo_zero _ _))
  | cons c bits ih =>
      have hs := decListMachine_seekSep_some tm out b
        (decListSepStart (c :: bits) L R) (x := c) (by
          simp [decListSepStart])
      have hi := ih L (some c :: R) (by
        simp [hL])
      have hmove := decListSepStart_cons_move_left c bits L R
      have hi' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.seekSep b,
            (decListSepStart (c :: bits) L R).move Dir.left⟩
          ⟨.seekOut b,
            (decListSepStart [] L
              (bits.reverse.map some ++ some c :: R)).move Dir.left⟩
          (bits.length + 1) := by
        simpa [hmove] using hi
      have hi'' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.seekSep b,
            (decListSepStart (c :: bits) L R).move Dir.left⟩
          ⟨.seekOut b,
            (decListSepStart [] L
              ((c :: bits).reverse.map some ++ R)).move Dir.left⟩
          (c :: bits).length := by
        simpa [decListSepStart, List.reverse_cons, List.map_append,
          List.append_assoc] using hi'
      exact stepsTo_cons _ hs hi''

noncomputable def decListOutStart (outs : List Bool)
    (R : List (Option Bool)) : Tape (Option Bool) :=
  match outs with
  | [] => Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: R))
  | c :: rest => Tape.mk' (ListBlank.mk (rest.map some))
      (ListBlank.mk (some c :: R))

lemma dec_list_sep_out_move_left (c : Bool) (outs : List Bool)
    (R : List (Option Bool)) :
    (decListSepStart [] (none :: (c :: outs).map some) R).move Dir.left =
      decListOutStart (c :: outs) (none :: R) := by
  simp [decListSepStart, decListOutStart, Tape.move_left_mk',
    ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListOutStart_move_left (c : Bool) (outs : List Bool)
    (R : List (Option Bool)) :
    (decListOutStart (c :: outs) R).move Dir.left =
      decListOutStart outs (some c :: R) := by
  cases outs with
  | nil =>
      simp [decListOutStart, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, default]

  | cons d outs =>
      simp [decListOutStart, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListMachine_walkOutLeft_scan (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (left : List Bool) (x : Bool) (right : List Bool) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.walkOutLeft,
        Tape.mk' (ListBlank.mk (left.map some))
          (ListBlank.mk (some x :: right.map some ++ [none]))⟩
      ⟨.done,
        Tape.mk₁ (tapeSymbols (left.reverse ++ [x] ++ right))⟩
      (left.length + 2) := by
  induction left generalizing x right with
  | nil =>
      let T : Tape (Option Bool) :=
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (some x :: right.map some ++ [none]))
      have hs := decListMachine_walkOutLeft_some tm out T (x := x) (by
        simp [T])
      let T₁ := T.move Dir.left
      have hn := decListMachine_walkOutLeft_none tm out T₁ (by
        simp [T₁, T, default])
      have hchain := stepsTo_cons _ hs
        (stepsTo_cons _ hn (stepsTo_zero _ _))
      have hleft : ListBlank.mk ([none] : List (Option Bool)) =
          ListBlank.mk [] := by
        apply Quotient.sound'
        exact Or.inr ⟨1, rfl⟩
      have hright :
          ListBlank.mk (some x :: right.map some ++ [none]) =
            ListBlank.mk (some x :: right.map some) := by
        apply Quotient.sound'
        exact Or.inr ⟨1, rfl⟩
      convert hchain using 1
      · simp [T]
      · simp [T₁, T, Tape.move_left_mk', Tape.move_right_mk',
          Tape.mk₁, Tape.mk₂, tapeSymbols, ListBlank.head_mk,
          ListBlank.tail_mk, ListBlank.cons_mk,
          default, hleft]
        rw [← hright]
        rfl
  | cons a left ih =>
      let T : Tape (Option Bool) :=
        Tape.mk' (ListBlank.mk (some a :: left.map some))
          (ListBlank.mk (some x :: right.map some ++ [none]))
      have hs := decListMachine_walkOutLeft_some tm out T (x := x) (by
        simp [T])
      have hi := ih a (x :: right)
      have hchain := stepsTo_cons _ hs hi
      simpa [T, Tape.move_left_mk', ListBlank.head_mk,
        ListBlank.tail_mk, ListBlank.cons_mk, List.reverse_cons,
        List.map_append, List.append_assoc, Nat.add_assoc] using hchain

lemma decListMachine_seekOut_scan (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (outs : List Bool) (R : List (Option Bool)) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekOut b, decListOutStart outs R⟩
      ⟨.checkOutput,
        (decListOutStart [] (outs.reverse.map some ++ R)).write
          (some b)⟩
      (outs.length + 1) := by
  induction outs generalizing R with
  | nil =>
      have hs := decListMachine_seekOut_none tm out b
        (decListOutStart [] R) (by simp [decListOutStart])
      simpa [decListOutStart] using
        (stepsTo_cons _ hs (stepsTo_zero _ _))
  | cons c outs ih =>
      have hs := decListMachine_seekOut_some tm out b
        (decListOutStart (c :: outs) R) (x := c) (by
          simp [decListOutStart])
      have hi := ih (some c :: R)
      have hmove := decListOutStart_move_left c outs R
      have hi' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.seekOut b, (decListOutStart (c :: outs) R).move Dir.left⟩
          ⟨.checkOutput,
            (decListOutStart []
              (outs.reverse.map some ++ some c :: R)).write
                (some b)⟩
          (outs.length + 1) := by
        simpa [hmove] using hi
      have hi'' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.seekOut b, (decListOutStart (c :: outs) R).move Dir.left⟩
          ⟨.checkOutput,
            (decListOutStart []
              ((c :: outs).reverse.map some ++ R)).write
                (some b)⟩
          (c :: outs).length := by
        simpa [decListOutStart, List.reverse_cons, List.map_append,
          List.append_assoc] using hi'
      exact stepsTo_cons _ hs hi''

noncomputable def decListCheckOutputStart (pref bits : List Bool)
    (R : List (Option Bool)) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (pref.map some))
    (ListBlank.mk (bits.map some ++ none :: R))

lemma decListCheckOutputStart_cons_move_right (pref : List Bool)
    (b : Bool) (bits : List Bool)
    (R : List (Option Bool)) :
    (decListCheckOutputStart pref (b :: bits) R).move Dir.right =
      decListCheckOutputStart (b :: pref) bits R := by
  simp [decListCheckOutputStart, Tape.move_right_mk', ListBlank.head_mk,
    ListBlank.tail_mk, ListBlank.cons_mk]

lemma decListMachine_checkOutput_scan (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (pref : List Bool) (R : List (Option Bool)) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.checkOutput, decListCheckOutputStart pref bits R⟩
      ⟨.checkInput,
        Tape.mk' (ListBlank.mk
          (none :: bits.reverse.map some ++ pref.map some))
          (ListBlank.mk R)⟩
      (bits.length + 1) := by
  induction bits generalizing pref R with
  | nil =>
      have hs := decListMachine_checkOutput_none tm out
        (decListCheckOutputStart pref [] R) (by
          simp [decListCheckOutputStart])
      simpa [decListCheckOutputStart] using
        (stepsTo_cons _ hs (stepsTo_zero _ _))
  | cons c bits ih =>
      have hs := decListMachine_checkOutput_some tm out
        (decListCheckOutputStart pref (c :: bits) R) (x := c) (by
          simp [decListCheckOutputStart])
      have hi := ih (c :: pref) R
      have hmove := decListCheckOutputStart_cons_move_right pref c bits R
      have hi' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.checkOutput,
            (decListCheckOutputStart pref (c :: bits) R).move Dir.right⟩
          ⟨.checkInput,
            Tape.mk' (ListBlank.mk
              (none :: bits.reverse.map some ++ (c :: pref).map some))
              (ListBlank.mk R)⟩
          (bits.length + 1) := by
        simpa [hmove] using hi
      have hi'' : StepsTo (TM0.step (decListMachine tm out))
          ⟨.checkOutput,
            (decListCheckOutputStart pref (c :: bits) R).move Dir.right⟩
          ⟨.checkInput,
            Tape.mk' (ListBlank.mk
              (none :: (c :: bits).reverse.map some ++ pref.map some))
              (ListBlank.mk R)⟩
          (c :: bits).length := by
        simpa [decListCheckOutputStart, List.reverse_cons,
          List.map_append, List.append_assoc] using hi'
      exact stepsTo_cons _ hs hi''

lemma decListForwardTape_trailing (pre : List Bool)
    (L : List (Option Bool)) (n : ℕ) :
    Tape.mk' (ListBlank.mk L)
        (ListBlank.mk (pre.map some ++ List.replicate n none)) =
      decListForwardTape pre L := by
  apply congrArg (fun R => Tape.mk' (ListBlank.mk L) R)
  simp only [tapeSymbols]
  apply Quotient.sound'
  exact Or.inr ⟨n, rfl⟩

/-- Decodes the rightmost nonempty block into a vector and reaches `readBackFinish` in the exact
    number of steps given by the `StepsTo` conclusion. -/
lemma decListMachine_checkInput_to_block (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (pre block : List Bool) (L : List (Option Bool))
    (hblock : block ≠ []) (hlen : block.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = block.reverse ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.checkInput, decListForwardTape (pre ++ block.reverse) L⟩
        ⟨.readBackFinish (decListResult tm out v),
          decListReadTape (decListN tm) [] (pre.reverse.map some ++ L) []⟩
        (1 + ((pre ++ block.reverse).length + 1) +
          (2 * block.length - 1)) := by
  let raw := pre ++ block.reverse
  have hraw : raw ≠ [] := by
    dsimp [raw]
    simp [hblock]
  obtain ⟨y, rest, hcons⟩ := List.exists_cons_of_ne_nil hraw
  have hhead : (decListForwardTape raw L).head = some y := by
    rw [hcons]
    simp [decListForwardTape, tapeSymbols]
  have hstep :
      TM0.step (decListMachine tm out) ⟨.checkInput, decListForwardTape raw L⟩ =
        some ⟨.seekEnd true, (decListForwardTape raw L).write (some y)⟩ := by
    simp [TM0.step, decListMachine, hhead]
  have hwrite : (decListForwardTape raw L).write (some y) =
      decListForwardTape raw L := by
    rw [hcons]
    simp [decListForwardTape, tapeSymbols, Tape.write_mk',
      ListBlank.tail_mk, ListBlank.cons_mk]
  rw [hwrite] at hstep
  have hs := decListMachine_seekEnd_to_block tm out true pre block L hblock
  obtain ⟨v, hv, hwalk⟩ := decListMachine_readBack_walk tm out true
    ⟨0, by omega⟩ .nil block (pre.reverse.map some ++ L) [] hblock
    (by simp [hlen])
  have hwalk' :
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.readBack true ⟨0, by omega⟩ .nil,
          decListReadTape 0 block (pre.reverse.map some ++ L) []⟩
        ⟨.readBackFinish (decListResult tm out v),
          decListReadTape (decListN tm) [] (pre.reverse.map some ++ L) []⟩
        (2 * block.length - 1) := by
    simpa [hlen] using hwalk
  have hchain := stepsTo_trans _
    (stepsTo_cons _ hstep (stepsTo_zero _ _))
    (stepsTo_trans _ hs hwalk')
  have hv' : v.toList = block.reverse := by simpa using hv
  refine ⟨v, hv', ?_⟩
  convert hchain using 1
  all_goals simp [List.length_append, List.length_reverse, Nat.add_assoc]
  all_goals omega


end NPComplete.CookLevin

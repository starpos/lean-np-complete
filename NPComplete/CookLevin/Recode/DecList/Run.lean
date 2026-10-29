module

public import NPComplete.CookLevin.Recode.DecList.RawPreprocess

/-!
# Raw decoder runs

The tape-level decoder wraps the block phases with initialization and completion
logic. This module relates those wrapped transitions to the phase machine and
proves the start-to-finish runs needed by the raw computability result.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

lemma decListRawMachine_run_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (q : DecListPhase (decListN tm)) (T : Tape (Option Bool)) :
    TM0.step (decListRawMachine tm out) ⟨.run q, T⟩ =
      (TM0.step (decListMachine tm out) ⟨q, T⟩).map
        (fun p => ⟨.run p.1, p.2⟩) := by
  cases h : decListMachine tm out q T.head with
  | none => simp [TM0.step, decListRawMachine, h]
  | some p =>
      rcases p with ⟨q', s⟩
      simp [TM0.step, decListRawMachine, h]

lemma decListRawMachine_run_steps (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    {q q' : DecListPhase (decListN tm)} {T T' : Tape (Option Bool)}
    {k : ℕ}
    (h : StepsTo (TM0.step (decListMachine tm out))
      ⟨q, T⟩ ⟨q', T'⟩ k) :
    StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.run q, T⟩ ⟨.run q', T'⟩ k := by
  induction k generalizing q T q' T' with
  | zero =>
      simpa [StepsTo] using h
  | succ k ih =>
      obtain ⟨mid, hmid, hstep⟩ :=
        (TM1to0.stepsTo_succ_iff).1 h
      obtain ⟨qmid, Tmid⟩ := mid
      have hih := ih hmid
      have hrun :
          TM0.step (decListRawMachine tm out) ⟨.run qmid, Tmid⟩ =
            some ⟨.run q', T'⟩ := by
        rw [decListRawMachine_run_step]
        simp [hstep]
      exact stepsTo_succ _ hih hrun

lemma decListMachine_readBack_some_mid (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (i : Fin (decListN tm).succ)
    (acc : List.Vector Bool i.val) (b : Bool) (T : Tape (Option Bool))
    (hi : i.val + 1 < decListN tm) (hhead : T.head = some b) :
    TM0.step (decListMachine tm out)
        ⟨.readBack hasOutput i acc, T⟩ =
      some ⟨.readBackMove hasOutput ⟨i.val + 1, by
        change i.val + 1 < decListN tm + 1
        omega⟩ (acc.cons b), T.write none⟩ := by
  simp [TM0.step, decListMachine, hhead, hi]

lemma decListMachine_readBack_some_last (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (i : Fin (decListN tm).succ)
    (acc : List.Vector Bool i.val) (b : Bool) (T : Tape (Option Bool))
    (hi : i.val + 1 = decListN tm) (hhead : T.head = some b) :
    TM0.step (decListMachine tm out)
        ⟨.readBack hasOutput i acc, T⟩ =
      some ⟨.readBackFinish
        (decListResult tm out ⟨(acc.cons b).toList,
          by simp [List.Vector.toList_length, hi]⟩), T.write none⟩ := by
  simp [TM0.step, decListMachine, hhead, hi]

lemma decListMachine_readBack_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (i : Fin (decListN tm).succ)
    (acc : List.Vector Bool i.val) (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (decListMachine tm out)
        ⟨.readBack hasOutput i acc, T⟩ =
      some ⟨.partialRestart hasOutput, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hhead]

lemma decListMachine_partialRestart_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (decListMachine tm out)
        ⟨.partialRestart hasOutput, T⟩ =
      some ⟨.checkInput, T.write none⟩ := by
  simp [TM0.step, decListMachine, hhead]

lemma decListMachine_seekEnd_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (h : Bool) (T : Tape (Option Bool)) {b : Bool}
    (hhead : T.head = some b) :
    TM0.step (decListMachine tm out) ⟨.seekEnd h, T⟩ =
      some ⟨.seekEnd h, T.move Dir.right⟩ := by
  simp [TM0.step, decListMachine, hhead]

lemma decListMachine_seekEnd_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (h : Bool) (T : Tape (Option Bool)) (hn : 0 < decListN tm)
    (hhead : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.seekEnd h, T⟩ =
      some ⟨.readBack h ⟨0, by omega⟩ .nil, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hhead, hn]

lemma decListMachine_seekEnd_scan (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (raw : List Bool) (L : List (Option Bool)) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekEnd hasOutput, decListForwardTape raw L⟩
      ⟨.seekEnd hasOutput,
        decListForwardTape [] (raw.reverse.map some ++ L)⟩
      raw.length := by
  induction raw generalizing L with
  | nil => exact stepsTo_zero _ _
  | cons b raw ih =>
      have hs := decListMachine_seekEnd_some tm out hasOutput
        (b := b) (decListForwardTape (b :: raw) L) (by
          rfl)
      have hr := ih (some b :: L)
      rw [decListForwardTape_move_right] at hs
      refine stepsTo_cons _ hs ?_
      simpa [decListForwardTape, List.reverse_cons, List.map_append,
        List.append_assoc] using hr

lemma decListReadTape_block_reverse (pre block : List Bool)
    (L : List (Option Bool)) (hblock : block ≠ []) :
    decListReadTape 0 block (pre.reverse.map some ++ L) [] =
      (decListForwardTape [] ((pre ++ block.reverse).reverse.map some ++ L)).move Dir.left := by
  cases block with
  | nil => exact (hblock rfl).elim
  | cons b block =>
      simp [decListReadTape, decListForwardTape, tapeSymbols,
        List.reverse_append, List.map_append, Tape.move_left_mk',
        ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk,
        List.append_assoc]

lemma decListMachine_seekEnd_to_readBack (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (raw : List Bool) (L : List (Option Bool))
    (hraw : raw ≠ []) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekEnd hasOutput, decListForwardTape raw L⟩
      ⟨.readBack hasOutput ⟨0, by
        have _hn := decN_pos tm
        omega⟩ .nil,
        (decListForwardTape [] (raw.reverse.map some ++ L)).move Dir.left⟩
      (raw.length + 1) := by
  have hs := decListMachine_seekEnd_scan tm out hasOutput raw L
  have hn : 0 < decListN tm := by exact decN_pos tm
  have he := decListMachine_seekEnd_none tm out hasOutput
    (decListForwardTape [] (raw.reverse.map some ++ L)) hn (by
      rfl)
  have hz := stepsTo_cons _ he (stepsTo_zero _ _)
  have htot := stepsTo_trans _ hs hz
  cases raw with
  | nil => exact (hraw rfl).elim
  | cons b raw =>
      convert htot using 1
      all_goals simp
      all_goals omega

lemma decListMachine_seekEnd_to_block (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (pre block : List Bool) (L : List (Option Bool))
    (hblock : block ≠ []) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekEnd hasOutput, decListForwardTape (pre ++ block.reverse) L⟩
      ⟨.readBack hasOutput ⟨0, by
        have _hn := decN_pos tm
        omega⟩ .nil,
        decListReadTape 0 block (pre.reverse.map some ++ L) []⟩
      ((pre ++ block.reverse).length + 1) := by
  have hraw : pre ++ block.reverse ≠ [] := by
    simp [hblock]
  have h := decListMachine_seekEnd_to_readBack tm out hasOutput
    (pre ++ block.reverse) L hraw
  rw [decListReadTape_block_reverse pre block L hblock]
  simpa [List.length_append, List.length_reverse] using h

lemma decListMachine_readBackMove_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (h : Bool) (i : Fin (decListN tm).succ)
    (acc : List.Vector Bool i.val) (T : Tape (Option Bool)) :
    TM0.step (decListMachine tm out)
        ⟨.readBackMove h i acc, T⟩ =
      some ⟨.readBack h i acc, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine]

lemma decListMachine_readBackFinish_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) :
    TM0.step (decListMachine tm out)
        ⟨.readBackFinish b, T⟩ =
      some ⟨.seekSep b, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine]

lemma decListMachine_seekSep_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) {x : Bool} (hx : T.head = some x) :
    TM0.step (decListMachine tm out) ⟨.seekSep b, T⟩ =
      some ⟨.seekSep b, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_seekSep_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.seekSep b, T⟩ =
      some ⟨.seekOut b, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_seekOut_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) {x : Bool} (hx : T.head = some x) :
    TM0.step (decListMachine tm out) ⟨.seekOut b, T⟩ =
      some ⟨.seekOut b, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_seekOut_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.seekOut b, T⟩ =
      some ⟨.checkOutput, T.write (some b)⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_checkOutput_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) {x : Bool} (hx : T.head = some x) :
    TM0.step (decListMachine tm out) ⟨.checkOutput, T⟩ =
      some ⟨.checkOutput, T.move Dir.right⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_checkOutput_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.checkOutput, T⟩ =
      some ⟨.checkInput, T.move Dir.right⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_checkInput_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.checkInput, T⟩ =
      some ⟨.findOut, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_findOut_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.findOut, T⟩ =
      some ⟨.walkOutLeft, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_walkOutLeft_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) {x : Bool} (hx : T.head = some x) :
    TM0.step (decListMachine tm out) ⟨.walkOutLeft, T⟩ =
      some ⟨.walkOutLeft, T.move Dir.left⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_walkOutLeft_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (hx : T.head = none) :
    TM0.step (decListMachine tm out) ⟨.walkOutLeft, T⟩ =
      some ⟨.done, T.move Dir.right⟩ := by
  simp [TM0.step, decListMachine, hx]

lemma decListMachine_readBack_walk (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (hasOutput : Bool) (i : Fin (decListN tm).succ)
    (acc : List.Vector Bool i.val) (remaining : List Bool)
    (L R : List (Option Bool)) (hrem : remaining ≠ [])
    (hlen : i.val + remaining.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = remaining.reverse ++ acc.toList ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.readBack hasOutput i acc,
          decListReadTape i.val remaining L R⟩
        ⟨.readBackFinish (decListResult tm out v),
          decListReadTape (i.val + remaining.length) [] L R⟩
        (2 * remaining.length - 1) := by
  cases remaining with
  | nil => exact (hrem rfl).elim
  | cons b rest =>
      cases rest with
      | nil =>
          have hlast : i.val + 1 = decListN tm := by simpa using hlen
          have hhead :
              (decListReadTape i.val [b] L R).head = some b :=
            decListReadTape_nonempty_head _ _ _ _ _
          have hs := decListMachine_readBack_some_last tm out hasOutput i acc b
            (decListReadTape i.val [b] L R) hlast hhead
          let v : List.Vector Bool (decListN tm) :=
            ⟨b :: acc.toList, by simp; omega⟩
          have hv : v.toList = [b] ++ acc.toList := rfl
          have hacc : (acc.cons b).toList = b :: acc.toList := by
            simp [List.Vector.toList_cons]
          have hres :
              decListResult tm out
                  ⟨(acc.cons b).toList,
                    by simp [List.Vector.toList_length, hlast]⟩ =
                decListResult tm out v := by
            simp [v, hacc]
          have hT := decListReadTape_last_step i.val b L R
          refine ⟨v, hv, ?_⟩
          simpa [v, hT, hres, hacc, decListReadTape, List.replicate_succ] using
            (stepsTo_cons _ hs (stepsTo_zero _ _))
      | cons c rest =>
          have hmid : i.val + 1 < decListN tm := by
            have := hlen
            simp at this
            omega
          let i' : Fin (decListN tm).succ :=
            ⟨i.val + 1, by omega⟩
          let acc' := acc.cons b
          have hhead :
              (decListReadTape i.val (b :: c :: rest) L R).head = some b :=
            decListReadTape_nonempty_head _ _ _ _ _
          have hs := decListMachine_readBack_some_mid tm out hasOutput i acc b
            (decListReadTape i.val (b :: c :: rest) L R) hmid hhead
          have hm := decListMachine_readBackMove_step tm out hasOutput i' acc'
            ((decListReadTape i.val (b :: c :: rest) L R).write none)
          have hT := decListReadTape_mid_step i.val b c rest L R
          have hlen' : i'.val + (c :: rest).length = decListN tm := by
            dsimp [i']
            simp at hlen ⊢
            omega
          have hi := decListMachine_readBack_walk tm out hasOutput i' acc'
            (c :: rest) L R (by simp) hlen'
          obtain ⟨v, hv, hr⟩ := hi
          have hr' : StepsTo (TM0.step (decListMachine tm out))
              ⟨.readBack hasOutput i' acc',
                ((decListReadTape i.val (b :: c :: rest) L R).write none).move Dir.left⟩
              ⟨.readBackFinish (decListResult tm out v),
                decListReadTape (i'.val + (c :: rest).length) [] L R⟩
              (2 * (c :: rest).length - 1) := by
            simpa [i', hT] using hr
          refine ⟨v, ?_, ?_⟩
          · simpa [acc', List.Vector.toList_cons, List.reverse_cons,
              List.append_assoc] using hv
          · have hchain := stepsTo_cons _ hs (stepsTo_cons _ hm hr')
            have hiEq : i'.val + (c :: rest).length =
                i.val + (b :: c :: rest).length := by
              dsimp [i']
              change i.val + 1 + (rest.length + 1) =
                i.val + (rest.length + 1 + 1)
              omega
            have htime : 1 + (1 + (2 * (c :: rest).length - 1)) =
                2 * (b :: c :: rest).length - 1 := by
              change 1 + (1 + (2 * (rest.length + 1) - 1)) =
                2 * (rest.length + 1 + 1) - 1
              omega
            convert hchain using 1
            · rw [hiEq]
            · omega


end NPComplete.CookLevin

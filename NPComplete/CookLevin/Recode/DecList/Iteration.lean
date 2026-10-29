module

public import NPComplete.CookLevin.Recode.DecList.Blocks

/-!
# Decoded-list iteration

Each block macro appends one decoded symbol, so whole-output correctness follows
by iterating the local transition. This layer combines those macros into runs and
bounds their total cost for the raw decoder's output-time proof.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

lemma decListMachine_final_from_check (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (outs : List Bool) :
    ∃ k : ℕ,
      k ≤ outs.length + 3 ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.checkInput, decListForwardTape [] (none :: outs.map some)⟩
        ⟨.done, Tape.mk₁ (tapeSymbols outs.reverse)⟩ k := by
  cases outs with
  | nil =>
      let T : Tape (Option Bool) := decListForwardTape [] [none]
      have hc := decListMachine_checkInput_none tm out T (by
        simp [T, decListForwardTape, tapeSymbols, default])
      let T₁ := T.move Dir.left
      have hf := decListMachine_findOut_none tm out T₁ (by
        simp [T₁, T, decListForwardTape, tapeSymbols])
      let T₂ := T₁.move Dir.left
      have hn := decListMachine_walkOutLeft_none tm out T₂ (by
        simp [T₂, T₁, T, decListForwardTape, tapeSymbols, default])
      have hchain := stepsTo_cons _ hc
        (stepsTo_cons _ hf
          (stepsTo_cons _ hn (stepsTo_zero _ _)))
      have hblank :
          Tape.mk' (ListBlank.mk [none]) (ListBlank.mk [none]) =
            Tape.mk₁ (tapeSymbols ([] : List Bool)) := by
        simp only [Tape.mk₁, Tape.mk₂]
        congr 1
        · apply Quotient.sound'
          exact Or.inr ⟨1, rfl⟩
        · apply Quotient.sound'
          exact Or.inr ⟨1, rfl⟩
      refine ⟨3, by simp, ?_⟩
      simpa [T, T₁, T₂, decListForwardTape, Tape.move_left_mk',
        Tape.move_right_mk', Tape.mk₁, Tape.mk₂, tapeSymbols,
        ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk,
        default, hblank] using hchain
  | cons c rest =>
      let T : Tape (Option Bool) :=
        decListForwardTape [] (none :: (c :: rest).map some)
      have hc := decListMachine_checkInput_none tm out T (by
        simp [T, decListForwardTape, tapeSymbols, default])
      let T₁ := T.move Dir.left
      have hf := decListMachine_findOut_none tm out T₁ (by
        simp [T₁, T, decListForwardTape, tapeSymbols])
      have hbase : T₁.move Dir.left =
          decListOutStart (c :: rest) [none] := by
        simp [T₁, T, decListForwardTape, decListOutStart,
          Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
          ListBlank.cons_mk, tapeSymbols]
      rw [hbase] at hf
      have hs := decListMachine_walkOutLeft_scan tm out rest c []
      have hchain := stepsTo_cons _ hc
        (stepsTo_cons _ hf hs)
      refine ⟨rest.length + 4, by simp, ?_⟩
      simpa [T, T₁, decListForwardTape, decListOutStart,
        List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc] using hchain

lemma decListMachine_seekEnd_empty_run (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    ∃ k : ℕ,
      k ≤ 6 ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false, Tape.mk₁ (tapeSymbols ([] : List Bool))⟩
        ⟨.done, Tape.mk₁ (tapeSymbols ([] : List Bool))⟩ k := by
  let T : Tape (Option Bool) := Tape.mk₁ (tapeSymbols ([] : List Bool))
  have hn : 0 < decListN tm := decN_pos tm
  have hs := decListMachine_seekEnd_none tm out false T hn (by
    simp [T, Tape.mk₁, Tape.mk₂, tapeSymbols, default])
  let T₁ := T.move Dir.left
  have hr := decListMachine_readBack_none tm out false
    ⟨0, by omega⟩ .nil T₁ (by
      simp [T₁, T, Tape.mk₁, Tape.mk₂, tapeSymbols,
        Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
        ListBlank.cons_mk, default])
  let T₂ := T₁.move Dir.left
  have hc := decListMachine_partialRestart_none tm out false T₂ (by
    simp [T₂, T₁, T, Tape.mk₁, Tape.mk₂, tapeSymbols,
      Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk, default])
  obtain ⟨k, hk, hfin⟩ := decListMachine_final_from_check tm out []
  have hchain := stepsTo_cons _ hs
    (stepsTo_cons _ hr (stepsTo_cons _ hc (stepsTo_zero _ _)))
  refine ⟨k + 3, ?_, ?_⟩
  · have hk' : k ≤ 3 := by simpa using hk
    omega
  have hmid :
      T₂.write none =
        decListForwardTape [] (none :: ([] : List Bool).map some) := by
    simp only [T₂, T₁, T, Tape.mk₁, Tape.mk₂, Tape.write_mk',
      Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk, decListForwardTape, tapeSymbols]
    change Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none]) =
      Tape.mk' (ListBlank.mk [none]) (ListBlank.mk [])
    rw [dec_list_raw_blank_right]
    simpa [Tape.move_right_mk'] using
      dec_list_raw_blank_move_right.symm
  rw [hmid] at hchain
  have htotal := stepsTo_trans _ hchain hfin
  simpa [T, Tape.mk₁, Tape.mk₂, tapeSymbols] using htotal

lemma decListMachine_raw_blocks_run_bound (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (blocks : List (DecListRawBlock tm))
    (hblocks : blocks ≠ []) :
    ∃ k : ℕ,
      k ≤ (2 * blocks.length + 8) *
        (40 + 8 * (decListRawBlocksBits tm blocks).length +
          8 * decListN tm) ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false,
          Tape.mk₁ (tapeSymbols (decListRawBlocksBits tm blocks))⟩
        ⟨.done,
          Tape.mk₁ (tapeSymbols
            (blocks.map (decListRawBlockResult tm out)))⟩ k := by
  induction blocks using List.reverseRecOn with
  | nil => exact (hblocks rfl).elim
  | append_singleton blocks b =>
      let pre := decListRawBlocksBits tm blocks
      let block := b.1
      have hblock : block ≠ [] := by
        intro hb
        have hzero : block.length = 0 := by simp [hb]
        have hlen := b.2
        rw [hzero] at hlen
        have hn : 0 < decListN tm := decN_pos tm
        omega
      have hlen : block.length = decListN tm := b.2
      obtain ⟨v, hv, km, hkm, hmacro⟩ := decListMachine_seekEnd_block_macro
        tm out pre block hblock hlen
      let bvec : List.Vector Bool (decListN tm) :=
        ⟨block.reverse, by rw [List.length_reverse]; exact hlen⟩
      have hres : decListResult tm out v =
          decListRawBlockResult tm out b := by
        have hvv : v = bvec := by
          apply List.Vector.eq
          simpa [bvec, block] using hv
        subst v
        rfl
      obtain ⟨ki, hki, hiter⟩ := decListMachine_raw_blocks_iter_bound tm out
        blocks [decListRawBlockResult tm out b]
      let outs := [decListRawBlockResult tm out b] ++
        blocks.reverse.map (decListRawBlockResult tm out)
      obtain ⟨kf, hkf, hfin⟩ := decListMachine_final_from_check tm out outs
      rw [hres] at hmacro
      have hchain := stepsTo_trans _ hmacro
        (stepsTo_trans _ hiter hfin)
      refine ⟨kf + ki + km, ?_, ?_⟩
      · let C := 40 + 8 * pre.length + 8 * decListN tm
        have hn : 0 < decListN tm := decN_pos tm
        have hkm' : km ≤ C := by
          have hb := hkm
          dsimp [C, pre, block] at hb ⊢
          dsimp [pre, block] at hlen
          omega
        have hki' : ki ≤ (blocks.length + 1) * C := by
          have hfactor :
              20 + 8 * pre.length +
                  8 * [decListRawBlockResult tm out b].length +
                  8 * decListN tm ≤ C := by
            simp [C]
            omega
          exact hki.trans (Nat.mul_le_mul_left _ hfactor)
        have houts : outs.length = blocks.length + 1 := by
          simp [outs]
        have hkf₀ : kf ≤ blocks.length + 4 := by
          rw [houts] at hkf
          omega
        have hC₄ : 4 ≤ C := by
          dsimp [C]
          omega
        have hkf' : kf ≤ (blocks.length + 1) * C := by
          apply hkf₀.trans
          calc
            blocks.length + 4 ≤ (blocks.length + 1) * 4 := by omega
            _ ≤ (blocks.length + 1) * C :=
              Nat.mul_le_mul_left _ hC₄
        have hsum : kf + ki + km ≤ (2 * blocks.length + 3) * C := by
          calc
            kf + ki + km ≤ (blocks.length + 1) * C +
                (blocks.length + 1) * C + C := by
              omega
            _ = (2 * blocks.length + 3) * C := by
              simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
              omega
        have hbits :
            (decListRawBlocksBits tm (blocks ++ [b])).length =
              pre.length + decListN tm := by
          simp [decListRawBlocksBits, pre, block, hlen]
        have hD : C ≤ 40 + 8 *
            (pre.length + decListN tm) + 8 * decListN tm := by
          dsimp [C]
          omega
        have hsum' := hsum.trans (Nat.mul_le_mul_left _ hD)
        have hsum'' : kf + ki + km ≤
            (2 * (blocks.length + 1) + 8) *
              (40 + 8 * (pre.length + decListN tm) +
                8 * decListN tm) := by
          exact hsum'.trans (by
            apply Nat.mul_le_mul_right
            omega)
        rw [hbits]
        simpa [List.length_append] using hsum''
      · simpa [pre, block, outs, decListRawBlocksBits,
          List.flatMap_append, List.reverse_append, List.reverse_cons,
          List.map_append, List.append_assoc, Tape.mk₁, Tape.mk₂,
          decListForwardTape, tapeSymbols, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hchain

lemma decListRawMachine_empty_run (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    ∃ k : ℕ,
      k ≤ 1 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.seekFirst, Tape.mk₁ (tapeSymbols ([] : List Bool))⟩
        ⟨.run .done, Tape.mk₁ (tapeSymbols ([] : List Bool))⟩ k := by
  let T : Tape (Option Bool) := Tape.mk₁ (tapeSymbols ([] : List Bool))
  have hhead : T.head = none := by
    simp [T, Tape.mk₁, Tape.mk₂, tapeSymbols, default]
  have hs :
      TM0.step (decListRawMachine tm out) ⟨.seekFirst, T⟩ =
        some ⟨.run .done, T.write none⟩ := by
    simp [TM0.step, decListRawMachine, hhead]
  have hblank : T.write none = Tape.mk₁ (tapeSymbols ([] : List Bool)) := by
    simp only [T, Tape.mk₁, Tape.mk₂, Tape.write_mk', tapeSymbols]
    apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
    apply Quotient.sound'
    exact Or.inr ⟨1, by simp [default]⟩
  have hsteps := stepsTo_cons _ hs (stepsTo_zero _ _)
  rw [hblank] at hsteps
  exact ⟨1, by simp, by simpa [T] using hsteps⟩

lemma decListRawBlocksBits_length (tm : FinTM2)
    (blocks : List (DecListRawBlock tm)) :
    (decListRawBlocksBits tm blocks).length =
      blocks.length * decListN tm := by
  induction blocks with
  | nil => simp [decListRawBlocksBits]
  | cons b blocks ih =>
      have hconcat : decListRawBlocksBits tm (b :: blocks) =
          b.1.reverse ++ decListRawBlocksBits tm blocks := by
        simp [decListRawBlocksBits]
      rw [hconcat, List.length_append, List.length_reverse, b.2, ih]
      simp only [List.length_cons, Nat.succ_mul]
      omega


end NPComplete.CookLevin

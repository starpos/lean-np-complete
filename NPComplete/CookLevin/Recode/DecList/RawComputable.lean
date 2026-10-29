module

public import NPComplete.CookLevin.Recode.DecList.Iteration

/-!
# Raw decoder computability

A raw packed input may end partway through an encoded symbol, so its decoder
normalizes the tape before running the block-level machine. This module transfers
the output property across that preprocessing and packages the raw machine as
computable.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

noncomputable def decListRawTime (n : ℕ) : Polynomial ℕ :=
  (2 * X + 8) * (40 + 8 * X + Polynomial.C (8 * n)) + 5 * X + 20

lemma decListRawTime_eval (n L : ℕ) :
    (decListRawTime n).eval L =
      (2 * L + 8) * (40 + 8 * L + 8 * n) + 5 * L + 20 := by
  simp [decListRawTime, eval_add, eval_mul, eval_X]

/-- Packages a completed run into the `MachineOutputsInTime` contract. -/
lemma decListRawMachine_machineOutputsInTime_of_run (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (raw output : List Bool) {k : ℕ}
    (hk : k ≤ (decListRawTime (decListN tm)).eval raw.length)
    (hrun : StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.seekFirst, Tape.mk₁ (tapeSymbols raw)⟩
      ⟨.run .done, Tape.mk₁ (tapeSymbols output)⟩ k) :
    MachineOutputsInTime (decListRawMachine tm out)
      (tapeSymbols raw) (tapeSymbols output)
      ((decListRawTime (decListN tm)).eval raw.length) := by
  refine ⟨.run .done, k, hk, ?_, ?_⟩
  · simpa [TM0.init, default] using hrun
  · simp [TM0.step, decListRawMachine, decListMachine]

/-- Decoding the empty raw tape yields the empty list. -/
lemma dec_list_raw_outputs_in_time_decode_nil (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) :
    decodePackedOutputList tm out [] = [] := by
  let e := BlockEnc.ofFinite
    (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  change (e.decodeList []).map (decListCell tm out) = []
  rw [e.decodeList_nil]
  simp

/-- Canonical split of a nonempty raw tape: the preprocessing run leaves the
block-aligned prefix on the tape. -/
lemma decListRawMachine_preprocess_decompose (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (rest : List Bool) :
    ∃ (pre suf : List Bool) (kp : ℕ),
      b :: rest = pre ++ suf ∧
      decListN tm ∣ pre.length ∧
      suf.length < decListN tm ∧
      kp ≤ 5 * (b :: rest).length + 20 ∧
      StepsTo (TM0.step (decListRawMachine tm out))
        ⟨.seekFirst, Tape.mk₁ (tapeSymbols (b :: rest))⟩
        ⟨.run (.seekEnd false), Tape.mk₁ (tapeSymbols pre)⟩ kp ∧
      decodePackedOutputList tm out (b :: rest) =
        decodePackedOutputList tm out pre := by
  obtain ⟨pre, suf, hraw, hprecanon, hprediv, hsuflen, hsuflt⟩ :=
    dec_list_raw_canonical_decompose (decN_pos tm) (b :: rest)
  obtain ⟨kp, hkp, hpreproc⟩ :=
    dec_list_raw_preprocess_canonical_nonempty tm out b rest
  rw [← hprecanon] at hpreproc
  have hdrop : ((b :: rest).reverse.drop
      ((rest.length + 1) % decListN tm)).length ≤ (b :: rest).length := by
    simp
  have hlenraw : (b :: rest).length = rest.length + 1 := by simp
  refine ⟨pre, suf, kp, hraw, hprediv, hsuflt, ?_, hpreproc, ?_⟩
  · simp only [List.length_cons] at hkp hdrop ⊢
    omega
  · calc
      decodePackedOutputList tm out (b :: rest) =
          decodePackedOutputList tm out (pre ++ suf) := by rw [← hraw]
      _ = decodePackedOutputList tm out pre :=
        decodePackedOutputList_append_short tm out pre suf hprediv hsuflt

/-- When the aligned prefix is empty, the output is empty and the run takes
only the preprocessing steps plus a constant. -/
lemma decListRawMachine_machineOutputsInTime_pre_empty (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (raw : List Bool) {kp : ℕ}
    (hkp : kp ≤ 5 * raw.length + 20)
    (hpreproc : StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.seekFirst, Tape.mk₁ (tapeSymbols raw)⟩
      ⟨.run (.seekEnd false), Tape.mk₁ (tapeSymbols ([] : List Bool))⟩ kp)
    (hsem : decodePackedOutputList tm out raw = []) :
    MachineOutputsInTime (decListRawMachine tm out)
      (tapeSymbols raw) (tapeSymbols (decodePackedOutputList tm out raw))
      ((decListRawTime (decListN tm)).eval raw.length) := by
  obtain ⟨ke, hke, hexact⟩ := decListMachine_seekEnd_empty_run tm out
  have hchain := stepsTo_trans _ hpreproc (decListRawMachine_run_steps tm out hexact)
  rw [hsem]
  refine decListRawMachine_machineOutputsInTime_of_run tm out raw [] ?_ hchain
  rw [decListRawTime_eval]
  have hprod : 8 ≤ (2 * raw.length + 8) *
      (40 + 8 * raw.length + 8 * decListN tm) :=
    le_trans (by omega : 8 ≤ (2 * raw.length + 8) * 1)
      (Nat.mul_le_mul_left _ (by omega))
  omega

/-- When the aligned prefix is a nonempty block sequence, the block loop
runs within the time bound. -/
lemma decListRawMachine_machineOutputsInTime_pre_blocks (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (raw : List Bool)
    (blocks : List (DecListRawBlock tm)) {kp : ℕ}
    (hne : blocks ≠ [])
    (hle : (decListRawBlocksBits tm blocks).length ≤ raw.length)
    (hkp : kp ≤ 5 * raw.length + 20)
    (hpreproc : StepsTo (TM0.step (decListRawMachine tm out))
      ⟨.seekFirst, Tape.mk₁ (tapeSymbols raw)⟩
      ⟨.run (.seekEnd false),
        Tape.mk₁ (tapeSymbols (decListRawBlocksBits tm blocks))⟩ kp)
    (hsem : decodePackedOutputList tm out raw =
      blocks.map (decListRawBlockResult tm out)) :
    MachineOutputsInTime (decListRawMachine tm out)
      (tapeSymbols raw) (tapeSymbols (decodePackedOutputList tm out raw))
      ((decListRawTime (decListN tm)).eval raw.length) := by
  obtain ⟨kr, hkr, hexact⟩ := decListMachine_raw_blocks_run_bound tm out blocks hne
  have hchain := stepsTo_trans _ hpreproc (decListRawMachine_run_steps tm out hexact)
  have hblocksle : blocks.length ≤ raw.length := by
    rw [decListRawBlocksBits_length] at hle
    exact (Nat.le_mul_of_pos_right _ (decN_pos tm)).trans hle
  have hkr' : kr ≤ (2 * raw.length + 8) *
      (40 + 8 * raw.length + 8 * decListN tm) :=
    hkr.trans (Nat.mul_le_mul (by omega) (by omega))
  rw [hsem]
  refine decListRawMachine_machineOutputsInTime_of_run tm out raw _ ?_ hchain
  rw [decListRawTime_eval]
  omega

lemma decListRawMachine_machineOutputsInTime (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (raw : List Bool) :
    MachineOutputsInTime (decListRawMachine tm out)
      (tapeSymbols raw)
      (tapeSymbols (decodePackedOutputList tm out raw))
      ((decListRawTime (decListN tm)).eval raw.length) := by
  cases raw with
  | nil =>
      obtain ⟨k, hk, hrun⟩ := decListRawMachine_empty_run tm out
      rw [dec_list_raw_outputs_in_time_decode_nil]
      refine decListRawMachine_machineOutputsInTime_of_run tm out [] [] ?_ hrun
      simp only [decListRawTime_eval]
      omega
  | cons b rest =>
      obtain ⟨pre, suf, kp, hraw, hprediv, hsuflt, hkp, hpreproc, hdec⟩ :=
        decListRawMachine_preprocess_decompose tm out b rest
      by_cases hpre : pre = []
      · subst hpre
        refine decListRawMachine_machineOutputsInTime_pre_empty tm out (b :: rest) hkp
          hpreproc ?_
        rw [hdec, dec_list_raw_outputs_in_time_decode_nil]
      · obtain ⟨blocks, hbits⟩ := decListRawBlocksBits_exists tm hprediv
        subst hbits
        have hne : blocks ≠ [] := by
          rintro rfl
          exact hpre rfl
        refine decListRawMachine_machineOutputsInTime_pre_blocks tm out (b :: rest) blocks
          hne ?_ hkp hpreproc ?_
        · rw [hraw]
          simp
        · rw [hdec]
          exact decodePackedOutputList_raw_blocks tm out blocks


end NPComplete.CookLevin

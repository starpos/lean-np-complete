module

public import NPComplete.CookLevin.UniformPackaging.OuterZero

/-!
# Uniform producer program

The reduction's semantic stages must form one executable program while keeping
setup, repeated emission, and finalization separately analyzable. This module
assembles those phases and proves the evaluation behavior used by later bounds
and correctness arguments.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

def uniformProducerSetupWith (continuation : Program) : Program :=
  Program.seq uniformRelocateProg <|
  Program.seq (uniformCursorInitProg uctCursorReg uctInputBaseReg) <|
  Program.seq uniformControlInitProg <|
  Program.seq
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg) <|
  Program.seq uniformPostDecodeStatsProg <|
  Program.seq uniformSaveBoundProg <|
  Program.seq uniformSetArenaProg <|
  Program.seq
    (secondPassStartupProgramAt uctCursorReg uctInputBaseReg uctOuterReg uctDoneReg
      uctSavedBoundReg uctCurJ uctTmpJ uniformStartE uctFreshReg uctCountReg) <|
  Program.seq uniformEmitAuxInitProg <|
  Program.seq uniformFreshFromMaxProg <|
  Program.seq uniformEmitResetProg continuation

def uniformProducerSetupProg : Program := uniformProducerSetupWith Program.skip

def uniformProducerLoopProg : Program :=
  .forN (.reg uctOuterReg) uniformEmitIterBody

def uniformProducerFinalizeProg : Program :=
  Program.seq (.assign uctOutBaseReg uniformStartE) <|
  Program.seq (.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE))
    (finalizeOutputProg uctOutBaseReg uctOutLenReg)

def uniformProducerProg : Program :=
  uniformProducerSetupWith
    (uniformProducerLoopProg.seq uniformProducerFinalizeProg)

lemma uniformProducerProg_eq_uniformSatToThreeCNFProg :
    uniformProducerProg = uniformSatToThreeCNFProg := by
  rfl

lemma uniformProducerSetupProg_eval (φ : CNF) :
    uniformProducerSetupProg.eval (bitInputStore (encodeCNF φ)) =
      uniformProducerResetStore φ := by
  simp [uniformProducerSetupProg, uniformProducerSetupWith, uniformProducerResetStore,
    eval_seq]

lemma programBoundedIn_uniform_producer_setup_append
    (B : ℕ) (σ : Store) (continuation : Program)
    (hsetup : ProgramBoundedIn B σ uniformProducerSetupProg)
    (hcontinuation : ProgramBoundedIn B
      (uniformProducerSetupProg.eval σ) continuation) :
    ProgramBoundedIn B σ (uniformProducerSetupWith continuation) := by
  simp only [uniformProducerSetupProg] at hsetup
  simp only [uniformProducerSetupWith] at hsetup ⊢
  simp only [ProgramBoundedIn] at hsetup ⊢
  rcases hsetup with ⟨h1, hrest⟩
  rcases hrest with ⟨h2, hrest⟩
  rcases hrest with ⟨h3, hrest⟩
  rcases hrest with ⟨h4, hrest⟩
  rcases hrest with ⟨h5, hrest⟩
  rcases hrest with ⟨h6, hrest⟩
  rcases hrest with ⟨h7, hrest⟩
  rcases hrest with ⟨h8, hrest⟩
  rcases hrest with ⟨h9, hrest⟩
  rcases hrest with ⟨h10, hrest⟩
  rcases hrest with ⟨h11, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    (by simpa [uniformProducerSetupProg, uniformProducerSetupWith, eval_seq] using hcontinuation)⟩

lemma programBoundedIn_decodeClauseWithLengthPrefixAt_of_bounds
    (B cursorReg doneReg remainingReg lengthReg boundReg : ℕ) (σ : Store)
    (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ doneReg ≤ B ∧ remainingReg ≤ B ∧ lengthReg ≤ B ∧
      boundReg ≤ B)
    (hdist : cursorReg ≠ doneReg ∧ cursorReg ≠ lengthReg ∧ lengthReg ≠ doneReg ∧
      boundReg ≠ cursorReg ∧ boundReg ≠ lengthReg ∧ boundReg ≠ doneReg)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg) := by
  rcases hidx with ⟨hcurI, hdoneI, hremI, hlenI, hboundI⟩
  rcases hdist with ⟨hcd, hcl, hld, hbc, hbl, hbd⟩
  let σ0 := (Program.assign doneReg (.const 0)).eval σ
  let σ1 := (Program.assign lengthReg (.const 0)).eval σ0
  have hσ0 : StoreValuesLe B σ0 := by
    exact storeValuesLe_assign hσ (by simp [Expr.eval])
  have hσ1 : StoreValuesLe B σ1 := by
    exact storeValuesLe_assign hσ0 (by simp [Expr.eval])
  have hσ0b : σ0 boundReg = σ boundReg := by
    simp [σ0, eval_assign, Expr.eval, writeReg_diff _ doneReg _ _ hbd]
  have hσ1b : σ1 boundReg = σ boundReg := by
    simp [σ1, eval_assign, Expr.eval, writeReg_diff _ lengthReg _ _ hbl, hσ0b]
  have hσ1c : σ1 cursorReg = σ cursorReg := by
    simp [σ1, σ0, eval_assign, Expr.eval,
      writeReg_diff _ lengthReg _ _ hcl, writeReg_diff _ doneReg _ _ hcd]
  have hσ1l : σ1 lengthReg = 0 := by
    simp [σ1, eval_assign, Expr.eval, writeReg_same]
  have hnat : ProgramBoundedIn B σ1
      (decodeNatProgramAt cursorReg lengthReg doneReg boundReg) := by
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg lengthReg doneReg boundReg B σ1
      hcl hcd hld ⟨hcurI, hlenI, hdoneI, hboundI⟩
    · rw [hσ1c, hσ1b]
      omega
    · rw [hσ1l, hσ1b]
      omega
  let σ2 := (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1
  have hσ2 : StoreValuesLe B σ2 := by
    exact program_eval_storeValuesLe σ1 _ (by omega) hσ1 hnat
      (scanFree_decodeNatProgramAt cursorReg lengthReg doneReg boundReg)
  unfold decodeClauseWithLengthPrefixAt
  simp only [ProgramBoundedIn]
  rw [show (Program.assign doneReg (.const 0)).eval σ = σ0 from rfl]
  rw [show (Program.assign lengthReg (.const 0)).eval σ0 = σ1 from rfl]
  rw [show (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1 = σ2 from rfl]
  refine ⟨⟨hdoneI, by simp [ExprBoundedIn]⟩, ?_⟩
  refine ⟨⟨hlenI, by simp [ExprBoundedIn]⟩, ?_⟩
  refine ⟨hnat, ?_⟩
  refine ⟨⟨hdoneI, by simp [ExprBoundedIn]⟩, ?_⟩
  exact ⟨hremI, hlenI⟩

lemma decodeClauseWithLengthPrefixAt_cursor_le
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hcl : cursorReg ≠ lengthReg)
    (hrc : remainingReg ≠ cursorReg) (hbl : boundReg ≠ lengthReg)
    (hbd : boundReg ≠ doneReg) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
      cursorReg ≤ σ cursorReg + 1 + σ boundReg := by
  unfold decodeClauseWithLengthPrefixAt
  rw [eval_seq, eval_seq, eval_seq, eval_seq]
  let σ0 := (Program.assign doneReg (.const 0)).eval σ
  let σ1 := (Program.assign lengthReg (.const 0)).eval σ0
  let σ2 := (decodeNatProgramAt cursorReg lengthReg doneReg boundReg).eval σ1
  have hσ1c : σ1 cursorReg = σ cursorReg := by
    simp [σ1, σ0, eval_assign, Expr.eval,
      writeReg_diff _ lengthReg _ _ hcl, writeReg_diff _ doneReg _ _ hcd]
  have hσ1b : σ1 boundReg = σ boundReg := by
    simp [σ1, σ0, eval_assign, Expr.eval,
      writeReg_diff _ lengthReg _ _ hbl,
      writeReg_diff _ doneReg _ _ hbd]
  have hcur : σ2 cursorReg ≤ σ1 cursorReg + σ1 boundReg := by
    dsimp [σ2]
    unfold decodeNatProgramAt decodeUnaryProgAt
    rw [eval_forN]
    simp only [Expr.eval]
    exact loopEval_decodeUnaryStep_cursor_le cursorReg lengthReg doneReg hcl hcd (σ1 boundReg) σ1
  have hσ3 : (Program.assign doneReg (.const 0)).eval σ2 cursorReg = σ2 cursorReg := by
    simp [eval_assign, Expr.eval, writeReg_diff _ doneReg _ _ hcd]
  have hσ4 : (Program.assign remainingReg (.reg lengthReg)).eval
      ((Program.assign doneReg (.const 0)).eval σ2) cursorReg =
        (Program.assign doneReg (.const 0)).eval σ2 cursorReg := by
    simp [eval_assign, Expr.eval, writeReg_diff _ remainingReg _ _ (Ne.symm hrc)]
  rw [hσ4, hσ3]
  rw [hσ1c, hσ1b] at hcur
  exact hcur.trans (by omega)

lemma decodeClauseStepAt_one_cursor_le
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hmc : maxReg ≠ cursorReg) (hbc : boundReg ≠ cursorReg)
    (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) :
    (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg).eval σ
        cursorReg ≤ σ cursorReg + 1 + σ boundReg := by
  unfold decodeClauseStepAt
  rw [eval_ifNZ]
  by_cases hz : σ remainingReg = 0
  · rw [ite_eq_right (by simpa [Expr.eval] using hz)]
    simp [eval_skip]
    omega
  · rw [ite_eq_left (by simpa [Expr.eval] using hz)]
    rw [eval_seq, eval_seq]
    let τ := (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
    have hτ := decodeLiteralValueProgramAt_cursor_le cursorReg polReg varReg doneReg boundReg σ
      hcp hcv hcd hbc hbp hbv hbd
    rw [show (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ = τ from rfl]
    let υ := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ
    have hυ : υ cursorReg = τ cursorReg := by
      simp [υ, eval_assign, Expr.eval,
        writeReg_diff _ remainingReg _ cursorReg (Ne.symm hrc)]
    rw [show (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ = υ from rfl]
    rw [eval_ifNZ]
    by_cases hlt : (Expr.lt (.reg maxReg) (.reg varReg)).eval υ ≠ 0
    · rw [ite_eq_left hlt]
      simp only [eval_assign, Expr.eval]
      rw [writeReg_diff _ maxReg _ cursorReg (Ne.symm hmc), hυ]
      exact hτ
    · rw [ite_eq_right hlt]
      simp [eval_skip, hυ]
      exact hτ

lemma decodeClauseStepAt_cursor_le
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg k : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hrc : remainingReg ≠ cursorReg)
    (hmc : maxReg ≠ cursorReg) (hbc : boundReg ≠ cursorReg)
    (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) (hbr : boundReg ≠ remainingReg)
    (hbm : boundReg ≠ maxReg) :
    (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
      k σ) cursorReg ≤ σ cursorReg + k * (σ boundReg + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [uniform_loopEval_succ_right]
      have hs := decodeClauseStepAt_one_cursor_le cursorReg polReg varReg doneReg remainingReg
        maxReg boundReg
        (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
          k σ) hcp hcv hcd hrc hmc hbc hbp hbv hbd
      have hbnd := decodeClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
        remainingReg maxReg boundReg k σ hbc hbp hbv hbd hbr hbm
      rw [hbnd] at hs
      calc
        _ ≤ (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
          k σ) cursorReg + 1 + σ boundReg := by simpa using hs
        _ ≤ σ cursorReg + (k + 1) * (σ boundReg + 1) := by
          rw [Nat.succ_mul]
          omega

lemma programBoundedIn_decodeClauseStepAt_of_store_bounds
    (B cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ)
    (σ : Store)
    (hσ : StoreValuesLe B σ)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ maxReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hbudget : σ cursorReg + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg) := by
  have hB1 : 1 ≤ B := by omega
  have hlit := programBoundedIn_decodeLiteralValueProgramAt_of_bounds B cursorReg polReg
    varReg doneReg boundReg σ
    ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2.2.2⟩
    ⟨hdist.1, hdist.2.1, hdist.2.2.1, hdist.2.2.2.1,
      hdist.2.2.2.2.1, hdist.2.2.2.2.2.1, hdist.2.2.2.2.2.2.1,
      hdist.2.2.2.2.2.2.2⟩ hB1 hσ hbudget
  have hσlit : StoreValuesLe B
      ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ) :=
    program_eval_storeValuesLe σ _ hB1 hσ hlit
      (scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
  unfold decodeClauseStepAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hidx.2.2.2.2.1, ⟨⟨hlit, ?_⟩, trivial⟩⟩
  refine ⟨⟨hidx.2.2.2.2.1, hidx.2.2.2.2.1, hB1, hσlit remainingReg⟩, ?_⟩
  exact ⟨⟨hidx.2.2.2.2.2.1, hidx.2.2.1⟩,
    ⟨hidx.2.2.2.2.2.1, hidx.2.2.1⟩, trivial⟩

lemma storeValuesLe_decodeClauseStepAt_loop_of_bounds
    (B cursorReg polReg varReg doneReg remainingReg maxReg boundReg k n : ℕ) (σ : Store)
    (hB1 : 1 ≤ B)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ maxReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hloopdist : remainingReg ≠ cursorReg ∧ maxReg ≠ cursorReg ∧
      boundReg ≠ remainingReg ∧ boundReg ≠ maxReg)
    (hσ : StoreValuesLe B σ)
    (hcoarse : σ cursorReg + n * (σ boundReg + 1) + 1 + σ boundReg ≤ B)
    (hk : k ≤ n) :
    StoreValuesLe B
      (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
        k σ) := by
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  rcases hloopdist with ⟨hrc, hmc, hbr, hbm⟩
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hprev := ih hk'
      have hcur := decodeClauseStepAt_cursor_le cursorReg polReg varReg doneReg remainingReg
        maxReg boundReg k σ hcp hcv hcd hrc hmc hbc hbp hbv hbd hbr hbm
      have hbound := decodeClauseStepAt_loopEval_bound_frame cursorReg polReg varReg doneReg
        remainingReg maxReg boundReg k σ hbc hbp hbv hbd hbr hbm
      have hprod : k * (σ boundReg + 1) ≤ n * (σ boundReg + 1) :=
        Nat.mul_le_mul_right _ hk'
      have hbudget :
          (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg
            boundReg) k σ) cursorReg + 1 +
            (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg
              boundReg) k σ) boundReg ≤ B := by
        rw [hbound]
        have hcur' :
            (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg
              boundReg) k σ) cursorReg ≤ σ cursorReg + k * (σ boundReg + 1) := hcur
        omega
      have hstep := programBoundedIn_decodeClauseStepAt_of_store_bounds B cursorReg polReg
        varReg doneReg remainingReg maxReg boundReg
        (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
          k σ) hprev
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
        ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩ hbudget
      rw [uniform_loopEval_succ_right]
      exact program_eval_storeValuesLe _ _ hB1 hprev hstep
        (scanFree_decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)

lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_invariants
    (B cursorReg polReg varReg doneReg remainingReg maxReg lengthReg boundReg : ℕ)
    (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧
      remainingReg ≤ B ∧ maxReg ≤ B ∧ lengthReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧ boundReg ≠ remainingReg)
    (hprefix : ProgramBoundedIn B σ
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg))
    (hbudget : ∀ m <
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
        m ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ))
          cursorReg + 1 +
        (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
          m ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ))
          boundReg ≤ B)
    (hstoreLoop : ∀ m ≤
        (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
          remainingReg,
      StoreValuesLe B
        (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
          m ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ))) :
    ProgramBoundedIn B σ
      (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg boundReg) := by
  unfold decodeClauseWithLengthProgramAt
  simp only [ProgramBoundedIn, ExprBoundedIn]
  refine ⟨hprefix, ⟨hidx.2.2.2.2.1, ?_⟩⟩
  intro m hm
  have hm' := hm
  change m <
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
        remainingReg at hm'
  have hmle : m ≤
      (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
        remainingReg := by omega
  exact programBoundedIn_decodeClauseStepAt_of_store_bounds B cursorReg polReg varReg doneReg
    remainingReg maxReg boundReg
    (loopEval (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
      m ((decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ))
    (hstoreLoop m hmle)
    ⟨hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2.1,
      hidx.2.2.2.2.2.1, hidx.2.2.2.2.2.2.2⟩
    ⟨hdist.1, hdist.2.1, hdist.2.2.1, hdist.2.2.2.1,
      hdist.2.2.2.2.1, hdist.2.2.2.2.2.1, hdist.2.2.2.2.2.2.1,
      hdist.2.2.2.2.2.2.2.1⟩ (hbudget m hm')

/-- The length prefix of a clause decode stays bounded, leaves the remaining counter at the
    clause length, and keeps the cursor-plus-loop budget inside the envelope. -/
lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_input_prefix
    (B N addr : ℕ) (ls : List NPComplete.SAT.Literal)
    (tail : Bits) (τ : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B) (ha : 25 ≤ addr)
    (hσ : StoreValuesLe B τ)
    (hcursor : τ uctCursorReg = addr) (hbound : τ uctBoundReg = N)
    (hls : ls.length + 1 ≤ N)
    (hbits : BitsFrom τ addr (encodeList encodeLiteral ls ++ tail))
    (hcoarse : addr + N + 1 + N * (N + 1) + 1 + N ≤ B) :
    ∃ σ1, σ1 = (decodeClauseWithLengthPrefixAt uctCursorReg uctDoneReg uctRemainingReg
        uctLengthReg uctBoundReg).eval τ ∧
      ProgramBoundedIn B τ
        (decodeClauseWithLengthPrefixAt uctCursorReg uctDoneReg uctRemainingReg
          uctLengthReg uctBoundReg) ∧
      StoreValuesLe B σ1 ∧ σ1 uctRemainingReg = ls.length ∧
      σ1 uctCursorReg + ls.length * (σ1 uctBoundReg + 1) + 1 + σ1 uctBoundReg ≤ B := by
  have hprefix : ProgramBoundedIn B τ
      (decodeClauseWithLengthPrefixAt uctCursorReg uctDoneReg uctRemainingReg
        uctLengthReg uctBoundReg) := by
    apply programBoundedIn_decodeClauseWithLengthPrefixAt_of_bounds B uctCursorReg uctDoneReg
      uctRemainingReg uctLengthReg uctBoundReg τ hσ
      ⟨by simp [uctCursorReg]; omega, by simp [uctDoneReg]; omega,
        by simp [uctRemainingReg]; omega, by simp [uctLengthReg]; omega,
        by simp [uctBoundReg]⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    rw [hcursor, hbound]
    omega
  refine ⟨_, rfl, hprefix, program_eval_storeValuesLe τ _ hB1 hσ hprefix
    (scanFree_decodeClauseWithLengthPrefixAt uctCursorReg uctDoneReg uctRemainingReg
      uctLengthReg uctBoundReg), ?_, ?_⟩
  · have heq := decodeClauseWithLengthPrefixAt_eq uctCursorReg uctDoneReg uctRemainingReg
      uctLengthReg uctBoundReg N τ hbound (by decide) (by decide)
    have hrem := decodeClauseWithLengthPrefix_remaining_eval uctCursorReg uctDoneReg
      uctRemainingReg uctLengthReg N addr ls tail τ (by decide) (by decide) (by decide)
      (by simp [uctCursorReg, uctDoneReg, uctLengthReg]; omega) hcursor hls hbits
    rw [heq]
    exact hrem
  · have hcur := decodeClauseWithLengthPrefixAt_cursor_le uctCursorReg uctDoneReg
      uctRemainingReg uctLengthReg uctBoundReg τ (by decide) (by decide) (by decide)
      (by decide) (by decide)
    have hb := decodeClauseWithLengthPrefixAt_bound_frame uctCursorReg uctDoneReg
      uctRemainingReg uctLengthReg uctBoundReg τ (by decide) (by decide) (by decide)
      (by decide)
    have hprod : ls.length * (N + 1) ≤ N * (N + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [hb, hbound]
    rw [hcursor, hbound] at hcur
    omega

/-- Every intermediate store of the clause-step loop stays in the envelope, given the
    coarse cursor budget after the length prefix. -/
lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_input_loop_store
    (B n : ℕ) (σ1 : Store) (hB1 : 1 ≤ B) (hB25 : 25 ≤ B)
    (hσ1 : StoreValuesLe B σ1) (hrem : σ1 uctRemainingReg = n)
    (hcoarse : σ1 uctCursorReg + n * (σ1 uctBoundReg + 1) + 1 + σ1 uctBoundReg ≤ B) :
    ∀ q ≤ σ1 uctRemainingReg,
      StoreValuesLe B (loopEval
        (decodeClauseStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
          uctMaxReg uctBoundReg) q σ1) := by
  intro q hq
  exact storeValuesLe_decodeClauseStepAt_loop_of_bounds B uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctMaxReg uctBoundReg q n σ1 hB1
    ⟨by simp [uctCursorReg]; omega, by simp [uctPolReg]; omega,
      by simp [uctVarReg]; omega, by simp [uctDoneReg]; omega,
      by simp [uctRemainingReg]; omega, by simp [uctMaxReg]; omega,
      by simp [uctBoundReg]⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ hσ1 hcoarse
    (by rw [hrem] at hq; exact hq)

/-- The cursor-plus-bound budget of each clause step in the loop stays in the envelope. -/
lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_input_loop_budget
    (B n : ℕ) (σ1 : Store) (hrem : σ1 uctRemainingReg = n)
    (hcoarse : σ1 uctCursorReg + n * (σ1 uctBoundReg + 1) + 1 + σ1 uctBoundReg ≤ B) :
    ∀ q < σ1 uctRemainingReg,
      (loopEval (decodeClauseStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctMaxReg uctBoundReg) q σ1) uctCursorReg + 1 +
        (loopEval (decodeClauseStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctRemainingReg uctMaxReg uctBoundReg) q σ1) uctBoundReg ≤ B := by
  intro q hq
  have hq' : q ≤ n := by rw [hrem] at hq; omega
  have hcur := decodeClauseStepAt_cursor_le uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctRemainingReg uctMaxReg uctBoundReg q σ1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hboundq := decodeClauseStepAt_loopEval_bound_frame uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctMaxReg uctBoundReg q σ1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hprod : q * (σ1 uctBoundReg + 1) ≤ n * (σ1 uctBoundReg + 1) :=
    Nat.mul_le_mul_right _ hq'
  rw [hboundq]
  omega

/-- The decoded length, the fresh counter and the count register after a clause decode with
    length, from the semantic decoder specification. -/
lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_input_eval_facts
    (N addr m : ℕ) (ls : List NPComplete.SAT.Literal) (tail : Bits) (τ : Store)
    (ha : 25 ≤ addr)
    (hcursor : τ uctCursorReg = addr) (hmax : τ uctMaxReg = m)
    (hbound : τ uctBoundReg = N)
    (hls : ls.length + 1 ≤ N)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hbits : BitsFrom τ addr (encodeList encodeLiteral ls ++ tail)) :
    (decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctMaxReg uctLengthReg uctBoundReg).eval τ uctLengthReg = ls.length ∧
      (decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctMaxReg uctLengthReg uctBoundReg).eval τ uctFreshReg =
          τ uctFreshReg ∧
      (decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctMaxReg uctLengthReg uctBoundReg).eval τ uctCountReg =
          τ uctCountReg := by
  have hsem := decodeClauseWithLengthProgramDynamic_eval uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctMaxReg uctLengthReg N addr m ls tail τ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg,
      uctMaxReg, uctLengthReg]; omega)
    hcursor hmax hls hvarbound hbits
  have heq := decodeClauseWithLengthProgramAt_eq_dynamic uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctMaxReg uctLengthReg uctBoundReg N τ hbound
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← heq] at hsem
  exact ⟨hsem.2.2.2.1,
    hsem.2.2.2.2 uctFreshReg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    hsem.2.2.2.2 uctCountReg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

lemma programBoundedIn_decodeClauseWithLengthProgramAt_of_input
    (B N addr m : ℕ) (ls : List NPComplete.SAT.Literal)
    (tail : Bits) (τ : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B) (ha : 25 ≤ addr)
    (hσ : StoreValuesLe B τ)
    (hcursor : τ uctCursorReg = addr) (hmax : τ uctMaxReg = m)
    (hbound : τ uctBoundReg = N)
    (hls : ls.length + 1 ≤ N)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hbits : BitsFrom τ addr (encodeList encodeLiteral ls ++ tail))
    (hcoarse : addr + N + 1 + N * (N + 1) + 1 + N ≤ B) :
    ∃ π, π = (decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctMaxReg uctLengthReg uctBoundReg).eval τ ∧
      ProgramBoundedIn B τ
        (decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
          uctRemainingReg uctMaxReg uctLengthReg uctBoundReg) ∧
      StoreValuesLe B π ∧ π uctLengthReg = ls.length ∧
      π uctFreshReg = τ uctFreshReg ∧ π uctCountReg = τ uctCountReg := by
  obtain ⟨σ1, hσ1, hprefix, hσ1store, hσ1rem, hσ1coarse⟩ :=
    programBoundedIn_decodeClauseWithLengthProgramAt_of_input_prefix B N addr ls tail τ
      hB1 hB25 ha hσ hcursor hbound hls hbits hcoarse
  subst hσ1
  have hparser := programBoundedIn_decodeClauseWithLengthProgramAt_of_invariants B
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctMaxReg uctLengthReg
    uctBoundReg τ
    ⟨by simp [uctCursorReg]; omega, by simp [uctPolReg]; omega,
      by simp [uctVarReg]; omega, by simp [uctDoneReg]; omega,
      by simp [uctRemainingReg]; omega, by simp [uctMaxReg]; omega,
      by simp [uctLengthReg]; omega, by simp [uctBoundReg]⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩ hprefix
    (programBoundedIn_decodeClauseWithLengthProgramAt_of_input_loop_budget B ls.length _
      hσ1rem hσ1coarse)
    (programBoundedIn_decodeClauseWithLengthProgramAt_of_input_loop_store B ls.length _
      hB1 hB25 hσ1store hσ1rem hσ1coarse)
  obtain ⟨hlen, hfresh, hcount⟩ :=
    programBoundedIn_decodeClauseWithLengthProgramAt_of_input_eval_facts N addr m ls tail τ
      ha hcursor hmax hbound hls hvarbound hbits
  exact ⟨_, rfl, hparser, program_eval_storeValuesLe τ _ hB1 hσ hparser
    (scanFree_decodeClauseWithLengthProgramAt uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctRemainingReg uctMaxReg uctLengthReg uctBoundReg), hlen, hfresh, hcount⟩

end NPComplete.CookLevin

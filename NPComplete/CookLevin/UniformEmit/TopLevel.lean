module

public import NPComplete.CookLevin.UniformEmit.Dispatch

/-!
# Top-level producer programs

The emitter's register layout and phase programs need one concrete assembly that subsequent proofs
can analyze. This module defines those shared programs and their startup evaluations, while lower
modules establish each phase's correctness.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF)


/-! ## One fixed program on `bitInputStore` -/

def uctPol2Reg : ℕ := 13
def uctVar2Reg : ℕ := 14
def uctPol3Reg : ℕ := 15
def uctVar3Reg : ℕ := 16
def uctPosPolReg : ℕ := 17
def uctNegPolReg : ℕ := 18
def uctCarryPolReg : ℕ := 19
def uctCarryValReg : ℕ := 20
def uctOutBaseReg : ℕ := 21
def uctOutLenReg : ℕ := 22
def uctSavedBoundReg : ℕ := 23
def uctCurJ : ℕ := 1
def uctTmpJ : ℕ := 2

/-- Writer output origin: fixed above every uct control register. -/
def uniformStartE : Expr :=
  .const uniformStartNat

/-- Workspace limit `M = start + (N+1)^3 + 16`, from the saved input length. -/
def uniformME : Expr :=
  .add (.const uniformStartNat)
    (.add
      (.mul (.add (.reg uctSavedBoundReg) (.const 1))
        (.mul (.add (.reg uctSavedBoundReg) (.const 1))
          (.add (.reg uctSavedBoundReg) (.const 1))))
      (.const 16))

/-- After a zero-seeded decode: save the increment total, bump `max` to
    `maxVar+1` when a literal was seen, then form header `numVars`.
    The seen flag is required: `max = 0` for both the empty input and a
    variable-0-only input, while `cnfVarBound` is `0` vs `1`. -/
def uniformPostDecodeStatsProg : Program :=
  .seq (.assign uctTmpReg (.reg uctFreshReg))
    (.seq
      (.ifNZ (.reg uctSeenReg)
        (.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1)))
        .skip)
      (.assign uctFreshReg (.add (.reg uctMaxReg) (.reg uctTmpReg))))

/-- Reset the emission fresh-base to the (possibly bumped) max after the header. -/
def uniformFreshFromMaxProg : Program :=
  .assign uctFreshReg (.reg uctMaxReg)

def uniformEmitAuxInitProg : Program :=
  .seq (.assign uctPosPolReg (.const 0))
    (.assign uctNegPolReg (.const 1))

def uniformEmitResetProg : Program :=
  emitClauseResetProg uctLengthReg uctDoneReg

/-!
The clause-boundary relation carries only the cursor, outer counter, fresh base,
writer state, and the canonical polarity pair.  Every other emitter register is
written before its value can affect a selected branch.  We therefore normalize
the parser, look-ahead, and split-tail registers at the boundary.  The polarity
pair is reset to its canonical relation values rather than treated as scratch.

Read-before-write scratch registers are `pol`, `var`, `done`, `length`,
`remaining`, `pol2`, `var2`, `pol3`, `var3`, `carry_pol`, and `carry_val`.
`posPol` and `negPol` are read before assignment only by the empty and three-
literal branches, so they are reset to their relation values `0` and `1`.
The cursor, outer count, fresh/base state, saved bound, root cell, and writer
cursor are persistent and are deliberately absent from the reset program.
-/
def uniformEmitScratchRegs : List ℕ :=
  [uctPolReg, uctVarReg, uctDoneReg, uctLengthReg, uctRemainingReg,
    uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg,
    uctCarryValReg]

def uniformEmitScratchResetProg : Program :=
  .seq (zeroRegsProg uniformEmitScratchRegs)
    (.seq (.assign uctPosPolReg (.const 0))
      (.assign uctNegPolReg (.const 1)))

def uniformEmitIterCoreBody : Program :=
  emitClauseIterProgramAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg
    uctFreshReg uctOuterReg uctSavedBoundReg

def uniformEmitIterBody : Program :=
  .seq uniformEmitScratchResetProg
    (.seq uniformEmitIterCoreBody uniformEmitScratchResetProg)

lemma uniformEmitScratchResetProg_frame (σ : Store) {r : ℕ}
    (hr : r ∉ uniformEmitScratchRegs) (hp : r ≠ uctPosPolReg)
    (hn : r ≠ uctNegPolReg) :
    uniformEmitScratchResetProg.eval σ r = σ r :=
  (by decide +kernel : uniformEmitScratchResetProg.Avoids
    (fun x => x ∉ uniformEmitScratchRegs ∧ x ≠ uctPosPolReg ∧ x ≠ uctNegPolReg)).eval_frame
    σ ⟨hr, hp, hn⟩

lemma uniformEmitScratchResetProg_values (σ : Store) :
    (uniformEmitScratchResetProg.eval σ) uctPosPolReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctNegPolReg = 1 ∧
    (uniformEmitScratchResetProg.eval σ) uctPolReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctVarReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctDoneReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctLengthReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctRemainingReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctPol2Reg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctVar2Reg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctPol3Reg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctVar3Reg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctCarryPolReg = 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctCarryValReg = 0 := by
  repeat' apply And.intro
  all_goals
    simp [uniformEmitScratchResetProg, uniformEmitScratchRegs, zeroRegsProg,
      eval_seq, eval_assign, Expr.eval, writeReg, uctPolReg, uctVarReg,
      uctDoneReg, uctLengthReg, uctRemainingReg, uctPol2Reg, uctVar2Reg,
      uctPol3Reg, uctVar3Reg, uctPosPolReg, uctNegPolReg, uctCarryPolReg,
      uctCarryValReg]

lemma uniformEmitScratchResetProg_persistent_values (σ : Store) :
    (uniformEmitScratchResetProg.eval σ) 0 = σ 0 ∧
    (uniformEmitScratchResetProg.eval σ) uctCursorReg = σ uctCursorReg ∧
    (uniformEmitScratchResetProg.eval σ) uctOuterReg = σ uctOuterReg ∧
    (uniformEmitScratchResetProg.eval σ) uctFreshReg = σ uctFreshReg ∧
    (uniformEmitScratchResetProg.eval σ) uctInputBaseReg = σ uctInputBaseReg ∧
    (uniformEmitScratchResetProg.eval σ) uctSavedBoundReg = σ uctSavedBoundReg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply uniformEmitScratchResetProg_frame <;> decide

def uniformSaveBoundProg : Program :=
  .assign uctSavedBoundReg (.reg 0)

def uniformSetArenaProg : Program :=
  .assign 0 uniformME

/-- Single input-independent SAT→3CNF producer: relocate, decode, emit, publish ABI. -/
def uniformSatToThreeCNFProg : Program :=
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
   Program.seq uniformEmitResetProg <|
   Program.seq
     (.forN (.reg uctOuterReg) uniformEmitIterBody) <|
  Program.seq (.assign uctOutBaseReg uniformStartE) <|
  Program.seq (.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE))
    (finalizeOutputProg uctOutBaseReg uctOutLenReg)

lemma uniformStartE_eval (σ : Store) :
    uniformStartE.eval σ = uniformStartNat := by
  simp [uniformStartE, Expr.eval]

lemma uniformME_eval (σ : Store) (N : ℕ) (h : σ uctSavedBoundReg = N) :
    uniformME.eval σ = uniformMNat N := by
  simp [uniformME, uniformMNat, uniformSlackNat, uniformStartNat, Expr.eval, h,
    Nat.mul_assoc]

lemma uniformSaveBoundProg_eval (σ : Store) :
    (uniformSaveBoundProg.eval σ) uctSavedBoundReg = σ 0 ∧
    (∀ r, r ≠ uctSavedBoundReg → uniformSaveBoundProg.eval σ r = σ r) := by
  constructor
  · simp [uniformSaveBoundProg, eval_assign, Expr.eval]
  · intro r hr
    simp [uniformSaveBoundProg, eval_assign, Expr.eval,
      writeReg_diff σ uctSavedBoundReg _ r hr]

lemma uniformSetArenaProg_eval (σ : Store) :
    (uniformSetArenaProg.eval σ) 0 = uniformME.eval σ := by
  simp [uniformSetArenaProg, eval_assign]

end NPComplete.CookLevin

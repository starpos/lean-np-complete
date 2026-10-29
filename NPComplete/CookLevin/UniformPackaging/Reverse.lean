module

public import NPComplete.CookLevin.UniformPackaging.OutputBounds

/-!
# Whole-program facts for the uniform SAT-to-3CNF producer

The producer is a fixed `seq` of stages, so properties that every stage has separately
(such as not using the list-scanning operations) are assembled here once for the whole program.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeThreeCNF)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma uniform_loopEval_succ_right (body : Program) (k : ℕ) (σ : Store) :
    loopEval body (k + 1) σ = body.eval (loopEval body k σ) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      rw [loopEval_succ, ih (body.eval σ), loopEval_succ]

lemma scanFree_uniformSatToThreeCNFProg : ScanFree uniformSatToThreeCNFProg := by
  unfold uniformSatToThreeCNFProg
  refine ⟨scanFree_uniformRelocateProg, ?_⟩
  refine ⟨scanFree_uniformCursorInitProg _ _, ?_⟩
  refine ⟨scanFree_uniformControlInitProg, ?_⟩
  refine ⟨scanFree_decodeCNFProgramAtSeen _ _ _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  refine ⟨scanFree_uniformPostDecodeStatsProg, ?_⟩
  refine ⟨scanFree_uniformSaveBoundProg, ?_⟩
  refine ⟨scanFree_uniformSetArenaProg, ?_⟩
  refine ⟨scanFree_secondPassStartupProgramAt _ _ _ _ _ _ _ _ _ _, ?_⟩
  refine ⟨scanFree_uniformEmitAuxInitProg, ?_⟩
  refine ⟨scanFree_uniformFreshFromMaxProg, ?_⟩
  refine ⟨scanFree_uniformEmitResetProg, ?_⟩
  refine ⟨scanFree_uniformEmitIterBody, ?_⟩
  refine ⟨by simp [ScanFree], ?_⟩
  refine ⟨by simp [ScanFree], scanFree_finalizeOutputProg⟩

end NPComplete.CookLevin

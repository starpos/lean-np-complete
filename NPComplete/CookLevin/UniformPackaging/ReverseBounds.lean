module

public import NPComplete.CookLevin.UniformPackaging.OuterLoopBounds

/-!
# Layout bounds for the emit writer

The emit writer's cursor and temporary registers, and their offsets from the layout base,
must lie inside the tight outer-loop envelope for the later operand-budget arguments.
This module records that layout fact.
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

lemma uniform_emit_writer_layout_le_tight (N : ℕ) :
    uctCurJ ≤ uniformEmitTightEnvelope N ∧
      uctTmpJ ≤ uniformEmitTightEnvelope N ∧
      uniformMNat N + uctCurJ ≤ uniformEmitTightEnvelope N ∧
      uniformMNat N + uctTmpJ ≤ uniformEmitTightEnvelope N := by
  simp [uniformEmitTightEnvelope, uctCurJ, uctTmpJ]
  omega

end NPComplete.CookLevin

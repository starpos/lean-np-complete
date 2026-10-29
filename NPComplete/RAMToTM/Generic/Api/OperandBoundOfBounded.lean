module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
# `CompiledOperandBound` from a value bound

**Construction API** (not part of the stable surface; may change). A `BoundedWhileDecider`
must supply `compiled_operands_le`, a `CompiledOperandBound` for its program. This module
packages the standard way to obtain one: if every cell the program touches stays `<= B` and the
program is scan-free, then the compiled run keeps all operands within `bitLen B` bits
(`compiledOperandBound_of_programBoundedIn`). It sits above `CompileExecBounded` and
`BoundedWhileDecider` and below every concrete packaging that needs it.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits)

/-- **Construction API.** Every cell of the store `σ` is bounded by `B`. -/
@[construction_api] def StoreValuesLe (B : ℕ) (σ : Store) : Prop := ∀ i, σ i ≤ B

/-- **Construction API.** If `p` is scan-free and stays within the value bound `B` when run
    from the canonical input store `bitInputStore bits` (whose cells are themselves `<= B`),
    then its compiled form keeps every dynamic operand within `bitLen B` bits. This is the
    usual discharge of `BoundedWhileDecider.compiled_operands_le`. -/
@[construction_api] lemma compiledOperandBound_of_programBoundedIn
    (p : Program) (bits : Bits) (B : ℕ) (hB1 : 1 ≤ B)
    (hσ : StoreValuesLe B (bitInputStore bits))
    (hp : ProgramBoundedIn B (bitInputStore bits) p) (hsf : ScanFree p) :
    CompiledOperandBound p bits (bitLen B) := by
  let rr := compiledInputRAM p bits
  have hrr : RegsMemLe B rr := by
    refine ⟨?_, ?_⟩
    · intro i
      simp [rr, compiledInputRAM, emptyBank]
    · intro i
      simpa [rr, compiledInputRAM] using hσ i
  have hseg : SegmentAt rr.program rr.pc
      (compile p rr.pc 0) := by
    simpa [rr, compiledInputRAM] using
      segmentAt_self (compile p 0 0)
  obtain ⟨k, hpc, _hmem, _hfr, hprog, hb⟩ := compile_exec_bounded
    p rr.pc B hB1 rr hseg hrr hp hsf
  have hklen : (run k rr).program.length ≤ (run k rr).pc := by
    rw [hprog, hpc]
    simp [rr, compiledInputRAM, compile_length]
  have hhalt : (run k rr).current = Instruction.halt := by
    rw [current_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none hklen]
    simp
  intro k' _ j hj
  by_cases hjk : j < k
  · exact RegsMemLe.dynamic_operands_le (le_refl _) (hb j (by omega))
  · have hrun : run j rr = run k rr := by
      obtain ⟨d, hd⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
      rw [hd, run_add, run_halted _ hhalt]
    rw [hrun]
    exact RegsMemLe.dynamic_operands_le (le_refl _) (hb k le_rfl)
end NPComplete.RAMToTM

module

import NPComplete

/-!
# A downstream-style use of `compile_exec_bounded`

The statement of `compile_exec_bounded` is applied to `Program.skip` as a smoke test that the
`CompileExecBounded` API (ProgramBoundedIn, ScanFree, SegmentAt, RegsMemLe, RAM, run) elaborates
through a plain `import NPComplete`. Expected: ok.
-/

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitCostRAM

example (sb B : Nat) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile Program.skip rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem Program.skip) (hsf : ScanFree Program.skip) :
    ∃ k, (run k rr).mem = Program.eval Program.skip rr.mem :=
  let ⟨k, _, hmem, _⟩ := compile_exec_bounded Program.skip sb B hB1 rr hseg hr hp hsf
  ⟨k, hmem⟩

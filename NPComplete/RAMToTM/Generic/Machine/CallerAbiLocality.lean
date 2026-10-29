module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiMasterRam

/-!
# Locality bridge for `abiProgram`

`BoundedWhileDecider.lean`'s locality bridge (`fullProgram_pc_no_return`/`fullProgram_run_confined`/
`compiledInputRAM_full_agree`/`runDynLe_bare_to_full`) transfers a decider's `compiled_operands_le`
bound — stated against the *bare* `compiledInputRAM` — to `compiledInputFullRAM`. `abiProgram`
appends six more instructions (`abiSuffix`) after `fullProgram`'s own `outputLoad` epilogue, so the
same confinement argument needs re-establishing for `compiledInputAbiRAM`: `ram_run_to_cleanup_abi`'s
own bound (`CallerAbiMasterRam.lean`) needs `compile_exec_cost`'s `RunDynLe` hypothesis for the
main-program leg, and that hypothesis only comes from `d.compiled_operands_le` via this bridge.

Unlike `fullProgram_pc_no_return`'s hand-rolled two-step derivation, `abiProgram`'s eight-instruction
epilogue (`outputLoad ++ abiSuffix`) is handled once, generically, via `run_pc_add_of_no_jump`: every
instruction in that block is a `loadImm`/`load` (never a jump/branch), so any prefix of it just
advances `pc` by one per step — no need to hand-simulate each of the eight steps individually.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Program Expr)
open NPComplete.BitEncoding (Bits)
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits
  DynamicOperandsLe RunDynLe ProgramImmediatesLe)

/-- Every instruction in `code` is a `loadImm`/`load` (never a jump/branch): running any prefix
    of it just advances `pc` by that many steps and leaves `.program` fixed. -/
lemma run_pc_add_of_no_jump (t : RAM) (code : List Instruction)
    (hseg : SegmentAt t.program t.pc code)
    (hcode : ∀ i ∈ code,
      (∃ rd n, i = Instruction.loadImm rd n) ∨ (∃ rd rAddr, i = Instruction.load rd rAddr)) :
    ∀ j ≤ code.length, (run j t).pc = t.pc + j ∧ (run j t).program = t.program := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by simp, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨ihpc, ihprog⟩ := ih (by omega)
    have hjlt : j < code.length := by omega
    have hcur : (run j t).current = code.getD j Instruction.halt :=
      current_of_segment j hseg hjlt (run j t) ihpc ihprog
    have hcurEq : code.getD j Instruction.halt = code[j] := List.getD_eq_getElem code _ hjlt
    have hmem : code[j] ∈ code := List.getElem_mem hjlt
    rcases hcode code[j] hmem with ⟨rd, n, hi⟩ | ⟨rd, rAddr, hi⟩
    · have hc : (run j t).current = Instruction.loadImm rd n := by rw [hcur, hcurEq, hi]
      obtain ⟨_, hpc', _, hprog', _⟩ := step_loadImm (run j t) rd n hc
      refine ⟨by rw [run_succ_right, hpc', ihpc]; omega, by rw [run_succ_right, hprog', ihprog]⟩
    · have hc : (run j t).current = Instruction.load rd rAddr := by rw [hcur, hcurEq, hi]
      obtain ⟨_, hpc', _, hprog', _⟩ := step_load (run j t) rd rAddr hc
      refine ⟨by rw [run_succ_right, hpc', ihpc]; omega, by rw [run_succ_right, hprog', ihprog]⟩

/-- `outputLoad outReg ++ abiSuffix p addrCell lenCell` is built entirely from `loadImm`/`load`
    (`compileExpr`'s `.reg` case plus two literal `loadImm`s) — never a jump/branch. -/
lemma no_jump_outputLoad_append_abiSuffix (p : Program) (outReg addrCell lenCell : ℕ) :
    ∀ i ∈ (outputLoad outReg ++ abiSuffix p addrCell lenCell),
      (∃ rd n, i = Instruction.loadImm rd n) ∨ (∃ rd rAddr, i = Instruction.load rd rAddr) := by
  intro i hi
  simp only [outputLoad, abiSuffix, compileExpr, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi <;> subst hi
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩

/-- `outputLoad outReg ++ abiSuffix p outAddrCell outLenCell` occupies `abiProgram`'s tail, right
    at the `compile p 0 0`/epilogue boundary `codeLenP p`. -/
lemma segmentAt_abiProgram_outputLoad_abiSuffix (p : Program) (outReg : ℕ) :
    SegmentAt (abiProgram p outReg) (codeLenP p)
      (outputLoad outReg ++ abiSuffix p outAddrCell outLenCell) :=
  ⟨compile p 0 0, [],
    by simp [abiProgram, fullProgramAbi, fullProgram, List.append_assoc], compile_length p 0 0⟩

/-- `abiProgram`'s counterpart of `fullProgram_pc_no_return`: once an `abiProgram`-labelled RAM's
    PC reaches `codeLenP p`, it never returns there — `outputLoad`/`abiSuffix` are eight
    non-jump instructions (`no_jump_outputLoad_append_abiSuffix`), so `run_pc_add_of_no_jump` gives
    strictly increasing `pc` across them, then the run falls off `abiProgram`'s end and freezes
    strictly past the boundary. -/
lemma abiProgram_pc_no_return (p : Program) (outReg : ℕ) (t : RAM)
    (hprog : t.program = abiProgram p outReg) (hpc : t.pc = codeLenP p) :
    ∀ m, 0 < m → (run m t).pc ≠ codeLenP p := by
  have hseg : SegmentAt t.program t.pc
      (outputLoad outReg ++ abiSuffix p outAddrCell outLenCell) := by
    rw [hprog, hpc]; exact segmentAt_abiProgram_outputLoad_abiSuffix p outReg
  have hadv := run_pc_add_of_no_jump t _ hseg
    (no_jump_outputLoad_append_abiSuffix p outReg outAddrCell outLenCell)
  have h8 : (run 8 t).pc = t.pc + 8 ∧ (run 8 t).program = t.program :=
    hadv 8 (by simp [outputLoad, abiSuffix, compileExpr])
  have hcur8 : (run 8 t).current = Instruction.halt := by
    have hplen : (abiProgram p outReg).length = t.pc + 8 := by
      rw [hpc, abiProgram_length]
    rw [current_eq_getD, h8.2, hprog, h8.1]
    exact List.getD_eq_default _ _ (by omega)
  intro m hm
  rcases Nat.lt_or_ge m 8 with hlt | hge
  · have hpcm := (hadv m (by simp [outputLoad, abiSuffix, compileExpr]; omega)).1
    rw [hpcm, hpc]; omega
  · have heq : run m t = run (m - 8) (run 8 t) := by
      conv_lhs => rw [show m = 8 + (m - 8) from by omega]
      rw [run_add]
    rw [heq, run_halted _ hcur8, h8.1, hpc]
    omega

/-- Confinement for the `abiProgram`-labelled run: given any completion witness `k` (a step
    count at which the PC lands on the `compile p 0 0`/`outputLoad` boundary), every earlier
    step's PC stays strictly inside `compile p 0 0`'s segment. The proof follows the same
    confinement argument as `fullProgram_run_confined`, using `abiProgram_pc_no_return`. -/
lemma abiProgram_run_confined (p : Program) (outReg : ℕ) (R : RAM)
    (hprog : R.program = abiProgram p outReg) (hpc0 : R.pc = 0) (k : ℕ)
    (hk : (run k R).pc = codeLenP p) :
    ∀ j, j < k → (run j R).pc < codeLenP p := by
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨j0, hj0lt, hj0ge⟩ := hcon
  have hex : ∃ j, j < k ∧ codeLenP p ≤ (run j R).pc := ⟨j0, hj0lt, hj0ge⟩
  set j0' := Nat.find hex with hj0'def
  have hspec := Nat.find_spec hex
  rw [← hj0'def] at hspec
  obtain ⟨hj0'lt, hj0'ge⟩ := hspec
  have hrunprog : ∀ i, (run i R).program = abiProgram p outReg := by
    intro i; rw [run_program, hprog]
  rcases Nat.eq_zero_or_pos j0' with hz | hpos
  · have hpceq : R.pc = codeLenP p := by
      have := hj0'ge; rw [hz, run_zero, hpc0] at this; omega
    exact (abiProgram_pc_no_return p outReg R hprog hpceq k (by omega)) hk
  · have hmin : ¬ (j0' - 1 < k ∧ codeLenP p ≤ (run (j0' - 1) R).pc) :=
      Nat.find_min hex (by omega)
    have hlt' : (run (j0' - 1) R).pc < codeLenP p := by
      by_contra h; exact hmin ⟨by omega, by omega⟩
    have hseg : SegmentAt (run (j0' - 1) R).program 0 (compile p 0 0) := by
      rw [hrunprog]; exact segmentAt_abiProgram_compile p outReg
    have hstep := step_confined (s := run (j0' - 1) R) (start := 0) (len := codeLenP p)
      (code := compile p 0 0) hseg (compile_length p 0 0) (compile_targets_in p 0 0)
      (by omega) (by omega)
    have hj0eq : (run j0' R).pc = codeLenP p := by
      have hstepeq : step (run (j0' - 1) R) = run j0' R := by
        have hsr : run (j0' - 1 + 1) R = step (run (j0' - 1) R) := run_succ_right (j0' - 1) R
        rw [show j0' - 1 + 1 = j0' from by omega] at hsr
        exact hsr.symm
      rw [hstepeq] at hstep
      omega
    have hnr := abiProgram_pc_no_return p outReg (run j0' R) (hrunprog j0') hj0eq
      (k - j0') (by omega)
    apply hnr
    have heq : run (k - j0') (run j0' R) = run k R := by
      rw [← run_add]
      congr 1
      omega
    rw [heq, hk]

/-- State-agreement: `compiledInputRAM` (bare) and `compiledInputAbiRAM` (ABI) start with
    identical `regs`/`mem`/`pc`/`cost` and differ only in `.program`. Given an ABI-run completion
    witness `k`, `abiProgram_run_confined` keeps `abi`'s PC strictly inside the shared
    `compile p 0 0` prefix for every `j < k`, so both runs read the same `.current` there and
    `step_congr` propagates agreement one step at a time. Mirrors
    `compiledInputRAM_full_agree`. -/
lemma compiledInputRAM_abi_agree (p : Program) (outReg : ℕ) (bits : Bits) (k : ℕ)
    (hk : (run k (compiledInputAbiRAM p outReg bits)).pc = codeLenP p) :
    ∀ j, j ≤ k →
      (run j (compiledInputRAM p bits)).regs = (run j (compiledInputAbiRAM p outReg bits)).regs ∧
      (run j (compiledInputRAM p bits)).mem = (run j (compiledInputAbiRAM p outReg bits)).mem ∧
      (run j (compiledInputRAM p bits)).pc = (run j (compiledInputAbiRAM p outReg bits)).pc ∧
      (run j (compiledInputRAM p bits)).cost = (run j (compiledInputAbiRAM p outReg bits)).cost := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl, rfl, rfl⟩
  | succ j ih =>
      intro hjk
      obtain ⟨hr, hm, hp, hco⟩ := ih (by omega)
      have hconf := abiProgram_run_confined p outReg (compiledInputAbiRAM p outReg bits)
        rfl rfl k hk j (by omega)
      have hpb : (run j (compiledInputRAM p bits)).pc < codeLenP p := by rw [hp]; exact hconf
      have hsegB : SegmentAt (run j (compiledInputRAM p bits)).program 0 (compile p 0 0) := by
        rw [run_program]; exact segmentAt_self (compile p 0 0)
      have hsegF : SegmentAt (run j (compiledInputAbiRAM p outReg bits)).program 0
          (compile p 0 0) := by
        rw [run_program]; exact segmentAt_abiProgram_compile p outReg
      have hcurB : (run j (compiledInputRAM p bits)).current =
          (compile p 0 0).getD (run j (compiledInputRAM p bits)).pc Instruction.halt := by
        rw [current_eq_getD]
        have := segment_getD hsegB (by rw [compile_length]; exact hpb)
        rwa [show (0:ℕ) + (run j (compiledInputRAM p bits)).pc
          = (run j (compiledInputRAM p bits)).pc from by omega] at this
      have hcurF : (run j (compiledInputAbiRAM p outReg bits)).current =
          (compile p 0 0).getD (run j (compiledInputAbiRAM p outReg bits)).pc Instruction.halt := by
        rw [current_eq_getD]
        have := segment_getD hsegF (by rw [compile_length]; exact hconf)
        rwa [show (0:ℕ) + (run j (compiledInputAbiRAM p outReg bits)).pc
          = (run j (compiledInputAbiRAM p outReg bits)).pc from by omega] at this
      have hcur : (run j (compiledInputRAM p bits)).current =
          (run j (compiledInputAbiRAM p outReg bits)).current := by
        rw [hcurB, hcurF, hp]
      obtain ⟨hr', hm', hp', hco'⟩ := step_congr hcur hr hm hp hco
      rw [run_succ_right, run_succ_right]
      exact ⟨hr', hm', hp', hco'⟩

/-- Bare and ABI agree on `.current` too at every step *before* completion (`j < k`) — the same
    segment argument `compiledInputRAM_abi_agree`'s inductive step uses, exposed standalone for
    `RunDynLe`'s per-step predicate. Mirrors `compiledInputRAM_full_current_agree`. -/
lemma compiledInputRAM_abi_current_agree (p : Program) (outReg : ℕ) (bits : Bits) (k j : ℕ)
    (hk : (run k (compiledInputAbiRAM p outReg bits)).pc = codeLenP p) (hj : j < k) :
    (run j (compiledInputRAM p bits)).current =
      (run j (compiledInputAbiRAM p outReg bits)).current := by
  obtain ⟨hr, hm, hp, hco⟩ := compiledInputRAM_abi_agree p outReg bits k hk j (by omega)
  have hconf := abiProgram_run_confined p outReg (compiledInputAbiRAM p outReg bits)
    rfl rfl k hk j hj
  have hpb : (run j (compiledInputRAM p bits)).pc < codeLenP p := by rw [hp]; exact hconf
  have hsegB : SegmentAt (run j (compiledInputRAM p bits)).program 0 (compile p 0 0) := by
    rw [run_program]; exact segmentAt_self (compile p 0 0)
  have hsegF : SegmentAt (run j (compiledInputAbiRAM p outReg bits)).program 0
      (compile p 0 0) := by
    rw [run_program]; exact segmentAt_abiProgram_compile p outReg
  have hcurB : (run j (compiledInputRAM p bits)).current =
      (compile p 0 0).getD (run j (compiledInputRAM p bits)).pc Instruction.halt := by
    rw [current_eq_getD]
    have := segment_getD hsegB (by rw [compile_length]; exact hpb)
    rwa [show (0:ℕ) + (run j (compiledInputRAM p bits)).pc
      = (run j (compiledInputRAM p bits)).pc from by omega] at this
  have hcurF : (run j (compiledInputAbiRAM p outReg bits)).current =
      (compile p 0 0).getD (run j (compiledInputAbiRAM p outReg bits)).pc Instruction.halt := by
    rw [current_eq_getD]
    have := segment_getD hsegF (by rw [compile_length]; exact hconf)
    rwa [show (0:ℕ) + (run j (compiledInputAbiRAM p outReg bits)).pc
      = (run j (compiledInputAbiRAM p outReg bits)).pc from by omega] at this
  rw [hcurB, hcurF, hp]

/-- The `RunDynLe` bridge: `compiled_operands_le`'s bare bound transfers to `compiledInputAbiRAM`,
    for any `k` at which the ABI run's own `compile_exec` completes. Mirrors
    `runDynLe_bare_to_full`. -/
lemma runDynLe_bare_to_abi (p : Program) (outReg : ℕ) (bits : Bits) (W k : ℕ)
    (hk : (run k (compiledInputAbiRAM p outReg bits)).pc = codeLenP p)
    (hbare : RunDynLe W k (compiledInputRAM p bits)) :
    RunDynLe W k (compiledInputAbiRAM p outReg bits) := by
  intro j hj
  obtain ⟨hr, hm, _, _⟩ := compiledInputRAM_abi_agree p outReg bits k hk j (by omega)
  have hcur := compiledInputRAM_abi_current_agree p outReg bits k j hk hj
  have hbareDyn := hbare j hj
  unfold DynamicOperandsLe at hbareDyn ⊢
  rw [← hcur, ← hr, ← hm]
  exact hbareDyn

/-- `abiProgram`'s `loadImm` immediates are bounded by the largest of `compile p 0 0`'s own
    bound, `outputLoad`'s (`bitLen outReg`), and `abiSuffix`'s (`outAddrCell`/`outLenCell`/`1`) —
    the `I` `compile_exec_cost` needs when run against `compiledInputAbiRAM`. -/
lemma programImmediatesLe_abiProgram (p : Program) (outReg : ℕ) :
    ProgramImmediatesLe
      (max (programImmBound p) (max (bitLen outReg)
        (max (bitLen outAddrCell) (max (bitLen outLenCell) 1))))
      (abiProgram p outReg) := by
  show ProgramImmediatesLe _ (fullProgram p outReg ++ abiSuffix p outAddrCell outLenCell)
  refine ProgramImmediatesLe.append ?_ ?_
  · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_fullProgram p outReg)
  · exact ProgramImmediatesLe.mono (by omega)
      (programImmediatesLe_abiSuffix p outAddrCell outLenCell)

end NPComplete.RAMToTM.Generic

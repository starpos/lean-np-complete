module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BitCostRAM
public import NPComplete.BoundedWhile.Basic

/-!
# Semantics-preserving refinement from bounded-WHILE to BitCostRAM

To preserve the bounded-WHILE store semantics, this refinement maps every DSL `Store` cell `i` to
`RAM.mem i` and reserves `RAM.regs` for temporary values used during compilation. The two banks
therefore have disjoint roles, while direct and indirect DSL accesses refer to the same store.

The calling convention `dst < sb` keeps an expression's result register below the scratch base.
The refinement statements specify execution, memory placement, and register-frame behavior; the
bit-cost obligations remain separate from semantic correctness.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile (Expr Program writeReg findVal
  eval_skip eval_assign eval_assignInd eval_seq eval_ifNZ eval_forN eval_scanList eval_lookup
  scanListEval loopEval scanListCost loopCost writeReg_same writeReg_diff
  scanListEval_nil scanListEval_cons loopEval_zero loopEval_succ findVal_nil findVal_cons
  loopCost_zero loopCost_succ scanListCost_nil scanListCost_cons
  cost_skip cost_assign cost_assignInd cost_seq cost_ifNZ cost_forN cost_scanList cost_lookup)

/-- Mem-unified expression lowering.  `compileExpr e dst sb` evaluates `e`
    against the RAM `mem` bank and leaves the result in register `dst`, using
    `regs sb, sb+1, …` as scratch.  Calling convention: `dst < sb`.

    * `reg r` loads `mem r` (address `r` staged in `sb`, then `load`).
    * `regInd e` computes the address into `dst`, then dereferences via `mem`.
    * binary nodes place the two operands in `sb` / `sb+1`, recursing with
      scratch base `sb+2` so the left operand survives the right's evaluation. -/
def compileExpr : Expr → ℕ → ℕ → List Instruction
  | .const n, dst, _   => [Instruction.loadImm dst n]
  | .reg r, dst, sb    => [Instruction.loadImm sb r, Instruction.load dst sb]
  | .regInd e, dst, sb => compileExpr e dst sb ++ [Instruction.load dst dst]
  | .add e1 e2, dst, sb =>
      compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++
        [Instruction.add dst sb (sb + 1)]
  | .sub e1 e2, dst, sb =>
      compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++
        [Instruction.sub dst sb (sb + 1)]
  | .mul e1 e2, dst, sb =>
      compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++
        [Instruction.mul dst sb (sb + 1)]
  | .lt e1 e2, dst, sb =>
      compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++
        [Instruction.setIfLt dst sb (sb + 1)]
  | .eq e1 e2, dst, sb =>
      compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++
        [Instruction.setIfEq dst sb (sb + 1)]

/-- Absolute-PC code placement: `code` occupies `program` starting at PC `pc`.
    The RAM uses absolute jump targets, so semantic statements must fix where the
    compiled block sits rather than speak of `compile` in isolation. -/
def SegmentAt (program : List Instruction) (pc : ℕ) (code : List Instruction) : Prop :=
  ∃ pre suf : List Instruction, program = pre ++ code ++ suf ∧ pre.length = pc

/-- A program is trivially its own (only) segment at PC `0` — the shape `compiledInputRAM`
    feeds `compile_exec`/`compile_exec_cost` (the whole compiled program, no frame). -/
lemma segmentAt_self (program : List Instruction) : SegmentAt program 0 program :=
  ⟨[], [], by simp, rfl⟩

/-- Running the sum of two step counts factors through the intermediate state. -/
lemma run_add (a b : ℕ) (r : RAM) : run (a + b) r = run b (run a r) := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h, run_succ, ih, run_succ]

/-- The instruction a machine sees when its PC points `i` steps into a segment. -/
lemma current_of_segment {r : RAM} {code : List Instruction} (i : ℕ)
    (hseg : SegmentAt r.program r.pc code) (hi : i < code.length)
    (r' : RAM) (hpc : r'.pc = r.pc + i) (hprog : r'.program = r.program) :
    r'.current = code.getD i Instruction.halt := by
  obtain ⟨pre, suf, hp, hl⟩ := hseg
  unfold RAM.current
  rw [hprog, hpc, ← hl, hp, List.append_assoc,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

/-- `RAM.current` reads the program entry at the PC.  A rfl-lemma exposing this so
    fixed-PC instruction lookups can be phrased with an explicit PC rather than a
    RAM's `.pc` field (needed when the placement PC is a literal offset). -/
lemma current_eq_getD (r : RAM) : r.current = r.program.getD r.pc Instruction.halt := rfl

/-- The program entry at `pc + i` equals the segment's `i`-th instruction.  Same
    content as `current_of_segment` but phrased with an explicit placement PC. -/
lemma segment_getD {program code : List Instruction} {pc i : ℕ}
    (hseg : SegmentAt program pc code) (hi : i < code.length) :
    program.getD (pc + i) Instruction.halt = code.getD i Instruction.halt := by
  obtain ⟨pre, suf, hp, hl⟩ := hseg
  rw [hp, ← hl, List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

/-- A segment placed at `pc` starts with any code prefix, also placed at `pc`. -/
lemma SegmentAt.append_left {program : List Instruction} {pc : ℕ} {c1 c2 : List Instruction}
    (h : SegmentAt program pc (c1 ++ c2)) : SegmentAt program pc c1 := by
  obtain ⟨pre, suf, hp, hl⟩ := h
  exact ⟨pre, c2 ++ suf, by rw [hp]; simp [List.append_assoc], hl⟩

/-- The second half of a segment sits at `pc` shifted by the first half's length. -/
lemma SegmentAt.append_right {program : List Instruction} {pc : ℕ} {c1 c2 : List Instruction}
    (h : SegmentAt program pc (c1 ++ c2)) : SegmentAt program (pc + c1.length) c2 := by
  obtain ⟨pre, suf, hp, hl⟩ := h
  exact ⟨pre ++ c1, suf, by rw [hp]; simp [List.append_assoc], by rw [List.length_append, hl]⟩

/-- Binary-node composition: given execution certificates for two operand blocks
    `c1` (result in `sb`) and `c2` (result in `sb+1`), and the effect of the
    final binary instruction `opI`, the block `c1 ++ c2 ++ [opI]` leaves
    `g v1 v2` in `dst`, preserves memory / program, and frames registers below
    `sb` (except `dst`).  The operand frames use bound `sb+2`, the scratch base
    of the recursive calls, so the two intermediate results survive each other. -/
lemma exec_bin (c1 c2 : List Instruction) (opI : Instruction) (dst sb : ℕ)
    (r : RAM) (v1 v2 : ℕ) (g : ℕ → ℕ → ℕ) (b1 b2 : ℕ)
    (hseg : SegmentAt r.program r.pc (c1 ++ c2 ++ [opI]))
    (h1 : ∃ k, (run k r).pc = r.pc + c1.length ∧ (run k r).regs sb = v1 ∧
        (run k r).mem = r.mem ∧ (∀ x, x < sb + 2 → x ≠ sb → (run k r).regs x = r.regs x) ∧
        (run k r).program = r.program ∧ k ≤ b1)
    (h2 : ∀ r1 : RAM, r1.mem = r.mem → SegmentAt r1.program r1.pc c2 →
        ∃ k, (run k r1).pc = r1.pc + c2.length ∧ (run k r1).regs (sb + 1) = v2 ∧
        (run k r1).mem = r1.mem ∧ (∀ x, x < sb + 2 → x ≠ sb + 1 → (run k r1).regs x = r1.regs x) ∧
        (run k r1).program = r1.program ∧ k ≤ b2)
    (hop : ∀ rr : RAM, rr.current = opI →
        (step rr).regs dst = g (rr.regs sb) (rr.regs (sb + 1)) ∧
        (step rr).pc = rr.pc + 1 ∧ (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
        ∀ y, y ≠ dst → (step rr).regs y = rr.regs y) :
    ∃ k, (run k r).pc = r.pc + (c1 ++ c2 ++ [opI]).length ∧ (run k r).regs dst = g v1 v2 ∧
        (run k r).mem = r.mem ∧ (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
        (run k r).program = r.program ∧ k ≤ b1 + b2 + 1 := by
  obtain ⟨k1, hpc1, hrsb1, hmem1, hfr1, hprog1, hk1⟩ := h1
  rw [List.append_assoc] at hseg
  have segc2 : SegmentAt r.program (r.pc + c1.length) c2 := hseg.append_right.append_left
  have segop : SegmentAt r.program (r.pc + c1.length + c2.length) [opI] :=
    hseg.append_right.append_right
  have segc2' : SegmentAt (run k1 r).program (run k1 r).pc c2 := by rw [hprog1, hpc1]; exact segc2
  obtain ⟨k2, hpc2, hrsb2, hmem2, hfr2, hprog2, hk2⟩ := h2 (run k1 r) hmem1 segc2'
  have hr2pc : (run k2 (run k1 r)).pc = r.pc + c1.length + c2.length := by rw [hpc2, hpc1]
  have hr2prog : (run k2 (run k1 r)).program = r.program := by rw [hprog2, hprog1]
  have hcurop : (run k2 (run k1 r)).current = opI := by
    have hs : SegmentAt (run k2 (run k1 r)).program (run k2 (run k1 r)).pc [opI] := by
      rw [hr2prog, hr2pc]; exact segop
    have := current_of_segment 0 hs (by simp) (run k2 (run k1 r)) rfl rfl; simpa using this
  obtain ⟨hopr, hoppc, hopmem, hopprog, hopfr⟩ := hop (run k2 (run k1 r)) hcurop
  have hrun : run (k1 + k2 + 1) r = step (run k2 (run k1 r)) := by
    rw [show k1 + k2 + 1 = k1 + (k2 + 1) by omega, run_add, run_add]; rfl
  refine ⟨k1 + k2 + 1, ?_, ?_, ?_, ?_, ?_, by omega⟩ <;> rw [hrun]
  · rw [hoppc, hr2pc]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [hopr, hfr2 sb (by omega) (by omega), hrsb1, hrsb2]
  · rw [hopmem, hmem2, hmem1]
  · intro x hx hxd
    rw [hopfr x hxd, hfr2 x (by omega) (by omega), hfr1 x (by omega) (by omega)]
  · rw [hopprog, hr2prog]

/-- Single-step effect of a `loadImm rd n`: `rd` gets `n`, the PC advances, memory
    and program are untouched, and every other register is framed. -/
lemma step_loadImm (rr : RAM) (rd n : ℕ) (hc : rr.current = Instruction.loadImm rd n) :
    (step rr).regs rd = n ∧ (step rr).pc = rr.pc + 1 ∧ (step rr).mem = rr.mem ∧
    (step rr).program = rr.program ∧ ∀ y, y ≠ rd → (step rr).regs y = rr.regs y := by
  refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp only [step, hc]; exact bankWrite_same _ _ _
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy

/-- Single-step effect of a `load rd rAddr`: `rd` gets `mem (regs rAddr)`, the PC
    advances, memory and program are untouched, and other registers are framed. -/
lemma step_load (rr : RAM) (rd rAddr : ℕ) (hc : rr.current = Instruction.load rd rAddr) :
    (step rr).regs rd = rr.mem (rr.regs rAddr) ∧ (step rr).pc = rr.pc + 1 ∧
    (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
    ∀ y, y ≠ rd → (step rr).regs y = rr.regs y := by
  refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp only [step, hc]; exact bankWrite_same _ _ _
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy


/-- Induction-hypothesis shape of `compileExpr_exec`: its execution contract for every valid
    destination, scratch base and start state. -/
def CompileExprExecGoal (e : Expr) : Prop :=
  ∀ dst sb : ℕ, dst < sb → ∀ r : RAM,
    SegmentAt r.program r.pc (compileExpr e dst sb) →
    ∃ k : ℕ,
      (run k r).pc = r.pc + (compileExpr e dst sb).length ∧
      (run k r).regs dst = e.eval r.mem ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      k ≤ 2 * e.cost

/-- `compileExpr_exec` for a constant: one `loadImm` instruction realizes its value. -/
lemma compileExpr_exec_const (n dst sb : ℕ) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.const n) dst sb)) :
    ∃ k : ℕ,
      (run k r).pc = r.pc + (compileExpr (Expr.const n) dst sb).length ∧
      (run k r).regs dst = (Expr.const n).eval r.mem ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧ k ≤ 2 * (Expr.const n).cost := by
  simp only [compileExpr, Expr.eval] at hseg ⊢
  have hcur : r.current = Instruction.loadImm dst n := by
    have := current_of_segment 0 hseg (by simp) r rfl rfl
    simpa using this
  obtain ⟨hr, hp, hm, hpr, hf⟩ := step_loadImm r dst n hcur
  refine ⟨1, ?_, ?_, ?_, ?_, ?_, by simp only [Expr.cost]; omega⟩ <;>
    rw [show run 1 r = step r from rfl]
  · rw [hp]; simp
  · rw [hr]
  · rw [hm]
  · intro x hx hxd; exact hf x hxd
  · rw [hpr]

/-- `compileExpr_exec` for a register: stage its address before loading its contents. -/
lemma compileExpr_exec_reg (r0 dst sb : ℕ) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.reg r0) dst sb)) :
    ∃ k : ℕ,
      (run k r).pc = r.pc + (compileExpr (Expr.reg r0) dst sb).length ∧
      (run k r).regs dst = (Expr.reg r0).eval r.mem ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧ k ≤ 2 * (Expr.reg r0).cost := by
  simp only [compileExpr, Expr.eval] at hseg ⊢
  have hcur0 : r.current = Instruction.loadImm sb r0 := by
    have := current_of_segment 0 hseg (by simp) r rfl rfl
    simpa using this
  obtain ⟨e0regs, e0pc, e0mem, e0prog, e0fr⟩ := step_loadImm r sb r0 hcur0
  have hcur1 : (step r).current = Instruction.load dst sb := by
    have := current_of_segment 1 hseg (by simp) (step r) e0pc e0prog
    simpa using this
  obtain ⟨e1regs, e1pc, e1mem, e1prog, e1fr⟩ := step_load (step r) dst sb hcur1
  refine ⟨2, ?_, ?_, ?_, ?_, ?_, by simp only [Expr.cost]; omega⟩ <;>
    rw [show run 2 r = step (step r) from by rw [show (2 : ℕ) = 1 + 1 from rfl, run_add]; rfl]
  · rw [e1pc, e0pc]; simp
  · rw [e1regs, e0mem, e0regs]
  · rw [e1mem, e0mem]
  · intro x hx hxd; rw [e1fr x hxd, e0fr x (by omega)]
  · rw [e1prog, e0prog]

/-- `compileExpr_exec` for an indirect register: evaluate the address, then dereference it. -/
lemma compileExpr_exec_regInd (e : Expr) (dst sb : ℕ) (hconv : dst < sb)
    (ih : CompileExprExecGoal e) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.regInd e) dst sb)) :
    ∃ k : ℕ,
      (run k r).pc = r.pc + (compileExpr (Expr.regInd e) dst sb).length ∧
      (run k r).regs dst = (Expr.regInd e).eval r.mem ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧ k ≤ 2 * (Expr.regInd e).cost := by
  simp only [compileExpr, Expr.eval] at hseg ⊢
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hk1⟩ :=
    ih dst sb hconv r hseg.append_left
  have hcurop : (run k1 r).current = Instruction.load dst dst := by
    have hs : SegmentAt (run k1 r).program (run k1 r).pc [Instruction.load dst dst] := by
      rw [hprog1, hpc1]; exact hseg.append_right
    have := current_of_segment 0 hs (by simp) (run k1 r) rfl rfl
    simpa using this
  obtain ⟨eR, eP, eM, ePr, eF⟩ := step_load (run k1 r) dst dst hcurop
  refine ⟨k1 + 1, ?_, ?_, ?_, ?_, ?_, by simp only [Expr.cost]; omega⟩ <;>
    rw [show run (k1 + 1) r = step (run k1 r) from by rw [run_add]; rfl]
  · rw [eP, hpc1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · rw [eR, hmem1, hrd1]
  · rw [eM, hmem1]
  · intro x hx hxd; rw [eF x hxd, hfr1 x hx hxd]
  · rw [ePr, hprog1]

/-- Binary expression nodes compose operand executions with their final instruction. -/
lemma compileExpr_exec_bin (e1 e2 : Expr) (opI : Instruction) (g : ℕ → ℕ → ℕ)
    (dst sb : ℕ) (r : RAM)
    (ih1 : CompileExprExecGoal e1) (ih2 : CompileExprExecGoal e2)
    (hseg : SegmentAt r.program r.pc
      (compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++ [opI]))
    (hop : ∀ rr : RAM, rr.current = opI →
        (step rr).regs dst = g (rr.regs sb) (rr.regs (sb + 1)) ∧
        (step rr).pc = rr.pc + 1 ∧ (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
        ∀ y, y ≠ dst → (step rr).regs y = rr.regs y) :
    ∃ k,
      (run k r).pc = r.pc +
        (compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++ [opI]).length ∧
      (run k r).regs dst = g (e1.eval r.mem) (e2.eval r.mem) ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧ k ≤ 2 * e1.cost + 2 * e2.cost + 1 := by
  exact exec_bin _ _ opI dst sb r (e1.eval r.mem) (e2.eval r.mem) g
    (2 * e1.cost) (2 * e2.cost) hseg
    (ih1 sb (sb + 2) (by omega) r hseg.append_left.append_left)
    (fun r1 hm hs => by
      obtain ⟨k, a, b, c, d, ee, hk⟩ := ih2 (sb + 1) (sb + 2) (by omega) r1 hs
      exact ⟨k, a, by rw [b, hm], c, d, ee, hk⟩)
    hop

/-- Expression execution certificate: running the compiled block advances the PC
    past it, leaves `e.eval mem` in `dst`, keeps `mem` and `program` unchanged
    (expression evaluation is memory-pure), and preserves every register below
    `sb` other than `dst` (the register frame).  Bit-cost is stated separately. -/
lemma compileExpr_exec (e : Expr) (dst sb : ℕ) (hconv : dst < sb)
    (r : RAM) (hseg : SegmentAt r.program r.pc (compileExpr e dst sb)) :
    ∃ k : ℕ,
      (run k r).pc = r.pc + (compileExpr e dst sb).length ∧
      (run k r).regs dst = e.eval r.mem ∧
      (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      k ≤ 2 * e.cost := by
  induction e generalizing dst sb r with
  | const n => exact compileExpr_exec_const n dst sb r hseg
  | reg r0 => exact compileExpr_exec_reg r0 dst sb r hseg
  | regInd e ih => exact compileExpr_exec_regInd e dst sb hconv ih r hseg
  | add e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval] at hseg ⊢
    obtain ⟨k, a, b, c, d, ee, hk⟩ :=
      compileExpr_exec_bin e1 e2 _ (· + ·) dst sb r ih1 ih2 hseg
        (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
          by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
    exact ⟨k, a, b, c, d, ee, by simp only [Expr.cost]; omega⟩
  | sub e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval] at hseg ⊢
    obtain ⟨k, a, b, c, d, ee, hk⟩ :=
      compileExpr_exec_bin e1 e2 _ (· - ·) dst sb r ih1 ih2 hseg
        (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
          by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
    exact ⟨k, a, b, c, d, ee, by simp only [Expr.cost]; omega⟩
  | mul e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval] at hseg ⊢
    obtain ⟨k, a, b, c, d, ee, hk⟩ :=
      compileExpr_exec_bin e1 e2 _ (· * ·) dst sb r ih1 ih2 hseg
        (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
          by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
    exact ⟨k, a, b, c, d, ee, by simp only [Expr.cost]; omega⟩
  | lt e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval] at hseg ⊢
    obtain ⟨k, a, b, c, d, ee, hk⟩ :=
      compileExpr_exec_bin e1 e2 _ (fun a b => if a < b then 1 else 0) dst sb r ih1 ih2 hseg
        (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
          by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
    exact ⟨k, a, b, c, d, ee, by simp only [Expr.cost]; omega⟩
  | eq e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval] at hseg ⊢
    obtain ⟨k, a, b, c, d, ee, hk⟩ :=
      compileExpr_exec_bin e1 e2 _ (fun a b => if a = b then 1 else 0) dst sb r ih1 ih2 hseg
        (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
          by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
    exact ⟨k, a, b, c, d, ee, by simp only [Expr.cost]; omega⟩

/-! ## Program lowering (mem-unified)

`compile p pc sb` lowers a `Program` to a flat instruction list placed at
absolute PC `pc`, with `regs sb, sb+1, …` as scratch.  Every DSL `Store` cell
`i` lives in `RAM.mem i`, so `assign`/`assignInd` end in a `store` and
`scanList`'s binder is a `store` into `mem` — nothing writes the DSL state into
`regs`.  Control flow (`ifNZ`, `forN`) resolves jump targets to absolute PCs via
`codeLenE`/`codeLenP`, which match the compiled lengths exactly (`compile_length`),
so the target arithmetic is sound.  `scanList`/`lookup` unroll their meta-level
lists (one `compile body` per element / five instructions per pair).

`lookup` reads its key from `mem` once into a register, keeps the running result
in a register, walks the pairs in reverse so the first matching entry's write
wins, and stores the result to `mem` once at the end — the alias discipline that
a naive per-iteration `mem` re-read would violate. -/

/-- Compiled length of `compileExpr e dst sb`: one instruction per `Expr` node,
    with `reg`/`regInd` charging the extra `load`.  Independent of `dst`/`sb`,
    so jump-target arithmetic can be phrased structurally. -/
def codeLenE : Expr → ℕ
  | .const _ => 1
  | .reg _ => 2
  | .regInd e => codeLenE e + 1
  | .add e1 e2 => codeLenE e1 + codeLenE e2 + 1
  | .sub e1 e2 => codeLenE e1 + codeLenE e2 + 1
  | .mul e1 e2 => codeLenE e1 + codeLenE e2 + 1
  | .lt e1 e2 => codeLenE e1 + codeLenE e2 + 1
  | .eq e1 e2 => codeLenE e1 + codeLenE e2 + 1

/-- Compiled length of `compile p pc sb`: matches `(compile p pc sb).length`
    (via `compile_length`) so the `ifNZ`/`forN` jump targets are exact. -/
def codeLenP : Program → ℕ
  | .skip => 0
  | .assign _ e => codeLenE e + 2
  | .assignInd eA eV => codeLenE eA + codeLenE eV + 1
  | .seq p1 p2 => codeLenP p1 + codeLenP p2
  | .ifNZ e t f => codeLenE e + codeLenP t + codeLenP f + 2
  | .forN n body => codeLenE n + codeLenP body + 6
  | .scanList xs _ body => xs.length * (3 + codeLenP body)
  | .lookup pairs _ _ => 5 + 5 * pairs.length

/-- Exact length identity for `compileExpr`. -/
lemma compileExpr_length (e : Expr) (dst sb : ℕ) :
    (compileExpr e dst sb).length = codeLenE e := by
  induction e generalizing dst sb with
  | const _ => simp [compileExpr, codeLenE]
  | reg _ => simp [compileExpr, codeLenE]
  | regInd e ih =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h := ih dst sb; omega
  | add e1 e2 ih1 ih2 =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h1 := ih1 sb (sb+2); have h2 := ih2 (sb+1) (sb+2); omega
  | sub e1 e2 ih1 ih2 =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h1 := ih1 sb (sb+2); have h2 := ih2 (sb+1) (sb+2); omega
  | mul e1 e2 ih1 ih2 =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h1 := ih1 sb (sb+2); have h2 := ih2 (sb+1) (sb+2); omega
  | lt e1 e2 ih1 ih2 =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h1 := ih1 sb (sb+2); have h2 := ih2 (sb+1) (sb+2); omega
  | eq e1 e2 ih1 ih2 =>
      simp only [compileExpr, List.length_append, List.length_cons, List.length_nil, codeLenE]
      have h1 := ih1 sb (sb+2); have h2 := ih2 (sb+1) (sb+2); omega

/-- Compile the iterations of `lookup pairs kReg vReg`.  The caller passes the
    key register (holding `mem kReg`) and the result register, and hands over
    `pairs.reverse` so a later (earlier-in-`pairs`) match's `loadImm` into the
    result register wins, matching `findVal`'s first-match semantics.  Each pair
    emits five instructions using scratch `sb+3` (literal key) / `sb+4` (compare
    flag).  Recurses only on the pair list, so it lives outside the mutual block. -/
def compileLookupIters : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → List Instruction
  | [], _, _, _, _ => []
  | (k, v) :: rest, keyReg, resReg, sb, pc =>
      [Instruction.loadImm (sb + 3) k, Instruction.setIfEq (sb + 4) keyReg (sb + 3),
       Instruction.branchIfNZ (sb + 4) (pc + 4), Instruction.jump (pc + 5),
       Instruction.loadImm resReg v] ++
      compileLookupIters rest keyReg resReg sb (pc + 5)

mutual
  /-- Lower a `Program` to RAM code at absolute PC `pc` with scratch base `sb`. -/
  def compile : Program → ℕ → ℕ → List Instruction
    | .skip, _, _ => []
    | .assign r e, _, sb =>
        compileExpr e sb (sb + 1) ++
          [Instruction.loadImm (sb + 1) r, Instruction.store sb (sb + 1)]
    | .assignInd eA eV, _, sb =>
        compileExpr eA sb (sb + 2) ++ compileExpr eV (sb + 1) (sb + 2) ++
          [Instruction.store (sb + 1) sb]
    | .seq p1 p2, pc, sb =>
        compile p1 pc sb ++ compile p2 (pc + codeLenP p1) sb
    | .ifNZ e t f, pc, sb =>
        compileExpr e sb (sb + 1) ++
          [Instruction.branchIfNZ sb (pc + codeLenE e + codeLenP f + 2)] ++
          compile f (pc + codeLenE e + 1) (sb + 1) ++
          [Instruction.jump (pc + codeLenE e + codeLenP f + codeLenP t + 2)] ++
          compile t (pc + codeLenE e + codeLenP f + 2) (sb + 1)
    | .forN n body, pc, sb =>
        compileExpr n (sb + 1) (sb + 3) ++
          [Instruction.loadImm sb 0, Instruction.loadImm (sb + 2) 1] ++
          ([Instruction.branchIfLt sb (sb + 1) (pc + codeLenE n + 4),
            Instruction.jump (pc + codeLenE n + codeLenP body + 6)] ++
           compile body (pc + codeLenE n + 4) (sb + 3) ++
           [Instruction.add sb sb (sb + 2), Instruction.jump (pc + codeLenE n + 2)])
    | .scanList xs r body, pc, sb => compileScanList xs r body pc sb
    | .lookup pairs kReg vReg, pc, sb =>
        [Instruction.loadImm sb kReg, Instruction.load (sb + 1) sb,
         Instruction.loadImm (sb + 2) 0] ++
          compileLookupIters pairs.reverse (sb + 1) (sb + 2) sb (pc + 3) ++
          [Instruction.loadImm sb vReg, Instruction.store (sb + 2) sb]

  /-- Unroll `scanList xs r body`: each element writes `mem r ← x` (three
      instructions) then runs the compiled body.  Recurses jointly with
      `compile` on the fixed `body` subterm. -/
  def compileScanList : List ℕ → ℕ → Program → ℕ → ℕ → List Instruction
    | [], _, _, _, _ => []
    | x :: xs, r, body, pc, sb =>
        [Instruction.loadImm sb r, Instruction.loadImm (sb + 1) x,
         Instruction.store (sb + 1) sb] ++
          compile body (pc + 3) (sb + 2) ++
          compileScanList xs r body (pc + 3 + codeLenP body) sb
end

/-- `compileLookupIters` emits exactly `5 * pairs.length` instructions. -/
lemma compileLookupIters_length (pairs : List (ℕ × ℕ)) (keyReg resReg sb pc : ℕ) :
    (compileLookupIters pairs keyReg resReg sb pc).length = 5 * pairs.length := by
  induction pairs generalizing pc with
  | nil => simp [compileLookupIters]
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      simp only [compileLookupIters, List.length_append, List.length_cons, List.length_nil]
      rw [ih (pc + 5)]; omega

/-- Exact length identity for `compile`: the compiled code has `codeLenP p`
    instructions, matching the offsets used for `ifNZ`/`forN` jump targets. -/
lemma compile_length (p : Program) (pc sb : ℕ) :
    (compile p pc sb).length = codeLenP p := by
  induction p generalizing pc sb with
  | skip => simp [compile, codeLenP]
  | assign r e =>
      simp only [compile, codeLenP, List.length_append, List.length_cons, List.length_nil]
      rw [compileExpr_length]
  | assignInd eA eV =>
      simp only [compile, codeLenP, List.length_append, List.length_cons, List.length_nil]
      rw [compileExpr_length, compileExpr_length]
  | seq p1 p2 ih1 ih2 => simp only [compile, codeLenP, List.length_append]; rw [ih1, ih2]
  | ifNZ e t f iht ihf =>
      simp only [compile, codeLenP, List.length_append, List.length_cons, List.length_nil]
      rw [compileExpr_length, iht, ihf]; omega
  | forN n body ihbody =>
      simp only [compile, codeLenP, List.length_append, List.length_cons, List.length_nil]
      rw [compileExpr_length, ihbody]; omega
  | scanList xs r body ihbody =>
      simp only [compile, codeLenP]
      induction xs generalizing pc with
      | nil => simp [compileScanList]
      | cons x tail ih =>
          simp only [compileScanList, List.length_append, List.length_cons, List.length_nil]
          rw [ihbody (pc + 3) (sb + 2), ih (pc + 3 + codeLenP body), Nat.succ_mul]; omega
  | lookup pairs kReg vReg =>
      simp only [compile, codeLenP, List.length_append, List.length_cons, List.length_nil]
      rw [compileLookupIters_length, List.length_reverse]; omega

/-! ## Locality: jump-target range and confinement

`compile_exec` states only the *endpoint* PC of a compiled block's execution, nothing about
the trajectory in between — so it does not, by itself, tell us that `compile p pc sb`'s
execution never strays outside its own segment `[pc, pc + codeLenP p]`.  That confinement
fact is needed to bridge a dynamic-operand bound recorded against the *bare* compiled program
(`compiledInputRAM`) to the same program with a trailing epilogue appended
(`compiledInputFullRAM`, `BoundedWhileDecider.lean`): as long as execution stays inside the
shared `compile p 0 0` prefix, the two RAMs' trajectories agree regardless of what follows.

Every jump/branch target emitted by `compile`/`compileScanList`/`compileLookupIters` is a
*static*, execution-independent arithmetic expression in the placement PC (`compile`'s own
definition). `CodeTargetsIn`/`compile_targets_in` establish the range property by AST structural
recursion alone (mirroring `compile_length`'s induction), and `step_confined` turns that static
fact into a one-step preservation lemma. Multi-step confinement for a *specific* run
(`fullProgram_run_confined`, `BoundedWhileDecider.lean`) then follows from this lemma and a
least-counterexample argument, without replaying `compile_exec`'s case analysis. -/

/-- Whether an instruction's jump/branch target (if any) lies in `[start, start+len]`.
    Non-control instructions are vacuously fine. -/
def InstrTargetOk (start len : ℕ) : Instruction → Prop
  | Instruction.jump t => start ≤ t ∧ t ≤ start + len
  | Instruction.branchIfNZ _ t => start ≤ t ∧ t ≤ start + len
  | Instruction.branchIfLt _ _ t => start ≤ t ∧ t ≤ start + len
  | _ => True

/-- Every instruction in `code` has its jump/branch target (if any) within `[start, start+len]`. -/
def CodeTargetsIn (start len : ℕ) (code : List Instruction) : Prop :=
  ∀ i ∈ code, InstrTargetOk start len i

lemma CodeTargetsIn.append {start len : ℕ} {c1 c2 : List Instruction}
    (h1 : CodeTargetsIn start len c1) (h2 : CodeTargetsIn start len c2) :
    CodeTargetsIn start len (c1 ++ c2) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h1 i hi
  · exact h2 i hi

/-- A target range widens to any enclosing `[start, start+len]`. -/
lemma CodeTargetsIn.widen {start start' len len' : ℕ} {code : List Instruction}
    (hstart : start ≤ start') (hend : start' + len' ≤ start + len)
    (h : CodeTargetsIn start' len' code) : CodeTargetsIn start len code := by
  intro i hi
  have := h i hi
  cases i <;> simp only [InstrTargetOk] at this ⊢ <;> omega

/-- `compileExpr` never emits a control instruction, so its targets are trivially in any range. -/
lemma compileExpr_targets_in (e : Expr) (dst sb start len : ℕ) :
    CodeTargetsIn start len (compileExpr e dst sb) := by
  induction e generalizing dst sb with
  | const n => simp [compileExpr, CodeTargetsIn, InstrTargetOk]
  | reg r => simp [compileExpr, CodeTargetsIn, InstrTargetOk]
  | regInd e ih =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i (hi | hi)
      · exact ih dst sb i hi
      · simp [hi, InstrTargetOk]
  | add e1 e2 ih1 ih2 =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i ((hi | hi) | hi)
      · exact ih1 sb (sb+2) i hi
      · exact ih2 (sb+1) (sb+2) i hi
      · simp [hi, InstrTargetOk]
  | sub e1 e2 ih1 ih2 =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i ((hi | hi) | hi)
      · exact ih1 sb (sb+2) i hi
      · exact ih2 (sb+1) (sb+2) i hi
      · simp [hi, InstrTargetOk]
  | mul e1 e2 ih1 ih2 =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i ((hi | hi) | hi)
      · exact ih1 sb (sb+2) i hi
      · exact ih2 (sb+1) (sb+2) i hi
      · simp [hi, InstrTargetOk]
  | lt e1 e2 ih1 ih2 =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i ((hi | hi) | hi)
      · exact ih1 sb (sb+2) i hi
      · exact ih2 (sb+1) (sb+2) i hi
      · simp [hi, InstrTargetOk]
  | eq e1 e2 ih1 ih2 =>
      simp only [compileExpr, CodeTargetsIn, List.mem_append, List.mem_singleton] at *
      rintro i ((hi | hi) | hi)
      · exact ih1 sb (sb+2) i hi
      · exact ih2 (sb+1) (sb+2) i hi
      · simp [hi, InstrTargetOk]

/-- `compileLookupIters`'s local jumps/branches (skip-on-match, fallthrough) stay within its
    own `5 * pairs.length`-instruction block. -/
lemma compileLookupIters_targets_in (keyReg resReg sb : ℕ) :
    ∀ (pairs : List (ℕ × ℕ)) (pc : ℕ),
      CodeTargetsIn pc (5 * pairs.length) (compileLookupIters pairs keyReg resReg sb pc) := by
  intro pairs
  induction pairs with
  | nil => intro pc i hi; simp [compileLookupIters] at hi
  | cons p rest ih =>
      intro pc
      obtain ⟨k, v⟩ := p
      simp only [compileLookupIters]
      have hset : CodeTargetsIn pc (5 * (rest.length + 1))
          [Instruction.loadImm (sb + 3) k, Instruction.setIfEq (sb + 4) keyReg (sb + 3),
           Instruction.branchIfNZ (sb + 4) (pc + 4), Instruction.jump (pc + 5),
           Instruction.loadImm resReg v] := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h|h|h|h <;> simp [h, InstrTargetOk] <;> omega
      have hrest : CodeTargetsIn pc (5 * (rest.length + 1))
          (compileLookupIters rest keyReg resReg sb (pc + 5)) :=
        CodeTargetsIn.widen (by omega) (by omega) (ih (pc + 5))
      have := hset.append hrest
      simpa [List.length_cons, Nat.succ_mul] using this

/-- Static fact: every jump/branch target `compile p pc sb` emits lands inside the
    segment `[pc, pc + codeLenP p]` it occupies (mirrors `compile_length`'s AST induction). -/
lemma compile_targets_in : ∀ (p : Program) (pc sb : ℕ),
    CodeTargetsIn pc (codeLenP p) (compile p pc sb) := by
  intro p
  induction p with
  | skip => intro pc sb i hi; simp [compile] at hi
  | assign r e =>
      intro pc sb
      simp only [compile, codeLenP]
      exact (compileExpr_targets_in e sb (sb+1) pc (codeLenE e + 2)).append
        (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h <;> simp [h, InstrTargetOk])
  | assignInd eA eV =>
      intro pc sb
      simp only [compile, codeLenP]
      exact ((compileExpr_targets_in eA sb (sb+2) pc (codeLenE eA + codeLenE eV + 1)).append
        (compileExpr_targets_in eV (sb+1) (sb+2) pc (codeLenE eA + codeLenE eV + 1))).append
        (fun i hi => by simp only [List.mem_singleton] at hi; simp [hi, InstrTargetOk])
  | seq p1 p2 ih1 ih2 =>
      intro pc sb
      simp only [compile, codeLenP]
      exact (CodeTargetsIn.widen (le_refl pc) (by omega) (ih1 pc sb)).append
        (CodeTargetsIn.widen (by omega) (by omega) (ih2 (pc + codeLenP p1) sb))
  | ifNZ e t f iht ihf =>
      intro pc sb
      simp only [compile, codeLenP]
      have hbr : CodeTargetsIn pc (codeLenE e + codeLenP t + codeLenP f + 2)
          [Instruction.branchIfNZ sb (pc + codeLenE e + codeLenP f + 2)] := by
        intro i hi; simp only [List.mem_singleton] at hi; simp only [hi, InstrTargetOk]; omega
      have hjmp : CodeTargetsIn pc (codeLenE e + codeLenP t + codeLenP f + 2)
          [Instruction.jump (pc + codeLenE e + codeLenP f + codeLenP t + 2)] := by
        intro i hi; simp only [List.mem_singleton] at hi; simp only [hi, InstrTargetOk]; omega
      exact ((((compileExpr_targets_in e sb (sb+1) pc
        (codeLenE e + codeLenP t + codeLenP f + 2)).append hbr).append
        (CodeTargetsIn.widen (by omega) (by omega) (ihf (pc + codeLenE e + 1) (sb + 1)))).append
        hjmp).append
        (CodeTargetsIn.widen (by omega) (by omega) (iht (pc + codeLenE e + codeLenP f + 2) (sb + 1)))
  | forN n body ihbody =>
      intro pc sb
      simp only [compile, codeLenP]
      have hC : CodeTargetsIn pc (codeLenE n + codeLenP body + 6)
          [Instruction.branchIfLt sb (sb+1) (pc + codeLenE n + 4),
           Instruction.jump (pc + codeLenE n + codeLenP body + 6)] := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h <;> (simp only [h, InstrTargetOk]; omega)
      have hE : CodeTargetsIn pc (codeLenE n + codeLenP body + 6)
          [Instruction.add sb sb (sb+2), Instruction.jump (pc + codeLenE n + 2)] := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h
        · simp [h, InstrTargetOk]
        · simp only [h, InstrTargetOk]; omega
      have hD := CodeTargetsIn.widen (start := pc) (len := codeLenE n + codeLenP body + 6)
        (by omega) (by omega) (ihbody (pc + codeLenE n + 4) (sb + 3))
      exact ((compileExpr_targets_in n (sb+1) (sb+3) pc (codeLenE n + codeLenP body + 6)).append
        (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h <;> simp [h, InstrTargetOk])).append
        ((hC.append hD).append hE)
  | scanList xs r body ihbody =>
      intro pc sb
      simp only [compile, codeLenP]
      induction xs generalizing pc with
      | nil => intro i hi; simp [compileScanList] at hi
      | cons x tail ih =>
          simp only [compileScanList, List.length_cons]
          have hlit : CodeTargetsIn pc ((tail.length + 1) * (3 + codeLenP body))
              [Instruction.loadImm sb r, Instruction.loadImm (sb+1) x,
               Instruction.store (sb+1) sb] := by
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with h|h|h <;> simp [h, InstrTargetOk]
          have hbody := CodeTargetsIn.widen (start := pc)
            (len := (tail.length + 1) * (3 + codeLenP body))
            (by omega) (by rw [Nat.succ_mul]; omega) (ihbody (pc + 3) (sb + 2))
          have htail := CodeTargetsIn.widen (start := pc)
            (len := (tail.length + 1) * (3 + codeLenP body))
            (by omega) (by rw [Nat.succ_mul]; omega) (ih (pc + 3 + codeLenP body))
          exact (hlit.append hbody).append htail
  | lookup pairs kReg vReg =>
      intro pc sb
      simp only [compile, codeLenP]
      have hpre : CodeTargetsIn pc (5 + 5 * pairs.length)
          [Instruction.loadImm sb kReg, Instruction.load (sb+1) sb,
           Instruction.loadImm (sb+2) 0] := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h|h <;> simp [h, InstrTargetOk]
      have hmid := CodeTargetsIn.widen (start := pc) (len := 5 + 5 * pairs.length)
        (by omega) (by rw [List.length_reverse]; omega)
        (compileLookupIters_targets_in (sb+1) (sb+2) sb pairs.reverse (pc+3))
      have hpost : CodeTargetsIn pc (5 + 5 * pairs.length)
          [Instruction.loadImm sb vReg, Instruction.store (sb+2) sb] := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h <;> simp [h, InstrTargetOk]
      exact (hpre.append hmid).append hpost

/-- Single-step effect of a `store rSrc rAddr`: `mem (regs rAddr)` gets
    `regs rSrc`, the PC advances, and registers / program are untouched. -/
lemma step_store (rr : RAM) (rSrc rAddr : ℕ) (hc : rr.current = Instruction.store rSrc rAddr) :
    (step rr).mem = bankWrite rr.mem (rr.regs rAddr) (rr.regs rSrc) ∧
    (step rr).pc = rr.pc + 1 ∧ (step rr).regs = rr.regs ∧ (step rr).program = rr.program := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [step, hc]

/-- The RAM `bankWrite` and DSL `writeReg` point-updates coincide (both are
    `fun a => if a = addr then v else b a`), bridging the two state models. -/
lemma bankWrite_eq_writeReg (b : Bank) (addr v : ℕ) :
    bankWrite b addr v = writeReg b addr v := rfl

/-- Single-step effect of `branchIfNZ rs target`: the PC forks on `regs rs`; the
    banks and program are untouched. -/
lemma step_branchIfNZ (rr : RAM) (rs target : ℕ)
    (hc : rr.current = Instruction.branchIfNZ rs target) :
    (step rr).pc = (if rr.regs rs ≠ 0 then target else rr.pc + 1) ∧
    (step rr).mem = rr.mem ∧ (step rr).regs = rr.regs ∧ (step rr).program = rr.program := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [step, hc]

/-- Single-step effect of `jump target`: the PC becomes `target`; banks and
    program are untouched. -/
lemma step_jump (rr : RAM) (target : ℕ) (hc : rr.current = Instruction.jump target) :
    (step rr).pc = target ∧ (step rr).mem = rr.mem ∧ (step rr).regs = rr.regs ∧
    (step rr).program = rr.program := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [step, hc]

/-- Single-step effect of `branchIfLt rs rt target`: the PC forks on
    `regs rs < regs rt`; the banks and program are untouched. -/
lemma step_branchIfLt (rr : RAM) (rs rt target : ℕ)
    (hc : rr.current = Instruction.branchIfLt rs rt target) :
    (step rr).pc = (if rr.regs rs < rr.regs rt then target else rr.pc + 1) ∧
    (step rr).mem = rr.mem ∧ (step rr).regs = rr.regs ∧ (step rr).program = rr.program := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [step, hc]

/-- Single-step effect of `add rd rs rt`: `regs rd` gets `regs rs + regs rt`; PC
    advances, memory / program untouched, and other registers are framed. -/
lemma step_add (rr : RAM) (rd rs rt : ℕ) (hc : rr.current = Instruction.add rd rs rt) :
    (step rr).regs rd = rr.regs rs + rr.regs rt ∧ (step rr).pc = rr.pc + 1 ∧
    (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
    ∀ y, y ≠ rd → (step rr).regs y = rr.regs y := by
  refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp only [step, hc]; exact bankWrite_same _ _ _
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy

/-- Single-step effect of `setIfEq rd rs rt`: `regs rd` gets the equality flag;
    PC advances, memory / program untouched, and other registers are framed. -/
lemma step_setIfEq (rr : RAM) (rd rs rt : ℕ) (hc : rr.current = Instruction.setIfEq rd rs rt) :
    (step rr).regs rd = (if rr.regs rs = rr.regs rt then 1 else 0) ∧ (step rr).pc = rr.pc + 1 ∧
    (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
    ∀ y, y ≠ rd → (step rr).regs y = rr.regs y := by
  refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp only [step, hc]; exact bankWrite_same _ _ _
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]
  · simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy

/-- Reverse-walk semantics of `compileLookupIters`: the running result register,
    threaded left-to-right over the (reversed) pair list, takes the value of the
    last matching pair (or keeps the initial value).  Matches the compiled code's
    unconditional overwrite on match. -/
def lookupFold : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, r => r
  | (k, v) :: rest, key, r => lookupFold rest key (if key = k then v else r)

/-- `lookupFold` distributes over list append. -/
lemma lookupFold_append (ps qs : List (ℕ × ℕ)) (key r : ℕ) :
    lookupFold (ps ++ qs) key r = lookupFold qs key (lookupFold ps key r) := by
  induction ps generalizing r with
  | nil => rfl
  | cons p rest ih => obtain ⟨k, v⟩ := p; simp only [List.cons_append, lookupFold]; rw [ih]

/-- Folding the reversed pair list (last-match-wins) recovers `findVal`
    (first-match-wins on the original order). -/
lemma lookupFold_reverse (pairs : List (ℕ × ℕ)) (key : ℕ) :
    lookupFold pairs.reverse key 0 = findVal pairs key := by
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      rw [List.reverse_cons, lookupFold_append, ih]
      simp only [lookupFold, findVal_cons]
      by_cases h : k = key
      · rw [ite_eq_left h.symm, ite_eq_left h]
      · rw [ite_eq_right (fun he => h he.symm), ite_eq_right h]


/-- Execution certificate for the unrolled `scanList`, proved by induction on the
    element list.  Each iteration writes `mem r ← x` (three steps) and runs the
    body via the outer `ihbody`; the tail folds through the induction hypothesis.
    Phrased against a body certificate `ihbody` so it can be discharged with the
    `compile_exec` induction hypothesis for `body`. -/
lemma compileScanList_exec (body : Program) (r sb : ℕ)
    (ihbody : ∀ (sb' : ℕ) (rr : RAM),
      SegmentAt rr.program rr.pc (compile body rr.pc sb') →
      ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
           (run k rr).mem = Program.eval body rr.mem ∧
           (∀ x, x < sb' → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost body rr.mem) :
    ∀ (xs : List ℕ) (rr : RAM),
      SegmentAt rr.program rr.pc (compileScanList xs r body rr.pc sb) →
      ∃ k, (run k rr).pc = rr.pc + xs.length * (3 + codeLenP body) ∧
           (run k rr).mem = scanListEval body xs r rr.mem ∧
           (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧
           k ≤ 8 * scanListCost body xs r rr.mem := by
  intro xs
  induction xs with
  | nil =>
      intro rr _
      exact ⟨0, by simp, (scanListEval_nil body r rr.mem).symm, fun x _ => rfl, rfl, by simp⟩
  | cons x tail ih =>
      intro rr hseg
      simp only [compileScanList] at hseg
      rw [List.append_assoc] at hseg
      have segW : SegmentAt rr.program rr.pc
          [Instruction.loadImm sb r, Instruction.loadImm (sb + 1) x,
           Instruction.store (sb + 1) sb] := hseg.append_left
      have hc0 : rr.current = Instruction.loadImm sb r := by
        have := current_of_segment 0 segW (by simp) rr rfl rfl; simpa using this
      obtain ⟨w0regs, w0pc, w0mem, w0prog, w0fr⟩ := step_loadImm rr sb r hc0
      have hc1 : (step rr).current = Instruction.loadImm (sb + 1) x := by
        have := current_of_segment 1 segW (by simp) (step rr) w0pc w0prog; simpa using this
      obtain ⟨w1regs, w1pc, w1mem, w1prog, w1fr⟩ := step_loadImm (step rr) (sb + 1) x hc1
      have hpc2 : (step (step rr)).pc = rr.pc + 2 := by rw [w1pc, w0pc]
      have hprog2 : (step (step rr)).program = rr.program := by rw [w1prog, w0prog]
      have hc2 : (step (step rr)).current = Instruction.store (sb + 1) sb := by
        have := current_of_segment 2 segW (by simp) (step (step rr)) hpc2 hprog2
        simpa using this
      obtain ⟨w2mem, w2pc, w2regs, w2prog⟩ := step_store (step (step rr)) (sb + 1) sb hc2
      have hstep3 : run 3 rr = step (step (step rr)) := rfl
      have h3pc : (run 3 rr).pc = rr.pc + 3 := by rw [hstep3, w2pc, w1pc, w0pc]
      have h3prog : (run 3 rr).program = rr.program := by rw [hstep3, w2prog, w1prog, w0prog]
      have h3mem : (run 3 rr).mem = writeReg rr.mem r x := by
        rw [hstep3, w2mem, w1regs, w1fr sb (by omega), w0regs, w1mem, w0mem, bankWrite_eq_writeReg]
      have h3fr : ∀ y, y < sb → (run 3 rr).regs y = rr.regs y := by
        intro y hy; rw [hstep3, w2regs, w1fr y (by omega), w0fr y (by omega)]
      have segB : SegmentAt (run 3 rr).program (run 3 rr).pc (compile body (run 3 rr).pc (sb + 2)) := by
        rw [h3prog, h3pc]; simpa using hseg.append_right.append_left
      obtain ⟨kb, bpc, bmem, bfr, bprog, bhk⟩ := ihbody (sb + 2) (run 3 rr) segB
      have segT : SegmentAt (run kb (run 3 rr)).program (run kb (run 3 rr)).pc
          (compileScanList tail r body (run kb (run 3 rr)).pc sb) := by
        rw [bprog, h3prog, bpc, h3pc]
        have hT := hseg.append_right.append_right
        rw [compile_length] at hT; simpa using hT
      obtain ⟨kt, tpc, tmem, tfr, tprog, thk⟩ := ih (run kb (run 3 rr)) segT
      have hrun : run (3 + kb + kt) rr = run kt (run kb (run 3 rr)) := by
        rw [run_add, run_add]
      have hbound : 3 + kb + kt ≤ 8 * scanListCost body (x :: tail) r rr.mem := by
        rw [h3mem] at bhk
        rw [bmem, h3mem] at thk
        have hc := scanListCost_cons body x tail r rr.mem
        omega
      refine ⟨3 + kb + kt, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrun]
      · rw [tpc, bpc, h3pc]; simp only [List.length_cons]; rw [Nat.succ_mul]; omega
      · rw [tmem, bmem, h3mem]
        exact (scanListEval_cons body x tail r rr.mem).symm
      · intro y hy; rw [tfr y hy, bfr y (by omega), h3fr y hy]
      · rw [tprog, bprog, h3prog]

/-- The compiled `forN` loop, from the test PC.  Proved by induction on the
    remaining iteration count `m` (`= bound - i`).  The invariant threaded through
    the loop is: the counter register `sb` holds `bound - m`, the bound register
    `sb+1` holds `bound`, and the increment register `sb+2` holds `1`.  Each
    iteration runs the body via `ihbody` (which preserves `sb`/`sb+1`/`sb+2` since
    its scratch base is `sb+3`), increments the counter, and jumps back. -/
lemma forN_loop (body : Program) (sb base cn bound : ℕ)
    (ihbody : ∀ (rr : RAM), SegmentAt rr.program rr.pc (compile body rr.pc (sb + 3)) →
      ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
           (run k rr).mem = Program.eval body rr.mem ∧
           (∀ x, x < sb + 3 → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost body rr.mem) :
    ∀ (m : ℕ) (s : RAM),
      SegmentAt s.program (base + cn + 2)
        ([Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
          Instruction.jump (base + cn + codeLenP body + 6)] ++
         compile body (base + cn + 4) (sb + 3) ++
         [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)]) →
      s.pc = base + cn + 2 → s.regs (sb + 1) = bound → s.regs (sb + 2) = 1 →
      s.regs sb + m = bound →
      ∃ k, (run k s).pc = base + cn + codeLenP body + 6 ∧
           (run k s).mem = loopEval body m s.mem ∧
           (∀ x, x < sb → (run k s).regs x = s.regs x) ∧
           (run k s).program = s.program ∧ k ≤ 2 + 8 * loopCost body m s.mem := by
  intro m
  induction m with
  | zero =>
      intro s hseg hpc hbound hone hi
      have hisb : s.regs sb = bound := by omega
      have hcur0 : s.current = Instruction.branchIfLt sb (sb + 1) (base + cn + 4) := by
        rw [current_eq_getD, hpc]
        simpa using segment_getD hseg.append_left.append_left (show (0:ℕ) < 2 from by omega)
      obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfLt s sb (sb + 1) _ hcur0
      have hbrpc : (step s).pc = base + cn + 3 := by rw [brPc, hisb, hbound]; simp [hpc]
      have hcurJ : (step s).current = Instruction.jump (base + cn + codeLenP body + 6) := by
        rw [current_eq_getD, brProg, hbrpc]
        simpa using segment_getD hseg.append_left.append_left (show (1:ℕ) < 2 from by omega)
      obtain ⟨jPc, jMem, jRegs, jProg⟩ := step_jump (step s) _ hcurJ
      refine ⟨2, ?_, ?_, ?_, ?_, by simp⟩ <;> rw [show run 2 s = step (step s) from rfl]
      · rw [jPc]
      · rw [jMem, brMem]
        exact (loopEval_zero body s.mem).symm
      · intro x _; rw [jRegs, brRegs]
      · rw [jProg, brProg]
  | succ m ih =>
      intro s hseg hpc hbound hone hi
      have hlt : s.regs sb < s.regs (sb + 1) := by rw [hbound]; omega
      have hcur0 : s.current = Instruction.branchIfLt sb (sb + 1) (base + cn + 4) := by
        rw [current_eq_getD, hpc]
        simpa using segment_getD hseg.append_left.append_left (show (0:ℕ) < 2 from by omega)
      obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfLt s sb (sb + 1) _ hcur0
      have hbrpc : (step s).pc = base + cn + 4 := by rw [brPc]; simp [hlt]
      have segBody : SegmentAt (step s).program (step s).pc (compile body (step s).pc (sb + 3)) := by
        rw [brProg, hbrpc]; simpa using hseg.append_left.append_right
      obtain ⟨kb, bpc, bmem, bfr, bprog, bhk⟩ := ihbody (step s) segBody
      have haddpc : (run kb (step s)).pc = base + cn + 4 + codeLenP body := by rw [bpc, hbrpc]
      have haddprog : (run kb (step s)).program = s.program := by rw [bprog, brProg]
      have segAdd : SegmentAt (run kb (step s)).program (run kb (step s)).pc
          [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)] := by
        rw [haddprog, haddpc]
        have hb := hseg.append_right
        simp only [List.length_append, List.length_cons, List.length_nil, compile_length] at hb
        rw [show base + cn + 4 + codeLenP body = base + cn + 2 + (2 + codeLenP body) from by omega]
        exact hb
      have hcurAdd : (run kb (step s)).current = Instruction.add sb sb (sb + 2) := by
        have := current_of_segment 0 segAdd (by simp) (run kb (step s)) rfl rfl; simpa using this
      obtain ⟨addRegs, addPc, addMem, addProg, addFr⟩ :=
        step_add (run kb (step s)) sb sb (sb + 2) hcurAdd
      have hcurJb : (step (run kb (step s))).current = Instruction.jump (base + cn + 2) := by
        have := current_of_segment 1 segAdd (by simp) (step (run kb (step s))) addPc addProg
        simpa using this
      obtain ⟨jbPc, jbMem, jbRegs, jbProg⟩ := step_jump (step (run kb (step s))) _ hcurJb
      have hisb : (run kb (step s)).regs sb = s.regs sb := by
        rw [bfr sb (by omega), brRegs]
      have hone2 : (run kb (step s)).regs (sb + 2) = 1 := by
        rw [bfr (sb + 2) (by omega), brRegs, hone]
      have hs2pc : (step (step (run kb (step s)))).pc = base + cn + 2 := jbPc
      have hs2prog : (step (step (run kb (step s)))).program = s.program := by
        rw [jbProg, addProg, haddprog]
      have hs2sb : (step (step (run kb (step s)))).regs sb = s.regs sb + 1 := by
        rw [jbRegs, addRegs, hisb, hone2]
      have hs2b1 : (step (step (run kb (step s)))).regs (sb + 1) = bound := by
        rw [jbRegs, addFr (sb + 1) (by omega), bfr (sb + 1) (by omega), brRegs, hbound]
      have hs2b2 : (step (step (run kb (step s)))).regs (sb + 2) = 1 := by
        rw [jbRegs, addFr (sb + 2) (by omega), hone2]
      have hs2mem : (step (step (run kb (step s)))).mem = Program.eval body s.mem := by
        rw [jbMem, addMem, bmem, brMem]
      have hs2fr : ∀ x, x < sb → (step (step (run kb (step s)))).regs x = s.regs x := by
        intro x hx; rw [jbRegs, addFr x (by omega), bfr x (by omega), brRegs]
      have hsegs2 : SegmentAt (step (step (run kb (step s)))).program (base + cn + 2)
          ([Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
            Instruction.jump (base + cn + codeLenP body + 6)] ++
           compile body (base + cn + 4) (sb + 3) ++
           [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)]) := by
        rw [hs2prog]; exact hseg
      obtain ⟨kt, tpc, tmem, tfr, tprog, thk⟩ :=
        ih (step (step (run kb (step s)))) hsegs2 hs2pc hs2b1 hs2b2 (by rw [hs2sb]; omega)
      have hrun : run (kb + kt + 3) s = run kt (step (step (run kb (step s)))) := by
        rw [show kb + kt + 3 = (kb + 3) + kt from by omega, run_add,
          show kb + 3 = kb + 1 + 1 + 1 from by omega, run_succ_right, run_succ_right, run_succ]
      have hbound : kb + kt + 3 ≤ 2 + 8 * loopCost body (m + 1) s.mem := by
        rw [brMem] at bhk
        rw [hs2mem] at thk
        have hc := loopCost_succ body m s.mem
        omega
      refine ⟨kb + kt + 3, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrun]
      · rw [tpc]
      · rw [tmem, hs2mem]
        exact (loopEval_succ body m s.mem).symm
      · intro x hx; rw [tfr x hx, hs2fr x hx]
      · rw [tprog, hs2prog]

/-- One generated pair is a conditional result-register update, isolating the fixed-size
    execution contract used by the lookup-list induction. -/
lemma compileLookupIters_exec_pair (keyReg resReg sb k v : ℕ)
    (hkey : keyReg < sb + 3) (hres : resReg < sb + 3) (s : RAM)
    (hseg : SegmentAt s.program s.pc
      [Instruction.loadImm (sb + 3) k, Instruction.setIfEq (sb + 4) keyReg (sb + 3),
       Instruction.branchIfNZ (sb + 4) (s.pc + 4), Instruction.jump (s.pc + 5),
       Instruction.loadImm resReg v]) :
    (run 4 s).pc = s.pc + 5 ∧ (run 4 s).mem = s.mem ∧
      (run 4 s).regs resReg = (if s.regs keyReg = k then v else s.regs resReg) ∧
      (∀ y, y < sb + 3 → y ≠ resReg → (run 4 s).regs y = s.regs y) ∧
      (run 4 s).program = s.program := by
  have hc0 : s.current = Instruction.loadImm (sb + 3) k := by
    have := current_of_segment 0 hseg (by simp) s rfl rfl
    simpa using this
  obtain ⟨s0regs, s0pc, s0mem, s0prog, s0fr⟩ := step_loadImm s (sb + 3) k hc0
  have hc1 : (step s).current = Instruction.setIfEq (sb + 4) keyReg (sb + 3) := by
    have := current_of_segment 1 hseg (by simp) (step s) s0pc s0prog
    simpa using this
  obtain ⟨s1regs, s1pc, s1mem, s1prog, s1fr⟩ :=
    step_setIfEq (step s) (sb + 4) keyReg (sb + 3) hc1
  have hflag : (step (step s)).regs (sb + 4) = (if s.regs keyReg = k then 1 else 0) := by
    rw [s1regs, s0fr keyReg (by omega), s0regs]
  have hp2pc : (step (step s)).pc = s.pc + 2 := by rw [s1pc, s0pc]
  have hp2prog : (step (step s)).program = s.program := by rw [s1prog, s0prog]
  have hc2 : (step (step s)).current = Instruction.branchIfNZ (sb + 4) (s.pc + 4) := by
    have := current_of_segment 2 hseg (by simp) (step (step s)) hp2pc hp2prog
    simpa using this
  obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfNZ (step (step s)) (sb + 4) (s.pc + 4) hc2
  have s3mem : (step (step (step s))).mem = s.mem := by rw [brMem, s1mem, s0mem]
  have s3prog : (step (step (step s))).program = s.program := by rw [brProg, s1prog, s0prog]
  have s3res : (step (step (step s))).regs resReg = s.regs resReg := by
    rw [brRegs, s1fr resReg (by omega), s0fr resReg (by omega)]
  have s3fr : ∀ y, y < sb + 3 → y ≠ resReg →
      (step (step (step s))).regs y = s.regs y := by
    intro y hy hyr
    rw [brRegs, s1fr y (by omega), s0fr y (by omega)]
  have hrun4 : run 4 s = step (step (step (step s))) := rfl
  by_cases hkk : s.regs keyReg = k
  · have hflag1 : (step (step s)).regs (sb + 4) = 1 := by rw [hflag, ite_eq_left hkk]
    have hs3pc : (step (step (step s))).pc = s.pc + 4 := by rw [brPc, hflag1]; simp
    have hc4 : (step (step (step s))).current = Instruction.loadImm resReg v := by
      have := current_of_segment 4 hseg (by simp) (step (step (step s))) hs3pc s3prog
      simpa using this
    obtain ⟨w4regs, w4pc, w4mem, w4prog, w4fr⟩ :=
      step_loadImm (step (step (step s))) resReg v hc4
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hrun4]
    · rw [w4pc, hs3pc]
    · rw [w4mem, s3mem]
    · rw [w4regs, ite_eq_left hkk]
    · intro y hy hyr
      rw [w4fr y hyr, s3fr y hy hyr]
    · rw [w4prog, s3prog]
  · have hflag0 : (step (step s)).regs (sb + 4) = 0 := by rw [hflag, ite_eq_right hkk]
    have hs3pc : (step (step (step s))).pc = s.pc + 2 + 1 := by
      rw [brPc, hflag0, hp2pc]
      simp
    have hc3 : (step (step (step s))).current = Instruction.jump (s.pc + 5) := by
      have := current_of_segment 3 hseg (by simp) (step (step (step s))) hs3pc s3prog
      simpa using this
    obtain ⟨j3pc, j3mem, j3regs, j3prog⟩ := step_jump (step (step (step s))) _ hc3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hrun4]
    · rw [j3pc]
    · rw [j3mem, s3mem]
    · rw [j3regs, s3res, ite_eq_right hkk]
    · intro y hy hyr
      rw [j3regs, s3fr y hy hyr]
    · rw [j3prog, s3prog]

/-- Execution certificate for the unrolled `lookup` iterations.  Proved by
    induction on the pair list.  Each pair is four executed steps (the fifth
    instruction is skipped by the branch): compute the equality flag, branch, and
    on a match overwrite the result register.  Reads the key register (preserved),
    writes only the result register and scratch `sb+3`/`sb+4`.  The running result
    tracks `lookupFold` (last-match-wins over the given, already-reversed, list). -/
lemma compileLookupIters_exec (keyReg resReg sb : ℕ)
    (hkey : keyReg < sb + 3) (hres : resReg < sb + 3) (hkr : keyReg ≠ resReg) :
    ∀ (ps : List (ℕ × ℕ)) (s : RAM),
      SegmentAt s.program s.pc (compileLookupIters ps keyReg resReg sb s.pc) →
      ∃ k, (run k s).pc = s.pc + 5 * ps.length ∧ (run k s).mem = s.mem ∧
           (run k s).regs resReg = lookupFold ps (s.regs keyReg) (s.regs resReg) ∧
           (∀ y, y < sb + 3 → y ≠ resReg → (run k s).regs y = s.regs y) ∧
           (run k s).program = s.program ∧ k ≤ 4 * ps.length := by
  intro ps
  induction ps with
  | nil => intro s _; exact ⟨0, by simp, rfl, rfl, fun y _ _ => rfl, rfl, by simp⟩
  | cons p rest ih =>
      intro s hseg
      obtain ⟨k, v⟩ := p
      simp only [compileLookupIters] at hseg
      have segPair : SegmentAt s.program s.pc
          [Instruction.loadImm (sb + 3) k, Instruction.setIfEq (sb + 4) keyReg (sb + 3),
           Instruction.branchIfNZ (sb + 4) (s.pc + 4), Instruction.jump (s.pc + 5),
           Instruction.loadImm resReg v] := hseg.append_left
      obtain ⟨hp5pc, hp5mem, hp5res, hp5fr, hp5prog⟩ :=
        compileLookupIters_exec_pair keyReg resReg sb k v hkey hres s segPair
      have segRest : SegmentAt (run 4 s).program (run 4 s).pc
          (compileLookupIters rest keyReg resReg sb (run 4 s).pc) := by
        rw [hp5prog, hp5pc]; simpa using hseg.append_right
      obtain ⟨kr, rpc, rmem, rres, rfr, rprog, rhk⟩ := ih (run 4 s) segRest
      have hrun : run (4 + kr) s = run kr (run 4 s) := run_add 4 kr s
      refine ⟨4 + kr, ?_, ?_, ?_, ?_, ?_, by simp only [List.length_cons]; omega⟩ <;> rw [hrun]
      · rw [rpc, hp5pc]; simp only [List.length_cons]; rw [Nat.mul_succ]; omega
      · rw [rmem, hp5mem]
      · rw [rres, hp5fr keyReg (by omega) hkr, hp5res]; simp only [lookupFold]
      · intro y hy hyr; rw [rfr y hy hyr, hp5fr y hy hyr]
      · rw [rprog, hp5prog]

/-- One step of a machine strictly inside a `code` segment (all of whose jump/branch
    targets stay within `[start, start+len]`, e.g. via `compile_targets_in`) lands back
    within `[start, start+len]`. The dynamic half of the locality argument (module comment
    above `InstrTargetOk`); `BoundedWhileDecider.lean`'s `fullProgram_run_confined` iterates
    this to get multi-step confinement for a specific run. -/
lemma step_confined {s : RAM} {start len : ℕ} {code : List Instruction}
    (hseg : SegmentAt s.program start code) (hlen : code.length = len)
    (htargets : CodeTargetsIn start len code)
    (hlo : start ≤ s.pc) (hhi : s.pc < start + len) :
    start ≤ (step s).pc ∧ (step s).pc ≤ start + len := by
  have hi : s.pc - start < code.length := by omega
  have hcur : s.current = code.getD (s.pc - start) Instruction.halt := by
    rw [current_eq_getD]
    have := segment_getD hseg hi
    rwa [show start + (s.pc - start) = s.pc from by omega] at this
  have hmem : code.getD (s.pc - start) Instruction.halt ∈ code := by
    rw [← List.getElem_eq_getD Instruction.halt (h := hi)]
    exact List.getElem_mem hi
  have htarget := htargets _ hmem
  rw [← hcur] at htarget
  unfold step
  cases hc : s.current with
  | jump t => simp only [hc, InstrTargetOk] at htarget; simp; omega
  | branchIfNZ rs t =>
      simp only [hc, InstrTargetOk] at htarget; simp; split <;> omega
  | branchIfLt rs rt t =>
      simp only [hc, InstrTargetOk] at htarget; simp; split <;> omega
  | loadImm _ _ => simp; omega
  | move _ _ => simp; omega
  | load _ _ => simp; omega
  | store _ _ => simp; omega
  | add _ _ _ => simp; omega
  | sub _ _ _ => simp; omega
  | mul _ _ _ => simp; omega
  | setIfLt _ _ _ => simp; omega
  | setIfEq _ _ _ => simp; omega
  | halt => simp; omega

/-- `step`'s `regs`/`mem`/`pc`/`cost` fields are a pure function of the *current instruction*
    and the incoming `regs`/`mem`/`pc`/`cost` — `.program` is read only to compute `.current`
    and is otherwise untouched (`step_program`). So two RAMs that agree on those five values
    step to the same `regs`/`mem`/`pc`/`cost`, even with different `.program` fields — the
    other half of the locality argument (state-agreement, module comment above
    `InstrTargetOk`), used once confinement establishes the two RAMs read the same `.current`
    at every step. -/
lemma step_congr {r1 r2 : RAM} (hc : r1.current = r2.current) (hr : r1.regs = r2.regs)
    (hm : r1.mem = r2.mem) (hp : r1.pc = r2.pc) (hco : r1.cost = r2.cost) :
    (step r1).regs = (step r2).regs ∧ (step r1).mem = (step r2).mem ∧
    (step r1).pc = (step r2).pc ∧ (step r1).cost = (step r2).cost := by
  cases hcur : r2.current <;> simp [step, hc, hcur, hr, hm, hp, hco]

/-! ## Program execution certificate

`compile_exec` states that running the compiled block from a state whose program
places it at `rr.pc` terminates with the memory equal to `Program.eval p rr.mem`
(the mem-unified state model), the PC advanced past the block, the program
unchanged, and every register below the scratch base `sb` framed.  Register frame
`regs < sb` is what lets an enclosing loop keep its counter across a body call.
Bit-cost is a separate concern and is stated separately. -/

/-- `compile_exec` for `assign`: evaluate the expression into `sb`, stage the target
    address in `sb+1`, then `store`. -/
lemma compile_exec_assign (r : ℕ) (e : Expr) (sb : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.assign r e) rr.pc sb)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.assign r e) ∧
      (run k rr).mem = Program.eval (Program.assign r e) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost (Program.assign r e) rr.mem := by
  simp only [compile] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hk1⟩ :=
    compileExpr_exec e sb (sb + 1) (by omega) rr hseg.append_left
  have segtail : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.loadImm (sb + 1) r, Instruction.store sb (sb + 1)] := by
    rw [hprog1, hpc1]; exact hseg.append_right
  have hcur0 : (run k1 rr).current = Instruction.loadImm (sb + 1) r := by
    have := current_of_segment 0 segtail (by simp) (run k1 rr) rfl rfl; simpa using this
  obtain ⟨l0regs, l0pc, l0mem, l0prog, l0fr⟩ := step_loadImm (run k1 rr) (sb + 1) r hcur0
  have hcur1 : (step (run k1 rr)).current = Instruction.store sb (sb + 1) := by
    have := current_of_segment 1 segtail (by simp) (step (run k1 rr)) l0pc l0prog
    simpa using this
  obtain ⟨s1mem, s1pc, s1regs, s1prog⟩ := step_store (step (run k1 rr)) sb (sb + 1) hcur1
  have hrun : run (k1 + 2) rr = step (step (run k1 rr)) := by
    rw [show k1 + 2 = k1 + 1 + 1 from rfl, run_succ_right, run_succ_right]
  refine ⟨k1 + 2, ?_, ?_, ?_, ?_, by have hc := cost_assign r e rr.mem; omega⟩ <;> rw [hrun]
  · rw [s1pc, l0pc, hpc1, compileExpr_length]; simp only [codeLenP]; omega
  · rw [s1mem, l0regs, l0fr sb (by omega), hrd1, l0mem, hmem1, bankWrite_eq_writeReg]
    exact (eval_assign r e rr.mem).symm
  · intro x hx
    rw [s1regs, l0fr x (by omega)]; exact hfr1 x (by omega) (by omega)
  · rw [s1prog, l0prog, hprog1]

/-- `compile_exec` for `assignInd`: evaluate address and value into `sb`/`sb+1`
    (with scratch base `sb+2`), then `store`. -/
lemma compile_exec_assignInd (eA eV : Expr) (sb : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.assignInd eA eV) rr.pc sb)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.assignInd eA eV) ∧
      (run k rr).mem = Program.eval (Program.assignInd eA eV) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost (Program.assignInd eA eV) rr.mem := by
  simp only [compile] at hseg
  rw [List.append_assoc] at hseg
  obtain ⟨k1, hpc1, hrdA, hmem1, hfr1, hprog1, hk1⟩ :=
    compileExpr_exec eA sb (sb + 2) (by omega) rr hseg.append_left
  have segB : SegmentAt (run k1 rr).program (run k1 rr).pc
      (compileExpr eV (sb + 1) (sb + 2)) := by
    rw [hprog1, hpc1]; exact hseg.append_right.append_left
  obtain ⟨k2, hpc2, hrdV, hmem2, hfr2, hprog2, hk2⟩ :=
    compileExpr_exec eV (sb + 1) (sb + 2) (by omega) (run k1 rr) segB
  have segS : SegmentAt (run k2 (run k1 rr)).program (run k2 (run k1 rr)).pc
      [Instruction.store (sb + 1) sb] := by
    rw [hprog2, hprog1, hpc2, hpc1]; exact hseg.append_right.append_right
  have hcurS : (run k2 (run k1 rr)).current = Instruction.store (sb + 1) sb := by
    have := current_of_segment 0 segS (by simp) (run k2 (run k1 rr)) rfl rfl; simpa using this
  obtain ⟨sMem, sPc, sRegs, sProg⟩ := step_store (run k2 (run k1 rr)) (sb + 1) sb hcurS
  have hrun : run (k1 + k2 + 1) rr = step (run k2 (run k1 rr)) := by
    rw [show k1 + k2 + 1 = k1 + (k2 + 1) from by omega, run_add, run_succ_right]
  refine ⟨k1 + k2 + 1, ?_, ?_, ?_, ?_, by have hc := cost_assignInd eA eV rr.mem; omega⟩ <;> rw [hrun]
  · rw [sPc, hpc2, hpc1, compileExpr_length, compileExpr_length]; simp only [codeLenP]; omega
  · rw [sMem, hfr2 sb (by omega) (by omega), hrdA, hrdV, hmem2, hmem1,
      bankWrite_eq_writeReg]
    exact (eval_assignInd eA eV rr.mem).symm
  · intro x hx
    rw [sRegs, hfr2 x (by omega) (by omega)]; exact hfr1 x (by omega) (by omega)
  · rw [sProg, hprog2, hprog1]

/-- `compile_exec` for `ifNZ`: evaluate the test, branch, run the chosen arm with scratch
    base `sb+1`, and (for the else arm) jump over the then arm. -/
lemma compile_exec_ifNZ (e : Expr) (t f : Program)
    (iht : ∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile t rr.pc sb) →
      ∃ k, (run k rr).pc = rr.pc + codeLenP t ∧
           (run k rr).mem = Program.eval t rr.mem ∧
           (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost t rr.mem)
    (ihf : ∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile f rr.pc sb) →
      ∃ k, (run k rr).pc = rr.pc + codeLenP f ∧
           (run k rr).mem = Program.eval f rr.mem ∧
           (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost f rr.mem)
    (sb : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.ifNZ e t f) rr.pc sb)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.ifNZ e t f) ∧
      (run k rr).mem = Program.eval (Program.ifNZ e t f) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost (Program.ifNZ e t f) rr.mem := by
  simp only [compile] at hseg
  simp only [List.append_assoc] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hk1⟩ :=
    compileExpr_exec e sb (sb + 1) (by omega) rr hseg.append_left
  have segBr : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.branchIfNZ sb (rr.pc + codeLenE e + codeLenP f + 2)] := by
    rw [hprog1, hpc1]; exact hseg.append_right.append_left
  have hcurBr : (run k1 rr).current =
      Instruction.branchIfNZ sb (rr.pc + codeLenE e + codeLenP f + 2) := by
    have := current_of_segment 0 segBr (by simp) (run k1 rr) rfl rfl; simpa using this
  obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfNZ (run k1 rr) sb _ hcurBr
  have hbrpc : (run k1 rr).pc = rr.pc + codeLenE e := by rw [hpc1, compileExpr_length]
  have hprogbr : (step (run k1 rr)).program = rr.program := by rw [brProg, hprog1]
  have hmembr : (step (run k1 rr)).mem = rr.mem := by rw [brMem, hmem1]
  by_cases hc : e.eval rr.mem = 0
  · have hbrpc0 : (step (run k1 rr)).pc = rr.pc + codeLenE e + 1 := by
      rw [brPc, hrd1, hbrpc]; simp [hc]
    have segF : SegmentAt (step (run k1 rr)).program (step (run k1 rr)).pc
        (compile f (step (run k1 rr)).pc (sb + 1)) := by
      rw [hprogbr, hbrpc0]
      simpa [compileExpr_length] using hseg.append_right.append_right.append_left
    obtain ⟨kf, fpc, fmem, ffr, fprog, hkf⟩ := ihf (sb + 1) (step (run k1 rr)) segF
    have segJ : SegmentAt (run kf (step (run k1 rr))).program (run kf (step (run k1 rr))).pc
        [Instruction.jump (rr.pc + codeLenE e + codeLenP f + codeLenP t + 2)] := by
      rw [fprog, hprogbr, fpc, hbrpc0]
      simpa [compileExpr_length, compile_length] using
        hseg.append_right.append_right.append_right.append_left
    have hcurJ : (run kf (step (run k1 rr))).current =
        Instruction.jump (rr.pc + codeLenE e + codeLenP f + codeLenP t + 2) := by
      have := current_of_segment 0 segJ (by simp) (run kf (step (run k1 rr))) rfl rfl
      simpa using this
    obtain ⟨jPc, jMem, jRegs, jProg⟩ := step_jump (run kf (step (run k1 rr))) _ hcurJ
    have hrunElse : run (k1 + kf + 2) rr = step (run kf (step (run k1 rr))) := by
      rw [show k1 + kf + 2 = (k1 + 1) + kf + 1 from by omega, run_succ_right, run_add,
        run_succ_right]
    have hbound : k1 + kf + 2 + 3 ≤ 8 * Program.cost (Program.ifNZ e t f) rr.mem := by
      rw [hmembr] at hkf
      have hc' := cost_ifNZ e t f rr.mem
      rw [ite_eq_right (by simp [hc])] at hc'
      omega
    refine ⟨k1 + kf + 2, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrunElse]
    · rw [jPc]; simp only [codeLenP]; omega
    · rw [jMem, fmem, hmembr]
      have he := eval_ifNZ e t f rr.mem
      rw [ite_eq_right (by simp [hc])] at he
      exact he.symm
    · intro x hx; rw [jRegs, ffr x (by omega), brRegs]; exact hfr1 x (by omega) (by omega)
    · rw [jProg, fprog, hprogbr]
  · have hbrpc1 : (step (run k1 rr)).pc = rr.pc + codeLenE e + codeLenP f + 2 := by
      rw [brPc, hrd1]; simp [hc]
    have segT : SegmentAt (step (run k1 rr)).program (step (run k1 rr)).pc
        (compile t (step (run k1 rr)).pc (sb + 1)) := by
      have h := hseg.append_right.append_right.append_right.append_right
      rw [compileExpr_length, compile_length] at h
      simp only [List.length_cons, List.length_nil] at h
      rw [show rr.pc + codeLenE e + 1 + codeLenP f + 1
        = rr.pc + codeLenE e + codeLenP f + 2 from by omega] at h
      rw [hprogbr, hbrpc1]; exact h
    obtain ⟨kt, tpc, tmem, tfr, tprog, hkt⟩ := iht (sb + 1) (step (run k1 rr)) segT
    have hrunThen : run (k1 + kt + 1) rr = run kt (step (run k1 rr)) := by
      rw [show k1 + kt + 1 = (k1 + 1) + kt from by omega, run_add, run_succ_right]
    have hbound : k1 + kt + 1 + 3 ≤ 8 * Program.cost (Program.ifNZ e t f) rr.mem := by
      rw [hmembr] at hkt
      have hc' := cost_ifNZ e t f rr.mem
      rw [ite_eq_left hc] at hc'
      omega
    refine ⟨k1 + kt + 1, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrunThen]
    · rw [tpc, hbrpc1]; simp only [codeLenP]; omega
    · rw [tmem, hmembr]
      have he := eval_ifNZ e t f rr.mem
      rw [ite_eq_left hc] at he
      exact he.symm
    · intro x hx; rw [tfr x (by omega), brRegs]; exact hfr1 x (by omega) (by omega)
    · rw [tprog, hprogbr]

/-- `compile_exec` for `forN`: evaluate the bound, initialise the counter and increment
    registers, then run the loop (`forN_loop`). -/
lemma compile_exec_forN (n : Expr) (body : Program)
    (ihbody : ∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile body rr.pc sb) →
      ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
           (run k rr).mem = Program.eval body rr.mem ∧
           (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost body rr.mem)
    (sb : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.forN n body) rr.pc sb)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.forN n body) ∧
      (run k rr).mem = Program.eval (Program.forN n body) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost (Program.forN n body) rr.mem := by
  simp only [compile] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hk1⟩ :=
    compileExpr_exec n (sb + 1) (sb + 3) (by omega) rr hseg.append_left.append_left
  have seg2 : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.loadImm sb 0, Instruction.loadImm (sb + 2) 1] := by
    rw [hprog1, hpc1]; exact hseg.append_left.append_right
  have hcurL0 : (run k1 rr).current = Instruction.loadImm sb 0 := by
    have := current_of_segment 0 seg2 (by simp) (run k1 rr) rfl rfl; simpa using this
  obtain ⟨l0regs, l0pc, l0mem, l0prog, l0fr⟩ := step_loadImm (run k1 rr) sb 0 hcurL0
  have hcurL1 : (step (run k1 rr)).current = Instruction.loadImm (sb + 2) 1 := by
    have := current_of_segment 1 seg2 (by simp) (step (run k1 rr)) l0pc l0prog; simpa using this
  obtain ⟨l1regs, l1pc, l1mem, l1prog, l1fr⟩ := step_loadImm (step (run k1 rr)) (sb + 2) 1 hcurL1
  have hsL : run (k1 + 2) rr = step (step (run k1 rr)) := by
    rw [show k1 + 2 = k1 + 1 + 1 from rfl, run_succ_right, run_succ_right]
  have hsLpc : (step (step (run k1 rr))).pc = rr.pc + codeLenE n + 2 := by
    rw [l1pc, l0pc, hpc1, compileExpr_length]
  have hsLprog : (step (step (run k1 rr))).program = rr.program := by
    rw [l1prog, l0prog, hprog1]
  have hsLmem : (step (step (run k1 rr))).mem = rr.mem := by rw [l1mem, l0mem, hmem1]
  have hsLsb0 : (step (step (run k1 rr))).regs sb = 0 := by rw [l1fr sb (by omega), l0regs]
  have hsLb1 : (step (step (run k1 rr))).regs (sb + 1) = n.eval rr.mem := by
    rw [l1fr (sb + 1) (by omega), l0fr (sb + 1) (by omega), hrd1]
  have hsLfr : ∀ x, x < sb → (step (step (run k1 rr))).regs x = rr.regs x := by
    intro x hx; rw [l1fr x (by omega), l0fr x (by omega), hfr1 x (by omega) (by omega)]
  have hsegL : SegmentAt (step (step (run k1 rr))).program (rr.pc + codeLenE n + 2)
      ([Instruction.branchIfLt sb (sb + 1) (rr.pc + codeLenE n + 4),
        Instruction.jump (rr.pc + codeLenE n + codeLenP body + 6)] ++
       compile body (rr.pc + codeLenE n + 4) (sb + 3) ++
       [Instruction.add sb sb (sb + 2), Instruction.jump (rr.pc + codeLenE n + 2)]) := by
    rw [hsLprog]
    have hb := hseg.append_right
    simp only [List.length_append, List.length_cons, List.length_nil, compileExpr_length] at hb
    rw [show rr.pc + codeLenE n + 2 = rr.pc + (codeLenE n + 2) from by omega]; exact hb
  obtain ⟨kL, Lpc, Lmem, Lfr, Lprog, hkL⟩ :=
    forN_loop body sb rr.pc (codeLenE n) (n.eval rr.mem)
      (fun rr' h => ihbody (sb + 3) rr' h) (n.eval rr.mem) (step (step (run k1 rr)))
      hsegL hsLpc hsLb1 l1regs (by rw [hsLsb0]; omega)
  have hrunTot : run (k1 + 2 + kL) rr = run kL (step (step (run k1 rr))) := by
    rw [run_add, hsL]
  have hbound : k1 + 2 + kL + 3 ≤ 8 * Program.cost (Program.forN n body) rr.mem := by
    rw [hsLmem] at hkL
    have hc := cost_forN n body rr.mem
    omega
  refine ⟨k1 + 2 + kL, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrunTot]
  · rw [Lpc]; simp only [codeLenP]; omega
  · rw [Lmem, hsLmem]
    exact (eval_forN n body rr.mem).symm
  · intro x hx; rw [Lfr x hx, hsLfr x hx]
  · rw [Lprog, hsLprog]

/-- `compile_exec` for `lookup`: stage the key and result registers, run the unrolled
    pair iterations (`compileLookupIters_exec`), then store the result. -/
lemma compile_exec_lookup (pairs : List (ℕ × ℕ)) (kReg vReg sb : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.lookup pairs kReg vReg) rr.pc sb)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.lookup pairs kReg vReg) ∧
      (run k rr).mem = Program.eval (Program.lookup pairs kReg vReg) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost (Program.lookup pairs kReg vReg) rr.mem := by
  simp only [compile] at hseg
  have seg3 : SegmentAt rr.program rr.pc
      [Instruction.loadImm sb kReg, Instruction.load (sb + 1) sb,
       Instruction.loadImm (sb + 2) 0] := hseg.append_left.append_left
  have hc0 : rr.current = Instruction.loadImm sb kReg := by
    have := current_of_segment 0 seg3 (by simp) rr rfl rfl; simpa using this
  obtain ⟨p0regs, p0pc, p0mem, p0prog, p0fr⟩ := step_loadImm rr sb kReg hc0
  have hc1 : (step rr).current = Instruction.load (sb + 1) sb := by
    have := current_of_segment 1 seg3 (by simp) (step rr) p0pc p0prog; simpa using this
  obtain ⟨p1regs, p1pc, p1mem, p1prog, p1fr⟩ := step_load (step rr) (sb + 1) sb hc1
  have hp2pc : (step (step rr)).pc = rr.pc + 2 := by rw [p1pc, p0pc]
  have hp2prog : (step (step rr)).program = rr.program := by rw [p1prog, p0prog]
  have hc2 : (step (step rr)).current = Instruction.loadImm (sb + 2) 0 := by
    have := current_of_segment 2 seg3 (by simp) (step (step rr)) hp2pc hp2prog; simpa using this
  obtain ⟨p2regs, p2pc, p2mem, p2prog, p2fr⟩ := step_loadImm (step (step rr)) (sb + 2) 0 hc2
  have hstep3 : run 3 rr = step (step (step rr)) := rfl
  have hMpc : (run 3 rr).pc = rr.pc + 3 := by rw [hstep3, p2pc, p1pc, p0pc]
  have hMprog : (run 3 rr).program = rr.program := by rw [hstep3, p2prog, p1prog, p0prog]
  have hMmem : (run 3 rr).mem = rr.mem := by rw [hstep3, p2mem, p1mem, p0mem]
  have hMkey : (run 3 rr).regs (sb + 1) = rr.mem kReg := by
    rw [hstep3, p2fr (sb + 1) (by omega), p1regs, p0mem, p0regs]
  have hMres0 : (run 3 rr).regs (sb + 2) = 0 := by rw [hstep3, p2regs]
  have hMfr : ∀ x, x < sb → (run 3 rr).regs x = rr.regs x := by
    intro x hx; rw [hstep3, p2fr x (by omega), p1fr x (by omega), p0fr x (by omega)]
  have segLookup : SegmentAt (run 3 rr).program (run 3 rr).pc
      (compileLookupIters pairs.reverse (sb + 1) (sb + 2) sb (run 3 rr).pc) := by
    rw [hMprog, hMpc]; simpa using hseg.append_left.append_right
  obtain ⟨kI, Ipc, Imem, Ires, Ifr, Iprog, Ihk⟩ :=
    compileLookupIters_exec (sb + 1) (sb + 2) sb (by omega) (by omega) (by omega)
      pairs.reverse (run 3 rr) segLookup
  have segLast : SegmentAt (run kI (run 3 rr)).program (run kI (run 3 rr)).pc
      [Instruction.loadImm sb vReg, Instruction.store (sb + 2) sb] := by
    rw [Iprog, hMprog, Ipc, hMpc]
    have hb := hseg.append_right
    simp only [List.length_append, List.length_cons, List.length_nil,
      compileLookupIters_length] at hb
    rw [show rr.pc + 3 + 5 * pairs.reverse.length
      = rr.pc + (3 + 5 * pairs.reverse.length) from by omega]
    exact hb
  have hcL0 : (run kI (run 3 rr)).current = Instruction.loadImm sb vReg := by
    have := current_of_segment 0 segLast (by simp) (run kI (run 3 rr)) rfl rfl; simpa using this
  obtain ⟨L0regs, L0pc, L0mem, L0prog, L0fr⟩ := step_loadImm (run kI (run 3 rr)) sb vReg hcL0
  have hcL1 : (step (run kI (run 3 rr))).current = Instruction.store (sb + 2) sb := by
    have := current_of_segment 1 segLast (by simp) (step (run kI (run 3 rr))) L0pc L0prog
    simpa using this
  obtain ⟨L1mem, L1pc, L1regs, L1prog⟩ := step_store (step (run kI (run 3 rr))) (sb + 2) sb hcL1
  have hrunTot : run (3 + kI + 2) rr = step (step (run kI (run 3 rr))) := by
    rw [show 3 + kI + 2 = 3 + kI + 1 + 1 from by omega, run_succ_right, run_succ_right, run_add]
  have hbound : 3 + kI + 2 + 3 ≤ 8 * Program.cost (Program.lookup pairs kReg vReg) rr.mem := by
    rw [List.length_reverse] at Ihk
    have hc := cost_lookup pairs kReg vReg rr.mem
    omega
  refine ⟨3 + kI + 2, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrunTot]
  · rw [L1pc, L0pc, Ipc, hMpc, List.length_reverse]; simp only [codeLenP]; omega
  · rw [L1mem, L0regs, L0fr (sb + 2) (by omega), Ires, hMkey, hMres0, lookupFold_reverse,
      L0mem, Imem, hMmem, bankWrite_eq_writeReg]
    exact (eval_lookup pairs kReg vReg rr.mem).symm
  · intro x hx
    rw [L1regs, L0fr x (by omega), Ifr x (by omega) (by omega), hMfr x hx]
  · rw [L1prog, L0prog, Iprog, hMprog]

lemma compile_exec : ∀ (p : Program) (sb : ℕ) (rr : RAM),
    SegmentAt rr.program rr.pc (compile p rr.pc sb) →
    ∃ k, (run k rr).pc = rr.pc + codeLenP p ∧
         (run k rr).mem = Program.eval p rr.mem ∧
         (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
         (run k rr).program = rr.program ∧ k + 3 ≤ 8 * Program.cost p rr.mem := by
  intro p
  induction p with
  | skip =>
      intro sb rr _
      exact ⟨0, by simp [codeLenP], (eval_skip rr.mem).symm, fun x _ => rfl, rfl,
        by have hc := cost_skip rr.mem; omega⟩
  | assign r e => exact fun sb rr hseg => compile_exec_assign r e sb rr hseg
  | assignInd eA eV => exact fun sb rr hseg => compile_exec_assignInd eA eV sb rr hseg
  | seq p1 p2 ih1 ih2 =>
      intro sb rr hseg
      simp only [compile] at hseg
      obtain ⟨k1, hpc1, hmem1, hfr1, hprog1, hk1⟩ := ih1 sb rr hseg.append_left
      have seg2 : SegmentAt (run k1 rr).program (run k1 rr).pc
          (compile p2 (run k1 rr).pc sb) := by
        rw [hprog1, hpc1]
        have h := hseg.append_right
        rw [compile_length] at h; exact h
      obtain ⟨k2, hpc2, hmem2, hfr2, hprog2, hk2⟩ := ih2 sb (run k1 rr) seg2
      have hrun : run (k1 + k2) rr = run k2 (run k1 rr) := run_add k1 k2 rr
      have hbound : k1 + k2 + 3 ≤ 8 * Program.cost (Program.seq p1 p2) rr.mem := by
        rw [hmem1] at hk2
        have hc := cost_seq p1 p2 rr.mem
        omega
      refine ⟨k1 + k2, ?_, ?_, ?_, ?_, hbound⟩ <;> rw [hrun]
      · rw [hpc2, hpc1]; simp only [codeLenP]; omega
      · rw [hmem2, hmem1]
        exact (eval_seq p1 p2 rr.mem).symm
      · intro x hx; rw [hfr2 x hx]; exact hfr1 x hx
      · rw [hprog2, hprog1]
  | ifNZ e t f iht ihf => exact fun sb rr hseg => compile_exec_ifNZ e t f iht ihf sb rr hseg
  | forN n body ihbody => exact fun sb rr hseg => compile_exec_forN n body ihbody sb rr hseg
  | scanList xs r body ihbody =>
      intro sb rr hseg
      simp only [compile] at hseg
      obtain ⟨k, hpc, hmem, hfr, hprog, hk⟩ := compileScanList_exec body r sb ihbody xs rr hseg
      exact ⟨k, by rw [hpc]; simp only [codeLenP], hmem.trans (eval_scanList xs r body rr.mem).symm,
        hfr, hprog, by have hc := cost_scanList xs r body rr.mem; omega⟩
  | lookup pairs kReg vReg => exact fun sb rr hseg => compile_exec_lookup pairs kReg vReg sb rr hseg

/-! ## Runtime bit-cost accumulation

`compile_exec` bounds the *step count*.  The RAM's `cost` field additionally
accumulates each executed instruction's bit-cost, so a runtime-cost bound needs a
per-step bit-cost bound.  `cost_step_eq`/`cost_run_le` turn a uniform per-step
bit-cost bound `D` into a total-cost bound `k * D` — the arithmetic core.

A *derived* bound on `D` (from an initial store bound `B₀` alone) does not hold for
every `Program`: a `mul` nested inside a `forN` loop can square a single cell's
value every iteration, blowing its `bitLen` up exponentially in the iteration
count, while `Program.cost` (a plain operation count) stays linear. So
`DynamicOperandsLe`/`ProgramImmediatesLe`/`compile_exec_cost` below take the
per-step operand bound `W` as a *hypothesis* on the run rather than deriving it —
`W` must come from a source-level value invariant proved separately for each
concrete validator instantiation. -/

/-- One `step` adds exactly the current instruction's bit-cost to `cost`. -/
lemma cost_step_eq (r : RAM) :
    (step r).cost = r.cost + instructionCost r.regs r.mem r.current := by
  cases hcur : r.current <;> simp [step, hcur, instructionCost]

/-- If every one of the first `k` steps has bit-cost at most `D`, the accumulated
    cost grows by at most `k * D`. -/
lemma cost_run_le (D : ℕ) : ∀ (k : ℕ) (r : RAM),
    (∀ j, j < k →
      instructionCost (run j r).regs (run j r).mem (run j r).current ≤ D) →
    (run k r).cost ≤ r.cost + k * D := by
  intro k
  induction k with
  | zero => intro r _; simp
  | succ k ih =>
      intro r hstep
      have h0 : instructionCost r.regs r.mem r.current ≤ D := by
        have := hstep 0 (by omega); simpa using this
      have hstep' : ∀ j, j < k → instructionCost (run j (step r)).regs
          (run j (step r)).mem (run j (step r)).current ≤ D := by
        intro j hj
        have := hstep (j + 1) (by omega); rwa [run_succ] at this
      have hcost : (step r).cost ≤ r.cost + D := by rw [cost_step_eq]; omega
      calc (run (k + 1) r).cost = (run k (step r)).cost := by rw [run_succ]
        _ ≤ (step r).cost + k * D := ih (step r) hstep'
        _ ≤ r.cost + D + k * D := by omega
        _ = r.cost + (k + 1) * D := by rw [Nat.succ_mul]; omega

/-- No `step` branch touches the `program` field: RAM programs are immutable
    during execution. -/
@[simp] lemma step_program (r : RAM) : (step r).program = r.program := by
  cases hcur : r.current <;> simp [step, hcur]

/-- `program` is `run`-invariant, by iterating `step_program`. -/
lemma run_program (k : ℕ) (r : RAM) : (run k r).program = r.program := by
  induction k generalizing r with
  | zero => simp
  | succ k ih => rw [run_succ, ih, step_program]

/-- A `loadImm` current instruction was fetched from `program`: `RAM.current`
    only synthesizes `halt` past the program's end, and `halt` is a different
    constructor, so a `loadImm` current instruction cannot be that default. -/
lemma current_loadImm_mem {r : RAM} {dst n : ℕ} (h : r.current = Instruction.loadImm dst n) :
    r.current ∈ r.program := by
  rw [h]
  have h' : r.program.getD r.pc Instruction.halt = Instruction.loadImm dst n := by
    unfold RAM.current at h; exact h
  rw [List.getD_eq_getElem?_getD] at h'
  rcases hopt : r.program[r.pc]? with _ | i
  · rw [hopt] at h'; simp at h'
  · rw [hopt] at h'
    simp only [Option.getD_some] at h'
    rw [← h']
    exact List.mem_of_getElem? hopt

/-- The register/memory operands actually read by `r`'s current instruction have
    `bitLen` at most `W`.  Deliberately weaker than a uniform bound on every bank
    cell (see the module comment): only the cells an instruction touches at that
    step need bounding. -/
@[construction_api] def DynamicOperandsLe (W : ℕ) (r : RAM) : Prop :=
  match r.current with
  | Instruction.loadImm _ _ => True
  | Instruction.move _ rs => bitLen (r.regs rs) ≤ W
  | Instruction.load _ rAddr => bitLen (r.regs rAddr) ≤ W ∧ bitLen (r.mem (r.regs rAddr)) ≤ W
  | Instruction.store rSrc rAddr => bitLen (r.regs rAddr) ≤ W ∧ bitLen (r.regs rSrc) ≤ W
  | Instruction.add _ rs rt => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.sub _ rs rt => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.mul _ rs rt => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.setIfLt _ rs rt => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.setIfEq _ rs rt => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.branchIfLt rs rt _ => bitLen (r.regs rs) ≤ W ∧ bitLen (r.regs rt) ≤ W
  | Instruction.branchIfNZ rs _ => bitLen (r.regs rs) ≤ W
  | Instruction.jump _ => True
  | Instruction.halt => True

/-- `DynamicOperandsLe` is monotone in its threshold: a bound at a smaller `W1` transfers to any
    larger `W2`. -/
@[construction_api] lemma DynamicOperandsLe.mono {W1 W2 : ℕ} {r : RAM} (h : W1 ≤ W2)
    (hd : DynamicOperandsLe W1 r) : DynamicOperandsLe W2 r := by
  cases hc : r.current <;> simp only [DynamicOperandsLe, hc] at hd ⊢ <;>
    first
      | exact hd.trans h
      | exact ⟨hd.1.trans h, hd.2.trans h⟩

/-- Every `loadImm` immediate in `program` has `bitLen` at most `I`.  Jump/branch
    targets and register indices are not `instructionCost`-charged, so they are
    excluded. -/
def ProgramImmediatesLe (I : ℕ) (program : List Instruction) : Prop :=
  ∀ i ∈ program, ∀ dst n, i = Instruction.loadImm dst n → bitLen n ≤ I

/-- `DynamicOperandsLe W` holds at every one of the first `k` steps of running `r`. -/
@[construction_api] def RunDynLe (W k : ℕ) (r : RAM) : Prop :=
  ∀ j, j < k → DynamicOperandsLe W (run j r)

/-- Per-step bit-cost is bounded once the operands an instruction actually reads
    (`DynamicOperandsLe`) and the program's `loadImm` immediates
    (`ProgramImmediatesLe`) are both bounded. -/
lemma instructionCost_le_of_dynamic_operands {W I : ℕ} {r : RAM}
    (hdyn : DynamicOperandsLe W r) (himm : ProgramImmediatesLe I r.program) :
    instructionCost r.regs r.mem r.current ≤ 2 * max W I + 1 := by
  unfold DynamicOperandsLe at hdyn
  cases hcur : r.current with
  | loadImm dst n =>
      have hn : bitLen n ≤ I := himm r.current (current_loadImm_mem hcur) dst n hcur
      simp only [instructionCost]; omega
  | move _ rs => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | load _ rAddr => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | store rSrc rAddr => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | add _ rs rt => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | sub _ rs rt => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | mul _ rs rt => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | setIfLt _ rs rt => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | setIfEq _ rs rt => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | branchIfLt rs rt _ => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | branchIfNZ rs _ => simp only [instructionCost]; rw [hcur] at hdyn; omega
  | jump _ => simp only [instructionCost]; omega
  | halt => simp only [instructionCost]; omega

/-- `compile_exec` extended with a conditional bit-cost bound: given a
    `loadImm`-immediate bound `I` on the whole program, *any* dynamic operand
    bound `W` that holds at every step of the run (`RunDynLe`) bounds the
    accumulated `RAM.cost` by `steps * (2 * max W I + 1)`, with `steps` the
    existing step-count bound.  `W` is a hypothesis, not derived (module
    comment): it must come from a source-level value invariant proved
    separately per concrete validator instantiation. -/
lemma compile_exec_cost (p : Program) (sb : ℕ) (rr : RAM) (I : ℕ)
    (hseg : SegmentAt rr.program rr.pc (compile p rr.pc sb))
    (himm : ProgramImmediatesLe I rr.program) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP p ∧
         (run k rr).mem = Program.eval p rr.mem ∧
         (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
         (run k rr).program = rr.program ∧
         k + 3 ≤ 8 * Program.cost p rr.mem ∧
         ∀ W, RunDynLe W k rr →
           (run k rr).cost ≤ rr.cost + (8 * Program.cost p rr.mem) * (2 * max W I + 1) := by
  obtain ⟨k, hpc, hmem, hfr, hprog, hk⟩ := compile_exec p sb rr hseg
  refine ⟨k, hpc, hmem, hfr, hprog, hk, ?_⟩
  intro W hdyn
  have hstep : ∀ j, j < k →
      instructionCost (run j rr).regs (run j rr).mem (run j rr).current ≤ 2 * max W I + 1 := by
    intro j hj
    apply instructionCost_le_of_dynamic_operands (hdyn j hj)
    rw [run_program]
    exact himm
  have hcost := cost_run_le (2 * max W I + 1) k rr hstep
  have hkle : k ≤ 8 * Program.cost p rr.mem := by omega
  have hfinal := Nat.mul_le_mul_right (2 * max W I + 1) hkle
  omega

/-! ## A generic `ProgramImmediatesLe` witness

`compile_exec_cost` takes `ProgramImmediatesLe I rr.program` as a hypothesis rather than
deriving it, but unlike `DynamicOperandsLe`'s `W` (genuinely runtime-dependent, module
comment), every `loadImm` immediate `compile`/`compileExpr`/`compileScanList`/
`compileLookupIters` emit is a *literal* already present in the source `Program`/`Expr` AST
(a constant, a register index, or a `scanList`/`lookup` table entry) — never a value computed
at runtime. So a bound is available unconditionally, computed by structural recursion over the
same AST `compile` itself recurses on. `ProgramImmediatesLe.mono`/`.append`/`.nil` are the
composition lemmas the recursion below repeatedly falls back on: every compiled block is either
a literal instruction list (checked directly against its own immediates) or built from `++`. -/

lemma ProgramImmediatesLe.mono {I J : ℕ} (hIJ : I ≤ J) {prog : List Instruction}
    (h : ProgramImmediatesLe I prog) : ProgramImmediatesLe J prog :=
  fun i hi d n hin => le_trans (h i hi d n hin) hIJ

lemma ProgramImmediatesLe.append {I : ℕ} {c1 c2 : List Instruction}
    (h1 : ProgramImmediatesLe I c1) (h2 : ProgramImmediatesLe I c2) :
    ProgramImmediatesLe I (c1 ++ c2) := by
  intro i hi d n hin
  rcases List.mem_append.mp hi with h | h
  · exact h1 i h d n hin
  · exact h2 i h d n hin

lemma ProgramImmediatesLe.nil {I : ℕ} : ProgramImmediatesLe I ([] : List Instruction) := by
  intro i hi; simp at hi

/-- `bitLen n = Nat.log2 n + 1` is never `0`, so the constants `compile` itself emits
    (`forN`'s loop counter reset to `0`/`1`, `lookup`'s scan-miss flag `0`) are always covered
    by any bound already dominated by some other `bitLen _` term. -/
lemma bitLen_ge_one (n : ℕ) : 1 ≤ bitLen n := by simp only [bitLen]; omega

/-- Every literal immediate `compileExpr` can emit: `const`'s own value, or `reg`'s register
    index (staged through a `loadImm` before the `load`). Recursive nodes just propagate their
    operands' bounds. -/
def exprImmBound : Expr → ℕ
  | .const n => bitLen n
  | .reg r => bitLen r
  | .regInd e => exprImmBound e
  | .add e1 e2 => max (exprImmBound e1) (exprImmBound e2)
  | .sub e1 e2 => max (exprImmBound e1) (exprImmBound e2)
  | .mul e1 e2 => max (exprImmBound e1) (exprImmBound e2)
  | .lt e1 e2 => max (exprImmBound e1) (exprImmBound e2)
  | .eq e1 e2 => max (exprImmBound e1) (exprImmBound e2)

lemma programImmediatesLe_compileExpr (e : Expr) (dst sb : ℕ) :
    ProgramImmediatesLe (exprImmBound e) (compileExpr e dst sb) := by
  induction e generalizing dst sb with
  | const n =>
      simp only [compileExpr, exprImmBound]
      intro i hi d n hin
      simp only [List.mem_singleton] at hi; subst hi
      simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
      exact le_rfl
  | reg r =>
      simp only [compileExpr, exprImmBound]
      intro i hi d n hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
        exact le_rfl
      · subst hi; exact absurd hin (by simp)
  | regInd e ih =>
      simp only [compileExpr, exprImmBound]
      exact ProgramImmediatesLe.append (ih dst sb) (fun i hi d n hin => absurd hin (by simp_all))
  | add e1 e2 ih1 ih2 | sub e1 e2 ih1 ih2 | mul e1 e2 ih1 ih2
  | lt e1 e2 ih1 ih2 | eq e1 e2 ih1 ih2 =>
      simp only [compileExpr, exprImmBound]
      refine ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_
      · exact ProgramImmediatesLe.mono (by omega) (ih1 sb (sb + 2))
      · exact ProgramImmediatesLe.mono (by omega) (ih2 (sb + 1) (sb + 2))
      · exact fun i hi d n hin => absurd hin (by simp_all)

/-- Every literal key/value in a `lookup` table (`compileLookupIters`'s own `k`/`v` per pair). -/
def pairsImmBound (pairs : List (ℕ × ℕ)) : ℕ :=
  pairs.foldr (fun kv acc => max (bitLen kv.1) (max (bitLen kv.2) acc)) 0

lemma pairsImmBound_cons (k v : ℕ) (rest : List (ℕ × ℕ)) :
    pairsImmBound ((k, v) :: rest) = max (bitLen k) (max (bitLen v) (pairsImmBound rest)) := rfl

lemma programImmediatesLe_compileLookupIters_five (k v keyReg resReg sb pc I : ℕ)
    (hk : bitLen k ≤ I) (hv : bitLen v ≤ I) :
    ProgramImmediatesLe I
      [Instruction.loadImm (sb + 3) k, Instruction.setIfEq (sb + 4) keyReg (sb + 3),
       Instruction.branchIfNZ (sb + 4) (pc + 4), Instruction.jump (pc + 5),
       Instruction.loadImm resReg v] := by
  intro i hi d n hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi
  · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; exact hk
  · subst hi; exact absurd hin (by simp)
  · subst hi; exact absurd hin (by simp)
  · subst hi; exact absurd hin (by simp)
  · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; exact hv

lemma programImmediatesLe_compileLookupIters (pairs : List (ℕ × ℕ)) (keyReg resReg sb pc : ℕ) :
    ProgramImmediatesLe (pairsImmBound pairs) (compileLookupIters pairs keyReg resReg sb pc) := by
  induction pairs generalizing pc with
  | nil => exact ProgramImmediatesLe.nil
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      rw [pairsImmBound_cons]
      simp only [compileLookupIters]
      exact ProgramImmediatesLe.append
        (programImmediatesLe_compileLookupIters_five k v keyReg resReg sb pc _ (by omega) (by omega))
        (ProgramImmediatesLe.mono (by omega) (ih (pc + 5)))

/-- Every literal element a `scanList` unrolls (`compileScanList`'s own `x` per list entry). -/
def xsImmBound (xs : List ℕ) : ℕ := xs.foldr (fun x acc => max (bitLen x) acc) 0

lemma xsImmBound_cons (x : ℕ) (xs : List ℕ) :
    xsImmBound (x :: xs) = max (bitLen x) (xsImmBound xs) := rfl

lemma programImmediatesLe_scanList_three (r x sb I : ℕ) (hr : bitLen r ≤ I) (hx : bitLen x ≤ I) :
    ProgramImmediatesLe I
      [Instruction.loadImm sb r, Instruction.loadImm (sb + 1) x, Instruction.store (sb + 1) sb] := by
  intro i hi d n hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi
  · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; exact hr
  · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; exact hx
  · subst hi; exact absurd hin (by simp)

/-- `ifNZ`'s own bound: the condition's immediates, plus those of both branches. -/
lemma programImmediatesLe_compile_ifNZ (e : Expr) (t f : Program) (pc sb : ℕ) {IT IF : ℕ}
    (iht : ∀ pc sb, ProgramImmediatesLe IT (compile t pc sb))
    (ihf : ∀ pc sb, ProgramImmediatesLe IF (compile f pc sb)) :
    ProgramImmediatesLe (max (exprImmBound e) (max IT IF))
      (compileExpr e sb (sb + 1) ++ [Instruction.branchIfNZ sb (pc + codeLenE e + codeLenP f + 2)] ++
        compile f (pc + codeLenE e + 1) (sb + 1) ++
        [Instruction.jump (pc + codeLenE e + codeLenP f + codeLenP t + 2)] ++
        compile t (pc + codeLenE e + codeLenP f + 2) (sb + 1)) := by
  refine ProgramImmediatesLe.append
    (ProgramImmediatesLe.append (ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_) ?_)
    ?_
  · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compileExpr e sb (sb + 1))
  · exact fun i hi d n hin => absurd hin (by simp_all)
  · exact ProgramImmediatesLe.mono (by omega) (ihf (pc + codeLenE e + 1) (sb + 1))
  · exact fun i hi d n hin => absurd hin (by simp_all)
  · exact ProgramImmediatesLe.mono (by omega) (iht (pc + codeLenE e + codeLenP f + 2) (sb + 1))

/-- `forN`'s own bound: the loop bound expression's immediates, the body's, and the loop
    counter reset constants `0`/`1` (covered by `bitLen_ge_one`, factored as a plain `1`). -/
lemma programImmediatesLe_compile_forN (n : Expr) (body : Program) (pc sb : ℕ) {IB : ℕ}
    (ihbody : ∀ pc sb, ProgramImmediatesLe IB (compile body pc sb)) :
    ProgramImmediatesLe (max 1 (max (exprImmBound n) IB))
      (compileExpr n (sb + 1) (sb + 3) ++
        [Instruction.loadImm sb 0, Instruction.loadImm (sb + 2) 1] ++
        ([Instruction.branchIfLt sb (sb + 1) (pc + codeLenE n + 4),
            Instruction.jump (pc + codeLenE n + codeLenP body + 6)] ++
          compile body (pc + codeLenE n + 4) (sb + 3) ++
          [Instruction.add sb sb (sb + 2), Instruction.jump (pc + codeLenE n + 2)])) := by
  refine ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_)
    (ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_)
  · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compileExpr n (sb + 1) (sb + 3))
  · intro i hi d n' hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
      exact le_trans (by decide) (le_max_left _ _)
    · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
      exact le_trans (by decide) (le_max_left _ _)
  · exact fun i hi d n hin => absurd hin (by simp_all)
  · exact ProgramImmediatesLe.mono (by omega) (ihbody (pc + codeLenE n + 4) (sb + 3))
  · exact fun i hi d n hin => absurd hin (by simp_all)

/-- `scanList`'s own bound: nested induction on the unrolled list `xs`, mirroring
    `compileScanList`'s own recursion (`compile_length`'s `scanList` case uses the same nested
    shape) and reusing the *outer* induction's `ihbody` (generalized over `pc`/`sb`) at every
    unrolled copy of `body`. -/
lemma programImmediatesLe_compile_scanList (xs : List ℕ) (r : ℕ) (body : Program) (pc sb : ℕ)
    {IB : ℕ} (ihbody : ∀ pc sb, ProgramImmediatesLe IB (compile body pc sb)) :
    ProgramImmediatesLe (max (bitLen r) (max (xsImmBound xs) IB))
      (compileScanList xs r body pc sb) := by
  induction xs generalizing pc with
  | nil => simp only [compileScanList]; exact ProgramImmediatesLe.nil
  | cons x tail ih =>
      simp only [compileScanList, xsImmBound_cons]
      refine ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_
      · exact ProgramImmediatesLe.mono (by omega)
          (programImmediatesLe_scanList_three r x sb (max (bitLen r) (bitLen x))
            (le_max_left _ _) (le_max_right _ _))
      · exact ProgramImmediatesLe.mono (by omega) (ihbody (pc + 3) (sb + 2))
      · exact ProgramImmediatesLe.mono (by omega) (ih (pc + 3 + codeLenP body))

/-- `lookup`'s own bound: the two register-index immediates plus the table's own `pairsImmBound`
    (over the reversed list `compile` actually feeds `compileLookupIters`). -/
lemma programImmediatesLe_compile_lookup (pairs : List (ℕ × ℕ)) (kReg vReg pc sb : ℕ) :
    ProgramImmediatesLe (max (bitLen kReg) (max (bitLen vReg) (pairsImmBound pairs.reverse)))
      ([Instruction.loadImm sb kReg, Instruction.load (sb + 1) sb, Instruction.loadImm (sb + 2) 0] ++
        compileLookupIters pairs.reverse (sb + 1) (sb + 2) sb (pc + 3) ++
        [Instruction.loadImm sb vReg, Instruction.store (sb + 2) sb]) := by
  refine ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_
  · intro i hi d n hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi
    · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; omega
    · subst hi; exact absurd hin (by simp)
    · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
      exact le_trans (by decide) (le_trans (bitLen_ge_one kReg) (le_max_left _ _))
  · exact ProgramImmediatesLe.mono (by omega)
      (programImmediatesLe_compileLookupIters pairs.reverse (sb + 1) (sb + 2) sb (pc + 3))
  · intro i hi d n hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin; omega
    · subst hi; exact absurd hin (by simp)

/-- Every literal immediate `compile p pc sb` can emit, computed purely from `p`'s own AST
    (`exprImmBound`/`pairsImmBound`/`xsImmBound` at its leaves) — independent of `pc`/`sb`, since
    those only ever address *destination* registers, never `loadImm`'s loaded value. -/
def programImmBound : Program → ℕ
  | .skip => 0
  | .assign r e => max (bitLen r) (exprImmBound e)
  | .assignInd eA eV => max (exprImmBound eA) (exprImmBound eV)
  | .seq p1 p2 => max (programImmBound p1) (programImmBound p2)
  | .ifNZ e t f => max (exprImmBound e) (max (programImmBound t) (programImmBound f))
  | .forN n body => max 1 (max (exprImmBound n) (programImmBound body))
  | .scanList xs r body => max (bitLen r) (max (xsImmBound xs) (programImmBound body))
  | .lookup pairs kReg vReg => max (bitLen kReg) (max (bitLen vReg) (pairsImmBound pairs.reverse))

/-- The compiler bound: for every `p`, each `loadImm` immediate in `compile p pc sb` has bit
    length at most `programImmBound p`. `BoundedWhileDecider.lean` combines it with the
    `outputLoad` bound into `ProgramImmediatesLe` for `fullProgram`. Induction on `p`,
    delegating each multi-instruction constructor to its own lemma above so this induction
    itself stays a plain case dispatch. -/
lemma programImmediatesLe_compile (p : Program) (pc sb : ℕ) :
    ProgramImmediatesLe (programImmBound p) (compile p pc sb) := by
  induction p generalizing pc sb with
  | skip => simp only [compile, programImmBound]; exact ProgramImmediatesLe.nil
  | assign r e =>
      simp only [compile, programImmBound]
      refine ProgramImmediatesLe.append ?_ ?_
      · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compileExpr e sb (sb + 1))
      · intro i hi d n hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi
        · subst hi; simp only [Instruction.loadImm.injEq] at hin; obtain ⟨_, rfl⟩ := hin
          exact le_max_left _ _
        · subst hi; exact absurd hin (by simp)
  | assignInd eA eV =>
      simp only [compile, programImmBound]
      refine ProgramImmediatesLe.append (ProgramImmediatesLe.append ?_ ?_) ?_
      · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compileExpr eA sb (sb + 2))
      · exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compileExpr eV (sb + 1) (sb + 2))
      · exact fun i hi d n hin => absurd hin (by simp_all)
  | seq p1 p2 ih1 ih2 =>
      simp only [compile, programImmBound]
      exact ProgramImmediatesLe.append (ProgramImmediatesLe.mono (by omega) (ih1 pc sb))
        (ProgramImmediatesLe.mono (by omega) (ih2 (pc + codeLenP p1) sb))
  | ifNZ e t f iht ihf =>
      simp only [compile, programImmBound]
      exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compile_ifNZ e t f pc sb iht ihf)
  | forN n body ihbody =>
      simp only [compile, programImmBound]
      exact ProgramImmediatesLe.mono (by omega) (programImmediatesLe_compile_forN n body pc sb ihbody)
  | scanList xs r body ihbody =>
      simp only [compile, programImmBound]
      exact programImmediatesLe_compile_scanList xs r body pc sb ihbody
  | lookup pairs kReg vReg =>
      simp only [compile, programImmBound]
      exact programImmediatesLe_compile_lookup pairs kReg vReg pc sb

/-- The compiler's canonical instance: `compile p 0 0` (the shape `compiledInputRAM`/`Mg` actually
    build) always has a computable `ProgramImmediatesLe` witness. -/
lemma programImmediatesLe_compile_zero (p : Program) :
    ProgramImmediatesLe (programImmBound p) (compile p 0 0) :=
  programImmediatesLe_compile p 0 0

end NPComplete.RAMToTM

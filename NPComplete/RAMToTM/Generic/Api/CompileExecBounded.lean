module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileRefinement
public import Mathlib.Tactic.IntervalCases

/-!
# A value-bounded companion to `compileExpr_exec`/`compile_exec` (`compiled_operands_le`)

`compile_exec`/`compileExpr_exec` (`BoundedWhileRefinement.lean`) certify the *endpoint* of a
compiled run: they say nothing about intermediate steps, so they cannot discharge
`BoundedWhileDecider.compiled_operands_le` (a `DynamicOperandsLe` bound over *every* step of the
run). Unfolding the compiled program step by step makes the proof grow with the program size, so
this module proves the bound structurally instead of replaying the whole run.

This module reuses `compile_exec`'s own step-level building blocks (`step_loadImm`, `step_load`,
`exec_bin`'s pattern, `forN_loop`'s loop induction) — never raw `simp` on `run`/`step` — to prove
a *bounded* companion: if every register/memory cell starts `≤ B`, it *stays* `≤ B` throughout the
compiled run. `RegsMemLe.dynamic_operands_le` then turns that uniform bound into
`DynamicOperandsLe` at every step.

`compileExpr_exec_bounded` covers all 8 `Expr` constructors. `compile_exec_bounded` covers
the six constructors outside `scanList`/`lookup`: `skip`, `assign`, `assignInd`, `seq`,
`ifNZ`, and `forN`. It takes an explicit `ScanFree` hypothesis, since `ProgramBoundedIn`
alone cannot bound the unconstrained `scanList`/`lookup` operations. What remains for a
concrete `compiled_operands_le` instance is applying `compile_exec_bounded` to the chosen
program (discharging `ProgramBoundedIn` for its specific sub-programs) and wiring the result
into a `BoundedWhileDecider` instance.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BitCostRAM
open NPComplete.BoundedWhile

/-- Every register and memory cell of `r` holds a value `≤ B`. -/
def RegsMemLe (B : ℕ) (r : RAM) : Prop := (∀ i, r.regs i ≤ B) ∧ (∀ i, r.mem i ≤ B)

/-- A uniform `RegsMemLe` bound gives `DynamicOperandsLe` (the two operands any instruction
    reads are individual register/memory cells, hence `≤ B`, hence `bitLen ≤ W`). -/
lemma RegsMemLe.dynamic_operands_le {B W : ℕ} {r : RAM} (hB : bitLen B ≤ W) (h : RegsMemLe B r) :
    DynamicOperandsLe W r := by
  obtain ⟨hregs, hmem⟩ := h
  have hb : ∀ i, bitLen (r.regs i) ≤ W := fun i => (bitLen_le_of_le (hregs i)).trans hB
  have hb' : ∀ i, bitLen (r.mem i) ≤ W := fun i => (bitLen_le_of_le (hmem i)).trans hB
  unfold DynamicOperandsLe
  cases r.current <;> simp_all

/-- Bounded companion to `exec_bin`: given bounded execution certificates for the two operand
    blocks and a bound on the combined result, the composed block also keeps every intermediate
    `RegsMemLe B` state. -/
lemma exec_bin_bounded (c1 c2 : List Instruction) (opI : Instruction) (dst sb B : ℕ)
    (r : RAM) (v1 v2 : ℕ) (g : ℕ → ℕ → ℕ)
    (hseg : SegmentAt r.program r.pc (c1 ++ c2 ++ [opI]))
    (hg : g v1 v2 ≤ B)
    (h1 : ∃ k, (run k r).pc = r.pc + c1.length ∧ (run k r).regs sb = v1 ∧
        (run k r).mem = r.mem ∧ (∀ x, x < sb + 2 → x ≠ sb → (run k r).regs x = r.regs x) ∧
        (run k r).program = r.program ∧ ∀ j ≤ k, RegsMemLe B (run j r))
    (h2 : ∀ r1 : RAM, r1.mem = r.mem → SegmentAt r1.program r1.pc c2 → RegsMemLe B r1 →
        ∃ k, (run k r1).pc = r1.pc + c2.length ∧ (run k r1).regs (sb + 1) = v2 ∧
        (run k r1).mem = r1.mem ∧ (∀ x, x < sb + 2 → x ≠ sb + 1 → (run k r1).regs x = r1.regs x) ∧
        (run k r1).program = r1.program ∧ ∀ j ≤ k, RegsMemLe B (run j r1))
    (hop : ∀ rr : RAM, rr.current = opI →
        (step rr).regs dst = g (rr.regs sb) (rr.regs (sb + 1)) ∧
        (step rr).pc = rr.pc + 1 ∧ (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
        ∀ y, y ≠ dst → (step rr).regs y = rr.regs y) :
    ∃ k, (run k r).pc = r.pc + (c1 ++ c2 ++ [opI]).length ∧ (run k r).regs dst = g v1 v2 ∧
        (run k r).mem = r.mem ∧ (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
        (run k r).program = r.program ∧
        ∀ j ≤ k, RegsMemLe B (run j r) := by
  obtain ⟨k1, hpc1, hrsb1, hmem1, hfr1, hprog1, hb1⟩ := h1
  rw [List.append_assoc] at hseg
  have segc2 : SegmentAt r.program (r.pc + c1.length) c2 := hseg.append_right.append_left
  have segop : SegmentAt r.program (r.pc + c1.length + c2.length) [opI] :=
    hseg.append_right.append_right
  have segc2' : SegmentAt (run k1 r).program (run k1 r).pc c2 := by rw [hprog1, hpc1]; exact segc2
  obtain ⟨k2, hpc2, hrsb2, hmem2, hfr2, hprog2, hb2⟩ := h2 (run k1 r) hmem1 segc2' (hb1 k1 le_rfl)
  have hr2pc : (run k2 (run k1 r)).pc = r.pc + c1.length + c2.length := by rw [hpc2, hpc1]
  have hr2prog : (run k2 (run k1 r)).program = r.program := by rw [hprog2, hprog1]
  have hcurop : (run k2 (run k1 r)).current = opI := by
    have hs : SegmentAt (run k2 (run k1 r)).program (run k2 (run k1 r)).pc [opI] := by
      rw [hr2prog, hr2pc]; exact segop
    have := current_of_segment 0 hs (by simp) (run k2 (run k1 r)) rfl rfl; simpa using this
  obtain ⟨hopr, hoppc, hopmem, hopprog, hopfr⟩ := hop (run k2 (run k1 r)) hcurop
  have hrun : run (k1 + k2 + 1) r = step (run k2 (run k1 r)) := by
    rw [show k1 + k2 + 1 = k1 + (k2 + 1) by omega, run_add, run_add]; rfl
  have hrunmid : ∀ m, m ≤ k2 → run (k1 + m) r = run m (run k1 r) := fun m _ => run_add k1 m r
  refine ⟨k1 + k2 + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, hoppc, hr2pc]; simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [hrun, hopr, hfr2 sb (by omega) (by omega), hrsb1, hrsb2]
  · rw [hrun, hopmem, hmem2, hmem1]
  · intro x hx hxd
    rw [hrun, hopfr x hxd, hfr2 x (by omega) (by omega), hfr1 x (by omega) (by omega)]
  · rw [hrun, hopprog, hr2prog]
  · have hv1 : (run k2 (run k1 r)).regs sb = v1 := by
      rw [hfr2 sb (by omega) (by omega)]; exact hrsb1
    intro j hj
    rcases Nat.lt_or_ge j k1 with hj1 | hj1
    · exact hb1 j (by omega)
    rcases Nat.lt_or_ge j (k1 + k2) with hj2 | hj2
    · obtain ⟨m, hm⟩ : ∃ m, j = k1 + m := ⟨j - k1, by omega⟩
      rw [hm, hrunmid m (by omega)]
      exact hb2 m (by omega)
    rcases eq_or_lt_of_le hj2 with hj3 | hj3
    · rw [← hj3, run_add]
      exact hb2 k2 le_rfl
    · have : j = k1 + k2 + 1 := by omega
      subst this
      rw [hrun]
      have hb2k2 := hb2 k2 le_rfl
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = dst
        · rw [hi, hopr, hv1, hrsb2]; exact hg
        · rw [hopfr i hi]; exact hb2k2.1 i
      · intro i; rw [hopmem]; exact hb2k2.2 i

/-- `ExprBoundedIn` constrains constants, register indices, and `regInd` addresses to `≤ B`.
    It also bounds `add`/`mul` results and the left operand value of `sub`. For `lt` and `eq`, only
    the operands are constrained; their `0`/`1` results need `B ≥ 1`, supplied at use sites. -/
@[construction_api] def ExprBoundedIn (B : ℕ) (σ : Store) : Expr → Prop
  | .const n => n ≤ B
  | .reg r => r ≤ B
  | .regInd e => ExprBoundedIn B σ e ∧ e.eval σ ≤ B
  | .add e1 e2 => ExprBoundedIn B σ e1 ∧ ExprBoundedIn B σ e2 ∧ e1.eval σ + e2.eval σ ≤ B
  | .sub e1 e2 => ExprBoundedIn B σ e1 ∧ ExprBoundedIn B σ e2 ∧ e1.eval σ ≤ B
  | .mul e1 e2 => ExprBoundedIn B σ e1 ∧ ExprBoundedIn B σ e2 ∧ e1.eval σ * e2.eval σ ≤ B
  | .lt e1 e2 => ExprBoundedIn B σ e1 ∧ ExprBoundedIn B σ e2
  | .eq e1 e2 => ExprBoundedIn B σ e1 ∧ ExprBoundedIn B σ e2

/-- Induction-hypothesis shape of `compileExpr_exec_bounded`: the bounded execution contract of
    `compileExpr e` for every destination, scratch base and start state. -/
def CompileExprBoundedGoal (B : ℕ) (e : Expr) : Prop :=
  ∀ dst sb : ℕ, dst < sb → ∀ r : RAM, SegmentAt r.program r.pc (compileExpr e dst sb) →
    RegsMemLe B r → ExprBoundedIn B r.mem e →
    ∃ k, (run k r).pc = r.pc + (compileExpr e dst sb).length ∧
      (run k r).regs dst = e.eval r.mem ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r)

/-- `compileExpr_exec_bounded` for `const`: a single `loadImm` keeps all cells `≤ B`. -/
lemma compileExpr_exec_bounded_const (n dst sb B : ℕ) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.const n) dst sb))
    (hr : RegsMemLe B r) (he : ExprBoundedIn B r.mem (Expr.const n)) :
    ∃ k, (run k r).pc = r.pc + (compileExpr (Expr.const n) dst sb).length ∧
      (run k r).regs dst = (Expr.const n).eval r.mem ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r) := by
  simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
  have hcur : r.current = Instruction.loadImm dst n := by
    have := current_of_segment 0 hseg (by simp) r rfl rfl; simpa using this
  obtain ⟨hrr, hp, hm, hpr, hf⟩ := step_loadImm r dst n hcur
  have hrun1 : run 1 r = step r := rfl
  refine ⟨1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun1, hp]; simp
  · rw [hrun1, hrr]
  · rw [hrun1, hm]
  · intro x hx hxd; rw [hrun1]; exact hf x hxd
  · rw [hrun1, hpr]
  · intro j hj
    interval_cases j
    · simpa [run_zero] using hr
    · refine ⟨fun i => ?_, ?_⟩
      · rw [hrun1]
        by_cases hi : i = dst
        · rw [hi, hrr]; exact he
        · rw [hf i hi]; exact hr.1 i
      · rw [hrun1, hm]; exact hr.2

/-- `compileExpr_exec_bounded` for `reg`: stage the address, then `load` it. -/
lemma compileExpr_exec_bounded_reg (r0 dst sb B : ℕ) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.reg r0) dst sb))
    (hr : RegsMemLe B r) (he : ExprBoundedIn B r.mem (Expr.reg r0)) :
    ∃ k, (run k r).pc = r.pc + (compileExpr (Expr.reg r0) dst sb).length ∧
      (run k r).regs dst = (Expr.reg r0).eval r.mem ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r) := by
  simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
  have hcur0 : r.current = Instruction.loadImm sb r0 := by
    have := current_of_segment 0 hseg (by simp) r rfl rfl; simpa using this
  obtain ⟨e0regs, e0pc, e0mem, e0prog, e0fr⟩ := step_loadImm r sb r0 hcur0
  have hcur1 : (step r).current = Instruction.load dst sb := by
    have := current_of_segment 1 hseg (by simp) (step r) e0pc e0prog; simpa using this
  obtain ⟨e1regs, e1pc, e1mem, e1prog, e1fr⟩ := step_load (step r) dst sb hcur1
  have hrun2 : run 2 r = step (step r) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, run_add]; rfl
  have hstep1 : RegsMemLe B (step r) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = sb
      · rw [hi, e0regs]; exact he
      · rw [e0fr i hi]; exact hr.1 i
    · rw [e0mem]; exact hr.2
  refine ⟨2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun2, e1pc, e0pc]; simp
  · rw [hrun2, e1regs, e0mem, e0regs]
  · rw [hrun2, e1mem, e0mem]
  · intro x hx hxd; rw [hrun2, e1fr x hxd, e0fr x (by omega)]
  · rw [hrun2, e1prog, e0prog]
  · intro j hj
    interval_cases j
    · simpa [run_zero] using hr
    · exact hstep1
    · rw [hrun2]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = dst
        · rw [hi, e1regs, e0mem, e0regs]; exact hr.2 r0
        · rw [e1fr i hi]; exact hstep1.1 i
      · rw [e1mem]; exact hstep1.2

/-- `compileExpr_exec_bounded` for `regInd`: run the address expression, then dereference it. -/
lemma compileExpr_exec_bounded_regInd (e : Expr) (dst sb B : ℕ) (hconv : dst < sb)
    (ih : CompileExprBoundedGoal B e) (r : RAM)
    (hseg : SegmentAt r.program r.pc (compileExpr (Expr.regInd e) dst sb))
    (hr : RegsMemLe B r) (he : ExprBoundedIn B r.mem (Expr.regInd e)) :
    ∃ k, (run k r).pc = r.pc + (compileExpr (Expr.regInd e) dst sb).length ∧
      (run k r).regs dst = (Expr.regInd e).eval r.mem ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r) := by
  simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
  obtain ⟨he1, he2⟩ := he
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hb1⟩ := ih dst sb hconv r hseg.append_left hr he1
  have hcurop : (run k1 r).current = Instruction.load dst dst := by
    have hs : SegmentAt (run k1 r).program (run k1 r).pc [Instruction.load dst dst] := by
      rw [hprog1, hpc1]; exact hseg.append_right
    have := current_of_segment 0 hs (by simp) (run k1 r) rfl rfl; simpa using this
  obtain ⟨eR, eP, eM, ePr, eF⟩ := step_load (run k1 r) dst dst hcurop
  have hrun : run (k1 + 1) r = step (run k1 r) := by rw [run_add]; rfl
  have hbk1 := hb1 k1 le_rfl
  have hlast : RegsMemLe B (step (run k1 r)) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = dst
      · rw [hi, eR, hmem1, hrd1]; exact hr.2 (e.eval r.mem)
      · rw [eF i hi]; exact hbk1.1 i
    · intro i; rw [eM]; exact hbk1.2 i
  refine ⟨k1 + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, eP, hpc1]; simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [hrun, eR, hmem1, hrd1]
  · rw [hrun, eM, hmem1]
  · intro x hx hxd; rw [hrun, eF x hxd, hfr1 x hx hxd]
  · rw [hrun, ePr, hprog1]
  · intro j hj
    rcases Nat.lt_or_ge j k1 with hj1 | hj1
    · exact hb1 j (by omega)
    rcases eq_or_lt_of_le hj1 with hj2 | hj2
    · rw [← hj2]; exact hbk1
    · have : j = k1 + 1 := by omega
      subst this
      rw [hrun]; exact hlast

/-- `compileExpr_exec_bounded` for the binary constructors: both operand blocks stay bounded
    (by the induction hypotheses), and the final instruction `opI` computes `g` of the two
    operand values within `B`. -/
lemma compileExpr_exec_bounded_bin (e1 e2 : Expr) (opI : Instruction) (g : ℕ → ℕ → ℕ)
    (dst sb B : ℕ) (r : RAM)
    (ih1 : CompileExprBoundedGoal B e1) (ih2 : CompileExprBoundedGoal B e2)
    (hseg : SegmentAt r.program r.pc
      (compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++ [opI]))
    (hr : RegsMemLe B r) (he1 : ExprBoundedIn B r.mem e1) (he2 : ExprBoundedIn B r.mem e2)
    (hg : g (e1.eval r.mem) (e2.eval r.mem) ≤ B)
    (hop : ∀ rr : RAM, rr.current = opI →
        (step rr).regs dst = g (rr.regs sb) (rr.regs (sb + 1)) ∧
        (step rr).pc = rr.pc + 1 ∧ (step rr).mem = rr.mem ∧ (step rr).program = rr.program ∧
        ∀ y, y ≠ dst → (step rr).regs y = rr.regs y) :
    ∃ k, (run k r).pc = r.pc +
        (compileExpr e1 sb (sb + 2) ++ compileExpr e2 (sb + 1) (sb + 2) ++ [opI]).length ∧
      (run k r).regs dst = g (e1.eval r.mem) (e2.eval r.mem) ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r) :=
  exec_bin_bounded _ _ opI dst sb B r (e1.eval r.mem) (e2.eval r.mem) g hseg hg
    (ih1 sb (sb + 2) (by omega) r hseg.append_left.append_left hr he1)
    (fun r1 hm hs hr1 => by
      rw [← hm]
      exact ih2 (sb + 1) (sb + 2) (by omega) r1 hs hr1 (by rw [hm]; exact he2))
    hop

/-- Bounded companion to `compileExpr_exec`: running the compiled block keeps every register and
    memory cell `≤ B` at every intermediate step, given `r`'s registers/memory started `≤ B` and
    `e`'s own indices/values (`ExprBoundedIn`) stay `≤ B` against `r.mem`. -/
lemma compileExpr_exec_bounded (e : Expr) (dst sb B : ℕ) (hconv : dst < sb) (hB1 : 1 ≤ B)
    (r : RAM) (hseg : SegmentAt r.program r.pc (compileExpr e dst sb))
    (hr : RegsMemLe B r) (he : ExprBoundedIn B r.mem e) :
    ∃ k, (run k r).pc = r.pc + (compileExpr e dst sb).length ∧
      (run k r).regs dst = e.eval r.mem ∧ (run k r).mem = r.mem ∧
      (∀ x, x < sb → x ≠ dst → (run k r).regs x = r.regs x) ∧
      (run k r).program = r.program ∧
      ∀ j ≤ k, RegsMemLe B (run j r) := by
  induction e generalizing dst sb r with
  | const n => exact compileExpr_exec_bounded_const n dst sb B r hseg hr he
  | reg r0 => exact compileExpr_exec_bounded_reg r0 dst sb B r hseg hr he
  | regInd e ih => exact compileExpr_exec_bounded_regInd e dst sb B hconv ih r hseg hr he
  | add e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
    obtain ⟨he1, he2, hesum⟩ := he
    exact compileExpr_exec_bounded_bin e1 e2 _ (· + ·) dst sb B r ih1 ih2 hseg hr he1 he2 hesum
      (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
        by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
  | sub e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
    obtain ⟨he1, he2, he1val⟩ := he
    exact compileExpr_exec_bounded_bin e1 e2 _ (· - ·) dst sb B r ih1 ih2 hseg hr he1 he2
      (Nat.le_trans (Nat.sub_le _ _) he1val)
      (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
        by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
  | mul e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
    obtain ⟨he1, he2, heprod⟩ := he
    exact compileExpr_exec_bounded_bin e1 e2 _ (· * ·) dst sb B r ih1 ih2 hseg hr he1 he2 heprod
      (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
        by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
  | lt e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
    obtain ⟨he1, he2⟩ := he
    exact compileExpr_exec_bounded_bin e1 e2 _ (fun x y => if x < y then 1 else 0) dst sb B r
      ih1 ih2 hseg hr he1 he2 (by split <;> omega)
      (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
        by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)
  | eq e1 e2 ih1 ih2 =>
    simp only [compileExpr, Expr.eval, ExprBoundedIn] at hseg he ⊢
    obtain ⟨he1, he2⟩ := he
    exact compileExpr_exec_bounded_bin e1 e2 _ (fun x y => if x = y then 1 else 0) dst sb B r
      ih1 ih2 hseg hr he1 he2 (by split <;> omega)
      (fun rr hc => ⟨by simp [step, hc], by simp [step, hc], by simp [step, hc],
        by simp [step, hc], fun y hy => by simp only [step, hc]; exact bankWrite_diff _ _ _ _ hy⟩)

/-- `ExprBoundedIn` gives the top-level value bound too, once `σ` itself is uniformly bounded
    (`reg`'s case needs `σ r ≤ B`, not just the register index `r ≤ B`). -/
lemma expr_eval_le_of_bounded_in {B : ℕ} {σ : Store} (hσ : ∀ i, σ i ≤ B) (hB1 : 1 ≤ B) :
    ∀ e : Expr, ExprBoundedIn B σ e → e.eval σ ≤ B
  | .const _, h => h
  | .reg r0, _ => hσ r0
  | .regInd e', _ => hσ (e'.eval σ)
  | .add _ _, h => h.2.2
  | .sub _ _, h => Nat.le_trans (Nat.sub_le _ _) h.2.2
  | .mul _ _, h => h.2.2
  | .lt _ _, _ => by simp only [Expr.eval]; split <;> omega
  | .eq _ _, _ => by simp only [Expr.eval]; split <;> omega

/-- Every DSL address a `Program` assigns to (`assign`'s register `r`, `assignInd`'s evaluated
    address `eA.eval σ`) is `≤ B`, and every expression it evaluates satisfies `ExprBoundedIn B`
    at the store it is evaluated in, along the run from `σ`. `scanList`/`lookup` are `True`
    (unconstrained): this predicate does not track their write targets, so
    `compile_exec_bounded` excludes them with a separate `ScanFree` hypothesis. -/
@[construction_api] def ProgramBoundedIn (B : ℕ) (σ : Store) : Program → Prop
  | .skip => True
  | .assign r e => r ≤ B ∧ ExprBoundedIn B σ e
  | .assignInd eA eV => ExprBoundedIn B σ eA ∧ ExprBoundedIn B σ eV ∧ eA.eval σ ≤ B
  | .seq p1 p2 => ProgramBoundedIn B σ p1 ∧ ProgramBoundedIn B (Program.eval p1 σ) p2
  | .ifNZ e t f => ExprBoundedIn B σ e ∧ ProgramBoundedIn B σ t ∧ ProgramBoundedIn B σ f
  | .forN n body => ExprBoundedIn B σ n ∧ ∀ m' < n.eval σ, ProgramBoundedIn B (loopEval body m' σ) body
   | .scanList _ _ _ => True
   | .lookup _ _ _ => True

@[construction_api] lemma programBoundedIn_assign_iff (B : ℕ) (σ : Store) (r : ℕ) (e : Expr) :
    ProgramBoundedIn B σ (.assign r e) ↔ r ≤ B ∧ ExprBoundedIn B σ e := Iff.rfl

@[construction_api] lemma programBoundedIn_assignInd_iff (B : ℕ) (σ : Store) (a v : Expr) :
    ProgramBoundedIn B σ (.assignInd a v) ↔
      ExprBoundedIn B σ a ∧ ExprBoundedIn B σ v ∧ a.eval σ ≤ B := Iff.rfl

@[construction_api] lemma programBoundedIn_seq_iff (B : ℕ) (σ : Store) (p q : Program) :
    ProgramBoundedIn B σ (.seq p q) ↔
      ProgramBoundedIn B σ p ∧ ProgramBoundedIn B (p.eval σ) q := Iff.rfl

@[construction_api] lemma programBoundedIn_ifNZ_iff (B : ℕ) (σ : Store) (e : Expr)
    (t f : Program) : ProgramBoundedIn B σ (.ifNZ e t f) ↔
      ExprBoundedIn B σ e ∧ ProgramBoundedIn B σ t ∧ ProgramBoundedIn B σ f := Iff.rfl

@[construction_api] lemma programBoundedIn_forN_iff (B : ℕ) (σ : Store) (n : Expr)
    (body : Program) : ProgramBoundedIn B σ (.forN n body) ↔
      ExprBoundedIn B σ n ∧ ∀ i < n.eval σ, ProgramBoundedIn B (loopEval body i σ) body :=
  Iff.rfl

@[construction_api] lemma programBoundedIn_forN_of_indexed (B : ℕ) (σ : Store) (n : Expr)
    (body : Program) (I : ℕ → Store → Prop) (hinit : I 0 σ)
    (hstep : ∀ i < n.eval σ, ∀ τ, I i τ → I (i + 1) (body.eval τ))
    (hbody : ∀ i < n.eval σ, I i (loopEval body i σ) →
      ProgramBoundedIn B (loopEval body i σ) body)
    (hn : ExprBoundedIn B σ n) : ProgramBoundedIn B σ (.forN n body) := by
  refine ⟨hn, ?_⟩
  intro i hi
  apply hbody i hi
  have inv : ∀ j ≤ i, I j (loopEval body j σ) := by
    intro j hj
    induction j with
    | zero => simpa using hinit
    | succ j ih =>
      rw [loopEval_succ_snoc]
      exact hstep j (by omega) _ (ih (by omega))
  exact inv i le_rfl

/-- `ProgramBoundedIn` for `forN` only inspects the bound `Expr` through its entry-store value
    and the loop's own visited-store obligations, so an extensionally equal replacement bound
    (same value, still `≤ B`) preserves it — the uniformization target `.forN (.const N)` to
    `.forN (.reg r)` needs exactly this to reuse a `ProgramBoundedIn` proof for the constant
    bound. -/
lemma programBoundedIn_forN_congr_bound (B : ℕ) (σ : Store) (e₁ e₂ : Expr) (body : Program)
    (hbound : e₁.eval σ = e₂.eval σ) (he₂ : ExprBoundedIn B σ e₂)
    (h : ProgramBoundedIn B σ (Program.forN e₁ body)) :
    ProgramBoundedIn B σ (Program.forN e₂ body) := by
  refine ⟨he₂, ?_⟩
  rw [← hbound]
  exact h.2

/-- A program that does not use the list-scanning operations. -/
@[construction_api] def ScanFree : Program → Prop
  | .skip => True
  | .assign _ _ => True
  | .assignInd _ _ => True
  | .seq p1 p2 => ScanFree p1 ∧ ScanFree p2
  | .ifNZ _ t f => ScanFree t ∧ ScanFree f
  | .forN _ body => ScanFree body
  | .scanList _ _ _ => False
  | .lookup _ _ _ => False

/-- Appending a bounded continuation to a bounded prefix of a run keeps the whole trace bounded. -/
lemma compile_exec_bounded_trace_append (B n k : ℕ) (rr : RAM)
    (hn : ∀ j ≤ n, RegsMemLe B (run j rr))
    (hk : ∀ j ≤ k, RegsMemLe B (run j (run n rr))) :
    ∀ j ≤ n + k, RegsMemLe B (run j rr) := by
  intro j hj
  rcases Nat.lt_or_ge j n with hjn | hjn
  · exact hn j (by omega)
  obtain ⟨m, hm⟩ : ∃ m, j = n + m := ⟨j - n, by omega⟩
  rw [hm, run_add]
  exact hk m (by omega)

/-- Per-call bounded certificate for a loop body, as used by `forN_loop_bounded`. -/
def ForNBodyBoundedGoal (body : Program) (sb B : ℕ) : Prop :=
  ∀ rr : RAM, SegmentAt rr.program rr.pc (compile body rr.pc (sb + 3)) →
    RegsMemLe B rr → ProgramBoundedIn B rr.mem body →
    ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
         (run k rr).mem = Program.eval body rr.mem ∧
         (∀ x, x < sb + 3 → (run k rr).regs x = rr.regs x) ∧
         (run k rr).program = rr.program ∧
         ∀ j ≤ k, RegsMemLe B (run j rr)

/-- The conclusion of `forN_loop_bounded` for a fixed iteration count `m`; the induction
    hypothesis of the loop induction. -/
def ForNLoopBoundedGoal (body : Program) (sb base cn bound B m : ℕ) : Prop :=
  ∀ s : RAM,
    SegmentAt s.program (base + cn + 2)
      ([Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
        Instruction.jump (base + cn + codeLenP body + 6)] ++
       compile body (base + cn + 4) (sb + 3) ++
       [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)]) →
    s.pc = base + cn + 2 → s.regs (sb + 1) = bound → s.regs (sb + 2) = 1 →
    s.regs sb + m = bound → RegsMemLe B s →
    (∀ m' < m, ProgramBoundedIn B (loopEval body m' s.mem) body) →
    ∃ k, (run k s).pc = base + cn + codeLenP body + 6 ∧
         (run k s).mem = loopEval body m s.mem ∧
         (∀ x, x < sb → (run k s).regs x = s.regs x) ∧
         (run k s).program = s.program ∧
         ∀ j ≤ k, RegsMemLe B (run j s)


/-- `forN_loop_bounded` for an exhausted counter: the guard falls through to the exit jump. -/
lemma forN_loop_bounded_zero (body : Program) (sb base cn bound B : ℕ) :
    ForNLoopBoundedGoal body sb base cn bound B 0 := by
  intro s hseg hpc hbound hone hi hrs hpbody
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
  refine ⟨2, ?_, ?_, ?_, ?_, ?_⟩ <;> try rw [show run 2 s = step (step s) from rfl]
  · rw [jPc]
  · rw [jMem, brMem]
    exact (loopEval_zero body s.mem).symm
  · intro x _; rw [jRegs, brRegs]
  · rw [jProg, brProg]
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with h | h | h
    · subst h; simpa [run_zero] using hrs
    · subst h
      rw [show run 1 s = step s from rfl]
      exact ⟨fun i => by rw [brRegs]; exact hrs.1 i, fun i => by rw [brMem]; exact hrs.2 i⟩
    · subst h
      rw [show run 2 s = step (step s) from rfl]
      exact ⟨fun i => by rw [jRegs, brRegs]; exact hrs.1 i,
        fun i => by rw [jMem, brMem]; exact hrs.2 i⟩

/-- `forN_loop_bounded`: when the counter is below the bound, the guard enters the body. -/
lemma forN_loop_bounded_enter (body : Program) (sb base cn : ℕ) (s : RAM)
    (hseg : SegmentAt s.program (base + cn + 2)
      [Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
        Instruction.jump (base + cn + codeLenP body + 6)])
    (hpc : s.pc = base + cn + 2) (hlt : s.regs sb < s.regs (sb + 1)) :
    (step s).pc = base + cn + 4 ∧ (step s).mem = s.mem ∧ (step s).regs = s.regs ∧
      (step s).program = s.program := by
  have hcur0 : s.current = Instruction.branchIfLt sb (sb + 1) (base + cn + 4) := by
    rw [current_eq_getD, hpc]
    simpa using segment_getD hseg (show (0:ℕ) < 2 from by omega)
  obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfLt s sb (sb + 1) _ hcur0
  exact ⟨by rw [brPc]; simp [hlt], brMem, brRegs, brProg⟩

/-- `forN_loop_bounded`: the increment-and-jump-back tail keeps the state bounded, given that
    the incremented counter stays `≤ B`. -/
lemma forN_loop_bounded_tail (sb t B : ℕ) (r : RAM)
    (hseg : SegmentAt r.program r.pc [Instruction.add sb sb (sb + 2), Instruction.jump t])
    (hr : RegsMemLe B r) (hsum : r.regs sb + r.regs (sb + 2) ≤ B) :
    (step (step r)).pc = t ∧ (step (step r)).program = r.program ∧
      (step (step r)).mem = r.mem ∧ (step (step r)).regs sb = r.regs sb + r.regs (sb + 2) ∧
      (∀ x, x ≠ sb → (step (step r)).regs x = r.regs x) ∧
      RegsMemLe B (step r) ∧ RegsMemLe B (step (step r)) := by
  have hcurAdd : r.current = Instruction.add sb sb (sb + 2) := by
    have := current_of_segment 0 hseg (by simp) r rfl rfl; simpa using this
  obtain ⟨addRegs, addPc, addMem, addProg, addFr⟩ := step_add r sb sb (sb + 2) hcurAdd
  have hcurJ : (step r).current = Instruction.jump t := by
    have := current_of_segment 1 hseg (by simp) (step r) addPc addProg
    simpa using this
  obtain ⟨jPc, jMem, jRegs, jProg⟩ := step_jump (step r) _ hcurJ
  have hafter : RegsMemLe B (step r) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = sb
      · rw [hi, addRegs]; exact hsum
      · rw [addFr i hi]; exact hr.1 i
    · rw [addMem]; exact hr.2
  refine ⟨jPc, by rw [jProg, addProg], by rw [jMem, addMem], by rw [jRegs, addRegs],
    fun x hx => by rw [jRegs, addFr x hx], hafter, ?_⟩
  exact ⟨fun i => by rw [jRegs]; exact hafter.1 i, fun i => by rw [jMem]; exact hafter.2 i⟩

/-- `forN_loop_bounded`: one full iteration (guard, body, increment, jump back) returns to the
    loop head with the counter incremented, the memory advanced by `body`, and every
    intermediate state bounded. -/
lemma forN_loop_bounded_iter (body : Program) (sb base cn B : ℕ)
    (ihbody : ForNBodyBoundedGoal body sb B) (s : RAM)
    (hseg : SegmentAt s.program (base + cn + 2)
      ([Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
        Instruction.jump (base + cn + codeLenP body + 6)] ++
       compile body (base + cn + 4) (sb + 3) ++
       [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)]))
    (hpc : s.pc = base + cn + 2) (hone : s.regs (sb + 2) = 1)
    (hlt : s.regs sb < s.regs (sb + 1)) (hrs : RegsMemLe B s)
    (hpbody : ProgramBoundedIn B s.mem body) :
    ∃ k, (run k s).pc = base + cn + 2 ∧ (run k s).regs (sb + 1) = s.regs (sb + 1) ∧
      (run k s).regs (sb + 2) = 1 ∧ (run k s).regs sb = s.regs sb + 1 ∧
      (run k s).mem = Program.eval body s.mem ∧
      (∀ x, x < sb → (run k s).regs x = s.regs x) ∧ (run k s).program = s.program ∧
      ∀ j ≤ k, RegsMemLe B (run j s) := by
  obtain ⟨brPc, brMem, brRegs, brProg⟩ :=
    forN_loop_bounded_enter body sb base cn s hseg.append_left.append_left hpc hlt
  have segBody : SegmentAt (step s).program (step s).pc (compile body (step s).pc (sb + 3)) := by
    rw [brProg, brPc]; simpa using hseg.append_left.append_right
  have hstepbr : RegsMemLe B (step s) :=
    ⟨fun i => by rw [brRegs]; exact hrs.1 i, fun i => by rw [brMem]; exact hrs.2 i⟩
  obtain ⟨kb, bpc, bmem, bfr, bprog, bbnd⟩ :=
    ihbody (step s) segBody hstepbr (by rw [brMem]; exact hpbody)
  have hbk := bbnd kb le_rfl
  have hprogb : (run kb (step s)).program = s.program := by rw [bprog, brProg]
  have segAdd : SegmentAt (run kb (step s)).program (run kb (step s)).pc
      [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)] := by
    rw [hprogb, bpc, brPc]
    have hb := hseg.append_right
    simp only [List.length_append, List.length_cons, List.length_nil, compile_length] at hb
    rw [show base + cn + 4 + codeLenP body = base + cn + 2 + (2 + codeLenP body) from by omega]
    exact hb
  have hisb : (run kb (step s)).regs sb = s.regs sb := by rw [bfr sb (by omega), brRegs]
  have hone2 : (run kb (step s)).regs (sb + 2) = 1 := by
    rw [bfr (sb + 2) (by omega), brRegs, hone]
  have hsum : (run kb (step s)).regs sb + (run kb (step s)).regs (sb + 2) ≤ B := by
    have := hrs.1 (sb + 1); rw [hisb, hone2]; omega
  obtain ⟨tPc, tProg, tMem, tSb, tFr, tB1, tB2⟩ :=
    forN_loop_bounded_tail sb (base + cn + 2) B _ segAdd hbk hsum
  have hr1 : run (1 + kb) s = run kb (step s) := run_add 1 kb s
  have hrf : run (1 + kb + 2) s = step (step (run kb (step s))) := by
    rw [run_add, hr1]; rfl
  have htr1 : ∀ j ≤ 1 + kb, RegsMemLe B (run j s) :=
    compile_exec_bounded_trace_append B 1 kb s
      (fun j hj => by interval_cases j; exacts [by simpa [run_zero] using hrs, hstepbr])
      (fun j hj => bbnd j hj)
  have htr : ∀ j ≤ 1 + kb + 2, RegsMemLe B (run j s) :=
    compile_exec_bounded_trace_append B (1 + kb) 2 s htr1 (fun j hj => by
      rw [hr1]; interval_cases j; exacts [by simpa [run_zero] using hbk, tB1, tB2])
  refine ⟨1 + kb + 2, ?_⟩
  rw [hrf]
  refine ⟨tPc, ?_, ?_, ?_, ?_, ?_, ?_, htr⟩
  · rw [tFr _ (by omega), bfr (sb + 1) (by omega), brRegs]
  · rw [tFr _ (by omega), hone2]
  · rw [tSb, hisb, hone2]
  · rw [tMem, bmem, brMem]
  · intro x hx; rw [tFr x (by omega), bfr x (by omega), brRegs]
  · rw [tProg, hprogb]

/-- `forN_loop_bounded` induction step: one iteration (`forN_loop_bounded_iter`) followed by
    the remaining `m` iterations (the induction hypothesis). -/
lemma forN_loop_bounded_succ (body : Program) (sb base cn bound B : ℕ)
    (ihbody : ForNBodyBoundedGoal body sb B) (m : ℕ)
    (ih : ForNLoopBoundedGoal body sb base cn bound B m) :
    ForNLoopBoundedGoal body sb base cn bound B (m + 1) := by
  intro s hseg hpc hbound hone hi hrs hpbody
  have hlt : s.regs sb < s.regs (sb + 1) := by rw [hbound]; omega
  obtain ⟨k1, pc1, b1, o1, sb1, mem1, fr1, prog1, tr1⟩ :=
    forN_loop_bounded_iter body sb base cn B ihbody s hseg hpc hone hlt hrs
      ((congrArg (fun z => ProgramBoundedIn B z body) (loopEval_zero body s.mem)).mp
        (hpbody 0 (by omega)))
  have hpbody' : ∀ m' < m, ProgramBoundedIn B (loopEval body m' (run k1 s).mem) body := by
    intro m' hm'
    rw [mem1]
    have := hpbody (m' + 1) (by omega)
    rwa [loopEval_succ body m' s.mem] at this
  obtain ⟨kt, tpc, tmem, tfr, tprog, ttr⟩ :=
    ih (run k1 s) (by rw [prog1]; exact hseg) pc1 (by rw [b1, hbound]) o1
      (by rw [sb1]; omega) (tr1 k1 le_rfl) hpbody'
  refine ⟨k1 + kt, ?_, ?_, ?_, ?_, ?_⟩ <;> try rw [run_add]
  · exact tpc
  · rw [tmem, mem1]
    exact (loopEval_succ body m s.mem).symm
  · intro x hx; rw [tfr x hx, fr1 x hx]
  · rw [tprog, prog1]
  · exact compile_exec_bounded_trace_append B k1 kt s tr1 ttr

/-- Bounded companion to `forN_loop` (`BoundedWhileRefinement.lean`): the loop keeps every
    register/memory cell `≤ B` at every intermediate step, given a bounded per-call certificate
    for the body (`ihbody`) and the body's `ProgramBoundedIn` at every iteration's own store
    (`hpbody`, indexed against `loopEval body m' s.mem` — the store the `m'`-th call actually
    sees). -/
lemma forN_loop_bounded (body : Program) (sb base cn bound B : ℕ)
    (ihbody : ∀ rr : RAM, SegmentAt rr.program rr.pc (compile body rr.pc (sb + 3)) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem body →
      ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
           (run k rr).mem = Program.eval body rr.mem ∧
           (∀ x, x < sb + 3 → (run k rr).regs x = rr.regs x) ∧
           (run k rr).program = rr.program ∧
           ∀ j ≤ k, RegsMemLe B (run j rr)) :
    ∀ (m : ℕ) (s : RAM),
      SegmentAt s.program (base + cn + 2)
        ([Instruction.branchIfLt sb (sb + 1) (base + cn + 4),
          Instruction.jump (base + cn + codeLenP body + 6)] ++
         compile body (base + cn + 4) (sb + 3) ++
         [Instruction.add sb sb (sb + 2), Instruction.jump (base + cn + 2)]) →
      s.pc = base + cn + 2 → s.regs (sb + 1) = bound → s.regs (sb + 2) = 1 →
      s.regs sb + m = bound → RegsMemLe B s →
      (∀ m' < m, ProgramBoundedIn B (loopEval body m' s.mem) body) →
      ∃ k, (run k s).pc = base + cn + codeLenP body + 6 ∧
           (run k s).mem = loopEval body m s.mem ∧
           (∀ x, x < sb → (run k s).regs x = s.regs x) ∧
           (run k s).program = s.program ∧
           ∀ j ≤ k, RegsMemLe B (run j s) := by
  intro m
  induction m with
  | zero => exact forN_loop_bounded_zero body sb base cn bound B
  | succ m ih => exact forN_loop_bounded_succ body sb base cn bound B ihbody m ih


/-- `compile_exec_bounded` for `assign`: evaluate the right-hand side, then store it. -/
lemma compile_exec_bounded_assign (r_addr : ℕ) (e : Expr)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.assign r_addr e) rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem (Program.assign r_addr e)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.assign r_addr e) ∧
      (run k rr).mem = Program.eval (Program.assign r_addr e) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  obtain ⟨haddr, he⟩ := hp
  simp only [compile] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hb1⟩ :=
    compileExpr_exec_bounded e sb (sb + 1) B (by omega) hB1 rr hseg.append_left hr he
  have segtail : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.loadImm (sb + 1) r_addr, Instruction.store sb (sb + 1)] := by
    rw [hprog1, hpc1]; exact hseg.append_right
  have hcur0 : (run k1 rr).current = Instruction.loadImm (sb + 1) r_addr := by
    have := current_of_segment 0 segtail (by simp) (run k1 rr) rfl rfl; simpa using this
  obtain ⟨l0regs, l0pc, l0mem, l0prog, l0fr⟩ := step_loadImm (run k1 rr) (sb + 1) r_addr hcur0
  have hcur1 : (step (run k1 rr)).current = Instruction.store sb (sb + 1) := by
    have := current_of_segment 1 segtail (by simp) (step (run k1 rr)) l0pc l0prog
    simpa using this
  obtain ⟨s1mem, s1pc, s1regs, s1prog⟩ := step_store (step (run k1 rr)) sb (sb + 1) hcur1
  have hrun : run (k1 + 2) rr = step (step (run k1 rr)) := by
    rw [show k1 + 2 = k1 + 1 + 1 from rfl, run_succ_right, run_succ_right]
  refine ⟨k1 + 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, s1pc, l0pc, hpc1, compileExpr_length]; simp only [codeLenP]; omega
  · rw [hrun, s1mem, l0regs, l0fr sb (by omega), hrd1, l0mem, hmem1, bankWrite_eq_writeReg]
    exact (eval_assign r_addr e rr.mem).symm
  · intro x hx
    rw [hrun, s1regs, l0fr x (by omega)]; exact hfr1 x (by omega) (by omega)
  · rw [hrun, s1prog, l0prog, hprog1]
  · have hbk1 := hb1 k1 le_rfl
    have heval : e.eval rr.mem ≤ B := expr_eval_le_of_bounded_in hr.2 hB1 e he
    intro j hj
    rcases Nat.lt_or_ge j k1 with hj1 | hj1
    · exact hb1 j (by omega)
    rcases eq_or_lt_of_le hj1 with hj2 | hj2
    · rw [← hj2]; exact hbk1
    have hstep1 : RegsMemLe B (step (run k1 rr)) := by
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = sb + 1
        · rw [hi, l0regs]; exact haddr
        · rw [l0fr i hi]; exact hbk1.1 i
      · intro i; rw [l0mem]; exact hbk1.2 i
    rcases eq_or_lt_of_le (show k1 + 1 ≤ j from hj2) with hj3 | hj3
    · rw [← hj3, show run (k1 + 1) rr = step (run k1 rr) from by rw [run_add]; rfl]
      exact hstep1
    · have : j = k1 + 2 := by omega
      subst this
      rw [hrun]
      refine ⟨fun i => ?_, ?_⟩
      · rw [s1regs]; exact hstep1.1 i
      · intro i
        rw [s1mem]
        by_cases hi : i = (step (run k1 rr)).regs (sb + 1)
        · rw [hi]
          unfold bankWrite; rw [ite_eq_left rfl]
          rw [l0fr sb (by omega), hrd1]; exact heval
        · unfold bankWrite; rw [ite_eq_right hi]; exact hstep1.2 i

/-- `compile_exec_bounded` for `seq`: chain the two bounded runs. -/
lemma compile_exec_bounded_seq (p1 p2 : Program)
    (sb B : ℕ) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.seq p1 p2) rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem (Program.seq p1 p2))
    (hsf : ScanFree (Program.seq p1 p2))
    (ih1 : (∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile p1 rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem p1 → ScanFree p1 →
      ∃ k, (run k rr).pc = rr.pc + codeLenP p1 ∧
        (run k rr).mem = Program.eval p1 rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr)))
    (ih2 : (∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile p2 rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem p2 → ScanFree p2 →
      ∃ k, (run k rr).pc = rr.pc + codeLenP p2 ∧
        (run k rr).mem = Program.eval p2 rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr))) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.seq p1 p2) ∧
      (run k rr).mem = Program.eval (Program.seq p1 p2) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hsf1, hsf2⟩ := hsf
  simp only [compile] at hseg
  obtain ⟨k1, hpc1, hmem1, hfr1, hprog1, hb1⟩ :=
    ih1 sb rr hseg.append_left hr hp1 hsf1
  have seg2 : SegmentAt (run k1 rr).program (run k1 rr).pc (compile p2 (run k1 rr).pc sb) := by
    rw [hprog1, hpc1]
    have h := hseg.append_right
    rw [compile_length] at h; exact h
  have hp2' : ProgramBoundedIn B (run k1 rr).mem p2 := by rw [hmem1]; exact hp2
  obtain ⟨k2, hpc2, hmem2, hfr2, hprog2, hb2⟩ :=
    ih2 sb (run k1 rr) seg2 (hb1 k1 le_rfl) hp2' hsf2
  have hrun : run (k1 + k2) rr = run k2 (run k1 rr) := run_add k1 k2 rr
  refine ⟨k1 + k2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, hpc2, hpc1]; simp only [codeLenP]; omega
  · rw [hrun, hmem2, hmem1]
    exact (eval_seq p1 p2 rr.mem).symm
  · intro x hx; rw [hrun, hfr2 x hx]; exact hfr1 x hx
  · rw [hrun, hprog2, hprog1]
  · intro j hj
    rcases Nat.lt_or_ge j k1 with hj1 | hj1
    · exact hb1 j (by omega)
    obtain ⟨m, hm⟩ : ∃ m, j = k1 + m := ⟨j - k1, by omega⟩
    rw [hm, show run (k1 + m) rr = run m (run k1 rr) from run_add k1 m rr]
    exact hb2 m (by omega)

/-- `compile_exec_bounded` for `assignInd`: evaluate address and value, then store. -/
lemma compile_exec_bounded_assignInd (eA eV : Expr)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.assignInd eA eV) rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem (Program.assignInd eA eV)) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.assignInd eA eV) ∧
      (run k rr).mem = Program.eval (Program.assignInd eA eV) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  obtain ⟨heA, heV, heAval⟩ := hp
  simp only [compile] at hseg
  rw [List.append_assoc] at hseg
  obtain ⟨k1, hpc1, hrdA, hmem1, hfr1, hprog1, hb1⟩ :=
    compileExpr_exec_bounded eA sb (sb + 2) B (by omega) hB1 rr hseg.append_left hr heA
  have segB : SegmentAt (run k1 rr).program (run k1 rr).pc
      (compileExpr eV (sb + 1) (sb + 2)) := by
    rw [hprog1, hpc1]; exact hseg.append_right.append_left
  have heV1 : ExprBoundedIn B (run k1 rr).mem eV := by rw [hmem1]; exact heV
  obtain ⟨k2, hpc2, hrdV, hmem2, hfr2, hprog2, hb2⟩ :=
    compileExpr_exec_bounded eV (sb + 1) (sb + 2) B (by omega) hB1 (run k1 rr) segB
      (hb1 k1 le_rfl) heV1
  have segS : SegmentAt (run k2 (run k1 rr)).program (run k2 (run k1 rr)).pc
      [Instruction.store (sb + 1) sb] := by
    rw [hprog2, hprog1, hpc2, hpc1]; exact hseg.append_right.append_right
  have hcurS : (run k2 (run k1 rr)).current = Instruction.store (sb + 1) sb := by
    have := current_of_segment 0 segS (by simp) (run k2 (run k1 rr)) rfl rfl; simpa using this
  obtain ⟨sMem, sPc, sRegs, sProg⟩ := step_store (run k2 (run k1 rr)) (sb + 1) sb hcurS
  have hrun : run (k1 + k2 + 1) rr = step (run k2 (run k1 rr)) := by
    rw [show k1 + k2 + 1 = k1 + (k2 + 1) from by omega, run_add, run_succ_right]
  refine ⟨k1 + k2 + 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, sPc, hpc2, hpc1, compileExpr_length, compileExpr_length]
    simp only [codeLenP]; omega
  · rw [hrun, sMem, hfr2 sb (by omega) (by omega), hrdA, hrdV, hmem2, hmem1,
      bankWrite_eq_writeReg]
    exact (eval_assignInd eA eV rr.mem).symm
  · intro x hx
    rw [hrun, sRegs, hfr2 x (by omega) (by omega)]; exact hfr1 x (by omega) (by omega)
  · rw [hrun, sProg, hprog2, hprog1]
  · have hbk2 := hb2 k2 le_rfl
    have heV2 : ExprBoundedIn B (run k2 (run k1 rr)).mem eV := by rw [hmem2]; exact heV1
    have hevalV : eV.eval (run k1 rr).mem ≤ B := by
      have := expr_eval_le_of_bounded_in hbk2.2 hB1 eV heV2
      rwa [hmem2] at this
    have hevalV' : eV.eval rr.mem ≤ B := by rw [← hmem1]; exact hevalV
    intro j hj
    rcases Nat.lt_or_ge j k1 with hj1 | hj1
    · exact hb1 j (by omega)
    rcases Nat.lt_or_ge j (k1 + k2) with hj2 | hj2
    · obtain ⟨m, hm⟩ : ∃ m, j = k1 + m := ⟨j - k1, by omega⟩
      rw [hm, show run (k1 + m) rr = run m (run k1 rr) from run_add k1 m rr]
      exact hb2 m (by omega)
    rcases eq_or_lt_of_le hj2 with hj3 | hj3
    · rw [← hj3, show run (k1 + k2) rr = run k2 (run k1 rr) from run_add k1 k2 rr]
      exact hbk2
    · have : j = k1 + k2 + 1 := by omega
      subst this
      rw [hrun]
      refine ⟨fun i => ?_, ?_⟩
      · rw [sRegs]; exact hbk2.1 i
      · intro i
        rw [sMem]
        by_cases hi : i = (run k2 (run k1 rr)).regs sb
        · rw [hi]
          unfold bankWrite; rw [ite_eq_left rfl]
          rw [hrdV]; exact hevalV
        · unfold bankWrite; rw [ite_eq_right hi]; exact hbk2.2 i

/-- `compile_exec_bounded` for `ifNZ`, condition part: evaluating the condition and taking the
    branch keeps the state bounded and leaves the program counter at the chosen branch. -/
lemma compile_exec_bounded_ifNZ_cond (e : Expr) (t f : Program)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.ifNZ e t f) rr.pc sb))
    (hr : RegsMemLe B rr) (he : ExprBoundedIn B rr.mem e) :
    ∃ k1, (∀ j ≤ k1 + 1, RegsMemLe B (run j rr)) ∧
      (run (k1 + 1) rr).program = rr.program ∧ (run (k1 + 1) rr).mem = rr.mem ∧
      (∀ x, x < sb → (run (k1 + 1) rr).regs x = rr.regs x) ∧
      (e.eval rr.mem = 0 → (run (k1 + 1) rr).pc = rr.pc + codeLenE e + 1) ∧
      (e.eval rr.mem ≠ 0 →
        (run (k1 + 1) rr).pc = rr.pc + codeLenE e + codeLenP f + 2) := by
  simp only [compile] at hseg
  simp only [List.append_assoc] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hb1⟩ :=
    compileExpr_exec_bounded e sb (sb + 1) B (by omega) hB1 rr hseg.append_left hr he
  have segBr : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.branchIfNZ sb (rr.pc + codeLenE e + codeLenP f + 2)] := by
    rw [hprog1, hpc1]; exact hseg.append_right.append_left
  have hcurBr : (run k1 rr).current =
      Instruction.branchIfNZ sb (rr.pc + codeLenE e + codeLenP f + 2) := by
    have := current_of_segment 0 segBr (by simp) (run k1 rr) rfl rfl; simpa using this
  obtain ⟨brPc, brMem, brRegs, brProg⟩ := step_branchIfNZ (run k1 rr) sb _ hcurBr
  have hk1s : run (k1 + 1) rr = step (run k1 rr) := by rw [run_add]; rfl
  have hstepbr : RegsMemLe B (step (run k1 rr)) := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [brRegs]; exact (hb1 k1 le_rfl).1 i
    · rw [brMem]; exact (hb1 k1 le_rfl).2
  refine ⟨k1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases eq_or_lt_of_le hj with hj1 | hj1
    · rw [hj1, hk1s]; exact hstepbr
    · exact hb1 j (by omega)
  · rw [hk1s, brProg, hprog1]
  · rw [hk1s, brMem, hmem1]
  · intro x hx
    rw [hk1s, brRegs]; exact hfr1 x (by omega) (by omega)
  · intro hc
    rw [hk1s, brPc, hrd1, hpc1, compileExpr_length]; simp [hc]
  · intro hc
    rw [hk1s, brPc, hrd1]; simp [hc]


/-- `compile_exec_bounded` for `ifNZ`, else branch: from the state after the condition test,
    run the compiled `f` and jump over the then block. -/
lemma compile_exec_bounded_ifNZ_else (e : Expr) (t f : Program)
    (sb B : ℕ) (rr s : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.ifNZ e t f) rr.pc sb))
    (hpf : ProgramBoundedIn B rr.mem f) (hsff : ScanFree f)
    (ihf : ∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile f rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem f → ScanFree f →
      ∃ k, (run k rr).pc = rr.pc + codeLenP f ∧
        (run k rr).mem = Program.eval f rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr))
    (hs_prog : s.program = rr.program) (hs_mem : s.mem = rr.mem)
    (hs_fr : ∀ x, x < sb → s.regs x = rr.regs x) (hs_le : RegsMemLe B s)
    (hs_pc : s.pc = rr.pc + codeLenE e + 1) (hc : e.eval rr.mem = 0) :
    ∃ k, (run k s).pc = rr.pc + codeLenP (Program.ifNZ e t f) ∧
      (run k s).mem = Program.eval (Program.ifNZ e t f) rr.mem ∧
      (∀ x, x < sb → (run k s).regs x = rr.regs x) ∧
      (run k s).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j s) := by
  simp only [compile] at hseg
  simp only [List.append_assoc] at hseg
  have segF : SegmentAt s.program s.pc (compile f s.pc (sb + 1)) := by
    rw [hs_prog, hs_pc]
    simpa [compileExpr_length] using hseg.append_right.append_right.append_left
  have hpf1 : ProgramBoundedIn B s.mem f := by rw [hs_mem]; exact hpf
  obtain ⟨kf, fpc, fmem, ffr, fprog, hbf⟩ := ihf (sb + 1) s segF hs_le hpf1 hsff
  have segJ : SegmentAt (run kf s).program (run kf s).pc
      [Instruction.jump (rr.pc + codeLenE e + codeLenP f + codeLenP t + 2)] := by
    rw [fprog, hs_prog, fpc, hs_pc]
    simpa [compileExpr_length, compile_length] using
      hseg.append_right.append_right.append_right.append_left
  have hcurJ : (run kf s).current =
      Instruction.jump (rr.pc + codeLenE e + codeLenP f + codeLenP t + 2) := by
    have := current_of_segment 0 segJ (by simp) (run kf s) rfl rfl
    simpa using this
  obtain ⟨jPc, jMem, jRegs, jProg⟩ := step_jump (run kf s) _ hcurJ
  have hrunElse : run (kf + 1) s = step (run kf s) := run_succ_right kf s
  refine ⟨kf + 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrunElse, jPc]; simp only [codeLenP]; omega
  · rw [hrunElse, jMem, fmem, hs_mem]
    have he := eval_ifNZ e t f rr.mem
    rw [ite_eq_right (by simp [hc])] at he
    exact he.symm
  · intro x hx; rw [hrunElse, jRegs, ffr x (by omega)]; exact hs_fr x hx
  · rw [hrunElse, jProg, fprog, hs_prog]
  · intro j hj
    rcases Nat.lt_or_ge j (kf + 1) with hj1 | hj1
    · exact hbf j (by omega)
    · have : j = kf + 1 := by omega
      subst this
      rw [hrunElse]
      exact ⟨fun i => by rw [jRegs]; exact (hbf kf le_rfl).1 i,
        fun i => by rw [jMem]; exact (hbf kf le_rfl).2 i⟩


/-- `compile_exec_bounded` for `ifNZ`, then branch: from the state after the condition test,
    the branch jumps straight to the compiled `t`. -/
lemma compile_exec_bounded_ifNZ_then (e : Expr) (t f : Program)
    (sb B : ℕ) (rr s : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.ifNZ e t f) rr.pc sb))
    (hpt : ProgramBoundedIn B rr.mem t) (hsft : ScanFree t)
    (iht : ∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile t rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem t → ScanFree t →
      ∃ k, (run k rr).pc = rr.pc + codeLenP t ∧
        (run k rr).mem = Program.eval t rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr))
    (hs_prog : s.program = rr.program) (hs_mem : s.mem = rr.mem)
    (hs_fr : ∀ x, x < sb → s.regs x = rr.regs x) (hs_le : RegsMemLe B s)
    (hs_pc : s.pc = rr.pc + codeLenE e + codeLenP f + 2) (hc : ¬ e.eval rr.mem = 0) :
    ∃ k, (run k s).pc = rr.pc + codeLenP (Program.ifNZ e t f) ∧
      (run k s).mem = Program.eval (Program.ifNZ e t f) rr.mem ∧
      (∀ x, x < sb → (run k s).regs x = rr.regs x) ∧
      (run k s).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j s) := by
  simp only [compile] at hseg
  simp only [List.append_assoc] at hseg
  have segT : SegmentAt s.program s.pc (compile t s.pc (sb + 1)) := by
    have h := hseg.append_right.append_right.append_right.append_right
    rw [compileExpr_length, compile_length] at h
    simp only [List.length_cons, List.length_nil] at h
    rw [show rr.pc + codeLenE e + 1 + codeLenP f + 1
      = rr.pc + codeLenE e + codeLenP f + 2 from by omega] at h
    rw [hs_prog, hs_pc]; exact h
  have hpt1 : ProgramBoundedIn B s.mem t := by rw [hs_mem]; exact hpt
  obtain ⟨kt, tpc, tmem, tfr, tprog, hbt⟩ := iht (sb + 1) s segT hs_le hpt1 hsft
  refine ⟨kt, ?_, ?_, ?_, ?_, hbt⟩
  · rw [tpc, hs_pc]; simp only [codeLenP]; omega
  · rw [tmem, hs_mem]
    have he := eval_ifNZ e t f rr.mem
    rw [ite_eq_left (by simpa using hc)] at he
    exact he.symm
  · intro x hx; rw [tfr x (by omega)]; exact hs_fr x hx
  · rw [tprog, hs_prog]


/-- `compile_exec_bounded` for `ifNZ`: test the condition, then run the chosen branch. -/
lemma compile_exec_bounded_ifNZ (e : Expr) (t f : Program)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.ifNZ e t f) rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem (Program.ifNZ e t f))
    (hsf : ScanFree (Program.ifNZ e t f))
    (iht : (∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile t rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem t → ScanFree t →
      ∃ k, (run k rr).pc = rr.pc + codeLenP t ∧
        (run k rr).mem = Program.eval t rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr)))
    (ihf : (∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile f rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem f → ScanFree f →
      ∃ k, (run k rr).pc = rr.pc + codeLenP f ∧
        (run k rr).mem = Program.eval f rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr))) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.ifNZ e t f) ∧
      (run k rr).mem = Program.eval (Program.ifNZ e t f) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  obtain ⟨he, hpt, hpf⟩ := hp
  obtain ⟨hsft, hsff⟩ := hsf
  obtain ⟨k1, htr, hprog, hmem, hfr, hpc0, hpc1⟩ :=
    compile_exec_bounded_ifNZ_cond e t f sb B hB1 rr hseg hr he
  by_cases hc : e.eval rr.mem = 0
  · obtain ⟨k, hpc, hm, hf, hpg, hb⟩ :=
      compile_exec_bounded_ifNZ_else e t f sb B rr (run (k1 + 1) rr) hseg hpf hsff ihf
        hprog hmem hfr (htr _ le_rfl) (hpc0 hc) hc
    exact ⟨k1 + 1 + k, by rw [run_add]; exact hpc, by rw [run_add]; exact hm,
      fun x hx => by rw [run_add]; exact hf x hx, by rw [run_add]; exact hpg,
      compile_exec_bounded_trace_append B (k1 + 1) k rr htr hb⟩
  · obtain ⟨k, hpc, hm, hf, hpg, hb⟩ :=
      compile_exec_bounded_ifNZ_then e t f sb B rr (run (k1 + 1) rr) hseg hpt hsft iht
        hprog hmem hfr (htr _ le_rfl) (hpc1 hc) hc
    exact ⟨k1 + 1 + k, by rw [run_add]; exact hpc, by rw [run_add]; exact hm,
      fun x hx => by rw [run_add]; exact hf x hx, by rw [run_add]; exact hpg,
      compile_exec_bounded_trace_append B (k1 + 1) k rr htr hb⟩


/-- Bounded certificate for the `forN` prologue: evaluate the bound and initialize the loop
    counters while preserving the full bounded trace needed by the loop contract. -/
lemma compile_exec_bounded_forN_init (n : Expr) (body : Program)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.forN n body) rr.pc sb))
    (hr : RegsMemLe B rr) (hn : ExprBoundedIn B rr.mem n) :
    ∃ k, (run k rr).pc = rr.pc + codeLenE n + 2 ∧
      (run k rr).regs sb = 0 ∧
      (run k rr).regs (sb + 1) = n.eval rr.mem ∧
      (run k rr).regs (sb + 2) = 1 ∧
      (run k rr).mem = rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      SegmentAt (run k rr).program (rr.pc + codeLenE n + 2)
        ([Instruction.branchIfLt sb (sb + 1) (rr.pc + codeLenE n + 4),
          Instruction.jump (rr.pc + codeLenE n + codeLenP body + 6)] ++
         compile body (rr.pc + codeLenE n + 4) (sb + 3) ++
         [Instruction.add sb sb (sb + 2), Instruction.jump (rr.pc + codeLenE n + 2)]) ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  simp only [compile] at hseg
  obtain ⟨k1, hpc1, hrd1, hmem1, hfr1, hprog1, hb1⟩ :=
    compileExpr_exec_bounded n (sb + 1) (sb + 3) B (by omega) hB1 rr
      hseg.append_left.append_left hr hn
  have seg2 : SegmentAt (run k1 rr).program (run k1 rr).pc
      [Instruction.loadImm sb 0, Instruction.loadImm (sb + 2) 1] := by
    rw [hprog1, hpc1]
    exact hseg.append_left.append_right
  have hcurL0 : (run k1 rr).current = Instruction.loadImm sb 0 := by
    have := current_of_segment 0 seg2 (by simp) (run k1 rr) rfl rfl
    simpa using this
  obtain ⟨l0regs, l0pc, l0mem, l0prog, l0fr⟩ := step_loadImm (run k1 rr) sb 0 hcurL0
  have hcurL1 : (step (run k1 rr)).current = Instruction.loadImm (sb + 2) 1 := by
    have := current_of_segment 1 seg2 (by simp) (step (run k1 rr)) l0pc l0prog
    simpa using this
  obtain ⟨l1regs, l1pc, l1mem, l1prog, l1fr⟩ :=
    step_loadImm (step (run k1 rr)) (sb + 2) 1 hcurL1
  have hsL : run (k1 + 2) rr = step (step (run k1 rr)) := by
    rw [show k1 + 2 = k1 + 1 + 1 from rfl, run_succ_right, run_succ_right]
  have hsLpc : (step (step (run k1 rr))).pc = rr.pc + codeLenE n + 2 := by
    rw [l1pc, l0pc, hpc1, compileExpr_length]
  have hsLprog : (step (step (run k1 rr))).program = rr.program := by
    rw [l1prog, l0prog, hprog1]
  have hsLmem : (step (step (run k1 rr))).mem = rr.mem := by rw [l1mem, l0mem, hmem1]
  have hsLsb0 : (step (step (run k1 rr))).regs sb = 0 := by
    rw [l1fr sb (by omega), l0regs]
  have hsLb1 : (step (step (run k1 rr))).regs (sb + 1) = n.eval rr.mem := by
    rw [l1fr (sb + 1) (by omega), l0fr (sb + 1) (by omega), hrd1]
  have hsLsb2 : (step (step (run k1 rr))).regs (sb + 2) = 1 := by
    rw [l1regs]
  have hsLfr : ∀ x, x < sb → (step (step (run k1 rr))).regs x = rr.regs x := by
    intro x hx
    rw [l1fr x (by omega), l0fr x (by omega), hfr1 x (by omega) (by omega)]
  have hstep0Bound : RegsMemLe B (step (run k1 rr)) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = sb
      · rw [hi, l0regs]
        omega
      · rw [l0fr i hi]
        exact (hb1 k1 le_rfl).1 i
    · rw [l0mem]
      exact (hb1 k1 le_rfl).2
  have hsLbnd : RegsMemLe B (step (step (run k1 rr))) := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi2 : i = sb + 2
      · rw [hi2, l1regs]; exact hB1
      · by_cases hi0 : i = sb
        · rw [hi0, l1fr sb (by omega), l0regs]; omega
        · rw [l1fr i hi2, l0fr i hi0]; exact (hb1 k1 le_rfl).1 i
    · rw [l1mem, l0mem]; exact (hb1 k1 le_rfl).2
  have hsegL : SegmentAt (step (step (run k1 rr))).program (rr.pc + codeLenE n + 2)
      ([Instruction.branchIfLt sb (sb + 1) (rr.pc + codeLenE n + 4),
        Instruction.jump (rr.pc + codeLenE n + codeLenP body + 6)] ++
       compile body (rr.pc + codeLenE n + 4) (sb + 3) ++
       [Instruction.add sb sb (sb + 2), Instruction.jump (rr.pc + codeLenE n + 2)]) := by
    rw [hsLprog]
    have hb := hseg.append_right
    simp only [List.length_append, List.length_cons, List.length_nil, compileExpr_length] at hb
    rw [show rr.pc + codeLenE n + 2 = rr.pc + (codeLenE n + 2) from by omega]
    exact hb
  have hloadTrace : ∀ j ≤ 2, RegsMemLe B (run j (run k1 rr)) := by
    intro j hj
    interval_cases j
    · simpa [run_zero] using (hb1 k1 le_rfl)
    · rw [show run 1 (run k1 rr) = step (run k1 rr) from rfl]
      exact hstep0Bound
    · rw [show run 2 (run k1 rr) = step (step (run k1 rr)) from rfl]
      exact hsLbnd
  have htrInit : ∀ j ≤ k1 + 2, RegsMemLe B (run j rr) :=
    compile_exec_bounded_trace_append B k1 2 rr hb1 hloadTrace
  refine ⟨k1 + 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htrInit⟩
  · rw [hsL, hsLpc]
  · rw [hsL, hsLsb0]
  · rw [hsL, hsLb1]
  · rw [hsL, hsLsb2]
  · rw [hsL, hsLmem]
  · intro x hx
    rw [hsL, hsLfr x hx]
  · rw [hsL, hsLprog]
  · rw [hsL]
    exact hsegL

/-- `compile_exec_bounded` for `forN`: load the loop counters, then run the bounded loop. -/
lemma compile_exec_bounded_forN (n : Expr) (body : Program)
    (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile (Program.forN n body) rr.pc sb))
    (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem (Program.forN n body))
    (hsf : ScanFree (Program.forN n body))
    (ih : (∀ (sb : ℕ) (rr : RAM), SegmentAt rr.program rr.pc (compile body rr.pc sb) →
      RegsMemLe B rr → ProgramBoundedIn B rr.mem body → ScanFree body →
      ∃ k, (run k rr).pc = rr.pc + codeLenP body ∧
        (run k rr).mem = Program.eval body rr.mem ∧
        (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
        (run k rr).program = rr.program ∧
        ∀ j ≤ k, RegsMemLe B (run j rr))) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP (Program.forN n body) ∧
      (run k rr).mem = Program.eval (Program.forN n body) rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  obtain ⟨hn, hpbody⟩ := hp
  obtain ⟨k1, hsLpc, hsLsb0, hsLb1, hsLsb2, hsLmem, hsLfr, hsLprog, hsegL, hb1⟩ :=
    compile_exec_bounded_forN_init n body sb B hB1 rr hseg hr hn
  have hpbodyL : ∀ m' < n.eval rr.mem,
      ProgramBoundedIn B (loopEval body m' (run k1 rr).mem) body := by
    rw [hsLmem]
    exact hpbody
  obtain ⟨kL, Lpc, Lmem, Lfr, Lprog, hbL⟩ :=
    forN_loop_bounded body sb rr.pc (codeLenE n) (n.eval rr.mem) B
      (fun rr' hseg' hr' hp' => ih (sb + 3) rr' hseg' hr' hp' hsf)
      (n.eval rr.mem) (run k1 rr) hsegL hsLpc hsLb1 hsLsb2
      (by rw [hsLsb0]; omega) (hb1 k1 le_rfl) hpbodyL
  have hrun : run (k1 + kL) rr = run kL (run k1 rr) := run_add k1 kL rr
  have htrace := compile_exec_bounded_trace_append B k1 kL rr hb1 hbL
  refine ⟨k1 + kL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, Lpc]
    simp only [codeLenP]
    omega
  · rw [hrun, Lmem, hsLmem]
    exact (eval_forN n body rr.mem).symm
  · intro x hx
    rw [hrun, Lfr x hx, hsLfr x hx]
  · rw [hrun, Lprog, hsLprog]
  · intro j hj
    exact htrace j hj
/-- Bounded companion to `compile_exec`: running the compiled block keeps every register/memory
    cell `≤ B` at every intermediate step, given `rr` started `≤ B` and `p`'s own addresses/values
    (`ProgramBoundedIn`) stay `≤ B` against `rr.mem`. `scanList`/`lookup` are excluded by
    `hsf`, so this theorem covers the scan-free fragment. -/
lemma compile_exec_bounded (p : Program) (sb B : ℕ) (hB1 : 1 ≤ B) (rr : RAM)
    (hseg : SegmentAt rr.program rr.pc (compile p rr.pc sb))
     (hr : RegsMemLe B rr) (hp : ProgramBoundedIn B rr.mem p) (hsf : ScanFree p) :
    ∃ k, (run k rr).pc = rr.pc + codeLenP p ∧
      (run k rr).mem = Program.eval p rr.mem ∧
      (∀ x, x < sb → (run k rr).regs x = rr.regs x) ∧
      (run k rr).program = rr.program ∧
      ∀ j ≤ k, RegsMemLe B (run j rr) := by
  induction p generalizing sb rr with
  | skip =>
    refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [codeLenP]
    · exact (eval_skip rr.mem).symm
    · intro x _; rfl
    · rfl
    · intro j hj
      have hj0 : j = 0 := by omega
      rw [hj0, run_zero]
      exact hr
  | assign r_addr e => exact compile_exec_bounded_assign r_addr e sb B hB1 rr hseg hr hp
  | seq p1 p2 ih1 ih2 =>
    exact compile_exec_bounded_seq p1 p2 sb B rr hseg hr hp hsf
      (fun sb rr hs hr hp hsf => ih1 sb rr hs hr hp hsf)
      (fun sb rr hs hr hp hsf => ih2 sb rr hs hr hp hsf)
  | assignInd eA eV => exact compile_exec_bounded_assignInd eA eV sb B hB1 rr hseg hr hp
  | ifNZ e t f iht ihf =>
    exact compile_exec_bounded_ifNZ e t f sb B hB1 rr hseg hr hp hsf
      (fun sb rr hs hr hp hsf => iht sb rr hs hr hp hsf)
      (fun sb rr hs hr hp hsf => ihf sb rr hs hr hp hsf)
  | forN n body ih =>
    exact compile_exec_bounded_forN n body sb B hB1 rr hseg hr hp hsf
      (fun sb rr hs hr hp hsf => ih sb rr hs hr hp hsf)
  | scanList _ _ _ _ => cases hsf
  | lookup _ _ _ => cases hsf

end NPComplete.RAMToTM

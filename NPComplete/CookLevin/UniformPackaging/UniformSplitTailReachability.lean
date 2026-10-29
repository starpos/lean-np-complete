module

public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailStore

/-!
# Uniform split-tail reachability

The fixed-register emitter needs a reachability argument with raw bounds and
clause-variable bounds carried together. This module packages those concrete
invariants and derives uniform step and program bounds from windowed executions.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral encodeThreeClause)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

/-! A callback-free reachability package for the concrete uniform split-tail loop.  The
    raw bounds are carried in the relation branch and in the terminal branch; terminal-state
    facts alone do not imply quantitative bounds. -/

structure UniformSplitTailEmitRelRaw (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) : Prop where
  rel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry ls
    pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg
    uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
  bounds : ∀ l ∈ ls, l.var + 1 ≤ N
  raw : SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
    (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ
  bound_eq : σ uctSavedBoundReg = N
  window : SplitTailEmitWindow inputEnd baseLimit base ls tail addr

structure UniformSplitTailEmitDoneRaw (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) : Prop where
  done : SplitTailEmitDoneRawBounds (uniformEmitLongValueEnvelope N)
    (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    uctSavedBoundReg N base carry ls pref tail addr σ
  window : SplitTailEmitWindow inputEnd baseLimit base ls tail addr

/-- On an empty literal list the step program is a no-op, so the relation package persists. -/
lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window_nil
    (N inputEnd baseLimit base : ℕ) (carry : NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry [] pref tail addr σ) :
    (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ = σ := by
  have hrem : σ uctRemainingReg = 0 := by simpa using h.rel.remaining
  exact splitTailEmitStepProgAt_zero_eval uctCurJ uctTmpJ uctCursorReg
    uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg
    σ hrem

/-- A one-literal tail takes the terminal-one branch of the step program and lands in the
    done package. -/
lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window_one
    (N inputEnd baseLimit base : ℕ) (carry l : NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry [l] pref tail addr σ)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    UniformSplitTailEmitDoneRaw N inputEnd baseLimit base carry [l] pref tail addr
      ((splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) := by
  have hok := uniform_emit_bound_reg_ok.split
  have hdone := splitTailEmitRel_one_to_done_raw_bounds_of_window
    (K := uniformEmitLongValueEnvelope N) (B := uniformEmitSyntaxEnvelope N)
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (inputEnd := inputEnd) (baseLimit := baseLimit) (start := uniformStartNat)
    (cursorReg := uctCursorReg) (polReg := uctPolReg) (varReg := uctVarReg)
    (doneReg := uctDoneReg) (remainingReg := uctRemainingReg)
    (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg)
    (var3Reg := uctVar3Reg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (posPolReg := uctPosPolReg)
    (freshReg := uctFreshReg) (boundReg := uctSavedBoundReg) (bound := N)
    (lengthReg := uctLengthReg) (outerReg := uctOuterReg) (negPolReg := uctNegPolReg)
    (base := base) (carry := carry) (l := l) (pref := pref) (tail := tail)
    (addr := addr) (σ := σ) (hbound := h.bounds l (by simp)) h.rel h.bound_eq hok h.raw
    h.window (by simpa [h.bound_eq] using hend)
  have hat := splitTailEmitTerminalOneProgAt_eq uctCurJ uctTmpJ uctCursorReg
    uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg N σ
    h.bound_eq hok.ne_cursor hok.ne_pol2 hok.ne_var2 hok.ne_done
  rw [← hat] at hdone
  have hstep : (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ =
      (splitTailEmitTerminalOneProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
        uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ := by
    simp [splitTailEmitStepProgAt, h.rel.remaining, Expr.eval]
  rw [hstep]
  exact ⟨hdone, h.window⟩

/-- A two-literal tail takes the terminal-two branch of the step program and lands in the
    done package. -/
lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window_two
    (N inputEnd baseLimit base : ℕ) (carry l l2 : NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry [l, l2] pref tail addr σ)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    UniformSplitTailEmitDoneRaw N inputEnd baseLimit base carry [l, l2] pref tail addr
      ((splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) := by
  have hok := uniform_emit_bound_reg_ok.split
  have hdone := splitTailEmitRel_two_to_done_raw_bounds_of_window
    (K := uniformEmitLongValueEnvelope N) (B := uniformEmitSyntaxEnvelope N)
    (M := uniformMNat N) (curJ := uctCurJ) (tmpJ := uctTmpJ)
    (inputEnd := inputEnd) (baseLimit := baseLimit) (start := uniformStartNat)
    (cursorReg := uctCursorReg) (polReg := uctPolReg) (varReg := uctVarReg)
    (doneReg := uctDoneReg) (remainingReg := uctRemainingReg)
    (pol2Reg := uctPol2Reg) (var2Reg := uctVar2Reg) (pol3Reg := uctPol3Reg)
    (var3Reg := uctVar3Reg) (carryPolReg := uctCarryPolReg)
    (carryValReg := uctCarryValReg) (posPolReg := uctPosPolReg)
    (freshReg := uctFreshReg) (boundReg := uctSavedBoundReg) (bound := N)
    (lengthReg := uctLengthReg) (outerReg := uctOuterReg) (negPolReg := uctNegPolReg)
    (base := base) (carry := carry) (l1 := l) (l2 := l2) (pref := pref)
    (tail := tail) (addr := addr) (σ := σ)
    (hbound1 := h.bounds l (by simp)) (hbound2 := h.bounds l2 (by simp))
    h.rel h.bound_eq hok h.raw h.window (by simpa [h.bound_eq] using hend)
  have hat := splitTailEmitTerminalTwoProgAt_eq uctCurJ uctTmpJ uctCursorReg
    uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg
    uctFreshReg uctSavedBoundReg N σ h.bound_eq hok.ne_cursor hok.ne_pol2
    hok.ne_var2 hok.ne_done hok.ne_pol3 hok.ne_var3
  rw [← hat] at hdone
  have hstep : (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ =
      (splitTailEmitTerminalTwoProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg
        uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg).eval σ := by
    simp [splitTailEmitStepProgAt, h.rel.remaining, Expr.eval]
  rw [hstep]
  exact ⟨hdone, h.window⟩

/-- For three or more literals the step program equals the intermediate relation step, whose
    result `τ` satisfies the relation for the shorter tail and keeps the saved bound. -/
lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window_intermediate_rel
    (N inputEnd baseLimit base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry (l :: l2 :: l3 :: rest)
      pref tail addr σ)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N) :
    ∃ τ, τ = (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ ∧
      SplitTailEmitRel τ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat (base + 1)
        (NPComplete.SAT.Literal.neg base) (l2 :: l3 :: rest)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
        tail (addr + l.var + 2) uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
        uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
        uctPosPolReg uctFreshReg ∧
      τ uctSavedBoundReg = N ∧ StoreValuesLe (uniformEmitLongValueEnvelope N) τ := by
  have hok := uniform_emit_bound_reg_ok.split
  obtain ⟨τ, hτ, hrelτ⟩ := splitTailEmitRel_intermediate_to_rel
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg N
    base carry l l2 l3 rest pref tail addr σ (h.bounds l (by simp)) h.rel
  have hbase1 : base + 1 ≤ uniformEmitLongValueEnvelope N := by
    have hw := h.window.2
    simp only [List.length_cons] at hw
    omega
  have hpostCursor : addr + l.var + 2 ≤ uniformEmitLongValueEnvelope N := by
    have hw := h.window.1
    rw [splitTailInputBits_cons_length] at hw
    omega
  have hstore := storeValuesLe_splitTailEmitIntermediateProgAt_of_rel
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N)
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    uctSavedBoundReg uctLengthReg uctOuterReg uctNegPolReg N base carry l l2 l3
    rest pref tail addr σ hbase1 hpostCursor (h.bounds l (by simp)) h.rel
    h.bound_eq h.raw
  have hinterAt := splitTailEmitIntermediateProgAt_eq uctCurJ uctTmpJ
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctCarryPolReg
    uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg N σ h.bound_eq
    hok.ne_cursor hok.ne_pol hok.ne_var hok.ne_done
  have hstoreτ : StoreValuesLe (uniformEmitLongValueEnvelope N) τ := by
    rw [← hinterAt.trans hτ.symm]
    exact hstore
  have hframe := splitTailEmitStepProg_low_frame_of_rel
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg
    uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
    uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
    N base carry (l :: l2 :: l3 :: rest) pref tail addr σ h.bounds
    h.rel hok.below hok.ne_write_set
  have hbody :
      (splitTailEmitStepProg uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg N).eval σ = τ := by
    simp [splitTailEmitStepProg, h.rel.remaining, Expr.eval]
    exact hτ.symm
  have hat := splitTailEmitStepProgAt_eq uctCurJ uctTmpJ uctCursorReg
    uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
    uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg
    uctFreshReg uctSavedBoundReg N σ h.bound_eq hok.ne_cursor hok.ne_pol
    hok.ne_var hok.ne_done hok.ne_pol2 hok.ne_var2 hok.ne_pol3 hok.ne_var3
  exact ⟨τ, hat.trans hbody |>.symm, hrelτ, by rw [← hbody]; exact hframe.trans h.bound_eq,
    hstoreτ⟩

/-- A tail with three or more literals steps to the relation package for the shorter tail,
    with the syntax raw bounds re-derived from the window. -/
lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window_intermediate
    (N inputEnd baseLimit base : ℕ) (carry l l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry (l :: l2 :: l3 :: rest)
      pref tail addr σ)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    UniformSplitTailEmitRelRaw N inputEnd baseLimit (base + 1)
      (NPComplete.SAT.Literal.neg base) (l2 :: l3 :: rest)
      (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
      tail (addr + l.var + 2) ((splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) := by
  obtain ⟨τ, hτ, hrelτ, hτbound, hstoreτ⟩ :=
    uniform_split_tail_emit_step_raw_bounds_of_rel_window_intermediate_rel N inputEnd baseLimit
      base carry l l2 l3 rest pref tail addr σ h hinputEnd hbaseLimit
  have hwindow := SplitTailEmitWindow.intermediate inputEnd baseLimit base l l2 l3
    rest tail addr h.window
  have hrawτ := uniform_split_tail_emit_step_syntax_bounds_of_rel N (base + 1)
    inputEnd baseLimit (NPComplete.SAT.Literal.neg base) (l2 :: l3 :: rest)
    (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
    tail (addr + l.var + 2) τ hrelτ hwindow hτbound hend hstoreτ
  subst hτ
  exact ⟨hrelτ, fun x hx => h.bounds x (by simp [hx]), hrawτ, hτbound, hwindow⟩

lemma uniform_split_tail_emit_step_raw_bounds_of_rel_window
    (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (h : UniformSplitTailEmitRelRaw N inputEnd baseLimit base carry ls pref tail addr σ)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ ∧
      (UniformSplitTailEmitRelRaw N inputEnd baseLimit base' carry' ls' pref' tail addr' τ ∨
       UniformSplitTailEmitDoneRaw N inputEnd baseLimit base' carry' ls' pref' tail addr' τ) := by
  match ls, h with
  | [], h =>
      have hzero := uniform_split_tail_emit_step_raw_bounds_of_rel_window_nil N inputEnd baseLimit
        base carry pref tail addr σ h
      exact ⟨σ, base, carry, [], pref, addr, hzero.symm, Or.inl h⟩
  | [l], h =>
      exact ⟨_, base, carry, [l], pref, addr, rfl, Or.inr
        (uniform_split_tail_emit_step_raw_bounds_of_rel_window_one N inputEnd baseLimit base carry l
          pref tail addr σ h hend)⟩
  | [l, l2], h =>
      exact ⟨_, base, carry, [l, l2], pref, addr, rfl, Or.inr
        (uniform_split_tail_emit_step_raw_bounds_of_rel_window_two N inputEnd baseLimit base carry l
          l2 pref tail addr σ h hend)⟩
  | l :: l2 :: l3 :: rest, h =>
      exact ⟨_, base + 1, NPComplete.SAT.Literal.neg base, l2 :: l3 :: rest,
        pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base,
        addr + l.var + 2, rfl, Or.inl
        (uniform_split_tail_emit_step_raw_bounds_of_rel_window_intermediate N inputEnd baseLimit base
          carry l l2 l3 rest pref tail addr σ h hinputEnd hbaseLimit hend)⟩

lemma uniform_split_tail_emit_prog_at_reachable_raw_of_window
    (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (n : ℕ) (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry
      ls pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N) (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hraw : SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
      (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ∃ τ base' carry' ls' pref' addr',
      τ = loopEval
        (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
          uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
          uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)
        n σ ∧
      (UniformSplitTailEmitRelRaw N inputEnd baseLimit base' carry' ls' pref' tail addr' τ ∨
       UniformSplitTailEmitDoneRaw N inputEnd baseLimit base' carry' ls' pref' tail addr' τ) := by
  induction n generalizing base carry ls pref addr σ hbound hrel hb hσ hraw hwin with
  | zero =>
      exact ⟨σ, base, carry, ls, pref, addr, by simp,
        Or.inl ⟨hrel, hbound, hraw, hb, hwin⟩⟩
  | succ n ih =>
      obtain ⟨τ, base', carry', ls', pref', addr', hτ, hstate⟩ := ih
        (base := base) (carry := carry) (ls := ls) (pref := pref) (addr := addr)
        (σ := σ) hbound hrel hb hσ hraw hwin
      have hsucc :
          loopEval
              (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
                uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
                uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)
              (n + 1) σ =
            (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
              uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
              uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval τ := by
        rw [uniform_loopEval_succ_right, hτ]
      rcases hstate with hrel' | hdone'
      · obtain ⟨τ', base'', carry'', ls'', pref'', addr'', hstep, hstate'⟩ :=
          uniform_split_tail_emit_step_raw_bounds_of_rel_window N inputEnd baseLimit base' carry'
            ls' pref' tail addr' τ hrel' hinputEnd hbaseLimit hend
        refine ⟨τ', base'', carry'', ls'', pref'', addr'', ?_, hstate'⟩
        exact hstep.trans hsucc.symm
      · have hzero := splitTailEmitStepProgAt_zero_eval uctCurJ uctTmpJ uctCursorReg
          uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
          uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg
          τ hdone'.done.done.remaining
        refine ⟨τ, base', carry', ls', pref', addr', ?_, Or.inr hdone'⟩
        exact hzero.symm.trans hsucc.symm

lemma programBoundedIn_uniform_split_tail_emit_step_of_raw
    (N : ℕ) (σ : Store)
    (hraw : SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
      (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
  exact programBoundedIn_splitTailEmitStepProgAt_raw_of_bounds
    (uniformEmitLongValueEnvelope N) (uniformEmitSyntaxEnvelope N) (uniformMNat N)
    uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg uctSavedBoundReg σ hraw.cur_j1 hraw.tmp_jlt hraw.static hraw.idx
    hraw.dist hraw.dist1 hraw.dist2 hraw.zero1 hraw.zero2 hraw.control1 hraw.control2
    hraw.zero hraw.control
    hraw.store hraw.root hraw.cursor_nonzero hraw.cursor1 hraw.cursor2 hraw.carry_val0
    hraw.fresh0 hraw.carry_val_cursor hraw.fresh_cursor hraw.budget

lemma programBoundedIn_uniform_splitTailEmitProgAt_of_reach
    (N inputEnd baseLimit : ℕ) (σ : Store) (tail : Bits)
    (hB1 : 1 ≤ uniformEmitSyntaxEnvelope N)
    (hremaining : uctRemainingReg ≤ uniformEmitSyntaxEnvelope N)
    (hremainingValue : σ uctRemainingReg + 1 ≤ uniformEmitSyntaxEnvelope N)
    (hzero : ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitTerminalZeroProg uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg))
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref : Bits) (addr : ℕ)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry
      ls pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
  have hraw := uniform_split_tail_emit_step_syntax_bounds_of_rel N base inputEnd baseLimit carry ls
    pref tail addr σ hrel hwin hb hend hσ
  apply programBoundedIn_splitTailEmitProgAt_of_step (uniformEmitSyntaxEnvelope N)
    uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
    uctPosPolReg uctFreshReg uctSavedBoundReg σ hB1 hremaining hremainingValue hzero
  intro m hm
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hstate⟩ :=
    uniform_split_tail_emit_prog_at_reachable_raw_of_window N inputEnd baseLimit base carry ls
      pref tail addr σ m hbound hrel hb hσ hraw hwin hinputEnd hbaseLimit hend
  rw [← hτ]
  rcases hstate with hrel' | hdone'
  · exact programBoundedIn_uniform_split_tail_emit_step_of_raw N τ hrel'.raw
  · exact programBoundedIn_uniform_split_tail_emit_step_of_raw N τ hdone'.done.raw

lemma programBoundedIn_uniform_splitTailEmitLongClauseProgAt_of_reach
    (N inputEnd baseLimit : ℕ) (σ : Store)
    (hsetup : ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg))
    (hσsetup : StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ))
    (hzero : ProgramBoundedIn (uniformEmitSyntaxEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ)
      (splitTailEmitTerminalZeroProg uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg
        uctSavedBoundReg))
    (hremainingValue :
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ)
        uctRemainingReg + 1 ≤ uniformEmitSyntaxEnvelope N)
    (base : ℕ) (carry : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ)
      (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry ls pref tail addr
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (hb :
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ)
        uctSavedBoundReg = N)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ProgramBoundedIn (uniformEmitSyntaxEnvelope N) σ
      (splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
  let σsetup :=
    (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ
  have hremainingReg : uctRemainingReg ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uctRemainingReg, uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
      writerAppendRawStepBound, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
      uniformMNat, uniformStartNat, uniformSlackNat]
    omega
  have hsyntax1 : 1 ≤ uniformEmitSyntaxEnvelope N := by
    simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
      writerAppendRawStepBound, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
      uniformMNat, uniformStartNat, uniformSlackNat]
    omega
  have hlong := programBoundedIn_uniform_splitTailEmitProgAt_of_reach N inputEnd baseLimit
    σsetup tail
    hsyntax1 hremainingReg hremainingValue hzero base carry ls pref addr hbound hrel hb hσsetup hwin
    hinputEnd hbaseLimit hend
  exact programBoundedIn_splitTailEmitLongClauseProgAt_of_parts
    (uniformEmitSyntaxEnvelope N) uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ hsetup
    (by simpa [σsetup] using hlong)

/-- The two `At` decoders of the long-clause setup stay within the long value envelope, and
    their composed output equals that of the bound-parameterised decoders. -/
lemma storeValuesLe_uniform_long_clause_setup_at_tight_of_state_decode
    (N : ℕ) (σ : Store)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hcursorBudget : σ uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    ProgramBoundedIn (uniformEmitLongValueEnvelope N) σ
      (decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg) ∧
    ProgramBoundedIn (uniformEmitLongValueEnvelope N)
      ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ)
      (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
        uctSavedBoundReg) ∧
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
        uctSavedBoundReg).eval
        ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
          uctSavedBoundReg).eval σ)) ∧
    (decodeLiteralValueProgramAt uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
        uctSavedBoundReg).eval
      ((decodeLiteralValueProgramAt uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
        uctSavedBoundReg).eval σ) =
    (decodeLiteralValueProgram uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg N).eval
      ((decodeLiteralValueProgram uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg N).eval σ) := by
  set K := uniformEmitLongValueEnvelope N with hK
  have hK1 : 1 ≤ K := by
    simp [K, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hidx1 : uctCursorReg ≤ K ∧ uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧
      uctDoneReg ≤ K ∧ uctSavedBoundReg ≤ K := by
    simp [K, uctCursorReg, uctPol2Reg, uctVar2Reg, uctDoneReg, uctSavedBoundReg,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hidx2 : uctCursorReg ≤ K ∧ uctPol3Reg ≤ K ∧ uctVar3Reg ≤ K ∧
      uctDoneReg ≤ K ∧ uctSavedBoundReg ≤ K := by
    simp [K, uctCursorReg, uctPol3Reg, uctVar3Reg, uctDoneReg, uctSavedBoundReg,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hdec1 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K K
    uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg uctSavedBoundReg σ hidx1
    (by decide) (by decide) hK1 hσ (by rw [hb]; omega) le_rfl
  have hbτ := decodeLiteralValueProgramAt_bound_frame uctCursorReg uctPol2Reg
    uctVar2Reg uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide) (by decide)
  have hcτ := decodeLiteralValueProgramAt_cursor_le uctCursorReg uctPol2Reg
    uctVar2Reg uctDoneReg uctSavedBoundReg σ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hdec2 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K K
    uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg uctSavedBoundReg _ hidx2
    (by decide) (by decide) hK1 hdec1.2.1 (by rw [hbτ, hb]; omega) le_rfl
  have heq1 := decodeLiteralValueProgramAt_eq uctCursorReg uctPol2Reg uctVar2Reg uctDoneReg
    uctSavedBoundReg N σ hb (by decide) (by decide) (by decide) (by decide)
  have heq2 := decodeLiteralValueProgramAt_eq uctCursorReg uctPol3Reg uctVar3Reg uctDoneReg
    uctSavedBoundReg N _ (hbτ.trans hb) (by decide) (by decide) (by decide) (by decide)
  exact ⟨hdec1.1, hdec2.1, hdec2.2.1, by rw [heq2, heq1]⟩

/-- Appending the two decoded literals stays within the long value envelope, and keeps the
    fresh-variable register at `base`. -/
lemma storeValuesLe_uniform_long_clause_setup_at_tight_of_state_writer
    (N base : ℕ) (l1 l2 : NPComplete.SAT.Literal) (pref : Bits) (υ : Store)
    (hυ : StoreValuesLe (uniformEmitLongValueEnvelope N) υ)
    (hυstate : WriterState υ (uniformMNat N) uctCurJ uniformStartNat pref)
    (hpol1 : υ uctPol2Reg = literalPolarity l1) (hvar1 : υ uctVar2Reg = l1.var)
    (hpol2 : υ uctPol3Reg = literalPolarity l2) (hvar2 : υ uctVar3Reg = l2.var)
    (hpos : υ uctPosPolReg = 0) (hfresh : υ uctFreshReg = base)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ) :
    ProgramBoundedIn (uniformEmitLongValueEnvelope N) υ
      (writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg) ∧
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg).eval υ) ∧
    (writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctFreshReg).eval υ uctFreshReg = base := by
  set K := uniformEmitLongValueEnvelope N with hK
  have hK1 : 1 ≤ K := by
    simp [K, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hpol01 : literalPolarity l1 = 0 ∨ literalPolarity l1 = 1 := by
    cases l1 <;> simp [literalPolarity]
  have hpol02 : literalPolarity l2 = 0 ∨ literalPolarity l2 = 1 := by
    cases l2 <;> simp [literalPolarity]
  have hidxw : uctPol2Reg ≤ K ∧ uctVar2Reg ≤ K ∧ uctPol3Reg ≤ K ∧
      uctVar3Reg ≤ K ∧ uctPosPolReg ≤ K ∧ uctFreshReg ≤ K := by
    simp [K, uctPol2Reg, uctVar2Reg, uctPol3Reg, uctVar3Reg, uctPosPolReg,
      uctFreshReg, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hcurJB : uctCurJ ≤ K := by
    simp [K, uctCurJ, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have htmpJB : uctTmpJ ≤ K := by
    simp [K, uctTmpJ, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hMcurB : uniformMNat N + uctCurJ ≤ K :=
    (uniform_emit_writer_layout_le_tight N).2.2.1.trans
      (uniformEmitTightEnvelope_le_long_value_envelope N)
  have hMtmpB : uniformMNat N + uctTmpJ ≤ K :=
    (uniform_emit_writer_layout_le_tight N).2.2.2.trans
      (uniformEmitTightEnvelope_le_long_value_envelope N)
  have hlow2 : uctPol2Reg < uniformStartNat ∧ uctVar2Reg < uniformStartNat := by
    simp [uctPol2Reg, uctVar2Reg, uniformStartNat, relocateControlGap]
  have hlow3 : uctPol3Reg < uniformStartNat ∧ uctVar3Reg < uniformStartNat := by
    simp [uctPol3Reg, uctVar3Reg, uniformStartNat, relocateControlGap]
  have hlowW : uctPosPolReg < uniformStartNat ∧ uctFreshReg < uniformStartNat := by
    simp [uctPosPolReg, uctFreshReg, uniformStartNat, relocateControlGap]
  have hpw := programBoundedIn_writerAppendThreeRegsProg_of_state K (uniformMNat N)
    uctCurJ uctTmpJ uniformStartNat pref uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctFreshReg (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hcurJB htmpJB hMcurB hMtmpB
    hidxw.1 hidxw.2.1 hidxw.2.2.1 hidxw.2.2.2.1 hidxw.2.2.2.2.1 hidxw.2.2.2.2.2
    hpol1 hvar1 hpol2 hvar2 hpos hfresh hpol01 hpol02 hlow2.2 hlow3 hlowW hυstate hroom
  refine ⟨hpw, program_eval_storeValuesLe υ _ hK1 hυ hpw
    (scanFree_writerAppendThreeRegsProg uctCurJ uctTmpJ uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctPosPolReg uctFreshReg), ?_⟩
  have hf := writerAppendThreeRegsProg_frame (uniformMNat N) uctCurJ uctTmpJ uniformStartNat pref
    uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctFreshReg
    (literalPolarity l1) l1.var (literalPolarity l2) l2.var 0 base υ
    uniform_cur_j_bounds.1 uniform_cur_j_bounds.2 hpol1 hvar1 hpol2 hvar2 hpos hfresh
    hpol01 hpol02 (Or.inl rfl) hlow2.2 hlow3 hlowW hυstate hroom hlowW.2
  exact hf.trans hfresh

/-- The four trailing assignments of the long-clause setup stay within the long value
    envelope, given the writer output `σw` is bounded and has fresh register `base`. -/
lemma storeValuesLe_uniform_long_clause_setup_at_tight_of_state_assigns
    (N base : ℕ) (σw : Store)
    (hσw : StoreValuesLe (uniformEmitLongValueEnvelope N) σw)
    (hfresh : σw uctFreshReg = base)
    (hbase1 : base + 1 ≤ uniformEmitLongValueEnvelope N)
    (hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg) :
    ProgramBoundedIn (uniformEmitLongValueEnvelope N) σw
      (.seq (.assign uctCarryPolReg (.const 1))
        (.seq (.assign uctCarryValReg (.reg uctFreshReg))
          (.seq (.assign uctFreshReg (.add (.reg uctFreshReg) (.const 1)))
            (.seq (.assign uctRemainingReg (.sub (.reg uctRemainingReg) (.const 2)))
              (.skip))))) := by
  set K := uniformEmitLongValueEnvelope N with hK
  have hidxp : uctCarryPolReg ≤ K ∧ uctCarryValReg ≤ K ∧ uctRemainingReg ≤ K := by
    simp [K, uctCarryPolReg, uctCarryValReg, uctRemainingReg,
      uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hK2 : 2 ≤ K := by
    simp [K, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  have hfreshK : uctFreshReg ≤ K := by
    simp [K, uctFreshReg, uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  obtain ⟨σ3, h3⟩ : ∃ σ3, σ3 = (Program.assign uctCarryPolReg (.const 1)).eval σw :=
    ⟨_, rfl⟩
  have hσ3 : StoreValuesLe K σ3 :=
    h3 ▸ storeValuesLe_assign hσw (by simp only [Expr.eval]; omega)
  have hσ3fresh : σ3 uctFreshReg = base := by
    rw [h3, eval_assign, writeReg_diff _ _ _ _ hsafety.writer_distinct.2.2.1.symm, hfresh]
  obtain ⟨σ4, h4⟩ : ∃ σ4, σ4 = (Program.assign uctCarryValReg (.reg uctFreshReg)).eval σ3 :=
    ⟨_, rfl⟩
  have hσ4 : StoreValuesLe K σ4 :=
    h4 ▸ storeValuesLe_assign hσ3 (by simp only [Expr.eval]; exact hσ3 uctFreshReg)
  have hσ4fresh : σ4 uctFreshReg = base := by
    rw [h4, eval_assign, writeReg_diff _ _ _ _ hsafety.writer_distinct.2.2.2.2.2.1.symm,
      hσ3fresh]
  obtain ⟨σ5, h5⟩ : ∃ σ5, σ5 = (Program.assign uctFreshReg
      (.add (.reg uctFreshReg) (.const 1))).eval σ4 := ⟨_, rfl⟩
  have hσ5 : StoreValuesLe K σ5 :=
    h5 ▸ storeValuesLe_assign hσ4 (by simp only [Expr.eval, hσ4fresh]; exact hbase1)
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · simp [ProgramBoundedIn, ExprBoundedIn, uctCarryPolReg]
    exact ⟨hidxp.1, by omega⟩
  · rw [← h3]
    simp [ProgramBoundedIn, ExprBoundedIn, uctCarryValReg, uctFreshReg]
    exact ⟨hidxp.2.1, hfreshK⟩
  · rw [← h3, ← h4]
    simp [ProgramBoundedIn, ExprBoundedIn, Expr.eval, hσ4fresh]
    omega
  · rw [← h3, ← h4, ← h5]
    have hremVal := hσ5 uctRemainingReg
    simp [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    exact ⟨hidxp.2.2, by omega⟩

lemma storeValuesLe_uniform_long_clause_setup_at_tight_of_state
    (N : ℕ)
    (base : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal) (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound1 : l1.var + 1 ≤ N) (hbound2 : l2.var + 1 ≤ N)
    (hinput : BitsFrom σ addr (splitTailInputBits (l1 :: l2 :: l3 :: rest) tail))
    (hcursor : σ uctCursorReg = addr)
    (hpos : σ uctPosPolReg = 0)
    (hfresh : σ uctFreshReg = base)
    (hwriter : WriterState σ (uniformMNat N) uctCurJ uniformStartNat pref)
    (hstartAtInput : uniformStartNat ≤ addr)
    (hsafety : SplitTailRegisterSafety uniformStartNat uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hcursorBudget : σ uctCursorReg + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N)
    (hroom : uniformStartNat + pref.length + l1.var + l2.var + base + 6 <
      uniformMNat N + uctCurJ)
    (hbase1 : base + 1 ≤ uniformEmitLongValueEnvelope N) :
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) := by
  have hK1 : 1 ≤ uniformEmitLongValueEnvelope N := by
    simp [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformMNat,
      uniformStartNat, uniformSlackNat, relocateControlGap]
    omega
  obtain ⟨hdec1, hdec2, hτ2store, hτ2eq⟩ :=
    storeValuesLe_uniform_long_clause_setup_at_tight_of_state_decode N σ hb hσ hcursorBudget
  obtain ⟨υ, hυ, hυstate, -, hpol1, hvar1, hpol2, hvar2, -, hwf, -⟩ :=
    splitTailEmitLongClauseSetup_eval_parse (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg
      uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg N l1 l2
      (l3 :: rest) pref tail addr σ hbound1 hbound2 hinput uniform_cur_j_bounds.2
      hstartAtInput hwriter hcursor hsafety
  have htau2 := hτ2eq.trans hυ.symm
  have hpos0 : υ uctPosPolReg = 0 := (hwf uctPosPolReg (by simp)).trans hpos
  have hfresh0 : υ uctFreshReg = base := (hwf uctFreshReg (by simp)).trans hfresh
  rw [htau2] at hτ2store
  obtain ⟨hpw, hσw, hfreshw⟩ :=
    storeValuesLe_uniform_long_clause_setup_at_tight_of_state_writer N base l1 l2 pref υ hτ2store
      hυstate hpol1 hvar1 hpol2 hvar2 hpos0 hfresh0 hroom
  have hassigns := storeValuesLe_uniform_long_clause_setup_at_tight_of_state_assigns N base _
    hσw hfreshw hbase1 hsafety
  have hprog : ProgramBoundedIn (uniformEmitLongValueEnvelope N) σ
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg) := by
    refine ⟨hdec1, hdec2, ?_, ?_⟩
    · rw [htau2]; exact hpw
    · rw [htau2]; exact hassigns
  exact program_eval_storeValuesLe σ _ hK1 hσ hprog
    (scanFree_splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)

structure EmitClauseDispatchRawBounds
    (B curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg boundReg : ℕ)
    (σ : Store) : Prop where
  bound : 3 ≤ B
  length : lengthReg ≤ B
  zero : ProgramBoundedIn B σ
    (Program.seq
      (writerAppendClauseEmptyProg curJ tmpJ posPolReg negPolReg freshReg)
      (Program.seq (emitClauseEmptyFreshProg freshReg)
        (emitClauseCommitProg outerReg)))
  one : ProgramBoundedIn B σ
    (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
      (Program.seq (writerAppendClauseOneProg curJ tmpJ polReg varReg)
        (emitClauseCommitProg outerReg)))
  two : ProgramBoundedIn B σ
    (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
      (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
        (Program.seq (writerAppendClauseTwoProg curJ tmpJ polReg varReg pol2Reg var2Reg)
          (emitClauseCommitProg outerReg))))
  three : ProgramBoundedIn B σ
    (Program.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
      (Program.seq (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg)
        (Program.seq (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg)
          (Program.seq
            (writerAppendClauseThreeProg curJ tmpJ polReg varReg pol2Reg var2Reg
              pol3Reg var3Reg posPolReg negPolReg freshReg)
            (Program.seq (emitClauseEmptyFreshProg freshReg)
              (emitClauseCommitProg outerReg))))))
  long : ProgramBoundedIn B σ
    (Program.seq
      (.assign remainingReg (.reg lengthReg))
      (Program.seq (.assign carryPolReg (.const 1))
        (Program.seq (.assign carryValReg (.reg freshReg))
          (Program.seq (.assign posPolReg (.const 0))
            (Program.seq
              (splitTailEmitLongClauseProgAt curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                posPolReg freshReg boundReg)
              (emitClauseCommitProg outerReg))))))

lemma programBoundedIn_emitClauseDispatchProgAt_of_raw_bounds
    (B curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg
       pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg freshReg outerReg
      boundReg : ℕ) (σ : Store)
    (h : EmitClauseDispatchRawBounds B curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg boundReg σ) :
    ProgramBoundedIn B σ
      (emitClauseDispatchProgAt curJ tmpJ cursorReg polReg varReg doneReg lengthReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
        carryValReg freshReg outerReg boundReg) := by
  exact programBoundedIn_emitClauseDispatchProgAt (var3Reg := var3Reg)
    B curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg
    posPolReg negPolReg carryPolReg carryValReg freshReg outerReg boundReg σ
    h.bound h.length h.zero h.one h.two h.three h.long

lemma storeValuesLe_uniformEmitScratchResetProg_tight
    (N : ℕ) (σ : Store)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope N) σ) :
    StoreValuesLe (uniformEmitTightEnvelope N) (uniformEmitScratchResetProg.eval σ) := by
  have hB1 : 1 ≤ uniformEmitTightEnvelope N := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hB25 : 25 ≤ uniformEmitTightEnvelope N := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  exact storeValuesLe_uniformEmitScratchResetProg (uniformEmitTightEnvelope N) σ hB1 hσ hB25

lemma programBoundedIn_uniformEmitIterBody_of_dispatch_raw
    (B : ℕ) (σ : Store) (hB25 : 25 ≤ B)
    (hdecode : ProgramBoundedIn B (uniformEmitScratchResetProg.eval σ)
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg))
    (hdispatch : EmitClauseDispatchRawBounds B uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
      uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
      uctOuterReg uctSavedBoundReg
        ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
          (uniformEmitScratchResetProg.eval σ)))
    (hreset : ProgramBoundedIn B
      ((emitClauseDispatchProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg
        uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg
        uctOuterReg uctSavedBoundReg).eval
        ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
          (uniformEmitScratchResetProg.eval σ)))
      uniformEmitResetProg) :
    ProgramBoundedIn B σ uniformEmitIterBody := by
  apply programBoundedIn_uniformEmitIterBody_of_program_parts B σ hB25 hdecode
  · exact programBoundedIn_emitClauseDispatchProgAt_of_raw_bounds B uctCurJ uctTmpJ
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg
      uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg uctCarryPolReg
      uctCarryValReg uctFreshReg uctOuterReg uctSavedBoundReg
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) hdispatch
  · exact hreset

lemma storeValuesLe_uniform_split_tail_emit_prog_at_of_window_raw
    (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) (n : ℕ)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel σ (uniformMNat N) uctCurJ uctTmpJ uniformStartNat base carry
      ls pref tail addr uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg)
    (hb : σ uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σ)
    (hraw : SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
      (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σ)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      (loopEval
        (splitTailEmitStepProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
          uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
          uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg)
        n σ) := by
  obtain ⟨τ, base', carry', ls', pref', addr', hτ, hstate⟩ :=
    uniform_split_tail_emit_prog_at_reachable_raw_of_window N inputEnd baseLimit base carry ls
      pref tail addr σ n hbound hrel hb hσ hraw hwin hinputEnd hbaseLimit hend
  rw [← hτ]
  rcases hstate with hrel' | hdone'
  · exact hrel'.raw.store
  · exact hdone'.done.raw.store

lemma storeValuesLe_uniform_splitTailEmitLongClauseProgAt_of_setup_raw
    (N inputEnd baseLimit : ℕ)
    (base : ℕ) (carry : NPComplete.SAT.Literal) (ls : List NPComplete.SAT.Literal)
    (pref tail : Bits) (addr : ℕ) (σ σsetup : Store) (n : ℕ)
    (hsetup :
      (splitTailEmitLongClauseSetupAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ = σsetup)
    (hcount : σsetup uctRemainingReg = n)
    (hk : 0 < n)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ N)
    (hrel : SplitTailEmitRel σsetup (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      base carry ls pref tail addr uctCursorReg uctPolReg uctVarReg
      uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg)
    (hb : σsetup uctSavedBoundReg = N)
    (hσ : StoreValuesLe (uniformEmitLongValueEnvelope N) σsetup)
    (hraw : SplitTailEmitStepRawBounds (uniformEmitLongValueEnvelope N)
      (uniformEmitSyntaxEnvelope N) (uniformMNat N) uctCurJ uctTmpJ uctCursorReg uctPolReg
      uctVarReg uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
      uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg σsetup)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hinputEnd : inputEnd ≤ uniformEmitLongValueEnvelope N)
    (hbaseLimit : baseLimit ≤ uniformEmitLongValueEnvelope N)
    (hend : inputEnd + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N) :
    StoreValuesLe (uniformEmitLongValueEnvelope N)
      ((splitTailEmitLongClauseProgAt uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
        uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
        uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg).eval σ) := by
  have hloop := storeValuesLe_uniform_split_tail_emit_prog_at_of_window_raw N inputEnd baseLimit
    base carry ls pref tail addr σsetup (n + 1) hbound hrel hb hσ hraw hwin
    hinputEnd hbaseLimit hend
  rw [splitTailEmitLongClauseProgAt, eval_seq, hsetup]
  rw [splitTailEmitProgAt_pos_eval uctCurJ uctTmpJ uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctCarryPolReg uctCarryValReg uctPosPolReg uctFreshReg uctSavedBoundReg n σsetup
    hcount hk]
  exact hloop

end NPComplete.CookLevin

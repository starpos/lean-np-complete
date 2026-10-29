module

public import NPComplete.CookLevin.ToThreeCNF.LongSafety

/-!
# Long-clause loop completion

A split-tail writer must reduce a nonempty suffix to a terminal clause while
preserving the emitter's store invariants. This module lifts its single-step
transition to loop completion, giving the outer clause proof a composable
long-branch result.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
  (BitsFrom bitsFrom_append bitsFrom_writeReg bitsFrom_of_eq_on BitsAt bitsAt_of_frame finalizeOutputProg FinalizeRegsOk ctlCell ctlCell_eval)
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same cost_seq
    cost_ifNZ cost_forN eval_ifNZ eval_forN loopEval loopEval_succ
    loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
/-! The semantic loop theorem below deliberately exposes the terminal
parameters.  After an intermediate link, the carried literal and base are
updated, so the terminal `SplitTailEmitDone` naturally describes the
remaining suffix rather than pretending that the original base is unchanged.
The returned `loopEval` count is the number of step-program iterations. -/

/-- Conclusion of the nonempty-suffix emit loop: the step program, iterated, reaches a terminal
store with the high-register frame and cursor accounting. Naming it lets the inductive case take
the recursive call as a hypothesis. -/
def SplitTailNonemptyDoneFrameGoal
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) : Prop :=
  ∃ k τ base' carry' ls' pref' addr',
    k ≤ ls.length + 1 ∧
    τ = loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      k σ ∧
    SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
      cursorReg remainingReg freshReg posPolReg ∧
    base' = (splitTail base carry ls).2 ∧
    pref' ++ splitTailPayload base' carry' ls' =
      pref ++ splitTailPayload base carry ls ∧
    τ cursorReg = addr + (splitTailInputBits ls []).length ∧
    (∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r)

/-- Single-literal suffix: one step of the loop is the terminal-one program. -/
lemma splitTailEmitRel_nonempty_to_done_after_frame_one
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l : Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    SplitTailNonemptyDoneFrameGoal M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry [l] pref tail addr σ := by
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_one_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l pref tail addr σ hbound hrel
  have hstep := splitTailEmitStepProg_one_eval
    curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound σ hrel.remaining
  refine ⟨1, τ, base, carry, [l], pref, addr, by simp, ?_, hdone, rfl, ?_, hdone.done.cursor, ?_⟩
  · rw [hτ, loopEval_succ]
    simpa [splitTailEmitStepProg] using hstep.symm
  · simp [splitTailPayload]
  · intro r hr hrc hrt
    have hlen : carry.var + 2 * l.var + 6 ≤ (splitTailPayload base carry [l]).length := by
      cases carry <;> cases l <;>
        simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
          Literal.var] <;> omega
    have hr' : start + pref.length + carry.var + 2 * l.var + 6 ≤ r := by
      rw [hdone.done.writer.cursor] at hr
      simp [List.length_append] at hr ⊢
      omega
    rw [hτ]
    exact splitTailEmitTerminalOneProg_after_frame_of_rel
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l pref
      tail addr σ hbound hrel hr' hrc hrt

/-- Two-literal suffix: one step of the loop is the terminal-two program. -/
lemma splitTailEmitRel_nonempty_to_done_after_frame_two
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 : Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound) (hbound2 : l2.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry [l, l2] pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    SplitTailNonemptyDoneFrameGoal M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry [l, l2] pref tail addr σ := by
  obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_two_to_done_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l l2 pref tail addr σ hbound hbound2 hrel
  have hstep := splitTailEmitStepProg_two_eval
    curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
    carryPolReg carryValReg posPolReg freshReg bound σ hrel.remaining
  refine ⟨1, τ, base, carry, [l, l2], pref, addr, by simp, ?_, hdone, rfl, ?_,
    hdone.done.cursor, ?_⟩
  · rw [hτ, loopEval_succ]
    simpa [splitTailEmitStepProg] using hstep.symm
  · simp [splitTailPayload]
  · intro r hr hrc hrt
    have hlen : carry.var + l.var + l2.var + 6 ≤
        (splitTailPayload base carry [l, l2]).length := by
      cases carry <;> cases l <;> cases l2 <;>
        simp [splitTailPayload, encodeThreeClause, encodeLiteral, encodeNat_length,
          Literal.var] <;> omega
    have hr' : start + pref.length + carry.var + l.var + l2.var + 6 ≤ r := by
      rw [hdone.done.writer.cursor] at hr
      simp [List.length_append] at hr ⊢
      omega
    rw [hτ]
    exact splitTailEmitTerminalTwoProg_after_frame_of_rel
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l l2
      pref tail addr σ hbound hbound2 hrel hr' hrc hrt

/-- Three-or-more suffix: one intermediate step, then the recursive call on the shorter suffix. -/
lemma splitTailEmitRel_nonempty_to_done_after_frame_cons
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry (l :: l2 :: l3 :: rest)
      pref tail addr cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg
      var3Reg carryPolReg carryValReg posPolReg freshReg)
    (ih : ∀ τ1,
      SplitTailEmitRel τ1 M curJ tmpJ start (base + 1) (Literal.neg base) (l2 :: l3 :: rest)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base) tail
        (addr + l.var + 2) cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg →
      SplitTailNonemptyDoneFrameGoal M curJ tmpJ start cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        bound (base + 1) (Literal.neg base) (l2 :: l3 :: rest)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base) tail
        (addr + l.var + 2) τ1) :
    SplitTailNonemptyDoneFrameGoal M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      bound base carry (l :: l2 :: l3 :: rest) pref tail addr σ := by
  obtain ⟨τ1, hτ1, hrel1⟩ := splitTailEmitRel_intermediate_to_rel
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l l2 l3 rest pref tail addr σ hbound hrel
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone, hbase', hpayload',
    hcursor', hafter⟩ := ih τ1 hrel1
  have hstep : (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ
      = τ1 := by
    simp [splitTailEmitStepProg, hrel.remaining, Expr.eval, hτ1]
  have hhigh := splitTailEmitIntermediateProg_frame_of_rel
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
    base carry l l2 l3 rest pref tail addr σ hbound hrel
  refine ⟨k + 1, τ, base', carry', ls', pref', addr', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons] at hk ⊢
    omega
  · rw [loopEval_succ, hstep]
    exact hloop
  · refine ⟨hdone.done, fun q hq => ?_, hdone.pos⟩
    exact (hdone.high_frame q hq).trans (by simpa [hτ1] using hhigh.1 q hq)
  · simpa [splitTail] using hbase'
  · rw [hpayload', splitTailPayload_cons3, hrel.carry_one]
    simp [List.append_assoc]
  · have hlen : (encodeLiteral l).length = l.var + 2 := by
      cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
    have hsplit : (splitTailInputBits (l :: l2 :: l3 :: rest) []).length =
        l.var + 2 + (splitTailInputBits (l2 :: l3 :: rest) []).length := by
      simp [splitTailInputBits, List.length_append, hlen]
    rw [hcursor', hsplit]
    omega
  · intro r hr hrc hrt
    have hτ1le : τ1 (M + curJ) ≤ τ (M + curJ) := by
      rw [hrel1.writer.cursor, hdone.done.writer.cursor, hpayload']
      simp [List.length_append]
    have hr1' : start + pref.length + carry.var + l.var + base + 6 ≤ r := by
      have hr1 := le_trans hτ1le hr
      rw [hrel1.writer.cursor] at hr1
      simp [encodedThreeLiteralBits, encodedLiteralBits, encodeNat_length,
        List.length_append] at hr1 ⊢
      omega
    have hinter := splitTailEmitIntermediateProg_after_frame_of_rel
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      base carry l l2 l3 rest pref tail addr σ hbound hrel hr1' hrc hrt
    exact (hafter r hr hrc hrt).trans (by simpa [hτ1] using hinter)

lemma splitTailEmitRel_nonempty_to_done_after_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ k τ base' carry' ls' pref' addr',
      k ≤ ls.length + 1 ∧
      τ = loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        k σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg posPolReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length ∧
      (∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r) := by
  match ls, hbound, hne, hrel with
  | [], _, hne, _ => exact False.elim (hne rfl)
  | [l], hbound, _, hrel =>
      exact splitTailEmitRel_nonempty_to_done_after_frame_one
        M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        base carry l pref tail addr σ (hbound l (by simp)) hrel
  | [l, l2], hbound, _, hrel =>
      exact splitTailEmitRel_nonempty_to_done_after_frame_two
        M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        base carry l l2 pref tail addr σ (hbound l (by simp)) (hbound l2 (by simp)) hrel
  | l :: l2 :: l3 :: rest, hbound, _, hrel =>
      exact splitTailEmitRel_nonempty_to_done_after_frame_cons
        M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        base carry l l2 l3 rest pref tail addr σ (hbound l (by simp)) hrel
        (fun τ1 hrel1 =>
          splitTailEmitRel_nonempty_to_done_after_frame
            M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg
            var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
            (base + 1) (Literal.neg base) (l2 :: l3 :: rest)
            (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
            tail (addr + l.var + 2) τ1
            (fun x hx => hbound x (by simpa only [List.mem_cons] using Or.inr hx))
            (by simp) hrel1)

lemma splitTailEmitRel_nonempty_to_done
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ k τ base' carry' ls' pref' addr',
      k ≤ ls.length + 1 ∧
      τ = loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        k σ ∧
      SplitTailEmitDone τ M curJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length := by
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone,
      hbase', hpayload', hcursor', _⟩ :=
    splitTailEmitRel_nonempty_to_done_after_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        base carry ls pref tail addr σ hbound hne hrel
  exact ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone.done,
    hbase', hpayload', hcursor'⟩

lemma splitTailEmitRel_nonempty_to_done_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ k τ base' carry' ls' pref' addr',
      k ≤ ls.length + 1 ∧
      τ = loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        k σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg posPolReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length := by
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone,
      hbase', hpayload', hcursor', _⟩ :=
    splitTailEmitRel_nonempty_to_done_after_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        base carry ls pref tail addr σ hbound hne hrel
  exact ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone,
    hbase', hpayload', hcursor'⟩

lemma splitTailEmitRel_nonempty_to_done_low_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
      r ≠ remainingReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
      r ≠ var3Reg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ posPolReg ∧
      r ≠ freshReg) :
    ∃ k τ, k ≤ ls.length + 1 ∧
      τ = loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        k σ ∧ τ r = σ r ∧ τ remainingReg = 0 := by
  rcases hrsafe with ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3,
    hcp, hcv, hpos, hfr⟩
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  cases ls with
  | nil => exact False.elim (hne rfl)
  | cons l rest =>
      cases rest with
      | nil =>
          obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_one_to_done
            M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
            pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
            base carry l pref tail addr σ (hbound l (by simp)) hrel
          have hl := splitTailEmitTerminalOneProg_low_frame_of_rel
            M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
            pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l
            pref tail addr σ (hbound l (by simp)) hrel hr
            ⟨hrc, hrp2, hrv2, hrd, hcp, hcv, hrem⟩
          have hs := splitTailEmitStepProg_one_eval
            curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
            carryPolReg carryValReg posPolReg freshReg bound σ hrel.remaining
          refine ⟨1, τ, by simp, ?_, ?_, hdone.remaining⟩
          · calc
              τ = (splitTailEmitTerminalOneProg curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg bound).eval σ := hτ
              _ = body.eval σ := by simpa [body] using hs.symm
              _ = loopEval body 1 σ := by simp
          · rw [hτ]
            exact hl
      | cons l2 rest =>
          cases rest with
          | nil =>
              obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_two_to_done
                M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
                pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
                base carry l l2 pref tail addr σ (hbound l (by simp)) (hbound l2 (by simp)) hrel
              have hl := splitTailEmitTerminalTwoProg_low_frame_of_rel
                M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
                pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l l2
                pref tail addr σ (hbound l (by simp)) (hbound l2 (by simp)) hrel hr
                ⟨hrc, hrp2, hrv2, hrp3, hrv3, hrd, hcp, hcv, hrem⟩
              have hs := splitTailEmitStepProg_two_eval
                curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
                carryPolReg carryValReg posPolReg freshReg bound σ hrel.remaining
              refine ⟨1, τ, by simp, ?_, ?_, hdone.remaining⟩
              · calc
                  τ = (splitTailEmitTerminalTwoProg curJ tmpJ cursorReg polReg varReg doneReg
                    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                    posPolReg freshReg bound).eval σ := hτ
                  _ = body.eval σ := by simpa [body] using hs.symm
                  _ = loopEval body 1 σ := by simp
              · rw [hτ]
                exact hl
          | cons l3 rest =>
              obtain ⟨τ1, hτ1, hrel1⟩ := splitTailEmitRel_intermediate_to_rel
                M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
                pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
                base carry l l2 l3 rest pref tail addr σ (hbound l (by simp)) hrel
              have hl1 := splitTailEmitStepProg_low_frame_of_rel
                M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
                pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry
                (l :: l2 :: l3 :: rest) pref tail addr σ hbound hrel hr
                ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3, hcp, hcv, hpos, hfr⟩
              have hbound1 : ∀ x ∈ (l2 :: l3 :: rest), x.var + 1 ≤ bound := by
                intro x hx
                exact hbound x (by simpa only [List.mem_cons] using Or.inr hx)
              obtain ⟨k, τ, hk, hloop, hl2, hl2rem⟩ :=
                splitTailEmitRel_nonempty_to_done_low_frame
                  M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
                  pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
                  (base + 1) (Literal.neg base) (l2 :: l3 :: rest)
                  (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
                  tail (addr + l.var + 2) τ1 hbound1 (by simp) hrel1 hr
                  ⟨hrc, hrp, hrv, hrd, hrem, hrp2, hrv2, hrp3, hrv3, hcp, hcv, hpos, hfr⟩
              have hstep : body.eval σ = τ1 := by
                calc
                  body.eval σ =
                      (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
                        remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
                          simp [body, splitTailEmitStepProg, hrel.remaining, Expr.eval]
                  _ = τ1 := hτ1.symm
              refine ⟨k + 1, τ, ?_, ?_, ?_, hl2rem⟩
              · simp only [List.length_cons] at hk ⊢
                omega
              · calc
                  τ = loopEval body k τ1 := hloop
                  _ = loopEval body k (body.eval σ) := by rw [hstep]
                  _ = loopEval body (k + 1) σ := by rw [loopEval_succ]
              · exact hl2.trans ((congrArg (fun q : Store => q r) hstep).symm.trans hl1)

lemma splitTailEmitProg_eval_eq_loopEval_of_remaining
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ)
    (σ τ : Store) (body : Program) (k : ℕ)
    (hk : k ≤ tailBound + 1)
    (hloop : τ = loopEval body k σ)
    (hbody : body = splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg bound)
    (hzero : ∀ ρ : Store, ρ remainingReg = 0 → body.eval ρ = ρ)
    (hrem : σ remainingReg ≠ 0) (hτ : τ remainingReg = 0) :
    (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      tailBound).eval σ = τ := by
  have hpad : loopEval body (tailBound + 1) σ = τ := by
    rw [show tailBound + 1 = k + (tailBound + 1 - k) by omega,
      loopEval_add_right_local body k (tailBound + 1 - k) σ, ← hloop]
    have hzeroLoop : ∀ n : ℕ, loopEval body n τ = τ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [loopEval_succ, hzero τ hτ]
          exact ih
    exact hzeroLoop _
  have hprog :
      (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        tailBound).eval σ = loopEval body (tailBound + 1) σ := by
    rw [hbody, splitTailEmitProg, eval_ifNZ]
    split_ifs <;> simp_all [eval_forN, Expr.eval]
  rw [hprog, hpad]

lemma splitTailEmitRel_nonempty_fixed_eval_low_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ []) (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    {r : ℕ}
    (hr : r < start)
    (hrsafe : r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
      r ≠ remainingReg ∧ r ≠ pol2Reg ∧ r ≠ var2Reg ∧ r ≠ pol3Reg ∧
      r ≠ var3Reg ∧ r ≠ carryPolReg ∧ r ≠ carryValReg ∧ r ≠ posPolReg ∧
      r ≠ freshReg) :
    (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      tailBound).eval σ r = σ r := by
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  obtain ⟨k, τ, hk, hloop, hτr, hτrem⟩ := splitTailEmitRel_nonempty_to_done_low_frame
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry ls pref tail addr σ
    hbound hne hrel hr hrsafe
  have hk' : k ≤ tailBound + 1 := by omega
  have hzero : ∀ ρ : Store, ρ remainingReg = 0 → body.eval ρ = ρ := by
    intro ρ hρ
    exact splitTailEmitStepProg_zero_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound ρ hρ
  have hrem0 : σ remainingReg ≠ 0 := by
    rw [hrel.remaining]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hne)
  have hfinish := splitTailEmitProg_eval_eq_loopEval_of_remaining
    (curJ := curJ) (tmpJ := tmpJ) (cursorReg := cursorReg) (polReg := polReg)
    (varReg := varReg) (doneReg := doneReg) (remainingReg := remainingReg)
    (pol2Reg := pol2Reg) (var2Reg := var2Reg) (pol3Reg := pol3Reg)
    (var3Reg := var3Reg) (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (bound := bound)
    (tailBound := tailBound) (σ := σ) (τ := τ) (body := body) (k := k)
    hk' hloop (by rfl) hzero hrem0 hτrem
  rw [hfinish]
  exact hτr

lemma splitTailEmitRel_nonempty_fixed_eval
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        tailBound).eval σ ∧
      SplitTailEmitDone τ M curJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length := by
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone, hbaseStrong,
      hpayloadStrong, hcursorStrong⟩ :=
    splitTailEmitRel_nonempty_to_done
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      base carry ls pref tail addr σ hbound hne hrel
  have hk' : k ≤ tailBound + 1 := by
    omega
  have hzero : ∀ ρ : Store, ρ remainingReg = 0 → body.eval ρ = ρ := by
    intro ρ hρ
    simp [body, splitTailEmitStepProg, hρ, Expr.eval]
  have hrem0 : σ remainingReg ≠ 0 := by
    rw [hrel.remaining]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hne)
  have hfinish := splitTailEmitProg_eval_eq_loopEval_of_remaining
    (curJ := curJ) (tmpJ := tmpJ) (cursorReg := cursorReg) (polReg := polReg)
    (varReg := varReg) (doneReg := doneReg) (remainingReg := remainingReg)
    (pol2Reg := pol2Reg) (var2Reg := var2Reg) (pol3Reg := pol3Reg)
    (var3Reg := var3Reg) (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (bound := bound)
    (tailBound := tailBound) (σ := σ) (τ := τ) (body := body) (k := k)
    hk' hloop (by rfl) hzero hrem0 hdone.remaining
  refine ⟨τ, base', carry', ls', pref', addr', ?_, hdone, hbaseStrong,
    hpayloadStrong, hcursorStrong⟩
  exact hfinish.symm

lemma splitTailEmitRel_nonempty_fixed_eval_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ [])
    (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        tailBound).eval σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg posPolReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length := by
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop, hdone,
      hbaseStrong, hpayloadStrong, hcursorStrong⟩ :=
    splitTailEmitRel_nonempty_to_done_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      base carry ls pref tail addr σ hbound hne hrel
  have hk' : k ≤ tailBound + 1 := by omega
  have hzero : ∀ ρ : Store, ρ remainingReg = 0 → body.eval ρ = ρ := by
    intro ρ hρ
    simp [body, splitTailEmitStepProg, hρ, Expr.eval]
  have hrem0 : σ remainingReg ≠ 0 := by
    rw [hrel.remaining]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hne)
  have hfinish := splitTailEmitProg_eval_eq_loopEval_of_remaining
    (curJ := curJ) (tmpJ := tmpJ) (cursorReg := cursorReg) (polReg := polReg)
    (varReg := varReg) (doneReg := doneReg) (remainingReg := remainingReg)
    (pol2Reg := pol2Reg) (var2Reg := var2Reg) (pol3Reg := pol3Reg)
    (var3Reg := var3Reg) (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (bound := bound)
    (tailBound := tailBound) (σ := σ) (τ := τ) (body := body) (k := k)
    hk' hloop (by rfl) hzero hrem0 hdone.done.remaining
  refine ⟨τ, base', carry', ls', pref', addr', ?_, hdone, hbaseStrong,
    hpayloadStrong, hcursorStrong⟩
  exact hfinish.symm

lemma splitTailEmitRel_nonempty_fixed_eval_after_frame
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ []) (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg) :
    ∃ τ base' carry' ls' pref' addr',
      τ = (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
        tailBound).eval σ ∧
      SplitTailEmitDoneFrame τ σ M curJ tmpJ start base' carry' ls' pref' tail addr'
        cursorReg remainingReg freshReg posPolReg ∧
      base' = (splitTail base carry ls).2 ∧
      pref' ++ splitTailPayload base' carry' ls' =
        pref ++ splitTailPayload base carry ls ∧
      τ cursorReg = addr + (splitTailInputBits ls []).length ∧
      (∀ r, τ (M + curJ) ≤ r → r ≠ M + curJ → r ≠ M + tmpJ → τ r = σ r) := by
  let body := splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
  obtain ⟨k, τ, base', carry', ls', pref', addr', hk, hloop,
      hdone, hbase', hpayload', hcursor', hafter⟩ :=
    splitTailEmitRel_nonempty_to_done_after_frame
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      base carry ls pref tail addr σ hbound hne hrel
  have hk' : k ≤ tailBound + 1 := by omega
  have hzero : ∀ ρ : Store, ρ remainingReg = 0 → body.eval ρ = ρ := by
    intro ρ hρ
    exact splitTailEmitStepProg_zero_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound ρ hρ
  have hrem0 : σ remainingReg ≠ 0 := by
    rw [hrel.remaining]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hne)
  have hfinish := splitTailEmitProg_eval_eq_loopEval_of_remaining
    (curJ := curJ) (tmpJ := tmpJ) (cursorReg := cursorReg) (polReg := polReg)
    (varReg := varReg) (doneReg := doneReg) (remainingReg := remainingReg)
    (pol2Reg := pol2Reg) (var2Reg := var2Reg) (pol3Reg := pol3Reg)
    (var3Reg := var3Reg) (carryPolReg := carryPolReg) (carryValReg := carryValReg)
    (posPolReg := posPolReg) (freshReg := freshReg) (bound := bound)
    (tailBound := tailBound) (σ := σ) (τ := τ) (body := body) (k := k)
    hk' hloop (by rfl) hzero hrem0 hdone.done.remaining
  refine ⟨τ, base', carry', ls', pref', addr', ?_, hdone, hbase', hpayload', hcursor', hafter⟩
  exact hfinish.symm

end NPComplete.CookLevin

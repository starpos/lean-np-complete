module

public import NPComplete.CookLevin.Verifier.Depair
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-!
# Bounded depairing program

The verifier's packed input is split into paired bit lists by a loop, so compiled
execution needs the step and iteration to stay within a fixed memory window.
This module supplies those bounds for the depair program before the parser uses
its output.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits)

/-- `depairStep` keeps every address and value it computes `≤ B`. The control-register indices are
    bounded by `B`; `cursorReg`, `dstReg`, and `countReg` are pairwise distinct, `cursorReg ≠ doneReg`,
    the first three are distinct from the current write address `σ dstReg`, and their current values
    leave one step's worth of headroom under `B`. -/
lemma depairStep_programBoundedIn (B cursorReg dstReg countReg doneReg : ℕ) (σ : Store)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg)
    (hci : cursorReg ≤ B) (hdi : dstReg ≤ B) (hki : countReg ≤ B) (hni : doneReg ≤ B)
    (hB1 : 1 ≤ B)
    (hCurDst : cursorReg ≠ σ dstReg) (hDstDst : dstReg ≠ σ dstReg) (hCountDst : countReg ≠ σ dstReg)
    (hcursor : σ cursorReg + 2 ≤ B) (hdst : σ dstReg + 1 ≤ B) (hcount : σ countReg + 1 ≤ B) :
    ProgramBoundedIn B σ (depairStep cursorReg dstReg countReg doneReg) := by
  unfold depairStep
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_assign, eval_assignInd]
  refine ⟨hni, trivial, ⟨hci, by omega⟩,
    ⟨⟨hdi, ⟨⟨hci, hB1, by omega⟩, by omega⟩, by omega⟩, ?_⟩, ?_⟩
  · set σ1 := writeReg σ (σ dstReg) (σ (σ cursorReg + 1)) with hσ1
    have hcur1 : σ1 cursorReg = σ cursorReg := writeReg_diff σ (σ dstReg) _ cursorReg hCurDst
    have hdst1 : σ1 dstReg = σ dstReg := writeReg_diff σ (σ dstReg) _ dstReg hDstDst
    have hcnt1 : σ1 countReg = σ countReg := writeReg_diff σ (σ dstReg) _ countReg hCountDst
    refine ⟨⟨hci, hci, by omega, by rw [hcur1]; omega⟩, ?_⟩
    set σ2 := writeReg σ1 cursorReg (σ1 cursorReg + 2) with hσ2
    have hdst2 : σ2 dstReg = σ1 dstReg := writeReg_diff σ1 cursorReg _ dstReg (Ne.symm hcd0)
    have hcnt2 : σ2 countReg = σ1 countReg := writeReg_diff σ1 cursorReg _ countReg (Ne.symm hck0)
    refine ⟨⟨hdi, hdi, by omega, by rw [hdst2, hdst1]; omega⟩, ?_⟩
    set σ3 := writeReg σ2 dstReg (σ2 dstReg + 1) with hσ3
    have hcnt3 : σ3 countReg = σ2 countReg := writeReg_diff σ2 dstReg _ countReg (Ne.symm hdk0)
    exact ⟨hki, hki, by omega, by rw [hcnt3, hcnt2, hcnt1]; omega⟩
  · refine ⟨⟨hni, hB1⟩, ?_⟩
    set τ1 := writeReg σ doneReg 1 with hτ1
    have hcurτ1 : τ1 cursorReg = σ cursorReg := writeReg_diff σ doneReg 1 cursorReg hcDone
    exact ⟨hci, hci, by omega, by rw [hcurτ1]; omega⟩

/-- `doubleBits` distributes over `++`, mirroring `List.flatMap_append`. -/
lemma doubleBits_append (x y : List Bool) :
    doubleBits (x ++ y) = doubleBits x ++ doubleBits y := by
  simp [doubleBits, List.flatMap_append]

/-- The de-pair loop's register values at any prefix count `m ≤ x.length`: an
    intermediate-store specialization of `depair_loop_correct` obtained by splitting
    `x` at `m` and absorbing the undecoded tail into `rest`. -/
lemma depair_loop_prefix (cursorReg dstReg countReg doneReg : ℕ)
    (hcd0 : cursorReg ≠ dstReg) (hck0 : cursorReg ≠ countReg) (hdk0 : dstReg ≠ countReg)
    (hcDone : cursorReg ≠ doneReg) (hdDone : dstReg ≠ doneReg) (hkDone : countReg ≠ doneReg)
    (x : List Bool) (addr dst0 c0 : ℕ) (rest : Bits) (σ : Store)
    (hca : cursorReg < addr) (hda : dstReg < addr) (hka : countReg < addr) (hna : doneReg < addr)
    (hgap : addr + (doubleBits x ++ rest).length ≤ dst0)
    (hc : σ cursorReg = addr) (hd : σ dstReg = dst0) (hk : σ countReg = c0) (hn : σ doneReg = 0)
    (hbits : BitsFrom σ addr (doubleBits x ++ rest)) :
    ∀ m ≤ x.length,
      (loopEval (depairStep cursorReg dstReg countReg doneReg) m σ) cursorReg = addr + 2 * m ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) m σ) dstReg = dst0 + m ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) m σ) countReg = c0 + m ∧
      (loopEval (depairStep cursorReg dstReg countReg doneReg) m σ) doneReg = 0 := by
  intro m hm
  have hsplit : x = x.take m ++ x.drop m := (List.take_append_drop m x).symm
  have hlen : (x.take m).length = m := by simp; omega
  have hshape : doubleBits x ++ rest =
      doubleBits (x.take m) ++ (doubleBits (x.drop m) ++ rest) := by
    conv_lhs => rw [hsplit, doubleBits_append]
    rw [List.append_assoc]
  rw [hshape] at hgap hbits
  obtain ⟨g1, g2, g3, g4, _, _, _⟩ := depair_loop_correct cursorReg dstReg countReg doneReg
    hcd0 hck0 hdk0 hcDone hdDone hkDone (x.take m) addr dst0 c0
    (doubleBits (x.drop m) ++ rest) σ hca hda hka hna hgap hc hd hk hn hbits
  rw [hlen] at g1 g2 g3 g4
  exact ⟨g1, g2, g3, g4⟩

end NPComplete.CookLevin

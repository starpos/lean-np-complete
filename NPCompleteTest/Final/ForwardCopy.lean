module

public import NPComplete

@[expose] public section

namespace NPCompleteTest.ForwardCopy

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitEncoding

def linearDst : Expr := .add (.add (.reg 0) (.reg 0)) (.const 101)
def quadraticDst : Expr :=
  .add (.mul (.add (.reg 0) (.const 2)) (.add (.reg 0) (.const 2))) (.const 101)

lemma linear_gap (bits : Bits) : bits.length + 2 < linearDst.eval (bitInputStore bits) := by
  simp [linearDst, Expr.eval, bitInputStore_zero]
  omega

lemma linear_correct (bits : Bits) :
    BitsFrom ((forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore bits))
      (2 * bits.length + 101) bits ∧
    ∀ r ≤ bits.length,
      (forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore bits) r = bitInputStore bits r := by
  simpa [linearDst, Expr.eval, bitInputStore_zero, two_mul] using
    forwardCopyProg_correct_bitInputStore bits linearDst (linear_gap bits)

example (bits : Bits) (i : ℕ) (hi : i < bits.length) :
    (forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore bits)
      (2 * bits.length + 101 + i) = if bits[i] then 1 else 0 :=
  (linear_correct bits).1 i hi

example (bits : Bits) (r : ℕ) (hr : r < 2 * bits.length + 101)
    (ha : r ≠ bits.length + 1) (hb : r ≠ bits.length + 2) :
    (forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore bits) r = bitInputStore bits r := by
  have hl : ForwardCopyLayout 1 0 1 2 (bitInputStore bits 0)
      (linearDst.eval (bitInputStore bits)) := by
    simp only [ForwardCopyLayout, bitInputStore_zero, max_lt_iff, linearDst, Expr.eval]
    omega
  apply forwardCopyProg_frame 1 0 1 2 linearDst (bitInputStore bits) hl r
  · simpa only [bitInputStore_zero] using ha
  · simpa only [bitInputStore_zero] using hb
  · left; simpa [linearDst, Expr.eval, bitInputStore_zero, two_mul] using hr

lemma linear_bounded (bits : Bits) :
    ProgramBoundedIn (3 * bits.length + 101) (bitInputStore bits)
      (forwardCopyProg 1 0 1 2 linearDst) := by
  apply forwardCopyProg_programBoundedIn_bitInputStore bits linearDst _ (linear_gap bits)
  · simp only [linearDst, ExprBoundedIn, Expr.eval, bitInputStore_zero]
    omega
  · simp only [linearDst, Expr.eval, bitInputStore_zero]
    omega

lemma quadratic_bounded (bits : Bits) :
    ProgramBoundedIn ((bits.length + 2)^2 + 101 + bits.length) (bitInputStore bits)
      (forwardCopyProg 1 0 1 2 quadraticDst) := by
  apply forwardCopyProg_programBoundedIn_bitInputStore bits quadraticDst
  · simp only [quadraticDst, Expr.eval, bitInputStore_zero]
    nlinarith
  · have h : bits.length + 2 ≤ (bits.length + 2) * (bits.length + 2) := by nlinarith
    simp only [quadraticDst, ExprBoundedIn, Expr.eval, bitInputStore_zero, pow_two]
    omega
  · simp only [quadraticDst, Expr.eval, bitInputStore_zero, pow_two, le_refl]

noncomputable def linearDecider : BoundedWhileDecider id (fun _ : Bits => True)
    (fun bits => (forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore bits) 0 = 1) :=
  BoundedWhileDecider.ofProgramBoundedIn id (forwardCopyProg 1 0 1 2 linearDst) 0
    (fun L => 3 * L + 101) (Polynomial.C 3 * Polynomial.X + Polynomial.C 101)
    (by intro L; simp) (scanFree_forwardCopyProg 1 0 1 2 linearDst) linear_bounded

example : (forwardCopyProg 1 0 1 2 linearDst).eval (bitInputStore []) 0 = 0 := by
  simpa [bitInputStore_zero] using (linear_correct []).2 0 (by simp)

def scratchStore : Store := fun r => if r = 1 then 5 else 0
def scratchDst : Expr := .regInd (.add (.reg 0) (.const 1))

example : (forwardCopyProg 1 0 1 2 scratchDst).eval scratchStore 2 = 5 := by
  simp [forwardCopyProg, eval_seq, eval_assignInd, eval_forN, scratchDst, scratchStore,
    Expr.eval, writeReg, loopEval_zero]

end NPCompleteTest.ForwardCopy

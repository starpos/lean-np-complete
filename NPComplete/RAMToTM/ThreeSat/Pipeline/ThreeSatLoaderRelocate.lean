module

public import NPComplete.RAMToTM.Generic.LoadRelocate
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatInputRelocate
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Flatten

/-!
# 3-SAT loader relocation contract

This facade keeps the bit-vector and clause-encoding contracts used by 3-SAT callers while the
wide-gap relocation mechanics remain independent of the encoding.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg_same writeReg_diff)
open NPComplete.BoundedWhile (writeReg cost_seq cost_forN
  loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits)

/-! ## Layout and structured postconditions -/

def LoadRelocInput (σ : Store) (bits : Bits) : Prop :=
  σ 0 = bits.length ∧ BitsFrom σ 1 bits

/-! ## `bitInputStore` satisfies the relocation input promise -/

/-- `bitInputStore bits` is a valid `loadRelocProg` input: cell `0` already holds `bits.length` by
    construction, and the bit region matches `BitsFrom` from `bits_from_bitInputStore`. -/
lemma loadRelocInput_bitInputStore (bits : Bits) :
    LoadRelocInput (bitInputStore bits) bits :=
  ⟨by simp [bitInputStore], bits_from_bitInputStore bits⟩

def LoadRelocPost (σ : Store) (bits : Bits) : Prop :=
  σ 0 = bits.length ∧
  BitsFrom σ (2 * bits.length + loadRelocControlGap) bits ∧
  σ (bits.length + loadRelocSrcJ) = bits.length + 1 ∧
  σ (bits.length + loadRelocDstJ) =
    2 * bits.length + loadRelocControlGap + bits.length ∧
  σ (bits.length + loadRelocLenJ) = bits.length ∧
  σ (bits.length + loadRelocBaseJ) =
    2 * bits.length + loadRelocControlGap

/- The two-sided frame below is deliberately not a claim that the original input may be
   discarded.  The eventual finalize phase must cover the original `[1, N]` region either by
   overwriting it in the output window or by including it in its zeroing range; a function-wide
   canonical-store equality cannot justify destruction merely because decoding has finished. -/

lemma loadRelocProg_output (σ : Store) (bits : Bits)
    (hin : LoadRelocInput σ bits) :
    ∀ t, t < bits.length →
      (loadRelocProg.eval σ) (bits.length + (bits.length + loadRelocControlGap) + t) =
        σ (1 + t) := by
  intro t ht
  have h0 := hin.1
  have hInv := load_reloc_loop_invariant σ bits.length h0 bits.length le_rfl
  rw [loadRelocProg_eval_eq_loop σ bits.length h0]
  exact hInv.2.2.2.2.2.1 t ht

lemma loadRelocProg_final_state (σ : Store) (bits : Bits)
    (hin : LoadRelocInput σ bits) :
    (loadRelocProg.eval σ) 0 = bits.length ∧
    (loadRelocProg.eval σ) (bits.length + loadRelocSrcJ) =
      bits.length + 1 ∧
    (loadRelocProg.eval σ) (bits.length + loadRelocDstJ) =
      bits.length + (bits.length + loadRelocControlGap) + bits.length ∧
    (loadRelocProg.eval σ) (bits.length + loadRelocLenJ) =
      bits.length ∧
    (loadRelocProg.eval σ) (bits.length + loadRelocBaseJ) =
      bits.length + (bits.length + loadRelocControlGap) := by
  have hInv := load_reloc_loop_invariant σ bits.length hin.1 bits.length le_rfl
  rw [loadRelocProg_eval_eq_loop σ bits.length hin.1]
  exact ⟨hInv.1, by simpa [Nat.add_comm] using hInv.2.1,
    hInv.2.2.1, hInv.2.2.2.1, hInv.2.2.2.2.1⟩

lemma loadRelocProg_output_bits (σ : Store) (bits : Bits)
    (hin : LoadRelocInput σ bits) :
    BitsFrom (loadRelocProg.eval σ) (bits.length + (bits.length + loadRelocControlGap)) bits := by
  intro i hi
  rw [loadRelocProg_output σ bits hin i hi]
  exact hin.2 i hi

lemma loadRelocProg_frame_two_sided (σ : Store) (bits : Bits)
    (hin : LoadRelocInput σ bits) :
    ∀ r, r < bits.length + 1 ∨
      bits.length + (bits.length + loadRelocControlGap) + bits.length ≤ r →
      (loadRelocProg.eval σ) r = σ r := by
  intro r hr
  rw [loadRelocProg_eval_eq_loop σ bits.length hin.1]
  exact load_reloc_loop_frame σ bits.length hin.1 bits.length le_rfl r hr

lemma loadRelocProg_correct (σ : Store) (bits : Bits)
    (hin : LoadRelocInput σ bits) :
    LoadRelocPost (loadRelocProg.eval σ) bits := by
  have hs := loadRelocProg_final_state σ bits hin
  have haddr : bits.length + (bits.length + loadRelocControlGap) =
      2 * bits.length + loadRelocControlGap := by omega
  refine ⟨hs.1, ?_, hs.2.1, ?_, hs.2.2.2.1, ?_⟩
  · rw [← haddr]; exact loadRelocProg_output_bits σ bits hin
  · rw [← haddr]; exact hs.2.2.1
  · rw [← haddr]; exact hs.2.2.2.2

/-! ## A lower bound on the encoded length

This module proves a lower bound on the length of an encoded 3CNF. It follows from the unary
headers and the minimum length of each encoded clause. -/

open NPComplete.SAT (ThreeCNF ThreeClause Literal encodeLiteral encodeThreeCNF encodeThreeClause)
open NPComplete.BitEncoding (encodeNat_length encodeList)

/-- Every `encodeThreeClause` output has length exactly `6` more than the sum of its three
    literals' variable indices — in particular, at least `6`. -/
lemma encodeThreeClause_length_ge6 (c : ThreeClause) : 6 ≤ (encodeThreeClause c).length := by
  unfold encodeThreeClause encodeLiteral
  cases c.l1 <;> cases c.l2 <;> cases c.l3 <;>
    simp [encodeNat_length] <;> omega

/-- `encodeThreeCNF`'s length is at least `numVars + 7 * clauses.length + 2`, with no
    `ValidThreeCNF` hypothesis: the unary headers contribute `numVars + clauses.length + 2` bits,
    and each clause contributes at least six more. -/
lemma encodeThreeCNF_length_ge (f : ThreeCNF) :
    f.numVars + 7 * f.clauses.length + 2 ≤ (encodeThreeCNF f).length := by
  unfold encodeThreeCNF encodeList
  simp only [List.length_append]
  have h1 := encodeNat_length f.numVars
  have h2 := encodeNat_length f.clauses.length
  have h3 : f.clauses.length * 6 ≤ (f.clauses.map encodeThreeClause).flatten.length := by
    simpa using (List.length_nsmul_le_sum
      ((f.clauses.map encodeThreeClause).map List.length) 6 (by
        intro l hl
        obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hl
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hxs
        exact encodeThreeClause_length_ge6 c))
  omega

end NPComplete.RAMToTM

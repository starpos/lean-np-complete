module

public import NPComplete.CookLevin.UniformPackaging.Reverse
public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded

/-!
# Split-tail emission windows

The split-tail emitter reads a suffix while staging clauses and must stay within
its input and writer limits. This module defines the window and terminal
conditions, then proves how those bounds shift across intermediate states and
clause emissions.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

/-! Certificate that every cell from `n` upward is zero.  The producer builds the
    input on the zero-default store, so the input tail above the window end keeps
    this property through every emit phase; decoders that over-run a short clause
    then read polarity bits that are still Boolean. -/

def CellsZeroFrom (n : ℕ) (σ : Store) : Prop := ∀ i, n ≤ i → σ i = 0

def SplitTailEmitWindow (inputEnd baseLimit base : ℕ)
    (ls : List NPComplete.SAT.Literal)
    (tail : Bits) (addr : ℕ) : Prop :=
  addr + (splitTailInputBits ls tail).length ≤ inputEnd ∧ base + ls.length ≤ baseLimit

lemma splitTailInputBits_cons_length (l : NPComplete.SAT.Literal)
    (ls : List NPComplete.SAT.Literal) (tail : Bits) :
    (splitTailInputBits (l :: ls) tail).length = l.var + 2 +
      (splitTailInputBits ls tail).length := by
  simp [splitTailInputBits, encodeLiteral_length_eq, List.length_append]

lemma SplitTailEmitWindow.intermediate
    (inputEnd baseLimit base : ℕ) (l1 l2 l3 : NPComplete.SAT.Literal)
    (rest : List NPComplete.SAT.Literal)
    (tail : Bits) (addr : ℕ)
    (h : SplitTailEmitWindow inputEnd baseLimit base (l1 :: l2 :: l3 :: rest) tail addr) :
    SplitTailEmitWindow inputEnd baseLimit (base + 1) (l2 :: l3 :: rest) tail
      (addr + l1.var + 2) := by
  rcases h with ⟨hend, hbase⟩
  constructor
  · calc
      (addr + l1.var + 2) + (splitTailInputBits (l2 :: l3 :: rest) tail).length =
          addr + (splitTailInputBits (l1 :: l2 :: l3 :: rest) tail).length := by
        simp [splitTailInputBits, encodeLiteral_length_eq, List.length_append,
          Nat.add_assoc]
      _ ≤ inputEnd := hend
  · simp only [List.length_cons] at hbase ⊢
    omega

lemma SplitTailEmitWindow.long_setup
    (inputEnd baseLimit base : ℕ) (l1 l2 : NPComplete.SAT.Literal)
    (lsTail : List NPComplete.SAT.Literal) (tail : Bits) (addr : ℕ)
    (h : SplitTailEmitWindow inputEnd baseLimit base (l1 :: l2 :: lsTail) tail addr) :
    SplitTailEmitWindow inputEnd baseLimit (base + 1) lsTail tail
      (addr + l1.var + 2 + l2.var + 2) := by
  rcases h with ⟨hend, hbase⟩
  constructor
  · simp [splitTailInputBits, encodeLiteral_length_eq, List.length_append] at hend ⊢
    omega
  · simp only [List.length_cons] at hbase ⊢
    omega

lemma splitTailEmitWindow_shift_after_clause
    (inputEnd baseLimit base : ℕ) (c : Clause) (tail : Bits) (addr : ℕ)
    (haddr : addr + (encodeList encodeLiteral c.lits).length + tail.length ≤ inputEnd)
    (hbase : base + c.lits.length ≤ baseLimit) :
    SplitTailEmitWindow inputEnd baseLimit base c.lits tail
      (addr + c.lits.length + 1) := by
  refine ⟨?_, hbase⟩
  simp only [splitTailInputBits, NPComplete.BitEncoding.encodeList,
    List.length_append, encodeNat_length] at haddr ⊢
  omega

def writerAppendRawStepBound (K : ℕ) : ℕ :=
  3 * K + 3

def writerAppendRawThreeBound (K : ℕ) : ℕ :=
  writerAppendRawStepBound (writerAppendRawStepBound (writerAppendRawStepBound K))

def writerAppendRawSixBound (K : ℕ) : ℕ :=
  writerAppendRawThreeBound (writerAppendRawThreeBound K)

def uniformEmitTightEnvelope (N : ℕ) : ℕ :=
  uniformMNat N + uctCurJ + N + 25

/-! The tight envelope bounds every store value along the outer clause loop, but
    the split-tail decoder's coarse operand budget `cursor + 2 + 2 * bound`
    can overshoot it for some `N` (`uniform_split_tail_cursor_budget_not_tight`). The inner loop
    therefore runs one level up: a value envelope with two extra `N` of slack,
    which is still below the syntax envelope. -/
def uniformEmitLongValueEnvelope (N : ℕ) : ℕ :=
  uniformEmitTightEnvelope N + 2 * N

/-! The syntax envelope must absorb the split-tail step's raw writer chain,
    whose composition triples the operand budget per emitted literal
    (`writerAppendRawThreeBound`).  Sizing it from the long value envelope keeps
    the two-envelope discipline: tight for outer-loop values, syntax for all
    register indices and indirect operands of one emit step. -/
def uniformEmitSyntaxEnvelope (N : ℕ) : ℕ :=
  writerAppendRawThreeBound (uniformEmitLongValueEnvelope N) + 1

lemma uniform_split_tail_input_end_le_tight (N : ℕ) :
    uniformAddrNat N + N ≤ uniformEmitTightEnvelope N := by
  simp [uniformAddrNat, uniformMNat, uniformAddrOffset, uniformEmitTightEnvelope,
    uniformStartNat, uniformSlackNat, uctCurJ, relocateControlGap]
  omega

lemma uniformEmitTightEnvelope_le_long_value_envelope (N : ℕ) :
    uniformEmitTightEnvelope N ≤ uniformEmitLongValueEnvelope N := by
  simp only [uniformEmitLongValueEnvelope]
  omega

lemma uniformEmitLongValueEnvelope_le_syntax_envelope (N : ℕ) :
    uniformEmitLongValueEnvelope N ≤ uniformEmitSyntaxEnvelope N := by
  simp only [uniformEmitSyntaxEnvelope, writerAppendRawThreeBound,
    writerAppendRawStepBound]
  omega

lemma uniform_split_tail_cursor_budget_le_long_value_envelope (N : ℕ) :
    uniformAddrNat N + N + 2 + 2 * N ≤ uniformEmitLongValueEnvelope N := by
  simp only [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformAddrNat,
    uniformMNat, uniformAddrOffset, uniformStartNat, uniformSlackNat, uctCurJ]
  omega

lemma uniform_split_tail_cursor_budget_not_tight :
    ∃ N, uniformEmitTightEnvelope N < uniformAddrNat N + N + 2 + 2 * N := by
  refine ⟨100, ?_⟩
  norm_num [uniformEmitTightEnvelope, uniformAddrNat, uniformMNat, uniformAddrOffset,
    uniformStartNat, uniformSlackNat, uctCurJ, relocateControlGap]

lemma uniform_producer_input_end_window (φ : CNF) :
    uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1 +
        (φ.clauses.map encodeClause).flatten.length ≤
      uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
  have hsplit := encodeCNF_split φ
  have hlen := congrArg List.length hsplit
  simp [encodeNat_length, List.length_append] at hlen
  have hflat : (φ.clauses.map encodeClause).flatten.length =
      (φ.clauses.map (List.length ∘ encodeClause)).sum := by
    simp [List.length_flatten]
  rw [hflat]
  omega

lemma uniformEmitTightEnvelope_le_syntax_envelope (N : ℕ) :
    uniformEmitTightEnvelope N ≤ uniformEmitSyntaxEnvelope N := by
  exact (uniformEmitTightEnvelope_le_long_value_envelope N).trans
    (uniformEmitLongValueEnvelope_le_syntax_envelope N)

end NPComplete.CookLevin

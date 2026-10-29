module

public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatDecodePhase

/-!
# Decode phase on a one-clause input

The header and clause decoders are proved correct separately. This module assembles them with a
setup program into one decode program and connects the stages end to end, for an input that
holds a single clause whose variables are below the declared variable count. It checks that the
stage statements fit together. No main construction uses the composition, so it stays outside the
consumer-facing umbrella.
-/

@[expose] public section
namespace NPComplete.RAMToTM

open NPComplete.SAT
open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding

def decodeCursorReg : ℕ := 1
def decodeNumVarsReg : ℕ := 2
def decodeCountReg : ℕ := 3
def decodeDoneReg : ℕ := 4
def decodePolReg : ℕ := 5
def decodeVarReg : ℕ := 6
def decodeBaseReg : ℕ := 7

def decodeAddrExpr : Expr := .add (.reg 0) (.const relocateControlGap)
def decodeBaseExpr : Expr := .add decodeAddrExpr (.reg 0)

def decodeSetup : Program :=
  .seq (.assign decodeCursorReg decodeAddrExpr)
  <| .seq (.assign decodeNumVarsReg (.const 0))
  <| .seq (.assign decodeCountReg (.const 0))
  <| .seq (.assign decodeDoneReg (.const 0))
  <| .seq (.assign decodePolReg (.const 0))
  <| .seq (.assign decodeVarReg (.const 0))
      (.assign decodeBaseReg decodeBaseExpr)

def decodeProg : Program :=
  .seq decodeSetup
    <| .seq
      (decodeThreeCNFHeaderProgAt decodeCursorReg decodeNumVarsReg decodeCountReg decodeDoneReg
        (.reg 0) (.reg 0))
      (decodeThreeClauseProgAt decodeCursorReg decodePolReg decodeVarReg decodeDoneReg
        (.reg decodeBaseReg) decodeBaseReg)

def DecodeOneClausePromise (n : ℕ) (c : ThreeClause) : Prop :=
  c.l1.var < n ∧ c.l2.var < n ∧ c.l3.var < n

def DecodePost (σ : Store) (N C n : ℕ) (c : ThreeClause) : Prop :=
  σ 0 = N ∧
  σ decodeNumVarsReg = n ∧
  σ decodeCountReg = 1 ∧
  σ decodeCursorReg = C + N ∧
  σ decodeBaseReg = C + N ∧
  ThreeClauseAt σ (C + N) 0 c

lemma decodeSetup_eval (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    decodeSetup.eval σ decodeCursorReg = N + relocateControlGap ∧
    decodeSetup.eval σ decodeBaseReg = N + relocateControlGap + N ∧
    decodeSetup.eval σ 0 = N := by
  simp [decodeSetup, decodeAddrExpr, decodeBaseExpr, eval_seq, eval_assign, Expr.eval,
    writeReg, decodeCursorReg, decodeNumVarsReg, decodeCountReg, decodeDoneReg,
    decodePolReg, decodeVarReg, decodeBaseReg, h0, relocateControlGap]

lemma decodeSetup_high_frame (σ : Store) (r : ℕ)
    (hr : 8 ≤ r) : decodeSetup.eval σ r = σ r := by
  exact (by decide +kernel : decodeSetup.Avoids (8 ≤ ·)).eval_frame σ hr

/-- Address-only fact used by `decodeProg_correct`: every register at or below
`decodeBaseReg` is disjoint from a clause's literal cells once the base exceeds
`decodeBaseReg`. This separation from `decodeProg_correct`'s program-level context
keeps the address arithmetic local to this lemma. -/
lemma decodeBaseReg_literalCells_ne (base r : ℕ) (hr : r ≤ decodeBaseReg)
    (hbase : decodeBaseReg < base) (j : ℕ) (hj : j < 3) :
    r ≠ literalPolCell base 0 j ∧ r ≠ literalVarCell base 0 j := by
  rw [literalPolCell_eq', literalVarCell_eq']
  omega

/-- Setup stage of `decodeProg_correct`: the setup program points the cursor and base
registers into the relocated input and leaves that input readable. -/
lemma decodeProg_correct_setup (σ : Store) (n : ℕ) (c : ThreeClause) (N : ℕ)
    (hN : N = (encodeThreeCNF ⟨n, [c]⟩).length)
    (hrel : RelocatePost σ (encodeThreeCNF ⟨n, [c]⟩)) :
    decodeSetup.eval σ 0 = N ∧
    decodeSetup.eval σ decodeCursorReg = N + relocateControlGap ∧
    decodeSetup.eval σ decodeBaseReg = N + relocateControlGap + N ∧
    BitsFrom (decodeSetup.eval σ) (N + relocateControlGap)
      (encodeNat n ++ encodeNat 1 ++ encodeThreeClause c) := by
  have h0 : σ 0 = N := by rw [hN]; exact hrel.1
  have hsetup := decodeSetup_eval σ N h0
  refine ⟨hsetup.2.2, hsetup.1, hsetup.2.1, ?_⟩
  have hbits : BitsFrom σ (N + relocateControlGap)
      (encodeNat n ++ encodeNat 1 ++ encodeThreeClause c) := by
    have h := hrel.2.1
    rw [← hN] at h
    simpa [encodeThreeCNF, encodeList] using h
  apply bitsFrom_of_eq_on (hb := hbits)
  intro k hk
  have hk8 : 8 ≤ N + relocateControlGap + k := by simp [relocateControlGap]; omega
  exact decodeSetup_high_frame σ (N + relocateControlGap + k) hk8

/-- Header stage of `decodeProg_correct`: decoding the two unary header fields records
`n` and the clause count and advances the cursor to the clause bits. -/
lemma decodeProg_correct_header (σ0 : Store) (n : ℕ) (c : ThreeClause) (N : ℕ)
    (hN : N = (encodeThreeCNF ⟨n, [c]⟩).length)
    (hσ00 : σ0 0 = N) (hσ0c : σ0 decodeCursorReg = N + relocateControlGap)
    (hσ0b : σ0 decodeBaseReg = N + relocateControlGap + N)
    (hfull : BitsFrom σ0 (N + relocateControlGap)
      (encodeNat n ++ encodeNat 1 ++ encodeThreeClause c)) :
    ∃ σ1, σ1 = (decodeThreeCNFHeaderProgAt decodeCursorReg decodeNumVarsReg decodeCountReg
        decodeDoneReg (.reg 0) (.reg 0)).eval σ0 ∧
      σ1 decodeNumVarsReg = n ∧ σ1 decodeCountReg = 1 ∧
      σ1 decodeCursorReg = N + relocateControlGap + n + 1 + 1 + 1 ∧
      σ1 0 = N ∧ σ1 decodeBaseReg = N + relocateControlGap + N ∧
      BitsFrom σ1 (N + relocateControlGap + n + 1 + 1 + 1) (encodeThreeClause c) := by
  have hstable : BoundExprStable (.reg 0) 0 N σ0 := by
    intro τ ht
    simpa [Expr.eval] using ht.trans hσ00
  have hnum : n + 1 ≤ N := by
    have := encodeThreeCNF_numVars_succ_le (⟨n, [c]⟩ : ThreeCNF)
    rw [hN]; simpa using this
  have hcount : 1 + 1 ≤ N := by
    have := encodeThreeCNF_clauseCount_succ_le (⟨n, [c]⟩ : ThreeCNF)
    rw [hN]; simpa using this
  have hprefix : BitsFrom σ0 (N + relocateControlGap) (encodeNat n ++ encodeNat 1) :=
    (bitsFrom_append σ0 _ (encodeNat n ++ encodeNat 1) (encodeThreeClause c) hfull).1
  have hhead := decodeThreeCNFHeaderProgAt_correct decodeCursorReg decodeNumVarsReg
    decodeCountReg decodeDoneReg N N (N + relocateControlGap) n 1 σ0 (.reg 0) (.reg 0)
    (by norm_num [decodeCursorReg, decodeNumVarsReg]) (by norm_num [decodeCursorReg, decodeCountReg])
    (by norm_num [decodeCursorReg, decodeDoneReg]) (by norm_num [decodeNumVarsReg, decodeCountReg])
    (by norm_num [decodeNumVarsReg, decodeDoneReg]) (by norm_num [decodeCountReg, decodeDoneReg])
    (by norm_num [decodeCursorReg]) (by norm_num [decodeNumVarsReg])
    (by norm_num [decodeCountReg]) (by norm_num [decodeDoneReg])
    (by simp only [decodeCursorReg, relocateControlGap]; omega)
    (by simp only [decodeNumVarsReg, relocateControlGap]; omega)
    (by simp only [decodeCountReg, relocateControlGap]; omega)
    (by simp only [decodeDoneReg, relocateControlGap]; omega)
    hstable hstable hnum hcount hσ0c hprefix
  have hframe : ∀ r, r ≠ decodeCursorReg → r ≠ decodeNumVarsReg → r ≠ decodeCountReg →
      r ≠ decodeDoneReg → (decodeThreeCNFHeaderProgAt decodeCursorReg decodeNumVarsReg
        decodeCountReg decodeDoneReg (.reg 0) (.reg 0)).eval σ0 r = σ0 r :=
    fun r h1 h2 h3 h4 => decodeThreeCNFHeaderProgAt_frame decodeCursorReg decodeNumVarsReg
      decodeCountReg decodeDoneReg (.reg 0) (.reg 0) r σ0 h1 h2 h3 h4
  have hclause : BitsFrom σ0 (N + relocateControlGap + n + 1 + 1 + 1) (encodeThreeClause c) := by
    have h := (bitsFrom_append σ0 _ (encodeNat n ++ encodeNat 1)
      (encodeThreeClause c) hfull).2
    convert h using 1
    all_goals simp [encodeNat_length]
    all_goals omega
  refine ⟨_, rfl, hhead.1, hhead.2.1, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhead.2.2
  · exact (hframe 0 (by norm_num [decodeCursorReg]) (by norm_num [decodeNumVarsReg])
      (by norm_num [decodeCountReg]) (by norm_num [decodeDoneReg])).trans hσ00
  · exact (hframe decodeBaseReg (by norm_num [decodeBaseReg, decodeCursorReg])
      (by norm_num [decodeBaseReg, decodeNumVarsReg])
      (by norm_num [decodeBaseReg, decodeCountReg])
      (by norm_num [decodeBaseReg, decodeDoneReg])).trans hσ0b
  · apply bitsFrom_of_eq_on (hb := hclause)
    intro k hk
    exact hframe _ (by simp only [decodeCursorReg, relocateControlGap]; omega)
      (by simp only [decodeNumVarsReg, relocateControlGap]; omega)
      (by simp only [decodeCountReg, relocateControlGap]; omega)
      (by simp only [decodeDoneReg, relocateControlGap]; omega)

/-- Clause stage of `decodeProg_correct`: the clause decoder reconstructs `c` at the base
address and leaves the cursor at the end of the input. -/
lemma decodeProg_correct_clause_post (σ1 : Store) (n : ℕ) (c : ThreeClause) (N : ℕ)
    (hp : DecodeOneClausePromise n c)
    (hN : N = (encodeThreeCNF ⟨n, [c]⟩).length)
    (hσ1c : σ1 decodeCursorReg = N + relocateControlGap + n + 1 + 1 + 1)
    (hσ1b : σ1 decodeBaseReg = N + relocateControlGap + N)
    (hclause : BitsFrom σ1 (N + relocateControlGap + n + 1 + 1 + 1) (encodeThreeClause c)) :
    ThreeClauseAt
      ((decodeThreeClauseProgAt decodeCursorReg decodePolReg decodeVarReg decodeDoneReg
        (.reg decodeBaseReg) decodeBaseReg).eval σ1) (N + relocateControlGap + N) 0 c ∧
    (decodeThreeClauseProgAt decodeCursorReg decodePolReg decodeVarReg decodeDoneReg
        (.reg decodeBaseReg) decodeBaseReg).eval σ1 decodeCursorReg =
      N + relocateControlGap + N := by
  have hstableBase : BoundExprStable (.reg decodeBaseReg) decodeBaseReg
      (N + relocateControlGap + N) σ1 := by
    intro τ ht
    simpa [Expr.eval] using ht.trans hσ1b
  have hNshape : N = n + 1 + 2 + (encodeThreeClause c).length := by
    rw [hN]
    simp [encodeThreeCNF, encodeList, encodeNat_length]
    omega
  have hbase : decodeBaseReg < σ1 decodeBaseReg := by
    rw [hσ1b]
    simp only [decodeBaseReg, relocateControlGap]
    omega
  have hvars : c.l1.var + 1 ≤ N + relocateControlGap + N ∧
      c.l2.var + 1 ≤ N + relocateControlGap + N ∧ c.l3.var + 1 ≤ N + relocateControlGap + N := by
    have h1 := hp.1
    have h2 := hp.2.1
    have h3 := hp.2.2
    omega
  have hsep : N + relocateControlGap + n + 1 + 1 + 1 + (encodeThreeClause c).length ≤
      σ1 decodeBaseReg := by
    rw [hσ1b]
    omega
  obtain ⟨hpostAt, hcur⟩ := decodeThreeClauseProgAt_correct decodeCursorReg decodePolReg decodeVarReg
    decodeDoneReg (N + relocateControlGap + N) decodeBaseReg (N + relocateControlGap + n + 1 + 1 + 1)
    (.reg decodeBaseReg) c σ1
    hbase hstableBase (by norm_num [decodeBaseReg, decodeCursorReg])
    (by norm_num [decodeBaseReg, decodePolReg]) (by norm_num [decodeBaseReg, decodeVarReg])
    (by norm_num [decodeBaseReg, decodeDoneReg])
    (by norm_num [decodeCursorReg, decodePolReg]) (by norm_num [decodeCursorReg, decodeVarReg])
    (by norm_num [decodeCursorReg, decodeDoneReg])
    (by norm_num [decodePolReg, decodeVarReg]) (by norm_num [decodePolReg, decodeDoneReg])
    (by norm_num [decodeVarReg, decodeDoneReg])
    (by simp only [decodeCursorReg, relocateControlGap]; omega)
    (by simp only [decodePolReg, relocateControlGap]; omega)
    (by simp only [decodeVarReg, relocateControlGap]; omega)
    (by simp only [decodeDoneReg, relocateControlGap]; omega)
    (by rw [hσ1b]; simp only [decodeCursorReg, relocateControlGap]; omega)
    (by rw [hσ1b]; simp only [decodePolReg, relocateControlGap]; omega)
    (by rw [hσ1b]; simp only [decodeVarReg, relocateControlGap]; omega)
    (by rw [hσ1b]; simp only [decodeDoneReg, relocateControlGap]; omega) hsep
    hvars.1 hvars.2.1 hvars.2.2 hσ1c hclause
  refine ⟨by simpa [hσ1b] using hpostAt, ?_⟩
  omega

/-- The clause decoder leaves every low register other than its own working registers
untouched. -/
lemma decodeProg_correct_clause_frame (σ1 : Store) (r N : ℕ)
    (hσ1b : σ1 decodeBaseReg = N + relocateControlGap + N)
    (hr : r ≤ decodeBaseReg) (hrc : r ≠ decodeCursorReg) (hrp : r ≠ decodePolReg)
    (hrv : r ≠ decodeVarReg) (hrd : r ≠ decodeDoneReg) :
    (decodeThreeClauseProgAt decodeCursorReg decodePolReg decodeVarReg decodeDoneReg
      (.reg decodeBaseReg) decodeBaseReg).eval σ1 r = σ1 r := by
  have hstableBase : BoundExprStable (.reg decodeBaseReg) decodeBaseReg
      (N + relocateControlGap + N) σ1 := by
    intro τ ht
    simpa [Expr.eval] using ht.trans hσ1b
  have hbase : decodeBaseReg < σ1 decodeBaseReg := by
    rw [hσ1b]
    simp only [decodeBaseReg, relocateControlGap]
    omega
  exact decodeThreeClauseProgAt_frame decodeCursorReg decodePolReg decodeVarReg
    decodeDoneReg (N + relocateControlGap + N) decodeBaseReg r (.reg decodeBaseReg) σ1
    hbase hstableBase
    (by norm_num [decodeBaseReg, decodeCursorReg]) (by norm_num [decodeBaseReg, decodePolReg])
    (by norm_num [decodeBaseReg, decodeVarReg]) (by norm_num [decodeBaseReg, decodeDoneReg])
    hrc hrp hrv hrd
    (fun j hj => decodeBaseReg_literalCells_ne (σ1 decodeBaseReg) r hr hbase j hj)

lemma decodeProg_correct (σ : Store) (n : ℕ) (c : ThreeClause)
    (hp : DecodeOneClausePromise n c)
    (hrel : RelocatePost σ (encodeThreeCNF ⟨n, [c]⟩)) :
    DecodePost (decodeProg.eval σ) (encodeThreeCNF ⟨n, [c]⟩).length
      ((encodeThreeCNF ⟨n, [c]⟩).length + relocateControlGap) n c := by
  obtain ⟨N, hN⟩ : ∃ N, N = (encodeThreeCNF ⟨n, [c]⟩).length := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨hs0, hsc, hsb, hsbits⟩ := decodeProg_correct_setup σ n c N hN hrel
  obtain ⟨σ1, hσ1, hn, hk, hc1, h01, hb1, hcl⟩ :=
    decodeProg_correct_header (decodeSetup.eval σ) n c N hN hs0 hsc hsb hsbits
  have hpost := decodeProg_correct_clause_post σ1 n c N hp hN hc1 hb1 hcl
  have hfr : ∀ r, r ≤ decodeBaseReg → r ≠ decodeCursorReg → r ≠ decodePolReg →
      r ≠ decodeVarReg → r ≠ decodeDoneReg →
      (decodeThreeClauseProgAt decodeCursorReg decodePolReg decodeVarReg decodeDoneReg
        (.reg decodeBaseReg) decodeBaseReg).eval σ1 r = σ1 r :=
    fun r => decodeProg_correct_clause_frame σ1 r N hb1
  have hphase : decodeProg.eval σ = (decodeThreeClauseProgAt decodeCursorReg decodePolReg
      decodeVarReg decodeDoneReg (.reg decodeBaseReg) decodeBaseReg).eval σ1 := by
    simp only [decodeProg, eval_seq]
    rw [hσ1]
  rw [hphase]
  refine ⟨?_, ?_, ?_, hpost.2, ?_, hpost.1⟩
  · exact (hfr 0 (by norm_num [decodeBaseReg]) (by norm_num [decodeCursorReg])
      (by norm_num [decodePolReg]) (by norm_num [decodeVarReg])
      (by norm_num [decodeDoneReg])).trans h01
  · exact (hfr decodeNumVarsReg (by norm_num [decodeNumVarsReg, decodeBaseReg])
      (by norm_num [decodeNumVarsReg, decodeCursorReg]) (by norm_num [decodeNumVarsReg, decodePolReg])
      (by norm_num [decodeNumVarsReg, decodeVarReg])
      (by norm_num [decodeNumVarsReg, decodeDoneReg])).trans hn
  · exact (hfr decodeCountReg (by norm_num [decodeCountReg, decodeBaseReg])
      (by norm_num [decodeCountReg, decodeCursorReg]) (by norm_num [decodeCountReg, decodePolReg])
      (by norm_num [decodeCountReg, decodeVarReg])
      (by norm_num [decodeCountReg, decodeDoneReg])).trans hk
  · exact (hfr decodeBaseReg le_rfl (by norm_num [decodeBaseReg, decodeCursorReg])
      (by norm_num [decodeBaseReg, decodePolReg]) (by norm_num [decodeBaseReg, decodeVarReg])
      (by norm_num [decodeBaseReg, decodeDoneReg])).trans hb1

end NPComplete.RAMToTM

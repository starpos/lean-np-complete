module

public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Relocate
public import NPComplete.RAMToTM.ThreeSat.Problem.ReductionMemoryLayout
public import NPComplete.SAT.ThreeCNFEncoding
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatRuntimeCore
public import NPComplete.BoundedWhile.Frame


/-!
# Three-CNF decode phase

The runtime reads an encoded header and fixed-shape clause fields from a
relocated input region. This module defines the header and literal decoder
phases and proves their correctness. Its frame lemmas preserve the encoded input
and cells outside the work registers and clause arena.
-/

@[expose] public section
namespace NPComplete.RAMToTM

open NPComplete.SAT
open NPComplete.BoundedWhile (Program Store Expr eval_seq eval_assign
  eval_assignInd eval_forN loopEval loopEval_succ loopEval_zero writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding

lemma encodeThreeCNF_numVars_succ_le (f : ThreeCNF) :
    f.numVars + 1 ≤ (encodeThreeCNF f).length := by
  unfold encodeThreeCNF
  simp only [List.length_append]
  have h := encodeNat_length f.numVars
  omega

lemma encodeThreeCNF_clauseCount_succ_le (f : ThreeCNF) :
    f.clauses.length + 1 ≤ (encodeThreeCNF f).length := by
  unfold encodeThreeCNF
  simp only [List.length_append]
  have h1 := encodeNat_length f.numVars
  have h2 := encodeList_length_ge encodeThreeClause f.clauses
  omega

def decodeThreeCNFHeaderProgAt
    (cursorReg numVarsReg countReg doneReg : ℕ) (boundE1 boundE2 : Expr) : Program :=
  .seq (.assign numVarsReg (.const 0))
  <| .seq (.assign doneReg (.const 0))
  <| .seq (decodeUnaryProgAt cursorReg numVarsReg doneReg boundE1)
  <| .seq (.assign countReg (.const 0))
  <| .seq (.assign doneReg (.const 0))
      (decodeUnaryProgAt cursorReg countReg doneReg boundE2)

def BoundExprStable (boundE : Expr) (stableReg bound : ℕ) (σ : Store) : Prop :=
  ∀ τ, τ stableReg = σ stableReg → boundE.eval τ = bound

lemma decodeThreeCNFHeaderProgAt_correct
    (cursorReg numVarsReg countReg doneReg bound1 bound2 addr numVars count : ℕ) (σ : Store)
    (boundE1 boundE2 : Expr)
    (hcn : cursorReg ≠ numVarsReg) (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hnc : numVarsReg ≠ countReg) (hnd : numVarsReg ≠ doneReg) (hcd' : countReg ≠ doneReg)
    (h0c : 0 ≠ cursorReg) (h0n : 0 ≠ numVarsReg) (h0k : 0 ≠ countReg)
    (h0d : 0 ≠ doneReg)
    (hca : cursorReg < addr) (hna : numVarsReg < addr) (hcta : countReg < addr)
    (hda : doneReg < addr) (hstable1 : BoundExprStable boundE1 0 bound1 σ)
    (hstable2 : BoundExprStable boundE2 0 bound2 σ)
    (hb1 : numVars + 1 ≤ bound1)
    (hb2 : count + 1 ≤ bound2) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeNat numVars ++ encodeNat count)) :
    (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg boundE1 boundE2).eval σ
        numVarsReg = numVars ∧
    (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg boundE1 boundE2).eval σ
        countReg = count ∧
    (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg boundE1 boundE2).eval σ
        cursorReg = addr + numVars + 1 + count + 1 := by
  unfold decodeThreeCNFHeaderProgAt
  simp only [eval_seq, eval_assign, Expr.eval]
  set σ0 := writeReg σ numVarsReg 0 with hσ0def
  set σ0' := writeReg σ0 doneReg 0 with hσ0'def
  have hσ0'c : σ0' cursorReg = addr := by
    rw [hσ0'def, writeReg_diff _ doneReg _ cursorReg hcd,
      hσ0def, writeReg_diff _ numVarsReg _ cursorReg hcn, hc]
  have hσ0'n : σ0' numVarsReg = 0 := by
    rw [hσ0'def, writeReg_diff _ doneReg _ numVarsReg hnd,
      hσ0def, writeReg_same]
  have hσ0'd : σ0' doneReg = 0 := by rw [hσ0'def, writeReg_same]
  have hσ0'bits : BitsFrom σ0' addr (encodeNat numVars) := by
    apply bitsFrom_of_eq_on (hb := (bitsFrom_append σ addr (encodeNat numVars)
      (encodeNat count) hbits).1)
    intro k hk
    rw [hσ0'def, writeReg_diff _ doneReg _ (addr + k) (by omega),
      hσ0def, writeReg_diff _ numVarsReg _ (addr + k) (by omega)]
  have hbE1' : boundE1.eval σ0' = bound1 := hstable1 σ0' (by
    rw [hσ0'def, writeReg_diff _ doneReg _ 0 h0d,
      hσ0def, writeReg_diff _ numVarsReg _ 0 h0n])
  set σ1 := (decodeUnaryProgAt cursorReg numVarsReg doneReg boundE1).eval σ0'
    with hσ1def
  obtain ⟨hfc, hfk, hfd, hfr⟩ := decodeUnaryProgAt_correct cursorReg numVarsReg doneReg
    hcn hcd hnd numVars bound1 addr 0 σ0' boundE1 hbE1' hb1 hca hna hda
    hσ0'c hσ0'n hσ0'd hσ0'bits
  rw [← hσ1def] at hfc hfk hfd hfr
  simp only [Nat.zero_add] at hfk
  set σ2 := writeReg σ1 countReg 0 with hσ2def
  have hσ2c : σ2 cursorReg = σ1 cursorReg :=
    writeReg_diff _ countReg _ cursorReg hcc
  have hσ2n : σ2 numVarsReg = σ1 numVarsReg :=
    writeReg_diff _ countReg _ numVarsReg hnc
  have hσ2cnt : σ2 countReg = 0 := writeReg_same _ _ _
  set σ3 := writeReg σ2 doneReg 0 with hσ3def
  have hσ3c : σ3 cursorReg = addr + numVars + 1 := by
    rw [hσ3def, writeReg_diff _ doneReg _ cursorReg hcd, hσ2c, hfc]
  have hσ3n : σ3 numVarsReg = numVars := by
    rw [hσ3def, writeReg_diff _ doneReg _ numVarsReg hnd, hσ2n, hfk]
  have hσ3cnt : σ3 countReg = 0 := by
    rw [hσ3def, writeReg_diff _ doneReg _ countReg hcd', hσ2cnt]
  have hσ3d : σ3 doneReg = 0 := by rw [hσ3def, writeReg_same]
  have hprefix := (bitsFrom_append σ addr (encodeNat numVars)
    (encodeNat count) hbits).2
  rw [encodeNat_length] at hprefix
  have hσ3bits : BitsFrom σ3 (addr + numVars + 1) (encodeNat count) := by
    apply bitsFrom_of_eq_on (hb := hprefix)
    intro k hk
    have e1 : σ3 (addr + (numVars + 1) + k) = σ1 (addr + (numVars + 1) + k) := by
      rw [hσ3def, writeReg_diff _ doneReg _ (addr + (numVars + 1) + k) (by omega),
        hσ2def, writeReg_diff _ countReg _ (addr + (numVars + 1) + k) (by omega)]
    have e2 : σ1 (addr + (numVars + 1) + k) = σ0' (addr + (numVars + 1) + k) :=
      hfr _ (by omega) (by omega) (by omega)
    have e3 : σ0' (addr + (numVars + 1) + k) = σ (addr + (numVars + 1) + k) := by
      rw [hσ0'def, writeReg_diff _ doneReg _ (addr + (numVars + 1) + k) (by omega),
        hσ0def, writeReg_diff _ numVarsReg _ (addr + (numVars + 1) + k) (by omega)]
    rw [e1, e2, e3]
  have hσ1zero : σ1 0 = σ0' 0 := hfr 0 h0c h0n h0d
  have hbE2' : boundE2.eval σ3 = bound2 := hstable2 σ3 (by
    rw [hσ3def, writeReg_diff _ doneReg _ 0 (by omega),
      hσ2def, writeReg_diff _ countReg _ 0 (by omega),
      hσ1zero,
      hσ0'def, writeReg_diff _ doneReg _ 0 (by omega),
      hσ0def, writeReg_diff _ numVarsReg _ 0 (by omega)])
  obtain ⟨hgc, hgk, hgd, hgr⟩ := decodeUnaryProgAt_correct cursorReg countReg doneReg
    hcc hcd hcd' count bound2 (addr + numVars + 1) 0 σ3 boundE2 hbE2' hb2
    (by omega) (by omega) (by omega) hσ3c hσ3cnt hσ3d hσ3bits
  simp only [Nat.zero_add] at hgk
  refine ⟨?_, hgk, ?_⟩
  · rw [hgr numVarsReg hcn.symm hnc hnd, hσ3n]
  · rw [hgc]

lemma decodeThreeCNFHeaderProgAt_frame
    (cursorReg numVarsReg countReg doneReg : ℕ) (boundE1 boundE2 : Expr) (r : ℕ)
    (σ : Store) (hrc : r ≠ cursorReg) (hrn : r ≠ numVarsReg)
    (hrk : r ≠ countReg) (hrd : r ≠ doneReg) :
    (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg boundE1 boundE2).eval σ r =
      σ r := by
  have hAvoids : (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg
      boundE1 boundE2).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ numVarsReg ∧ r ≠ countReg ∧ r ≠ doneReg) := by
    simp [Program.Avoids, decodeThreeCNFHeaderProgAt, decodeUnaryProgAt, decodeUnaryStep]
  exact hAvoids.eval_frame σ ⟨hrc, hrn, hrk, hrd⟩

def literalPolCellAtBaseExpr (baseReg j : ℕ) : Expr :=
  .add (.reg baseReg) (.const (2 * j))

def literalVarCellAtBaseExpr (baseReg j : ℕ) : Expr :=
  .add (.reg baseReg) (.const (2 * j + 1))

lemma literalPolCellAtBaseExpr_eval (baseReg j : ℕ) (σ : Store) :
    (literalPolCellAtBaseExpr baseReg j).eval σ = literalPolCell (σ baseReg) 0 j := by
  simp [literalPolCellAtBaseExpr, Expr.eval, literalPolCell_eq']

def decodeLiteralProgAt
    (cursorReg polReg varReg doneReg : ℕ) (boundE : Expr) (baseReg j : ℕ) : Program :=
  .seq (readBitAdvanceProg cursorReg polReg)
  <| .seq (.assign varReg (.const 0))
  <| .seq (.assign doneReg (.const 0))
  <| .seq (decodeUnaryProgAt cursorReg varReg doneReg boundE)
  <| .seq (.assignInd (literalPolCellAtBaseExpr baseReg j) (.reg polReg))
      (.assignInd (literalVarCellAtBaseExpr baseReg j) (.reg varReg))

lemma decodeLiteralProgAt_eq_fixed
    (cursorReg polReg varReg doneReg bound baseReg j : ℕ) (boundE : Expr) (σ : Store)
    (hbase : baseReg < σ baseReg)
    (hbE : BoundExprStable boundE baseReg bound σ)
    (hbc : baseReg ≠ cursorReg) (hbp : baseReg ≠ polReg)
    (hbv : baseReg ≠ varReg) (hbd : baseReg ≠ doneReg) :
    (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg j).eval σ =
      (decodeLiteralProg cursorReg polReg varReg doneReg bound (σ baseReg) 0 j).eval σ := by
  unfold decodeLiteralProgAt decodeLiteralProg
  simp only [eval_seq]
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ
  set σ2 := (Program.assign varReg (.const 0)).eval σ1
  set σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hbase1 : σ1 baseReg = σ baseReg := by
    exact readBitAdvanceProg_frame cursorReg polReg baseReg σ hbc hbp
  have hbase2 : σ2 baseReg = σ1 baseReg := by
    rw [show σ2 = writeReg σ1 varReg 0 by
      rw [show σ2 = (Program.assign varReg (.const 0)).eval σ1 by rfl]
      simp only [eval_assign, Expr.eval]]
    exact writeReg_diff _ varReg _ baseReg hbv
  have hbase3 : σ3 baseReg = σ2 baseReg := by
    rw [show σ3 = writeReg σ2 doneReg 0 by
      rw [show σ3 = (Program.assign doneReg (.const 0)).eval σ2 by rfl]
      simp only [eval_assign, Expr.eval]]
    exact writeReg_diff _ doneReg _ baseReg hbd
  have hbE3 : boundE.eval σ3 = bound := hbE σ3 (by rw [hbase3, hbase2, hbase1])
  have hUnary := decodeUnaryProgAt_eq cursorReg varReg doneReg boundE bound σ3 hbE3
  rw [show (decodeUnaryProgAt cursorReg varReg doneReg boundE).eval σ3 =
      (decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 from hUnary]
  have hbase4 : (decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 baseReg =
      σ3 baseReg := by
    exact decodeUnaryProg_frame cursorReg varReg doneReg bound baseReg σ3 hbc hbv hbd
  simp only [eval_assignInd, Expr.eval]
  rw [literalPolCellAtBaseExpr_eval, hbase4, hbase3, hbase2, hbase1]
  have hbasePol : baseReg ≠ literalPolCell (σ baseReg) 0 j := by
    rw [literalPolCell_eq']
    omega
  have hbaseAfter :
      (writeReg ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3)
        (literalPolCell (σ baseReg) 0 j)
        ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 polReg)) baseReg =
      ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3) baseReg :=
    writeReg_diff _ _ _ baseReg hbasePol
  have haddr :
      literalVarCell
          (writeReg ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3)
            (literalPolCell (σ baseReg) 0 j)
            ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 polReg) baseReg)
          0 j = literalVarCell (σ baseReg) 0 j := by
    rw [hbaseAfter]
    rw [hbase4, hbase3, hbase2, hbase1]
  congr 1

lemma decodeLiteralProgAt_frame
    (cursorReg polReg varReg doneReg bound baseReg j r : ℕ) (boundE : Expr) (σ : Store)
    (hbase : baseReg < σ baseReg) (hstable : BoundExprStable boundE baseReg bound σ)
    (hbc : baseReg ≠ cursorReg) (hbp : baseReg ≠ polReg)
    (hbv : baseReg ≠ varReg) (hbd : baseReg ≠ doneReg)
    (hrc : r ≠ cursorReg) (hrp : r ≠ polReg) (hrv : r ≠ varReg)
    (hrd : r ≠ doneReg) (hrpCell : r ≠ literalPolCell (σ baseReg) 0 j)
    (hrvCell : r ≠ literalVarCell (σ baseReg) 0 j) :
    (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg j).eval σ r = σ r := by
  have heq := decodeLiteralProgAt_eq_fixed cursorReg polReg varReg doneReg bound baseReg j
    boundE σ hbase hstable hbc hbp hbv hbd
  rw [heq]
  exact decodeLiteralProg_frame cursorReg polReg varReg doneReg bound
    (σ baseReg) 0 j r σ hrc hrp hrv hrd hrpCell hrvCell

def decodeThreeClauseProgAt
    (cursorReg polReg varReg doneReg : ℕ) (boundE : Expr) (baseReg : ℕ) : Program :=
  .seq (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0)
  <| .seq (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1)
      (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 2)

lemma decodeThreeClauseProgAt_eq_fixed
    (cursorReg polReg varReg doneReg bound baseReg _addr : ℕ) (boundE : Expr)
    (σ : Store) (hbase : baseReg < σ baseReg)
    (hstable : BoundExprStable boundE baseReg bound σ)
    (hbc : baseReg ≠ cursorReg) (hbp : baseReg ≠ polReg)
    (hbv : baseReg ≠ varReg) (hbd : baseReg ≠ doneReg) :
    (decodeThreeClauseProgAt cursorReg polReg varReg doneReg boundE baseReg).eval σ =
      (decodeThreeClauseProg cursorReg polReg varReg doneReg bound (σ baseReg) 0).eval σ := by
  unfold decodeThreeClauseProgAt decodeThreeClauseProg
  simp only [eval_seq]
  set σ1 := (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ
  have h0 := decodeLiteralProgAt_eq_fixed cursorReg polReg varReg doneReg bound baseReg 0
    boundE σ hbase hstable hbc hbp hbv hbd
  have h0base : σ1 baseReg = σ baseReg := by
    rw [show σ1 = (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ
      by rfl]
    apply decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 0 baseReg
      boundE σ hbase hstable hbc hbp hbv hbd hbc hbp hbv hbd
    · rw [literalPolCell_eq']; omega
    · rw [literalVarCell_eq']; omega
  have hstable1 : BoundExprStable boundE baseReg bound σ1 := by
    intro τ ht
    exact hstable τ (ht.trans h0base)
  set σ2 := (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval σ1
  have hbase1' : baseReg < σ1 baseReg := by rw [h0base]; exact hbase
  have h1 := decodeLiteralProgAt_eq_fixed cursorReg polReg varReg doneReg bound baseReg 1
    boundE σ1 hbase1' hstable1 hbc hbp hbv hbd
  have h1base : σ2 baseReg = σ1 baseReg := by
    apply decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 1 baseReg
      boundE σ1 hbase1' hstable1 hbc hbp hbv hbd hbc hbp hbv hbd
    · rw [literalPolCell_eq']; omega
    · rw [literalVarCell_eq']; omega
  have hstable2 : BoundExprStable boundE baseReg bound σ2 := by
    intro τ ht
    exact hstable1 τ (ht.trans h1base)
  have hbase2' : baseReg < σ2 baseReg := by rw [h1base, h0base]; exact hbase
  have h2 := decodeLiteralProgAt_eq_fixed cursorReg polReg varReg doneReg bound baseReg 2
    boundE σ2 hbase2' hstable2 hbc hbp hbv hbd
  have h2' :
      (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 2).eval
          ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
            ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ)) =
        (decodeLiteralProg cursorReg polReg varReg doneReg bound (σ baseReg) 0 2).eval
          ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
            ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ)) := by
    simpa [σ1, σ2, h1base, h0base] using h2
  have h1' :
      (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
          ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ) =
        (decodeLiteralProg cursorReg polReg varReg doneReg bound (σ baseReg) 0 1).eval
            ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ) := by
    simpa [σ1, h0base] using h1
  rw [h2', h1', h0]

lemma decodeThreeClauseProgAt_correct
    (cursorReg polReg varReg doneReg bound baseReg addr : ℕ) (boundE : Expr)
    (c : ThreeClause) (σ : Store)
    (hbase : baseReg < σ baseReg)
    (hstable : BoundExprStable boundE baseReg bound σ)
    (hbc : baseReg ≠ cursorReg) (hbp : baseReg ≠ polReg)
    (hbv : baseReg ≠ varReg) (hbd : baseReg ≠ doneReg)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr)
    (hda : doneReg < addr) (hcr : cursorReg < σ baseReg)
    (hpr : polReg < σ baseReg) (hvr : varReg < σ baseReg) (hdr : doneReg < σ baseReg)
    (hsep : addr + (encodeThreeClause c).length ≤ σ baseReg)
    (hb0 : c.l1.var + 1 ≤ bound) (hb1 : c.l2.var + 1 ≤ bound)
    (hb2 : c.l3.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeClause c)) :
    ThreeClauseAt
        ((decodeThreeClauseProgAt cursorReg polReg varReg doneReg boundE baseReg).eval σ)
        (σ baseReg) 0 c ∧
    (decodeThreeClauseProgAt cursorReg polReg varReg doneReg boundE baseReg).eval σ cursorReg =
      addr + (encodeThreeClause c).length := by
  have hfixed := decodeThreeClauseProg_correct cursorReg polReg varReg doneReg bound
    (σ baseReg) 0 addr c σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hcr hpr hvr hdr
    hsep hb0 hb1 hb2 hc hbits
  have heq := decodeThreeClauseProgAt_eq_fixed cursorReg polReg varReg doneReg bound baseReg
    addr boundE σ hbase hstable hbc hbp hbv hbd
  rw [← heq] at hfixed
  exact hfixed

lemma decodeThreeClauseProgAt_frame
    (cursorReg polReg varReg doneReg bound baseReg r : ℕ) (boundE : Expr) (σ : Store)
    (hbase : baseReg < σ baseReg) (hstable : BoundExprStable boundE baseReg bound σ)
    (hbc : baseReg ≠ cursorReg) (hbp : baseReg ≠ polReg)
    (hbv : baseReg ≠ varReg) (hbd : baseReg ≠ doneReg)
    (hrc : r ≠ cursorReg) (hrp : r ≠ polReg) (hrv : r ≠ varReg)
    (hrd : r ≠ doneReg)
    (hrcells : ∀ j, j < 3 → r ≠ literalPolCell (σ baseReg) 0 j ∧
      r ≠ literalVarCell (σ baseReg) 0 j) :
    (decodeThreeClauseProgAt cursorReg polReg varReg doneReg boundE baseReg).eval σ r = σ r := by
  unfold decodeThreeClauseProgAt
  simp only [eval_seq]
  set σ1 := (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ
  have h0 := decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 0 r
    boundE σ hbase hstable hbc hbp hbv hbd hrc hrp hrv hrd (hrcells 0 (by omega)).1
      (hrcells 0 (by omega)).2
  have hbase0 : σ1 baseReg = σ baseReg := by
    simpa [σ1] using (decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 0
      baseReg boundE σ hbase hstable hbc hbp hbv hbd hbc hbp hbv hbd
      (by rw [literalPolCell_eq']; omega) (by rw [literalVarCell_eq']; omega))
  have hstable1 : BoundExprStable boundE baseReg bound σ1 := by
    intro τ ht
    exact hstable τ (ht.trans hbase0)
  set σ2 := (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval σ1
  have hbase1' : baseReg < σ1 baseReg := by rw [hbase0]; exact hbase
  have h1 := decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 1 r
    boundE σ1 hbase1' hstable1 hbc hbp hbv hbd hrc hrp hrv hrd (by
      rw [hbase0]; exact (hrcells 1 (by omega)).1) (by
      rw [hbase0]; exact (hrcells 1 (by omega)).2)
  have hbase1 : σ2 baseReg = σ1 baseReg := by
    simpa [σ2] using (decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 1
      baseReg boundE σ1 hbase1' hstable1 hbc hbp hbv hbd hbc hbp hbv hbd
      (by rw [literalPolCell_eq']; omega) (by rw [literalVarCell_eq']; omega))
  have hstable2 : BoundExprStable boundE baseReg bound σ2 := by
    intro τ ht
    exact hstable1 τ (ht.trans hbase1)
  have hbase2' : baseReg < σ2 baseReg := by rw [hbase1, hbase0]; exact hbase
  have h2 := decodeLiteralProgAt_frame cursorReg polReg varReg doneReg bound baseReg 2 r
    boundE σ2 hbase2' hstable2 hbc hbp hbv hbd hrc hrp hrv hrd (by
      rw [hbase1, hbase0]; exact (hrcells 2 (by omega)).1) (by
      rw [hbase1, hbase0]; exact (hrcells 2 (by omega)).2)
  have h2' :
      (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 2).eval
          ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
            ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ)) r =
        ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
            ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ)) r := by
    simpa [σ1, σ2] using h2
  have h1' :
      (decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 1).eval
          ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ) r =
        ((decodeLiteralProgAt cursorReg polReg varReg doneReg boundE baseReg 0).eval σ) r := by
    simpa [σ1] using h1
  rw [h2', h1', h0]

end NPComplete.RAMToTM

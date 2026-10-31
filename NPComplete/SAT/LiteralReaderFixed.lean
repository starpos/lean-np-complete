module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded
public import NPComplete.SAT.ThreeCNFEncoding

/-!
# Literal reader

A literal can be read independently of any particular verifier or memory layout.
-/

@[expose] public section

namespace NPComplete.SAT

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat)

def decodeLiteralValueProgram
    (cursorReg polReg varReg doneReg bound : ℕ) : Program :=
  .seq (readBitAdvanceProg cursorReg polReg)
  <| .seq (.assign varReg (.const 0))
      <| .seq (.assign doneReg (.const 0))
          (decodeUnaryProg cursorReg varReg doneReg bound)

lemma decodeLiteralValueProgram_core
    (cursorReg polReg varReg doneReg bound addr pol v : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr)
    (hva : varReg < addr) (hda : doneReg < addr)
    (hbound : v + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hpol : σ addr = pol) (hbits : BitsFrom σ (addr + 1) (encodeNat v)) :
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ cursorReg =
        addr + v + 2 ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ polReg = pol ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ varReg = v ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ r = σ r) := by
  simp only [decodeLiteralValueProgram, eval_seq]
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ with hσ1def
  obtain ⟨hσ1pol, hσ1cur⟩ := readBitAdvanceProg_eval cursorReg polReg σ hcp
  rw [← hσ1def] at hσ1pol hσ1cur
  have hσ1bits : BitsFrom σ1 (addr + 1) (encodeNat v) := by
    intro k hk
    have hframe := readBitAdvanceProg_frame cursorReg polReg (addr + 1 + k) σ
      (by omega) (by omega)
    rw [hσ1def, hframe]
    exact hbits k hk
  set σ2 := (Program.assign varReg (Expr.const 0)).eval σ1 with hσ2def
  have hσ2eq : σ2 = writeReg σ1 varReg 0 := by
    rw [hσ2def]; simp only [eval_assign, Expr.eval]
  have hσ2var : σ2 varReg = 0 := by rw [hσ2eq, writeReg_same]
  have hσ2cur : σ2 cursorReg = σ1 cursorReg := by
    rw [hσ2eq]; exact writeReg_diff _ varReg _ cursorReg hcv
  have hσ2pol : σ2 polReg = σ1 polReg := by
    rw [hσ2eq]; exact writeReg_diff _ varReg _ polReg hpv
  have hσ2bits : BitsFrom σ2 (addr + 1) (encodeNat v) := by
    rw [hσ2eq]; exact bitsFrom_writeReg hσ1bits varReg 0 (by omega)
  set σ3 := (Program.assign doneReg (Expr.const 0)).eval σ2 with hσ3def
  have hσ3eq : σ3 = writeReg σ2 doneReg 0 := by
    rw [hσ3def]; simp only [eval_assign, Expr.eval]
  have hσ3done : σ3 doneReg = 0 := by rw [hσ3eq, writeReg_same]
  have hσ3cur : σ3 cursorReg = σ2 cursorReg := by
    rw [hσ3eq]; exact writeReg_diff _ doneReg _ cursorReg hcd
  have hσ3var : σ3 varReg = σ2 varReg := by
    rw [hσ3eq]; exact writeReg_diff _ doneReg _ varReg hvd
  have hσ3bits : BitsFrom σ3 (addr + 1) (encodeNat v) := by
    rw [hσ3eq]; exact bitsFrom_writeReg hσ2bits doneReg 0 (by omega)
  have hσ3cur' : σ3 cursorReg = addr + 1 := by
    rw [hσ3cur, hσ2cur, hσ1cur, hc]
  have hσ3var0 : σ3 varReg = 0 := by rw [hσ3var, hσ2var]
  obtain ⟨hfc, hfk, hfd, hfr⟩ := decodeUnaryProg_correct cursorReg varReg doneReg
    hcv hcd hvd v bound (σ3 cursorReg) 0 σ3 hbound
    (by rw [hσ3cur']; omega) (by rw [hσ3cur']; omega) (by rw [hσ3cur']; omega)
    rfl hσ3var0 hσ3done (by rw [hσ3cur']; exact hσ3bits)
  simp only [Nat.zero_add] at hfk
  set σ4 := (decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 with hσ4def
  have hσ4pol : σ4 polReg = σ3 polReg :=
    hfr polReg (Ne.symm hcp) hpv hpd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfc, hσ3cur']
    omega
  · rw [hσ4pol, hσ3eq, writeReg_diff _ doneReg _ polReg hpd,
      hσ2pol, hσ1pol, hc, hpol]
  · exact hfk
  · exact hfd
  · intro r hr1 hr2 hr3 hr4
    rw [hfr r hr1 hr3 hr4]
    rw [hσ3eq, writeReg_diff _ doneReg _ r hr4]
    rw [hσ2eq, writeReg_diff _ varReg _ r hr3]
    rw [hσ1def]
    exact readBitAdvanceProg_frame cursorReg polReg r σ hr1 hr2

lemma decodeLiteralValueProgram_correct
    (cursorReg polReg varReg doneReg bound addr : ℕ) (l : Literal) (rest : Bits)
    (σ : Store) (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr)
    (hva : varReg < addr) (hda : doneReg < addr)
    (hbound : l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest)) :
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ cursorReg =
        addr + l.var + 2 ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ polReg =
        (match l with | .pos _ => 0 | .neg _ => 1) ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ varReg = l.var ∧
    (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ r = σ r) := by
  cases l with
  | pos v =>
      have hshape : encodeLiteral (Literal.pos v) ++ rest =
          [false] ++ (encodeNat v ++ rest) := by
        simp [encodeLiteral]
      rw [hshape] at hbits
      obtain ⟨hpol, htail⟩ := bitsFrom_append σ addr [false] (encodeNat v ++ rest) hbits
      obtain ⟨hvar, _⟩ := bitsFrom_append σ (addr + 1) (encodeNat v) rest htail
      have hpolval : σ addr = 0 := by simpa using hpol 0 (by simp)
      have hvbound : v + 1 ≤ bound := by simpa [Literal.var] using hbound
      have h := decodeLiteralValueProgram_core cursorReg polReg varReg doneReg bound
        addr 0 v σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hvbound
        hc hpolval hvar
      simpa [Literal.var] using h
  | neg v =>
      have hshape : encodeLiteral (Literal.neg v) ++ rest =
          [true] ++ (encodeNat v ++ rest) := by
        simp [encodeLiteral]
      rw [hshape] at hbits
      obtain ⟨hpol, htail⟩ := bitsFrom_append σ addr [true] (encodeNat v ++ rest) hbits
      obtain ⟨hvar, _⟩ := bitsFrom_append σ (addr + 1) (encodeNat v) rest htail
      have hpolval : σ addr = 1 := by simpa using hpol 0 (by simp)
      have hvbound : v + 1 ≤ bound := by simpa [Literal.var] using hbound
      have h := decodeLiteralValueProgram_core cursorReg polReg varReg doneReg bound
        addr 1 v σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hvbound
        hc hpolval hvar
      simpa [Literal.var] using h

end NPComplete.SAT

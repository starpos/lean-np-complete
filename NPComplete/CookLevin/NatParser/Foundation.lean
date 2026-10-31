module

public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.BitEncoding
public import NPComplete.SAT.LiteralReader

/-!
# Executable bitstream decoder

Higher-level CNF parsing depends on small composable programs for reading unary
naturals, bits, literals, and clauses. This module establishes those primitives
and their correctness against the bit encoding, so later scanner modules can
focus on formula-level state and bounds.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr cost_forN loopCost loopCost_le_of_body_le
    eval_seq eval_assign eval_ifNZ eval_forN loopEval loopEval_succ cost_seq cost_assign
    writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_length)
open NPComplete.SAT (Literal encodeLiteral)

def decodeNatProgram (cursorReg countReg doneReg bound : ℕ) : Program :=
  decodeUnaryProg cursorReg countReg doneReg bound

lemma decodeNatProgram_encodeNat_append
    (cursorReg countReg doneReg n bound addr c0 : ℕ) (rest : Bits) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hkd : countReg ≠ doneReg)
    (hbound : n + 1 ≤ bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeNat n ++ rest)) :
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ cursorReg =
        addr + n + 1 ∧
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ countReg = c0 + n ∧
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeNatProgram cursorReg countReg doneReg bound).eval σ r = σ r) := by
  have hprefix : BitsFrom σ addr (encodeNat n) :=
    (bitsFrom_append σ addr (encodeNat n) rest hbits).1
  exact decodeUnaryProg_correct cursorReg countReg doneReg hcc hcd hkd n bound addr c0 σ
    hbound hca hka hda hc hk hd hprefix

lemma decodeNatProgram_encodeList_length_append
    {α : Type} (enc : α → Bits)
    (cursorReg countReg doneReg bound addr c0 : ℕ) (xs : List α) (rest : Bits)
    (σ : Store) (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hkd : countReg ≠ doneReg)
    (hbound : xs.length + 1 ≤ bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeList enc xs ++ rest)) :
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ cursorReg =
        addr + xs.length + 1 ∧
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ countReg = c0 + xs.length ∧
    (decodeNatProgram cursorReg countReg doneReg bound).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeNatProgram cursorReg countReg doneReg bound).eval σ r = σ r) := by
  have hshape : encodeList enc xs ++ rest =
      encodeNat xs.length ++ ((xs.map enc).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  rw [hshape] at hbits
  exact decodeNatProgram_encodeNat_append cursorReg countReg doneReg xs.length bound addr c0
    ((xs.map enc).flatten ++ rest) σ hcc hcd hkd hbound hca hka hda hc hk hd hbits

export NPComplete.SAT (decodeLiteralValueProgram)

/-- One bounded iteration of the clause scanner.

`remainingReg` counts literals still to decode and `maxReg` stores the largest
variable seen so far.  The outer loop supplies a bound at least as large as the
encoded clause length; iterations after the counter reaches zero are no-ops. -/
def decodeClauseStep
    (cursorReg polReg varReg doneReg remainingReg maxReg bound : ℕ) : Program :=
  .ifNZ (.reg remainingReg)
    (.seq (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
      <| .seq (.assign remainingReg (.sub (.reg remainingReg) (.const 1)))
          (.ifNZ (.lt (.reg maxReg) (.reg varReg))
            (.assign maxReg (.reg varReg)) .skip))
    .skip

export NPComplete.SAT (decodeLiteralValueProgram_core decodeLiteralValueProgram_correct)

lemma decode_nat_step_cost_le (cursorReg countReg doneReg : ℕ) :
    ∀ σ : Store, (decodeUnaryStep cursorReg countReg doneReg).cost σ ≤ 20 := by
  intro σ
  simp [decodeUnaryStep, Expr.cost]
  split <;> (try split) <;> omega

lemma decodeClauseStep_eval
    (cursorReg polReg varReg doneReg remainingReg maxReg bound addr k m : ℕ)
    (l : Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hrm : remainingReg ≠ maxReg)
    (hmc : maxReg ≠ cursorReg) (hmp : maxReg ≠ polReg)
    (hmv : maxReg ≠ varReg) (hmd : maxReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr)
    (hrem : σ remainingReg = k + 1) (hmax : σ maxReg = m)
    (hbound : l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest)) :
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ cursorReg =
        addr + l.var + 2 ∧
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ varReg =
        l.var ∧
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ doneReg = 1 ∧
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ remainingReg = k ∧
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ maxReg =
        max m l.var ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg →
      (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ r = σ r) := by
  obtain ⟨hcur, hpol, hvar, hdone, hframe⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l rest σ
      hcp hcv hcd hpv hpd hvd hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2.1
      hbound hc hbits
  set τ := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ
  have hτrem : τ remainingReg = k + 1 := by
    calc
      τ remainingReg = σ remainingReg := hframe remainingReg hrc hrp hrv hrd
      _ = k + 1 := hrem
  have hτmax : τ maxReg = m := by
    calc
      τ maxReg = σ maxReg := hframe maxReg hmc hmp hmv hmd
      _ = m := hmax
  have hτcur : τ cursorReg = addr + l.var + 2 := hcur
  have hτvar : τ varReg = l.var := hvar
  have hτdone : τ doneReg = 1 := hdone
  set υ := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ
  have hυeq : υ = writeReg τ remainingReg (τ remainingReg - 1) := by
    rw [show υ = (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ from rfl]
    simp only [eval_assign, Expr.eval]
  have hυrem : υ remainingReg = k := by
    rw [hυeq, writeReg_same, hτrem]
    omega
  have hυcur : υ cursorReg = τ cursorReg := by
    rw [hυeq, writeReg_diff _ remainingReg _ cursorReg (Ne.symm hrc)]
  have hυpol : υ polReg = τ polReg := by
    rw [hυeq, writeReg_diff _ remainingReg _ polReg (Ne.symm hrp)]
  have hυvar : υ varReg = τ varReg := by
    rw [hυeq, writeReg_diff _ remainingReg _ varReg (Ne.symm hrv)]
  have hυdone : υ doneReg = τ doneReg := by
    rw [hυeq, writeReg_diff _ remainingReg _ doneReg (Ne.symm hrd)]
  have hυmax : υ maxReg = τ maxReg := by
    rw [hυeq, writeReg_diff _ remainingReg _ maxReg (Ne.symm hrm)]
  have hstep :
      (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ =
        (if m < l.var then
          (Program.assign maxReg (.reg varReg)).eval υ else υ) := by
    unfold decodeClauseStep
    simp only [eval_ifNZ, eval_seq, Expr.eval]
    rw [ite_eq_left (by omega)]
    rw [show (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ = τ from rfl]
    rw [show (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval τ = υ from rfl]
    simp [hυmax, hυvar, hτmax, hτvar]
  rw [hstep]
  by_cases hlt : m < l.var
  · simp only [ite_eq_left hlt, eval_assign, Expr.eval]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeReg_diff _ maxReg _ cursorReg (Ne.symm hmc), hυcur, hτcur]
    · rw [writeReg_diff _ maxReg _ varReg (Ne.symm hmv), hυvar, hτvar]
    · rw [writeReg_diff _ maxReg _ doneReg (Ne.symm hmd), hυdone, hτdone]
    · rw [writeReg_diff _ maxReg _ remainingReg hrm, hυrem]
    · rw [writeReg_same, hυvar]
      omega
    · intro r h1 h2 h3 h4 h5 h6
      rw [writeReg_diff _ maxReg _ r h6, hυeq,
        writeReg_diff _ remainingReg _ r h5]
      exact hframe r h1 h2 h3 h4
  · simp only [ite_eq_right hlt]
    refine ⟨hυcur.trans hτcur, hυvar.trans hτvar, hυdone.trans hτdone, hυrem, ?_, ?_⟩
    · rw [hυmax]
      omega
    · intro r h1 h2 h3 h4 h5 h6
      rw [hυeq, writeReg_diff _ remainingReg _ r h5]
      exact hframe r h1 h2 h3 h4

lemma decodeClauseStep_zero
    (cursorReg polReg varReg doneReg remainingReg maxReg bound : ℕ) (σ : Store)
    (hrem : σ remainingReg = 0) :
    (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ = σ := by
  unfold decodeClauseStep
  simp only [eval_ifNZ, Expr.eval]
  simp [hrem]

def literalVarMax : List Literal → ℕ
  | [] => 0
  | l :: ls => max l.var (literalVarMax ls)

lemma decode_clause_loop_eval
    (cursorReg polReg varReg doneReg remainingReg maxReg bound addr m : ℕ)
    (xs : List Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hrm : remainingReg ≠ maxReg)
    (hmc : maxReg ≠ cursorReg) (hmp : maxReg ≠ polReg)
    (hmv : maxReg ≠ varReg) (hmd : maxReg ≠ doneReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ maxReg < addr)
    (hrem : σ remainingReg = xs.length) (hc : σ cursorReg = addr)
    (hmax : σ maxReg = m)
    (hbound : ∀ l ∈ xs, l.var + 1 ≤ bound)
    (hbits : BitsFrom σ addr ((xs.map encodeLiteral).flatten ++ rest)) :
    (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
      xs.length σ) cursorReg = addr + (xs.map encodeLiteral).flatten.length ∧
    (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
      xs.length σ) remainingReg = 0 ∧
    (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
      xs.length σ) maxReg = max m (literalVarMax xs) ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ maxReg →
      (loopEval (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
        xs.length σ) r = σ r) := by
  induction xs generalizing addr m σ with
  | nil =>
      simp [literalVarMax, hrem, hc, hmax]
  | cons l ls ih =>
      have hshape : ((l :: ls).map encodeLiteral).flatten ++ rest =
          encodeLiteral l ++ ((ls.map encodeLiteral).flatten ++ rest) := by
        simp
      rw [hshape] at hbits
      obtain ⟨hhead, htail⟩ := bitsFrom_append σ addr (encodeLiteral l)
        ((ls.map encodeLiteral).flatten ++ rest) hbits
      have hrem' : σ remainingReg = ls.length + 1 := by
        simpa using hrem
      have hbound_l : l.var + 1 ≤ bound := hbound l (by simp)
      obtain ⟨hcur1, hvar1, hdone1, hrem1, hmax1, hframe1⟩ :=
        decodeClauseStep_eval cursorReg polReg varReg doneReg remainingReg maxReg bound addr
          ls.length m l ((ls.map encodeLiteral).flatten ++ rest) σ
          hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hrm hmc hmp hmv hmd hbelow
          hrem' hmax hbound_l hc hbits
      set σ1 := (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ
        with hσ1
      have hlen : (encodeLiteral l).length = l.var + 2 := by
        cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
      set addr' := addr + (encodeLiteral l).length with haddr'
      have hc1 : σ1 cursorReg = addr' := by
        calc
          σ1 cursorReg = addr + l.var + 2 := hcur1
          _ = addr + (encodeLiteral l).length := by rw [hlen]; omega
          _ = addr' := by omega
      have hrem1' : σ1 remainingReg = ls.length := by
        exact hrem1
      have hmax1' : σ1 maxReg = max m l.var := by
        exact hmax1
      have hbits1 : BitsFrom σ1 addr' ((ls.map encodeLiteral).flatten ++ rest) := by
        intro i hi
        have hfr := hframe1 (addr' + i)
          (by rw [haddr']; omega) (by rw [haddr']; omega) (by rw [haddr']; omega)
          (by rw [haddr']; omega) (by rw [haddr']; omega) (by rw [haddr']; omega)
        calc
          σ1 (addr' + i) = σ (addr' + i) := hfr
          _ = σ (addr + (encodeLiteral l).length + i) := by rw [haddr']
          _ = if ((ls.map encodeLiteral).flatten ++ rest)[i] then 1 else 0 := htail i hi
      have hbound_ls : ∀ l' ∈ ls, l'.var + 1 ≤ bound := by
        intro l' hl'
        exact hbound l' (by simp [hl'])
      have hbelow' : cursorReg < addr' ∧ polReg < addr' ∧ varReg < addr' ∧
          doneReg < addr' ∧ remainingReg < addr' ∧ maxReg < addr' := by
        rw [haddr']
        omega
      obtain ⟨hcurTail, hremTail, hmaxTail, hframeTail⟩ :=
        ih addr' (max m l.var) σ1 hbelow' hrem1' hc1 hmax1' hbound_ls hbits1
      rw [show (l :: ls).length = ls.length + 1 by simp, loopEval_succ]
      rw [← hσ1]
      refine ⟨?_, hremTail, ?_, ?_⟩
      · rw [hcurTail, haddr']
        simp [hlen, List.length_append]; omega
      · rw [hmaxTail]
        simp [literalVarMax, max_assoc]
      · intro r h1 h2 h3 h4 h5 h6
        exact (hframeTail r h1 h2 h3 h4 h5 h6).trans (hframe1 r h1 h2 h3 h4 h5 h6)

end NPComplete.CookLevin

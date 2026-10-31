module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.NatParser
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Relocate
public import NPComplete.BoundedWhile.Frame

/-!
# Input-independent CNF decoder

`decodeNatProgram` and the fixed-bound clause steps bake unary loop bounds in as `.const`.
A single TM needs one `Program` for every CNF, so those bounds must be register
values sampled at loop entry.  This file is the `decodeUnaryProgAt` specialisation
of the existing scanner, with equality lemmas that recover the register-driven
dynamic scanners whenever the bound register still holds the bound.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd eval_ifNZ eval_forN eval_skip
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal encodeLiteral)

/-! ## Unary / literal scanners with a bound register -/

def decodeNatProgramAt (cursorReg countReg doneReg boundReg : ℕ) : Program :=
  decodeUnaryProgAt cursorReg countReg doneReg (.reg boundReg)

lemma decodeNatProgramAt_eq
    (cursorReg countReg doneReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ =
      (decodeNatProgram cursorReg countReg doneReg bound).eval σ := by
  unfold decodeNatProgramAt decodeNatProgram
  exact decodeUnaryProgAt_eq cursorReg countReg doneReg (.reg boundReg) bound σ
    (by simp [Expr.eval, hb])

lemma decodeNatProgramAt_encodeNat_append
    (cursorReg countReg doneReg boundReg n bound addr c0 : ℕ) (rest : Bits)
    (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hkd : countReg ≠ doneReg)
    (hbound : n + 1 ≤ bound) (hb : σ boundReg = bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeNat n ++ rest)) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ cursorReg =
        addr + n + 1 ∧
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ countReg = c0 + n ∧
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ r = σ r) := by
  rw [decodeNatProgramAt_eq cursorReg countReg doneReg boundReg bound σ hb]
  exact decodeNatProgram_encodeNat_append cursorReg countReg doneReg n bound addr c0
    rest σ hcc hcd hkd hbound hca hka hda hc hk hd hbits

lemma decodeNatProgramAt_frame
    (cursorReg countReg doneReg boundReg r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ countReg) (h3 : r ≠ doneReg) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ r = σ r :=
  decodeUnaryProgAt_frame cursorReg countReg doneReg (.reg boundReg) r σ h1 h2 h3

lemma decodeNatProgramAt_bound_frame
    (cursorReg countReg doneReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbv : boundReg ≠ countReg)
    (hbd : boundReg ≠ doneReg) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ boundReg =
      σ boundReg :=
  decodeNatProgramAt_frame cursorReg countReg doneReg boundReg boundReg σ hbc hbv hbd

@[construction_api] def decodeLiteralValueProgramAt
    (cursorReg polReg varReg doneReg boundReg : ℕ) : Program :=
  .seq (readBitAdvanceProg cursorReg polReg)
  <| .seq (.assign varReg (.const 0))
      <| .seq (.assign doneReg (.const 0))
          (decodeNatProgramAt cursorReg varReg doneReg boundReg)

lemma decodeLiteralValueProgramAt_eq
    (cursorReg polReg varReg doneReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ =
      (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ := by
  unfold decodeLiteralValueProgramAt decodeLiteralValueProgram
  rw [eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_seq]
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ
  have hσ1 : σ1 boundReg = bound :=
    (readBitAdvanceProg_frame cursorReg polReg boundReg σ hbc hbp).trans hb
  set σ2 := (Program.assign varReg (.const 0)).eval σ1
  have hσ2 : σ2 boundReg = bound := by
    simp only [σ2, eval_assign, Expr.eval]
    exact (writeReg_diff σ1 varReg 0 boundReg (hbv)).trans hσ1
  set σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hσ3 : σ3 boundReg = bound := by
    simp only [σ3, eval_assign, Expr.eval]
    exact (writeReg_diff σ2 doneReg 0 boundReg (hbd)).trans hσ2
  exact decodeNatProgramAt_eq cursorReg varReg doneReg boundReg bound σ3 hσ3

@[construction_api] lemma decodeLiteralValueProgramAt_avoids_frame
    (cursorReg polReg varReg doneReg boundReg : ℕ) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg) := by
  simp [Program.Avoids, decodeLiteralValueProgramAt, decodeNatProgramAt,
    decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg]

lemma decodeLiteralValueProgramAt_bound_frame
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
      boundReg = σ boundReg := by
  exact (decodeLiteralValueProgramAt_avoids_frame cursorReg polReg varReg doneReg boundReg).eval_frame
    σ ⟨hbc, hbp, hbv, hbd⟩

@[construction_api] lemma decodeLiteralValueProgramAt_correct
    (cursorReg polReg varReg doneReg boundReg bound addr : ℕ) (l : Literal)
    (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hpv : polReg ≠ varReg)
    (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr)
    (hva : varReg < addr) (hda : doneReg < addr)
    (hbound : l.var + 1 ≤ bound) (hb : σ boundReg = bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest)) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        cursorReg = addr + l.var + 2 ∧
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        polReg = (match l with | .pos _ => 0 | .neg _ => 1) ∧
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        varReg = l.var ∧
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        doneReg = 1 ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ r =
        σ r) := by
  rw [decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
    hb hbc hbp hbv hbd]
  exact decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l
    rest σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hbound hc hbits

@[construction_api] lemma decodeLiteralValueProgramAt_frame_rest
    (c p v d lr b : ℕ) (l : Literal) (rest : Bits) (σ : Store)
    (hc : c < b) (hp : p < b) (hv : v < b) (hd : d < b)
    (hbits : BitsFrom σ b (encodeLiteral l ++ rest)) :
    (∀ r, b ≤ r → (decodeLiteralValueProgramAt c p v d lr).eval σ r = σ r) ∧
      BitsFrom ((decodeLiteralValueProgramAt c p v d lr).eval σ)
        (b + (encodeLiteral l).length) rest := by
  have hf : ∀ r, b ≤ r → (decodeLiteralValueProgramAt c p v d lr).eval σ r = σ r := by
    intro r hr
    exact (decodeLiteralValueProgramAt_avoids_frame c p v d lr).eval_frame σ
      ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨hf, bitsFrom_of_eq_on (fun i _ => hf _ (by omega))
    (bitsFrom_append σ b (encodeLiteral l) rest hbits).2⟩

/-! ## Clause scanner: `.forN (.reg remainingReg)` plus a bound register -/

def decodeClauseStepAt
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ) : Program :=
  .ifNZ (.reg remainingReg)
    (.seq (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
      <| .seq (.assign remainingReg (.sub (.reg remainingReg) (.const 1)))
          (.ifNZ (.lt (.reg maxReg) (.reg varReg))
            (.assign maxReg (.reg varReg)) .skip))
    .skip

lemma decodeClauseStepAt_eq
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg bound : ℕ)
    (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg) :
    (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg).eval σ =
      (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound).eval σ := by
  unfold decodeClauseStepAt decodeClauseStep
  rw [eval_ifNZ, eval_ifNZ]
  split_ifs
  · have h := decodeLiteralValueProgramAt_eq cursorReg polReg varReg doneReg boundReg bound σ
      hb hbc hbp hbv hbd
    simp [eval_seq, h]
  · rfl

lemma decodeClauseStepAt_avoids_frame
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ) :
    (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg ∧
        r ≠ remainingReg ∧ r ≠ maxReg) := by
  simp [Program.Avoids, decodeClauseStepAt, decodeLiteralValueProgramAt,
    decodeNatProgramAt, decodeUnaryProgAt, decodeUnaryStep, readBitAdvanceProg]

lemma decodeClauseStepAt_bound_frame
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg : ℕ)
    (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg).eval σ
      boundReg = σ boundReg := by
  exact (decodeClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg maxReg
    boundReg).eval_frame σ ⟨hbc, hbp, hbv, hbd, hbr, hbm⟩

lemma decodeClauseStepAt_loopEval_eq
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg bound k : ℕ)
    (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    loopEval
        (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
        k σ =
      loopEval
        (decodeClauseStep cursorReg polReg varReg doneReg remainingReg maxReg bound)
        k σ := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
      have hstep := decodeClauseStepAt_eq cursorReg polReg varReg doneReg remainingReg
        maxReg boundReg bound σ hb hbc hbp hbv hbd
      have hb' := decodeClauseStepAt_bound_frame cursorReg polReg varReg doneReg
        remainingReg maxReg boundReg σ hbc hbp hbv hbd hbr hbm
      rw [loopEval_succ, loopEval_succ, hstep]
      apply ih
      exact hstep ▸ hb'.trans hb

def decodeClauseWithLengthPrefixAt
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) : Program :=
  .seq (.assign doneReg (.const 0))
      <| .seq (.assign lengthReg (.const 0))
        <| .seq (decodeNatProgramAt cursorReg lengthReg doneReg boundReg)
        <| .seq (.assign doneReg (.const 0))
          (.assign remainingReg (.reg lengthReg))

lemma decodeClauseWithLengthPrefixAt_eq
    (cursorReg doneReg remainingReg lengthReg boundReg bound : ℕ) (σ : Store)
    (hb : σ boundReg = bound)
    (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ =
      (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ := by
  unfold decodeClauseWithLengthPrefixAt decodeClauseWithLengthPrefix
  rw [eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_seq, eval_seq]
  set σ0 := (Program.assign doneReg (.const 0)).eval σ
  have hσ0 : σ0 boundReg = bound := by
    simp only [σ0, eval_assign, Expr.eval]
    exact (writeReg_diff σ doneReg 0 boundReg (hbd)).trans hb
  set σ1 := (Program.assign lengthReg (.const 0)).eval σ0
  have hσ1 : σ1 boundReg = bound := by
    simp only [σ1, eval_assign, Expr.eval]
    exact (writeReg_diff σ0 lengthReg 0 boundReg (hbl)).trans hσ0
  rw [decodeNatProgramAt_eq cursorReg lengthReg doneReg boundReg bound σ1 hσ1]

lemma decodeClauseWithLengthPrefixAt_avoids_frame
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ doneReg ∧ r ≠ remainingReg ∧ r ≠ lengthReg) := by
  simp [Program.Avoids, decodeClauseWithLengthPrefixAt, decodeNatProgramAt,
    decodeUnaryProgAt, decodeUnaryStep]

lemma decodeClauseWithLengthPrefixAt_bound_frame
    (cursorReg doneReg remainingReg lengthReg boundReg : ℕ) (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg) (hbr : boundReg ≠ remainingReg) :
    (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg).eval σ
      boundReg = σ boundReg := by
  exact (decodeClauseWithLengthPrefixAt_avoids_frame cursorReg doneReg remainingReg lengthReg
    boundReg).eval_frame σ ⟨hbc, hbd, hbr, hbl⟩

/-- Dynamic clause scanner: the literal loop is `.forN (.reg remainingReg)` and the
    unary bound is a register, so the whole command is input-independent. -/
def decodeClauseWithLengthProgramAt
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg boundReg : ℕ) :
    Program :=
  .seq (decodeClauseWithLengthPrefixAt cursorReg doneReg remainingReg lengthReg boundReg)
    (.forN (.reg remainingReg)
      (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg))

lemma decodeClauseWithLengthProgramAt_eq_dynamic
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg boundReg bound : ℕ)
    (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg boundReg).eval σ =
      (decodeClauseWithLengthProgramDynamic cursorReg polReg varReg doneReg remainingReg
        maxReg lengthReg bound).eval σ := by
  unfold decodeClauseWithLengthProgramAt decodeClauseWithLengthProgramDynamic
  rw [eval_seq, eval_seq, eval_forN, eval_forN]
  rw [decodeClauseWithLengthPrefixAt_eq cursorReg doneReg remainingReg lengthReg boundReg
    bound σ hb hbd hbl]
  set τ :=
    (decodeClauseWithLengthPrefix cursorReg doneReg remainingReg lengthReg bound).eval σ
  simp only [Expr.eval]
  have hbτ : τ boundReg = bound := by
    have hfr := decodeClauseWithLengthPrefixAt_bound_frame cursorReg doneReg remainingReg
      lengthReg boundReg σ hbc hbd hbl hbr
    have heq := decodeClauseWithLengthPrefixAt_eq cursorReg doneReg remainingReg lengthReg
      boundReg bound σ hb hbd hbl
    exact (heq ▸ hfr).trans hb
  exact decodeClauseStepAt_loopEval_eq cursorReg polReg varReg doneReg remainingReg
    maxReg boundReg bound (τ remainingReg) τ hbτ hbc hbp hbv hbd hbr hbm

/-! ## CNF scanner: `.forN (.reg outerReg)` plus a bound register -/

def decodeCNFClauseStepWithStatsAt
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      boundReg : ℕ) : Program :=
  .seq (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg boundReg)
    (clauseStatsProgram lengthReg freshReg countReg tmpReg)

def decodeCNFStepAt
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg : ℕ) : Program :=
  .seq (decodeCNFClauseStepWithStatsAt cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg)
    (.assign outerReg (.sub (.reg outerReg) (.const 1)))

/-- Mark that a nonempty clause (hence a literal) was observed. -/
def decodeCNFMarkSeenProg (lengthReg seenReg : ℕ) : Program :=
  .ifNZ (.reg lengthReg) (.assign seenReg (.const 1)) .skip

/-- For initial value `0`, the flag stays `0` until a nonempty clause is seen, then becomes `1`. -/
def cnfSeenStat : ℕ → List (List Literal) → ℕ
  | s, [] => s
  | s, ls :: rest => cnfSeenStat (if ls.length = 0 then s else 1) rest

lemma cnfSeenStat_one (cs : List (List Literal)) : cnfSeenStat 1 cs = 1 := by
  induction cs with
  | nil => rfl
  | cons ls rest ih =>
      simp only [cnfSeenStat]
      split_ifs <;> exact ih

lemma cnfSeenStat_zero_iff (cs : List (List Literal)) :
    cnfSeenStat 0 cs = 0 ↔ ∀ ls ∈ cs, ls.length = 0 := by
  induction cs with
  | nil => simp [cnfSeenStat]
  | cons ls rest ih =>
      simp only [cnfSeenStat, List.mem_cons, forall_eq_or_imp]
      by_cases hls : ls.length = 0
      · simpa [hls] using ih
      · simp [hls, cnfSeenStat_one rest]

def decodeCNFStepAtSeen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg seenReg : ℕ) : Program :=
  .seq
    (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg)
    (decodeCNFMarkSeenProg lengthReg seenReg)

def decodeCNFProgramAtSeen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg seenReg : ℕ) : Program :=
  .seq (.assign doneReg (.const 0))
    <| .seq (.assign outerReg (.const 0))
      <| .seq (decodeNatProgramAt cursorReg outerReg doneReg boundReg)
        (.forN (.reg outerReg)
          (decodeCNFStepAtSeen cursorReg polReg varReg doneReg outerReg remainingReg maxReg
            lengthReg freshReg countReg tmpReg boundReg seenReg))

lemma decodeCNFClauseStepWithStatsAt_eq_dynamic
    (cursorReg polReg varReg doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg
      boundReg bound : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    (decodeCNFClauseStepWithStatsAt cursorReg polReg varReg doneReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg).eval σ =
      (decodeCNFClauseStepWithStatsDynamic cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg bound).eval σ := by
  unfold decodeCNFClauseStepWithStatsAt decodeCNFClauseStepWithStatsDynamic
  rw [eval_seq, eval_seq, decodeClauseWithLengthProgramAt_eq_dynamic cursorReg polReg varReg
    doneReg remainingReg maxReg lengthReg boundReg bound σ hb hbc hbp hbv hbd hbl hbr hbm]

lemma decodeCNFStepAt_eq_dynamic
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg bound : ℕ) (σ : Store) (hb : σ boundReg = bound)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbl : boundReg ≠ lengthReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg boundReg).eval σ =
      (decodeCNFStepDynamic cursorReg polReg varReg doneReg outerReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg bound).eval σ := by
  unfold decodeCNFStepAt decodeCNFStepDynamic
  rw [eval_seq, eval_seq, decodeCNFClauseStepWithStatsAt_eq_dynamic cursorReg polReg varReg
    doneReg remainingReg maxReg lengthReg freshReg countReg tmpReg boundReg bound σ hb
    hbc hbp hbv hbd hbl hbr hbm]

lemma decodeClauseStepAt_loopEval_bound_frame
    (cursorReg polReg varReg doneReg remainingReg maxReg boundReg k : ℕ)
    (σ : Store)
    (hbc : boundReg ≠ cursorReg) (hbp : boundReg ≠ polReg)
    (hbv : boundReg ≠ varReg) (hbd : boundReg ≠ doneReg)
    (hbr : boundReg ≠ remainingReg) (hbm : boundReg ≠ maxReg) :
    loopEval
        (decodeClauseStepAt cursorReg polReg varReg doneReg remainingReg maxReg boundReg)
        k σ boundReg = σ boundReg := by
  exact (decodeClauseStepAt_avoids_frame cursorReg polReg varReg doneReg remainingReg maxReg
    boundReg).loopEval_frame ⟨hbc, hbp, hbv, hbd, hbr, hbm⟩ k σ

/-! ## `bitInputStore` is a legal relocate input -/

lemma decodeCNFStepAtSeen_eval_except_seen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg seenReg : ℕ) (σ : Store)
    (r : ℕ) (hr : r ≠ seenReg) :
    (decodeCNFStepAtSeen cursorReg polReg varReg doneReg outerReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg seenReg).eval σ r =
      (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg boundReg).eval σ r := by
  unfold decodeCNFStepAtSeen decodeCNFMarkSeenProg
  rw [eval_seq]
  set σ1 :=
    (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg).eval σ
  simp only [eval_ifNZ, Expr.eval]
  by_cases hlen : σ1 lengthReg = 0
  · simp [eval_skip, hlen]
  · simp [eval_assign, Expr.eval, hlen, writeReg_diff σ1 seenReg 1 r hr]

lemma decodeCNFStepAtSeen_seen
    (cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg freshReg countReg
      tmpReg boundReg seenReg : ℕ) (σ : Store)
    (hpres : ((decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg boundReg).eval σ) seenReg = σ seenReg) :
    let σ1 :=
      (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg boundReg).eval σ
    (decodeCNFStepAtSeen cursorReg polReg varReg doneReg outerReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg seenReg).eval σ seenReg =
      if σ1 lengthReg ≠ 0 then 1 else σ seenReg := by
  unfold decodeCNFStepAtSeen decodeCNFMarkSeenProg
  rw [eval_seq]
  set σ1 :=
    (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg
      lengthReg freshReg countReg tmpReg boundReg).eval σ
  simp only [eval_ifNZ, Expr.eval]
  by_cases hlen : σ1 lengthReg = 0
  · simpa [eval_skip, hlen] using hpres
  · simp [eval_assign, Expr.eval, hlen, writeReg_same]

/-! Writer output starts at a fixed low address above every control register of the uniform
    decoder. The workspace limit `M` and relocated input sit above that window so
    `CNFEmitRel.input_above` / `start_at_input` hold: `M + tmpJ < addr` and `start ≤ addr`.
    `tmpJ = 2`, so the input base is `M + 3`. -/

def uniformStartNat : ℕ := relocateControlGap

def uniformAddrOffset : ℕ := 3

def uniformSlackNat (N : ℕ) : ℕ :=
  (N + 1) * (N + 1) * (N + 1) + 16

def uniformMNat (N : ℕ) : ℕ :=
  uniformStartNat + uniformSlackNat N

def uniformAddrNat (N : ℕ) : ℕ :=
  uniformMNat N + uniformAddrOffset

def uniformSlackE : Expr :=
  .add
    (.mul (.add (.reg 0) (.const 1))
      (.mul (.add (.reg 0) (.const 1))
        (.add (.reg 0) (.const 1))))
    (.const 16)

def uniformMFromN : Expr :=
  .add (.const uniformStartNat) uniformSlackE

def uniformAddrE : Expr :=
  .add uniformMFromN (.const uniformAddrOffset)

lemma uniformSlackNat_ge_succ (N : ℕ) :
    N + 1 ≤ (N + 1) * (N + 1) * (N + 1) := by
  have h1 : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have h2 : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_of_pos_right (N + 1) h1
  exact h2.trans (Nat.le_mul_of_pos_right ((N + 1) * (N + 1)) h1)

lemma uniformAddrNat_ge_gap (N : ℕ) :
    N + relocateControlGap ≤ uniformAddrNat N := by
  have hcu := uniformSlackNat_ge_succ N
  simp [uniformAddrNat, uniformMNat, uniformSlackNat, uniformStartNat,
    uniformAddrOffset, relocateControlGap]
  omega

lemma uniformAddrNat_ge_start (N : ℕ) :
    uniformStartNat ≤ uniformAddrNat N := by
  simp [uniformAddrNat, uniformMNat, uniformStartNat, uniformAddrOffset]
  omega

lemma uniformAddrNat_ge_25 (N : ℕ) : 25 ≤ uniformAddrNat N := by
  have h := uniformAddrNat_ge_start N
  simp [uniformStartNat, relocateControlGap] at h
  omega

lemma uniformMNat_add_two_lt_addr (N : ℕ) :
    uniformMNat N + 2 < uniformAddrNat N := by
  simp [uniformAddrNat, uniformAddrOffset]

lemma uniformAddrE_eval (σ : Store) :
    uniformAddrE.eval σ = uniformAddrNat (σ 0) := by
  simp [uniformAddrE, uniformMFromN, uniformSlackE, uniformAddrNat, uniformMNat,
    uniformSlackNat, uniformStartNat, uniformAddrOffset, Expr.eval, Nat.mul_assoc]

def uniformRelocateSetup : Program :=
  .seq (relocateCtlAssign relocateSrcJ (.const 1))
    (.seq (relocateCtlAssign relocateDstJ uniformAddrE)
      (.seq (relocateCtlAssign relocateLenJ (.reg 0))
        (relocateCtlAssign relocateBaseJ uniformAddrE)))

def uniformRelocateProg : Program :=
  .seq uniformRelocateSetup (.forN (relocateCtlCell relocateLenJ) relocateStep)

lemma uniformRelocateSetup_eval (N : ℕ) (σ : Store) (h0 : σ 0 = N) :
    uniformRelocateSetup.eval σ =
      fun r => if r = N + relocateSrcJ then 1 else
        if r = N + relocateDstJ then uniformAddrNat N else
        if r = N + relocateLenJ then N else
        if r = N + relocateBaseJ then uniformAddrNat N else σ r := by
  have hC (τ : Store) (hτ : τ 0 = N) : uniformAddrE.eval τ = uniformAddrNat N := by
    rw [uniformAddrE_eval, hτ]
  funext r
  simp [uniformRelocateSetup, relocateCtlAssign, eval_seq, eval_assignInd,
    relocateCtlAddr_eval, Expr.eval, writeReg, relocateSrcJ, relocateDstJ,
     relocateLenJ, relocateBaseJ, h0, hC]
  by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
     by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;> simp_all

lemma uniformRelocateSetup_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    RelocateInvariant σ (uniformRelocateSetup.eval σ) N (uniformAddrNat N) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uniformRelocateSetup_eval N σ h0]
    simpa [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ] using h0
  · rw [uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ]
  · rw [uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ]
  · rw [uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ]
  · rw [uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ]
  · intro q hq
    omega
  · intro r hr
    rw [uniformRelocateSetup_eval N σ h0]
    by_cases h1 : r = N + 1 <;> by_cases h2 : r = N + 2 <;>
      by_cases h3 : r = N + 3 <;> by_cases h4 : r = N + 4 <;>
      simp_all [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ]

lemma uniform_relocate_loop_invariant (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ∀ t, t ≤ N →
      RelocateInvariant σ
        (loopEval relocateStep t (uniformRelocateSetup.eval σ))
        N (uniformAddrNat N) t := by
  intro t ht
  exact relocate_loop_invariant_from σ (uniformRelocateSetup.eval σ) N
    (uniformAddrNat N) (uniformAddrNat_ge_gap N)
    (uniformRelocateSetup_invariant σ N h0) t ht

lemma uniformRelocateProg_eval_eq_loop (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    uniformRelocateProg.eval σ =
      loopEval relocateStep N (uniformRelocateSetup.eval σ) := by
  have hbound : (relocateCtlCell relocateLenJ).eval (uniformRelocateSetup.eval σ) = N := by
    rw [relocateCtlCell_eval, uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  unfold uniformRelocateProg
  rw [eval_seq, eval_forN, hbound]

lemma uniformRelocateProg_output (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    ∀ t, t < bits.length →
      (uniformRelocateProg.eval σ) (uniformAddrNat bits.length + t) = σ (1 + t) := by
  intro t ht
  have h0 := hin.1
  have hInv := uniform_relocate_loop_invariant σ bits.length h0 bits.length le_rfl
  rw [uniformRelocateProg_eval_eq_loop σ bits.length h0]
  exact hInv.2.2.2.2.2.1 t ht

lemma uniformRelocateProg_bitsFrom (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    BitsFrom (uniformRelocateProg.eval σ) (uniformAddrNat bits.length) bits := by
  intro i hi
  rw [uniformRelocateProg_output σ bits hin i hi]
  exact hin.2 i hi

lemma uniformRelocateProg_zero (σ : Store) (bits : Bits)
    (hin : RelocateInput σ bits) :
    (uniformRelocateProg.eval σ) 0 = bits.length := by
  have hInv := uniform_relocate_loop_invariant σ bits.length hin.1 bits.length le_rfl
  rw [uniformRelocateProg_eval_eq_loop σ bits.length hin.1]
  exact hInv.1

lemma relocateInput_bitInputStore (bits : Bits) :
    RelocateInput (bitInputStore bits) bits := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have hsucc : 1 + i = i.succ := Nat.add_comm 1 i
  rw [hsucc]
  simp only [bitInputStore]
  have hget : bits[i]?.getD false = bits[i] := by
    simp [List.getElem?_eq_getElem hi]
  simp [hget]

lemma uniformRelocateProg_bitInputStore (bits : Bits) :
    (uniformRelocateProg.eval (bitInputStore bits)) 0 = bits.length ∧
    BitsFrom (uniformRelocateProg.eval (bitInputStore bits))
      (uniformAddrNat bits.length) bits :=
  ⟨uniformRelocateProg_zero _ _ (relocateInput_bitInputStore bits),
    uniformRelocateProg_bitsFrom _ _ (relocateInput_bitInputStore bits)⟩

/-- After relocate, point the cursor at the copied input.  Cell 0 still holds
    the original length and is the unary bound register. -/
def uniformCursorInitProg (cursorReg inputBaseReg : ℕ) : Program :=
  .seq (.assign inputBaseReg uniformAddrE)
    (.assign cursorReg (.reg inputBaseReg))

lemma uniformCursorInitProg_eval
    (cursorReg inputBaseReg : ℕ) (σ : Store) (N : ℕ)
    (h0 : σ 0 = N) (hci : cursorReg ≠ inputBaseReg) (h0c : cursorReg ≠ 0)
    (h0i : inputBaseReg ≠ 0) :
    (uniformCursorInitProg cursorReg inputBaseReg).eval σ inputBaseReg =
        uniformAddrNat N ∧
    (uniformCursorInitProg cursorReg inputBaseReg).eval σ cursorReg =
        uniformAddrNat N ∧
    (uniformCursorInitProg cursorReg inputBaseReg).eval σ 0 = N := by
  have hC : uniformAddrE.eval σ = uniformAddrNat N := by
    rw [uniformAddrE_eval, h0]
  have hσ :
      (uniformCursorInitProg cursorReg inputBaseReg).eval σ =
        writeReg (writeReg σ inputBaseReg (uniformAddrNat N))
          cursorReg (uniformAddrNat N) := by
    simp [uniformCursorInitProg, eval_seq, eval_assign, Expr.eval, hC]
  rw [hσ]
  refine ⟨?_, ?_, ?_⟩
  · rw [writeReg_diff _ cursorReg _ inputBaseReg (Ne.symm hci), writeReg_same]
  · rw [writeReg_same]
  · rw [writeReg_diff _ cursorReg _ 0 (Ne.symm h0c),
      writeReg_diff _ inputBaseReg _ 0 (Ne.symm h0i), h0]

lemma uniformCursorInitProg_frame
    (cursorReg inputBaseReg r : ℕ) (σ : Store)
    (hrc : r ≠ cursorReg) (hri : r ≠ inputBaseReg) :
    (uniformCursorInitProg cursorReg inputBaseReg).eval σ r = σ r := by
  simp [uniformCursorInitProg, eval_seq, eval_assign, Expr.eval,
    writeReg_diff _ cursorReg _ r hrc, writeReg_diff _ inputBaseReg _ r hri]

lemma encodeList_length_ge_count {α : Type} (enc : α → Bits) (xs : List α) :
    xs.length + 1 ≤ (encodeList enc xs).length :=
  encodeList_length_ge enc xs

def zeroRegsProg : List ℕ → Program
  | [] => .skip
  | r :: rs => .seq (.assign r (.const 0)) (zeroRegsProg rs)

lemma zeroRegsProg_frame (rs : List ℕ) (s : ℕ) (σ : Store) (hs : s ∉ rs) :
    (zeroRegsProg rs).eval σ s = σ s := by
  induction rs generalizing σ with
  | nil => simp [zeroRegsProg]
  | cons r rest ih =>
      have hcons : ¬ (s = r ∨ s ∈ rest) := by simpa using hs
      simp only [zeroRegsProg, eval_seq, eval_assign, Expr.eval]
      exact (ih _ (fun h => hcons (Or.inr h))).trans
        (writeReg_diff σ r 0 s (fun h => hcons (Or.inl h)))

lemma zeroRegsProg_zero (rs : List ℕ) (r : ℕ) (σ : Store) (hr : r ∈ rs) :
    (zeroRegsProg rs).eval σ r = 0 := by
  induction rs generalizing σ with
  | nil => cases hr
  | cons s rest ih =>
      simp only [zeroRegsProg, eval_seq]
      rcases List.mem_cons.mp hr with h | h
      · subst h
        by_cases hmem : r ∈ rest
        · exact ih _ hmem
        · have hfr := zeroRegsProg_frame rest r
            ((Program.assign r (.const 0)).eval σ) hmem
          simpa [eval_assign, Expr.eval, writeReg_same] using hfr
      · exact ih _ h

/-! Fixed register layout for the uniform CNF decoder.  Cell 0 is the bound. -/

def uctBoundReg : ℕ := 0
def uctCursorReg : ℕ := 1
def uctPolReg : ℕ := 2
def uctVarReg : ℕ := 3
def uctDoneReg : ℕ := 4
def uctOuterReg : ℕ := 5
def uctRemainingReg : ℕ := 6
def uctMaxReg : ℕ := 7
def uctLengthReg : ℕ := 8
def uctFreshReg : ℕ := 9
def uctCountReg : ℕ := 10
def uctTmpReg : ℕ := 11
def uctInputBaseReg : ℕ := 12
def uctSeenReg : ℕ := 24

/-- Working controls that must not keep leftover relocate bits.  Cursor, bound,
    and input base are set by relocate/cursor-init and are excluded. -/
def uctControlRegs : List ℕ :=
  [uctPolReg, uctVarReg, uctDoneReg, uctOuterReg, uctRemainingReg,
    uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg, uctTmpReg, uctSeenReg]

def uniformControlInitProg : Program :=
  zeroRegsProg uctControlRegs

lemma uctControlRegs_not_bound : uctBoundReg ∉ uctControlRegs := by
  simp [uctControlRegs, uctBoundReg, uctPolReg, uctVarReg, uctDoneReg, uctOuterReg,
    uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg, uctTmpReg,
    uctSeenReg]

lemma uctControlRegs_not_cursor : uctCursorReg ∉ uctControlRegs := by
  simp [uctControlRegs, uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctOuterReg,
    uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg, uctTmpReg,
    uctSeenReg]

lemma uctControlRegs_not_inputBase : uctInputBaseReg ∉ uctControlRegs := by
  simp [uctControlRegs, uctInputBaseReg, uctPolReg, uctVarReg, uctDoneReg, uctOuterReg,
    uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg, uctTmpReg,
    uctSeenReg]

lemma not_mem_uctControlRegs_of_ge (r : ℕ) (hr : 25 ≤ r) :
    r ∉ uctControlRegs := by
  simp [uctControlRegs, uctPolReg, uctVarReg, uctDoneReg, uctOuterReg,
    uctRemainingReg, uctMaxReg, uctLengthReg, uctFreshReg, uctCountReg, uctTmpReg,
    uctSeenReg]
  omega

lemma uniformControlInitProg_zero (r : ℕ) (σ : Store) (hr : r ∈ uctControlRegs) :
    (uniformControlInitProg.eval σ) r = 0 :=
  zeroRegsProg_zero uctControlRegs r σ hr

lemma uniformControlInitProg_frame (r : ℕ) (σ : Store) (hr : r ∉ uctControlRegs) :
    (uniformControlInitProg.eval σ) r = σ r :=
  zeroRegsProg_frame uctControlRegs r σ hr

lemma uniformCursorInitProg_after_relocate (bits : Bits) :
    let σ := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits))
    σ uctBoundReg = bits.length ∧
    σ uctInputBaseReg = uniformAddrNat bits.length ∧
    σ uctCursorReg = uniformAddrNat bits.length := by
  have hp := uniformRelocateProg_bitInputStore bits
  have h := uniformCursorInitProg_eval uctCursorReg uctInputBaseReg
    (uniformRelocateProg.eval (bitInputStore bits)) bits.length hp.1
    (by decide) (by decide) (by decide)
  exact ⟨h.2.2, h.1, h.2.1⟩

lemma uniformCursorInitProg_bitsFrom (bits : Bits) :
    BitsFrom
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
      (uniformAddrNat bits.length) bits := by
  have hp := uniformRelocateProg_bitInputStore bits
  intro i hi
  have hge := uniformAddrNat_ge_25 bits.length
  have haddr : uctCursorReg ≠ uniformAddrNat bits.length + i := by
    simp [uctCursorReg]; omega
  have hbase : uctInputBaseReg ≠ uniformAddrNat bits.length + i := by
    simp [uctInputBaseReg]; omega
  rw [uniformCursorInitProg_frame uctCursorReg uctInputBaseReg
    (uniformAddrNat bits.length + i)
    (uniformRelocateProg.eval (bitInputStore bits)) (Ne.symm haddr) (Ne.symm hbase)]
  exact hp.2 i hi

lemma uniformControlInitProg_after_cursor (bits : Bits) :
    let σ := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    σ uctBoundReg = bits.length ∧
    σ uctInputBaseReg = uniformAddrNat bits.length ∧
    σ uctCursorReg = uniformAddrNat bits.length ∧
    σ uctPolReg = 0 ∧ σ uctVarReg = 0 ∧ σ uctDoneReg = 0 ∧ σ uctOuterReg = 0 ∧
    σ uctRemainingReg = 0 ∧ σ uctMaxReg = 0 ∧ σ uctLengthReg = 0 ∧
    σ uctFreshReg = 0 ∧ σ uctCountReg = 0 ∧ σ uctTmpReg = 0 ∧
    σ uctSeenReg = 0 := by
  set σc := (uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
    (uniformRelocateProg.eval (bitInputStore bits))
  have hc := uniformCursorInitProg_after_relocate bits
  have hb := uniformControlInitProg_frame uctBoundReg σc uctControlRegs_not_bound
  have hi := uniformControlInitProg_frame uctInputBaseReg σc uctControlRegs_not_inputBase
  have hcur := uniformControlInitProg_frame uctCursorReg σc uctControlRegs_not_cursor
  refine ⟨hb.trans hc.1, hi.trans hc.2.1, hcur.trans hc.2.2, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])
  · exact uniformControlInitProg_zero _ σc (by simp [uctControlRegs])

lemma uniformControlInitProg_bitsFrom (bits : Bits) :
    BitsFrom
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore bits))))
      (uniformAddrNat bits.length) bits := by
  intro i hi
  have hr : uniformAddrNat bits.length + i ∉ uctControlRegs :=
    not_mem_uctControlRegs_of_ge _ (by
      have hge := uniformAddrNat_ge_25 bits.length
      omega)
  rw [uniformControlInitProg_frame _ _ hr]
  exact uniformCursorInitProg_bitsFrom bits i hi

lemma decodeCNFStepDynamic_uct_eval
    (bound a m base c k : ℕ) (ls : List Literal) (tail : Bits) (τ : Store)
    (ha : 12 ≤ a) (houter : τ uctOuterReg = k + 1)
    (hc : τ uctCursorReg = a) (hmax : τ uctMaxReg = m)
    (hbase : τ uctFreshReg = base) (hcount : τ uctCountReg = c)
    (hbound : ls.length + 1 ≤ bound)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbits : BitsFrom τ a (encodeList encodeLiteral ls ++ tail)) :
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctCursorReg =
        a + (encodeList encodeLiteral ls).length ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctOuterReg = k ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctRemainingReg = 0 ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctMaxReg = max m (literalVarMax ls) ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctLengthReg = ls.length ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctFreshReg = base + clauseFreshIncByLength ls.length ∧
    (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      bound).eval τ uctCountReg = c + clauseThreeCountByLength ls.length ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg →
      (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        bound).eval τ r = τ r) := by
  have hpreBelow :
      uctCursorReg < a ∧ uctDoneReg < a ∧ uctLengthReg < a := by
    simp [uctCursorReg, uctDoneReg, uctLengthReg]; omega
  have hprefix := decodeClauseWithLengthPrefix_remaining_eval
    uctCursorReg uctDoneReg uctRemainingReg uctLengthReg bound a ls tail τ
    (by decide) (by decide) (by decide) hpreBelow hc hbound hbits
  have heq := decodeCNFStepDynamic_eq_fixed_of_prefix
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg uctRemainingReg
    uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg bound ls.length τ
    hprefix
  have hbelow :
      uctCursorReg < a ∧ uctPolReg < a ∧ uctVarReg < a ∧ uctDoneReg < a ∧
        uctRemainingReg < a ∧ uctMaxReg < a ∧ uctLengthReg < a := by
    simp [uctCursorReg, uctPolReg, uctVarReg, uctDoneReg, uctRemainingReg,
      uctMaxReg, uctLengthReg]; omega
  have hstats := decodeCNFClauseStepWithStats_eval
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctRemainingReg uctMaxReg
    uctLengthReg uctFreshReg uctCountReg uctTmpReg bound ls.length a m base c
    ls tail τ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hbelow hc hmax hbase hcount hbound (Nat.le_refl _) hvarbound hbits
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstep := decodeCNFStep_eval_from_clause
    uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg uctRemainingReg
    uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg bound ls.length
    a (a + (encodeList encodeLiteral ls).length)
    (max m (literalVarMax ls)) base c k ls.length
    (base + clauseFreshIncByLength ls.length)
    (c + clauseThreeCountByLength ls.length) τ
    hstats.1 hstats.2.1 hstats.2.2.1 hstats.2.2.2.1 hstats.2.2.2.2.1
    hstats.2.2.2.2.2.1 houter hstats.2.2.2.2.2.2 (by decide)
  rw [heq]
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2⟩

lemma decodeCNFStepAt_eq_dynamic_uct (bound : ℕ) (σ : Store)
    (hb : σ uctBoundReg = bound) :
    (decodeCNFStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg).eval σ =
      (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        bound).eval σ :=
  decodeCNFStepAt_eq_dynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
    uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
    uctBoundReg bound σ hb
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

lemma decodeCNFStepAtSeen_uct_except_seen (bound : ℕ) (σ : Store)
    (hb : σ uctBoundReg = bound) (r : ℕ) (hr : r ≠ uctSeenReg) :
    (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ r =
      (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        bound).eval σ r := by
  have hstep := decodeCNFStepAtSeen_eval_except_seen uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg
    uctCountReg uctTmpReg uctBoundReg uctSeenReg σ r hr
  exact hstep.trans (congrFun (decodeCNFStepAt_eq_dynamic_uct bound σ hb) r)

lemma decodeCNFStepAtSeen_uct_eval
    (bound a m base c k s : ℕ) (ls : List Literal) (tail : Bits) (τ : Store)
    (ha : 25 ≤ a) (houter : τ uctOuterReg = k + 1)
    (hc : τ uctCursorReg = a) (hmax : τ uctMaxReg = m)
    (hbase : τ uctFreshReg = base) (hcount : τ uctCountReg = c)
    (hseen : τ uctSeenReg = s) (hb : τ uctBoundReg = bound)
    (hbound : ls.length + 1 ≤ bound)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbits : BitsFrom τ a (encodeList encodeLiteral ls ++ tail)) :
    let σs :=
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ
    σs uctCursorReg = a + (encodeList encodeLiteral ls).length ∧
    σs uctOuterReg = k ∧
    σs uctRemainingReg = 0 ∧
    σs uctMaxReg = max m (literalVarMax ls) ∧
    σs uctLengthReg = ls.length ∧
    σs uctFreshReg = base + clauseFreshIncByLength ls.length ∧
    σs uctCountReg = c + clauseThreeCountByLength ls.length ∧
    σs uctSeenReg = (if ls.length = 0 then s else 1) ∧
    σs uctBoundReg = bound ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg →
      σs r = τ r) := by
  have ha12 : 12 ≤ a := (by decide : 12 ≤ 25).trans ha
  obtain ⟨hcur, houter', hrem, hmax', hlen, hfresh, hcount', hframe⟩ :=
    decodeCNFStepDynamic_uct_eval bound a m base c k ls tail τ ha12 houter hc hmax
      hbase hcount hbound hvarbound hbits
  have hexcept (r : ℕ) (hr : r ≠ uctSeenReg) :
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ r =
        (decodeCNFStepDynamic uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          bound).eval τ r :=
    decodeCNFStepAtSeen_uct_except_seen bound τ hb r hr
  have hpres :
      ((decodeCNFStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg).eval τ) uctSeenReg = τ uctSeenReg := by
    rw [decodeCNFStepAt_eq_dynamic_uct bound τ hb]
    exact hframe uctSeenReg (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hseen' :=
    decodeCNFStepAtSeen_seen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg τ hpres
  have hlenAt :
      ((decodeCNFStepAt uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg).eval τ) uctLengthReg = ls.length := by
    rw [decodeCNFStepAt_eq_dynamic_uct bound τ hb, hlen]
  have hseenVal :
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ uctSeenReg =
        if ls.length = 0 then s else 1 := by
    have h := hseen'
    simp only [hlenAt, hseen] at h
    by_cases hz : ls.length = 0
    · simp [hz] at h ⊢; exact h
    · simp [hz] at h ⊢; exact h
  have hbound' :
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ uctBoundReg = bound :=
    (hexcept uctBoundReg (by decide)).trans
      ((hframe uctBoundReg (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hb)
  refine ⟨(hexcept uctCursorReg (by decide)).trans hcur,
    (hexcept uctOuterReg (by decide)).trans houter',
    (hexcept uctRemainingReg (by decide)).trans hrem,
    (hexcept uctMaxReg (by decide)).trans hmax',
    (hexcept uctLengthReg (by decide)).trans hlen,
    (hexcept uctFreshReg (by decide)).trans hfresh,
    (hexcept uctCountReg (by decide)).trans hcount',
    hseenVal, hbound', ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact (hexcept r h12).trans (hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

lemma decodeCNFStepAtSeen_seen_loop_uct_eval
    (bound : ℕ) (clauses : List (List Literal)) (rest : Bits)
    (addr m base c s : ℕ) (σ : Store)
    (houter : σ uctOuterReg = clauses.length) (hc : σ uctCursorReg = addr)
    (hmax : σ uctMaxReg = m) (hbase : σ uctFreshReg = base)
    (hcount : σ uctCountReg = c) (hseen : σ uctSeenReg = s)
    (hrem : σ uctRemainingReg = 0) (hb : σ uctBoundReg = bound)
    (hbelow : 25 ≤ addr)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ bound ∧ ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbits : BitsFrom σ addr
      ((clauses.map (encodeList encodeLiteral)).flatten ++ rest)) :
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctCursorReg =
        addr + (clauses.map (encodeList encodeLiteral)).flatten.length ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctOuterReg = 0 ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctRemainingReg = 0 ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctMaxReg = cnfLiteralVarMaxStat m clauses ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctFreshReg = cnfFreshBaseStat base clauses ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctCountReg = c + cnfThreeCountStat clauses ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctSeenReg = cnfSeenStat s clauses ∧
    loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ uctBoundReg = bound ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg →
      loopEval
          (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
            uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
            uctBoundReg uctSeenReg)
          clauses.length σ r = σ r) := by
  induction clauses generalizing addr m base c s σ with
  | nil =>
      simp [houter, hc, hmax, hbase, hcount, hseen, hrem, hb, cnfLiteralVarMaxStat,
        cnfFreshBaseStat, cnfThreeCountStat, cnfSeenStat]
  | cons ls restClauses ih =>
      have hshape :
          ((ls :: restClauses).map (encodeList encodeLiteral)).flatten ++ rest =
            encodeList encodeLiteral ls ++
              ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
        simp
      rw [hshape] at hbits
      obtain ⟨hheadBits, htailBits0⟩ := bitsFrom_append σ addr
        (encodeList encodeLiteral ls)
        ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) hbits
      have houter' : σ uctOuterReg = restClauses.length + 1 := by
        simpa using houter
      have hheadBound := hbounds ls (by simp)
      obtain ⟨hcur1, houter1, hrem1, hmax1, hlen1, hbase1, hcount1, hseen1,
          hbound1, hframe1⟩ :=
        decodeCNFStepAtSeen_uct_eval bound addr m base c restClauses.length s ls
          ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) σ
          hbelow houter' hc hmax hbase hcount hseen hb hheadBound.1 hheadBound.2
          hbits
      set σ1 :=
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg).eval σ with hσ1
      have htailBits :
          BitsFrom σ1 (addr + (encodeList encodeLiteral ls).length)
            ((restClauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
        intro i hi
        have hfr := hframe1 (addr + (encodeList encodeLiteral ls).length + i)
          (by simp [uctCursorReg]; omega) (by simp [uctPolReg]; omega)
          (by simp [uctVarReg]; omega) (by simp [uctDoneReg]; omega)
          (by simp [uctOuterReg]; omega) (by simp [uctRemainingReg]; omega)
          (by simp [uctMaxReg]; omega) (by simp [uctLengthReg]; omega)
          (by simp [uctFreshReg]; omega) (by simp [uctCountReg]; omega)
          (by simp [uctTmpReg]; omega) (by simp [uctSeenReg]; omega)
        exact hfr.trans (htailBits0 i hi)
      have hbelowTail : 25 ≤ addr + (encodeList encodeLiteral ls).length := by omega
      have hboundsTail : ∀ d ∈ restClauses,
          d.length + 1 ≤ bound ∧ ∀ l ∈ d, l.var + 1 ≤ bound := by
        intro d hd
        exact hbounds d (List.mem_cons_of_mem ls hd)
      obtain ⟨hcurTail, houterTail, hremTail, hmaxTail, hbaseTail, hcountTail,
          hseenTail, hboundTail, hframeTail⟩ :=
        ih (addr + (encodeList encodeLiteral ls).length)
          (max m (literalVarMax ls))
          (base + clauseFreshIncByLength ls.length)
          (c + clauseThreeCountByLength ls.length)
          (if ls.length = 0 then s else 1) σ1
          houter1 hcur1 hmax1 hbase1 hcount1 hseen1 hrem1 hbound1 hbelowTail
          hboundsTail htailBits
      rw [show (ls :: restClauses).length = restClauses.length + 1 by simp,
        loopEval_succ, ← hσ1]
      refine ⟨?_, houterTail, hremTail, ?_, ?_, ?_, ?_, hboundTail, ?_⟩
      · rw [hcurTail]; simp [List.length_append]; omega
      · rw [hmaxTail]; simp [cnfLiteralVarMaxStat]
      · rw [hbaseTail]; simp [cnfFreshBaseStat, clauseFreshBaseStat_eq_length]
      · rw [hcountTail]
        simp [cnfThreeCountStat, clauseThreeCountStat_eq_length, Nat.add_assoc]
      · rw [hseenTail]; simp [cnfSeenStat]
      · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        exact (hframeTail r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12).trans
          (hframe1 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)

lemma decodeCNFProgramAtSeen_uct_append
    (bound : ℕ) (clauses : List (List Literal)) (rest : Bits)
    (addr m base c s : ℕ) (τ : Store)
    (hbound : clauses.length + 1 ≤ bound) (hbelow : 25 ≤ addr)
    (hc : τ uctCursorReg = addr) (hrem : τ uctRemainingReg = 0)
    (hmax : τ uctMaxReg = m) (hbase : τ uctFreshReg = base)
    (hcount : τ uctCountReg = c) (hseen : τ uctSeenReg = s)
    (hb : τ uctBoundReg = bound)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ bound ∧ ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbits : BitsFrom τ addr
      (encodeList (encodeList encodeLiteral) clauses ++ rest)) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctMaxReg = cnfLiteralVarMaxStat m clauses ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctFreshReg = cnfFreshBaseStat base clauses ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctCountReg = c + cnfThreeCountStat clauses ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctSeenReg = cnfSeenStat s clauses ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctRemainingReg = 0 ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctOuterReg = 0 ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ uctBoundReg = bound ∧
    (∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg →
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ r = τ r) := by
  have hshape :
      encodeList (encodeList encodeLiteral) clauses ++ rest =
        encodeNat clauses.length ++
          ((clauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
    simp [encodeList, List.append_assoc]
  have hbits' := hbits
  rw [hshape] at hbits'
  obtain ⟨_, htailBits⟩ := bitsFrom_append τ addr (encodeNat clauses.length)
    ((clauses.map (encodeList encodeLiteral)).flatten ++ rest) hbits'
  have houterBelow :
      uctCursorReg < addr ∧ uctOuterReg < addr ∧ uctDoneReg < addr := by
    simp [uctCursorReg, uctOuterReg, uctDoneReg]; omega
  obtain ⟨hcur0, houter0, hdone0, hframe0⟩ :=
    decode_cnf_outer_decode uctCursorReg uctOuterReg uctDoneReg bound addr clauses rest τ
      (by decide) (by decide) (by decide) houterBelow hc hbound hbits
  set σ2 := (decodeNatProgram uctCursorReg uctOuterReg uctDoneReg bound).eval
    ((Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval τ)) with hσ2def
  have hAt :
      (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval
        ((Program.assign uctOuterReg (.const 0)).eval
          ((Program.assign uctDoneReg (.const 0)).eval τ)) = σ2 := by
    have hb2 : ((Program.assign uctOuterReg (.const 0)).eval
        ((Program.assign uctDoneReg (.const 0)).eval τ)) uctBoundReg = bound := by
      simp [eval_assign, Expr.eval]
      rw [writeReg_diff _ uctOuterReg 0 uctBoundReg (by decide),
        writeReg_diff τ uctDoneReg 0 uctBoundReg (by decide), hb]
    exact decodeNatProgramAt_eq uctCursorReg uctOuterReg uctDoneReg uctBoundReg
      bound _ hb2
  have hσ2rem : σ2 uctRemainingReg = 0 :=
    (hframe0 uctRemainingReg (by decide) (by decide) (by decide)).trans hrem
  have hσ2max : σ2 uctMaxReg = m :=
    (hframe0 uctMaxReg (by decide) (by decide) (by decide)).trans hmax
  have hσ2base : σ2 uctFreshReg = base :=
    (hframe0 uctFreshReg (by decide) (by decide) (by decide)).trans hbase
  have hσ2count : σ2 uctCountReg = c :=
    (hframe0 uctCountReg (by decide) (by decide) (by decide)).trans hcount
  have hσ2seen : σ2 uctSeenReg = s :=
    (hframe0 uctSeenReg (by decide) (by decide) (by decide)).trans hseen
  have hσ2bound : σ2 uctBoundReg = bound :=
    (hframe0 uctBoundReg (by decide) (by decide) (by decide)).trans hb
  have htailBits2 :
      BitsFrom σ2 (addr + clauses.length + 1)
        ((clauses.map (encodeList encodeLiteral)).flatten ++ rest) := by
    intro i hi
    have hfr := hframe0 (addr + clauses.length + 1 + i)
      (by simp [uctCursorReg]; omega) (by simp [uctOuterReg]; omega)
      (by simp [uctDoneReg]; omega)
    have hi' : addr + clauses.length + 1 + i =
        addr + (encodeNat clauses.length).length + i := by
      simp [encodeNat_length]; omega
    exact hfr.trans (hi' ▸ htailBits i hi)
  obtain ⟨_, hloopOuter, hloopRem, hloopMax, hloopFresh, hloopCount, hloopSeen,
      hloopBound, hloopFrame⟩ :=
    decodeCNFStepAtSeen_seen_loop_uct_eval bound clauses rest
      (addr + clauses.length + 1) m base c s σ2 houter0 hcur0 hσ2max
      hσ2base hσ2count hσ2seen hσ2rem hσ2bound (by omega) hbounds htailBits2
  have hprog :
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval τ =
      loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg)
        clauses.length σ2 := by
    unfold decodeCNFProgramAtSeen
    rw [eval_seq, eval_seq, eval_seq, eval_forN]
    simp only [Expr.eval]
    rw [hAt]
    simp [houter0]
  rw [hprog]
  refine ⟨hloopMax, hloopFresh, hloopCount, hloopSeen, hloopRem, hloopOuter, hloopBound, ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact (hloopFrame r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12).trans
    (hframe0 r h1 h5 h4)

lemma decodeCNFProgramAtSeen_uct_frame_ge
    (bound : ℕ) (clauses : List (List Literal)) (rest : Bits)
    (addr m base c s : ℕ) (τ : Store)
    (hbound : clauses.length + 1 ≤ bound) (hbelow : 25 ≤ addr)
    (hc : τ uctCursorReg = addr) (hrem : τ uctRemainingReg = 0)
    (hmax : τ uctMaxReg = m) (hbase : τ uctFreshReg = base)
    (hcount : τ uctCountReg = c) (hseen : τ uctSeenReg = s)
    (hb : τ uctBoundReg = bound)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ bound ∧ ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hbits : BitsFrom τ addr
      (encodeList (encodeList encodeLiteral) clauses ++ rest))
    (r : ℕ) (hr : 25 ≤ r) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval τ r = τ r :=
  (decodeCNFProgramAtSeen_uct_append bound clauses rest addr m base c s τ
      hbound hbelow hc hrem hmax hbase hcount hseen hb hbounds hbits).2.2.2.2.2.2.2 r
    (by simp [uctCursorReg]; omega) (by simp [uctPolReg]; omega)
    (by simp [uctVarReg]; omega) (by simp [uctDoneReg]; omega)
    (by simp [uctOuterReg]; omega) (by simp [uctRemainingReg]; omega)
    (by simp [uctMaxReg]; omega) (by simp [uctLengthReg]; omega)
    (by simp [uctFreshReg]; omega) (by simp [uctCountReg]; omega)
    (by simp [uctTmpReg]; omega) (by simp [uctSeenReg]; omega)

end NPComplete.CookLevin

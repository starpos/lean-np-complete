module

public import NPComplete.CookLevin.NatParser.Foundation
public import NPComplete.CookLevin.Verifier.SATBool

/-!
`sat_inNP`'s machine half needs a RAM evaluator for `cnfSatBool` against the
certificate extracted by `depairProg`: given a decoded literal (variable, polarity)
and the certificate's assignment bit for that variable, compute the literal's
Boolean value and OR it into a clause accumulator.  `decodeLiteralValueProgram`
(`NatParser/Foundation.lean`) already decodes one literal; this module adds
the certificate read and the two-instruction value/accumulate step, reusing
the decoder rather than re-deriving literal decoding.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip)
open NPComplete.BitEncoding (Bits encodeNat_length)
open NPComplete.SAT (Literal encodeLiteral)

/-- Read the assignment bit for variable `varReg`: the certificate cell at
    `wBaseReg + varReg`. -/
def readAssignBitProg (wBaseReg varReg bitReg : ℕ) : Program :=
  .assign bitReg (.regInd (.add (.reg wBaseReg) (.reg varReg)))

/-- The literal's Boolean value as a `0`/`1` register: `pol = 0` (positive)
    keeps the assignment bit; `pol ≠ 0` (negative) flips it. -/
def literalValueProg (polReg bitReg valReg : ℕ) : Program :=
  .ifNZ (.reg polReg) (.assign valReg (.sub (.const 1) (.reg bitReg)))
    (.assign valReg (.reg bitReg))

/-- OR a literal's value into the clause accumulator: once `satReg` is `1` it
    stays `1`; a nonzero `valReg` sets it. -/
def orIntoProg (valReg satReg : ℕ) : Program :=
  .ifNZ (.reg valReg) (.assign satReg (.const 1)) .skip

lemma readAssignBitProg_eval (wBaseReg varReg bitReg : ℕ) (σ : Store) :
    (readAssignBitProg wBaseReg varReg bitReg).eval σ bitReg =
      σ (σ wBaseReg + σ varReg) := by
  unfold readAssignBitProg
  simp [eval_assign, Expr.eval, writeReg_same]

lemma readAssignBitProg_frame (wBaseReg varReg bitReg r : ℕ) (σ : Store)
    (hr : r ≠ bitReg) : (readAssignBitProg wBaseReg varReg bitReg).eval σ r = σ r := by
  unfold readAssignBitProg
  simp [eval_assign, Expr.eval, writeReg_diff σ bitReg _ r hr]

lemma literalValueProg_eval_pos (v : ℕ) (polReg bitReg valReg : ℕ) (σ : Store) (wBit : Bool)
    (hpol : σ polReg = 0) (hbit : σ bitReg = if wBit then 1 else 0) :
    (literalValueProg polReg bitReg valReg).eval σ valReg =
      (if (Literal.pos v).eval (fun _ => wBit) then 1 else 0) := by
  unfold literalValueProg
  simp only [Literal.eval, eval_ifNZ, Expr.eval, hpol]
  cases wBit <;> simp [eval_assign, Expr.eval, writeReg_same, hbit]

lemma literalValueProg_eval_neg (v : ℕ) (polReg bitReg valReg : ℕ) (σ : Store) (wBit : Bool)
    (hpol : σ polReg = 1) (hbit : σ bitReg = if wBit then 1 else 0) :
    (literalValueProg polReg bitReg valReg).eval σ valReg =
      (if (Literal.neg v).eval (fun _ => wBit) then 1 else 0) := by
  unfold literalValueProg
  simp only [Literal.eval, eval_ifNZ, Expr.eval, hpol]
  simp [eval_assign, Expr.eval, writeReg_same, hbit]
  cases wBit <;> simp

lemma literalValueProg_frame (polReg bitReg valReg r : ℕ) (σ : Store) (hr : r ≠ valReg) :
    (literalValueProg polReg bitReg valReg).eval σ r = σ r := by
  unfold literalValueProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases hpol : σ polReg = 0
  · simp [eval_assign, Expr.eval, hpol, writeReg_diff σ valReg _ r hr]
  · simp [eval_assign, Expr.eval, hpol, writeReg_diff σ valReg _ r hr]

lemma orIntoProg_eval (valReg satReg : ℕ) (σ : Store) :
    (orIntoProg valReg satReg).eval σ satReg =
      (if σ valReg ≠ 0 then 1 else σ satReg) := by
  unfold orIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases hval : σ valReg = 0
  · simp [eval_skip, hval]
  · simp [eval_assign, Expr.eval, hval, writeReg_same]

lemma orIntoProg_frame (valReg satReg r : ℕ) (σ : Store) (hr : r ≠ satReg) :
    (orIntoProg valReg satReg).eval σ r = σ r := by
  unfold orIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases hval : σ valReg = 0
  · simp [eval_skip, hval]
  · simp [eval_assign, Expr.eval, hval, writeReg_diff σ satReg 1 r hr]

/-- One step of decoding-and-evaluating a clause's literals: decode the next
    literal (as `decodeLiteralValueProgram` does), read the certificate's
    assignment bit for its variable, compute the literal's Boolean value, and
    OR it into `satReg`.  Mirrors `decodeClauseStep`'s scan/decrement shape,
    swapping the max-tracking accumulator for an OR-accumulator against the
    certificate. -/
def decodeClauseEvalStep
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg bound : ℕ) :
    Program :=
  .ifNZ (.reg remainingReg)
    (.seq (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound)
      <| .seq (.assign remainingReg (.sub (.reg remainingReg) (.const 1)))
          <| .seq (readAssignBitProg wBaseReg varReg bitReg)
            <| .seq (literalValueProg polReg bitReg valReg)
                (orIntoProg valReg satReg))
    .skip

/-- One `decodeClauseEvalStep`, decoding literal `l` at the cursor and folding
    its evaluated Boolean value (against certificate cell `wBase + l.var`)
    into `satReg` via OR: `satReg` becomes `1` if `l.eval τ` is `true` for the
    single-variable snapshot `τ v := wBit`, else unchanged.  Every control
    register must sit strictly below the certificate base `wBase`
    (`hbelowW`), so the decode/scalar-update phases (which only ever touch
    control registers) never alias the certificate cell `wBase + l.var`. -/
lemma decodeClauseEvalStep_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg bound
      addr k s wBase : ℕ) (l : Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)
    (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg)
    (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hrem : σ remainingReg = k + 1) (hsat : σ satReg = s) (hwbase : σ wBaseReg = wBase)
    (hbound : l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest))
    (wBit : Bool) (hwbit : σ (wBase + l.var) = if wBit then 1 else 0) :
    (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg bound).eval σ cursorReg = addr + (encodeLiteral l).length ∧
    (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg bound).eval σ remainingReg = k ∧
    (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
      wBaseReg bound).eval σ satReg =
      (if l.eval (fun _ => wBit) then 1 else s) ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → r ≠ remainingReg →
      r ≠ satReg → r ≠ bitReg → r ≠ valReg →
      (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg
        wBaseReg bound).eval σ r = σ r) := by
  unfold decodeClauseEvalStep
  rw [eval_ifNZ, ite_eq_left (show (Expr.reg remainingReg).eval σ ≠ 0 by simp [Expr.eval, hrem])]
  rw [eval_seq, eval_seq, eval_seq, eval_seq]
  obtain ⟨hcur, hpol, hvar, hdone, hframe⟩ :=
    decodeLiteralValueProgram_correct cursorReg polReg varReg doneReg bound addr l rest σ
      hcp hcv hcd hpv hpd hvd hbelow.1 hbelow.2.1 hbelow.2.2.1 hbelow.2.2.2 hbound hc hbits
  set σ1 := (decodeLiteralValueProgram cursorReg polReg varReg doneReg bound).eval σ with hσ1
  have h1rem : σ1 remainingReg = k + 1 := (hframe remainingReg hrc hrp hrv hrd).trans hrem
  have h1sat : σ1 satReg = s := (hframe satReg hsc hsp hsv hsd).trans hsat
  have h1wbase : σ1 wBaseReg = wBase := (hframe wBaseReg hwc hwp hwv hwd).trans hwbase
  have hwneC : wBase + l.var ≠ cursorReg := by have := hbelowW.1; omega
  have hwneP : wBase + l.var ≠ polReg := by have := hbelowW.2.1; omega
  have hwneV : wBase + l.var ≠ varReg := by have := hbelowW.2.2.1; omega
  have hwneD : wBase + l.var ≠ doneReg := by have := hbelowW.2.2.2.1; omega
  have hwneR : wBase + l.var ≠ remainingReg := by have := hbelowW.2.2.2.2.1; omega
  have hwneS : wBase + l.var ≠ satReg := by have := hbelowW.2.2.2.2.2.1; omega
  have hwneB : wBase + l.var ≠ bitReg := by have := hbelowW.2.2.2.2.2.2.1; omega
  have hwneVal : wBase + l.var ≠ valReg := by have := hbelowW.2.2.2.2.2.2.2; omega
  have h1wbit : σ1 (wBase + l.var) = if wBit then 1 else 0 :=
    (hframe (wBase + l.var) hwneC hwneP hwneV hwneD).trans hwbit
  set σ2 := (Program.assign remainingReg (.sub (.reg remainingReg) (.const 1))).eval σ1 with hσ2
  have h2eq : σ2 = writeReg σ1 remainingReg (σ1 remainingReg - 1) := by
    rw [hσ2]; simp only [eval_assign, Expr.eval]
  have h2rem : σ2 remainingReg = k := by rw [h2eq, writeReg_same, h1rem]; omega
  have h2var : σ2 varReg = σ1 varReg := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ varReg hrv.symm
  have h2pol : σ2 polReg = σ1 polReg := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ polReg hrp.symm
  have h2sat : σ2 satReg = σ1 satReg := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ satReg hsr
  have h2wbase : σ2 wBaseReg = σ1 wBaseReg := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ wBaseReg hwr
  have h2cur : σ2 cursorReg = σ1 cursorReg := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ cursorReg hrc.symm
  have h2wbit : σ2 (wBase + l.var) = σ1 (wBase + l.var) := by
    rw [h2eq]; exact writeReg_diff _ remainingReg _ (wBase + l.var) hwneR
  set σ3 := (readAssignBitProg wBaseReg varReg bitReg).eval σ2 with hσ3
  have h3bit : σ3 bitReg = σ2 (σ2 wBaseReg + σ2 varReg) := by
    rw [hσ3]; exact readAssignBitProg_eval wBaseReg varReg bitReg σ2
  have h3bitval : σ3 bitReg = if wBit then 1 else 0 := by
    rw [h3bit, h2wbase, h1wbase, h2var, hvar, h2wbit, h1wbit]
  have h3pol : σ3 polReg = σ2 polReg := by
    rw [hσ3]; exact readAssignBitProg_frame wBaseReg varReg bitReg polReg σ2 hbp.symm
  have h3sat : σ3 satReg = σ2 satReg := by
    rw [hσ3]; exact readAssignBitProg_frame wBaseReg varReg bitReg satReg σ2 hsb
  have h3cur : σ3 cursorReg = σ2 cursorReg := by
    rw [hσ3]; exact readAssignBitProg_frame wBaseReg varReg bitReg cursorReg σ2 hbc.symm
  have h3rem : σ3 remainingReg = σ2 remainingReg := by
    rw [hσ3]; exact readAssignBitProg_frame wBaseReg varReg bitReg remainingReg σ2 hbr.symm
  set σ4 := (literalValueProg polReg bitReg valReg).eval σ3 with hσ4
  have h4val : σ4 valReg = if l.eval (fun _ => wBit) then 1 else 0 := by
    rw [hσ4]
    cases l with
    | pos v =>
        have hpol0 : σ3 polReg = 0 := by rw [h3pol, h2pol]; exact hpol
        exact literalValueProg_eval_pos v polReg bitReg valReg σ3 wBit hpol0 h3bitval
    | neg v =>
        have hpol1 : σ3 polReg = 1 := by rw [h3pol, h2pol]; exact hpol
        exact literalValueProg_eval_neg v polReg bitReg valReg σ3 wBit hpol1 h3bitval
  have h4sat : σ4 satReg = σ3 satReg := by
    rw [hσ4]; exact literalValueProg_frame polReg bitReg valReg satReg σ3 hsl
  have h4cur : σ4 cursorReg = σ3 cursorReg := by
    rw [hσ4]; exact literalValueProg_frame polReg bitReg valReg cursorReg σ3 hvc.symm
  have h4rem : σ4 remainingReg = σ3 remainingReg := by
    rw [hσ4]; exact literalValueProg_frame polReg bitReg valReg remainingReg σ3 hvr.symm
  set σ5 := (orIntoProg valReg satReg).eval σ4 with hσ5
  have h5sat : σ5 satReg = (if σ4 valReg ≠ 0 then 1 else σ4 satReg) := by
    rw [hσ5]; exact orIntoProg_eval valReg satReg σ4
  have h5cur : σ5 cursorReg = σ4 cursorReg := by
    rw [hσ5]; exact orIntoProg_frame valReg satReg cursorReg σ4 hsc.symm
  have h5rem : σ5 remainingReg = σ4 remainingReg := by
    rw [hσ5]; exact orIntoProg_frame valReg satReg remainingReg σ4 hsr.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h5cur, h4cur, h3cur, h2cur, hcur]
    cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var] <;> omega
  · rw [h5rem, h4rem, h3rem, h2rem]
  · rw [h5sat, h4val]
    cases l.eval (fun _ => wBit) <;> simp [h4sat, h3sat, h2sat, h1sat]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8
    have hf := hframe r h1 h2 h3 h4
    have hg2 : σ2 r = σ1 r := by rw [h2eq]; exact writeReg_diff _ remainingReg _ r h5
    have hg3 : σ3 r = σ2 r := by
      rw [hσ3]; exact readAssignBitProg_frame wBaseReg varReg bitReg r σ2 h7
    have hg4 : σ4 r = σ3 r := by
      rw [hσ4]; exact literalValueProg_frame polReg bitReg valReg r σ3 h8
    have hg5 : σ5 r = σ4 r := by
      rw [hσ5]; exact orIntoProg_frame valReg satReg r σ4 h6
    rw [hg5, hg4, hg3, hg2, hf]

/-- Loop correctness for `decodeClauseEvalStep` over a literal list `ls`: after
    `ls.length` iterations, the cursor has advanced past all of `ls`'s
    encoding, `remainingReg` reaches `0`, and `satReg` holds the `∨`-fold of
    `ls`'s literal evaluations (against the certificate `w`) seeded at the
    initial `satReg` value `s ∈ {0, 1}`.  Every control register must sit
    strictly below the certificate base `wBase`, which itself must sit below
    the bit region `addr` (so `decodeLiteralValueProgram`'s scan and the
    certificate read never alias). -/
lemma decode_clause_eval_loop_eval
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg bound
      addr s wBase : ℕ) (ls : List Literal) (rest : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hrc : remainingReg ≠ cursorReg) (hrp : remainingReg ≠ polReg)
    (hrv : remainingReg ≠ varReg) (hrd : remainingReg ≠ doneReg)
    (hbc : bitReg ≠ cursorReg) (hbp : bitReg ≠ polReg)
    (hbr : bitReg ≠ remainingReg)
    (hvc : valReg ≠ cursorReg) (hvr : valReg ≠ remainingReg)
    (hwc : wBaseReg ≠ cursorReg) (hwp : wBaseReg ≠ polReg) (hwv : wBaseReg ≠ varReg)
    (hwd : wBaseReg ≠ doneReg) (hwr : wBaseReg ≠ remainingReg) (hwb : wBaseReg ≠ bitReg)
    (hwl : wBaseReg ≠ valReg)
    (hsc : satReg ≠ cursorReg) (hsp : satReg ≠ polReg) (hsv : satReg ≠ varReg)
    (hsd : satReg ≠ doneReg) (hsr : satReg ≠ remainingReg) (hsb : satReg ≠ bitReg)
    (hsl : satReg ≠ valReg) (hsw : satReg ≠ wBaseReg)
    (hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase)
    (hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr)
    (hWA : wBase < addr)
    (hrem : σ remainingReg = ls.length) (hsat : σ satReg = s) (hsatBool : s = 0 ∨ s = 1)
    (hwbase : σ wBaseReg = wBase)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr ((ls.map encodeLiteral).flatten ++ rest))
    (w : List Bool) (hwbits : ∀ l ∈ ls, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (loopEval (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg bound) ls.length σ) cursorReg = addr + (ls.map encodeLiteral).flatten.length ∧
    (loopEval (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg bound) ls.length σ) remainingReg = 0 ∧
    (loopEval (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg bound) ls.length σ) satReg =
      (if s = 1 ∨ ∃ l ∈ ls, l.eval (decodeAssignment w) = true then 1 else 0) ∧
    (∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg → r ≠ remainingReg →
      r ≠ satReg → r ≠ bitReg → r ≠ valReg →
      (loopEval (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg bound) ls.length σ) r = σ r) := by
  induction ls generalizing addr s σ with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero, loopEval]
      refine ⟨hc, hrem, ?_, fun r _ _ _ _ _ _ _ _ => trivial⟩
      rcases hsatBool with h0 | h1
      · simp [hsat, h0]
      · simp [hsat, h1]
  | cons l ls ih =>
      have hshape : ((l :: ls).map encodeLiteral).flatten ++ rest =
          encodeLiteral l ++ ((ls.map encodeLiteral).flatten ++ rest) := by simp
      rw [hshape] at hbits
      obtain ⟨hhead, htail⟩ := bitsFrom_append σ addr (encodeLiteral l)
        ((ls.map encodeLiteral).flatten ++ rest) hbits
      have hrem' : σ remainingReg = ls.length + 1 := by simpa using hrem
      have hbound_l : l.var + 1 ≤ bound := hbound l (by simp)
      obtain ⟨hcur1, hrem1, hsat1, hframe1⟩ :=
        decodeClauseEvalStep_eval cursorReg polReg varReg doneReg remainingReg satReg bitReg
          valReg wBaseReg bound addr ls.length s wBase l
          ((ls.map encodeLiteral).flatten ++ rest) σ
          hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
          hvc hvr hwc hwp hwv hwd hwr
          hsc hsp hsv hsd hsr hsb hsl
          ⟨hbelow.1, hbelow.2.1, hbelow.2.2.1, hbelow.2.2.2.1⟩ hbelowW hrem' hsat hwbase
          hbound_l hc hbits (w.getD l.var false) (hwbits l (by simp))
      set σ1 := (decodeClauseEvalStep cursorReg polReg varReg doneReg remainingReg satReg bitReg
        valReg wBaseReg bound).eval σ with hσ1def
      have hlen : (encodeLiteral l).length = l.var + 2 := by
        cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
      set addr' := addr + (encodeLiteral l).length with haddr'
      have hc1 : σ1 cursorReg = addr' := hcur1
      have hrem1' : σ1 remainingReg = ls.length := hrem1
      have heq_snapshot : l.eval (fun _ => w.getD l.var false) = l.eval (decodeAssignment w) := by
        cases l with
        | pos v => rfl
        | neg v => rfl
      have hs1v : σ1 satReg = 0 ∨ σ1 satReg = 1 := by
        rw [hsat1]
        cases l.eval (fun _ => w.getD l.var false) with
        | true => right; simp
        | false => simpa using hsatBool
      have hbelow1 : cursorReg < addr' ∧ polReg < addr' ∧ varReg < addr' ∧ doneReg < addr' ∧
          remainingReg < addr' ∧ satReg < addr' ∧ bitReg < addr' ∧ valReg < addr' ∧
          wBaseReg < addr' := by
        rw [haddr']; omega
      have hWA1 : wBase < addr' := by rw [haddr']; omega
      have hbits1 : BitsFrom σ1 addr' ((ls.map encodeLiteral).flatten ++ rest) := by
        intro i hi
        have hfr := hframe1 (addr' + i)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [hfr]
        exact htail i hi
      have hwbase1 : σ1 wBaseReg = wBase :=
        (hframe1 wBaseReg hwc hwp hwv hwd hwr hsw.symm hwb hwl).trans hwbase
      have hwbits1 : ∀ l' ∈ ls, σ1 (wBase + l'.var) = if w.getD l'.var false then 1 else 0 := by
        intro l' hl'
        have hne : wBase + l'.var ≠ cursorReg := by have := hbelowW.1; omega
        have hne2 : wBase + l'.var ≠ polReg := by have := hbelowW.2.1; omega
        have hne3 : wBase + l'.var ≠ varReg := by have := hbelowW.2.2.1; omega
        have hne4 : wBase + l'.var ≠ doneReg := by have := hbelowW.2.2.2.1; omega
        have hne5 : wBase + l'.var ≠ remainingReg := by have := hbelowW.2.2.2.2.1; omega
        have hne6 : wBase + l'.var ≠ satReg := by have := hbelowW.2.2.2.2.2.1; omega
        have hne7 : wBase + l'.var ≠ bitReg := by have := hbelowW.2.2.2.2.2.2.1; omega
        have hne8 : wBase + l'.var ≠ valReg := by have := hbelowW.2.2.2.2.2.2.2; omega
        rw [hframe1 (wBase + l'.var) hne hne2 hne3 hne4 hne5 hne6 hne7 hne8]
        exact hwbits l' (by simp [hl'])
      have hbound_ls : ∀ l' ∈ ls, l'.var + 1 ≤ bound := fun l' hl' => hbound l' (by simp [hl'])
      obtain ⟨hcurTail, hremTail, hsatTail, hframeTail⟩ :=
        ih addr' (σ1 satReg) σ1 hbelow1 hWA1 hrem1' rfl hs1v hwbase1
          hbound_ls hc1 hbits1 hwbits1
      rw [show (l :: ls).length = ls.length + 1 by simp, loopEval_succ]
      rw [← hσ1def]
      refine ⟨?_, hremTail, ?_, ?_⟩
      · rw [hcurTail, haddr']
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        omega
      · rw [hsatTail, hsat1, heq_snapshot]
        simp only [List.exists_mem_cons_iff]
        cases hl : l.eval (decodeAssignment w) with
        | true => simp
        | false => simp
      · intro r h1 h2 h3 h4 h5 h6 h7 h8
        exact (hframeTail r h1 h2 h3 h4 h5 h6 h7 h8).trans (hframe1 r h1 h2 h3 h4 h5 h6 h7 h8)

end NPComplete.CookLevin

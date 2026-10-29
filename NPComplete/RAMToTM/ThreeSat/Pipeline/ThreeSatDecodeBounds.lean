module

public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatDecodePhase
public import NPComplete.CookLevin.UniformPackaging.DecoderBounds

/-! The runtime-sized decoder is shared across reductions, so its memory-safety bounds belong with
    its library program definitions rather than in a downstream construction. -/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.SAT
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (encodeNat encodeNat_length encodeList)
open NPComplete.CookLevin (decodeUnaryStep_programBoundedIn)

lemma decodeUnaryStep_loop_register_bounds (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg)
    (n bound addr c0 B : ℕ) (τ : Store)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : τ cursorReg = addr) (hk : τ countReg = c0) (hd : τ doneReg = 0)
    (hbits : BitsFrom τ addr (encodeNat n))
    (hcursor : addr + n + 2 ≤ B) (hcount : c0 + n + 1 ≤ B) :
    ∀ m < bound,
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) cursorReg + 1 ≤ B ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) countReg + 1 ≤ B := by
  obtain ⟨hfc, hfk, hfd, _⟩ := decode_unary_loop_correct cursorReg countReg doneReg
    hcc hcd hkd n addr c0 τ hca hka hda hc hk hd hbits
  intro m hm
  by_cases hsmall : m < n + 1
  · have hcur := loopEval_decodeUnaryStep_cursor_le cursorReg countReg doneReg hcc hcd m τ
    have hcnt := loopEval_decodeUnaryStep_count_le cursorReg countReg doneReg hcc hkd m τ
    omega
  · have hsplit : m = (n + 1) + (m - (n + 1)) := by omega
    rw [hsplit, loopEval_add]
    rw [loopEval_decodeUnaryStep_done cursorReg countReg doneReg
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) τ)
      (m - (n + 1)) (by rw [hfd]; decide)]
    constructor
    · rw [hfc]
      omega
    · rw [hfk]
      omega

lemma decodeUnaryStep_loop_register_bounds_unconditional (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg)
    (bound B : ℕ) (τ : Store)
    (hcursor : τ cursorReg + bound + 1 ≤ B)
    (hcount : τ countReg + bound + 1 ≤ B) :
    ∀ m < bound,
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) cursorReg + 1 ≤ B ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) countReg + 1 ≤ B := by
  intro m hm
  have hcur := loopEval_decodeUnaryStep_cursor_le cursorReg countReg doneReg hcc hcd m τ
  have hcnt := loopEval_decodeUnaryStep_count_le cursorReg countReg doneReg hcc hkd m τ
  omega

lemma decodeUnaryProgAt_programBoundedIn
    (cursorReg countReg doneReg B : ℕ) (boundE : Expr) (τ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hboundE : ExprBoundedIn B τ boundE)
    (hregs : cursorReg ≤ B ∧ countReg ≤ B ∧ doneReg ≤ B)
    (hsteps : ∀ m < boundE.eval τ,
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) cursorReg + 1 ≤ B ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) countReg + 1 ≤ B) :
    ProgramBoundedIn B τ (decodeUnaryProgAt cursorReg countReg doneReg boundE) := by
  unfold decodeUnaryProgAt
  refine ⟨hboundE, ?_⟩
  intro m hm
  exact decodeUnaryStep_programBoundedIn B cursorReg countReg doneReg
    (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ)
    hcc hcd hregs (hsteps m hm).1 (hsteps m hm).2

lemma readBitAdvanceProg_programBoundedIn (cursorReg outReg B : ℕ) (τ : Store)
    (hco : cursorReg ≠ outReg) (hregs : cursorReg ≤ B ∧ outReg ≤ B)
    (hcursor : τ cursorReg + 1 ≤ B) :
    ProgramBoundedIn B τ (readBitAdvanceProg cursorReg outReg) := by
  simp [readBitAdvanceProg, ProgramBoundedIn, ExprBoundedIn, Expr.eval,
    hco, writeReg]
  rcases hregs with ⟨hcur, hout⟩
  omega

lemma decodeThreeCNFHeaderProgAt_first_pass
    (cursorReg numVarsReg doneReg B N C numVars count : ℕ) (τ : Store)
    (hdist : cursorReg ≠ numVarsReg ∧ cursorReg ≠ doneReg ∧ numVarsReg ≠ doneReg)
    (hbelow : cursorReg < C ∧ numVarsReg < C ∧ doneReg < C)
    (hzero : 0 ≠ cursorReg ∧ 0 ≠ numVarsReg ∧ 0 ≠ doneReg)
    (h0 : τ 0 = N) (hc : τ cursorReg = C)
    (hbits : BitsFrom τ C (encodeNat numVars ++ encodeNat count))
    (hnum : numVars + 1 ≤ N) (hB : C + N + 6 ≤ B) :
    let τ2 := writeReg (writeReg τ numVarsReg 0) doneReg 0
    let decode := decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)
    ProgramBoundedIn B τ2 decode ∧
      decode.eval τ2 cursorReg = C + numVars + 1 ∧
      decode.eval τ2 doneReg = 1 ∧
      decode.eval τ2 0 = N ∧
      BitsFrom (decode.eval τ2) (C + (numVars + 1)) (encodeNat count) := by
  dsimp only
  let τ1 := writeReg τ numVarsReg 0
  let τ2 := writeReg τ1 doneReg 0
  let decode := decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)
  let initProg := Program.seq (Program.assign numVarsReg (.const 0))
    (Program.assign doneReg (.const 0))
  have hInitAvoids : initProg.Avoids (fun r => r = cursorReg ∨ r = 0 ∨ C ≤ r) := by
    simp [initProg, Program.avoids_seq, Program.avoids_assign]
    omega
  have hτ2frame (r : ℕ) (hr : r = cursorReg ∨ r = 0 ∨ C ≤ r) : τ2 r = τ r := by
    have hframe := hInitAvoids.eval_frame τ hr
    simpa [τ2, τ1, initProg, Program.eval, Expr.eval] using hframe
  have hτ20 : τ2 0 = N := by
    rw [hτ2frame 0 (Or.inr (Or.inl rfl)), h0]
  have hτ2c : τ2 cursorReg = C := by
    rw [hτ2frame cursorReg (Or.inl rfl), hc]
  have hτ2n : τ2 numVarsReg = 0 := by
    dsimp [τ2, τ1]
    rw [writeReg_diff _ doneReg _ numVarsReg hdist.2.2, writeReg_same]
  have hτ2d : τ2 doneReg = 0 := by simp [τ2]
  have hbitsSplit := bitsFrom_append τ C (encodeNat numVars) (encodeNat count) hbits
  have hbits1 : BitsFrom τ2 C (encodeNat numVars) := by
    apply bitsFrom_of_eq_on (hb := hbitsSplit.1)
    intro i hi
    exact hτ2frame (C + i) (Or.inr (Or.inr (by omega)))
  have hrest := hbitsSplit.2
  rw [encodeNat_length] at hrest
  have hbitsCount : BitsFrom τ2 (C + (numVars + 1)) (encodeNat count) := by
    apply bitsFrom_of_eq_on (hb := hrest)
    intro i hi
    exact hτ2frame (C + (numVars + 1) + i) (Or.inr (Or.inr (by omega)))
  have hsteps1 : ∀ m < N,
      (loopEval (decodeUnaryStep cursorReg numVarsReg doneReg) m τ2) cursorReg + 1 ≤ B ∧
      (loopEval (decodeUnaryStep cursorReg numVarsReg doneReg) m τ2) numVarsReg + 1 ≤ B := by
    apply decodeUnaryStep_loop_register_bounds cursorReg numVarsReg doneReg
      hdist.1 hdist.2.1 hdist.2.2 numVars N C 0 B τ2
      hbelow.1 hbelow.2.1 hbelow.2.2 hτ2c hτ2n hτ2d hbits1
    · omega
    · omega
  have hregs : cursorReg ≤ B ∧ numVarsReg ≤ B ∧ doneReg ≤ B := by omega
  have hloop1 : ProgramBoundedIn B τ2 decode := by
    apply decodeUnaryProgAt_programBoundedIn cursorReg numVarsReg doneReg B (.reg 0) τ2
      hdist.1 hdist.2.1
    · simp [ExprBoundedIn]
    · exact ⟨by omega, by omega, by omega⟩
    · simpa [Expr.eval, hτ20] using hsteps1
  have hdecode1 := decodeUnaryProgAt_correct cursorReg numVarsReg doneReg
    hdist.1 hdist.2.1 hdist.2.2 numVars N C 0 τ2 (.reg 0)
    (by simp [Expr.eval, hτ20]) hnum hbelow.1 hbelow.2.1 hbelow.2.2
    hτ2c hτ2n hτ2d hbits1
  have hτ3c : decode.eval τ2 cursorReg = C + numVars + 1 := by
    simpa [decode, decodeUnaryProgAt, Expr.eval, hτ20] using hdecode1.1
  have hτ3d : decode.eval τ2 doneReg = 1 := by
    simpa [decode, decodeUnaryProgAt, Expr.eval, hτ20] using hdecode1.2.2.1
  have hbits2 : BitsFrom (decode.eval τ2) (C + (numVars + 1)) (encodeNat count) := by
    apply bitsFrom_of_eq_on (hb := hbitsCount)
    intro i hi
    have hframe := hdecode1.2.2.2
    simpa [decode] using hframe (C + (numVars + 1) + i) (by omega) (by omega) (by omega)
  have hτ30 : (loopEval (decodeUnaryStep cursorReg numVarsReg doneReg) N τ2) 0 = N := by
    calc
      (loopEval (decodeUnaryStep cursorReg numVarsReg doneReg) N τ2) 0 = τ2 0 :=
        loopEval_frame_of_step_frame (decodeUnaryStep cursorReg numVarsReg doneReg) 0
          (fun τ' => decodeUnaryStep_frame cursorReg numVarsReg doneReg 0 τ'
            hzero.1 hzero.2.1 hzero.2.2) N τ2
      _ = N := hτ20
  have hτ30' : decode.eval τ2 0 = N := by
    simpa [decode, decodeUnaryProgAt, Expr.eval, hτ20] using hτ30
  exact ⟨hloop1, hτ3c, hτ3d, hτ30', hbits2⟩

lemma decodeThreeCNFHeaderProgAt_second_pass
    (cursorReg countReg doneReg B N C numVars count : ℕ) (τ3 : Store)
    (hdist : cursorReg ≠ countReg ∧ cursorReg ≠ doneReg ∧ countReg ≠ doneReg)
    (hbelow : cursorReg < C ∧ countReg < C ∧ doneReg < C)
    (hzero : 0 ≠ cursorReg ∧ 0 ≠ countReg ∧ 0 ≠ doneReg)
    (hτ3c : τ3 cursorReg = C + numVars + 1)
    (hτ30 : τ3 0 = N)
    (hbits2 : BitsFrom τ3 (C + (numVars + 1)) (encodeNat count))
    (hshape : C + numVars + count + 3 ≤ B) :
    let τ4 := writeReg τ3 countReg 0
    let τ5 := writeReg τ4 doneReg 0
    ProgramBoundedIn B τ5 (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0)) ∧
      τ5 cursorReg = C + numVars + 1 ∧
      τ5 countReg = 0 ∧
      τ5 doneReg = 0 ∧
      τ5 0 = N ∧
      BitsFrom τ5 (C + (numVars + 1)) (encodeNat count) := by
  dsimp only
  let τ4 := writeReg τ3 countReg 0
  let τ5 := writeReg τ4 doneReg 0
  let resetProg := Program.seq (Program.assign countReg (.const 0))
    (Program.assign doneReg (.const 0))
  have hResetAvoids : resetProg.Avoids
      (fun r => r = cursorReg ∨ r = 0 ∨ C + (numVars + 1) ≤ r) := by
    simp [resetProg, Program.avoids_seq, Program.avoids_assign]
    omega
  have hτ5frame (r : ℕ)
      (hr : r = cursorReg ∨ r = 0 ∨ C + (numVars + 1) ≤ r) : τ5 r = τ3 r := by
    have hframe := hResetAvoids.eval_frame τ3 hr
    simpa [τ5, τ4, resetProg, Program.eval, Expr.eval] using hframe
  have hτ5c : τ5 cursorReg = C + numVars + 1 := by
    rw [hτ5frame cursorReg (Or.inl rfl), hτ3c]
  have hτ5k : τ5 countReg = 0 := by
    dsimp [τ5, τ4]
    rw [writeReg_diff _ doneReg _ countReg hdist.2.2, writeReg_same]
  have hτ5d : τ5 doneReg = 0 := by simp [τ5]
  have hτ50 : τ5 0 = N := by
    rw [hτ5frame 0 (Or.inr (Or.inl rfl)), hτ30]
  have hbits5 : BitsFrom τ5 (C + (numVars + 1)) (encodeNat count) := by
    apply bitsFrom_of_eq_on (hb := hbits2)
    intro i hi
    exact hτ5frame (C + (numVars + 1) + i) (Or.inr (Or.inr (by omega)))
  have hsteps2 : ∀ m < N,
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ5) cursorReg + 1 ≤ B ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ5) countReg + 1 ≤ B := by
    apply decodeUnaryStep_loop_register_bounds cursorReg countReg doneReg
      hdist.1 hdist.2.1 hdist.2.2 count N (C + numVars + 1) 0 B τ5
      (by omega) (by omega) (by omega) hτ5c hτ5k hτ5d hbits5
    · omega
    · omega
  have hregs : cursorReg ≤ B ∧ countReg ≤ B ∧ doneReg ≤ B := by omega
  have hloop2 : ProgramBoundedIn B τ5
      (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0)) := by
    apply decodeUnaryProgAt_programBoundedIn cursorReg countReg doneReg B (.reg 0) τ5
      hdist.1 hdist.2.1
    · simp [ExprBoundedIn]
    · exact ⟨by omega, by omega, by omega⟩
    · simpa [Expr.eval, hτ50] using hsteps2
  exact ⟨hloop2, hτ5c, hτ5k, hτ5d, hτ50, hbits5⟩

lemma decodeThreeCNFHeaderProgAt_programBoundedIn
    (cursorReg numVarsReg countReg doneReg B N C numVars count : ℕ) (τ : Store)
    (hregs : cursorReg ≤ B ∧ numVarsReg ≤ B ∧ countReg ≤ B ∧ doneReg ≤ B)
    (hdist : cursorReg ≠ numVarsReg ∧ cursorReg ≠ countReg ∧ cursorReg ≠ doneReg ∧
      numVarsReg ≠ countReg ∧ numVarsReg ≠ doneReg ∧ countReg ≠ doneReg)
    (hbelow : cursorReg < C ∧ numVarsReg < C ∧ countReg < C ∧ doneReg < C)
    (hzero : 0 ≠ cursorReg ∧ 0 ≠ numVarsReg ∧ 0 ≠ countReg ∧ 0 ≠ doneReg)
    (h0 : τ 0 = N) (hc : τ cursorReg = C)
    (hbits : BitsFrom τ C (encodeNat numVars ++ encodeNat count))
    (hnum : numVars + 1 ≤ N) (hB : C + N + 6 ≤ B)
    (hshape : C + numVars + count + 3 ≤ B) :
    ProgramBoundedIn B τ
      (decodeThreeCNFHeaderProgAt cursorReg numVarsReg countReg doneReg (.reg 0) (.reg 0)) := by
  let τ1 := writeReg τ numVarsReg 0
  let τ2 := writeReg τ1 doneReg 0
  let τ3 := (decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)).eval τ2
  let τ4 := writeReg τ3 countReg 0
  let τ5 := writeReg τ4 doneReg 0
  have hfirst := decodeThreeCNFHeaderProgAt_first_pass
    cursorReg numVarsReg doneReg B N C numVars count τ
    ⟨hdist.1, hdist.2.2.1, hdist.2.2.2.2.1⟩
    ⟨hbelow.1, hbelow.2.1, hbelow.2.2.2⟩
    ⟨hzero.1, hzero.2.1, hzero.2.2.2⟩ h0 hc hbits hnum hB
  rcases hfirst with ⟨hloop1, hτ3c, _, hτ30, hbits2⟩
  have hsecond := decodeThreeCNFHeaderProgAt_second_pass
    cursorReg countReg doneReg B N C numVars count τ3
    ⟨hdist.2.1, hdist.2.2.1, hdist.2.2.2.2.2⟩
    ⟨hbelow.1, hbelow.2.2.1, hbelow.2.2.2⟩
    ⟨hzero.1, hzero.2.2.1, hzero.2.2.2⟩ hτ3c hτ30 hbits2 hshape
  rcases hsecond with ⟨hloop2, _, _, _, _, _⟩
  have hp1 : ProgramBoundedIn B τ (.assign numVarsReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hp2 : ProgramBoundedIn B τ1 (.assign doneReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hp3 : ProgramBoundedIn B τ2
      (decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)) := hloop1
  have hp4 : ProgramBoundedIn B τ3 (.assign countReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hp5 : ProgramBoundedIn B τ4 (.assign doneReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hp4' : ProgramBoundedIn B
      ((decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)).eval τ2)
      (Program.assign countReg (.const 0)) := by
    simpa [τ3] using hp4
  have hp5' : ProgramBoundedIn B
      ((Program.assign countReg (.const 0)).eval
        ((decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)).eval τ2))
      (Program.assign doneReg (.const 0)) := by
    simpa [τ4, τ3, Program.eval, Expr.eval] using hp5
  have hloop2' : ProgramBoundedIn B
      ((Program.assign doneReg (.const 0)).eval
        ((Program.assign countReg (.const 0)).eval
          ((decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0)).eval τ2)))
      (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0)) := by
    simpa [τ5, τ4, τ3, Program.eval, Expr.eval] using hloop2
  unfold decodeThreeCNFHeaderProgAt
  change ProgramBoundedIn B τ (Program.assign numVarsReg (.const 0)) ∧
    ProgramBoundedIn B ((Program.assign numVarsReg (.const 0)).eval τ)
      (Program.seq (Program.assign doneReg (.const 0))
        (Program.seq (decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0))
          (Program.seq (Program.assign countReg (.const 0))
            (Program.seq (Program.assign doneReg (.const 0))
              (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0))))) )
  refine ⟨hp1, ?_⟩
  change ProgramBoundedIn B ((Program.assign numVarsReg (.const 0)).eval τ)
      (Program.assign doneReg (.const 0)) ∧
    ProgramBoundedIn B ((Program.assign doneReg (.const 0)).eval
      ((Program.assign numVarsReg (.const 0)).eval τ))
      (Program.seq (decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0))
        (Program.seq (Program.assign countReg (.const 0))
          (Program.seq (Program.assign doneReg (.const 0))
            (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0)))))
  have htail : ProgramBoundedIn B τ1 (Program.assign doneReg (.const 0)) ∧
    ProgramBoundedIn B τ2
      (Program.seq (decodeUnaryProgAt cursorReg numVarsReg doneReg (.reg 0))
        (Program.seq (Program.assign countReg (.const 0))
          (Program.seq (Program.assign doneReg (.const 0))
            (decodeUnaryProgAt cursorReg countReg doneReg (.reg 0))))) :=
    ⟨hp2, ⟨hp3, ⟨hp4', ⟨hp5', hloop2'⟩⟩⟩⟩
  simpa [τ1, τ2, Program.eval, Expr.eval] using htail

end NPComplete.RAMToTM

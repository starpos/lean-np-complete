module

public import NPComplete.CookLevin.UniformPackaging.ReverseBounds

/-!
# Decoder cursor and cost bounds

The formula scanner is assembled from unary decoders and clause parsers, each
of which must stay inside the input window and have bounded work. This module
supplies cursor, iteration-count, and encoded-input cost estimates for later
producer bounds. It also derives `ProgramBoundedIn` bounds for split-tail
emission, from its branches through the assembled program, including
`programBoundedIn_splitTailEmitProgAt_raw_of_step`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeThreeCNF)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

lemma decodeNatProgramAt_count_le
    (cursorReg countReg doneReg boundReg : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : countReg ≠ doneReg) :
    (decodeNatProgramAt cursorReg countReg doneReg boundReg).eval σ countReg ≤
      σ countReg + σ boundReg := by
  unfold decodeNatProgramAt decodeUnaryProgAt
  rw [eval_forN]
  simp only [Expr.eval]
  exact loopEval_decodeUnaryStep_count_le cursorReg countReg doneReg hcc hcd (σ boundReg) σ

lemma decodeLiteralValueProgramAt_cursor_le
    (cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hbc : boundReg ≠ cursorReg)
    (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
        cursorReg ≤ σ cursorReg + 1 + σ boundReg := by
  unfold decodeLiteralValueProgramAt
  rw [eval_seq, eval_seq, eval_seq]
  let σ1 := (readBitAdvanceProg cursorReg polReg).eval σ
  have hσ1 : σ1 cursorReg = σ cursorReg + 1 := by
    simpa [σ1] using (readBitAdvanceProg_eval cursorReg polReg σ hcp).2
  have hb1 : σ1 boundReg = σ boundReg :=
    readBitAdvanceProg_frame cursorReg polReg boundReg σ hbc hbp
  let σ2 := (Program.assign varReg (.const 0)).eval σ1
  have hσ2 : σ2 cursorReg = σ1 cursorReg := by
    simp [σ2, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hcv]
  have hb2 : σ2 boundReg = σ boundReg := by
    simp [σ2, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hbv, hb1]
  let σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hσ3 : σ3 cursorReg = σ2 cursorReg := by
    simp [σ3, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hcd]
  have hb3 : σ3 boundReg = σ boundReg := by
    simp [σ3, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hbd, hb2]
  unfold decodeNatProgramAt decodeUnaryProgAt
  rw [eval_forN]
  simp only [Expr.eval]
  change (loopEval (decodeUnaryStep cursorReg varReg doneReg) (σ3 boundReg) σ3) cursorReg ≤ _
  calc
    _ ≤ σ3 cursorReg + σ3 boundReg :=
      loopEval_decodeUnaryStep_cursor_le cursorReg varReg doneReg hcv hcd (σ3 boundReg) σ3
    _ = σ cursorReg + 1 + σ boundReg := by rw [hσ3, hσ2, hσ1, hb3]

lemma decodeLiteralValueProgramAt_cursor_budget_le
    (B cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hbc : boundReg ≠ cursorReg)
    (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg)
    (hbudget : σ cursorReg + 2 + 2 * σ boundReg ≤ B) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ boundReg ≤ B := by
  have hc := decodeLiteralValueProgramAt_cursor_le cursorReg polReg varReg doneReg boundReg σ
    hcp hcv hcd hbc hbp hbv hbd
  have hb := decodeLiteralValueProgramAt_bound_frame cursorReg polReg varReg doneReg boundReg σ
    hbc hbp hbv hbd
  rw [hb]
  omega

/-! The split-tail window pins the parse cursor against the input end, so both
    decoder operand budgets follow from the window instead of a tight store
    bound: this is the bridge that makes the long value envelope sufficient. -/
lemma split_tail_emit_cursor_budgets_of_window
    (K inputEnd baseLimit base : ℕ) (ls : List NPComplete.SAT.Literal)
    (tail : Bits) (addr : ℕ) (σ : Store)
    (cursorReg polReg varReg doneReg boundReg : ℕ)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg)
    (hcd : cursorReg ≠ doneReg) (hbc : boundReg ≠ cursorReg)
    (hbp : boundReg ≠ polReg) (hbv : boundReg ≠ varReg)
    (hbd : boundReg ≠ doneReg)
    (hwin : SplitTailEmitWindow inputEnd baseLimit base ls tail addr)
    (hcursor : σ cursorReg = addr)
    (hend : inputEnd + 2 + 2 * σ boundReg ≤ K) :
    σ cursorReg + 1 + σ boundReg ≤ K ∧
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
          cursorReg + 1 +
        (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
          boundReg ≤ K := by
  have haddr : addr ≤ inputEnd := by
    have h := hwin.1
    omega
  have h2 := decodeLiteralValueProgramAt_cursor_budget_le K cursorReg polReg varReg doneReg
    boundReg σ hcp hcv hcd hbc hbp hbv hbd (by omega)
  exact ⟨by omega, h2⟩

lemma decodeUnaryStep_programBoundedIn
    (B cursorReg countReg doneReg : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hidx : cursorReg ≤ B ∧ countReg ≤ B ∧ doneReg ≤ B)
    (hcursor : σ cursorReg + 1 ≤ B) (hcount : σ countReg + 1 ≤ B) :
    ProgramBoundedIn B σ (decodeUnaryStep cursorReg countReg doneReg) := by
  have hcursorDone : writeReg σ doneReg 1 cursorReg = σ cursorReg :=
    writeReg_diff σ doneReg 1 cursorReg hcd
  have hcursorCount : writeReg σ countReg (σ countReg + 1) cursorReg = σ cursorReg :=
    writeReg_diff σ countReg (σ countReg + 1) cursorReg hcc
  simp [decodeUnaryStep, ProgramBoundedIn, ExprBoundedIn, Expr.eval,
    hcursorDone, hcursorCount]
  omega

lemma programBoundedIn_decodeNatProgramAt_of_bounds
    (cursorReg countReg doneReg boundReg B : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (hcountDone : countReg ≠ doneReg)
    (hidx : cursorReg ≤ B ∧ countReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B)
    (hcursor : σ cursorReg + σ boundReg ≤ B)
    (hcount : σ countReg + σ boundReg ≤ B) :
    ProgramBoundedIn B σ (decodeNatProgramAt cursorReg countReg doneReg boundReg) := by
  unfold decodeNatProgramAt decodeUnaryProgAt
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
  refine ⟨hidx.2.2.2, ?_⟩
  intro m hm
  apply decodeUnaryStep_programBoundedIn B cursorReg countReg doneReg
    (loopEval (decodeUnaryStep cursorReg countReg doneReg) m σ)
    hcc hcd ⟨hidx.1, hidx.2.1, hidx.2.2.1⟩
  · have hc := loopEval_decodeUnaryStep_cursor_le cursorReg countReg doneReg hcc hcd m σ
    omega
  · have hc := loopEval_decodeUnaryStep_count_le cursorReg countReg doneReg hcc hcountDone m σ
    omega

lemma programBoundedIn_decodeLiteralValueProgramAt_of_bounds
    (B cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hB1 : 1 ≤ B) (hσ : StoreValuesLe B σ)
    (hcursor : σ cursorReg + 1 + σ boundReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) := by
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  let σ1 := (Program.assign polReg (.regInd (.reg cursorReg))).eval σ
  let σr := (Program.assign cursorReg (.add (.reg cursorReg) (.const 1))).eval σ1
  let σ2 := (Program.assign varReg (.const 0)).eval σr
  let σ3 := (Program.assign doneReg (.const 0)).eval σ2
  have hpRead1 : ProgramBoundedIn B σ
      (.assign polReg (.regInd (.reg cursorReg))) := by
    refine ⟨hidx.2.1, ?_⟩
    simp only [ExprBoundedIn, Expr.eval]
    exact ⟨hidx.1, hσ cursorReg⟩
  have hcursor1 : σ1 cursorReg = σ cursorReg := by
    simp [σ1, eval_assign, Expr.eval,
      writeReg_diff σ polReg _ cursorReg hcp]
  have hpRead2 : ProgramBoundedIn B σ1
      (.assign cursorReg (.add (.reg cursorReg) (.const 1))) := by
    refine ⟨hidx.1, ?_⟩
    simp only [ExprBoundedIn, Expr.eval]
    rw [hcursor1]
    omega
  have hpRead : ProgramBoundedIn B σ (readBitAdvanceProg cursorReg polReg) := by
    unfold readBitAdvanceProg
    exact ⟨hpRead1, hpRead2⟩
  have hpVar : ProgramBoundedIn B σr (Program.assign varReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have hpDone : ProgramBoundedIn B σ2 (Program.assign doneReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  have h1 : σ1 boundReg = σ boundReg := by
    simp [σ1, eval_assign, Expr.eval, writeReg_diff σ polReg _ boundReg hbp]
  have h1r : σr boundReg = σ boundReg := by
    simp [σr, eval_assign, Expr.eval, writeReg_diff _ cursorReg _ boundReg hbc, h1]
  have hbound3 : σ3 boundReg = σ boundReg := by
    simp only [σ3, σ2, eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ boundReg hbd,
      writeReg_diff _ varReg _ boundReg hbv, h1r]
  have hcursor3 : σ3 cursorReg = σ cursorReg + 1 := by
    simp only [σ3, σ2, σr, eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ cursorReg hcd,
      writeReg_diff _ varReg _ cursorReg hcv, writeReg_same]
    rw [hcursor1]
  have hpDecode : ProgramBoundedIn B σ3
      (decodeNatProgramAt cursorReg varReg doneReg boundReg) := by
    apply programBoundedIn_decodeNatProgramAt_of_bounds cursorReg varReg doneReg boundReg B σ3
      hcv hcd hvd ⟨hidx.1, hidx.2.2.1, hidx.2.2.2.1, hidx.2.2.2.2⟩
    · rw [hcursor3, hbound3]
      omega
    · rw [hbound3]
      have hv3 : σ3 varReg = 0 := by
        simp [σ3, σ2, eval_assign, Expr.eval, writeReg, hvd]
      rw [hv3]
      omega
  unfold decodeLiteralValueProgramAt
  refine ⟨hpRead, ?_⟩
  rw [show (readBitAdvanceProg cursorReg polReg).eval σ = σr by
    simp [readBitAdvanceProg, σr, σ1, eval_seq]]
  refine ⟨hpVar, ?_⟩
  rw [show (Program.assign varReg (.const 0)).eval σr = σ2 from rfl]
  exact ⟨hpDone, hpDecode⟩

lemma programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds
    (K B cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧ boundReg ≤ K)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (hB1 : 1 ≤ K) (hσ : StoreValuesLe K σ)
    (hcursor : σ cursorReg + 1 + σ boundReg ≤ K) (hK : K ≤ B) :
      ProgramBoundedIn B σ
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) ∧
      StoreValuesLe K
        ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ) ∧
      StoreValuesLe B
        ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ) ∧
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ 0 = σ 0 ∧
      σ cursorReg + 1 ≤
        (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
          cursorReg := by
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  have hpK := programBoundedIn_decodeLiteralValueProgramAt_of_bounds K cursorReg polReg
    varReg doneReg boundReg σ hidx ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩ hB1 hσ hcursor
  have hσB : StoreValuesLe B σ := fun i => (hσ i).trans hK
  have hidxB : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B := by
    omega
  have hpB := programBoundedIn_decodeLiteralValueProgramAt_of_bounds B cursorReg polReg
    varReg doneReg boundReg σ hidxB ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
    (by omega) hσB (by omega)
  have hstoreK := program_eval_storeValuesLe σ
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) hB1 hσ hpK
    (scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
  have hstore := program_eval_storeValuesLe σ
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) (by omega)
    hσB hpB (scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
  have hroot := decodeLiteralValueProgramAt_root cursorReg polReg varReg doneReg boundReg σ
    hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
  have hcursor := decodeLiteralValueProgramAt_cursor_ge cursorReg polReg varReg doneReg
    boundReg σ hcp hcv hcd
  exact ⟨hpB, hstoreK, hstore, hroot, hcursor⟩

lemma programBoundedIn_decodeLiteralValueProgramAt_syntax_bounds
    (K B cursorReg polReg varReg doneReg boundReg : ℕ) (σ : Store)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧ boundReg ≤ K)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (hσ : StoreValuesLe K σ)
    (hcursor : σ cursorReg + 1 + σ boundReg ≤ B) (hKB : K ≤ B) :
    ProgramBoundedIn B σ (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) ∧
      StoreValuesLe B
        ((decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ) ∧
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ 0 = σ 0 ∧
      (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ cursorReg ≤
        σ cursorReg + 1 + σ boundReg := by
  have hσB : StoreValuesLe B σ := fun i => (hσ i).trans hKB
  have hidxB : cursorReg ≤ B ∧ polReg ≤ B ∧ varReg ≤ B ∧ doneReg ≤ B ∧ boundReg ≤ B := by
    omega
  rcases hdist with ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
  have hp := programBoundedIn_decodeLiteralValueProgramAt_of_bounds B cursorReg polReg varReg
    doneReg boundReg σ hidxB ⟨hcp, hcv, hcd, hvd, hbc, hbp, hbv, hbd⟩
    (by omega) hσB hcursor
  have hstore := program_eval_storeValuesLe σ
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg) (by omega) hσB hp
    (scanFree_decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg)
  have hroot := decodeLiteralValueProgramAt_root cursorReg polReg varReg doneReg boundReg σ
    hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
  have hcur := decodeLiteralValueProgramAt_cursor_le cursorReg polReg varReg doneReg boundReg σ
    hcp hcv hcd hbc hbp hbv hbd
  exact ⟨hp, hstore, hroot, hcur⟩

lemma programBoundedIn_splitTailEmitTerminalOneProgAt_raw_bounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ carryPolReg ≤ K ∧
      carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hdist : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
      var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
      boundReg ≠ var2Reg ∧ boundReg ≠ doneReg)
    (hzero : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
      M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hcursor : σ cursorReg + 1 + σ boundReg ≤ K)
    (hbudget : writerAppendRawThreeBound K ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg) := by
  rcases hidx with ⟨hcursorB, hpolB, hvarB, hdoneB, hremB, hpol2B, hvar2B,
    hcpB, hcvB, hposB, hfreshB, hboundB⟩
  have hKB : K ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hdecode := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg pol2Reg var2Reg doneReg boundReg σ
    ⟨hcursorB, hpol2B, hvar2B, hdoneB, hboundB⟩ hdist hzero
    (by have := hσ 0; omega) hσ hcursor hKB
  let τ := (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
  have hτK : StoreValuesLe K τ := by simpa [τ] using hdecode.2.1
  have hτroot : τ 0 = M := by simpa [τ, hM] using hdecode.2.2.2.1
  have hτcursor0 : τ (M + curJ) ≠ 0 := by
    have hframe := decodeLiteralValueProgramAt_frame cursorReg pol2Reg var2Reg doneReg
      boundReg (M + curJ) σ hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hcontrol.2.2.2
    have hq : τ (M + curJ) = σ (M + curJ) := by simpa [τ] using hframe
    rw [hq]
    exact hq0
  have hwriter := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
    carryPolReg carryValReg pol2Reg var2Reg pol2Reg var2Reg τ hcurJ1 htmpJlt hstatic
    ⟨hcpB, hcvB, hpol2B, hvar2B, hpol2B, hvar2B⟩ hτK hτroot hτcursor0
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget)
  have hremProg : ProgramBoundedIn B
      ((writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
        pol2Reg var2Reg).eval τ) (.assign remainingReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  unfold splitTailEmitTerminalOneProgAt
  simpa [τ] using ⟨hdecode.1, ⟨hwriter.1, hremProg⟩⟩

lemma programBoundedIn_splitTailEmitTerminalTwoProgAt_raw_bounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ pol2Reg ≤ K ∧ var2Reg ≤ K ∧ pol3Reg ≤ K ∧ var3Reg ≤ K ∧
      carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hdist1 : cursorReg ≠ pol2Reg ∧ cursorReg ≠ var2Reg ∧ cursorReg ≠ doneReg ∧
      var2Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol2Reg ∧
      boundReg ≠ var2Reg ∧ boundReg ≠ doneReg)
    (hdist2 : cursorReg ≠ pol3Reg ∧ cursorReg ≠ var3Reg ∧ cursorReg ≠ doneReg ∧
      var3Reg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ pol3Reg ∧
      boundReg ≠ var3Reg ∧ boundReg ≠ doneReg)
    (hzero1 : cursorReg ≠ 0 ∧ pol2Reg ≠ 0 ∧ var2Reg ≠ 0 ∧ doneReg ≠ 0)
    (hzero2 : cursorReg ≠ 0 ∧ pol3Reg ≠ 0 ∧ var3Reg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol1 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol2Reg ∧
      M + curJ ≠ var2Reg ∧ M + curJ ≠ doneReg)
    (hcontrol2 : M + curJ ≠ cursorReg ∧ M + curJ ≠ pol3Reg ∧
      M + curJ ≠ var3Reg ∧ M + curJ ≠ doneReg)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hcursor1 : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcursor2 : (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
      cursorReg + 1 + (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
        boundReg ≤ K)
    (hbudget : writerAppendRawThreeBound K ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg) := by
  rcases hidx with ⟨hcursorB, hpolB, hvarB, hdoneB, hremB, hpol2B, hvar2B,
    hpol3B, hvar3B, hcpB, hcvB, hposB, hfreshB, hboundB⟩
  have hK1 : 1 ≤ K := by omega
  have hKB : K ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hdec1 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg pol2Reg var2Reg doneReg boundReg σ
    ⟨hcursorB, hpol2B, hvar2B, hdoneB, hboundB⟩ hdist1 hzero1
    (by have := hσ 0; omega) hσ hcursor1 hKB
  let τ1 := (decodeLiteralValueProgramAt cursorReg pol2Reg var2Reg doneReg boundReg).eval σ
  have hτ1K : StoreValuesLe K τ1 := by simpa [τ1] using hdec1.2.1
  have hτ1root : τ1 0 = M := by simpa [τ1, hM] using hdec1.2.2.2.1
  have hτ1cursor0 : τ1 (M + curJ) ≠ 0 := by
    have hframe := decodeLiteralValueProgramAt_frame cursorReg pol2Reg var2Reg doneReg
      boundReg (M + curJ) σ hcontrol1.1 hcontrol1.2.1 hcontrol1.2.2.1 hcontrol1.2.2.2
    have hq : τ1 (M + curJ) = σ (M + curJ) := by simpa [τ1] using hframe
    rw [hq]
    exact hq0
  have hdec2 := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg pol3Reg var3Reg doneReg boundReg τ1
    ⟨hcursorB, hpol3B, hvar3B, hdoneB, hboundB⟩ hdist2 hzero2
    hK1 hτ1K hcursor2 hKB
  let τ2 := (decodeLiteralValueProgramAt cursorReg pol3Reg var3Reg doneReg boundReg).eval τ1
  have hτ2K : StoreValuesLe K τ2 := by simpa [τ2] using hdec2.2.1
  have hτ2root : τ2 0 = M := by simpa [τ2, hτ1root] using hdec2.2.2.2.1
  have hτ2cursor0 : τ2 (M + curJ) ≠ 0 := by
    have hframe := decodeLiteralValueProgramAt_frame cursorReg pol3Reg var3Reg doneReg
      boundReg (M + curJ) τ1 hcontrol2.1 hcontrol2.2.1 hcontrol2.2.2.1 hcontrol2.2.2.2
    have hq : τ2 (M + curJ) = τ1 (M + curJ) := by simpa [τ2] using hframe
    rw [hq]
    exact hτ1cursor0
  have hwriter := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
    carryPolReg carryValReg pol2Reg var2Reg pol3Reg var3Reg τ2 hcurJ1 htmpJlt hstatic
    ⟨hcpB, hcvB, hpol2B, hvar2B, hpol3B, hvar3B⟩ hτ2K hτ2root hτ2cursor0
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget)
  have hremProg : ProgramBoundedIn B
      ((writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg pol2Reg var2Reg
        pol3Reg var3Reg).eval τ2) (.assign remainingReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  unfold splitTailEmitTerminalTwoProgAt
  simpa [τ1, τ2] using ⟨hdec1.1, ⟨hdec2.1, ⟨hwriter.1, hremProg⟩⟩⟩

lemma programBoundedIn_splitTailEmitIntermediateProgAt_raw_bounds
    (K B M curJ tmpJ cursorReg polReg varReg doneReg remainingReg carryPolReg carryValReg
      posPolReg freshReg boundReg : ℕ) (σ : Store)
    (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : cursorReg ≤ K ∧ polReg ≤ K ∧ varReg ≤ K ∧ doneReg ≤ K ∧
      remainingReg ≤ K ∧ carryPolReg ≤ K ∧ carryValReg ≤ K ∧ posPolReg ≤ K ∧
      freshReg ≤ K ∧ boundReg ≤ K)
    (hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
      varReg ≠ doneReg ∧ boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧
      boundReg ≠ varReg ∧ boundReg ≠ doneReg)
    (hzero : cursorReg ≠ 0 ∧ polReg ≠ 0 ∧ varReg ≠ 0 ∧ doneReg ≠ 0)
    (hcontrol : M + curJ ≠ cursorReg ∧ M + curJ ≠ polReg ∧
      M + curJ ≠ varReg ∧ M + curJ ≠ doneReg)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0) (hcursor : σ cursorReg + 1 + σ boundReg ≤ K)
    (hcarryVal0 : carryValReg ≠ 0) (hfresh0 : freshReg ≠ 0)
    (hcarryValCursor : carryValReg ≠ M + curJ)
    (hfreshCursor : freshReg ≠ M + curJ)
    (hbudget : writerAppendRawThreeBound K + 1 ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg) := by
  rcases hidx with ⟨hcursorB, hpolB, hvarB, hdoneB, hremB, hcpB, hcvB, hposB,
    hfreshB, hboundB⟩
  have hK1 : 1 ≤ K := by omega
  have hKB : K ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hdecode := programBoundedIn_decodeLiteralValueProgramAt_raw_post_bounds K B
    cursorReg polReg varReg doneReg boundReg σ
    ⟨hcursorB, hpolB, hvarB, hdoneB, hboundB⟩ hdist hzero hK1 hσ hcursor hKB
  let τ := (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ
  have hτK : StoreValuesLe K τ := by simpa [τ] using hdecode.2.1
  have hτroot : τ 0 = M := by simpa [τ, hM] using hdecode.2.2.2.1
  have hτcursor0 : τ (M + curJ) ≠ 0 := by
    have hframe := decodeLiteralValueProgramAt_frame cursorReg polReg varReg doneReg
      boundReg (M + curJ) σ hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hcontrol.2.2.2
    have hq : τ (M + curJ) = σ (M + curJ) := by simpa [τ] using hframe
    rw [hq]
    exact hq0
  have hwriter := programBoundedIn_writerAppendSplitTailLinkDynamicProg_raw_bounds K B M curJ
    tmpJ carryPolReg carryValReg polReg varReg posPolReg freshReg τ hcurJ1 htmpJlt hstatic
    ⟨hcpB, hcvB, hpolB, hvarB, hposB, hfreshB⟩ hτK hτroot hτcursor0
    hcarryVal0 hfresh0 hcarryValCursor hfreshCursor hbudget
  have hremPost :
      (writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg).eval τ remainingReg ≤ B := hwriter.2.1 remainingReg
  have hremProg : ProgramBoundedIn B
      ((writerAppendSplitTailLinkDynamicProg curJ tmpJ carryPolReg carryValReg polReg varReg
        posPolReg freshReg).eval τ)
      (.assign remainingReg (.sub (.reg remainingReg) (.const 1))) := by
    simp [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    omega
  unfold splitTailEmitIntermediateProgAt
  simpa [τ] using ⟨hdecode.1, ⟨hwriter.1, hremProg⟩⟩

lemma programBoundedIn_splitTailEmitTerminalZeroProg_raw_bounds
    (K B M curJ tmpJ remainingReg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hcurJ1 : 1 ≤ curJ) (htmpJlt : curJ < tmpJ)
    (hstatic : M + curJ ≤ K ∧ M + tmpJ ≤ K ∧ curJ ≤ K ∧ tmpJ ≤ K)
    (hidx : remainingReg ≤ K ∧ carryPolReg ≤ K ∧ carryValReg ≤ K ∧
      posPolReg ≤ K ∧ freshReg ≤ K ∧ boundReg ≤ K)
    (hσ : StoreValuesLe K σ) (hM : σ 0 = M)
    (hq0 : σ (M + curJ) ≠ 0)
    (hbudget : writerAppendRawThreeBound K ≤ B) :
    ProgramBoundedIn B σ
      (splitTailEmitTerminalZeroProg curJ tmpJ 0 0 0 0 remainingReg carryPolReg
        carryValReg posPolReg freshReg boundReg) := by
  rcases hidx with ⟨hremB, hcpB, hcvB, hposB, hfreshB, hboundB⟩
  have hKB : K ≤ B := by
    simp [writerAppendRawThreeBound, writerAppendRawStepBound] at hbudget ⊢
    omega
  have hwriter := programBoundedIn_writerAppendThreeRegsProg_raw_bounds K B M curJ tmpJ
    carryPolReg carryValReg carryPolReg carryValReg carryPolReg carryValReg σ hcurJ1 htmpJlt
    hstatic ⟨hcpB, hcvB, hcpB, hcvB, hcpB, hcvB⟩ hσ hM hq0
    (by simpa [writerAppendRawThreeBound, writerAppendRawStepBound] using hbudget)
  have hremProg : ProgramBoundedIn B
      ((writerAppendThreeRegsProg curJ tmpJ carryPolReg carryValReg carryPolReg carryValReg
        carryPolReg carryValReg).eval σ) (.assign remainingReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn]
    omega
  simpa [splitTailEmitTerminalZeroProg] using ⟨hwriter.1, hremProg⟩

lemma programBoundedIn_splitTailEmitStepProgAt_raw_of_branches
    (B curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hB2 : 2 ≤ B) (hremaining : remainingReg ≤ B)
    (hone : ProgramBoundedIn B σ
      (splitTailEmitTerminalOneProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg carryPolReg carryValReg posPolReg freshReg boundReg))
    (htwo : ProgramBoundedIn B σ
      (splitTailEmitTerminalTwoProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg))
    (hinter : ProgramBoundedIn B σ
      (splitTailEmitIntermediateProgAt curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg carryPolReg carryValReg posPolReg freshReg boundReg)) :
    ProgramBoundedIn B σ
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg) :=
  programBoundedIn_splitTailEmitStepProgAt_of_branches B curJ tmpJ cursorReg polReg varReg
    doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
    freshReg boundReg σ hB2 hremaining hone htwo hinter

lemma programBoundedIn_splitTailEmitProgAt_raw_of_step
    (B curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (hB1 : 1 ≤ B) (hremaining : remainingReg ≤ B)
    (hremainingValue : σ remainingReg + 1 ≤ B)
    (hzero : ProgramBoundedIn B σ
      (splitTailEmitTerminalZeroProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        carryPolReg carryValReg posPolReg freshReg boundReg))
    (hstep : ∀ m < σ remainingReg + 1,
      ProgramBoundedIn B
        (loopEval
          (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
            pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
            boundReg) m σ)
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
          boundReg)) :
    ProgramBoundedIn B σ
      (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg) :=
  programBoundedIn_splitTailEmitProgAt_of_step B curJ tmpJ cursorReg polReg varReg doneReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
    boundReg σ hB1 hremaining hremainingValue hzero hstep

end NPComplete.CookLevin

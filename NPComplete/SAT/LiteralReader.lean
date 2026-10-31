module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.SAT.LiteralReaderFixed

/-!
# Register-bounded literal reader

This reader samples its unary bound from a register, allowing one program to
read literals with input-dependent bounds.
-/

@[expose] public section

namespace NPComplete.SAT

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat)

@[construction_api] def decodeLiteralValueProgramAt
    (cursorReg polReg varReg doneReg boundReg : ℕ) : Program :=
  .seq (readBitAdvanceProg cursorReg polReg)
  <| .seq (.assign varReg (.const 0))
      <| .seq (.assign doneReg (.const 0))
          (decodeUnaryProgAt cursorReg varReg doneReg (.reg boundReg))

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
  exact decodeUnaryProgAt_eq cursorReg varReg doneReg (.reg boundReg) bound σ3
    (by simp [Expr.eval, hσ3])

@[construction_api] lemma decodeLiteralValueProgramAt_avoids_frame
    (cursorReg polReg varReg doneReg boundReg : ℕ) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).Avoids
      (fun r => r ≠ cursorReg ∧ r ≠ polReg ∧ r ≠ varReg ∧ r ≠ doneReg) := by
  simp [Program.Avoids, decodeLiteralValueProgramAt,
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

@[construction_api] lemma decodeLiteralValueProgramAt_frame
    (cursorReg polReg varReg doneReg boundReg r : ℕ) (σ : Store)
    (hrc : r ≠ cursorReg) (hrp : r ≠ polReg) (hrv : r ≠ varReg)
    (hrd : r ≠ doneReg) :
    (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg boundReg).eval σ r = σ r := by
  exact (decodeLiteralValueProgramAt_avoids_frame cursorReg polReg varReg doneReg boundReg).eval_frame
    σ ⟨hrc, hrp, hrv, hrd⟩

@[construction_api] lemma decodeLiteralValueProgramAt_bounded
    {c p k d lr b B : ℕ} {l : NPComplete.SAT.Literal} {rest : Bits} {σ : Store}
    (hcb : c < b) (hpb : p < b) (hkb : k < b) (hdb : d < b)
    (hcp : c ≠ p) (hck : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hc : σ c = b) (hcell : BitsFrom σ b (encodeLiteral l ++ rest))
    (hlr : lr ≤ B) (hB : b + l.var + 3 ≤ B) :
    ProgramBoundedIn B σ (decodeLiteralValueProgramAt c p k d lr) := by
  change ProgramBoundedIn B σ (((Program.assign p (.regInd (.reg c))).seq
    (Program.assign c (.add (.reg c) (.const 1)))).seq (readUnaryProgAt c k d lr))
  let τ := writeReg (writeReg σ p (σ (σ c))) c (σ c + 1)
  have hcell' : BitsFrom σ b ((!l.is_pos) :: (encodeNat l.var ++ rest)) := by
    cases l <;> simpa [encodeLiteral, NPComplete.SAT.Literal.is_pos, NPComplete.SAT.Literal.var] using hcell
  have hv : σ b ≤ 1 := by
    have h := hcell' 0 (by simp)
    cases hpos : l.is_pos <;> simp [hpos] at h <;> omega
  have hτ : ∀ r, b ≤ r → τ r = σ r := by
    intro r hr
    dsimp [τ]
    rw [writeReg_diff _ _ _ _ (by omega), writeReg_diff _ _ _ _ (by omega)]
  have htail : BitsFrom τ (b+1) (encodeNat l.var ++ rest) := by
    intro i hi
    rw [hτ _ (by omega)]
    exact (bitsFrom_cons _ _ _ _ hcell').2 i hi
  have hread := readUnaryProgAt_bounded (c := c) (k := k) (d := d) (lr := lr) (addr := b+1)
    (n := l.var) (rest := rest) (σ := τ) (B := B)
    (by omega) (by omega) (by omega) hck hcd hkd
    (by simp [τ, hc]) htail hlr (by omega)
  refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
  · simp only [ExprBoundedIn, Expr.eval, hc]; omega
  · simp only [eval_assign, ProgramBoundedIn, ExprBoundedIn, Expr.eval,
      writeReg_diff _ _ _ _ hcp, hc]; omega
  · simpa [τ, eval_seq, eval_assign, Expr.eval, writeReg_diff _ _ _ _ hcp] using hread

@[construction_api] lemma scanFree_decodeLiteralValueProgramAt
    (cursorReg polReg varReg doneReg boundReg : ℕ) :
    ScanFree (decodeLiteralValueProgramAt cursorReg polReg varReg doneReg
      boundReg) := by
  simp [ScanFree, decodeLiteralValueProgramAt, readBitAdvanceProg,
    decodeUnaryProgAt, decodeUnaryStep]

@[construction_api] lemma programBoundedIn_decodeLiteralValueProgramAt_of_bounds
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
  have hv3 : σ3 varReg = 0 := by
    simp [σ3, σ2, eval_assign, Expr.eval, writeReg, hvd]
  have hpDecode : ProgramBoundedIn B σ3
      (decodeUnaryProgAt cursorReg varReg doneReg (.reg boundReg)) := by
    simp only [decodeUnaryProgAt, ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    refine ⟨hidx.2.2.2.2, fun m hm => ?_⟩
    apply unary_step_bounded_aux B cursorReg varReg doneReg _ hcv hcd
      ⟨hidx.1, hidx.2.2.1, hidx.2.2.2.1⟩
    · have h := loopEval_decodeUnaryStep_cursor_le cursorReg varReg doneReg hcv hcd m σ3
      omega
    · have h := loopEval_decodeUnaryStep_count_le cursorReg varReg doneReg hcv hvd m σ3
      omega
  unfold decodeLiteralValueProgramAt
  refine ⟨hpRead, ?_⟩
  rw [show (readBitAdvanceProg cursorReg polReg).eval σ = σr by
    simp [readBitAdvanceProg, σr, σ1, eval_seq]]
  refine ⟨hpVar, ?_⟩
  rw [show (Program.assign varReg (.const 0)).eval σr = σ2 from rfl]
  exact ⟨hpDone, hpDecode⟩

end NPComplete.SAT

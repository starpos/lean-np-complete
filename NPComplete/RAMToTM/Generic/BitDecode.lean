module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BitEncoding
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.BoundedWhile.Frame

/-!
# Shared bit decoding

RAM-to-TM constructions need to consume bit encodings without knowing their values at compile
time. Keeping the representation and unary scanner independent of any reduction lets parsers and
other constructions reuse the same correctness and frame facts.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr writeReg eval_ifNZ eval_seq
  eval_assign eval_assignInd eval_skip eval_forN loopEval loopEval_succ loopEval_zero
  writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits encodeNat encodeNat_succ encodeNat_length)

/-- `σ` holds `bits` as `0`/`1` `Nat` cells starting at address `addr` — the shape
    `BoundedWhileDecider.bitInputStore` gives its bit region, generalized to an arbitrary base so
    it can describe the store mid-decode (past cells already consumed). -/
@[construction_api] def BitsFrom (σ : Store) (addr : ℕ) (bits : Bits) : Prop :=
  ∀ i, (h : i < bits.length) → σ (addr + i) = if bits[i] then 1 else 0

@[construction_api] lemma bits_from_bitInputStore (bits : Bits) :
    BitsFrom (bitInputStore bits) 1 bits := by
  intro i hi
  have haddr : 1 + i = i + 1 := Nat.add_comm 1 i
  rw [haddr]
  simp only [bitInputStore]
  rw [List.getD_eq_getElem _ false hi]

@[construction_api] lemma bitsFrom_cons (σ : Store) (addr : ℕ) (b : Bool) (rest : Bits)
    (h : BitsFrom σ addr (b :: rest)) :
    σ addr = (if b then 1 else 0) ∧ BitsFrom σ (addr + 1) rest := by
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    exact h0
  · intro i hi
    have hs := h (i + 1) (by simpa using hi)
    simp only [List.getElem_cons_succ] at hs
    rwa [show addr + (i + 1) = addr + 1 + i from by omega] at hs

/-- One iteration of the unary-`encodeNat` decode scan: while `doneReg = 0`, read the bit at
    `cursorReg`; a `1` (`true`) bit is the terminator — it sets `doneReg` and advances the cursor
    past it; a `0` (`false`) bit increments `countReg` and advances the cursor by one. Once
    `doneReg ≠ 0` the iteration is a no-op (the outer `.ifNZ` on `doneReg` short-circuits to
    `.skip`), so running this loop past the true terminator position leaves `countReg`/`cursorReg`
    fixed at their final values — the loop's caller can supply any bound `≥ n + 1`, not exactly
    `n + 1`. -/
def decodeUnaryStep (cursorReg countReg doneReg : ℕ) : Program :=
  .ifNZ (.reg doneReg) .skip
    (.ifNZ (.regInd (.reg cursorReg))
      (.seq (.assign doneReg (.const 1))
            (.assign cursorReg (.add (.reg cursorReg) (.const 1))))
      (.seq (.assign countReg (.add (.reg countReg) (.const 1)))
            (.assign cursorReg (.add (.reg cursorReg) (.const 1)))))

lemma decodeUnaryStep_frame (cursorReg countReg doneReg r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ countReg) (h3 : r ≠ doneReg) :
    (decodeUnaryStep cursorReg countReg doneReg).eval σ r = σ r := by
  unfold decodeUnaryStep
  simp only [eval_ifNZ, eval_seq, eval_assign, Expr.eval]
  split_ifs <;> simp_all [writeReg]
  all_goals split_ifs <;> simp_all [writeReg]

lemma decodeUnaryStep_zero_bit (cursorReg countReg doneReg : ℕ) (σ : Store)
    (hcc : cursorReg ≠ countReg) (hd : σ doneReg = 0) (hb : σ (σ cursorReg) = 0) :
    (decodeUnaryStep cursorReg countReg doneReg).eval σ =
      writeReg (writeReg σ countReg (σ countReg + 1)) cursorReg (σ cursorReg + 1) := by
  unfold decodeUnaryStep
  simp only [eval_ifNZ, eval_seq, eval_assign, Expr.eval]
  rw [ite_eq_right (by simpa using hd), ite_eq_right (by simpa using hb)]
  simp [writeReg_diff σ countReg (σ countReg + 1) cursorReg hcc]

lemma decodeUnaryStep_one_bit (cursorReg countReg doneReg : ℕ) (σ : Store)
    (hcd : cursorReg ≠ doneReg) (hd : σ doneReg = 0) (hb : σ (σ cursorReg) ≠ 0) :
    (decodeUnaryStep cursorReg countReg doneReg).eval σ =
      writeReg (writeReg σ doneReg 1) cursorReg (σ cursorReg + 1) := by
  unfold decodeUnaryStep
  simp only [eval_ifNZ, eval_seq, eval_assign, Expr.eval]
  rw [ite_eq_right (by simpa using hd), ite_eq_left hb]
  simp [writeReg_diff σ doneReg 1 cursorReg hcd]

/-- Decoding `encodeNat n` starting at `addr`, with the control registers `cursorReg`/
    `countReg`/`doneReg` disjoint from the bit region (all `< addr`, sufficient since `addr` only
    grows across the recursion) and pairwise distinct: after exactly `n + 1` steps the loop lands
    on the terminator, `cursorReg` advanced past it, `countReg` bumped by `n` from its starting
    value `c0` (letting decode calls chain: the next `encodeNat` read starts from `c0 := 0`
    freshly, while `cursorReg`/the input stream continues), `doneReg` set, and every cell outside
    `{cursorReg, countReg, doneReg}` unchanged. -/
lemma decode_unary_loop_correct (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg) :
    ∀ (n addr c0 : ℕ) (σ : Store),
      cursorReg < addr → countReg < addr → doneReg < addr →
      σ cursorReg = addr → σ countReg = c0 → σ doneReg = 0 →
      BitsFrom σ addr (encodeNat n) →
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ) cursorReg
        = addr + n + 1 ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ) countReg = c0 + n ∧
      (loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ) doneReg = 1 ∧
      ∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
        (loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ) r = σ r := by
  intro n
  induction n with
  | zero =>
    intro addr c0 σ hca hka hda hc hk hd hbits
    have hb0 : σ addr = 1 := by
      have := (bitsFrom_cons σ addr true [] (by simpa using hbits)).1
      simpa using this
    have hb : σ (σ cursorReg) ≠ 0 := by rw [hc, hb0]; decide
    rw [loopEval_one, decodeUnaryStep_one_bit cursorReg countReg doneReg σ hcd hd hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [writeReg_same, hc]
    · rw [writeReg_diff _ cursorReg _ countReg (Ne.symm hcc),
        writeReg_diff σ doneReg 1 countReg hkd, hk]; omega
    · rw [writeReg_diff _ cursorReg _ doneReg (Ne.symm hcd), writeReg_same]
    · intro r hr1 hr2 hr3
      rw [writeReg_diff _ cursorReg _ r hr1, writeReg_diff σ doneReg 1 r hr3]
  | succ n ih =>
    intro addr c0 σ hca hka hda hc hk hd hbits
    have hbits' : BitsFrom σ addr (false :: encodeNat n) := by
      rw [← encodeNat_succ]; exact hbits
    obtain ⟨hb0, hbrest⟩ := bitsFrom_cons σ addr false (encodeNat n) hbits'
    have hb0' : σ (σ cursorReg) = 0 := by rw [hc]; simpa using hb0
    set σ1 := (decodeUnaryStep cursorReg countReg doneReg).eval σ with hσ1def
    have hσ1 : σ1 =
        writeReg (writeReg σ countReg (σ countReg + 1)) cursorReg (σ cursorReg + 1) :=
      decodeUnaryStep_zero_bit cursorReg countReg doneReg σ hcc hd hb0'
    have hσ1c : σ1 cursorReg = addr + 1 := by rw [hσ1, writeReg_same, hc]
    have hσ1k : σ1 countReg = c0 + 1 := by
      rw [hσ1, writeReg_diff _ cursorReg _ countReg (Ne.symm hcc), writeReg_same, hk]
    have hσ1d : σ1 doneReg = 0 := by
      rw [hσ1, writeReg_diff _ cursorReg _ doneReg (Ne.symm hcd),
        writeReg_diff _ countReg _ doneReg (Ne.symm hkd), hd]
    have hσ1bits : BitsFrom σ1 (addr + 1) (encodeNat n) := by
      intro i hi
      have hrw : σ1 (addr + 1 + i) = σ (addr + 1 + i) := by
        rw [hσ1, writeReg_diff _ cursorReg _ (addr + 1 + i) (by omega),
          writeReg_diff _ countReg _ (addr + 1 + i) (by omega)]
      rw [hrw]; exact hbrest i hi
    obtain ⟨hfc, hfk, hfd, hfr⟩ :=
      ih (addr + 1) (c0 + 1) σ1 (by omega) (by omega) (by omega) hσ1c hσ1k hσ1d hσ1bits
    have hstep : loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1 + 1) σ =
        loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ1 := by
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, loopEval_succ]
    rw [hstep]
    refine ⟨?_, ?_, hfd, ?_⟩
    · rw [hfc]; omega
    · rw [hfk]; omega
    · intro r hr1 hr2 hr3
      rw [hfr r hr1 hr2 hr3, hσ1def]
      exact decodeUnaryStep_frame cursorReg countReg doneReg r σ hr1 hr2 hr3

/-! ## `decodeUnaryProg`: the `forN`-wrapped loop, safe for any bound `≥ n + 1`

`decode_unary_loop_correct` fixes the loop count to exactly `n + 1`; a caller writing a compiled
`Program` cannot know `n` (the value being decoded) statically, so must supply some fixed or
runtime-computed `bound`. `decodeUnaryStep`'s `doneReg`-gated no-op past the terminator (module
docstring) makes any `bound ≥ n + 1` safe — `decodeUnaryProg_correct` makes that precise via
`loopEval_add` splitting the run into the first `n + 1` (real) steps and the remaining
`bound - (n + 1)` (idempotent) steps. -/

lemma decodeUnaryStep_done (cursorReg countReg doneReg : ℕ) (σ : Store)
    (hd : σ doneReg ≠ 0) :
    (decodeUnaryStep cursorReg countReg doneReg).eval σ = σ := by
  unfold decodeUnaryStep
  simp only [eval_ifNZ, Expr.eval, ite_eq_left hd, eval_skip]

lemma loopEval_decodeUnaryStep_done (cursorReg countReg doneReg : ℕ) (σ : Store) (k : ℕ)
    (hd : σ doneReg ≠ 0) :
    loopEval (decodeUnaryStep cursorReg countReg doneReg) k σ = σ := by
  induction k with
  | zero => simp
  | succ k ih => rw [loopEval_succ, decodeUnaryStep_done cursorReg countReg doneReg σ hd, ih]

lemma decodeUnaryStep_cursor_succ_le (cursorReg countReg doneReg : ℕ) (τ : Store)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) :
    (decodeUnaryStep cursorReg countReg doneReg).eval τ cursorReg ≤ τ cursorReg + 1 := by
  unfold decodeUnaryStep
  simp only [Program.eval, Expr.eval]
  by_cases hd : τ doneReg = 0
  · by_cases hb : τ (τ cursorReg) = 0
    · simp [hd, hb, writeReg, hcc]
    · simp [hd, hb, writeReg, hcd]
  · simp [hd]

lemma decodeUnaryStep_count_succ_le (cursorReg countReg doneReg : ℕ) (τ : Store)
    (hcc : cursorReg ≠ countReg) (hkd : countReg ≠ doneReg) :
    (decodeUnaryStep cursorReg countReg doneReg).eval τ countReg ≤ τ countReg + 1 := by
  unfold decodeUnaryStep
  simp only [Program.eval, Expr.eval]
  by_cases hd : τ doneReg = 0
  · by_cases hb : τ (τ cursorReg) = 0
    · simp [hd, hb, writeReg, hcc.symm]
    · simp [hd, hb, writeReg, hcc.symm, hkd]
  · simp [hd]

/-- Running the unary decode step `m` times advances the cursor by at most `m`. -/
lemma loopEval_decodeUnaryStep_cursor_le (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg)
    (m : ℕ) (τ : Store) :
    (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) cursorReg ≤
      τ cursorReg + m := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [loopEval_succ]
    have hs := decodeUnaryStep_cursor_succ_le cursorReg countReg doneReg τ hcc hcd
    have hi := ih ((decodeUnaryStep cursorReg countReg doneReg).eval τ)
    omega

/-- Running the unary decode step `m` times raises the counter by at most `m`. -/
lemma loopEval_decodeUnaryStep_count_le (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hkd : countReg ≠ doneReg)
    (m : ℕ) (τ : Store) :
    (loopEval (decodeUnaryStep cursorReg countReg doneReg) m τ) countReg ≤
      τ countReg + m := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [loopEval_succ]
    have hs := decodeUnaryStep_count_succ_le cursorReg countReg doneReg τ hcc hkd
    have hi := ih ((decodeUnaryStep cursorReg countReg doneReg).eval τ)
    omega

/-- The loop a compiled reduction program actually emits: `decodeUnaryStep` run for a fixed
    `bound`. `decodeUnaryProg_correct` below is the corollary of `decode_unary_loop_correct` this
    exposes to callers — any `bound ≥ n + 1` gives the same answer. -/
def decodeUnaryProg (cursorReg countReg doneReg bound : ℕ) : Program :=
  .forN (.const bound) (decodeUnaryStep cursorReg countReg doneReg)

lemma decodeUnaryProg_correct (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg)
    (n bound addr c0 : ℕ) (σ : Store)
    (hbound : n + 1 ≤ bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeNat n)) :
    (decodeUnaryProg cursorReg countReg doneReg bound).eval σ cursorReg = addr + n + 1 ∧
    (decodeUnaryProg cursorReg countReg doneReg bound).eval σ countReg = c0 + n ∧
    (decodeUnaryProg cursorReg countReg doneReg bound).eval σ doneReg = 1 ∧
    ∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeUnaryProg cursorReg countReg doneReg bound).eval σ r = σ r := by
  obtain ⟨hfc, hfk, hfd, hfr⟩ :=
    decode_unary_loop_correct cursorReg countReg doneReg hcc hcd hkd n addr c0 σ
      hca hka hda hc hk hd hbits
  have hsplit : bound = (n + 1) + (bound - (n + 1)) := by omega
  have heq : (decodeUnaryProg cursorReg countReg doneReg bound).eval σ =
      loopEval (decodeUnaryStep cursorReg countReg doneReg) (n + 1) σ := by
    unfold decodeUnaryProg
    rw [eval_forN, Expr.eval, hsplit, loopEval_add,
      loopEval_decodeUnaryStep_done cursorReg countReg doneReg _ _ (by rw [hfd]; decide)]
  rw [heq]
  exact ⟨hfc, hfk, hfd, hfr⟩

/-- Read the bit at `σ cursorReg` into `outReg`, then advance the cursor by one. -/
def readBitAdvanceProg (cursorReg outReg : ℕ) : Program :=
  .seq (.assign outReg (.regInd (.reg cursorReg)))
       (.assign cursorReg (.add (.reg cursorReg) (.const 1)))

lemma readBitAdvanceProg_eval (cursorReg outReg : ℕ) (σ : Store) (hco : cursorReg ≠ outReg) :
    (readBitAdvanceProg cursorReg outReg).eval σ outReg = σ (σ cursorReg) ∧
    (readBitAdvanceProg cursorReg outReg).eval σ cursorReg = σ cursorReg + 1 := by
  unfold readBitAdvanceProg
  simp only [eval_seq, eval_assign, Expr.eval]
  refine ⟨?_, ?_⟩
  · rw [writeReg_diff _ cursorReg _ outReg (Ne.symm hco), writeReg_same]
  · rw [writeReg_diff _ outReg _ cursorReg hco, writeReg_same]

lemma readBitAdvanceProg_frame (cursorReg outReg r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ outReg) :
    (readBitAdvanceProg cursorReg outReg).eval σ r = σ r := by
  unfold readBitAdvanceProg
  simp only [eval_seq, eval_assign, Expr.eval]
  simp [writeReg, h1, h2]

lemma bitsFrom_writeReg {σ : Store} {addr : ℕ} {bits : Bits} (hb : BitsFrom σ addr bits)
    (r v : ℕ) (hr : r < addr) : BitsFrom (writeReg σ r v) addr bits := by
  intro i hi
  rw [writeReg_diff σ r v (addr + i) (by omega)]
  exact hb i hi

/-- If `body` leaves cell `r` unchanged from any starting store, looping it any number of times
    also leaves that cell unchanged. -/
lemma loopEval_frame_of_step_frame (body : Program) (r : ℕ)
    (hstep : ∀ σ, body.eval σ r = σ r) (k : ℕ) (σ : Store) :
    loopEval body k σ r = σ r :=
  NPComplete.BoundedWhile.loopEval_frame body r hstep k σ

lemma decodeUnaryProg_frame (cursorReg countReg doneReg bound r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ countReg) (h3 : r ≠ doneReg) :
    (decodeUnaryProg cursorReg countReg doneReg bound).eval σ r = σ r := by
  unfold decodeUnaryProg
  rw [eval_forN, Expr.eval]
  exact loopEval_frame_of_step_frame (decodeUnaryStep cursorReg countReg doneReg) r
    (fun σ' => decodeUnaryStep_frame cursorReg countReg doneReg r σ' h1 h2 h3) bound σ

/-! ## Runtime-bound unary scanner -/

@[construction_api] def decodeUnaryProgAt (cursorReg countReg doneReg : ℕ) (boundE : Expr) : Program :=
  .forN boundE (decodeUnaryStep cursorReg countReg doneReg)

lemma decodeUnaryProgAt_eq (cursorReg countReg doneReg : ℕ) (boundE : Expr)
    (bound : ℕ) (σ : Store) (hb : boundE.eval σ = bound) :
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ =
      (decodeUnaryProg cursorReg countReg doneReg bound).eval σ := by
  unfold decodeUnaryProgAt decodeUnaryProg
  rw [eval_forN, eval_forN, hb]
  rfl

@[construction_api] lemma decodeUnaryProgAt_correct (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg)
    (n bound addr c0 : ℕ) (σ : Store) (boundE : Expr)
    (hbE : boundE.eval σ = bound) (hbound : n + 1 ≤ bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeNat n)) :
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ cursorReg = addr + n + 1 ∧
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ countReg = c0 + n ∧
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ doneReg = 1 ∧
    ∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ r = σ r := by
  rw [decodeUnaryProgAt_eq cursorReg countReg doneReg boundE bound σ hbE]
  exact decodeUnaryProg_correct cursorReg countReg doneReg hcc hcd hkd n bound addr c0 σ
    hbound hca hka hda hc hk hd hbits

@[construction_api] lemma decodeUnaryProgAt_frame (cursorReg countReg doneReg : ℕ) (boundE : Expr)
    (r : ℕ) (σ : Store) (h1 : r ≠ cursorReg) (h2 : r ≠ countReg)
    (h3 : r ≠ doneReg) :
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ r = σ r := by
  unfold decodeUnaryProgAt
  simp only [eval_forN]
  exact loopEval_frame_of_step_frame (decodeUnaryStep cursorReg countReg doneReg) r
    (fun τ => decodeUnaryStep_frame cursorReg countReg doneReg r τ h1 h2 h3)
    (boundE.eval σ) σ

@[construction_api] lemma bitsFrom_append (σ : Store) (addr : ℕ) (bits1 bits2 : Bits)
    (h : BitsFrom σ addr (bits1 ++ bits2)) :
    BitsFrom σ addr bits1 ∧ BitsFrom σ (addr + bits1.length) bits2 := by
  constructor
  · intro i hi
    have hi' : i < (bits1 ++ bits2).length := by simp; omega
    have := h i hi'
    rwa [List.getElem_append_left hi] at this
  · intro i hi
    have hi' : bits1.length + i < (bits1 ++ bits2).length := by simp; omega
    have heq := h (bits1.length + i) hi'
    rw [show addr + (bits1.length + i) = addr + bits1.length + i from by omega] at heq
    simpa using heq

@[construction_api] lemma BitsFrom.append {σ : Store} {b : ℕ} {xs ys : Bits}
    (hx : BitsFrom σ b xs) (hy : BitsFrom σ (b + xs.length) ys) :
    BitsFrom σ b (xs ++ ys) := by
  intro i hi
  by_cases hix : i < xs.length
  · rw [List.getElem_append_left hix]
    exact hx i hix
  · have hiy : i - xs.length < ys.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right (by omega)]
    have h := hy (i - xs.length) hiy
    have he : b + xs.length + (i - xs.length) = b + i := by omega
    rw [he] at h
    exact h

@[construction_api] lemma bitsFrom_of_eq_on {σ σ' : Store} {addr : ℕ} {bits : Bits}
    (h : ∀ i, i < bits.length → σ' (addr + i) = σ (addr + i)) (hb : BitsFrom σ addr bits) :
    BitsFrom σ' addr bits := fun i hi => by rw [h i hi]; exact hb i hi


@[construction_api] lemma decodeUnaryProgAt_correct_append (cursorReg countReg doneReg : ℕ)
    (hcc : cursorReg ≠ countReg) (hcd : cursorReg ≠ doneReg) (hkd : countReg ≠ doneReg)
    (n bound addr c0 : ℕ) (σ : Store) (boundE : Expr) (rest : Bits)
    (hbE : boundE.eval σ = bound) (hbound : n + 1 ≤ bound)
    (hca : cursorReg < addr) (hka : countReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hk : σ countReg = c0) (hd : σ doneReg = 0)
    (hbits : BitsFrom σ addr (encodeNat n ++ rest)) :
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ cursorReg = addr + n + 1 ∧
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ countReg = c0 + n ∧
    (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ doneReg = 1 ∧
    ∀ r, r ≠ cursorReg → r ≠ countReg → r ≠ doneReg →
      (decodeUnaryProgAt cursorReg countReg doneReg boundE).eval σ r = σ r := by
  exact decodeUnaryProgAt_correct cursorReg countReg doneReg hcc hcd hkd n bound addr c0 σ boundE
    hbE hbound hca hka hda hc hk hd (bitsFrom_append σ addr _ _ hbits).1

@[construction_api] lemma scanFree_decodeUnaryProgAt (c k d : ℕ) (e : Expr) :
    ScanFree (decodeUnaryProgAt c k d e) := by
  simp [ScanFree, decodeUnaryProgAt, decodeUnaryStep]

@[construction_api] def readUnaryProgAt (c k d lr : ℕ) : Program :=
  .seq (.assign k (.const 0)) (.seq (.assign d (.const 0)) (decodeUnaryProgAt c k d (.reg lr)))

@[construction_api] lemma scanFree_readUnaryProgAt (c k d lr : ℕ) :
    ScanFree (readUnaryProgAt c k d lr) := by
  simp [readUnaryProgAt, ScanFree, scanFree_decodeUnaryProgAt]

@[construction_api] lemma readUnaryProgAt_avoids {c k d lr : ℕ} {P : ℕ → Prop}
    (hc : ¬ P c) (hk : ¬ P k) (hd : ¬ P d) :
    (readUnaryProgAt c k d lr).Avoids P := by
  simp [readUnaryProgAt, Program.Avoids, decodeUnaryProgAt, decodeUnaryStep, hc, hk, hd]

@[construction_api] lemma readUnaryProgAt_frame (c k d lr r : ℕ) (σ : Store)
    (hc : r ≠ c) (hk : r ≠ k) (hd : r ≠ d) :
    (readUnaryProgAt c k d lr).eval σ r = σ r :=
  (readUnaryProgAt_avoids (P := fun x => x = r) (c := c) (k := k) (d := d) (lr := lr)
    (fun h => hc h.symm) (fun h => hk h.symm) (fun h => hd h.symm)).eval_frame σ rfl

@[construction_api] lemma readUnaryProgAt_correct {c k d lr b n : ℕ} {rest : Bits} {σ : Store}
    (hcb : c < b) (hkb : k < b) (hdb : d < b) (hck : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hlk : lr ≠ k) (hld : lr ≠ d)
    (hc : σ c = b) (hN : n + 1 ≤ σ lr) (hbits : BitsFrom σ b (encodeNat n ++ rest)) :
    (readUnaryProgAt c k d lr).eval σ c = b + n + 1 ∧
    (readUnaryProgAt c k d lr).eval σ k = n ∧
    (readUnaryProgAt c k d lr).eval σ d = 1 ∧
    ∀ r, r ≠ c → r ≠ k → r ≠ d → (readUnaryProgAt c k d lr).eval σ r = σ r := by
  let τ := writeReg (writeReg σ k 0) d 0
  have heq (r : ℕ) (hr : b ≤ r) : τ r = σ r := by
    simp only [τ, writeReg_diff _ _ _ _ (show r ≠ d by omega),
      writeReg_diff _ _ _ _ (show r ≠ k by omega)]
  have hb : BitsFrom τ b (encodeNat n ++ rest) := bitsFrom_of_eq_on (fun i _ => heq _ (by omega)) hbits
  have hrun := decodeUnaryProgAt_correct_append c k d hck hcd hkd n (σ lr) b 0 τ (.reg lr) rest
    (by simp [Expr.eval, τ, writeReg_diff _ _ _ _ hld, writeReg_diff _ _ _ _ hlk]) hN
    hcb hkb hdb (by simp [τ, writeReg_diff _ _ _ _ hcd, writeReg_diff _ _ _ _ hck, hc])
    (by simp [τ, writeReg_diff _ _ _ _ hkd]) (by simp [τ]) hb
  simp only [readUnaryProgAt, eval_seq, eval_assign, Expr.eval]
  change (decodeUnaryProgAt c k d (.reg lr)).eval τ c = _ ∧
    (decodeUnaryProgAt c k d (.reg lr)).eval τ k = _ ∧
    (decodeUnaryProgAt c k d (.reg lr)).eval τ d = _ ∧ _
  refine ⟨hrun.1, by simpa using hrun.2.1, hrun.2.2.1, ?_⟩
  intro r hrc hrk hrd
  rw [hrun.2.2.2 r hrc hrk hrd, show τ r = σ r by simp [τ, writeReg_diff _ _ _ _ hrd, writeReg_diff _ _ _ _ hrk]]

@[construction_api] lemma readUnaryProgAt_frame_rest {c k d lr b n : ℕ} {rest : Bits}
    {σ : Store} (hcb : c < b) (hkb : k < b) (hdb : d < b)
    (hbits : BitsFrom σ b (encodeNat n ++ rest)) :
    (∀ r, b ≤ r → (readUnaryProgAt c k d lr).eval σ r = σ r) ∧
      BitsFrom ((readUnaryProgAt c k d lr).eval σ) (b + n + 1) rest := by
  have hf : ∀ r, b ≤ r → (readUnaryProgAt c k d lr).eval σ r = σ r := by
    intro r hr
    exact readUnaryProgAt_frame c k d lr r σ (by omega) (by omega) (by omega)
  refine ⟨hf, ?_⟩
  apply bitsFrom_of_eq_on (fun i _ => hf _ (by omega))
  simpa [encodeNat_length, Nat.add_assoc] using (bitsFrom_append σ b (encodeNat n) rest hbits).2

lemma unary_step_bounded_aux (B c k d : ℕ) (σ : Store)
    (hck : c ≠ k) (hcd : c ≠ d) (hidx : c ≤ B ∧ k ≤ B ∧ d ≤ B)
    (hc : σ c + 1 ≤ B) (hk : σ k + 1 ≤ B) :
    ProgramBoundedIn B σ (decodeUnaryStep c k d) := by
  have hcursorDone : writeReg σ d 1 c = σ c := writeReg_diff σ d 1 c hcd
  have hcursorCount : writeReg σ k (σ k + 1) c = σ c := writeReg_diff σ k (σ k + 1) c hck
  simp [decodeUnaryStep, ProgramBoundedIn, ExprBoundedIn, Expr.eval, hcursorDone, hcursorCount]
  omega

lemma unary_loop_bounds_aux (c k d : ℕ)
    (hck : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (n addr c0 B : ℕ) (τ : Store)
    (hca : c < addr) (hka : k < addr) (hda : d < addr)
    (hc : τ c = addr) (hk : τ k = c0) (hd : τ d = 0)
    (hbits : BitsFrom τ addr (encodeNat n))
    (hcursor : addr + n + 2 ≤ B) (hcount : c0 + n + 1 ≤ B) :
    ∀ m, (loopEval (decodeUnaryStep c k d) m τ) c + 1 ≤ B ∧
      (loopEval (decodeUnaryStep c k d) m τ) k + 1 ≤ B := by
  obtain ⟨hfc, hfk, hfd, _⟩ := decode_unary_loop_correct c k d hck hcd hkd n addr c0 τ
    hca hka hda hc hk hd hbits
  intro m
  by_cases hsmall : m < n + 1
  · have hcur := loopEval_decodeUnaryStep_cursor_le c k d hck hcd m τ
    have hcnt := loopEval_decodeUnaryStep_count_le c k d hck hkd m τ
    omega
  · have hsplit : m = (n + 1) + (m - (n + 1)) := by omega
    rw [hsplit, loopEval_add]
    rw [loopEval_decodeUnaryStep_done c k d _ (m - (n + 1)) (by rw [hfd]; decide)]
    constructor
    · rw [hfc]; omega
    · rw [hfk]; omega

@[construction_api] lemma decodeUnaryProgAt_bounded {c k d lr n addr c0 B : ℕ}
    {σ : Store} {rest : Bits}
    (hck : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hca : c < addr) (hka : k < addr) (hda : d < addr)
    (hc : σ c = addr) (hk : σ k = c0) (hd : σ d = 0)
    (hbits : BitsFrom σ addr (encodeNat n ++ rest))
    (hlr : lr ≤ B) (hcursor : addr + n + 2 ≤ B) (hcount : c0 + n + 1 ≤ B) :
    ProgramBoundedIn B σ (decodeUnaryProgAt c k d (.reg lr)) := by
  have hsteps := unary_loop_bounds_aux c k d hck hcd hkd n addr c0 B σ hca hka hda
    hc hk hd (bitsFrom_append σ addr _ _ hbits).1 hcursor hcount
  unfold decodeUnaryProgAt
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
  refine ⟨hlr, ?_⟩
  intro m hm
  exact unary_step_bounded_aux B c k d _ hck hcd ⟨by omega, by omega, by omega⟩
    (hsteps m).1 (hsteps m).2

@[construction_api] lemma readUnaryProgAt_bounded {c k d lr addr n B : ℕ}
    {rest : Bits} {σ : Store}
    (hca : c < addr) (hka : k < addr) (hda : d < addr)
    (hck : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hc : σ c = addr) (hbits : BitsFrom σ addr (encodeNat n ++ rest))
    (hlr : lr ≤ B) (hB : addr + n + 2 ≤ B) :
    ProgramBoundedIn B σ (readUnaryProgAt c k d lr) := by
  let τ := writeReg (writeReg σ k 0) d 0
  have heq (r : ℕ) (hr : addr ≤ r) : τ r = σ r := by
    simp only [τ, writeReg_diff _ _ _ _ (show r ≠ d by omega),
      writeReg_diff _ _ _ _ (show r ≠ k by omega)]
  have hb : BitsFrom τ addr (encodeNat n ++ rest) :=
    bitsFrom_of_eq_on (fun i _ => heq _ (by omega)) hbits
  have hp := decodeUnaryProgAt_bounded (lr := lr) (B := B) (c0 := 0) hck hcd hkd hca hka hda
    (by simp [τ, writeReg_diff _ _ _ _ hcd, writeReg_diff _ _ _ _ hck, hc])
    (by simp [τ, writeReg_diff _ _ _ _ hkd]) (by simp [τ]) hb hlr hB (by omega)
  unfold readUnaryProgAt
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_assign]
  exact ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, hp⟩⟩

end NPComplete.RAMToTM

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.BoundedWhile.WritesIn

/-!
A parameterized unary writer lets independent output producers share the same encoding program.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile NPComplete.BitEncoding

def unaryStep (base c : ℕ) : Program :=
  (Program.assignInd (.add (.const base) (.reg c)) (.const 0)).seq
    (Program.assign c (.add (.reg c) (.const 1)))

@[construction_api] def writeUnaryProgAt (base c k : ℕ) : Program :=
  (Program.forN (.reg k) (unaryStep base c)).seq
    ((Program.assignInd (.add (.const base) (.reg c)) (.const 1)).seq
      (Program.assign c (.add (.reg c) (.const 1))))

lemma unaryStep_apply (base c : ℕ) (τ : Store) (r : ℕ) (h : c ≠ base + τ c) :
    (unaryStep base c).eval τ r = if r = c then τ c + 1 else if r = base + τ c then 0 else τ r := by
  simp only [unaryStep, eval_seq, eval_assignInd, eval_assign, Expr.eval, writeReg]
  simp only [h, ite_false]

def UnaryInv (base c k p n : ℕ) (σ : Store) (i : ℕ) (τ : Store) : Prop :=
  τ c = p + i ∧ τ k = n ∧
  (∀ r, r ≠ c → (r < base + p ∨ base + p + i ≤ r) → τ r = σ r) ∧
    ∀ j < i, τ (base + p + j) = 0

lemma unaryInv_zero {base c k p n : ℕ} {σ : Store} (hp : σ c = p) (hn : σ k = n) :
    UnaryInv base c k p n σ 0 σ := by
  refine ⟨by simpa only [Nat.add_zero] using hp, hn, ?_, ?_⟩
  · intro r hr hrange; rfl
  · intro j hj; omega

lemma unaryInv_step {base c k p n i : ℕ} {σ τ : Store} (hc : c < base + p)
    (hk : k < base + p) (hck : c ≠ k)
    (hI : UnaryInv base c k p n σ i τ) :
    UnaryInv base c k p n σ (i + 1) ((unaryStep base c).eval τ) := by
  obtain ⟨hp, hn, hf, hz⟩ := hI
  have hc' : c ≠ base + τ c := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [unaryStep_apply _ _ _ _ hc']; simp only [ite_true, hp]; omega
  · rw [unaryStep_apply _ _ _ _ hc']
    simp only [show k ≠ c by omega, ite_false, show k ≠ base + τ c by omega, hn]
  · intro r hr hrange
    rw [unaryStep_apply _ _ _ _ hc']
    simp only [hr, ite_false, show r ≠ base + τ c by omega]
    apply hf r hr
    omega
  · intro j hj
    rw [unaryStep_apply _ _ _ _ hc']
    simp only [show base + p + j ≠ c by omega, ite_false, hp]
    by_cases hji : j = i
    · subst j; simp only [show base + p + i = base + (p + i) by omega, ite_true]
    · simp only [show base + p + j ≠ base + (p + i) by omega, ite_false]
      exact hz j (by omega)

lemma unary_loop {base c k p n : ℕ} {σ : Store} (hc : c < base + p) (hk : k < base + p)
    (hck : c ≠ k) (hp : σ c = p) (hn : σ k = n) :
    UnaryInv base c k p n σ n (loopEval (unaryStep base c) n σ) := by
  exact loopEval_index_inv (unaryStep base c) n (UnaryInv base c k p n σ)
    (fun i τ _ hi => unaryInv_step hc hk hck hi) n σ le_rfl (unaryInv_zero hp hn)

lemma unary_eval {base c k p n : ℕ} {σ : Store} (hc : c < base + p) (hk : k < base + p)
    (hck : c ≠ k) (hp : σ c = p) (hn : σ k = n) :
    (writeUnaryProgAt base c k).eval σ = writeReg
      (writeReg (loopEval (unaryStep base c) n σ) (base + (p + n)) 1) c (p + n + 1) := by
  have h := unary_loop hc hk hck hp hn
  simp only [writeUnaryProgAt, eval_seq, eval_forN, eval_assignInd, eval_assign, Expr.eval, hn, h.1,
    writeReg_diff _ _ _ _ (show c ≠ base + (p + n) by omega)]

@[construction_api] lemma writeUnaryProgAt_correct {base c k : ℕ} {σ : Store} (hck : c ≠ k)
    (hc : c < base + σ c) (hk : k < base + σ c) :
    (writeUnaryProgAt base c k).eval σ c = σ c + σ k + 1 ∧
    BitsFrom ((writeUnaryProgAt base c k).eval σ) (base + σ c) (encodeNat (σ k)) ∧
    (writeUnaryProgAt base c k).eval σ k = σ k := by
  have hI := unary_loop hc hk hck rfl rfl
  rw [unary_eval hc hk hck rfl rfl]
  refine ⟨by rw [writeReg_same], ?_, ?_⟩
  · intro i hi
    have hlen : i < σ k + 1 := by simpa only [encodeNat_length] using hi
    rw [encodeNat_getElem (σ k) i hi]
    by_cases hin : i = σ k
    · subst i
      rw [show base + σ c + σ k = base + (σ c + σ k) by omega,
        writeReg_diff _ _ _ _ (by omega), writeReg_same]
      simp only [decide_true, ↓reduceIte]
    · have hi' : i < σ k := by omega
      rw [writeReg_diff _ _ _ _ (by omega), writeReg_diff _ _ _ _ (by omega), hI.2.2.2 i hi']
      simp only [hin, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rw [writeReg_diff _ _ _ _ (by omega), writeReg_diff _ _ _ _ (by omega)]
    exact hI.2.1

@[construction_api] lemma writeUnaryProgAt_writesIn {base c k : ℕ} {σ : Store} (hck : c ≠ k)
    (hc : c < base + σ c) (hk : k < base + σ c) :
    WritesIn (fun r => r = c ∨ (base + σ c ≤ r ∧ r < base + σ c + σ k + 1))
      (writeUnaryProgAt base c k) σ := by
  let S : ℕ → Prop := fun r => r = c ∨ (base + σ c ≤ r ∧ r < base + σ c + σ k + 1)
  have hl : WritesIn S (.forN (.reg k) (unaryStep base c)) σ := by
    apply WritesIn.forN_of_indexed (UnaryInv base c k (σ c) (σ k) σ) (unaryInv_zero rfl rfl)
    intro i τ hi hI
    refine ⟨?_, unaryInv_step hc hk hck hI⟩
    simp only [unaryStep, WritesIn, Expr.eval, S]
    rw [hI.1]
    simp only [Expr.eval] at hi
    exact ⟨Or.inr ⟨by omega, by omega⟩, Or.inl trivial⟩
  have hI := unary_loop hc hk hck rfl rfl
  change WritesIn S (writeUnaryProgAt base c k) σ
  simp only [writeUnaryProgAt, WritesIn]
  refine ⟨hl, ?_⟩
  simp only [eval_forN, Expr.eval, hI.1, S]
  exact ⟨Or.inr ⟨by omega, by omega⟩, Or.inl trivial⟩

@[construction_api] lemma writeUnaryProgAt_frame {base c k r : ℕ} {σ : Store} (hck : c ≠ k)
    (hc : c < base + σ c) (hk : k < base + σ c) (hr : r ≠ c)
    (hout : r < base + σ c ∨ base + σ c + σ k + 1 ≤ r) :
    (writeUnaryProgAt base c k).eval σ r = σ r := by
  apply WritesIn.eval_frame _ _ (writeUnaryProgAt_writesIn hck hc hk)
  intro h
  rcases h with h | h
  · exact hr h
  · omega

@[construction_api] lemma scanFree_writeUnaryProgAt (base c k : ℕ) :
    ScanFree (writeUnaryProgAt base c k) := by
  simp only [writeUnaryProgAt, unaryStep, ScanFree, and_self]

@[construction_api] lemma writeUnaryProgAt_bounded {base c k B : ℕ} {σ : Store} (hck : c ≠ k)
    (hc : c < base + σ c) (hk : k < base + σ c) (hcb : c ≤ B) (hkb : k ≤ B)
    (h1 : 1 ≤ B) (hB : base + σ c + σ k + 1 ≤ B) :
    ProgramBoundedIn B σ (writeUnaryProgAt base c k) := by
  have hl : ProgramBoundedIn B σ (.forN (.reg k) (unaryStep base c)) := by
    apply programBoundedIn_forN_of_indexed B σ (.reg k) (unaryStep base c)
      (UnaryInv base c k (σ c) (σ k) σ) (unaryInv_zero rfl rfl)
    · intro i hi τ hI
      exact unaryInv_step hc hk hck hI
    · intro i hi hI
      simp only [Expr.eval] at hi
      have hv := hI.1
      simp only [unaryStep] at hv
      simp only [unaryStep, ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_assignInd, writeReg, hv]
      simp only [show ¬ c = base + (σ c + i) by omega, ite_false]
      omega
    · simp only [ExprBoundedIn]; omega
  have hI := unary_loop hc hk hck rfl rfl
  simp only [writeUnaryProgAt, programBoundedIn_seq_iff]
  refine ⟨hl, ?_⟩
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_forN, hI.1,
    eval_assignInd, writeReg_diff _ _ _ _ (show c ≠ base + (σ c + σ k) by omega)]
  omega

end NPComplete.RAMToTM

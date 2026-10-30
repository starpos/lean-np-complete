module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.BoundedWhile.WritesIn

/-!
# Parameterized forward copying

Moving an input to a higher address leaves room for fixed control registers without imposing a
fixed destination layout on the caller. The destination is evaluated before scratch is written.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

/-- Copy `src .. src + σ lr` to the address computed at entry by `dst`. -/
@[construction_api] def forwardCopyProg (src lr a b : ℕ) (dst : Expr) : Program :=
  let s : Expr := .add (.reg lr) (.const a)
  let d : Expr := .add (.reg lr) (.const b)
  let step : Program :=
    .seq (.assignInd (.regInd d) (.regInd (.regInd s)))
      (.seq (.assignInd s (.add (.regInd s) (.const 1)))
        (.assignInd d (.add (.regInd d) (.const 1))))
  .seq (.assignInd d dst)
    (.seq (.assignInd s (.const src)) (.forN (.reg lr) step))

/-- The source and scratch are disjoint and lie strictly below the destination. -/
@[construction_api] def ForwardCopyLayout (src lr a b N D : ℕ) : Prop :=
  0 < src ∧ src ≤ a ∧ src ≤ b ∧ a ≠ b ∧
    N + a ≠ lr ∧ N + b ≠ lr ∧ max (N + a) (N + b) < D ∧ lr < D

@[construction_api] lemma scanFree_forwardCopyProg (src lr a b : ℕ) (dst : Expr) :
    ScanFree (forwardCopyProg src lr a b dst) := by
  simp [forwardCopyProg, ScanFree]

def forwardCopyStep (lr a b : ℕ) : Program :=
  let s : Expr := .add (.reg lr) (.const a)
  let d : Expr := .add (.reg lr) (.const b)
  .seq (.assignInd (.regInd d) (.regInd (.regInd s)))
    (.seq (.assignInd s (.add (.regInd s) (.const 1)))
      (.assignInd d (.add (.regInd d) (.const 1))))

def ForwardCopyInv (src lr a b N D : ℕ) (σ : Store) (m : ℕ) (τ : Store) : Prop :=
  τ lr = N ∧ τ (N + a) = src + m ∧ τ (N + b) = D + m ∧
    (∀ r, r < src + N → r ≠ N + a → r ≠ N + b → τ r = σ r) ∧
    ∀ i < m, τ (D + i) = σ (src + i)

lemma forwardCopyStep_apply {src lr a b N D m : ℕ} {σ τ : Store}
    (hl : ForwardCopyLayout src lr a b N D)
    (hI : ForwardCopyInv src lr a b N D σ m τ) (hm : m < N) (r : ℕ) :
    (forwardCopyStep lr a b).eval τ r = if r = N + b then D + m + 1 else
      if r = N + a then src + m + 1 else if r = D + m then σ (src + m) else τ r := by
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  have hda : N + a < D := lt_of_le_of_lt (Nat.le_max_left _ _) hD
  have hdb : N + b < D := lt_of_le_of_lt (Nat.le_max_right _ _) hD
  obtain ⟨h0, h1, h2, hf, -⟩ := hI
  have hsrc : τ (src + m) = σ (src + m) := hf _ (by omega) (by omega) (by omega)
  simp only [forwardCopyStep, eval_seq, eval_assignInd, Expr.eval, writeReg, h0, h1, h2, hsrc]
  split_ifs <;> first | rfl | omega

lemma forwardCopyInv_step {src lr a b N D m : ℕ} {σ τ : Store}
    (hl : ForwardCopyLayout src lr a b N D)
    (hI : ForwardCopyInv src lr a b N D σ m τ) (hm : m < N) :
    ForwardCopyInv src lr a b N D σ (m + 1) ((forwardCopyStep lr a b).eval τ) := by
  have he := forwardCopyStep_apply hl hI hm
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  have hda : N + a < D := lt_of_le_of_lt (Nat.le_max_left _ _) hD
  have hdb : N + b < D := lt_of_le_of_lt (Nat.le_max_right _ _) hD
  obtain ⟨h0, h1, h2, hf, hc⟩ := hI
  refine ⟨?_, ?_, ?_, fun r hr hra hrb => ?_, fun i hi => ?_⟩
  · rw [he]; split_ifs <;> omega
  · rw [he]; split_ifs <;> omega
  · rw [he]; split_ifs <;> omega
  · rw [he]; split_ifs <;> first | omega | exact hf r hr hra hrb
  · rw [he]; by_cases him : i = m
    · subst i; simp only [show D + m ≠ N + b by omega, show D + m ≠ N + a by omega,
        ite_false, ite_true]
    · simp only [show D + i ≠ N + b by omega, show D + i ≠ N + a by omega,
        show D + i ≠ D + m by omega, ite_false]
      exact hc i (by omega)

lemma forwardCopyInv_zero {src lr a b N D : ℕ} {σ : Store} (hN : σ lr = N)
    (hl : ForwardCopyLayout src lr a b N D) :
    ForwardCopyInv src lr a b N D σ 0 (writeReg (writeReg σ (N + b) D) (N + a) src) := by
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  refine ⟨?_, ?_, ?_, fun r hr hra hrb => ?_, fun i hi => ?_⟩
  · rw [writeReg_diff _ _ _ _ (Ne.symm hla), writeReg_diff _ _ _ _ (Ne.symm hlb), hN]
  · simp
  · rw [writeReg_diff _ _ _ _ (by omega), writeReg_same]; simp
  · rw [writeReg_diff _ _ _ _ hra, writeReg_diff _ _ _ _ hrb]
  · omega

lemma forwardCopyProg_eval {src lr a b N : ℕ} {dst : Expr} {σ : Store}
    (hN : σ lr = N) (hl : ForwardCopyLayout src lr a b N (dst.eval σ)) :
    (forwardCopyProg src lr a b dst).eval σ =
      loopEval (forwardCopyStep lr a b) N
        (writeReg (writeReg σ (N + b) (dst.eval σ)) (N + a) src) := by
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  have h1 : writeReg σ (N + b) (dst.eval σ) lr = N := by
    rw [writeReg_diff _ _ _ _ (Ne.symm hlb), hN]
  have h2 : writeReg (writeReg σ (N + b) (dst.eval σ)) (N + a) src lr = N := by
    rw [writeReg_diff _ _ _ _ (Ne.symm hla), h1]
  simp only [forwardCopyProg, eval_seq, eval_assignInd, eval_forN, Expr.eval, hN, h1, h2,
    forwardCopyStep]

lemma forwardCopyStep_writesIn {src lr a b N D m : ℕ} {σ τ : Store}
    (hl : ForwardCopyLayout src lr a b N D)
    (hI : ForwardCopyInv src lr a b N D σ m τ) (hm : m < N) :
    WritesIn (fun r => r = N + a ∨ r = N + b ∨ D ≤ r ∧ r < D + N)
      (forwardCopyStep lr a b) τ := by
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  have hda : N + a < D := lt_of_le_of_lt (Nat.le_max_left _ _) hD
  have hdb : N + b < D := lt_of_le_of_lt (Nat.le_max_right _ _) hD
  obtain ⟨h0, h1, h2, hf, hc⟩ := hI
  simp only [forwardCopyStep, WritesIn, eval_assignInd, Expr.eval, writeReg, h0, h1, h2]
  simp only [show lr ≠ D + m by omega, show N + a ≠ D + m by omega,
    show lr ≠ N + a by omega, ite_false, h1]
  exact ⟨Or.inr (Or.inr ⟨by omega, by omega⟩), Or.inl trivial, Or.inr (Or.inl trivial)⟩

lemma forwardCopyStep_bounded {src lr a b N D m B : ℕ} {σ τ : Store}
    (hl : ForwardCopyLayout src lr a b N D) (hB : max lr (D + N) ≤ B)
    (hI : ForwardCopyInv src lr a b N D σ m τ) (hm : m < N) :
    ProgramBoundedIn B τ (forwardCopyStep lr a b) := by
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hl
  have hda : N + a < D := lt_of_le_of_lt (Nat.le_max_left _ _) hD
  have hdb : N + b < D := lt_of_le_of_lt (Nat.le_max_right _ _) hD
  obtain ⟨h0, h1, h2, hf, hc⟩ := hI
  simp only [forwardCopyStep, ProgramBoundedIn, ExprBoundedIn, Expr.eval, eval_assignInd,
    writeReg, h0, h1, h2]
  split_ifs <;> simp_all
  all_goals omega

lemma forwardCopyProg_inv {src lr a b N : ℕ} {dst : Expr} {σ : Store}
    (hN : σ lr = N) (hl : ForwardCopyLayout src lr a b N (dst.eval σ)) :
    ForwardCopyInv src lr a b N (dst.eval σ) σ N ((forwardCopyProg src lr a b dst).eval σ) := by
  rw [forwardCopyProg_eval hN hl]
  exact loopEval_index_inv (forwardCopyStep lr a b) N
    (ForwardCopyInv src lr a b N (dst.eval σ) σ)
    (fun _ _ hm hi => forwardCopyInv_step hl hi hm) N _ le_rfl (forwardCopyInv_zero hN hl)

@[construction_api] lemma forwardCopyProg_writesIn (src lr a b : ℕ) (dst : Expr) (σ : Store)
    (hl : ForwardCopyLayout src lr a b (σ lr) (dst.eval σ)) :
    WritesIn (fun r => r = σ lr + a ∨ r = σ lr + b ∨
      dst.eval σ ≤ r ∧ r < dst.eval σ + σ lr) (forwardCopyProg src lr a b dst) σ := by
  let N := σ lr
  let D := dst.eval σ
  let init := writeReg (writeReg σ (N + b) D) (N + a) src
  have h0 : σ lr = N := rfl
  have h1 : writeReg σ (N + b) D lr = N := by
    rw [writeReg_diff _ _ _ _ (Ne.symm hl.2.2.2.2.2.1), h0]
  have hi : ForwardCopyInv src lr a b N D σ 0 init := forwardCopyInv_zero h0 hl
  have h2 : init lr = N := hi.1
  have hw : WritesIn (fun r => r = N + a ∨ r = N + b ∨ D ≤ r ∧ r < D + N)
      (.forN (.reg lr) (forwardCopyStep lr a b)) init := by
    apply WritesIn.forN_of_indexed (ForwardCopyInv src lr a b N D σ) hi
    intro m τ hm hI
    have hm' : m < N := by simpa [Expr.eval, h2] using hm
    exact ⟨forwardCopyStep_writesIn hl hI hm', forwardCopyInv_step hl hI hm'⟩
  change WritesIn _ (.assignInd (.add (.reg lr) (.const b)) dst) σ ∧
    WritesIn _ (.assignInd (.add (.reg lr) (.const a)) (.const src))
      ((Program.assignInd (.add (.reg lr) (.const b)) dst).eval σ) ∧
    WritesIn _ (.forN (.reg lr) (forwardCopyStep lr a b))
      ((Program.assignInd (.add (.reg lr) (.const a)) (.const src)).eval
        ((Program.assignInd (.add (.reg lr) (.const b)) dst).eval σ))
  refine ⟨?_, ?_, ?_⟩
  · change σ lr + b = σ lr + a ∨ σ lr + b = σ lr + b ∨ _
    exact Or.inr (Or.inl rfl)
  · simp only [WritesIn, eval_assignInd, Expr.eval, h0]
    change writeReg σ (N + b) D lr + a = N + a ∨ _
    rw [h1]; exact Or.inl rfl
  · dsimp [D] at h1
    simpa only [eval_assignInd, Expr.eval, h0, h1, D, init] using hw

@[construction_api] lemma forwardCopyProg_frame (src lr a b : ℕ) (dst : Expr) (σ : Store)
    (hl : ForwardCopyLayout src lr a b (σ lr) (dst.eval σ)) (r : ℕ)
    (ha : r ≠ σ lr + a) (hb : r ≠ σ lr + b)
    (hr : r < dst.eval σ ∨ dst.eval σ + σ lr ≤ r) :
    (forwardCopyProg src lr a b dst).eval σ r = σ r := by
  apply WritesIn.eval_frame _ _ (forwardCopyProg_writesIn src lr a b dst σ hl)
  intro h
  rcases h with h | h | ⟨h1, h2⟩
  · exact ha h
  · exact hb h
  · omega

@[construction_api] lemma forwardCopyProg_correct (src lr a b : ℕ) (dst : Expr)
    (σ : Store) (bits : NPComplete.BitEncoding.Bits) (hlen : σ lr = bits.length)
    (hlayout : ForwardCopyLayout src lr a b bits.length (dst.eval σ))
    (hbits : BitsFrom σ src bits) :
    let τ := (forwardCopyProg src lr a b dst).eval σ
    BitsFrom τ (dst.eval σ) bits ∧
      (∀ i < bits.length, τ (src + i) = σ (src + i)) ∧ τ 0 = σ 0 := by
  have hinv := forwardCopyProg_inv hlen hlayout
  obtain ⟨hs, ha, hb, hab, hla, hlb, hD, hlr⟩ := hlayout
  obtain ⟨_, _, _, hf, hc⟩ := hinv
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [hc i hi]; exact hbits i hi
  · exact hf _ (by omega) (by omega) (by omega)
  · exact hf _ (by omega) (by omega) (by omega)

@[construction_api] lemma forwardCopyProg_programBoundedIn (src lr a b B : ℕ)
    (dst : Expr) (σ : Store) (hl : ForwardCopyLayout src lr a b (σ lr) (dst.eval σ))
    (hdst : ExprBoundedIn B σ dst) (hB : max lr (dst.eval σ + σ lr) ≤ B) :
    ProgramBoundedIn B σ (forwardCopyProg src lr a b dst) := by
  let N := σ lr
  let D := dst.eval σ
  let init := writeReg (writeReg σ (N + b) D) (N + a) src
  have h0 : σ lr = N := rfl
  have h1 : writeReg σ (N + b) D lr = N := by
    rw [writeReg_diff _ _ _ _ (Ne.symm hl.2.2.2.2.2.1), h0]
  have hi : ForwardCopyInv src lr a b N D σ 0 init := forwardCopyInv_zero h0 hl
  have h2 : init lr = N := hi.1
  have hb : max lr (D + N) ≤ B := hB
  have hda : N + a < D := lt_of_le_of_lt (Nat.le_max_left _ _) hl.2.2.2.2.2.2.1
  have hdb : N + b < D := lt_of_le_of_lt (Nat.le_max_right _ _) hl.2.2.2.2.2.2.1
  have hloop : ProgramBoundedIn B init (.forN (.reg lr) (forwardCopyStep lr a b)) := by
    apply programBoundedIn_forN_of_indexed B init (.reg lr) (forwardCopyStep lr a b)
      (ForwardCopyInv src lr a b N D σ) hi
    · intro m hm τ hI
      exact forwardCopyInv_step hl hI (by simpa [Expr.eval, h2] using hm)
    · intro m hm hI
      exact forwardCopyStep_bounded hl hb hI (by simpa [Expr.eval, h2] using hm)
    · simp only [ExprBoundedIn]; omega
  change ProgramBoundedIn B σ (.assignInd (.add (.reg lr) (.const b)) dst) ∧
    ProgramBoundedIn B ((Program.assignInd (.add (.reg lr) (.const b)) dst).eval σ)
      (.assignInd (.add (.reg lr) (.const a)) (.const src)) ∧
    ProgramBoundedIn B
      ((Program.assignInd (.add (.reg lr) (.const a)) (.const src)).eval
        ((Program.assignInd (.add (.reg lr) (.const b)) dst).eval σ))
      (.forN (.reg lr) (forwardCopyStep lr a b))
  refine ⟨?_, ?_, ?_⟩
  · simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval, h0]
    exact ⟨⟨by omega, by omega, by omega⟩, hdst, by omega⟩
  · simp only [ProgramBoundedIn, ExprBoundedIn, eval_assignInd, Expr.eval, h0]
    change (lr ≤ B ∧ a ≤ B ∧ writeReg σ (N + b) D lr + a ≤ B) ∧ src ≤ B ∧
      writeReg σ (N + b) D lr + a ≤ B
    rw [h1]
    have ha := hl.2.1
    omega
  · dsimp [D] at h1
    simpa only [eval_assignInd, Expr.eval, h0, h1, D, init] using hloop

@[construction_api] lemma forwardCopyProg_correct_bitInputStore
    (bits : NPComplete.BitEncoding.Bits) (dst : Expr)
    (hgap : bits.length + 2 < dst.eval (bitInputStore bits)) :
    let σ := bitInputStore bits
    let τ := (forwardCopyProg 1 0 1 2 dst).eval σ
    BitsFrom τ (dst.eval σ) bits ∧ ∀ r ≤ bits.length, τ r = σ r := by
  have hl : ForwardCopyLayout 1 0 1 2 bits.length (dst.eval (bitInputStore bits)) := by
    simp only [ForwardCopyLayout, max_lt_iff]
    omega
  have hc := forwardCopyProg_correct 1 0 1 2 dst (bitInputStore bits) bits
    (bitInputStore_zero bits) hl (bits_from_bitInputStore bits)
  refine ⟨hc.1, fun r hr => ?_⟩
  have hf := forwardCopyProg_frame 1 0 1 2 dst (bitInputStore bits)
    (by simpa only [bitInputStore_zero] using hl) r
  apply hf <;> simp only [bitInputStore_zero] <;> omega

@[construction_api] lemma forwardCopyProg_programBoundedIn_bitInputStore
    (bits : NPComplete.BitEncoding.Bits) (dst : Expr) (B : ℕ)
    (hgap : bits.length + 2 < dst.eval (bitInputStore bits))
    (hdst : ExprBoundedIn B (bitInputStore bits) dst)
    (hB : dst.eval (bitInputStore bits) + bits.length ≤ B) :
    ProgramBoundedIn B (bitInputStore bits) (forwardCopyProg 1 0 1 2 dst) := by
  apply forwardCopyProg_programBoundedIn 1 0 1 2 B dst (bitInputStore bits)
  · simp only [ForwardCopyLayout, bitInputStore_zero, max_lt_iff]
    omega
  · exact hdst
  · simp only [bitInputStore_zero, max_eq_right (Nat.zero_le _)]
    exact hB

end NPComplete.RAMToTM

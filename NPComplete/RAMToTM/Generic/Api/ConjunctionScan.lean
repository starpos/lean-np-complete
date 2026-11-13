module

public import NPComplete.RAMToTM.Generic.Api.Computation
meta import NPComplete.Meta.ApiLayer

/-!
Conjunction scans compose bounded per-index computations into a bounded loop while preserving
its frame and collecting the Boolean results in an accumulator.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- Multiply the flag into the accumulator. -/
@[construction_api] def mulAcc (acc flag : ℕ) : Program := .assign acc (.mul (.reg acc) (.reg flag))

/-- Start the accumulator at `1`, run the body once per index `0..n-1` and multiply the flag it
leaves into the accumulator: the accumulator ends as the conjunction of the flags. -/
@[construction_api] def accAll (i c acc flag : ℕ) (body : Program) : Program :=
  .seq (.assign acc (.const 1)) (forCnt i c (.seq body (mulAcc acc flag)))

@[construction_api] lemma ScanFree_accAll {i c acc flag : ℕ} {body : Program} (h : ScanFree body) :
    ScanFree (accAll i c acc flag body) := ⟨trivial, ScanFree_forCnt ⟨h, trivial⟩⟩

/-- The loop description: registers, bounds, context and the per-index `Comp` of the body. -/
@[construction_api] structure AccStep (B : ℕ) (Q : Store → Prop) (Wb : ℕ → Prop) (i c acc flag : ℕ) (body : Program)
    (n : ℕ) (G : ℕ → Bool) : Prop where
  i_ne_c : i ≠ c
  i_ne_acc : i ≠ acc
  acc_ne_c : acc ≠ c
  flag_ne_acc : flag ≠ acc
  i_le : i ≤ B
  c_le : c ≤ B
  acc_le : acc ≤ B
  flag_le : flag ≤ B
  n_lt : n < B
  not_i : ¬ Wb i
  not_acc : ¬ Wb acc
  sf : ScanFree body
  stab : ∀ τ τ', Q τ → SameOff (fun r => Wb r ∨ r = acc ∨ r = i) τ τ' → Q τ'
  count : ∀ τ, Q τ → τ c = n
  body : ∀ j < n, Comp B (fun τ => Q τ ∧ τ i = j) body Wb [(flag, G j)]

@[construction_api] lemma bool_ite_mul (b b' : Bool) :
    (if b then 1 else 0) * (if b' then 1 else 0) = if b && b' then 1 else (0 : ℕ) := by
  cases b <;> cases b' <;> simp

@[construction_api] lemma allLt_succ (G : ℕ → Bool) (j : ℕ) :
    decide (∀ m < j + 1, G m = true) = (decide (∀ m < j, G m = true) && G j) := by
  rw [Bool.eq_iff_iff]
  simp [Nat.forall_lt_succ_right]

@[construction_api] lemma AccStep.keep {B : ℕ} {Q : Store → Prop} {Wb : ℕ → Prop} {i c acc flag : ℕ} {body : Program}
    {n : ℕ} {G : ℕ → Bool} (h : AccStep B Q Wb i c acc flag body n G) {j : ℕ} (hj : j < n)
    {τ : Store} (hi : τ i = j) (hq : Q τ) (hv : StoreValuesLe B τ) (hacc : τ acc ≤ 1) :
    let τ' := (Program.seq body (mulAcc acc flag)).eval τ
    ProgramBoundedIn B τ (.seq body (mulAcc acc flag)) ∧
      SameOff (fun r => Wb r ∨ r = acc ∨ r = i) τ τ' ∧
      τ' i = j ∧ τ' acc = τ acc * (if G j then 1 else 0) := by
  obtain ⟨hb, hs, hf'⟩ := h.body j hj τ ⟨hq, hi⟩ hv
  have hf : (body.eval τ) flag = if G j then 1 else 0 := hf' (flag, G j) (List.mem_singleton_self _)
  have h1 : (body.eval τ) acc = τ acc := hs acc h.not_acc
  have h2 : (body.eval τ) i = j := by rw [← hi]; exact hs i h.not_i
  have hfl : (body.eval τ) flag ≤ 1 := by rw [hf]; split <;> omega
  have hn := h.n_lt
  have hprod : (body.eval τ) acc * (body.eval τ) flag ≤ 1 := by
    rw [h1]; simpa using Nat.mul_le_mul hacc hfl
  have hB1 : 1 ≤ B := by omega
  have hmul : ProgramBoundedIn B (body.eval τ) (mulAcc acc flag) :=
    ⟨h.acc_le, h.acc_le, h.flag_le, hprod.trans hB1⟩
  refine ⟨⟨hb, hmul⟩, ?_, ?_, ?_⟩
  · intro r hr
    simp only [eval_seq, mulAcc, eval_assign]
    rw [writeReg_diff _ _ _ _ (fun e => hr (Or.inr (Or.inl e)))]
    exact hs r fun hw => hr (Or.inl hw)
  · simp only [eval_seq, mulAcc, eval_assign]
    rw [writeReg_diff _ _ _ _ h.i_ne_acc, h2]
  · simp only [eval_seq, mulAcc, eval_assign, Expr.eval, writeReg_same, h1, hf]

/-- The progress predicate of a conjunction scan: the accumulator is the conjunction so far and
only the permitted registers changed since the start of the loop. -/
@[construction_api] def AccProg (S : ℕ → Prop) (acc : ℕ) (G : ℕ → Bool) (σ1 : Store) (j : ℕ) (τ : Store) : Prop :=
  τ acc = (if decide (∀ m < j, G m = true) then 1 else 0) ∧ SameOff S σ1 τ

@[construction_api] lemma AccStep.cntStep {B : ℕ} {Q : Store → Prop} {Wb : ℕ → Prop} {i c acc flag : ℕ}
    {body : Program} {n : ℕ} {G : ℕ → Bool} (h : AccStep B Q Wb i c acc flag body n G)
    (σ1 : Store) :
    CntStep i c (.seq body (mulAcc acc flag)) n B Q
      (AccProg (fun r => Wb r ∨ r = acc ∨ r = i) acc G σ1) where
  ne_cnt := h.i_ne_c
  i_le := h.i_le
  n_lt := h.n_lt
  cnt_le := h.c_le
  sf := ⟨h.sf, trivial⟩
  qi τ v hq := h.stab τ _ hq (SameOff.writeReg (Or.inr (Or.inr rfl)) v)
  pi j τ v hp := ⟨by rw [writeReg_diff _ _ _ _ h.i_ne_acc.symm]; exact hp.1,
    hp.2.trans (SameOff.writeReg (Or.inr (Or.inr rfl)) v)⟩
  count τ hq := h.count τ hq
  keep j hj τ hi hq hp hv := by
    have hacc : τ acc ≤ 1 := by rw [hp.1]; split <;> omega
    obtain ⟨-, hs, hi', hacc'⟩ := h.keep hj hi hq hv hacc
    refine ⟨h.stab τ _ hq hs, hi', ?_, hp.2.trans hs⟩
    rw [hacc', hp.1, allLt_succ, bool_ite_mul]
  bnd j hj τ hi hq hp hv := by
    have hacc : τ acc ≤ 1 := by rw [hp.1]; split <;> omega
    exact (h.keep hj hi hq hv hacc).1

/-- **Conjunction scan.** After `accAll` the accumulator holds the conjunction of the per-index
flags, the loop is bounded, and only the written registers, the accumulator and the index changed. -/
@[construction_api] lemma accAll_comp {B : ℕ} {Q : Store → Prop} {Wb : ℕ → Prop} {i c acc flag : ℕ} {body : Program}
    {n : ℕ} {G : ℕ → Bool} (h : AccStep B Q Wb i c acc flag body n G) :
    Comp B Q (accAll i c acc flag body) (fun r => Wb r ∨ r = acc ∨ r = i)
      [(acc, decide (∀ j < n, G j = true))] := by
  intro σ hq hv
  set σ1 := writeReg σ acc 1 with hσ1
  have hn := h.n_lt
  have hq1 : Q σ1 := h.stab σ σ1 hq (SameOff.writeReg (Or.inr (Or.inl rfl)) 1)
  have hv1 : StoreValuesLe B σ1 := storeValuesLe_writeReg hv acc (by omega)
  have hP : AccProg (fun r => Wb r ∨ r = acc ∨ r = i) acc G σ1 0 σ1 :=
    ⟨by simp [hσ1], SameOff.refl _ _⟩
  have hc := h.cntStep σ1
  have hev := forCnt_eval hc σ1 hq1 hP hv1
  have hbd := forCnt_bounded hc σ1 hq1 hP hv1
  have hfin : (accAll i c acc flag body).eval σ = (forCnt i c (.seq body (mulAcc acc flag))).eval σ1 := by
    simp [accAll, hσ1, Expr.eval]
  have h1B : 1 ≤ B := by omega
  refine ⟨⟨⟨h.acc_le, h1B⟩, ?_⟩, ?_, ?_⟩
  · simpa [eval_assign, Expr.eval] using hbd
  · rw [hfin]
    exact (SameOff.writeReg (Or.inr (Or.inl rfl)) 1).trans hev.2.1.2
  · intro q hq
    obtain rfl := List.mem_singleton.1 hq
    rw [hfin]
    exact hev.2.1.1

end NPComplete.RAMToTM

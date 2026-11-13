module

public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded
public import NPComplete.RAMToTM.Generic.Api.BoundedInMono
meta import NPComplete.Meta.ApiLayer

/-!
A counted loop separates the index and count registers. An invariant and a per-iteration summary
establish both its result and its resource bound without repeating the loop induction.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- Increase the index register. -/
@[construction_api] def incr (i : ℕ) : Program := .assign i (.add (.reg i) (.const 1))

@[construction_api] lemma incr_eval (i : ℕ) (σ : Store) :
    (incr i).eval σ = writeReg σ i (σ i + 1) := by
  simp [incr, Expr.eval]

@[construction_api] lemma ScanFree_incr (i : ℕ) : ScanFree (incr i) := trivial

@[construction_api] lemma incr_bounded {i B : ℕ} {τ : Store} {m : ℕ}
    (hi : i ≤ B) (hm : m + 1 ≤ B) (h : τ i = m) : ProgramBoundedIn B τ (incr i) := by
  simp only [incr, ProgramBoundedIn, ExprBoundedIn, Expr.eval, h]
  exact ⟨hi, hi, by omega, hm⟩

/-- Run `body` once per index, with the count read from register `c`. -/
@[construction_api] def forCnt (i c : ℕ) (body : Program) : Program :=
  .seq (.assign i (.const 0)) (.forN (.reg c) (.seq body (incr i)))

@[construction_api] lemma ScanFree_forCnt {i c : ℕ} {body : Program} (h : ScanFree body) :
    ScanFree (forCnt i c body) := ⟨trivial, h, trivial⟩

@[construction_api] lemma loopEval_indexed (body : Program) (n : ℕ) (I : ℕ → Store → Prop)
    (σ : Store) (h0 : I 0 σ) (hstep : ∀ i < n, ∀ τ, I i τ → I (i + 1) (body.eval τ)) :
    ∀ k ≤ n, I k (loopEval body k σ) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    rw [loopEval_succ_snoc]
    exact hstep k (by omega) _ (ih (by omega))

@[construction_api] lemma storeValuesLe_writeReg {B : ℕ} {σ : Store} (h : StoreValuesLe B σ)
    (r : ℕ) {v : ℕ} (hv : v ≤ B) : StoreValuesLe B (writeReg σ r v) := by
  intro x
  by_cases hx : x = r
  · subst hx; simpa using hv
  · rw [writeReg_diff _ _ _ _ hx]; exact h x

/-- A per-iteration summary preserving `Q` and advancing `P`. -/
@[construction_api] structure CntStep (i c : ℕ) (body : Program) (n B : ℕ) (Q : Store → Prop)
    (P : ℕ → Store → Prop) : Prop where
  ne_cnt : i ≠ c
  i_le : i ≤ B
  n_lt : n < B
  cnt_le : c ≤ B
  sf : ScanFree body
  qi : ∀ τ v, Q τ → Q (writeReg τ i v)
  pi : ∀ j τ v, P j τ → P j (writeReg τ i v)
  count : ∀ τ, Q τ → τ c = n
  keep : ∀ j < n, ∀ τ, τ i = j → Q τ → P j τ → StoreValuesLe B τ →
    Q (body.eval τ) ∧ (body.eval τ) i = j ∧ P (j + 1) (body.eval τ)
  bnd : ∀ j < n, ∀ τ, τ i = j → Q τ → P j τ → StoreValuesLe B τ → ProgramBoundedIn B τ body

@[construction_api] lemma CntStep.inv {i c : ℕ} {body : Program} {n B : ℕ}
    {Q : Store → Prop} {P : ℕ → Store → Prop} (h : CntStep i c body n B Q P) (σ : Store)
    (hQ : Q σ) (hP : P 0 σ) (hv : StoreValuesLe B σ) :
    ∀ k ≤ n, (loopEval (.seq body (incr i)) k (writeReg σ i 0)) i = k ∧
      Q (loopEval (.seq body (incr i)) k (writeReg σ i 0)) ∧
      P k (loopEval (.seq body (incr i)) k (writeReg σ i 0)) ∧
      StoreValuesLe B (loopEval (.seq body (incr i)) k (writeReg σ i 0)) := by
  have h1 : 1 ≤ B := by have := h.n_lt; omega
  refine loopEval_indexed (.seq body (incr i)) n
    (fun j τ => τ i = j ∧ Q τ ∧ P j τ ∧ StoreValuesLe B τ) (writeReg σ i 0)
    ⟨by simp, h.qi σ 0 hQ, h.pi 0 σ 0 hP, storeValuesLe_writeReg hv i (by omega)⟩
    (fun j hj τ ⟨hi, hq, hp, hvτ⟩ => ?_)
  obtain ⟨q1, i1, p1⟩ := h.keep j hj τ hi hq hp hvτ
  have hb := h.bnd j hj τ hi hq hp hvτ
  have hv1 := program_eval_storeValuesLe τ body h1 hvτ hb h.sf
  have hlt : j + 1 ≤ B := by have := h.n_lt; omega
  have hv2 : StoreValuesLe B (writeReg (body.eval τ) i (j + 1)) :=
    storeValuesLe_writeReg hv1 i hlt
  simp only [eval_seq, incr_eval, i1, writeReg_same]
  exact ⟨trivial, h.qi _ _ q1, h.pi _ _ _ p1, hv2⟩

/-- The loop preserves the context, advances the invariant and keeps the store bounded. -/
@[construction_api] lemma forCnt_eval {i c : ℕ} {body : Program} {n B : ℕ} {Q : Store → Prop}
    {P : ℕ → Store → Prop} (h : CntStep i c body n B Q P) (σ : Store) (hQ : Q σ) (hP : P 0 σ)
    (hv : StoreValuesLe B σ) :
    let τ := (forCnt i c body).eval σ
    Q τ ∧ P n τ ∧ τ i = n ∧ StoreValuesLe B τ := by
  have hcnt : (writeReg σ i 0) c = n := by
    rw [writeReg_diff _ _ _ _ h.ne_cnt.symm]
    exact h.count σ hQ
  have hinv := h.inv σ hQ hP hv n le_rfl
  simp only [forCnt, eval_seq, eval_assign, eval_forN, Expr.eval, hcnt]
  exact ⟨hinv.2.1, hinv.2.2.1, hinv.1, hinv.2.2.2⟩

/-- The same per-iteration summary bounds the loop. -/
@[construction_api] lemma forCnt_bounded {i c : ℕ} {body : Program} {n B : ℕ} {Q : Store → Prop}
    {P : ℕ → Store → Prop} (h : CntStep i c body n B Q P) (σ : Store) (hQ : Q σ) (hP : P 0 σ)
    (hv : StoreValuesLe B σ) : ProgramBoundedIn B σ (forCnt i c body) := by
  have hcnt : (writeReg σ i 0) c = n := by
    rw [writeReg_diff _ _ _ _ h.ne_cnt.symm]
    exact h.count σ hQ
  refine ⟨⟨h.i_le, Nat.zero_le _⟩, ?_⟩
  simp only [eval_assign]
  refine ⟨h.cnt_le, fun m hm => ?_⟩
  simp only [Expr.eval, hcnt] at hm
  simp only [Expr.eval]
  obtain ⟨hi, hq, hp, hvτ⟩ := h.inv σ hQ hP hv m hm.le
  refine ⟨h.bnd m hm _ hi hq hp hvτ, ?_⟩
  obtain ⟨q1, i1, p1⟩ := h.keep m hm _ hi hq hp hvτ
  have h1 := h.n_lt
  exact incr_bounded h.i_le (by omega) i1

end NPComplete.RAMToTM

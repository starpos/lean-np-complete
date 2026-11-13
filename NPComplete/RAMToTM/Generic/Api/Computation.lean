module

public import NPComplete.RAMToTM.Generic.Api.SameOff
public import NPComplete.RAMToTM.Generic.Api.BoolExpr
public import NPComplete.RAMToTM.Generic.Api.CountedLoop
meta import NPComplete.Meta.ApiLayer

/-!
Boolean computations can be composed using a common contract for resource bounds, write sets and
result registers, without exposing their implementations to callers.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- A bounded computation with a write set and Boolean result registers. -/
@[construction_api] def Comp (B : ℕ) (Q : Store → Prop) (p : Program) (Wr : ℕ → Prop)
    (res : List (ℕ × Bool)) : Prop :=
  ∀ τ, Q τ → StoreValuesLe B τ →
    ProgramBoundedIn B τ p ∧ SameOff Wr τ (p.eval τ) ∧
      ∀ q ∈ res, (p.eval τ) q.1 = if q.2 then 1 else 0

@[construction_api] lemma Comp.mono_ctx {B : ℕ} {Q Q' : Store → Prop} {Wr : ℕ → Prop}
    {p : Program} {res : List (ℕ × Bool)} (h : Comp B Q p Wr res) (hQ : ∀ τ, Q' τ → Q τ) :
    Comp B Q' p Wr res := fun τ hτ hv => h τ (hQ τ hτ) hv

@[construction_api] lemma Comp.mono_wr {B : ℕ} {Q : Store → Prop} {Wr Wr' : ℕ → Prop}
    {p : Program} {res : List (ℕ × Bool)} (h : Comp B Q p Wr res) (hW : ∀ r, Wr r → Wr' r) :
    Comp B Q p Wr' res := fun τ hτ hv => by
  obtain ⟨h1, h2, h3⟩ := h τ hτ hv
  exact ⟨h1, h2.mono hW, h3⟩

@[construction_api] lemma Comp.assign {B : ℕ} {Q : Store → Prop} {flag : ℕ} {e : Expr} {b : Bool}
    (hfl : flag ≤ B) (he : ∀ τ, Q τ → StoreValuesLe B τ → BX B τ b e) :
    Comp B Q (.assign flag e) (fun r => r = flag) [(flag, b)] := fun τ hq hv => by
  obtain ⟨h1, h2⟩ := he τ hq hv
  refine ⟨⟨hfl, h1⟩, fun r hr => ?_, fun q hq' => ?_⟩
  · simp only [eval_assign]
    exact writeReg_diff _ _ _ _ hr
  · obtain rfl := List.mem_singleton.1 hq'
    simp only [eval_assign, writeReg_same]
    exact h2

/-- Run two computations; the results of the first must survive the second. -/
@[construction_api] lemma Comp.seq {B : ℕ} {Q : Store → Prop} {Wr1 Wr2 : ℕ → Prop}
    {p1 p2 : Program} {res1 res2 : List (ℕ × Bool)} (hB : 1 ≤ B) (h1 : Comp B Q p1 Wr1 res1)
    (h2 : Comp B Q p2 Wr2 res2) (hsf : ScanFree p1)
    (hstab : ∀ τ τ', Q τ → SameOff Wr1 τ τ' → Q τ') (hres : ∀ q ∈ res1, ¬ Wr2 q.1) :
    Comp B Q (.seq p1 p2) (fun r => Wr1 r ∨ Wr2 r) (res1 ++ res2) := fun τ hq hv => by
  obtain ⟨hb1, hs1, hf1⟩ := h1 τ hq hv
  have hq' := hstab τ _ hq hs1
  have hv' := program_eval_storeValuesLe τ p1 hB hv hb1 hsf
  obtain ⟨hb2, hs2, hf2⟩ := h2 _ hq' hv'
  refine ⟨⟨hb1, hb2⟩, fun r hr => ?_, fun q hq'' => ?_⟩
  · simp only [eval_seq]
    rw [hs2 r fun hw => hr (Or.inr hw)]
    exact hs1 r fun hw => hr (Or.inl hw)
  · simp only [eval_seq]
    rcases List.mem_append.1 hq'' with hm | hm
    · rw [hs2 q.1 (hres q hm)]
      exact hf1 q hm
    · exact hf2 q hm

/-- Assign an expression of the earlier results. -/
@[construction_api] lemma Comp.seq_assign {B : ℕ} {Q : Store → Prop} {Wr : ℕ → Prop}
    {p : Program} {res : List (ℕ × Bool)} {flag : ℕ} {b : Bool} {e : Expr}
    (hB : 1 ≤ B) (hfl : flag ≤ B) (hp : Comp B Q p Wr res) (hsf : ScanFree p)
    (hstab : ∀ τ τ', Q τ → SameOff Wr τ τ' → Q τ') (hnew : ∀ q ∈ res, q.1 ≠ flag)
    (he : ∀ τ, Q τ → StoreValuesLe B τ → (∀ q ∈ res, τ q.1 = if q.2 then 1 else 0) →
      BX B τ b e) :
    Comp B Q (.seq p (.assign flag e)) (fun r => Wr r ∨ r = flag) ((flag, b) :: res) :=
  fun τ hq hv => by
  obtain ⟨hb, hs, hf⟩ := hp τ hq hv
  have hq' := hstab τ _ hq hs
  have hv' := program_eval_storeValuesLe τ p hB hv hb hsf
  obtain ⟨h1, h2⟩ := he _ hq' hv' hf
  refine ⟨⟨hb, hfl, h1⟩, fun r hr => ?_, fun q hq'' => ?_⟩
  · simp only [eval_seq, eval_assign]
    rw [writeReg_diff _ _ _ _ (fun e => hr (Or.inr e))]
    exact hs r fun hw => hr (Or.inl hw)
  · simp only [eval_seq, eval_assign]
    rcases List.mem_cons.1 hq'' with rfl | hm
    · simp only [writeReg_same]
      exact h2
    · rw [writeReg_diff _ _ _ _ (hnew q hm)]
      exact hf q hm

@[construction_api] lemma Comp.sub_res {B : ℕ} {Q : Store → Prop} {Wr : ℕ → Prop}
    {p : Program} {res res' : List (ℕ × Bool)} (h : Comp B Q p Wr res)
    (hs : ∀ q ∈ res', q ∈ res) : Comp B Q p Wr res' := fun τ hq hv => by
  obtain ⟨h1, h2, h3⟩ := h τ hq hv
  exact ⟨h1, h2, fun q hm => h3 q (hs q hm)⟩

end NPComplete.RAMToTM

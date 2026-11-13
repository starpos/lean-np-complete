module

public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded
public import NPComplete.RAMToTM.Generic.Api.BoundedInMono
meta import NPComplete.Meta.ApiLayer

/-!
Boolean computations repeatedly require both an operand bound and a 0/1 result. Bundling those
facts makes the resource obligations of composite expressions reusable.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- The expression is bounded and evaluates to `1` when `b` holds and to `0` otherwise. -/
@[construction_api] def BX (B : ℕ) (σ : Store) (b : Bool) (e : Expr) : Prop :=
  ExprBoundedIn B σ e ∧ e.eval σ = if b then 1 else 0

variable {B : ℕ} {σ : Store} {b b' : Bool} {e e' : Expr}

@[construction_api] lemma BX.const (b : Bool) (hB : 1 ≤ B) :
    BX B σ b (.const (if b then 1 else 0)) := by
  cases b <;> simp [BX, ExprBoundedIn, Expr.eval, hB]

@[construction_api] lemma BX.not (h : BX B σ b e) (hB : 1 ≤ B) :
    BX B σ (!b) (.sub (.const 1) e) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨hB, h1, hB⟩, ?_⟩
  cases b <;> simp [Expr.eval, h2]

@[construction_api] lemma BX.and (h : BX B σ b e) (h' : BX B σ b' e') (hB : 1 ≤ B) :
    BX B σ (b && b') (.mul e e') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨⟨h1, h1', ?_⟩, ?_⟩ <;> cases b <;> cases b' <;> simp [Expr.eval, h2, h2', hB]

@[construction_api] lemma BX.or (h : BX B σ b e) (h' : BX B σ b' e') (hB : 2 ≤ B) :
    BX B σ (b || b') (.sub (.add e e') (.mul e e')) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨⟨⟨h1, h1', ?_⟩, ⟨h1, h1', ?_⟩, ?_⟩, ?_⟩ <;> cases b <;> cases b' <;>
    simp [Expr.eval, h2, h2'] <;> omega

@[construction_api] lemma BX.eqReg {r c : ℕ} (hr : r ≤ B) (hc : c ≤ B) :
    BX B σ (decide (σ r = c)) (.eq (.reg r) (.const c)) := by
  refine ⟨⟨hr, hc⟩, ?_⟩
  by_cases h : σ r = c <;> simp [Expr.eval, h]

@[construction_api] lemma BX.eqRegs {r s : ℕ} (hr : r ≤ B) (hs : s ≤ B) :
    BX B σ (decide (σ r = σ s)) (.eq (.reg r) (.reg s)) := by
  refine ⟨⟨hr, hs⟩, ?_⟩
  by_cases h : σ r = σ s <;> simp [Expr.eval, h]

@[construction_api] lemma BX.reg {r : ℕ} (hr : r ≤ B) (h : σ r ≤ 1) :
    BX B σ (decide (σ r = 1)) (.reg r) := by
  refine ⟨hr, ?_⟩
  by_cases h' : σ r = 1
  · simp [Expr.eval, h']
  · have : σ r = 0 := by omega
    simp [Expr.eval, this]

@[construction_api] lemma BX.mono {B' : ℕ} (h : BX B σ b e) (hB : B ≤ B') : BX B' σ b e :=
  ⟨exprBoundedIn_mono e hB h.1, h.2⟩

@[construction_api] lemma BX.congr {τ : Store} (h : BX B σ b e) (he : e.eval τ = e.eval σ)
    (hb : ExprBoundedIn B τ e) : BX B τ b e := ⟨hb, he.trans h.2⟩

@[construction_api] lemma BX.regv {r : ℕ} (hr : r ≤ B)
    (h : σ r = if b then 1 else 0) : BX B σ b (.reg r) :=
  ⟨hr, by simpa [Expr.eval] using h⟩

/-- Boolean connectives as expressions. -/
@[construction_api] def bNot (e : Expr) : Expr := .sub (.const 1) e

@[construction_api] def bOr (e e' : Expr) : Expr := .sub (.add e e') (.mul e e')

@[construction_api] def bAnd (e e' : Expr) : Expr := .mul e e'

@[construction_api] lemma BX.bNot (h : BX B σ b e) (hB : 1 ≤ B) :
    BX B σ (!b) (bNot e) := BX.not h hB

@[construction_api] lemma BX.bOr (h : BX B σ b e) (h' : BX B σ b' e') (hB : 2 ≤ B) :
    BX B σ (b || b') (bOr e e') := BX.or h h' hB

@[construction_api] lemma BX.bAnd (h : BX B σ b e) (h' : BX B σ b' e') (hB : 1 ≤ B) :
    BX B σ (b && b') (bAnd e e') := BX.and h h' hB

end NPComplete.RAMToTM

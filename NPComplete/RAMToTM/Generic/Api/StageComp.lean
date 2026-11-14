module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.StageSpec
public import NPComplete.RAMToTM.Generic.Api.Computation
public import NPComplete.RAMToTM.Generic.Api.OperandBoundOfBounded

/-!
# `Comp` as a stage contract

`Comp` is the special case of `StageSpec` whose postcondition fixes Boolean result registers and
whose precondition carries the bound on all register values.  The core `StageSpec` keeps the value
bound out of its statement, because `ProgramBoundedIn` does not imply it; `keep_values` carries it
across a stage when a client needs it.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- The result registers `res` hold their Boolean values. -/
@[construction_api] def BoolResults (res : List (ℕ × Bool)) (σ : Store) : Prop :=
  ∀ q ∈ res, σ q.1 = if q.2 then 1 else 0

@[construction_api] lemma comp_iff_stageSpec {B : ℕ} {Q : Store → Prop} {p : Program}
    {Wr : ℕ → Prop} {res : List (ℕ × Bool)} :
    Comp B Q p Wr res ↔
      StageSpec B (fun σ => Q σ ∧ StoreValuesLe B σ) p {r | Wr r} (BoolResults res) := by
  constructor
  · intro h σ ⟨hq, hv⟩
    obtain ⟨hb, hs, hr⟩ := h σ hq hv
    exact ⟨hr, hs, hb⟩
  · intro h σ hq hv
    obtain ⟨hr, hs, hb⟩ := h σ ⟨hq, hv⟩
    exact ⟨hb, hs, hr⟩

/-- Carry the bound on all register values across a stage. -/
@[construction_api] lemma StageSpec.keep_values {B : ℕ} {P Q : Store → Prop} {p : Program}
    {W : Set ℕ} (hB : 1 ≤ B) (hsf : ScanFree p) (h : StageSpec B P p W Q) :
    StageSpec B (fun σ => P σ ∧ StoreValuesLe B σ) p W (fun σ => Q σ ∧ StoreValuesLe B σ) := by
  intro σ ⟨hP, hv⟩
  obtain ⟨hQ, hf, hb⟩ := h σ hP
  exact ⟨⟨hQ, program_eval_storeValuesLe σ p hB hv hb hsf⟩, hf, hb⟩

end NPComplete.RAMToTM

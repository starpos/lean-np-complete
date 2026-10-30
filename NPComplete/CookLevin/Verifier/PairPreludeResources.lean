module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Verifier.PairPrelude
public import NPComplete.RAMToTM.Generic.Api.ResourceBounds

/-!
A verifier body can reuse the prelude's resource bounds without exposing its layout.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitEncoding Polynomial

/-- A polynomial bound on the body yields resource bounds for the complete verifier. -/
@[construction_api] lemma exists_pairPrelude_resources {α : Type} (enc : α → Bits)
    (body : Program) (B : ℕ → ℕ) (q : Polynomial ℕ) (hq : ∀ L, B L ≤ q.eval L)
    (hsf : ScanFree body)
    (hp : ∀ a w, ProgramBoundedIn (B (pairBits (enc a) w).length)
      (pairPreludeProg.eval (bitInputStore (pairBits (enc a) w))) body) :
    ∃ c bit_c, (∀ a w, (pairPreludeProg.seq body).cost (bitInputStore (pairBits (enc a) w)) ≤
      c * ((pairBits (enc a) w).length + 1) ^ c) ∧
      (∀ a w, ∃ W, W ≤ bit_c * ((pairBits (enc a) w).length + 1) ^ bit_c ∧
        CompiledOperandBound (pairPreludeProg.seq body) (pairBits (enc a) w) W) := by
  let enc' : α × Bits → Bits := fun aw => pairBits (enc aw.1) aw.2
  let B' : ℕ → ℕ := fun L => B L + pairPreludeBound L
  let q' : Polynomial ℕ := q + C 5 * X + C 101
  have hq' : ∀ L, B' L ≤ q'.eval L := by
    intro L
    have := hq L
    simp [B', q', pairPreludeBound]
    omega
  have hp' : ∀ aw, ProgramBoundedIn (B' (enc' aw).length)
      (bitInputStore (enc' aw)) (pairPreludeProg.seq body) := by
    intro ⟨a, w⟩
    constructor
    · exact programBoundedIn_mono _ (by simp [B', enc']) (pairPreludeProg_runs (enc a) w).2
    · exact programBoundedIn_mono _ (by simp [B', enc']) (hp a w)
  obtain ⟨c, d, hc, hd⟩ := exists_resources_of_programBoundedIn enc' (pairPreludeProg.seq body)
    B' q' hq' ⟨ScanFree_pairPreludeProg, hsf⟩ hp'
  exact ⟨c, d, fun a w => hc (a, w), fun a w => hd (a, w)⟩

/-- A monomial body bound suffices, without a minimum coefficient. -/
@[construction_api] lemma exists_pairPrelude_resources_of_monomial_bound {α : Type}
    (enc : α → Bits) (body : Program) (k : ℕ) (hsf : ScanFree body)
    (hp : ∀ a w, ProgramBoundedIn (k * ((pairBits (enc a) w).length + 1) ^ k)
      (pairPreludeProg.eval (bitInputStore (pairBits (enc a) w))) body) :
    ∃ c bit_c, (∀ a w, (pairPreludeProg.seq body).cost (bitInputStore (pairBits (enc a) w)) ≤
      c * ((pairBits (enc a) w).length + 1) ^ c) ∧
      (∀ a w, ∃ W, W ≤ bit_c * ((pairBits (enc a) w).length + 1) ^ bit_c ∧
        CompiledOperandBound (pairPreludeProg.seq body) (pairBits (enc a) w) W) := by
  apply exists_pairPrelude_resources enc body (fun L => k * (L + 1) ^ k)
    (C k * (X + 1) ^ k) _ hsf hp
  intro L
  simp

/-- Build a verifier decider from the body bound and its semantic correctness. -/
@[construction_api] noncomputable def pairPreludeDecider {α : Type} (enc : α → Bits)
    (R : α → Bits → Prop) (body : Program) (outReg : ℕ) (B : ℕ → ℕ) (q : Polynomial ℕ)
    (hq : ∀ L, B L ≤ q.eval L) (hsf : ScanFree body)
    (hp : ∀ a w, ProgramBoundedIn (B (pairBits (enc a) w).length)
      (pairPreludeProg.eval (bitInputStore (pairBits (enc a) w))) body)
    (hcorrect : ∀ a w, (body.eval (pairPreludeProg.eval
      (bitInputStore (pairBits (enc a) w)))) outReg = 1 ↔ R a w) :
    BoundedWhileDecider (fun aw : α × Bits => pairBits (enc aw.1) aw.2)
      (fun _ => True) (fun aw => R aw.1 aw.2) :=
  let h := exists_pairPrelude_resources enc body B q hq hsf hp
  { p := pairPreludeProg.seq body
    outReg := outReg
    c := h.choose
    correct := fun aw _ => by rw [eval_seq]; exact hcorrect aw.1 aw.2
    cost_le := fun aw _ => h.choose_spec.choose_spec.1 aw.1 aw.2
    bit_c := h.choose_spec.choose
    compiled_operands_le := fun aw _ => h.choose_spec.choose_spec.2 aw.1 aw.2 }

end NPComplete.CookLevin

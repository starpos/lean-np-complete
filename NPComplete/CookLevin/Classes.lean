module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.TM0
public import Mathlib.Computability.Encoding

/-!
P and NP use the same TM0 model so reductions and class membership compose. The later
implication `p_ne_np_implies_h3sat` (from `PneNP`) connects these TM0 classes to the TM2-level
hypothesis that 3SAT is not promise-poly-decidable.
A verifier is a deterministic TM0 computer of a `Bool`-valued predicate on a paired
input; a fresh nondeterministic TM0 would not plug into SAT ∈ NP. Pairing doubles the
instance bits and ends them with a `false` separator, so a one-tape machine can recover
`(x, w)` uniquely: raw concatenation is not decodable, and a separator symbol would
need a larger alphabet. The certificate is appended unframed, so only the instance
part is self-delimiting, not the whole pairing.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1 (stepsTo_zero stepsTo_cons)

/-- Uniquely decodable pairing of an instance with a certificate.
    Each instance bit `b` becomes `[true, b]`; a single `false` marks the
    boundary; the certificate follows raw. Doubled bits always start with
    `true`, so the separator cannot be mistaken for data and the instance part
    is self-delimiting. The certificate is not framed, so the whole pairing is
    not prefix-free. -/
@[stable_api] def pairBits (x w : List Bool) : List Bool :=
  (x.flatMap fun b => [true, b]) ++ [false] ++ w

@[stable_api] lemma pairBits_length (x w : List Bool) :
    (pairBits x w).length = 2 * x.length + 1 + w.length := by
  simp [pairBits, List.length_flatMap]
  omega

/-- `L` is decided by a Boolean TM0 poly-time computer under `enc`. -/
@[stable_api] def InP {α : Type} (enc : α → List Bool) (L : α → Prop) : Prop :=
  ∃ f : α → Bool,
    Nonempty (TM0ComputableInPolyTime enc encodeBool f) ∧
    ∀ x, f x = true ↔ L x

/-- `L` has a deterministic poly-time TM0 verifier with polynomially
    bounded certificates. The verifier is computed on `pairBits (enc x) w`. -/
@[stable_api] def InNP {α : Type} (enc : α → List Bool) (L : α → Prop) : Prop :=
  ∃ (p : Polynomial ℕ) (V : α → List Bool → Bool),
    (∀ x, L x ↔ ∃ w, w.length ≤ p.eval (enc x).length ∧ V x w = true) ∧
    Nonempty
      (TM0ComputableInPolyTime
        (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
        encodeBool
        (fun xw => V xw.1 xw.2))

/-- Polynomial-time many-one reduction realized by a TM0 computer. -/
@[stable_api] structure PolyTimeReduction {α β : Type} (eα : α → List Bool) (eβ : β → List Bool)
    (Lα : α → Prop) (Lβ : β → Prop) where
  map : α → β
  computable : Nonempty (TM0ComputableInPolyTime eα eβ map)
  correct : ∀ x, Lα x ↔ Lβ (map x)

@[stable_api] def PolyTimeReduction.trans {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {Lα : α → Prop} {Lβ : β → Prop} {Lγ : γ → Prop}
    (r₁ : PolyTimeReduction eα eβ Lα Lβ) (r₂ : PolyTimeReduction eβ eγ Lβ Lγ) :
    PolyTimeReduction eα eγ Lα Lγ where
  map := r₂.map ∘ r₁.map
  computable :=
    match r₁.computable, r₂.computable with
    | ⟨hf⟩, ⟨hg⟩ => ⟨hf.comp hg⟩
  correct x := (r₁.correct x).trans (r₂.correct (r₁.map x))

@[stable_api] lemma InP.of_reduction {α β : Type} {eα : α → List Bool} {eβ : β → List Bool}
    {Lα : α → Prop} {Lβ : β → Prop}
    (r : PolyTimeReduction eα eβ Lα Lβ) (hβ : InP eβ Lβ) : InP eα Lα := by
  obtain ⟨f, ⟨hf⟩, hdec⟩ := hβ
  obtain ⟨hg⟩ := r.computable
  refine ⟨f ∘ r.map, ⟨hg.comp hf⟩, fun x => ?_⟩
  simp [hdec, r.correct]

/-- Two-state machine that writes `some false` and halts. Enough for the
    empty input, where the start tape is already blank. -/
inductive ConstFalseState
  | start
  | done
  deriving DecidableEq

instance : Inhabited ConstFalseState :=
  ⟨.start⟩

def constFalseMachine : Turing.TM0.Machine (Option Bool) ConstFalseState
  | .start, _ => some (.done, .write (some false))
  | .done, _ => none

lemma constFalseMachine_supports :
    Turing.TM0.Supports constFalseMachine
      ↑({ConstFalseState.start, .done} : Finset ConstFalseState) := by
  refine ⟨?_, ?_⟩
  · simp [default]
  · intro q a q' s hstep hq
    cases q with
    | start =>
      simp [constFalseMachine] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      simp
    | done =>
      simp [constFalseMachine] at hstep

lemma tape_mk₁_write_false :
    Tape.write (some false) (Tape.mk₁ (tapeSymbols ([] : List Bool))) =
      Tape.mk₁ (tapeSymbols [false]) := by
  simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
    ListBlank.head_mk, ListBlank.tail_mk]

lemma constFalseMachine_outputs :
    MachineOutputsInTime constFalseMachine (tapeSymbols []) (tapeSymbols [false]) 1 := by
  refine ⟨.done, 1, le_rfl, ?_, ?_⟩
  · have hstep :
        Turing.TM0.step constFalseMachine
            (Turing.TM0.init (tapeSymbols ([] : List Bool))) =
          some ⟨.done, Tape.write (some false) (Tape.mk₁ (tapeSymbols []))⟩ := by
      simp [Turing.TM0.step, Turing.TM0.init, constFalseMachine, tapeSymbols, default]
    rw [tape_mk₁_write_false] at hstep
    exact stepsTo_cons _ hstep (stepsTo_zero _ _)
  · simp [step_eq_none_iff, constFalseMachine]

/-- The empty language on a one-point type is in P. -/
lemma InP.empty : InP (fun _ : Unit => []) (fun _ => False) := by
  refine ⟨fun _ => false, ⟨?_⟩, fun _ => by simp⟩
  exact
    { Λ := ConstFalseState
      M := constFalseMachine
      S := {ConstFalseState.start, .done}
      supports := constFalseMachine_supports
      time := 1
      outputsFun := fun _ => by
        simpa [encodeBool] using constFalseMachine_outputs }

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Recode.Sim.CleanOccupied

/-!
# Simulation reachability

Correctness of the block simulator must hold across complete source executions,
not only one transition. This module lifts local simulation relations to reachable
configurations while preserving the clean-tape invariants used by the executable
simulator.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_stepsTo_ready_content_occupied {Γ Λ : Type}
    [Inhabited Γ] [Finite Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (c₀ c : TM0.Cfg Γ Λ) (U₀ : Tape (Option Bool))
    (hrel₀ : RawTapeCleanContentRel e c₀.Tape U₀)
    (hocc₀ : SimCleanRightTailOccupied e U₀)
    {k : ℕ} (hstepsSrc : StepsTo (TM0.step M) c₀ c k)
    (hn : 0 < e.n) :
    ∃ U t,
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready c₀.q), U₀⟩ ⟨.run (.ready c.q), U⟩ t ∧
      t ≤ k * (6 * e.n + 4) ∧
      RawTapeCleanContentRel e c.Tape U ∧
      SimCleanRightTailOccupied e U := by
  induction k generalizing c U₀ with
  | zero =>
      simp only [StepsTo, Function.iterate_zero_apply, Option.some.injEq] at hstepsSrc
      subst c
      exact ⟨U₀, 0, stepsTo_zero _ _, by omega, hrel₀, hocc₀⟩
  | succ k ih =>
      obtain ⟨c₁, hprev, hstep⟩ :=
        (TM1to0.stepsTo_succ_iff).1 hstepsSrc
      obtain ⟨U₁, t₁, hsteps₁, hbound₁, hcontent₁, hocc₁⟩ :=
        ih c₁ U₀ hrel₀ hocc₀ hprev
      have hstep' : TM0.step M c₁ = some c := hstep
      rcases c₁ with ⟨q₁, T₁⟩
      rcases Option.map_eq_some_iff.1 hstep' with ⟨⟨q₂, s⟩, hm, rfl⟩
      obtain ⟨Uc, hstepsC, hcontent₂⟩ :=
        simCleanMachine_normal_stmt_step_content M e q₁ q₂ s T₁ U₁
          hcontent₁ hm hn
      obtain ⟨Uo, hstepsO, hocc₂⟩ :=
        simCleanMachine_normal_stmt_step_occupied M e q₁ q₂ s T₁ U₁
          (rawTapeCleanContentRel_to_rawTapeCleanRel hcontent₁) hocc₁ hm hn
      have hendpointCfg := stepsTo_endpoint_eq
        (f := TM0.step (simCleanMachine M e)) hstepsC hstepsO
      have hendpoint : Uc = Uo := by
        cases hendpointCfg
        rfl
      have hocc₂' : SimCleanRightTailOccupied e Uc := by
        rw [hendpoint]
        exact hocc₂.2
      refine ⟨Uc, t₁ + simCleanStmtTime e s, ?_, ?_,
        (by cases s <;> simpa using hcontent₂), hocc₂'⟩
      · simpa [Nat.add_comm] using
          (stepsTo_trans (t₁ := t₁) (t₂ := simCleanStmtTime e s) _
            hsteps₁ hstepsC)
      · have hstepTime : simCleanStmtTime e s ≤ 6 * e.n + 4 := by
          cases s with
          | write => simp [simCleanStmtTime]
          | move => simp [simCleanStmtTime]; omega
        calc
          t₁ + simCleanStmtTime e s ≤
              k * (6 * e.n + 4) + (6 * e.n + 4) :=
            Nat.add_le_add hbound₁ hstepTime
          _ = (k + 1) * (6 * e.n + 4) := by ring

end NPComplete.CookLevin

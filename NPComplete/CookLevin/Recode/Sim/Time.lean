module

public import NPComplete.CookLevin.Recode.Sim.Support

/-!
# Simulation time majorant

A block representation adds scan and rewind work to each source-machine
transition. This module composes the translation and block-scan costs into a
polynomial majorant for the simulator's computability witness.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

/-- Polynomial majorant shape for the block simulation.

In the first factor, `p * C c₂ * (2 * (X + p * C c₂) + 4)` is the TM2-to-TM1
quadratic slowdown and `C c₁` scales it by the TM1-to-TM0 statement bound; the
additive one accounts for the final halt test.  The remaining factors
`(2 * X + 1) * C (8 * n + 8)` pay for a complete fixed-width block scan.
-/
noncomputable def simTime (p : Polynomial ℕ) (c₂ c₁ n : ℕ) : Polynomial ℕ :=
  (p * C c₂ * (2 * (X + p * C c₂) + 4) * C c₁ + 1) *
    (2 * X + 1) * C (8 * n + 8)

lemma simTime_eval (p : Polynomial ℕ) (c₂ c₁ n m : ℕ) :
    (simTime p c₂ c₁ n).eval m =
      (p.eval m * c₂ * (2 * (m + p.eval m * c₂) + 4) * c₁ + 1) *
        (2 * m + 1) * (8 * n + 8) := by
  simp [simTime, eval_add, eval_mul, eval_X]

noncomputable def simTimeFor {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  letI : Fintype (TM2to1.packFinTM2 h.tm).Λ := h.tm.ΛFin
  simTime h.time
    (TM2to1.machineStmtBound (TM2to1.packFinTM2 h.tm).m)
    (TM1to0.supportStmtBound
      (TM2to1.trSupp (TM2to1.packFinTM2 h.tm).m Finset.univ)
      (TM2to1.packTr h.tm))
    (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n

noncomputable def simAux (tm : FinTM2) : TM0ComputableAux Bool :=
  let inner := packedTM0 tm
  let eΓ := BlockEnc.ofFinite inner.Γ
  letI : DecidableEq inner.Λ := Classical.decEq _
  { Λ := SimCleanPhase eΓ.n inner.Λ
    M := simCleanMachine inner.M eΓ
    S := simCleanSupport inner.S
    supports := by
      exact simCleanMachine_supports inner.M eΓ
        inner.S inner.supports }


end NPComplete.CookLevin

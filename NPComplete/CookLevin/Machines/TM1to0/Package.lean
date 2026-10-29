module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

/-!
Mathlib `TM1to0.Λ'` pairs an inductive statement with `σ`, so it is not a
`Fintype`. The translator already names the reachable subset `trStmts`.
Packaging is that finite support plus the existing `tr`, not a new compiler.
The tape alphabet is unchanged, so TM1to0 adds no alphabet packaging.
-/

@[expose] public section

namespace NPComplete.CookLevin.TM1to0

open Turing TM0 TM1

variable {Γ Λ σ : Type*}

/-- A TM0 machine with a finite alphabet and a finite closed state support. -/
structure FinTM0 where
  Γ : Type*
  Λ : Type*
  [ΓInhabited : Inhabited Γ]
  [ΓFin : Fintype Γ]
  [ΛInhabited : Inhabited Λ]
  M : TM0.Machine Γ Λ
  S : Finset Λ
  supports : TM0.Supports M ↑S

attribute [instance] FinTM0.ΓInhabited FinTM0.ΓFin FinTM0.ΛInhabited

instance (tm : FinTM0) : Inhabited { q // q ∈ tm.S } :=
  ⟨⟨default, tm.supports.1⟩⟩

instance (tm : FinTM0) : Fintype { q // q ∈ tm.S } :=
  inferInstanceAs (Fintype { q // q ∈ tm.S })

/-- Existing `tr`, with states restricted to the finite set `trStmts`. -/
noncomputable def ofTM1 {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    [Fintype Γ] [Fintype σ] (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (ss : TM1.Supports M S) : FinTM0 where
  Γ := Γ
  Λ := Turing.TM1to0.Λ' M
  M := Turing.TM1to0.tr M
  S := Turing.TM1to0.trStmts M S
  supports := Turing.TM1to0.tr_supports M ss

end NPComplete.CookLevin.TM1to0

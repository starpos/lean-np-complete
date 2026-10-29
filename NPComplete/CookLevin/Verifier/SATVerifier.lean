module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Verifier.SATBool
public import NPComplete.CookLevin.ToThreeCNF.Basic
public import NPComplete.CookLevin.UniformEmit.LayoutBounds
public import NPComplete.CookLevin.Classes
public import NPComplete.CookLevin.Verifier.SATVerifierWiring
public import NPComplete.CookLevin.Entry
public import NPComplete.CookLevin.Verifier.LiteralEvalSupport

/-!
SAT's NP membership against the TM0 verifier class `InNP`.  The certificate is
the first `cnfVarBound φ` bits of a satisfying assignment and the verifier is a
Boolean CNF evaluator, so the specification half is pure list arithmetic.  The
machine half (`satVerifierDecider`, `SATVerifierWiring.lean`) is a `BoundedWhileDecider`
closing that obligation through the generic RAM-to-TM bridge.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open Computability (encodeBool)
open scoped Polynomial

/-- An accepting witness always yields satisfiability. -/
lemma sat_of_cnfSatBool (w : List Bool) (φ : CNF) (h : cnfSatBool w φ = true) :
    SAT φ :=
  ⟨decodeAssignment w, (cnfSatBool_iff w φ).mp h⟩

/-- Satisfiability yields a witness of length exactly `cnfVarBound φ`: the
    first `cnfVarBound φ` values of the satisfying assignment. -/
lemma cnfSatBool_of_sat (φ : CNF) (h : SAT φ) :
    ∃ w : List Bool, w.length = cnfVarBound φ ∧ cnfSatBool w φ = true := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨List.map (fun v : ℕ => τ v) (List.range (cnfVarBound φ)), ?_, ?_⟩
  · calc
      _ = (List.range (cnfVarBound φ)).length := List.length_map _
      _ = cnfVarBound φ := List.length_range
  rw [cnfSatBool_iff]
  intro c hc
  unfold Clause.Satisfied at hτ
  obtain ⟨l, hlmem, hleval⟩ := hτ c hc
  refine ⟨l, hlmem, ?_⟩
  show l.eval (decodeAssignment (List.map τ (List.range (cnfVarBound φ)))) = true
  rw [literal_eval_congr (fun v hv => getD_range_map (fun i : ℕ => τ i) _ v hv) l
    (cnfVarBound_gt φ c hc l hlmem)]
  exact hleval

lemma eval_X_add_one (n : ℕ) : (Polynomial.X + 1).eval n = n + 1 := by
  simp

/-- The linear polynomial `X + 1` dominates the certificate length. -/
lemma witness_bound (φ : CNF) :
    cnfVarBound φ ≤ (Polynomial.X + 1).eval (encodeCNF φ).length := by
  rw [eval_X_add_one]
  have h := cnfVarBound_le_encodeCNF φ
  omega

/-- The specification half of `InNP encodeCNF SAT`, with `V := cnfSatBool` and
    `p := X + 1`. -/
lemma sat_np_spec (φ : CNF) :
    SAT φ ↔ ∃ w : List Bool,
      w.length ≤ (Polynomial.X + 1).eval (encodeCNF φ).length ∧
        cnfSatBool w φ = true := by
  constructor
  · intro h
    obtain ⟨w, hw, hsat⟩ := cnfSatBool_of_sat φ h
    refine ⟨w, ?_, hsat⟩
    have hbound := witness_bound φ
    rw [eval_X_add_one] at hbound ⊢
    have hlen : w.length = cnfVarBound φ := hw
    omega
  · rintro ⟨w, -, hsat⟩
    exact sat_of_cnfSatBool w φ hsat

/-- SAT (unbounded-width CNF satisfiability) is in NP. The machine half is
    `satVerifierDecider` (`SATVerifierWiring.lean`), a `BoundedWhileDecider` de-pairing
    `pairBits (encodeCNF φ) w` off the canonical `bitInputStore` cells and evaluating the
    decoded CNF against the decoded certificate; `InNP.of_bounded_while_verifier` (`Entry.lean`)
    packages it. -/
@[stable_api] theorem sat_inNP : InNP encodeCNF SAT :=
  InNP.of_bounded_while_verifier encodeCNF SAT (Polynomial.X + 1)
    (fun φ w => cnfSatBool w φ = true) sat_np_spec satVerifierDecider

end NPComplete.CookLevin

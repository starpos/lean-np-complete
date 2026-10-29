module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Verifier.ThreeSATVerifierWiring
public import NPComplete.CookLevin.Entry
public import NPComplete.CookLevin.Verifier.LiteralEvalSupport

/-!
`ThreeSAT`'s NP membership against the TM0 verifier class `InNP`. The certificate is the first
`f.1.numVars` bits of a satisfying assignment and the verifier is a Boolean `ThreeCNF` evaluator,
so the specification half is pure list arithmetic. The machine half
(`threeSatVerifierDecider`, `ThreeSATVerifierWiring.lean`) is a `BoundedWhileDecider` closing
that obligation through the generic RAM-to-TM bridge. Mirrors `SATVerifier.lean`'s `sat_inNP`,
with `f.1.numVars` (via `f.Bounded`) in place of SAT's scan-derived `cnfVarBound φ` as the
certificate-window bound, since `ThreeCNF` carries its own variable count.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open scoped Polynomial

/-- An accepting witness always yields `ThreeSAT`. -/
lemma threeSAT_of_threeCnfSatBool (w : List Bool) (f : ThreeCNF) (h : threeCnfSatBool w f = true) :
    ThreeSAT f :=
  ⟨decodeAssignment w, (threeCnfSatBool_iff w f).mp h⟩

/-- Satisfiability yields a witness of length exactly `f.1.numVars`: the first `f.1.numVars`
    values of a satisfying assignment. `f.Bounded` (via `f.2`) bounds every literal's variable
    below `f.1.numVars`, so the certificate window `List.range f.1.numVars` covers every literal
    the formula reads. -/
lemma threeCnfSatBool_of_threeSAT (f : ValidThreeCNF) (h : ThreeSAT f.1) :
    ∃ w : List Bool, w.length = f.1.numVars ∧ threeCnfSatBool w f.1 = true := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨List.map (fun v : ℕ => τ v) (List.range f.1.numVars), ?_, ?_⟩
  · calc
      _ = (List.range f.1.numVars).length := List.length_map _
      _ = f.1.numVars := List.length_range
  rw [threeCnfSatBool_iff]
  unfold ThreeCNF.Satisfied at hτ
  intro c hc
  have hcτ := hτ c hc
  unfold ThreeClause.Satisfied at hcτ
  have hW : ∀ v, v < f.1.numVars →
      (List.map (fun i : ℕ => τ i) (List.range f.1.numVars)).getD v false = τ v :=
    fun v hv => getD_range_map (fun i : ℕ => τ i) f.1.numVars v hv
  have hb1 := f.2 c hc c.l1 (by simp [ThreeClause.literals])
  have hb2 := f.2 c hc c.l2 (by simp [ThreeClause.literals])
  have hb3 := f.2 c hc c.l3 (by simp [ThreeClause.literals])
  rcases hcτ with h1 | h2 | h3
  · left
    rw [literal_eval_congr hW c.l1 hb1]; exact h1
  · right; left
    rw [literal_eval_congr hW c.l2 hb2]; exact h2
  · right; right
    rw [literal_eval_congr hW c.l3 hb3]; exact h3

/-- The linear polynomial `X + 1` dominates the certificate length: `f.1.numVars` is bounded by
    the `numVars` header's own contribution to `encodeThreeCNF f.1`'s length. -/
lemma validThreeCNF_numVars_le_encode_length_add_one (f : ValidThreeCNF) :
    f.1.numVars ≤ (Polynomial.X + 1).eval (NPComplete.SAT.ValidThreeCNF.encode f).length := by
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  show f.1.numVars ≤ (encodeThreeCNF f.1).length + 1
  have h := encodeThreeCNF_numVars_succ_le f.1
  omega

/-- The specification half of `InNP ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val)`, with
    `V := threeCnfSatBool` and `p := X + 1`. -/
lemma three_sat_np_spec (f : ValidThreeCNF) :
    ThreeSAT f.1 ↔ ∃ w : List Bool,
      w.length ≤ (Polynomial.X + 1).eval (NPComplete.SAT.ValidThreeCNF.encode f).length ∧
        threeCnfSatBool w f.1 = true := by
  constructor
  · intro h
    obtain ⟨w, hw, hsat⟩ := threeCnfSatBool_of_threeSAT f h
    refine ⟨w, ?_, hsat⟩
    have hbound := validThreeCNF_numVars_le_encode_length_add_one f
    rw [hw]
    exact hbound
  · rintro ⟨w, -, hsat⟩
    exact threeSAT_of_threeCnfSatBool w f.1 hsat

/-- `ThreeSAT` (3-CNF satisfiability, restricted to `ValidThreeCNF`'s bounded instances) is in
    NP. The machine half is `threeSatVerifierDecider` (`ThreeSATVerifierWiring.lean`), a
    `BoundedWhileDecider` de-pairing `pairBits (encodeThreeCNF f.1) w` off the canonical
    `bitInputStore` cells and evaluating the decoded `ThreeCNF` against the decoded certificate;
    `InNP.of_bounded_while_verifier` (`Entry.lean`) packages it. -/
@[stable_api] theorem threeSAT_inNP : InNP NPComplete.SAT.ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) :=
  InNP.of_bounded_while_verifier NPComplete.SAT.ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val)
    (Polynomial.X + 1) (fun f w => threeCnfSatBool w f.1 = true) three_sat_np_spec
    threeSatVerifierDecider

end NPComplete.CookLevin

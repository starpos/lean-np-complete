module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.ReductionProg.HgenAssembly
public import NPComplete.CookLevin.Generate
public import NPComplete.CookLevin.Main

/-!
`hgen_of_abi_parts` gives the reduction directly to bounded general CNF
satisfiability: `SAT (g x) ↔ SAT (boundedCookLevinCNFMap enc p hV x)`.  Thus,
if general SAT is in TM0 P, every TM0 NP language is in TM0 P without a 3-CNF
conversion in the reduction chain.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Computability (encodeBool)

/-- If general SAT (`NPComplete.CookLevin.SAT` on unbounded-width CNF)
    is decidable in TM0 polynomial time, then every TM0 NP language is in TM0 P.
    Unlike `threeSAT_InP_implies_PeqNP`, the reduction chain stops at the CNF
    produced by the generator and never composes with `satToThreeCNF`. -/
@[stable_api] theorem sat_InP_implies_PeqNP :
    InP encodeCNF SAT → PeqNP := by
  intro hSAT α enc L hL
  obtain ⟨p, V, hSpec, ⟨hV⟩⟩ := hL
  obtain ⟨g, hsat, hcomp⟩ := hgen_of_abi_parts enc p hV
  have hSpec' : ∀ x, L x ↔ ∃ w : List Bool,
      w.length ≤ boundedCertificateBound enc p x ∧ V x w = true :=
    fun x => by simpa [boundedCertificateBound] using hSpec x
  exact InP.of_reduction
    { map := g
      computable := hcomp
      correct := fun x =>
        (boundedCookLevinCNFMap_correct enc L p hV hSpec' x).trans (hsat x).symm }
    hSAT

end NPComplete.CookLevin

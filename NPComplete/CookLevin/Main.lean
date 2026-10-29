module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Generate
public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.CookLevin.ReductionProg.HgenAssembly
public import NPComplete.CookLevin.PromisePolyDecidable

/-!
# Cook-Levin class consequences

The `P = NP` and `P ≠ NP` statements need to be related to the SAT and 3-SAT instances supplied by
Cook-Levin. This module collects those theorem-level consequences apart from the tableau and
program-construction details that establish them.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open NPComplete.SAT (ThreeSAT)
open NPComplete.RAMToTM

/-- Every TM0 NP language is in TM0 P. A class statement, not a synonym
    of "3SAT is not TM2-decidable". -/
@[stable_api] def PeqNP : Prop :=
  ∀ {α : Type} (enc : α → List Bool) (L : α → Prop), InNP enc L → InP enc L

@[stable_api] def PneNP : Prop := ¬ PeqNP

/-- **Stable API.** A TM2 poly-time decider (with trivial promise) is a TM0 poly-time decider:
    `PromisePolyDecidable enc (fun _ => True) L → InP enc L` for any encoding and language.
    Only the trivial promise domain is supported: with a non-trivial `D` the TM2 machine decides
    `L` only on `D`, so no `InP` conclusion follows. -/
@[stable_api] lemma promisePolyDecidable_to_InP {α : Type} {enc : α → List Bool} {L : α → Prop} :
    PromisePolyDecidable enc (fun _ => True) L → InP enc L := by
  rintro ⟨f, ⟨hf⟩, hdec⟩
  refine ⟨fun x => f ⟨x, trivial⟩, ⟨?drop⟩, fun x => hdec ⟨x, trivial⟩⟩
  refine TM0ComputableInPolyTime.congr_enc (fun _ => rfl) ?enc
    (TM2ComputableInPolyTime.toTM0
      (TM2ComputableInPolyTime.subtype_true hf))
  intro b
  cases b <;> rfl

/-- The generator obligation only needs *some* satisfiability-equivalent CNF, not
the compacted map itself: `map` is a field of `PolyTimeReduction`, and
correctness travels through any SAT-equivalence.  A producer is therefore free
to emit its own variable numbering instead of reproducing `compactCNF`'s
`dedup`/`idxOf` renaming at run time. -/
lemma inNP_has_reduction_of_sat_equivalent_map {α : Type}
    (enc : α → List Bool) (L : α → Prop) (hL : InNP enc L)
    (hgen : ∀ (p : Polynomial ℕ) (V : α → List Bool → Bool)
      (hV : TM0ComputableInPolyTime
        (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
        encodeBool (fun xw => V xw.1 xw.2)),
      ∃ g : α → CNF,
        (∀ x, SAT (g x) ↔ SAT (boundedCookLevinCNFMap enc p hV x)) ∧
        Nonempty (TM0ComputableInPolyTime enc encodeCNF g)) :
    Nonempty (PolyTimeReduction enc NPComplete.SAT.ValidThreeCNF.encode L
      (ThreeSAT ∘ Subtype.val)) := by
  obtain ⟨p, V, hSpec, ⟨hV⟩⟩ := hL
  obtain ⟨g, hsat, hcomp⟩ := hgen p V hV
  have hSpec' : ∀ x, L x ↔ ∃ w : List Bool,
      w.length ≤ boundedCertificateBound enc p x ∧ V x w = true :=
    fun x => by simpa [boundedCertificateBound] using hSpec x
  refine ⟨PolyTimeReduction.trans ?_ satToThreeCNF⟩
  exact {
    map := g
    computable := hcomp
    correct := fun x =>
      (boundedCookLevinCNFMap_correct enc L p hV hSpec' x).trans (hsat x).symm }

/-- If 3SAT is in TM0 P, then every TM0 NP language is in TM0 P. -/
@[stable_api] theorem threeSAT_InP_implies_PeqNP :
    InP NPComplete.SAT.ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) → PeqNP := by
  intro hSAT α enc L hL
  obtain ⟨r⟩ := inNP_has_reduction_of_sat_equivalent_map enc L hL
    (fun p _V hV => hgen_of_abi_parts enc p hV)
  exact InP.of_reduction r hSAT

/-- Standard `P ≠ NP` on TM0 implies the TM2-level hypothesis that 3SAT is not
    promise-poly-decidable (the conclusion below). A corollary of
    `threeSAT_InP_implies_PeqNP` and the generic `promisePolyDecidable_to_InP`. -/
@[stable_api] theorem p_ne_np_implies_h3sat : PneNP →
    ¬ PromisePolyDecidable NPComplete.SAT.ValidThreeCNF.encode (fun _ => True)
      (ThreeSAT ∘ Subtype.val) := fun hne hdec =>
  hne (threeSAT_InP_implies_PeqNP (promisePolyDecidable_to_InP hdec))

end NPComplete.CookLevin

module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Main
public import NPComplete.CookLevin.Verifier.SATVerifier
public import NPComplete.CookLevin.Verifier.ThreeSATVerifier

/-!
# SAT and 3SAT are NP-complete, in TM0 terms

`Classes.lean` already gives `InNP`/`InP`/`PolyTimeReduction`, but no NP-completeness statement:
neither `InNP` alone nor a single Karp reduction says a language is *complete* for NP, only that it
is *in* NP or that one other language reduces to it. `PeqNP`/`PneNP` (`Main.lean`) come closest,
but they quantify over 3SAT specifically, not an arbitrary target language.

Cook–Levin's generic obligation (`hgen_of_abi_parts`, `HgenAssembly.lean`) already produces, for
every TM0 `InNP` language, a satisfiability-equivalent CNF computable in poly time — that witness
*is* `NPHard`'s reduction target for `SAT` itself, so `sat_NPHard` needs no detour through 3-CNF.
Composing that reduction with `satToThreeCNF` (inside `inNP_has_reduction_of_sat_equivalent_map`,
`Main.lean`) narrows it to a `PolyTimeReduction` into `ThreeSAT ∘ Subtype.val`, giving
`threeSAT_NPHard`. Each hardness lemma pairs with its own NP-membership half (`sat_inNP`,
`SATVerifier.lean`; `threeSAT_inNP`, `ThreeSATVerifier.lean`) to give the `NPComplete`
theorems below, all descending from the same Cook-Levin witness.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT (ThreeSAT)

/-- `L` is NP-hard: every TM0 `InNP` language poly-time many-one reduces to it. -/
@[stable_api] def NPHard {β : Type} (eb : β → List Bool) (L : β → Prop) : Prop :=
  ∀ {α : Type} (ea : α → List Bool) (La : α → Prop),
    InNP ea La → Nonempty (PolyTimeReduction ea eb La L)

set_option linter.dupNamespace false in
/-- `L` is NP-complete: it is itself in NP and is NP-hard. -/
@[stable_api] def NPComplete {β : Type} (eb : β → List Bool) (L : β → Prop) : Prop :=
  InNP eb L ∧ NPHard eb L

/-- **Stable API (hardness transfer).** NP-hardness passes along a poly-time reduction:
    if `La` is NP-hard and `La` reduces to `Lb`, then `Lb` is NP-hard. -/
@[stable_api] lemma NPHard.of_reduction {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {La : α → Prop} {Lb : β → Prop}
    (h : NPHard ea La) (r : PolyTimeReduction ea eb La Lb) : NPHard eb Lb := by
  intro γ ec Lc hc
  obtain ⟨r0⟩ := h ec Lc hc
  exact ⟨PolyTimeReduction.trans r0 r⟩

/-- **SAT is NP-hard.** `hgen_of_abi_parts` already builds, for an arbitrary `InNP` language and
    its bounded verifier, a poly-time-computable CNF satisfiability-equivalent to
    `boundedCookLevinCNFMap`; composing that equivalence with `boundedCookLevinCNFMap_correct`
    turns it directly into the reduction `NPHard` asks for, without detouring through 3-CNF. -/
@[stable_api] theorem sat_NPHard : NPHard encodeCNF SAT := by
  intro α ea La hL
  obtain ⟨p, V, hSpec, ⟨hV⟩⟩ := hL
  obtain ⟨g, hsat, hcomp⟩ := hgen_of_abi_parts ea p hV
  have hSpec' : ∀ x, La x ↔ ∃ w : List Bool,
      w.length ≤ boundedCertificateBound ea p x ∧ V x w = true :=
    fun x => by simpa [boundedCertificateBound] using hSpec x
  exact ⟨g, hcomp, fun x =>
    (boundedCookLevinCNFMap_correct ea La p hV hSpec' x).trans (hsat x).symm⟩

/-- **SAT is NP-complete.** -/
@[stable_api] theorem sat_NPComplete : NPComplete encodeCNF SAT :=
  ⟨sat_inNP, sat_NPHard⟩

/-- **3SAT is NP-hard.** `inNP_has_reduction_of_sat_equivalent_map` narrows `sat_NPHard`'s
    CNF-valued reduction to a `ValidThreeCNF`-valued one by composing with `satToThreeCNF`. -/
@[stable_api] theorem threeSAT_NPHard :
    NPHard NPComplete.SAT.ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) := by
  intro α ea La hL
  obtain ⟨r⟩ := inNP_has_reduction_of_sat_equivalent_map ea La hL
    (fun p _V hV => hgen_of_abi_parts ea p hV)
  exact ⟨r⟩

/-- **3SAT is NP-complete.** -/
@[stable_api] theorem threeSAT_NPComplete :
    NPComplete NPComplete.SAT.ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) :=
  ⟨threeSAT_inNP, threeSAT_NPHard⟩

/-- **Stable API (standard entry for NP-hardness).** A language is NP-hard as soon as 3SAT
    poly-time reduces to it. Composes `threeSAT_NPHard` with the given reduction, so callers
    never re-run the Cook-Levin construction. -/
@[stable_api] lemma NPHard.of_threeSAT {β : Type} {eb : β → List Bool} {L : β → Prop}
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb (ThreeSAT ∘ Subtype.val) L) :
    NPHard eb L :=
  NPHard.of_reduction threeSAT_NPHard r

set_option linter.dupNamespace false in
/-- **Stable API (standard entry for NP-completeness).** A language in NP to which 3SAT
    poly-time reduces is NP-complete. -/
@[stable_api] lemma NPComplete.of_threeSAT {β : Type} {eb : β → List Bool} {L : β → Prop}
    (hN : InNP eb L)
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb (ThreeSAT ∘ Subtype.val) L) :
    NPComplete eb L :=
  ⟨hN, NPHard.of_threeSAT r⟩

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Generate.BoundedSATWindow

/-!
# Bounded Verifier Maps

The tableau construction is shared by executable and semantic maps; this module makes the polynomial
certificate and time bounds explicit at the reduction interface. This separation lets correctness
proofs reuse one encoding while callers supply the verifier-specific bounds.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

def boundedCertificateBound {α : Type} (enc : α → List Bool)
    (p : Polynomial ℕ) (x : α) : ℕ :=
  p.eval (enc x).length

def boundedVerifierTimeBound {α : Type} (enc : α → List Bool)
    (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw : α × List Bool => V xw.1 xw.2)) (x : α) : ℕ :=
  hV.time.eval
    (2 * (enc x).length + 1 + boundedCertificateBound enc p x)

/-!
This map exposes the executable tableau path.  The state and letter lists are
explicit fields (`stateList`, `letterList`) of `ExecutableTableauMachine`, so its
values do not depend on a classical enumeration of a `Finset`.
-/
def execCompactBoundedCookLevinCNFMap {α : Type}
    (tm : ExecutableTableauMachine) (enc : α → List Bool) (p time : Polynomial ℕ)
    (x : α) : CNF :=
  execCompactGenerateBoundedVerifierCNF tm (enc x)
    (boundedCertificateBound enc p x)
    (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x))

lemma execCompactBoundedCookLevinCNFMap_sat_iff
    {α : Type} (tm : ExecutableTableauAux) (enc : α → List Bool)
    (p time : Polynomial ℕ) (x : α) :
    SAT (execCompactBoundedCookLevinCNFMap
      (executableTableauMachineOf tm) enc p time x) ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        MachineOutputsInTime tm.base.M
          (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
          (time.eval (2 * (enc x).length + 1 +
            boundedCertificateBound enc p x)) := by
  unfold execCompactBoundedCookLevinCNFMap
  exact execCompactGenerateBoundedVerifierCNF_sat_iff tm (enc x)
    (boundedCertificateBound enc p x)
    (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x))

def semanticCompactBoundedCookLevinCNFMap {α : Type}
    (tm : ExecutableTableauAux) (enc : α → List Bool) (p time : Polynomial ℕ)
    (x : α) : CNF :=
  semanticCompactGenerateBoundedVerifierCNF tm (enc x)
    (boundedCertificateBound enc p x)
    (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x))

def semanticCompactBoundedCookLevinMap {α : Type}
    (tm : ExecutableTableauAux) (enc : α → List Bool) (p time : Polynomial ℕ)
    (x : α) : ValidThreeCNF :=
  toValidThreeCNF (semanticCompactBoundedCookLevinCNFMap tm enc p time x)

lemma semanticCompactBoundedCookLevinCNFMap_sat_iff
    {α : Type} (tm : ExecutableTableauAux) (enc : α → List Bool)
    (p time : Polynomial ℕ) (x : α) :
    SAT (semanticCompactBoundedCookLevinCNFMap tm enc p time x) ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        MachineOutputsInTime tm.base.M
          (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
          (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x)) := by
  unfold semanticCompactBoundedCookLevinCNFMap
  exact semanticCompactGenerateBoundedVerifierCNF_sat_iff tm (enc x)
    (boundedCertificateBound enc p x)
    (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x))

lemma semanticCompactBoundedCookLevinMap_threeSAT_iff
    {α : Type} (tm : ExecutableTableauAux) (enc : α → List Bool)
    (p time : Polynomial ℕ) (x : α) :
    ThreeSAT (semanticCompactBoundedCookLevinMap tm enc p time x).1 ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        MachineOutputsInTime tm.base.M
          (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
          (time.eval (2 * (enc x).length + 1 + boundedCertificateBound enc p x)) := by
  change ThreeSAT (toThreeCNF (semanticCompactBoundedCookLevinCNFMap tm enc p time x)) ↔ _
  rw [← sat_iff_threeSAT]
  exact semanticCompactBoundedCookLevinCNFMap_sat_iff tm enc p time x

noncomputable def boundedCookLevinMap {α : Type}
    (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw : α × List Bool => V xw.1 xw.2)) (x : α) : ValidThreeCNF :=
  toValidThreeCNF
    (compactCNF (generateBoundedVerifierCNF hV.toTM0ComputableAux (enc x)
      (boundedCertificateBound enc p x)
      (boundedVerifierTimeBound enc p hV x)))

lemma boundedCookLevinMap_correct {α : Type}
    (enc : α → List Bool) (L : α → Prop) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw : α × List Bool => V xw.1 xw.2))
    (hSpec : ∀ x, L x ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        V x w = true) (x : α) :
    L x ↔ ThreeSAT (boundedCookLevinMap enc p hV x).val := by
  have hRawSat : SAT (generateBoundedVerifierCNF hV.toTM0ComputableAux
      (enc x) (boundedCertificateBound enc p x)
      (boundedVerifierTimeBound enc p hV x)) ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        MachineOutputsInTime hV.M
          (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
          (boundedVerifierTimeBound enc p hV x) := by
    exact generateBoundedVerifierCNF_sat_iff hV.toTM0ComputableAux (enc x)
      (boundedCertificateBound enc p x)
      (boundedVerifierTimeBound enc p hV x)
  have hSat : SAT (compactCNF (generateBoundedVerifierCNF hV.toTM0ComputableAux
      (enc x) (boundedCertificateBound enc p x)
      (boundedVerifierTimeBound enc p hV x))) ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        MachineOutputsInTime hV.M
          (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
          (boundedVerifierTimeBound enc p hV x) :=
    (compactCNF_sat_iff _).trans hRawSat
  rw [show ThreeSAT (boundedCookLevinMap enc p hV x).val ↔
      SAT (compactCNF (generateBoundedVerifierCNF hV.toTM0ComputableAux
        (enc x) (boundedCertificateBound enc p x)
        (boundedVerifierTimeBound enc p hV x))) by
    simp [boundedCookLevinMap, toValidThreeCNF, sat_iff_threeSAT]]
  rw [hSat]
  constructor
  · intro hx
    obtain ⟨w, hw, hv⟩ := (hSpec x).mp hx
    have hVrun := hV.outputsFun (x, w)
    have hlen : (pairBits (enc x) w).length ≤
        2 * (enc x).length + 1 + boundedCertificateBound enc p x := by
      rw [pairBits_length]
      omega
    have htime := eval_mono_nat hV.time hlen
    have hVrun' : MachineOutputsInTime hV.M
        (tapeSymbols (pairBits (enc x) w)) (tapeSymbols [true])
        (boundedVerifierTimeBound enc p hV x) := by
      obtain ⟨q, t, ht, hs, hh⟩ := hVrun
      have hh' : step hV.M ⟨q, Turing.Tape.mk₁ (tapeSymbols [true])⟩ = none := by
        simpa [hv, encodeBool] using hh
      refine ⟨q, t, ht.trans htime, ?_, hh'⟩
      simpa [hv, encodeBool] using hs
    exact ⟨w, hw, hVrun'⟩
  · rintro ⟨w, hw, hRun⟩
    have hVrun := hV.outputsFun (x, w)
    have htape := machineOutputsInTime_unique_tape hVrun hRun
    have hbool : V x w = true := by
      apply tape_mk₁_bool_injective
      simpa [encodeBool] using htape
    exact (hSpec x).mpr ⟨w, hw, hbool⟩

noncomputable def boundedCookLevinCNFMap {α : Type}
    (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw => V xw.1 xw.2)) (x : α) : CNF :=
  compactCNF (generateBoundedVerifierCNF hV.toTM0ComputableAux
    (enc x) (boundedCertificateBound enc p x)
    (boundedVerifierTimeBound enc p hV x))

lemma boundedCookLevinCNFMap_correct {α : Type}
    (enc : α → List Bool) (L : α → Prop) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw => V xw.1 xw.2))
    (hSpec : ∀ x, L x ↔
      ∃ w : List Bool, w.length ≤ boundedCertificateBound enc p x ∧
        V x w = true) (x : α) :
    L x ↔ SAT (boundedCookLevinCNFMap enc p hV x) := by
  rw [show SAT (boundedCookLevinCNFMap enc p hV x) ↔
      ThreeSAT (boundedCookLevinMap enc p hV x).val by
    simp [boundedCookLevinCNFMap, boundedCookLevinMap,
      toValidThreeCNF, sat_iff_threeSAT]]
  exact boundedCookLevinMap_correct enc L p hV hSpec x

end NPComplete.CookLevin

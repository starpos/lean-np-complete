module

public import NPComplete.CookLevin.Recode.Sim.InputEncoding

/-!
# Simulation output certificate

The simulator needs a witness connecting its selected output to the terminal
tape produced by the packed source machine. This module packages that witness
as a clean-content certificate and converts finite-iterate evaluations into
machine reachability.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma sim_drop_reaches_of_evals {α : Type} {f : α → Option α} {a b : α} {t : ℕ}
    (h : (flip bind f)^[t] (some a) = some b) :
    StateTransition.Reaches f a b := by
  induction t generalizing a with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at h
      subst b
      exact Relation.ReflTransGen.refl
  | succ t ih =>
      rw [Function.iterate_succ, Function.comp_apply] at h
      change (flip bind f)^[t] (f a) = some b at h
      cases ha : f a with
      | none =>
          rw [ha, TM2to1.flip_bind_iterate_none] at h
          cases h
      | some a' =>
          rw [ha] at h
          exact Relation.ReflTransGen.head ha (ih h)

noncomputable def simPackedOutput {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    List (TM2to1.PackΓ h.tm h.tm.k₁) :=
  TM2to1.packList h.tm h.tm.k₁
    (List.map h.outputAlphabet.invFun (eb (f a)))
    (TM2to1.mem_usedSymbols_of_haltList h.tm (h.outputsFun a))

def SimCleanContentCertificate {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) (out : List Bool) : Prop :=
  let inner := packedTM0 h.tm
  let e := BlockEnc.ofFinite inner.Γ
  let tmP := TM2to1.packFinTM2 h.tm
  ∃ (c : TM0.Cfg inner.Γ inner.Λ) (U : Tape (Option Bool))
    (b : List (Option Bool)) (br : List (List (Option Bool)))
    (_a0 : inner.Γ) (_r : List inner.Γ)
    (L R : ListBlank (Option Bool)) (rs : List (Option Bool)),
    RawTapeCleanContentRelAt e c.Tape U b br ∧
    U = Tape.mk' L (ListBlank.append b R) ∧
    R = ListBlank.mk (rawBlocksRight br) ∧
    simCleanPartialWriteTail e b L R = ListBlank.mk rs ∧
    (∀ x ∈ rs, x.isSome) ∧
    out = (simMarkBlock b ++ rs).map (Option.getD · false) ∧
    ∃ Lsrc : ListBlank ((k : tmP.K) → Option (tmP.Γ k)),
      c.Tape.right₀ = TM2to1.addBottom Lsrc ∧
      ListBlank.map (proj tmP.k₁) Lsrc =
        ListBlank.mk ((simPackedOutput h a).map some).reverse

lemma sim_source_eval_mem {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ∃ out : ListBlank (packedTM0 h.tm).Γ,
      out ∈ TM0.eval (packedTM0 h.tm).M
        ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
          (encodePackedInput h.tm h.inputAlphabet (ea a))) ∧
      ∃ L : ListBlank
          ((k : (TM2to1.packFinTM2 h.tm).K) →
            Option ((TM2to1.packFinTM2 h.tm).Γ k)),
        out = TM2to1.addBottom L ∧
          ListBlank.map (proj (TM2to1.packFinTM2 h.tm).k₁) L =
            ListBlank.mk ((simPackedOutput h a).map some).reverse := by
  let tm := h.tm
  let tmP := TM2to1.packFinTM2 tm
  let l := List.map h.inputAlphabet.invFun (ea a)
  let lP : List (tmP.Γ tmP.k₀) := TM2to1.packList tm tm.k₀ l
      (TM2to1.mem_usedSymbols_of_list_k₀ tm l)
  let hOut := h.outputsFun a
  let hP := TM2to1.packFinTM2_outputsInTime tm hOut
  let hEval := hP.toTM2Outputs
  let : Inhabited tmP.Λ := ⟨tmP.main⟩
  let : Inhabited tmP.σ := ⟨tmP.initialState⟩
  have hcfgmem : haltList tmP
      (TM2to1.packList tm tm.k₁
        (List.map h.outputAlphabet.invFun (eb (f a)))
        (TM2to1.mem_usedSymbols_of_haltList tm hOut)) ∈
      StateTransition.eval tmP.step (initList tmP lP) := by
    apply StateTransition.mem_eval.2
    refine ⟨sim_drop_reaches_of_evals hEval.evals_in_steps, ?_⟩
    rfl
  have hinit : TM2to1.TrCfg (initList tmP lP)
      (TM1.init (TM2to1.trInit tmP.k₀ lP)) := by
    let init₂ := @TM2.init tmP.K tmP.Γ tmP.Λ tmP.σ
      (inferInstance : Inhabited tmP.Λ)
      (inferInstance : DecidableEq tmP.K)
      (inferInstance : Inhabited tmP.σ) tmP.k₀ lP
    have hinit₂ : TM2to1.TrCfg init₂
        (TM1.init (TM2to1.trInit tmP.k₀ lP)) := by
      dsimp [init₂]
      exact (@TM2to1.trCfg_init tmP.K tmP.Γ tmP.Λ tmP.σ
        (inferInstance : DecidableEq tmP.K)
        (inferInstance : Inhabited tmP.Λ)
        (inferInstance : Inhabited tmP.σ) tmP.k₀ lP)
    have heq : initList tmP lP = init₂ := by
      simp only [init₂, initList, TM2.init]
      congr 1
      funext k
      by_cases hk : k = tmP.k₀
      · subst k
        simp [Function.update]
      · simp [hk, Function.update]
    rw [heq]
    exact hinit₂
  have htr : StateTransition.Respects (TM2.step tmP.m)
      (TM1.step (TM2to1.tr tmP.m)) TM2to1.TrCfg :=
    TM2to1.tr_respects tmP.m
  obtain ⟨c₁, hc₁rel, hc₁mem⟩ :=
    StateTransition.tr_eval htr hinit hcfgmem
  have h1 : c₁.Tape.right₀ ∈
      TM1.eval (TM2to1.tr tmP.m) (TM2to1.trInit tmP.k₀ lP) := by
    rw [TM1.eval]
    exact (Part.mem_map_iff (fun c => c.Tape.right₀)).2 ⟨c₁, hc₁mem, rfl⟩
  have h0 : c₁.Tape.right₀ ∈
      TM0.eval (TM1to0.tr (TM2to1.tr tmP.m))
        (TM2to1.trInit tmP.k₀ lP) := by
    rw [TM1to0.tr_eval]
    exact h1
  rcases hc₁rel with ⟨L, hL⟩
  have hmem0 : (TM2to1.addBottom L) ∈
      TM0.eval (packedTM0 tm).M
        ((BlockEnc.ofFinite (packedTM0 tm).Γ).decodeList
          (encodePackedInput tm h.inputAlphabet (ea a))) := by
    have h0' : (TM2to1.addBottom L) ∈
        TM0.eval (packedTM0 tm).M
          (TM2to1.trInit tmP.k₀ lP) := by
      change (TM2to1.addBottom L) ∈
        TM0.eval (TM1to0.tr (TM2to1.tr tmP.m))
          (TM2to1.trInit tmP.k₀ lP)
      simpa only [Tape.mk'_right₀] using h0
    have hmem' : (TM2to1.addBottom L :
        ListBlank (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) ∈
        TM0.eval (packedTM0 tm).M
          ((BlockEnc.ofFinite
            (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).decodeList
            (encodePackedInput tm h.inputAlphabet (ea a))) := by
      rw [sim_decode_packed_input tm h.inputAlphabet (ea a)]
      exact h0'
    change (TM2to1.addBottom L :
      ListBlank (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) ∈
      TM0.eval (packedTM0 tm).M
        ((BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).decodeList
          (encodePackedInput tm h.inputAlphabet (ea a)))
    exact hmem'
  refine ⟨TM2to1.addBottom L, hmem0, L, rfl, ?_⟩
  change ListBlank.map (proj tmP.k₁) L =
    ListBlank.mk
      ((TM2to1.packList tm tm.k₁
        (List.map h.outputAlphabet.invFun (eb (f a)))
        (TM2to1.mem_usedSymbols_of_haltList tm hOut)).map some).reverse
  convert hL tmP.k₁ using 1;
    simp [tmP, tm]; rfl


end NPComplete.CookLevin

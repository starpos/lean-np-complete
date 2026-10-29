module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Machines.PackedOutputDecode

/-!
The TM2-to-TM0 construction depends on simulation and decoder contracts.
Isolating these bridges downstream keeps the shared run/tape layer independent
of the construction it supports.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

noncomputable def dropMaps {α : Type} {ea : α → List Bool} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea encodeBool f) (l : List Bool) : Bool :=
  decodePackedOutputBool h.tm h.outputAlphabet
    (simFn h (encodePackedInput h.tm h.inputAlphabet l))

lemma tm2to1_addBottom_output_order {K : Type*} {Γ : K → Type*}
    [DecidableEq K] (k : K)
    (L : ListBlank ((k : K) → Option (Γ k)))
    (S : List (Γ k))
    (hL : ListBlank.map (proj k) L =
      ListBlank.mk (S.map some).reverse) :
    ListBlank.map
        ({ f := fun z : TM2to1.Γ' K Γ => z.2 k,
           map_pt' := by rfl } : PointedMap
             (TM2to1.Γ' K Γ) (Option (Γ k)))
        (TM2to1.addBottom L) =
      ListBlank.mk (S.map some).reverse := by
  let f : PointedMap (TM2to1.Γ' K Γ) (Option (Γ k)) :=
    { f := fun z => z.2 k, map_pt' := by rfl }
  rw [← hL]
  apply ListBlank.ext
  intro n
  rw [ListBlank.nth_map, ListBlank.nth_map]
  change ((TM2to1.addBottom L).nth n).2 k = (L.nth n) k
  rw [TM2to1.addBottom_nth_snd]

lemma drop_out_cons (tm : FinTM2)
    (L : ListBlank (∀ k, Option (TM2to1.PackΓ tm k))) :
    ∃ c r, Quotient.out (TM2to1.addBottom L) = c :: r := by
  have hmk : ListBlank.mk (Quotient.out (TM2to1.addBottom L)) =
      TM2to1.addBottom L := Quotient.out_eq' _
  have hne : Quotient.out (TM2to1.addBottom L) ≠ [] := by
    intro he
    have hh := congrArg ListBlank.head hmk
    rw [he, ListBlank.head_mk] at hh
    have hfirst := congrArg Prod.fst hh
    rw [TM2to1.addBottom_head_fst] at hfirst
    exact absurd hfirst (by simp [default])
  exact List.exists_cons_of_ne_nil hne

/-- The packed TM2 initial configuration is related to the TM1 initial configuration. -/
lemma dropMaps_eq_of_tm2_init_trCfg (tmP : FinTM2)
    (lP : List (tmP.Γ tmP.k₀)) :
    letI : Inhabited tmP.Λ := ⟨tmP.main⟩
    letI : Inhabited tmP.σ := ⟨tmP.initialState⟩
    TM2to1.TrCfg (initList tmP lP)
      (TM1.init (TM2to1.trInit tmP.k₀ lP)) := by
  let : Inhabited tmP.Λ := ⟨tmP.main⟩
  let : Inhabited tmP.σ := ⟨tmP.initialState⟩
  have hinit₂ := @TM2to1.trCfg_init tmP.K tmP.Γ tmP.Λ tmP.σ
    (inferInstance : DecidableEq tmP.K)
    (inferInstance : Inhabited tmP.Λ)
    (inferInstance : Inhabited tmP.σ) tmP.k₀ lP
  have heq : initList tmP lP = @TM2.init tmP.K tmP.Γ tmP.Λ tmP.σ
      (inferInstance : Inhabited tmP.Λ)
      (inferInstance : DecidableEq tmP.K)
      (inferInstance : Inhabited tmP.σ) tmP.k₀ lP := by
    simp only [initList, TM2.init]
    congr 1
    funext k
    by_cases hk : k = tmP.k₀
    · subst k
      simp [Function.update]
    · simp [hk, Function.update]
  rw [heq]
  exact hinit₂

/-- The packed run halts with the encoded output bit in the head cell of the output stack. -/
lemma dropMaps_eq_of_tm2_halt_cell {α : Type} {ea : α → List Bool} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea encodeBool f) (a : α) :
    ∃ L : ListBlank (∀ k, Option (TM2to1.PackΓ h.tm k)),
      TM2to1.addBottom L ∈
        TM0.eval (packedTM0 h.tm).M
          ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
            (encodePackedInput h.tm h.inputAlphabet (ea a))) ∧
      ∃ hmem : h.outputAlphabet.invFun (f a) ∈ TM2to1.usedSymbols h.tm h.tm.k₁,
        (TM2to1.addBottom L).head.2 h.tm.k₁ =
          some (⟨h.outputAlphabet.invFun (f a), hmem⟩ : (TM2to1.packFinTM2 h.tm).Γ h.tm.k₁) := by
  let tm := h.tm
  let tmP := TM2to1.packFinTM2 tm
  let lP := TM2to1.packList tm tm.k₀ (List.map h.inputAlphabet.invFun (ea a))
    (TM2to1.mem_usedSymbols_of_list_k₀ tm _)
  let hOut := h.outputsFun a
  let hEval := (TM2to1.packFinTM2_outputsInTime tm hOut).toTM2Outputs
  let : Inhabited tmP.Λ := ⟨tmP.main⟩
  let : Inhabited tmP.σ := ⟨tmP.initialState⟩
  have hcfgmem : haltList tmP
      (TM2to1.packList tm tm.k₁
        (List.map h.outputAlphabet.invFun (encodeBool (f a)))
        (TM2to1.mem_usedSymbols_of_haltList tm hOut)) ∈
      StateTransition.eval tmP.step (initList tmP lP) :=
    StateTransition.mem_eval.2 ⟨drop_reaches_of_evals hEval.evals_in_steps, rfl⟩
  obtain ⟨c₁, hc₁rel, hc₁mem⟩ := StateTransition.tr_eval
    (TM2to1.tr_respects tmP.m) (dropMaps_eq_of_tm2_init_trCfg tmP lP) hcfgmem
  have h0 : c₁.Tape.right₀ ∈ TM0.eval (TM1to0.tr (TM2to1.tr tmP.m))
      (TM2to1.trInit tmP.k₀ lP) := by
    rw [TM1to0.tr_eval, TM1.eval]
    exact (Part.mem_map_iff (fun c => c.Tape.right₀)).2 ⟨c₁, hc₁mem, rfl⟩
  rcases hc₁rel with ⟨L, hL⟩
  have hx : h.outputAlphabet.invFun (f a) ∈
      List.map h.outputAlphabet.invFun (encodeBool (f a)) := by
    simp [encodeBool]
  have hmemout := TM2to1.mem_usedSymbols_of_haltList tm hOut _ hx
  have h0' : TM2to1.addBottom L ∈ TM0.eval (packedTM0 tm).M
      (TM2to1.trInit tmP.k₀ lP) := by
    change _ ∈ TM0.eval (TM1to0.tr (TM2to1.tr tmP.m)) (TM2to1.trInit tmP.k₀ lP)
    simpa only [Tape.mk'_right₀] using h0
  have hcell : (TM2to1.addBottom L).head.2 tmP.k₁ =
      some (⟨h.outputAlphabet.invFun (f a), hmemout⟩ : tmP.Γ tmP.k₁) := by
    rw [← ListBlank.nth_zero (TM2to1.addBottom L), TM2to1.addBottom_nth_snd,
      TM2to1.stk_nth_val 0 (hL tmP.k₁)]
    simp only [encodeBool]
    rw [List.getElem?_eq_getElem (Nat.zero_lt_succ 0)]
    rfl
  have hmem' : TM2to1.addBottom L ∈ TM0.eval (packedTM0 tm).M
      ((BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).decodeList
        (encodePackedInput tm h.inputAlphabet (ea a))) := by
    rw [sim_decode_packed_input tm h.inputAlphabet (ea a)]
    exact h0'
  exact ⟨L, hmem', hmemout, hcell⟩

/-- The simulated tape's first decoded cell is the head of the packed halting tape. -/
lemma dropMaps_eq_of_tm2_sim_head {α : Type} {ea : α → List Bool} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea encodeBool f) (a : α)
    (L : ListBlank (∀ k, Option (TM2to1.PackΓ h.tm k)))
    (hmem : TM2to1.addBottom L ∈
        TM0.eval (packedTM0 h.tm).M
          ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
            (encodePackedInput h.tm h.inputAlphabet (ea a)))) :
    (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst
        (simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))) =
      (TM2to1.addBottom L).head := by
  have hdom := (Part.dom_iff_mem).2 ⟨_, hmem⟩
  have hget : ((TM0.eval (packedTM0 h.tm).M
      ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a)))).get hdom) =
        (TM2to1.addBottom L : ListBlank (TM2to1.Γ' h.tm.K (TM2to1.PackΓ h.tm))) :=
    Part.get_eq_of_mem hmem hdom
  have hqout := congrArg
    (fun z : ListBlank (TM2to1.Γ' h.tm.K (TM2to1.PackΓ h.tm)) => Quotient.out z) hget
  have hmk : ListBlank.mk (Quotient.out (TM2to1.addBottom L)) =
      TM2to1.addBottom L := Quotient.out_eq' _
  obtain ⟨c, r, hr⟩ := drop_out_cons h.tm L
  have hc : c = (TM2to1.addBottom L).head := by
    have hh := congrArg ListBlank.head hmk
    rw [ListBlank.head_mk] at hh
    have hhead := congrArg List.headI hr
    simp only [List.headI] at hhead
    exact hhead.symm.trans hh
  have hsource : simSourceHead h
      (encodePackedInput h.tm h.inputAlphabet (ea a)) = c := by
    unfold simSourceHead
    dsimp only
    rw [dite_eq_left hdom]
    simp only [List.headI]
    exact (hqout.trans hr).symm ▸ rfl
  have hrun : ∃ out,
      MachineOutputsInTime (simAux h.tm).M
        (tapeSymbols (encodePackedInput h.tm h.inputAlphabet (ea a)))
        (tapeSymbols out)
        ((simTimeFor h).eval (encodePackedInput h.tm h.inputAlphabet (ea a)).length) ∧
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst out =
        simSourceHead h (encodePackedInput h.tm h.inputAlphabet (ea a)) := by
    obtain ⟨out, hrun, hfirst, _⟩ := sim_run_witness_with_content h a
    exact ⟨out, hrun, hfirst⟩
  have hsim := simFn_spec h
    (encodePackedInput h.tm h.inputAlphabet (ea a)) hdom hrun
  exact hsim.2.trans (hsource.trans hc)

lemma dropMaps_eq_of_tm2 {α : Type} {ea : α → List Bool} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea encodeBool f) (a : α) :
    dropMaps h (ea a) = f a := by
  obtain ⟨L, hmem, hmemout, hcell⟩ := dropMaps_eq_of_tm2_halt_cell h a
  have hobs := dropMaps_eq_of_tm2_sim_head h a L hmem
  unfold dropMaps
  rw [drop_decodePackedOutputBool_of_decodeFirst h.tm h.outputAlphabet _ _ hobs, hcell]
  simp

/-- Enc ; Sim ; Dec on `Option Bool`. The machine is the recoder. -/
@[construction_api] noncomputable def TM2ComputableInPolyTime.toTM0
    {α : Type} {ea : α → List Bool} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea encodeBool f) :
    TM0ComputableInPolyTime ea encodeBool f :=
  let encH := encComputable h.tm h.inputAlphabet ea
  let simH := simComputable h
  let decH := decComputable h.tm h.outputAlphabet
  let encSimAux := encH.toTM0ComputableAux.comp simH.toTM0ComputableAux
  let allAux := encSimAux.comp decH.toTM0ComputableAux
  let encSimTime := encH.time + 1 + simH.time.comp (X + encH.time)
  let allTime := encSimTime + 1 + decH.time.comp (X + encSimTime)
  { toTM0ComputableAux := allAux
    time := allTime
    outputsFun a := by
       have henc := encH.outputsFun a
       have hsim := simH.outputsFun a
       have hdec := decH.outputsFun (simFn h
         (encodePackedInput h.tm h.inputAlphabet (ea a)))
       obtain ⟨q₁, t₁, ht₁, hs₁, hh₁⟩ := machineOutputsInTime_comp henc hsim
       obtain ⟨q₂, t₂, ht₂, hs₂, hh₂⟩ := machineOutputsInTime_comp
         ⟨q₁, t₁, ht₁, hs₁, hh₁⟩ hdec
       have hmap := dropMaps_eq_of_tm2 h a
       rw [← hmap]
       refine ⟨q₂, t₂, ?_, hs₂, hh₂⟩
       have hmid : (encodePackedInput h.tm h.inputAlphabet (ea a)).length ≤
           (ea a).length + encH.time.eval (ea a).length :=
         machineOutputs_output_length henc
       have hsimlen : (simFn h
           (encodePackedInput h.tm h.inputAlphabet (ea a))).length ≤
           (encodePackedInput h.tm h.inputAlphabet (ea a)).length +
             simH.time.eval (encodePackedInput h.tm h.inputAlphabet (ea a)).length :=
         machineOutputs_output_length hsim
       have hsimmono : simH.time.eval
             (encodePackedInput h.tm h.inputAlphabet (ea a)).length ≤
           simH.time.eval ((ea a).length + encH.time.eval (ea a).length) :=
         eval_mono_nat simH.time hmid
       have hdecmid : decH.time.eval
             (simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))).length ≤
           decH.time.eval ((ea a).length +
             encH.time.eval (ea a).length +
             simH.time.eval ((ea a).length + encH.time.eval (ea a).length)) := by
         apply eval_mono_nat decH.time
         omega
       have hdecmid' : decH.time.eval
             (simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))).length ≤
           decH.time.eval ((ea a).length + encSimTime.eval (ea a).length) := by
         apply eval_mono_nat decH.time
         simp [encSimTime, eval_add, eval_comp, eval_X, eval_one]
         omega
       simp [encSimTime, allTime, eval_add, eval_comp, eval_X, eval_one]
         at ht₁ ht₂ hdecmid' ⊢
       omega }

/-! A generic final bridge for list-valued TM2 outputs.

The decoder is an explicit ABI witness.  It receives the raw Boolean tape
emitted by `simComputable` and emits the requested encoding.  The semantic
obligation for a concrete decoder is `hdecode`.
-/
noncomputable def TM2ComputableInPolyTime.toTM0WithRawDecoderAny
    {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {eb' : γ → List Bool} {f : α → β} {g : List Bool → γ}
    (h : TM2ComputableInPolyTime ea eb f)
    (dec : TM0ComputableInPolyTime (fun l : List Bool => l) eb' g)
    (f' : α → γ)
    (hdecode : ∀ a,
      g (simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))) = f' a) :
    TM0ComputableInPolyTime ea eb' f' := by
  let encH := encComputable h.tm h.inputAlphabet ea
  let simH := simComputable h
  let midH := simH.comp dec
  let allAux := encH.toTM0ComputableAux.comp midH.toTM0ComputableAux
  let allTime := encH.time + 1 + midH.time.comp (X + encH.time)
  exact
    { toTM0ComputableAux := allAux
      time := allTime
      outputsFun := by
        intro a
        have henc := encH.outputsFun a
        have hmid := midH.outputsFun a
        have hmid' :
            MachineOutputsInTime midH.M
              (tapeSymbols (encodePackedInput h.tm h.inputAlphabet (ea a)))
              (tapeSymbols
                (eb' (g (simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))))))
              (midH.time.eval
                (encodePackedInput h.tm h.inputAlphabet (ea a)).length) := by
          simpa only [Function.comp_apply] using hmid
        rw [hdecode a] at hmid'
        obtain ⟨q, t, ht, hsteps, hhalt⟩ :=
          machineOutputsInTime_comp henc hmid'
        refine ⟨q, t, ?_, hsteps, hhalt⟩
        have hlen : (encodePackedInput h.tm h.inputAlphabet (ea a)).length ≤
            (ea a).length + encH.time.eval (ea a).length :=
          machineOutputs_output_length henc
        have hmono : midH.time.eval
            (encodePackedInput h.tm h.inputAlphabet (ea a)).length ≤
            midH.time.eval ((ea a).length + encH.time.eval (ea a).length) :=
          eval_mono_nat midH.time hlen
        simp [allTime, eval_add, eval_comp, eval_X, eval_one] at ht hmono ⊢
        omega }

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Recode.Sim.Initial

/-!
# Polynomial-time simulation

The block-level execution proof is useful to reductions only when it supplies an
output function and a polynomial time bound. This module assembles the simulator's
witness and proves its output and total-step contracts from the lower-level
simulation lemmas.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

/-- The head of the packed source machine's selected output, using the default symbol for an
    empty output or when no result exists. -/
noncomputable def simSourceHead {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (l : List Bool) :
    (packedTM0 h.tm).Γ :=
  let inner := packedTM0 h.tm
  let eΓ := BlockEnc.ofFinite inner.Γ
  let input := eΓ.decodeList l
  open scoped Classical in
  if hsrc : (TM0.eval inner.M input).Dom then
    (Quotient.out ((TM0.eval inner.M input).get hsrc) : List inner.Γ).headI
  else
    default

noncomputable def simFn {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (l : List Bool) : List Bool :=
  let inner := packedTM0 h.tm
  let eΓ := BlockEnc.ofFinite inner.Γ
  let input := eΓ.decodeList l
  open scoped Classical in
  if _hsrc : (TM0.eval inner.M input).Dom then
    if hrun : ∃ out,
        MachineOutputsInTime (simAux h.tm).M (tapeSymbols l) (tapeSymbols out)
          ((simTimeFor h).eval l.length) ∧
        eΓ.decodeFirst out = simSourceHead h l then
      Classical.choose hrun
    else
      []
  else
    []

/-- The simulator selects a target output witness. Its decoded first symbol matches the source
    output head. -/
lemma simFn_spec {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (l : List Bool)
    (hsrc : (TM0.eval (packedTM0 h.tm).M
        ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList l)).Dom)
    (hrun : ∃ out,
      MachineOutputsInTime (simAux h.tm).M (tapeSymbols l) (tapeSymbols out)
        ((simTimeFor h).eval l.length) ∧
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst out =
        simSourceHead h l) :
    MachineOutputsInTime (simAux h.tm).M (tapeSymbols l)
      (tapeSymbols (simFn h l)) ((simTimeFor h).eval l.length) ∧
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst (simFn h l) =
        simSourceHead h l := by
  unfold simFn
  dsimp only
  rw [dite_eq_left hsrc]
  rw [dite_eq_left hrun]
  exact Classical.choose_spec hrun


lemma sim_run_input_normalization
    (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) (xs : List Bool) :
    let tmP := TM2to1.packFinTM2 tm
    letI : Fintype tmP.K := tm.kFin
    letI : Fintype tmP.Λ := tm.ΛFin
    letI : Inhabited tmP.Λ := ⟨tmP.main⟩
    letI : Inhabited tmP.σ := ⟨tmP.initialState⟩
    letI : ∀ k : tmP.K, Fintype (tmP.Γ k) := fun k => by
      exact TM2to1.packΓ_fintype tm k
    letI : Fintype (∀ k : tmP.K, Option (tmP.Γ k)) := inferInstance
    letI : Fintype (TM2to1.Γ' tmP.K tmP.Γ) := inferInstance
    let e := BlockEnc.ofFinite (packedTM0 tm).Γ
    let e0 := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    let l := encodePackedInput tm inp xs
    let lP := TM2to1.packList tm tm.k₀
      (List.map inp.invFun xs)
      (TM2to1.mem_usedSymbols_of_list_k₀ tm _)
    e.n = e0.n ∧
    l = e0.encodeList (TM2to1.trInit tmP.k₀ lP) ∧
    l.length = (TM2to1.trInit tmP.k₀ lP).length * e.n ∧
    lP.length = xs.length ∧
    xs.length ≤ l.length ∧
    initList tmP lP = TM2.init tmP.k₀ lP := by
  let tmP := TM2to1.packFinTM2 tm
  let : Fintype tmP.K := tm.kFin
  let : Fintype tmP.Λ := tm.ΛFin
  let : Inhabited tmP.Λ := ⟨tmP.main⟩
  let : Inhabited tmP.σ := ⟨tmP.initialState⟩
  let : ∀ k : tmP.K, Fintype (tmP.Γ k) := fun k => by
    exact TM2to1.packΓ_fintype tm k
  let : Fintype (∀ k : tmP.K, Option (tmP.Γ k)) := inferInstance
  let : Fintype (TM2to1.Γ' tmP.K tmP.Γ) := inferInstance
  let e := BlockEnc.ofFinite (packedTM0 tm).Γ
  let e0 := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let l := encodePackedInput tm inp xs
  let lP : List (tmP.Γ tmP.k₀) := TM2to1.packList tm tm.k₀
    (List.map inp.invFun xs)
    (TM2to1.mem_usedSymbols_of_list_k₀ tm _)
  have heqN : e.n = e0.n := by
    rfl
  have hencEq : l = e0.encodeList (TM2to1.trInit tmP.k₀ lP) := by
    simpa [l, e0, tmP, lP, packedTM0, TM2to1.packFinTM2] using
      (sim_encodePackedInput (tm := tm) inp xs)
  have hlenL : l.length =
      (TM2to1.trInit tmP.k₀ lP).length * e.n := by
    rw [hencEq, BlockEnc.encodeList_length, heqN]
    rfl
  have htrInitLen : lP.length ≤
      (TM2to1.trInit tmP.k₀ lP).length := by
    exact length_le_trInit_length tmP.k₀ lP
  have hpackLen : lP.length = xs.length := by
    have hp : ∀ (ys : List (tm.Γ tm.k₀))
        (hx : ∀ x ∈ ys, x ∈ TM2to1.usedSymbols tm tm.k₀),
        (TM2to1.packList tm tm.k₀ ys hx).length = ys.length := by
      intro ys
      induction ys with
      | nil => intro; rfl
      | cons x ys ih =>
          intro hx
          have htail := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
          simp only [TM2to1.packList, List.length_cons]
          exact congrArg (· + 1) htail
    change (TM2to1.packList tm tm.k₀
      (List.map inp.invFun xs) _).length = xs.length
    have hp' := hp (List.map inp.invFun xs)
      (TM2to1.mem_usedSymbols_of_list_k₀ tm _)
    simpa [List.length_map] using hp'
  have hinputLen : xs.length ≤ l.length := by
    have hmul : (TM2to1.trInit tmP.k₀ lP).length ≤
        (TM2to1.trInit tmP.k₀ lP).length * e.n := by
      simpa using Nat.mul_le_mul_left
        (TM2to1.trInit tmP.k₀ lP).length
        (show 0 < e.n from by
          change 0 < encN tm
          exact encN_pos tm)
    calc
      xs.length = lP.length := hpackLen.symm
      _ ≤ (TM2to1.trInit tmP.k₀ lP).length := htrInitLen
      _ ≤ (TM2to1.trInit tmP.k₀ lP).length * e.n := hmul
      _ = l.length := hlenL.symm
  have hinit₂ : initList tmP lP = TM2.init tmP.k₀ lP := by
    simp only [initList, TM2.init]
    congr 1
    funext k
    by_cases hk : k = tmP.k₀
    · subst k
      simp [Function.update]
    · simp [hk, Function.update]
  exact ⟨heqN, hencEq, hlenL, hpackLen, hinputLen, hinit₂⟩

lemma listBlank_headI_of_eq_cons {Γ : Type} [Inhabited Γ]
    (L : ListBlank Γ) (a : Γ) (rest : List Γ)
    (h : L = ListBlank.mk (a :: rest)) :
    List.headI (Quotient.out L) = a := by
  have hmk : ListBlank.mk (Quotient.out L) = L := Quotient.out_eq' _
  have hh := congrArg (fun z : ListBlank Γ => z.head) hmk
  rw [ListBlank.head_mk] at hh
  calc
    List.headI (Quotient.out L) = L.head := hh
    _ = a := by
      have hh' := congrArg (fun z : ListBlank Γ => z.head) h
      exact hh'

lemma sim_run_total_steps
    {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (M : Λ → TM2.Stmt Γ Λ σ) (k₀ : K) (input : List (Γ k₀))
    [Fintype K] [Fintype Λ] [Inhabited Λ] [Inhabited σ]
    (ss : TM2.Supports M Finset.univ)
    {c : TM2.Cfg Γ Λ σ} {T : ℕ}
    (hsteps : StepsTo (TM2.step M) (TM2.init k₀ input) c T) :
    ∃ c₁ t₁ t₀,
      TM2to1.TrCfg c c₁ ∧
      StepsTo (TM1.step (TM2to1.tr M))
        (TM1.init (TM2to1.trInit k₀ input)) c₁ t₁ ∧
      t₁ ≤ T * TM2to1.machineStmtBound M *
        (2 * (input.length + T * TM2to1.machineStmtBound M) + 4) ∧
      StepsTo (TM0.step (TM1to0.tr (TM2to1.tr M)))
        (TM1to0.trCfg (TM2to1.tr M)
          (TM1.init (TM2to1.trInit k₀ input)))
        (TM1to0.trCfg (TM2to1.tr M) c₁) t₀ ∧
      t₀ ≤ t₁ *
        TM1to0.supportStmtBound (TM2to1.trSupp M Finset.univ)
          (TM2to1.tr M) := by
  obtain ⟨c₁, t₁, htrRel, hsteps₁, hbound₁⟩ :=
    TM2to1.tr_total_steps M k₀ input hsteps
  obtain ⟨t₀, hsteps₀, hbound₀⟩ :=
    TM1to0.tr_total_steps_of_support (TM2to1.tr M)
      (TM2to1.tr_supports M ss) (TM2to1.trInit k₀ input) hsteps₁
  exact ⟨c₁, t₁, t₀, htrRel, hsteps₁, hbound₁, hsteps₀, hbound₀⟩

lemma sim_run_time_bound
    (n lLen P C₂ C₁ t₁ t₀ tR leftLen s lp : ℕ)
    (hn : 0 < n) (hlPos : 0 < lLen)
    (hs : s ≤ P) (hlp : lp ≤ lLen)
    (hbound₁ : t₁ ≤ s * C₂ * (2 * (lp + s * C₂) + 4))
    (hbound₀ : t₀ ≤ t₁ * C₁)
    (hrel : tR ≤ t₀ * (6 * n + 4))
    (hleft : leftLen ≤ lLen + tR) :
    tR + (3 * n + 3 * leftLen + 7) ≤
      (P * C₂ * (2 * (lLen + P * C₂) + 4) * C₁ + 1) *
        (2 * lLen + 1) * (8 * n + 8) := by
  have hsc : s * C₂ ≤ P * C₂ := Nat.mul_le_mul_right C₂ hs
  have hfactor : 2 * (lp + s * C₂) + 4 ≤
      2 * (lLen + P * C₂) + 4 := by
    have hsum := Nat.add_le_add hlp hsc
    omega
  have hprod : s * C₂ * (2 * (lp + s * C₂) + 4) ≤
      P * C₂ * (2 * (lLen + P * C₂) + 4) := by
    calc
      s * C₂ * (2 * (lp + s * C₂) + 4) ≤
          s * C₂ * (2 * (lLen + P * C₂) + 4) :=
        Nat.mul_le_mul_left _ hfactor
      _ ≤ P * C₂ * (2 * (lLen + P * C₂) + 4) :=
        Nat.mul_le_mul_right _ hsc
  let A : ℕ := P * C₂ * (2 * (lLen + P * C₂) + 4) * C₁
  have ht0A : t₀ ≤ A := by
    dsimp [A]
    calc
      t₀ ≤ t₁ * C₁ := hbound₀
      _ ≤ (s * C₂ * (2 * (lp + s * C₂) + 4)) * C₁ :=
        Nat.mul_le_mul_right _ hbound₁
      _ ≤ (P * C₂ * (2 * (lLen + P * C₂) + 4)) * C₁ :=
        Nat.mul_le_mul_right _ hprod
  have htR_A : tR ≤ A * (6 * n + 4) :=
    hrel.trans (Nat.mul_le_mul_right (6 * n + 4) ht0A)
  have hcleanTime : tR + (3 * n + 3 * leftLen + 7) ≤
      4 * (A * (6 * n + 4)) + 3 * lLen + 3 * n + 7 := by
    have h4 := Nat.mul_le_mul_left 4 htR_A
    have h3 := Nat.mul_le_mul_left 3 hleft
    omega
  have hmajor : 4 * (A * (6 * n + 4)) + 3 * lLen + 3 * n + 7 ≤
      (A + 1) * (2 * lLen + 1) * (8 * n + 8) := by
    have hAterm : A * (24 * n + 16) ≤
        A * (2 * lLen + 1) * (8 * n + 8) := by
      have hcoeff : 24 * n + 16 ≤ 3 * (8 * n + 8) := by
        omega
      have hleft' := Nat.mul_le_mul_left A hcoeff
      have hx3 : 3 ≤ 2 * lLen + 1 := by
        omega
      have hright := Nat.mul_le_mul_right (8 * n + 8) hx3
      calc
        A * (24 * n + 16) ≤ A * (3 * (8 * n + 8)) := hleft'
        _ ≤ A * ((2 * lLen + 1) * (8 * n + 8)) :=
          Nat.mul_le_mul_left A hright
        _ = A * (2 * lLen + 1) * (8 * n + 8) := by ring
    have hadd : 3 * lLen + 3 * n + 7 ≤
        (2 * lLen + 1) * (8 * n + 8) := by
      have hexpand : (2 * lLen + 1) * (8 * n + 8) =
          16 * lLen * n + 16 * lLen + 8 * n + 8 := by
        ring
      rw [hexpand]
      omega
    have hsum := Nat.add_le_add hAterm hadd
    calc
      4 * (A * (6 * n + 4)) + 3 * lLen + 3 * n + 7 =
          A * (24 * n + 16) + 3 * lLen + 3 * n + 7 := by ring
      _ ≤ A * (2 * lLen + 1) * (8 * n + 8) +
          (2 * lLen + 1) * (8 * n + 8) := by
        simpa [Nat.add_assoc] using hsum
      _ = (A + 1) * (2 * lLen + 1) * (8 * n + 8) := by ring
  simpa [A] using hcleanTime.trans hmajor

/-- The packed source machine halts after `t₀` steps from its encoded input, and every clean-up
    schedule whose length is controlled by `t₀` fits into the simulator's time polynomial. -/
lemma simRunWitnessWithContent_raw_run {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ∃ (c₁ : TM0.Cfg (packedTM0 h.tm).Γ (packedTM0 h.tm).Λ) (t₀ : ℕ),
      StepsTo (TM0.step (packedTM0 h.tm).M)
        (TM0.init ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
          (encodePackedInput h.tm h.inputAlphabet (ea a)))) c₁ t₀ ∧
      TM0.step (packedTM0 h.tm).M c₁ = none ∧
      ∀ tR leftLen : ℕ,
        tR ≤ t₀ * (6 * (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n + 4) →
        leftLen ≤ (encodePackedInput h.tm h.inputAlphabet (ea a)).length + tR →
        tR + (3 * (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n + 3 * leftLen + 7) ≤
          (simTimeFor h).eval (encodePackedInput h.tm h.inputAlphabet (ea a)).length := by
  let tm := h.tm
  let tmP := TM2to1.packFinTM2 tm
  let : Fintype tmP.K := tm.kFin
  let : Fintype tmP.Λ := tm.ΛFin
  let : Inhabited tmP.Λ := ⟨tmP.main⟩
  let : Inhabited tmP.σ := ⟨tmP.initialState⟩
  let : ∀ k : tmP.K, Fintype (tmP.Γ k) := fun k => by
    exact TM2to1.packΓ_fintype tm k
  let : Fintype (∀ k : tmP.K, Option (tmP.Γ k)) := inferInstance
  let : Fintype (TM2to1.Γ' tmP.K tmP.Γ) := inferInstance
  let e := BlockEnc.ofFinite (packedTM0 tm).Γ
  let l := encodePackedInput tm h.inputAlphabet (ea a)
  let lP := TM2to1.packList tm tm.k₀
    (List.map h.inputAlphabet.invFun (ea a))
    (TM2to1.mem_usedSymbols_of_list_k₀ tm _)
  let hOut := h.outputsFun a
  let hP := TM2to1.packFinTM2_outputsInTime tm hOut
  let hEval := hP.toTM2Outputs
  have hn : 0 < e.n := by
    change 0 < encN tm
    exact encN_pos tm
  obtain ⟨heqN, hencEq, hlenL, hpackLen, hinputLen, hinit₂⟩ :=
    sim_run_input_normalization tm h.inputAlphabet (ea a)
  have hsteps₂ : StepsTo tmP.step
      (initList tmP lP)
      (haltList tmP
        (TM2to1.packList tm tm.k₁
          (List.map h.outputAlphabet.invFun (eb (f a)))
          (TM2to1.mem_usedSymbols_of_haltList tm hOut))) hEval.steps := by
    have he := hEval.evals_in_steps
    change (flip bind tmP.step)^[hEval.steps]
      (some (initList tmP lP)) =
        some (haltList tmP
          (TM2to1.packList tm tm.k₁
            (List.map h.outputAlphabet.invFun (eb (f a)))
            (TM2to1.mem_usedSymbols_of_haltList tm hOut))) at he
    exact he
  have hsteps₂' : StepsTo (TM2.step tmP.m)
      (TM2.init tmP.k₀ lP)
      (haltList tmP
        (TM2to1.packList tm tm.k₁
          (List.map h.outputAlphabet.invFun (eb (f a)))
          (TM2to1.mem_usedSymbols_of_haltList tm hOut))) hP.steps := by
    change (flip bind tmP.step)^[hEval.steps]
      (some (TM2.init tmP.k₀ lP)) = some _
    exact hinit₂ ▸ hsteps₂
  obtain ⟨c₁, t₁, t₀, htrRel, hsteps₁, hbound₁, hsteps₀, hbound₀⟩ :=
    sim_run_total_steps tmP.m tmP.k₀ lP
      (tm2_univ_supports tmP.m) hsteps₂'
  have hhaltRaw : TM0.step (TM1to0.tr (TM2to1.tr tmP.m))
      (TM1to0.trCfg (TM2to1.tr tmP.m) c₁) = none := by
    rcases htrRel with ⟨L, hL⟩
    simp [TM1to0.trCfg, TM0.step, TM1to0.tr]
  have hdecode : (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
      (encodePackedInput h.tm h.inputAlphabet (ea a)) = TM2to1.trInit tmP.k₀ lP :=
    sim_decode_packed_input tm h.inputAlphabet (ea a)
  have hlPos : 0 < l.length := by
    rw [hlenL]
    exact Nat.mul_pos (trInit_length_pos tmP.k₀ lP) hn
  have hstepsBound : hP.steps ≤ h.time.eval l.length :=
    hP.steps_le_m.trans (eval_mono_nat h.time hinputLen)
  have hlPBound : lP.length ≤ l.length := by
    rw [hpackLen]
    exact hinputLen
  have hbound₁' : t₁ ≤ hP.steps * TM2to1.machineStmtBound tmP.m *
      (2 * (lP.length + hP.steps * TM2to1.machineStmtBound tmP.m) + 4) := hbound₁
  have hbound₀' : t₀ ≤ t₁ * TM1to0.supportStmtBound
      (TM2to1.trSupp tmP.m Finset.univ) (TM2to1.packTr tm) := by
    convert hbound₀ using 1
    rfl
  have htimeEq : (simTimeFor h).eval l.length =
      (h.time.eval l.length * TM2to1.machineStmtBound tmP.m *
          (2 * (l.length + h.time.eval l.length * TM2to1.machineStmtBound tmP.m) + 4) *
          TM1to0.supportStmtBound (TM2to1.trSupp tmP.m Finset.univ) (TM2to1.packTr tm) + 1) *
        (2 * l.length + 1) * (8 * e.n + 8) := by
    change (simTime h.time (TM2to1.machineStmtBound tmP.m) (TM1to0.supportStmtBound
      (TM2to1.trSupp tmP.m Finset.univ) (TM2to1.packTr tm)) e.n).eval l.length = _
    rw [simTime_eval]
  refine ⟨TM1to0.trCfg (TM2to1.tr tmP.m) c₁, t₀, ?_, hhaltRaw, ?_⟩
  · rw [hdecode]
    exact hsteps₀
  · intro tR leftLen hR hleft
    have htimeBound := sim_run_time_bound e.n l.length (h.time.eval l.length)
      (TM2to1.machineStmtBound tmP.m) (TM1to0.supportStmtBound
        (TM2to1.trSupp tmP.m Finset.univ) (TM2to1.packTr tm)) t₁ t₀ tR leftLen
      hP.steps lP.length hn hlPos hstepsBound hlPBound hbound₁' hbound₀' hR hleft
    exact htimeBound.trans htimeEq.symm.le

/-- The source symbol read by the simulator is the head of the halting source tape, whose
    right half carries the packed output. -/
lemma simRunWitnessWithContent_source {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α)
    (c₁ : TM0.Cfg (packedTM0 h.tm).Γ (packedTM0 h.tm).Λ) (t₀ : ℕ)
    (hrun : StepsTo (TM0.step (packedTM0 h.tm).M)
      (TM0.init ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a)))) c₁ t₀)
    (hhalt : TM0.step (packedTM0 h.tm).M c₁ = none) :
    simSourceHead h (encodePackedInput h.tm h.inputAlphabet (ea a)) =
        List.headI (Quotient.out c₁.Tape.right₀) ∧
      ∃ Lsrc : ListBlank ((k : (TM2to1.packFinTM2 h.tm).K) →
          Option ((TM2to1.packFinTM2 h.tm).Γ k)),
        c₁.Tape.right₀ = TM2to1.addBottom Lsrc ∧
          ListBlank.map (proj (TM2to1.packFinTM2 h.tm).k₁) Lsrc =
            ListBlank.mk ((simPackedOutput h a).map some).reverse := by
  obtain ⟨outSrc, hmem, Lsrc, hout, hproj⟩ := sim_source_eval_mem h a
  have hdom : (TM0.eval (packedTM0 h.tm).M
      ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a)))).Dom :=
    (Part.dom_iff_mem).2 ⟨outSrc, hmem⟩
  have hend : c₁.Tape.right₀ ∈ TM0.eval (packedTM0 h.tm).M
      ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a))) := by
    rw [TM0.eval]
    apply (Part.mem_map_iff
      (fun c : TM0.Cfg (packedTM0 h.tm).Γ (packedTM0 h.tm).Λ => c.Tape.right₀)).2
    exact ⟨c₁, StateTransition.mem_eval.2 ⟨reaches_of_stepsTo hrun, hhalt⟩, rfl⟩
  have heq : c₁.Tape.right₀ = outSrc := Part.mem_unique hend hmem
  refine ⟨?_, Lsrc, heq.trans hout, hproj⟩
  unfold simSourceHead
  dsimp only
  rw [dite_eq_left hdom, Part.get_eq_of_mem hmem hdom, heq]

/-- The clean-up machine reaches its ready phase with content related to `c₁.Tape`; the final
    data-cell count is at most the encoded input length plus `tR`. -/
lemma simRunWitnessWithContent_ready {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α)
    (c₁ : TM0.Cfg (packedTM0 h.tm).Γ (packedTM0 h.tm).Λ) (t₀ : ℕ)
    (hrun : StepsTo (TM0.step (packedTM0 h.tm).M)
      (TM0.init ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a)))) c₁ t₀) :
    ∃ (UR : Tape (Option Bool)) (tR : ℕ),
      StepsTo (TM0.step (simCleanMachine (packedTM0 h.tm).M
          (BlockEnc.ofFinite (packedTM0 h.tm).Γ)))
        (TM0.init (tapeSymbols (encodePackedInput h.tm h.inputAlphabet (ea a))))
        ⟨SimCleanPhase.run (SimPhase.ready c₁.q), UR⟩ tR ∧
      tR ≤ t₀ * (6 * (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n + 4) ∧
      RawTapeCleanContentRel (BlockEnc.ofFinite (packedTM0 h.tm).Γ) c₁.Tape UR ∧
      SimCleanRightTailOccupied (BlockEnc.ofFinite (packedTM0 h.tm).Γ) UR ∧
      tapeDataCount UR ≤ (encodePackedInput h.tm h.inputAlphabet (ea a)).length + tR := by
  have hn : 0 < (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n := by
    change 0 < encN h.tm
    exact encN_pos h.tm
  obtain ⟨UR, tR, hready, htR, hrel, hocc⟩ :=
    simCleanMachine_stepsTo_ready_content_occupied (packedTM0 h.tm).M
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ)
      (TM0.init ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
        (encodePackedInput h.tm h.inputAlphabet (ea a)))) c₁
      (Tape.mk₁ (tapeSymbols (encodePackedInput h.tm h.inputAlphabet (ea a))))
      (sim_initial_rawTapeCleanContentRel h.tm h.inputAlphabet (ea a))
      (sim_initial_rawTapeCleanOccupiedRel h.tm h.inputAlphabet (ea a)).2 hrun hn
  refine ⟨UR, tR, hready, htR, hrel, hocc, ?_⟩
  have hc := tapeDataCount_stepsTo hready
  simpa [tapeDataCount_mk₁_map_some] using hc

/-- Final clean-up phase: from the ready phase the clean-up machine halts on the packed output,
    and the produced word is certified by the halting source tape. -/
lemma simRunWitnessWithContent_finish {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α)
    (c₁ : TM0.Cfg (packedTM0 h.tm).Γ (packedTM0 h.tm).Λ)
    (UR : Tape (Option Bool)) (N : ℕ)
    (hhalt : TM0.step (packedTM0 h.tm).M c₁ = none)
    (hrel : RawTapeCleanContentRel (BlockEnc.ofFinite (packedTM0 h.tm).Γ) c₁.Tape UR)
    (hocc : SimCleanRightTailOccupied (BlockEnc.ofFinite (packedTM0 h.tm).Γ) UR)
    (hcount : tapeDataCount UR ≤ N)
    (hLsrc : ∃ Lsrc : ListBlank ((k : (TM2to1.packFinTM2 h.tm).K) →
          Option ((TM2to1.packFinTM2 h.tm).Γ k)),
        c₁.Tape.right₀ = TM2to1.addBottom Lsrc ∧
          ListBlank.map (proj (TM2to1.packFinTM2 h.tm).k₁) Lsrc =
            ListBlank.mk ((simPackedOutput h a).map some).reverse) :
    ∃ (out : List Bool) (leftLen : ℕ), leftLen ≤ N ∧
      StepsTo (TM0.step (simCleanMachine (packedTM0 h.tm).M
          (BlockEnc.ofFinite (packedTM0 h.tm).Γ)))
        ⟨SimCleanPhase.run (SimPhase.ready c₁.q), UR⟩
        ⟨SimCleanPhase.final, Tape.mk₁ (tapeSymbols out)⟩
        (3 * (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n + 3 * leftLen + 7) ∧
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst out =
        List.headI (Quotient.out c₁.Tape.right₀) ∧
      SimCleanContentCertificate h a out := by
  have hn : 0 < (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n := by
    change 0 < encN h.tm
    exact encN_pos h.tm
  set e := BlockEnc.ofFinite (packedTM0 h.tm).Γ with he
  rcases hrel with ⟨lsrcRaw, rsrcRaw, blRaw, brRaw, a0Raw,
    bRaw, hTRaw, hURaw, hblRaw, hbrRaw, hbRaw, hblmRaw, hcontentRaw⟩
  have hcontentAtRaw : RawTapeCleanContentRelAt e c₁.Tape UR bRaw brRaw :=
    ⟨lsrcRaw, rsrcRaw, blRaw, a0Raw, hTRaw, hURaw,
      hblRaw, hbrRaw, hbRaw, hblmRaw, hcontentRaw⟩
  let LRaw : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft blRaw)
  let RRaw : ListBlank (Option Bool) := ListBlank.mk (rawBlocksRight brRaw)
  have hURaw' : UR = Tape.mk' LRaw (ListBlank.append bRaw RRaw) := by
    simp [LRaw, RRaw, hURaw]
  have hRRaw : SimCleanTailOccupied RRaw :=
    simCleanRightTailOccupied_split e LRaw bRaw RRaw UR
      (blockDecodes_length hbRaw) hURaw' hocc
  have hLRaw : LRaw = ListBlank.mk (rawBlocksLeft blRaw) ∧
      ∀ x ∈ rawBlocksLeft blRaw, x.isSome :=
    ⟨rfl, rawBlocksLeft_marked hblmRaw⟩
  have hleftRaw_le : (rawBlocksLeft blRaw).length ≤ N := by
    have hcnt := optionListDataCount_eq_length_of_all_some hLRaw.2
    have hlenBlocks := rawBlocksLeft_length_of_rel hblRaw
    have hleftData : blRaw.length * e.n ≤ tapeDataCount UR := by
      rw [hURaw']
      simp [tapeDataCount, LRaw, RRaw, listBlankDataCount_mk, hcnt, hlenBlocks]
      omega
    rw [hlenBlocks]
    exact hleftData.trans hcount
  have hheadRaw : c₁.Tape.head = a0Raw := by
    rw [hTRaw]
    rfl
  have hmRaw : (packedTM0 h.tm).M c₁.q a0Raw = none := by
    simpa [TM0.step, hheadRaw] using hhalt
  obtain ⟨outRaw, hcleanRaw, hdecodeRaw, hshapeRaw⟩ :=
    simCleanMachine_partial_halt_macro_rep (packedTM0 h.tm).M e c₁.q a0Raw bRaw
      LRaw RRaw (rawBlocksLeft blRaw) (blockDecodes_length hbRaw)
      hbRaw.choose_spec hmRaw hn hLRaw hRRaw
  obtain ⟨rsRaw, hshapeRawEq, hrsRaw, houtRaw⟩ := hshapeRaw
  have hrightRaw : c₁.Tape.right₀ = ListBlank.mk (a0Raw :: rsrcRaw) := by
    rw [hTRaw]
    rfl
  have hheadSrc : List.headI (Quotient.out c₁.Tape.right₀) = a0Raw :=
    listBlank_headI_of_eq_cons _ _ _ hrightRaw
  refine ⟨outRaw, (rawBlocksLeft blRaw).length, hleftRaw_le, ?_, hdecodeRaw.trans hheadSrc.symm, ?_⟩
  · rw [hURaw']
    exact hcleanRaw
  · dsimp [SimCleanContentCertificate]
    exact ⟨c₁, UR, bRaw, brRaw, a0Raw, rsrcRaw, LRaw, RRaw, rsRaw, hcontentAtRaw, hURaw',
      rfl, hshapeRawEq, hrsRaw, houtRaw, hLsrc⟩

lemma sim_run_witness_with_content {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ∃ out,
      MachineOutputsInTime (simAux h.tm).M
        (tapeSymbols (encodePackedInput h.tm h.inputAlphabet (ea a)))
        (tapeSymbols out)
        ((simTimeFor h).eval
          (encodePackedInput h.tm h.inputAlphabet (ea a)).length) ∧
      (BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeFirst out =
        simSourceHead h (encodePackedInput h.tm h.inputAlphabet (ea a)) ∧
      SimCleanContentCertificate h a out := by
  obtain ⟨c₁, t₀, hrun, hhalt, htime⟩ := simRunWitnessWithContent_raw_run h a
  obtain ⟨hsrcHead, hLsrc⟩ := simRunWitnessWithContent_source h a c₁ t₀ hrun hhalt
  obtain ⟨UR, tR, hready, htR, hrel, hocc, hcount⟩ :=
    simRunWitnessWithContent_ready h a c₁ t₀ hrun
  obtain ⟨out, leftLen, hleft, hclean, hdecode, hcert⟩ :=
    simRunWitnessWithContent_finish h a c₁ UR _ hhalt hrel hocc hcount hLsrc
  refine ⟨out, ⟨SimCleanPhase.final,
    (3 * (BlockEnc.ofFinite (packedTM0 h.tm).Γ).n + 3 * leftLen + 7) + tR,
    ?_, stepsTo_trans _ hready hclean, rfl⟩, hdecode.trans hsrcHead.symm, hcert⟩
  have := htime tR leftLen htR hleft
  omega

noncomputable def simComputable {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) :
    TM0ComputableInPolyTime
      (fun a => encodePackedInput h.tm h.inputAlphabet (ea a))
      (fun l : List Bool => l)
      (fun a => simFn h (encodePackedInput h.tm h.inputAlphabet (ea a))) where
  toTM0ComputableAux := simAux h.tm
  time := simTimeFor h
  outputsFun a := by
    have hdom : (TM0.eval (packedTM0 h.tm).M
        ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList
          (encodePackedInput h.tm h.inputAlphabet (ea a)))).Dom := by
      obtain ⟨out, hout⟩ := sim_source_eval_mem h a
      exact (Part.dom_iff_mem).2 ⟨out, hout.1⟩
    obtain ⟨out, hrun, hfirst, _⟩ := sim_run_witness_with_content h a
    exact (simFn_spec h (encodePackedInput h.tm h.inputAlphabet (ea a))
      hdom ⟨out, hrun, hfirst⟩).1


end NPComplete.CookLevin

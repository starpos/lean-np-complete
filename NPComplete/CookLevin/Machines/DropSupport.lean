module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Recode
public import NPComplete.CookLevin.Recode.Enc
public import NPComplete.CookLevin.Recode.EncRun
public import NPComplete.CookLevin.Recode.Dec
public import NPComplete.CookLevin.Recode.DecRun
public import NPComplete.CookLevin.Recode.DecList
public import NPComplete.CookLevin.Recode.Sim
public import NPComplete.CookLevin.Machines.TM1to0
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Computability.Encoding

/-!
This shared layer keeps the TM computability adapters and run/tape/raw-block
facts below the machine, decoder, and conversion modules. Those layers can
reuse the common reasoning without depending on one another cyclically.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

/-! ## Explicit timed-output packaging

The machine-construction modules often prove a `TM2OutputsInTime` statement first.  This
small adapter keeps that proof separate from the bookkeeping needed by
`TM2ComputableInPolyTime`; it does not provide a machine or infer a time bound. -/

noncomputable def TM2ComputableInPolyTime.of_outputsInTime
    {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (tm : Turing.FinTM2) (inputAlphabet : tm.Γ tm.k₀ ≃ αΓ)
    (outputAlphabet : tm.Γ tm.k₁ ≃ βΓ) (time : Polynomial ℕ)
    (outputs : ∀ a,
      Turing.TM2OutputsInTime tm
        (List.map inputAlphabet.invFun (ea a))
        (some (List.map outputAlphabet.invFun (eb (f a))))
        (time.eval (ea a).length)) :
    Turing.TM2ComputableInPolyTime ea eb f where
  tm := tm
  inputAlphabet := inputAlphabet
  outputAlphabet := outputAlphabet
  time := time
  outputsFun := outputs

@[construction_api] noncomputable def TM0ComputableInPolyTime.congr_enc {α β Γ : Type} [Fintype Γ]
    {ea ea' : α → List Γ} {eb eb' : β → List Γ} {f : α → β}
    (hea : ∀ a, ea a = ea' a) (heb : ∀ b, eb b = eb' b)
    (h : TM0ComputableInPolyTime ea eb f) :
    TM0ComputableInPolyTime ea' eb' f where
  toTM0ComputableAux := h.toTM0ComputableAux
  time := h.time
  outputsFun a := by
    simpa [hea a, heb (f a)] using h.outputsFun a

/-- Reinterpret a TM0 computer when only the encoded output tape must agree.
    The equality `eb (f a) = eb' (f' a)` transfers the output guarantee to a
    different result type and encoding. -/
@[construction_api] noncomputable def TM0ComputableInPolyTime.congr_map {α β β' Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {eb' : β' → List Γ}
    {f : α → β} {f' : α → β'}
    (hmap : ∀ a, eb (f a) = eb' (f' a))
    (h : TM0ComputableInPolyTime ea eb f) :
    TM0ComputableInPolyTime ea eb' f' where
  toTM0ComputableAux := h.toTM0ComputableAux
  time := h.time
  outputsFun a := by
    simpa [hmap a] using h.outputsFun a

noncomputable def TM0ComputableInPolyTime.subtype_true {α β Γ : Type} [Fintype Γ]
    {ea : α → List Γ} {eb : β → List Γ} {f : {_x : α // True} → β}
    (h : TM0ComputableInPolyTime (ea ∘ Subtype.val) eb f) :
    TM0ComputableInPolyTime ea eb (fun x => f ⟨x, trivial⟩) where
  toTM0ComputableAux := h.toTM0ComputableAux
  time := h.time
  outputsFun a := h.outputsFun ⟨a, trivial⟩

noncomputable def TM2ComputableInPolyTime.subtype_true {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : {_x : α // True} → β}
    (h : TM2ComputableInPolyTime (ea ∘ Subtype.val) eb f) :
    TM2ComputableInPolyTime ea eb (fun x => f ⟨x, trivial⟩) where
  tm := h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun a := h.outputsFun ⟨a, trivial⟩

/-- Converts a finite successful iteration of a partial transition into reachability. -/
lemma drop_reaches_of_evals {α : Type} {f : α → Option α} {a b : α} {t : ℕ}
    (h : (flip bind f)^[t] (some a) = some b) : StateTransition.Reaches f a b := by
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

lemma machineOutputsInTime_unique_state_drop {α : Type} {f : α → Option α}
    {s a b : α} {t₁ t₂ : ℕ}
    (h₁ : TM2to1.StepsTo f s a t₁)
    (h₂ : TM2to1.StepsTo f s b t₂)
    (ha : f a = none) (hb : f b = none) : a = b := by
  induction t₁ generalizing s t₂ b with
  | zero =>
      simp only [TM2to1.StepsTo] at h₁
      cases h₁
      cases t₂ with
      | zero =>
          simp only [TM2to1.StepsTo] at h₂
          cases h₂
          rfl
      | succ t₂ =>
          obtain ⟨c, hfirst, _⟩ := TM2to1.stepsTo_cons_inv f h₂
          rw [ha] at hfirst
          cases hfirst
  | succ t₁ ih =>
      cases t₂ with
      | zero =>
          simp only [TM2to1.StepsTo] at h₂
          cases h₂
          obtain ⟨c, hfirst, _⟩ := TM2to1.stepsTo_cons_inv f h₁
          rw [hb] at hfirst
          cases hfirst
      | succ t₂ =>
          obtain ⟨a', hfa, h₁'⟩ := TM2to1.stepsTo_cons_inv f h₁
          obtain ⟨b', hfb, h₂'⟩ := TM2to1.stepsTo_cons_inv f h₂
          have hab : a' = b' := Option.some.inj (hfa.symm.trans hfb)
          cases hab
          exact ih h₁' h₂' hb

lemma machineOutputsInTime_unique_tape_drop {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {M : TM0.Machine Γ Λ} {input output₁ output₂ : List Γ}
    {m₁ m₂ : ℕ}
    (h₁ : MachineOutputsInTime M input output₁ m₁)
    (h₂ : MachineOutputsInTime M input output₂ m₂) :
    Tape.mk₁ output₁ = Tape.mk₁ output₂ := by
  obtain ⟨q₁, t₁, _, hs₁, hh₁⟩ := h₁
  obtain ⟨q₂, t₂, _, hs₂, hh₂⟩ := h₂
  have hcfg := machineOutputsInTime_unique_state_drop hs₁ hs₂ hh₁ hh₂
  exact congrArg (fun c : TM0.Cfg Γ Λ => c.Tape) hcfg

lemma tapeSymbols_injective_drop {Γ : Type} [Inhabited Γ]
    {xs ys : List Γ}
    (h : Tape.mk₁ (tapeSymbols xs) = Tape.mk₁ (tapeSymbols ys)) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hhead := congrArg Tape.head h
          simp [Tape.mk₁, Tape.mk₂, Tape.mk', tapeSymbols] at hhead
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hhead := congrArg Tape.head h
          simp [Tape.mk₁, Tape.mk₂, Tape.mk', tapeSymbols] at hhead
      | cons y ys =>
          have hhead := congrArg Tape.head h
          have htail := congrArg Tape.right h
          simp [Tape.mk₁, Tape.mk₂, Tape.mk', tapeSymbols] at hhead htail
          have hxy : x = y := hhead
          subst y
          have htail' : Tape.mk₁ (tapeSymbols xs) = Tape.mk₁ (tapeSymbols ys) := by
            change Tape.mk' (ListBlank.mk []) (ListBlank.mk (tapeSymbols xs)) =
              Tape.mk' (ListBlank.mk []) (ListBlank.mk (tapeSymbols ys))
            rw [show ListBlank.mk (tapeSymbols xs) =
                ListBlank.mk (tapeSymbols ys) by exact htail]
          exact congrArg (fun z => x :: z) (ih htail')

lemma packList_map_equiv {tm : FinTM2} (k : tm.K)
    (e : tm.Γ k ≃ Bool) (l : List Bool)
    (h : ∀ x ∈ l.map e.invFun, x ∈ TM2to1.usedSymbols tm k) :
    (TM2to1.packList tm k (l.map e.invFun) h).map (fun x => e x.1) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.map_cons, Equiv.invFun_as_coe, TM2to1.packList]
      have htail : ∀ x ∈ l.map e.invFun, x ∈ TM2to1.usedSymbols tm k := by
        intro x hx
        exact h x (by simpa using List.mem_cons_of_mem (e.symm b) hx)
      have hi := ih htail
      exact congrArg₂ List.cons (e.apply_symm_apply b) hi

lemma listBlank_map_mk_some_nth {α β : Type} [Inhabited α]
    (p : PointedMap α (Option β)) (xs : List α) (ys : List β)
    (h : ListBlank.map p (ListBlank.mk xs) = ListBlank.mk (ys.map some))
    (i : ℕ) (hi : i < ys.length) :
    p.f (xs.getI i) = some (ys[i]'(by omega)) := by
  have hnth := congrArg (fun z : ListBlank (Option β) => z.nth i) h
  rw [ListBlank.nth_map, ListBlank.nth_mk, ListBlank.nth_mk] at hnth
  have hmap : (ys.map some).getI i = some (ys[i]'(by omega)) := by
    rw [List.getI_eq_getElem _ (by simpa using hi)]
    simp
  rw [hmap] at hnth
  exact hnth

lemma listBlank_cons_head {Γ : Type} [Inhabited Γ]
    (x : Γ) (l : ListBlank Γ) : (ListBlank.cons x l).head = x := by
  refine Quotient.inductionOn l ?_
  intro xs
  rfl

lemma listBlank_tail_cons_getD {R : ListBlank (Option Bool)}
    (x : Option Bool) (hx : x.getD false = R.head.getD false) (i : ℕ) :
    ((R.tail.cons x).nth i).getD false = (R.nth i).getD false := by
  cases i with
  | zero =>
      simp only [ListBlank.nth_zero]
      rw [listBlank_cons_head]
      exact hx
  | succ i =>
      rw [ListBlank.nth_succ, ListBlank.nth_succ]
      rw [ListBlank.tail_cons]

lemma rawBlocksRel_take {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {bs : List (List (Option Bool))} {as : List Γ}
    (h : RawBlocksRel e bs as) (n : ℕ) :
    RawBlocksRel e (bs.take n) (as.take n) := by
  induction h generalizing n with
  | nil => simpa using (@RawBlocksRel.nil _ _ _ e)
  | @cons b a bs as hb hbs ih =>
      cases n with
      | zero => exact RawBlocksRel.nil
      | succ n =>
          simpa using RawBlocksRel.cons hb (ih n)

lemma rawBlocksRight_take_blocks_of_rel {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {bs : List (List (Option Bool))} {as : List Γ}
    (h : RawBlocksRel e bs as) (n : ℕ) :
    (rawBlocksRight bs).take (n * e.n) = rawBlocksRight (bs.take n) := by
  induction h generalizing n with
  | nil => simp [rawBlocksRight]
  | @cons b a bs as hb hbs ih =>
      cases n with
      | zero => simp [rawBlocksRight]
      | succ n =>
          have hblen : b.length = e.n := blockDecodes_length hb
          have htakeBound : b.length ≤ (n + 1) * e.n := by
            rw [hblen, Nat.add_mul, Nat.one_mul]
            omega
          rw [rawBlocksRight_cons, List.take_append,
            List.take_of_length_le htakeBound, hblen]
          have hsub : (n + 1) * e.n - e.n = n * e.n := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
          rw [hsub, ih n]
          simp [rawBlocksRight]

end NPComplete.CookLevin

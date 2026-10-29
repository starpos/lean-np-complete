module

public import NPComplete.CookLevin.Machines.DropSupport
public import NPComplete.CookLevin.Machines.DropTrailingFalse

/-!
The packed-output ABI combines fixed-width decoding with raw-tape and clean-halt
invariants. Keeping these proofs together lets conversion bridges depend on one
decoder layer without reversing the dependency direction.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

noncomputable def decodePackedOutputListTrailingFalseComputableInPolyTime
    (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l)
      (fun l => dropTrailingFalse (decodePackedOutputList tm out l)) := by
  let hdec := decListRawComputableInPolyTime tm out
  let htrim := dropTrailingFalseComputableInPolyTime
  simpa only [Function.comp_def] using hdec.comp htrim

lemma list_take_eq_of_getD_eq {xs ys : List Bool} (n : ℕ)
    (h : ∀ i, xs.getD i false = ys.getD i false)
    (hx : n ≤ xs.length) (hy : n ≤ ys.length) :
    xs.take n = ys.take n := by
  apply List.ext_getElem
  · rw [List.length_take_of_le hx, List.length_take_of_le hy]
  · intro i hiX hiY
    have hix' : i < n := by
      simpa [List.length_take_of_le hx] using hiX
    have hiy' : i < n := by
      simpa [List.length_take_of_le hy] using hiY
    have hix : i < xs.length := by omega
    have hiy : i < ys.length := by omega
    have hh := h i
    rw [List.getD_eq_getElem xs false hix,
      List.getD_eq_getElem ys false hiy] at hh
    rw [List.getElem_take, List.getElem_take]
    exact hh

lemma list_append_getD_congr {α : Type} [Inhabited α]
    {xs xs' ys ys' : List α} (hlen : xs.length = xs'.length)
    (hxs : ∀ i, xs.getD i default = xs'.getD i default)
    (hys : ∀ i, ys.getD i default = ys'.getD i default) :
    ∀ i, (xs ++ ys).getD i default = (xs' ++ ys').getD i default := by
  induction xs generalizing xs' ys ys' with
  | nil =>
      have hxs' : xs' = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst xs'
      simpa using hys
  | cons x xs ih =>
      cases xs' with
      | nil => simp at hlen
      | cons x' xs' =>
          have h0 := hxs 0
          have hlen' : xs.length + 1 = xs'.length + 1 := by simpa using hlen
          have htailLen : xs.length = xs'.length := by omega
          have htail : ∀ i, xs.getD i default = xs'.getD i default := by
            intro i
            simpa [List.getD] using hxs (i + 1)
          have hi := ih htailLen htail hys
          intro i
          cases i with
          | zero => simpa using h0
          | succ i => simpa using hi i

lemma list_getD_map_getD (xs : List (Option Bool)) (i : ℕ) :
    (xs.map (Option.getD · false)).getD i false =
      (xs.getD i none).getD false := by
  induction xs generalizing i with
  | nil => simp [List.getD]
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [List.getD] using ih i

lemma list_length_ge_of_listBlank_nth_isSome {xs : List (Option Bool)}
    {L : ListBlank (Option Bool)} (h : ListBlank.mk xs = L)
    (K : ℕ) (hL : ∀ i, i < K → (L.nth i).isSome) :
    K ≤ xs.length := by
  by_contra hle
  have hlt : xs.length < K := Nat.lt_of_not_ge hle
  have hnth := congrArg (fun z : ListBlank (Option Bool) => z.nth xs.length) h
  rw [ListBlank.nth_mk, List.getI_eq_default _ le_rfl] at hnth
  have hsome := hL xs.length hlt
  rw [← hnth] at hsome
  simp [default] at hsome

lemma listBlank_length_le_of_tail_cons {xs raw : List (Option Bool)}
    (x : Option Bool) (h : ListBlank.mk xs =
      (ListBlank.mk raw).tail.cons x)
    (hxs : ∀ y ∈ xs, y.isSome) (hraw : raw ≠ []) :
    xs.length ≤ raw.length := by
  have h' : ListBlank.mk xs = ListBlank.mk (x :: raw.tail) := by
    simpa [ListBlank.tail_mk, ListBlank.cons_mk] using h
  rcases Quotient.exact h' with hxy | hyx
  · obtain ⟨n, hn⟩ := hxy
    have hlen := congrArg List.length hn
    simp only [List.length_cons, List.length_append, List.length_replicate] at hlen
    have hrawlen : raw.length = raw.tail.length + 1 := by
      cases raw with
      | nil => exact (hraw rfl).elim
      | cons y ys => simp
    omega
  · obtain ⟨n, hn⟩ := hyx
    by_cases hn0 : n = 0
    · subst n
      rw [hn]
      have hraw1 : 1 ≤ raw.length := by
        cases raw with
        | nil => exact (hraw rfl).elim
        | cons y ys => simp
      simp only [List.length_cons, List.length_append, List.length_replicate]
      have hrawlen : raw.tail.length + 1 = raw.length := by
        cases raw with
        | nil => exact (hraw rfl).elim
        | cons y ys => simp
      rw [hrawlen]
    · have hnone : (none : Option Bool) ∈ List.replicate n none := by
        apply List.mem_replicate.2
        exact ⟨by omega, rfl⟩
      have hnone' : (none : Option Bool) ∈
          (x :: raw.tail) ++ List.replicate n none :=
        List.mem_append_right _ hnone
      have hnone'' : (none : Option Bool) ∈ xs := by
        rw [hn]
        exact hnone'
      have := hxs none hnone''
      simp at this

lemma blocksMarked_take_of_content_nth {Γ : Type} [Inhabited Γ]
    {bs : List (List (Option Bool))} {xs : List Γ}
    (h : BlocksContentMarked bs xs) (n : ℕ)
    (hne : ∀ i, i < n → xs.getI i ≠ default) :
    BlocksMarked (bs.take n) := by
  induction bs generalizing xs n with
  | nil =>
      cases xs <;> simp [BlocksMarked]
  | cons b bs ih =>
      cases xs with
      | nil => simp [BlocksContentMarked] at h
      | cons x xs =>
          simp only [BlocksContentMarked] at h
          rcases h with ⟨hbx, htail⟩
          cases n with
          | zero => simp [BlocksMarked]
          | succ n =>
              have hx : x ≠ default := by
                intro hx
                have hi := hne 0 (by omega)
                simp [hx] at hi
              have hb : BlockMarked b := by
                rcases hbx with hdef | hb
                · exact (hx hdef).elim
                · exact hb
              have hneTail : ∀ i, i < n → xs.getI i ≠ default := by
                intro i hi
                simpa [List.getI] using hne (i + 1) (by omega)
              simp only [List.take_succ_cons]
              exact blocksMarked_cons.mpr ⟨hb, ih htail n hneTail⟩

lemma drop_decodePackedOutputBool_of_decodeFirst (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (l : List Bool)
    (c : TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
    (h : (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).decodeFirst l = c) :
    decodePackedOutputBool tm out l =
      match c.2 tm.k₁ with
      | some x => out x.1
      | none => false := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  have hn : 0 < e.n := encN_pos tm
  have hlen : ((l ++ List.replicate e.n false).take e.n).length = e.n := by
    simp [List.length_take]
  unfold decodePackedOutputBool decodePackedOutput at ⊢
  unfold BlockEnc.decodeFirst at h
  dsimp only at h ⊢
  rw [dite_eq_left hlen] at h ⊢
  rw [h]
  cases hc : c.2 tm.k₁ with
  | none => simp [encodeBool]
  | some x => simp [encodeBool]

/-! A blockwise list decoder companion.  `simFn` exposes a raw tape, while the
list decoder consumes fixed-width blocks from that tape.  The lemmas below
relate the two without going through the simulator. -/

lemma blockEnc_decodeList_take_rawBlocksRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (hn : 0 < e.n)
    {bs : List (List (Option Bool))} {as : List Γ}
    (h : RawBlocksRel e bs as) (m : ℕ)
    (hm : m ≤ ((rawBlocksRight bs).map (Option.getD · false)).length) :
    e.decodeList (((rawBlocksRight bs).map (Option.getD · false)).take m) =
      as.take (m / e.n) := by
  induction h generalizing m with
  | nil =>
      have hm0 : m = 0 := by simp [rawBlocksRight] at hm; omega
      subst m
      simp [BlockEnc.decodeList_nil]
  | @cons b a bs as hb hbs ih =>
      have hblen : b.length = e.n := blockDecodes_length hb
      have hbmap : (b.map (Option.getD · false)).length = e.n := by
        simpa using hblen
      have htotal : m ≤
          (b.map (Option.getD · false)).length +
            ((rawBlocksRight bs).map (Option.getD · false)).length := by
        simpa [rawBlocksRight_cons, List.map_append] using hm
      by_cases hshort : m < e.n
      · have hinputshort :
            (((rawBlocksRight (b :: bs)).map (Option.getD · false)).take m).length < e.n := by
          have hle := List.length_take_le m
            ((rawBlocksRight (b :: bs)).map (Option.getD · false))
          have hmle :
              (((rawBlocksRight (b :: bs)).map (Option.getD · false)).take m).length ≤ m := hle
          omega
        have hdec := e.decodeList_of_short (Or.inr hinputshort)
        have hdiv : m / e.n = 0 := Nat.div_eq_of_lt hshort
        rw [hdec, hdiv]
        simp
      · have hfull : e.n ≤ m := Nat.le_of_not_gt hshort
        have hmTail : m - e.n ≤
            ((rawBlocksRight bs).map (Option.getD · false)).length := by
          rw [← hbmap]
          omega
        let v : List.Vector Bool e.n :=
          ⟨b.map (Option.getD · false), by simpa using hbmap⟩
        have hv : e.dec v = a := by
          simpa [v] using hb.choose_spec
        have htake :
            (((rawBlocksRight (b :: bs)).map (Option.getD · false)).take m) =
              v.toList ++
                (((rawBlocksRight bs).map (Option.getD · false)).take (m - e.n)) := by
          rw [rawBlocksRight_cons, List.map_append, List.take_append]
          rw [hbmap]
          have htakeb :
              (b.map (Option.getD · false)).take m = b.map (Option.getD · false) :=
            List.take_of_length_le (by omega)
          rw [htakeb]
          rfl
        have hrest := ih (m - e.n) hmTail
        rw [htake, e.decodeList_append_block hn v _, hv, hrest]
        rw [Nat.div_eq_sub_div hn hfull]
        simp

lemma decodePackedOutputList_take_rawBlocksRel (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool)
    {bs : List (List (Option Bool))}
    {as : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    (h : RawBlocksRel
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) bs as)
    (m : ℕ)
    (hm : m ≤ ((rawBlocksRight bs).map (Option.getD · false)).length) :
    decodePackedOutputList tm out
        (((rawBlocksRight bs).map (Option.getD · false)).take m) =
      (as.take (m / decListN tm)).map (decListCell tm out) := by
  let e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  change (e.decodeList
      (((rawBlocksRight bs).map (Option.getD · false)).take m)).map
      (decListCell tm out) = _
  rw [blockEnc_decodeList_take_rawBlocksRel e (by simpa [e, decListN] using decN_pos tm)
    h m hm]

lemma rawBlocksRight_marked {bs : List (List (Option Bool))}
    (h : BlocksMarked bs) :
    ∀ x ∈ rawBlocksRight bs, x.isSome := by
  induction bs with
  | nil =>
      simp [rawBlocksRight]
  | cons b bs ih =>
      intro x hx
      have hb : BlockMarked b := (blocksMarked_cons.mp h).1
      have hbs : BlocksMarked bs := (blocksMarked_cons.mp h).2
      simp only [rawBlocksRight, List.flatten_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hb x hx
      · exact ih hbs x hx

end NPComplete.CookLevin

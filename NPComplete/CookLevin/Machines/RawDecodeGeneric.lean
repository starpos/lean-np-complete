module

public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.BitEncoding

/-!
The step from a `TM2ComputableInPolyTime` producer to a `TM0ComputableInPolyTime`
one goes through a raw tape decode whose argument never inspects the produced
value: the simulation reads the output tape as an opaque bit list. Stating that
step once, against an abstract target encoding, keeps every producer from
carrying its own copy of the same tape reasoning. This module holds only the
encoding-independent part, so that the producer entry points do not import the
SAT-specific encodings used by `RawDecodePackaging.lean`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BitEncoding

section GenericRawDecode

open Turing

/-- Reads the occupied output slot of a source cell list through a projection
that is known to land on `ListBlank.mk (S.map some)`. -/
lemma output_slot_getI_some (tm : FinTM2)
    (p : PointedMap (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) (Option (TM2to1.PackΓ tm tm.k₁)))
    (hp : ∀ z, p.f z = z.2 tm.k₁)
    {cells : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {S : List (TM2to1.PackΓ tm tm.k₁)}
    (hproj : ListBlank.map p (ListBlank.mk cells) = ListBlank.mk (S.map some))
    (i : ℕ) (hi : i < S.length) :
    (cells.getI i).2 tm.k₁ = some S[i] := by
  rw [← hp]
  exact listBlank_map_mk_some_nth p cells S hproj i hi

/-- Beyond the produced output the output slot of a source cell is empty. -/
lemma output_slot_getI_none (tm : FinTM2)
    (p : PointedMap (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) (Option (TM2to1.PackΓ tm tm.k₁)))
    (hp : ∀ z, p.f z = z.2 tm.k₁)
    {cells : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {S : List (TM2to1.PackΓ tm tm.k₁)}
    (hproj : ListBlank.map p (ListBlank.mk cells) = ListBlank.mk (S.map some))
    (i : ℕ) (hi : S.length ≤ i) :
    (cells.getI i).2 tm.k₁ = none := by
  have hnth := congrArg (fun z => z.nth i) hproj
  rw [ListBlank.nth_map, ListBlank.nth_mk, ListBlank.nth_mk] at hnth
  have hmap : (S.map some).getI i = none :=
    List.getI_eq_default _ (by simpa using hi)
  rw [hmap] at hnth
  rw [← hp]
  exact hnth

/-- The source cell list is at least as long as the produced output. -/
lemma output_cells_length_ge (tm : FinTM2)
    (p : PointedMap (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) (Option (TM2to1.PackΓ tm tm.k₁)))
    (hp : ∀ z, p.f z = z.2 tm.k₁)
    {cells : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {S : List (TM2to1.PackΓ tm tm.k₁)}
    (hproj : ListBlank.map p (ListBlank.mk cells) = ListBlank.mk (S.map some)) :
    S.length ≤ cells.length := by
  by_contra hlt
  have h1 := output_slot_getI_some tm p hp hproj cells.length (Nat.lt_of_not_ge hlt)
  rw [List.getI_eq_default _ le_rfl] at h1
  simp [default] at h1

/-- Cells inside the produced output are never the blank cell. -/
lemma output_cells_getI_ne_default (tm : FinTM2)
    (p : PointedMap (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) (Option (TM2to1.PackΓ tm tm.k₁)))
    (hp : ∀ z, p.f z = z.2 tm.k₁)
    {cells : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {S : List (TM2to1.PackΓ tm tm.k₁)}
    (hproj : ListBlank.map p (ListBlank.mk cells) = ListBlank.mk (S.map some))
    (i : ℕ) (hi : i < S.length) :
    cells.getI i ≠ default := by
  intro hd
  have h1 := output_slot_getI_some tm p hp hproj i hi
  rw [hd] at h1
  simp [default] at h1

/-- Observing the cleaned tail through `Option.getD` agrees with the raw tail. -/
lemma tail_cons_getD_obs {rs raw : List (Option Bool)}
    (htailShape : ListBlank.mk rs =
      (ListBlank.mk raw).tail.cons (simMarkCell (ListBlank.mk raw).head)) (i : ℕ) :
    (rs.getI i).getD false = (raw.getI i).getD false := by
  have hnth := congrArg
    (fun z : ListBlank (Option Bool) => (z.nth i).getD false) htailShape
  rw [ListBlank.nth_mk] at hnth
  have htail := listBlank_tail_cons_getD
    (R := ListBlank.mk raw) (simMarkCell (ListBlank.mk raw).head)
    (simMarkCell_getD _) i
  rw [ListBlank.nth_mk] at htail
  exact hnth.trans htail

/-- The cleaned output bits agree pointwise with the raw source bits. -/
lemma clean_bits_getD_eq {b rs raw : List (Option Bool)}
    (htailShape : ListBlank.mk rs =
      (ListBlank.mk raw).tail.cons (simMarkCell (ListBlank.mk raw).head)) (i : ℕ) :
    ((simMarkBlock b ++ rs).map (Option.getD · false)).getD i false =
      ((b ++ raw).map (Option.getD · false)).getD i false := by
  simp only [List.map_append]
  apply list_append_getD_congr
  · simp [simMarkBlock_length]
  · intro j
    exact congrArg (fun z : List Bool => z.getD j false) (simMarkBlock_getD b)
  · intro j
    change (rs.map (Option.getD · false)).getD j false =
      (raw.map (Option.getD · false)).getD j false
    rw [list_getD_map_getD, list_getD_map_getD]
    simpa [List.getI, default] using tail_cons_getD_obs htailShape j

/-- The marked prefix of the raw tail consists of `some` cells. -/
lemma rawBlocksRight_getI_isSome {Γ : Type} [Inhabited Γ] [Finite Γ] {e : BlockEnc Γ}
    {br : List (List (Option Bool))} {r : List Γ}
    (hbr : RawBlocksRel e br r) (hcontent : BlocksContentMarked br r)
    (n : ℕ) (hn : n ≤ r.length) (hne : ∀ i, i < n → r.getI i ≠ default)
    (i : ℕ) (hi : i < n * e.n) : ((rawBlocksRight br).getI i).isSome := by
  have hmarked := rawBlocksRight_marked
    (blocksMarked_take_of_content_nth hcontent n hne)
  have hlen : (rawBlocksRight (br.take n)).length = n * e.n := by
    rw [rawBlocksRight_length_of_rel (rawBlocksRel_take hbr n), List.length_take,
      RawBlocksRel.length_eq hbr, Nat.min_eq_left hn]
  have hiP : i < (rawBlocksRight (br.take n)).length := by omega
  have htake := rawBlocksRight_take_blocks_of_rel hbr n
  have hiF : i < (rawBlocksRight br).length := by
    rw [rawBlocksRight_length_of_rel hbr, RawBlocksRel.length_eq hbr]
    exact lt_of_lt_of_le hi (Nat.mul_le_mul_right _ hn)
  have heq : (rawBlocksRight br).getI i = (rawBlocksRight (br.take n))[i] := by
    have h1 : ((rawBlocksRight br).take (n * e.n))[i]'(by rw [htake]; exact hiP) =
        (rawBlocksRight (br.take n))[i] := List.getElem_of_eq htake _
    rw [← h1, List.getElem_take, List.getI_eq_getElem _ hiF]
  rw [heq]
  exact hmarked _ (List.getElem_mem hiP)

/-- A cleaned tail that is `some` on its first `K` cells has at least `K` cells. -/
lemma tail_cons_nth_isSome {raw : List (Option Bool)} {K : ℕ}
    (hsome : ∀ i, i < K → (raw.getI i).isSome) (i : ℕ) (hi : i < K) :
    (((ListBlank.mk raw).tail.cons (simMarkCell (ListBlank.mk raw).head)).nth i).isSome := by
  cases i with
  | zero =>
      have hm : (simMarkCell (ListBlank.mk raw).head).isSome := by
        cases hh : (ListBlank.mk raw).head <;> simp [simMarkCell]
      rw [ListBlank.nth_zero, listBlank_cons_head]
      exact hm
  | succ i =>
      rw [ListBlank.nth_succ, ListBlank.tail_cons, ← ListBlank.nth_succ,
        ListBlank.nth_mk]
      exact hsome (i + 1) hi

/-- Length bounds of the cleaned tail relative to the raw tail. -/
lemma tail_rs_length_bounds {rs raw : List (Option Bool)} {K : ℕ}
    (htail : ListBlank.mk rs =
      (ListBlank.mk raw).tail.cons (simMarkCell (ListBlank.mk raw).head))
    (hrs : ∀ x ∈ rs, x.isSome) (hK : 0 < K)
    (hsome : ∀ i, i < K → (raw.getI i).isSome) :
    K ≤ rs.length ∧ rs.length ≤ raw.length := by
  refine ⟨list_length_ge_of_listBlank_nth_isSome htail K
    (tail_cons_nth_isSome hsome), ?_⟩
  have hne : raw ≠ [] := by
    rintro rfl
    simpa [default] using hsome 0 hK
  exact listBlank_length_le_of_tail_cons _ htail hrs hne

/-- Decoding a cleaned prefix of the raw bits is decoding a prefix of the cells. -/
lemma decodePackedOutputList_eq_take_of_getD (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    {bs : List (List (Option Bool))} {as : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    (hAll : RawBlocksRel
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) bs as)
    {clean : List Bool}
    (hget : ∀ i, clean.getD i false =
      ((rawBlocksRight bs).map (Option.getD · false)).getD i false)
    (hlen : clean.length ≤ ((rawBlocksRight bs).map (Option.getD · false)).length) :
    decodePackedOutputList tm out clean =
      (as.take (clean.length / decListN tm)).map (decListCell tm out) := by
  have hcleanEq := list_take_eq_of_getD_eq clean.length hget le_rfl hlen
  rw [List.take_length] at hcleanEq
  have hfull := decodePackedOutputList_take_rawBlocksRel tm out hAll clean.length hlen
  rw [← hcleanEq] at hfull
  exact hfull

/-- Cells past the output decode to `false`, so a longer prefix only appends `false`s. -/
lemma map_take_append_replicate_of_getI {α : Type} [Inhabited α] (f : α → Bool)
    (xs : List α) {N q : ℕ} (hNq : N ≤ q) (hq : q ≤ xs.length)
    (h : ∀ i, N ≤ i → f (xs.getI i) = false) :
    (xs.take q).map f = (xs.take N).map f ++ List.replicate (q - N) false := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNq
  rw [List.take_add, List.map_append, Nat.add_sub_cancel_left]
  congr 1
  apply List.eq_replicate_iff.2
  refine ⟨by simp; omega, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
  have hi' : N + i < xs.length := by simp at hi; omega
  have := h (N + i) (by omega)
  rw [List.getI_eq_getElem _ hi'] at this
  simpa using this

/-- Decoding the output cells yields the produced output. -/
lemma output_cells_take_decode (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    {cells : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {S : List (TM2to1.PackΓ tm tm.k₁)} {T : List Bool}
    (hle : S.length ≤ cells.length)
    (hcell : ∀ (i : ℕ) (hi : i < S.length),
      decListCell tm out (cells.getI i) = out S[i].1)
    (hS : S.map (fun s => out s.1) = T) :
    (cells.take S.length).map (decListCell tm out) = T := by
  apply List.ext_getElem
  · simp [← hS]; omega
  · intro i hi1 hi2
    have hiS : i < S.length := by simp at hi1; exact hi1.1
    have hiC : i < cells.length := lt_of_lt_of_le hiS hle
    rw [List.getElem_map, List.getElem_take, ← List.getI_eq_getElem _ hiC,
      hcell i hiS]
    subst hS
    simp

/-- The cleaned bits decode to the output followed by trailing `false`s. -/
lemma decodePackedOutputList_clean_eq_append_replicate
    (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    {b : List (Option Bool)} {br : List (List (Option Bool))}
    {rs : List (Option Bool)} {srcQ : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {N : ℕ} {T : List Bool}
    (hAll : RawBlocksRel
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) (b :: br) srcQ)
    (hbLen : b.length = decListN tm)
    (htailShape : ListBlank.mk rs =
      (ListBlank.mk (rawBlocksRight br)).tail.cons
        (simMarkCell (ListBlank.mk (rawBlocksRight br)).head))
    (hN : 1 ≤ N) (hlow : (N - 1) * decListN tm ≤ rs.length)
    (hup : rs.length ≤ (rawBlocksRight br).length)
    (hafter : ∀ i, N ≤ i → decListCell tm out (srcQ.getI i) = false)
    (hdec : (srcQ.take N).map (decListCell tm out) = T) :
    ∃ k, decodePackedOutputList tm out
        ((simMarkBlock b ++ rs).map (Option.getD · false)) = T ++ List.replicate k false := by
  have hePos : 0 < decListN tm := decN_pos tm
  have hsrcLen : (b ++ rawBlocksRight br).length = srcQ.length * decListN tm := by
    have h1 := rawBlocksRight_length_of_rel hAll
    rw [RawBlocksRel.length_eq hAll] at h1
    exact h1
  have hcleanU : ((simMarkBlock b ++ rs).map (Option.getD · false)).length ≤
      ((b ++ rawBlocksRight br).map (Option.getD · false)).length := by
    simp only [List.length_map, List.length_append, simMarkBlock_length]
    omega
  have hcleanL : N * decListN tm ≤
      ((simMarkBlock b ++ rs).map (Option.getD · false)).length := by
    simp only [List.length_map, List.length_append, simMarkBlock_length]
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    simp only [Nat.add_sub_cancel_left] at hlow
    rw [Nat.add_mul, one_mul]
    omega
  have hget := decodePackedOutputList_eq_take_of_getD tm out hAll
    (clean := (simMarkBlock b ++ rs).map (Option.getD · false))
    (by simpa [rawBlocksRight] using clean_bits_getD_eq htailShape)
    (by simpa [rawBlocksRight] using hcleanU)
  have hqN : N ≤ ((simMarkBlock b ++ rs).map (Option.getD · false)).length /
      decListN tm := (Nat.le_div_iff_mul_le hePos).2 hcleanL
  have hqLen : ((simMarkBlock b ++ rs).map (Option.getD · false)).length /
      decListN tm ≤ srcQ.length := by
    apply Nat.le_of_mul_le_mul_right _ hePos
    calc _ ≤ ((simMarkBlock b ++ rs).map (Option.getD · false)).length :=
          Nat.div_mul_le_self _ _
      _ ≤ (b ++ rawBlocksRight br).length := by simpa using hcleanU
      _ = _ := hsrcLen
  refine ⟨((simMarkBlock b ++ rs).map (Option.getD · false)).length /
    decListN tm - N, ?_⟩
  rw [hget, map_take_append_replicate_of_getI _ srcQ hqN hqLen hafter, hdec]

/-- The cleaned bits of a certificate decode to the produced output followed by
trailing `false`s, which `dropTrailingFalse` later removes. -/
lemma decode_clean_eq_output_append_replicate (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (p : PointedMap (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) (Option (TM2to1.PackΓ tm tm.k₁)))
    (hp : ∀ z, p.f z = z.2 tm.k₁)
    {a : TM2to1.Γ' tm.K (TM2to1.PackΓ tm)} {rsrc : List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))}
    {b : List (Option Bool)} {br : List (List (Option Bool))} {rs : List (Option Bool)}
    {S : List (TM2to1.PackΓ tm tm.k₁)} {T : List Bool}
    (hb0 : BlockDecodes (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) b a)
    (hbr0 : RawBlocksRel (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))) br rsrc)
    (hcontent : BlocksContentMarked br rsrc)
    (htailShape : ListBlank.mk rs =
      (ListBlank.mk (rawBlocksRight br)).tail.cons
        (simMarkCell (ListBlank.mk (rawBlocksRight br)).head))
    (hrs : ∀ x ∈ rs, x.isSome)
    (hproj : ListBlank.map p (ListBlank.mk (a :: rsrc)) = ListBlank.mk (S.map some))
    (hS : S.map (fun s => out s.1) = T) (hT : 2 ≤ T.length) :
    ∃ k, decodePackedOutputList tm out
        ((simMarkBlock b ++ rs).map (Option.getD · false)) = T ++ List.replicate k false := by
  have hSlen : S.length = T.length := by rw [← hS]; simp
  have hge := output_cells_length_ge tm p hp hproj
  have hn : S.length - 1 ≤ rsrc.length := by
    simp only [List.length_cons] at hge; omega
  have hne : ∀ i, i < S.length - 1 → rsrc.getI i ≠ default := by
    intro i hi
    have := output_cells_getI_ne_default tm p hp hproj (i + 1) (by omega)
    simpa [List.getI_cons_succ] using this
  have hsome := rawBlocksRight_getI_isSome hbr0 hcontent (S.length - 1) hn hne
  have hKpos : 0 < (S.length - 1) * decListN tm :=
    Nat.mul_pos (by omega) (decN_pos tm)
  have hbounds := tail_rs_length_bounds htailShape hrs hKpos hsome
  have hbLen : b.length = decListN tm := blockDecodes_length hb0
  refine decodePackedOutputList_clean_eq_append_replicate tm out
    (RawBlocksRel.cons hb0 hbr0) hbLen htailShape (by omega) hbounds.1 hbounds.2 ?_ ?_
  · intro i hi
    unfold decListCell
    rw [output_slot_getI_none tm p hp hproj i hi]
  · refine output_cells_take_decode tm out hge ?_ hS
    intro i hi
    unfold decListCell
    rw [output_slot_getI_some tm p hp hproj i hi]

/-- The raw tape decode of a packed TM2 simulation never inspects the produced
value, so the argument depends on the target encoding only through the two
side conditions above.  Stating it once here lets a second producer reuse the
tape reasoning instead of duplicating it. -/
lemma computable_of_raw_decode_generic {α β : Type}
    (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (h : TM2ComputableInPolyTime ea (fun l : List Bool => l)
      (fun x => (eb (f x)).reverse))
    (hends : ∀ x, ∃ xs, eb (f x) = xs ++ [true])
    (hlen2 : ∀ x, 2 ≤ (eb (f x)).length) :
    ∀ x : α, dropTrailingFalse (decodePackedOutputList h.tm h.outputAlphabet
        (simFn h (encodePackedInput h.tm h.inputAlphabet (ea x)))) = eb (f x) := by
  intro x
  obtain ⟨out, hrun, hfirst, hcontent⟩ :=
    sim_run_witness_with_content h x
  let l := encodePackedInput h.tm
    h.inputAlphabet (ea x)
  have hdom :
      (TM0.eval (packedTM0 h.tm).M
        ((BlockEnc.ofFinite (packedTM0 h.tm).Γ).decodeList l)).Dom := by
    obtain ⟨source, hsource⟩ := sim_source_eval_mem h x
    exact (Part.dom_iff_mem).2 ⟨source, hsource.1⟩
  have hsim := simFn_spec h l hdom
    ⟨out, hrun, hfirst⟩
  have htape := machineOutputsInTime_unique_tape_drop hrun hsim.1
  have houtEq : out = simFn h l :=
    tapeSymbols_injective_drop htape
  change dropTrailingFalse (decodePackedOutputList h.tm
      h.outputAlphabet
      (simFn h l)) =
    eb (f x)
  rw [← houtEq]
  dsimp [SimCleanContentCertificate] at hcontent
  rcases hcontent with ⟨c, U, b, br, a0, r, L, R, rs,
    hrel, hU, hR, hshape, hrs, hout, hsrc⟩
  rcases hsrc with ⟨Lsrc, hsourceTape, hsourceOutput⟩
  let tmP := TM2to1.packFinTM2 h.tm
  let pOut : PointedMap (TM2to1.Γ' tmP.K tmP.Γ)
      (Option (tmP.Γ tmP.k₁)) :=
    { f := fun z => z.2 tmP.k₁, map_pt' := by rfl }
  have hsourceProj :
      ListBlank.map pOut c.Tape.right₀ =
        ListBlank.mk ((simPackedOutput h x).map some).reverse := by
    rw [hsourceTape]
    exact tm2to1_addBottom_output_order _ _ _ hsourceOutput
  rcases hrel with ⟨lsrc, rsrc, bl, a,
    hT, hU0, hbl, hbr0, hb0, hblm, hcontent⟩
  have hsourceProj' :
      ListBlank.map pOut (ListBlank.mk (a :: rsrc)) =
        ListBlank.mk ((simPackedOutput h x).reverse.map some) := by
    rw [hT, Tape.mk'_right₀] at hsourceProj
    rw [List.map_reverse]
    exact hsourceProj
  have hSmap :
      (simPackedOutput h x).reverse.map (fun x => h.outputAlphabet x.1) =
        eb (f x) := by
    have hh : (simPackedOutput h x).map (fun x => h.outputAlphabet x.1) =
        (eb (f x)).reverse := by
      simpa [simPackedOutput] using
        (packList_map_equiv (tm := h.tm) h.tm.k₁ h.outputAlphabet
          ((eb (f x)).reverse)
          (TM2to1.mem_usedSymbols_of_haltList h.tm (h.outputsFun x)))
    simpa [List.map_reverse] using congrArg List.reverse hh
  let e := BlockEnc.ofFinite (packedTM0 h.tm).Γ
  have hbLen : b.length = e.n := by
    simpa [e] using blockDecodes_length hb0
  have htailShape :
      ListBlank.mk rs =
        (ListBlank.mk (rawBlocksRight br)).tail.cons
          (simMarkCell (ListBlank.mk (rawBlocksRight br)).head) := by
    rw [← hshape, simCleanPartialWriteTail_eq e b L R hbLen, hR]
  obtain ⟨k, hk⟩ := decode_clean_eq_output_append_replicate h.tm h.outputAlphabet
    pOut (fun _ => rfl) hb0 hbr0 hcontent htailShape hrs hsourceProj' hSmap (hlen2 x)
  rw [hout, hk]
  simpa using dropTrailingFalse_append_false
    (pre := eb (f x)) (tail := List.replicate k false) (Or.inr (hends x))
    (fun _ hb => (List.mem_replicate.mp hb).2)

end GenericRawDecode

end NPComplete.CookLevin

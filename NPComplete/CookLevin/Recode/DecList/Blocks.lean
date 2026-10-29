module

public import NPComplete.CookLevin.Recode.DecList.Output

/-!
# Decoded-list block macros

A decoded output is assembled by reading one aligned symbol block, decoding it,
and appending the corresponding output bit. Keeping this proof at the block
boundary lets iteration compose local tape transitions into a whole run.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

/-- First half of `decListMachine_block_macro`: from `checkInput` over the packed block,
read the block back and seek through the separator to `seekOut` on the output
side, carrying the decoded vector. -/
lemma decListMachine_block_macro_seek (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (pre block outs : List Bool)
    (hblock : block ≠ []) (hlen : block.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = block.reverse ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.checkInput,
          decListForwardTape (pre ++ block.reverse)
            (none :: outs.map some)⟩
        ⟨.seekOut (decListResult tm out v),
          (decListSepStart [] (none :: outs.map some)
            (pre.map some ++ List.replicate (decListN tm) none)).move
              Dir.left⟩
        (pre.reverse.length + 1 +
          (1 + (1 + ((pre ++ block.reverse).length + 1) +
            (2 * block.length - 1)))) := by
  have hblen : 0 < block.length := List.length_pos_of_ne_nil hblock
  obtain ⟨v, hv, h0⟩ := decListMachine_checkInput_to_block tm out pre block
    (none :: outs.map some) hblock hlen
  let b := decListResult tm out v
  have hfinish := decListMachine_readBackFinish_step tm out b
    (decListReadTape (decListN tm) []
      (pre.reverse.map some ++ (none :: outs.map some)) [])
  have h1 := stepsTo_trans _ h0
    (stepsTo_cons _ hfinish (stepsTo_zero _ _))
  rw [decListReadTape_move_left_sep] at h1
  have h1' :
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.checkInput,
          decListForwardTape (pre ++ block.reverse)
            (none :: outs.map some)⟩
        ⟨.seekSep b,
          decListSepStart pre.reverse (none :: outs.map some)
            (List.replicate (decListN tm) none)⟩
        (1 + (1 + ((pre ++ block.reverse).length + 1) +
          (2 * block.length - 1))) := by
    simpa using h1
  have hsep := decListMachine_seekSep_scan tm out b pre.reverse
    (none :: outs.map some) (List.replicate (decListN tm) none) (by
      simp)
  have h2 := stepsTo_trans _ h1' hsep
  exact ⟨v, hv, by
    simpa [b, List.reverse_reverse] using h2⟩

/-- Output half of `decListMachine_block_macro`: from `seekOut` at the left end of the
separator, copy the decoded bit over the outputs and re-check the input prefix,
landing on `checkInput` with the outputs extended. -/
lemma decListMachine_block_macro_output (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (pre outs : List Bool) (b : Bool) :
    ∃ k : ℕ,
        k = (outs.reverse ++ [b]).length + 1 + (outs.length + 1) ∧
        StepsTo (TM0.step (decListMachine tm out))
          ⟨.seekOut b,
            (decListSepStart [] (none :: outs.map some)
              (pre.map some ++ List.replicate (decListN tm) none)).move
                Dir.left⟩
          ⟨.checkInput,
            decListForwardTape pre
              (none :: (outs ++ [b]).map some)⟩ k := by
  cases outs with
  | nil =>
      have hstart :
          (decListSepStart [] (none :: ([] : List Bool).map some)
            (pre.map some ++ List.replicate (decListN tm) none)).move
              Dir.left =
            decListOutStart []
              (none :: pre.map some ++ List.replicate (decListN tm) none) := by
        simp [decListSepStart, decListOutStart,
          Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
          ListBlank.cons_mk, default]
      rw [hstart]
      have hout := decListMachine_seekOut_scan tm out b []
        (none :: pre.map some ++ List.replicate (decListN tm) none)
      have hcheck := decListMachine_checkOutput_scan tm out [b] []
        (pre.map some ++ List.replicate (decListN tm) none)
      have hchain := stepsTo_trans _ hout hcheck
      have htail := decListForwardTape_trailing pre
        (none :: [b].map some) (decListN tm)
      have htail' :
          Tape.mk' (ListBlank.mk
              (none :: [b].reverse.map some ++ [].map some))
            (ListBlank.mk
              (pre.map some ++ List.replicate (decListN tm) none)) =
            decListForwardTape pre (none :: [b].map some) := by
        simpa [List.reverse_cons, List.map_append] using htail
      rw [htail'] at hchain
      refine ⟨_, rfl, ?_⟩
      simpa [decListForwardTape, decListCheckOutputStart,
        tapeSymbols, List.reverse_cons, List.map_append,
        List.append_assoc] using hchain
  | cons c rest =>
      have hstart :
          (decListSepStart [] (none :: (c :: rest).map some)
            (pre.map some ++ List.replicate (decListN tm) none)).move
              Dir.left =
            decListOutStart (c :: rest)
              (none :: pre.map some ++ List.replicate (decListN tm) none) := by
        exact dec_list_sep_out_move_left c rest _
      rw [hstart]
      have hout := decListMachine_seekOut_scan tm out b (c :: rest)
        (none :: pre.map some ++ List.replicate (decListN tm) none)
      have hcheck := decListMachine_checkOutput_scan tm out
        (b :: (c :: rest).reverse) []
        (pre.map some ++ List.replicate (decListN tm) none)
      have hchain := stepsTo_trans _ hout hcheck
      have htail := decListForwardTape_trailing pre
        (none :: ((c :: rest) ++ [b]).map some) (decListN tm)
      have htail' :
          Tape.mk' (ListBlank.mk
              (none :: (b :: (c :: rest).reverse).reverse.map some ++
                [].map some))
            (ListBlank.mk
              (pre.map some ++ List.replicate (decListN tm) none)) =
            decListForwardTape pre
              (none :: ((c :: rest) ++ [b]).map some) := by
        simpa [List.reverse_cons, List.map_append, List.append_assoc]
          using htail
      rw [htail'] at hchain
      refine ⟨_, rfl, ?_⟩
      simpa [decListForwardTape, decListCheckOutputStart,
        tapeSymbols, List.reverse_cons, List.map_append,
        List.append_assoc] using hchain

lemma decListMachine_block_macro (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (pre block outs : List Bool)
    (hblock : block ≠ []) (hlen : block.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = block.reverse ∧ ∃ k : ℕ,
        k ≤ 10 + 4 * pre.length + 4 * block.length +
          4 * outs.length + 4 * decListN tm ∧
        StepsTo (TM0.step (decListMachine tm out))
          ⟨.checkInput,
            decListForwardTape (pre ++ block.reverse)
              (none :: outs.map some)⟩
          ⟨.checkInput,
            decListForwardTape pre
              (none :: (outs ++
                [decListResult tm out v]).map some)⟩ k := by
  obtain ⟨v, hv, hseek⟩ := decListMachine_block_macro_seek tm out pre block outs
    hblock hlen
  obtain ⟨kout, hkout, hchain⟩ := decListMachine_block_macro_output tm out pre outs
    (decListResult tm out v)
  refine ⟨v, hv, kout + (pre.reverse.length + 1 +
    (1 + (1 + ((pre ++ block.reverse).length + 1) +
      (2 * block.length - 1)))), ?_, ?_⟩
  · have hn : 0 < decListN tm := decN_pos tm
    have hrev : block.reverse.length = block.length := by
      simp [List.length_reverse]
    have hboth : (pre ++ block.reverse).length =
        pre.length + block.length := by
      simp [List.length_append]
    have hprev : pre.reverse.length = pre.length := by
      simp
    have houtlen : (outs.reverse ++ [decListResult tm out v]).length =
        outs.length + 1 := by
      simp
    rw [hkout, hboth, hprev, houtlen]
    omega
  · exact stepsTo_trans _ hseek hchain

/-- Reach `seekOut` after reading the block and crossing the separator. -/
lemma decListMachine_seekEnd_block_macro_seek (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (pre block : List Bool)
    (hblock : block ≠ []) (hlen : block.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = block.reverse ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false, decListForwardTape (pre ++ block.reverse) []⟩
        ⟨.seekOut (decListResult tm out v),
          (decListSepStart [] []
            (pre.map some ++ List.replicate (decListN tm) none)).move Dir.left⟩
        (pre.reverse.length + 1 +
          (1 + ((pre ++ block.reverse).length + 1 + (2 * block.length - 1)))) := by
  have hs := decListMachine_seekEnd_to_block tm out false pre block [] hblock
  obtain ⟨v, hv, hwalk⟩ := decListMachine_readBack_walk tm out false
    ⟨0, by omega⟩ .nil block (pre.reverse.map some) [] hblock
    (by simpa using hlen)
  let b := decListResult tm out v
  let R := pre.map some ++ List.replicate (decListN tm) none
  have hwalk' :
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.readBack false ⟨0, by omega⟩ .nil,
          decListReadTape 0 block (pre.reverse.map some ++ []) []⟩
        ⟨.readBackFinish (decListResult tm out v),
          decListReadTape block.length [] (pre.reverse.map some) []⟩
        (2 * block.length - 1) := by
    simpa using hwalk
  have hfinish := decListMachine_readBackFinish_step tm out b
    (decListReadTape (decListN tm) [] (pre.reverse.map some) [])
  have hfinish' :
      TM0.step (decListMachine tm out)
          ⟨.readBackFinish (decListResult tm out v),
            decListReadTape block.length [] (pre.reverse.map some) []⟩ =
        some ⟨.seekSep (decListResult tm out v),
          (decListReadTape block.length [] (pre.reverse.map some) []).move Dir.left⟩ := by
    simpa [b, hlen] using hfinish
  have h0 := stepsTo_trans _ hs hwalk'
  have h1 := stepsTo_trans _ h0
    (stepsTo_cons _ hfinish' (stepsTo_zero _ _))
  have hmove := decListReadTape_move_left_sep block.length pre.reverse [] []
  have hmove' :
      (decListReadTape block.length [] (pre.reverse.map some ++ []) []).move Dir.left =
        decListSepStart pre.reverse [] (List.replicate (decListN tm) none) := by
    simpa [hlen, List.append_nil] using hmove
  have hmove'' :
      (decListReadTape block.length [] (pre.reverse.map some) []).move Dir.left =
        decListSepStart pre.reverse [] (List.replicate (decListN tm) none) := by
    simpa [List.append_nil] using hmove'
  rw [hmove''] at h1
  have h1' :
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false, decListForwardTape (pre ++ block.reverse) []⟩
        ⟨.seekSep b,
          decListSepStart pre.reverse [] (List.replicate (decListN tm) none)⟩
        ((pre ++ block.reverse).length + 1 +
          (1 + (2 * block.length - 1))) := by
    simpa [b, R, hlen, List.length_append, List.append_nil,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
  have hsep := decListMachine_seekSep_scan tm out b pre.reverse []
    (List.replicate (decListN tm) none) (by
      change (default : Option Bool) = none
      exact Option.default_eq_none)
  have h2 := stepsTo_trans _ h1' hsep
  have h2' :
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false, decListForwardTape (pre ++ block.reverse) []⟩
        ⟨.seekOut b, (decListSepStart [] [] R).move Dir.left⟩
        (pre.reverse.length + 1 +
          (1 + ((pre ++ block.reverse).length + 1 + (2 * block.length - 1)))) := by
    simpa [b, R, List.reverse_reverse, List.length_append,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h2
  exact ⟨v, by simpa using hv, by simpa [b] using h2'⟩

/-- Emit the decoded result and re-check the input prefix from the empty output tape. -/
lemma decListMachine_seekEnd_block_macro_output (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (pre : List Bool) (b : Bool) :
    StepsTo (TM0.step (decListMachine tm out))
      ⟨.seekOut b,
        (decListSepStart [] []
          (pre.map some ++ List.replicate (decListN tm) none)).move Dir.left⟩
      ⟨.checkInput, decListForwardTape pre (none :: [b].map some)⟩ 3 := by
  let R := pre.map some ++ List.replicate (decListN tm) none
  have hstart : (decListSepStart [] [] R).move Dir.left =
      decListOutStart [] (none :: R) := by
    simp [decListSepStart, decListOutStart, Tape.move_left_mk',
      ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, default]
  rw [hstart]
  have hout := decListMachine_seekOut_scan tm out b [] (none :: R)
  have hcheck := decListMachine_checkOutput_scan tm out [b] [] R
  have hchain := stepsTo_trans _ hout hcheck
  have htail := decListForwardTape_trailing pre (none :: [b].map some)
    (decListN tm)
  have htail' :
      Tape.mk' (ListBlank.mk (none :: [b].reverse.map some ++ [].map some))
        (ListBlank.mk R) = decListForwardTape pre (none :: [b].map some) := by
    simpa [List.reverse_cons, List.map_append] using htail
  rw [htail'] at hchain
  simpa [decListForwardTape, decListCheckOutputStart, tapeSymbols,
    List.reverse_cons, List.map_append, List.append_assoc] using hchain

lemma decListMachine_seekEnd_block_macro (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (pre block : List Bool)
    (hblock : block ≠ []) (hlen : block.length = decListN tm) :
    ∃ v : List.Vector Bool (decListN tm),
      v.toList = block.reverse ∧ ∃ k : ℕ,
      k ≤ 10 + 4 * pre.length + 4 * block.length + 4 * decListN tm ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.seekEnd false,
          decListForwardTape (pre ++ block.reverse) []⟩
        ⟨.checkInput,
          decListForwardTape pre
            (none :: [decListResult tm out v].map some)⟩ k := by
  obtain ⟨v, hv, hseek⟩ :=
    decListMachine_seekEnd_block_macro_seek tm out pre block hblock hlen
  have hblockpos : 0 < block.length := List.length_pos_of_ne_nil hblock
  let nseek := pre.reverse.length + 1 +
    (1 + ((pre ++ block.reverse).length + 1 + (2 * block.length - 1)))
  let k := 3 + nseek
  have houtput := decListMachine_seekEnd_block_macro_output tm out pre
    (decListResult tm out v)
  refine ⟨v, hv, k, ?_, ?_⟩
  · dsimp [k, nseek]
    have hpre : pre.reverse.length = pre.length := by simp
    have hboth : (pre ++ block.reverse).length = pre.length + block.length := by simp
    rw [hpre, hboth]
    omega
  · exact stepsTo_trans (t₁ := nseek) (t₂ := 3) _ hseek houtput

def DecListRawBlock (tm : FinTM2) :=
  { b : List Bool // b.length = decListN tm }

noncomputable def decListRawBlockResult (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (b : DecListRawBlock tm) : Bool :=
  decListResult tm out
    ⟨b.1.reverse, by rw [List.length_reverse]; exact b.2⟩

def decListRawBlocksBits (tm : FinTM2)
    (blocks : List (DecListRawBlock tm)) : List Bool :=
  (blocks.map (fun b => b.1.reverse)).flatten

lemma decListRawBlocksBits_exists (tm : FinTM2) {raw : List Bool}
    (hdiv : decListN tm ∣ raw.length) :
    ∃ blocks : List (DecListRawBlock tm),
      decListRawBlocksBits tm blocks = raw := by
  have main : ∀ len : ℕ, ∀ xs : List Bool, xs.length = len →
      decListN tm ∣ xs.length →
      ∃ blocks : List (DecListRawBlock tm),
        decListRawBlocksBits tm blocks = xs := by
    intro len
    induction len using Nat.strong_induction_on with
    | h len ih =>
        intro xs hxs hdiv'
        by_cases hnil : xs = []
        · subst xs
          exact ⟨[], by simp [decListRawBlocksBits]⟩
        obtain ⟨pre, block, hsplit, hblock, hblocklen, hprediv⟩ :=
          dec_list_split_last_block (decN_pos tm) hnil hdiv'
        have hblockpos : 0 < block.length := by
          rw [hblocklen]
          exact decN_pos tm
        have hprelt : pre.length < xs.length := by
          rw [hsplit]
          simp only [List.length_append, List.length_reverse]
          omega
        have hprelt' : pre.length < len := by simpa [hxs] using hprelt
        obtain ⟨blocks, hblocks⟩ := ih pre.length hprelt' pre rfl hprediv
        let b : DecListRawBlock tm := ⟨block, hblocklen⟩
        refine ⟨blocks ++ [b], ?_⟩
        calc
          decListRawBlocksBits tm (blocks ++ [b]) =
              decListRawBlocksBits tm blocks ++ b.1.reverse := by
            simp [decListRawBlocksBits]
          _ = pre ++ block.reverse := by simp [hblocks, b]
          _ = xs := hsplit.symm
  exact main raw.length raw rfl hdiv

lemma decodePackedOutputList_raw_blocks (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (blocks : List (DecListRawBlock tm)) :
    decodePackedOutputList tm out (decListRawBlocksBits tm blocks) =
      blocks.map (decListRawBlockResult tm out) := by
  let e := BlockEnc.ofFinite
    (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  induction blocks with
  | nil =>
      change (e.decodeList []).map (decListCell tm out) = []
      rw [e.decodeList_nil]
      rfl
  | cons b blocks ih =>
      let v : List.Vector Bool e.n :=
          ⟨b.1.reverse, by rw [List.length_reverse]; exact b.2⟩
      have hn : 0 < e.n := by
        simpa [e, decListN, decN] using decN_pos tm
      have hconcat : decListRawBlocksBits tm (b :: blocks) =
          b.1.reverse ++ decListRawBlocksBits tm blocks := by
        simp [decListRawBlocksBits]
      have hresult : decListCell tm out (e.dec v) =
          decListRawBlockResult tm out b := by
        change (match (e.dec v).2 tm.k₁ with
          | some x => out x.1
          | none => false) = _
        rfl
      change (e.decodeList (decListRawBlocksBits tm (b :: blocks))).map
          (decListCell tm out) = _
      rw [hconcat]
      change (e.decodeList (v.toList ++ decListRawBlocksBits tm blocks)).map
          (decListCell tm out) = _
      rw [e.decodeList_append_block hn v
        (decListRawBlocksBits tm blocks)]
      rw [List.map_cons, hresult]
      simpa [decodePackedOutputList, e] using ih

lemma decListMachine_raw_blocks_iter_bound (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (blocks : List (DecListRawBlock tm))
    (outs : List Bool) :
    ∃ k : ℕ,
      k ≤ (blocks.length + 1) *
        (20 + 8 * (decListRawBlocksBits tm blocks).length +
          8 * outs.length + 8 * decListN tm) ∧
      StepsTo (TM0.step (decListMachine tm out))
        ⟨.checkInput,
          decListForwardTape (decListRawBlocksBits tm blocks)
            (none :: outs.map some)⟩
        ⟨.checkInput,
          decListForwardTape [] (none ::
            (outs ++ blocks.reverse.map
              (decListRawBlockResult tm out)).map some)⟩ k := by
  induction blocks using List.reverseRecOn generalizing outs with
  | nil =>
      refine ⟨0, by simp [decListRawBlocksBits], ?_⟩
      simpa [decListRawBlocksBits] using
        (stepsTo_zero (TM0.step (decListMachine tm out))
          ⟨.checkInput, decListForwardTape [] (none :: outs.map some)⟩)
  | append_singleton blocks b ih =>
      let block := b.1
      have hblock : block ≠ [] := by
        intro hb
        have hzero : block.length = 0 := by simp [hb]
        have hlen := b.2
        dsimp [block] at hzero
        rw [hzero] at hlen
        have hn : 0 < decListN tm := decN_pos tm
        omega
      have hlen : block.length = decListN tm := b.2
      obtain ⟨v, hv, k₁, hk₁, hmacro⟩ := decListMachine_block_macro
        tm out (decListRawBlocksBits tm blocks) block outs hblock hlen
      let bvec : List.Vector Bool (decListN tm) :=
        ⟨block.reverse, by
          dsimp [block]
          rw [List.length_reverse]
          exact hlen⟩
      have hres : decListResult tm out v =
          decListRawBlockResult tm out b := by
        have hvv : v = bvec := by
          apply List.Vector.eq
          simpa [bvec, block] using hv
        subst v
        rfl
      obtain ⟨k₂, hk₂, hih⟩ := ih
        (outs ++ [decListRawBlockResult tm out b])
      rw [hres] at hmacro
      have hchain := stepsTo_trans _ hmacro hih
      refine ⟨k₂ + k₁, ?_, ?_⟩
      · let C := 20 + 8 *
            (decListRawBlocksBits tm blocks).length +
            8 * outs.length + 16 * decListN tm
        have hn : 0 < decListN tm := decN_pos tm
        have hC₁ : k₁ ≤ C := by
          dsimp [C]
          simp [block, hlen] at hk₁
          omega
        have hk₂' : k₂ ≤ (blocks.length + 1) * C := by
          have hfactor :
              20 + 8 * (decListRawBlocksBits tm blocks).length +
                  8 * (outs ++ [decListRawBlockResult tm out b]).length +
                  8 * decListN tm ≤ C := by
            simp [C, List.length_append]
            omega
          exact hk₂.trans (Nat.mul_le_mul_left _ hfactor)
        have hsum : k₂ + k₁ ≤ (blocks.length + 2) * C := by
          calc
            k₂ + k₁ ≤ (blocks.length + 1) * C + C :=
              Nat.add_le_add hk₂' hC₁
            _ = (blocks.length + 2) * C := by
              simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
              omega
        have hbits :
            (decListRawBlocksBits tm (blocks ++ [b])).length =
              (decListRawBlocksBits tm blocks).length + decListN tm := by
          simp [decListRawBlocksBits, block, hlen]
        rw [hbits]
        have hC : C = 20 + 8 *
            ((decListRawBlocksBits tm blocks).length + decListN tm) +
            8 * outs.length + 8 * decListN tm := by
          dsimp [C]
          omega
        rw [hC] at hsum
        simpa [List.length_append] using hsum
      · simpa [hres, block, decListRawBlocksBits,
          List.flatMap_append, List.reverse_append, List.reverse_cons,
          List.map_append, List.append_assoc] using hchain

end NPComplete.CookLevin

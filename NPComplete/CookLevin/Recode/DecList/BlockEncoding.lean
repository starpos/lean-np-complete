module

public import NPComplete.CookLevin.Recode.DecList.Foundation

/-!
# Block-Encoded List Machines

A raw packed input may end partway through a fixed-width block, and the list decoder must ignore
that partial block. This module wraps the raw machine in its finite-support package
and proves the block-decomposition facts behind that behaviour: a short trailing block decodes to
nothing, and a raw input splits into complete blocks followed by a short remainder.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

noncomputable def decListRawAux (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0ComputableAux Bool where
  Λ := RawDecListPhase (decListN tm)
  M := decListRawMachine tm out
  S := decListRawSupport _
  supports := decListRawMachine_supports tm out

/-!
  A partial final block is semantically ignored by `BlockEnc.decodeList`.
  This pure list fact is kept separate from the physical preprocessing
  relation of the raw decoder.
-/
lemma BlockEnc.decodeList_append_short
    {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (hn : 0 < e.n)
    (pre suffix : List Bool) (hpre : e.n ∣ pre.length)
    (hsuffix : suffix.length < e.n) :
    e.decodeList (pre ++ suffix) = e.decodeList pre := by
  obtain ⟨q, hq⟩ := hpre
  have main : ∀ q : ℕ, ∀ xs : List Bool, e.n * q = xs.length →
      e.decodeList (xs ++ suffix) = e.decodeList xs := by
    intro q
    induction q with
    | zero =>
        intro xs hlen
        cases xs with
        | nil =>
            rw [e.decodeList_nil]
            exact e.decodeList_of_short (Or.inr hsuffix)
        | cons bit rest =>
            simp at hlen
    | succ q ih =>
        intro xs hlen
        have hlen' : e.n * q + e.n = xs.length := by
          simpa [Nat.mul_succ] using hlen
        have hsize : e.n ≤ xs.length := by omega
        let v : List.Vector Bool e.n :=
          ⟨xs.take e.n, by simp [List.length_take, hsize]⟩
        have hsplit : xs = xs.take e.n ++ xs.drop e.n :=
          (List.take_append_drop e.n xs).symm
        have hdrop_len : e.n * q = (xs.drop e.n).length := by
          rw [List.length_drop, ← hlen']
          omega
        have htail := ih (xs.drop e.n) hdrop_len
        calc
          e.decodeList (xs ++ suffix) =
              e.decodeList ((xs.take e.n ++ xs.drop e.n) ++ suffix) := by
            exact congrArg (fun z => e.decodeList (z ++ suffix)) hsplit
          _ = e.dec v :: e.decodeList (xs.drop e.n ++ suffix) := by
            rw [List.append_assoc]
            exact e.decodeList_append_block hn v _
          _ = e.dec v :: e.decodeList (xs.drop e.n) :=
            congrArg (fun z => e.dec v :: z) htail
          _ = e.decodeList (xs.take e.n ++ xs.drop e.n) := by
            symm
            exact e.decodeList_append_block hn v _
          _ = e.decodeList xs := congrArg e.decodeList hsplit.symm
  exact main q pre hq.symm

lemma decodePackedOutputList_append_short (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (pre suffix : List Bool)
    (hpre : decListN tm ∣ pre.length)
    (hsuffix : suffix.length < decListN tm) :
    decodePackedOutputList tm out (pre ++ suffix) =
      decodePackedOutputList tm out pre := by
  let e := BlockEnc.ofFinite
    (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  have hpre' : e.n ∣ pre.length := by
    simpa [e, decListN] using hpre
  have hsuffix' : suffix.length < e.n := by
    simpa [e, decListN] using hsuffix
  change (e.decodeList (pre ++ suffix)).map (decListCell tm out) =
    (e.decodeList pre).map (decListCell tm out)
  rw [e.decodeList_append_short (decN_pos tm) pre suffix hpre' hsuffix']

lemma dec_list_split_last_block {n : ℕ} (hn : 0 < n)
    {raw : List Bool} (hraw : raw ≠ []) (hdiv : n ∣ raw.length) :
    ∃ pre block : List Bool,
      raw = pre ++ block.reverse ∧ block ≠ [] ∧
      block.length = n ∧ n ∣ pre.length := by
  obtain ⟨q, hq⟩ := hdiv
  have hlenpos : 0 < raw.length := List.length_pos_of_ne_nil hraw
  have hqpos : 0 < q := by
    by_contra hq0
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
    subst q
    have hzero : raw.length = 0 := by simpa using hq
    omega
  have hlen : n ≤ raw.length := by
    rw [hq]
    exact Nat.le_mul_of_pos_right _ hqpos
  let k := raw.length - n
  let pre := raw.take k
  let block := (raw.drop k).reverse
  have hk : k ≤ raw.length := by
    dsimp [k]
    exact Nat.sub_le _ _
  have hprelen : pre.length = raw.length - n := by
    simp [pre, k]
  have hblocklen : block.length = n := by
    simp [block, k]
    omega
  have hraw' : raw = pre ++ block.reverse := by
    dsimp [pre, block]
    rw [List.reverse_reverse]
    exact (List.take_append_drop k raw).symm
  have hprediv : n ∣ pre.length := by
    refine ⟨q - 1, ?_⟩
    rw [hprelen, hq]
    simp [Nat.mul_sub_left_distrib]
  refine ⟨pre, block, hraw', ?_, hblocklen, hprediv⟩
  intro hblock
  rw [hblock] at hblocklen
  simp at hblocklen
  omega

lemma dec_list_raw_canonical_decompose {n : ℕ} (hn : 0 < n)
    (raw : List Bool) :
    ∃ pre suf : List Bool,
      raw = pre ++ suf ∧
      pre = (raw.reverse.drop (raw.length % n)).reverse ∧
      n ∣ pre.length ∧
      suf.length = raw.length % n ∧
      suf.length < n := by
  let rem := raw.length % n
  let k := raw.length - rem
  let pre := raw.take k
  let suf := raw.drop k
  have hrem : rem ≤ raw.length := by
    dsimp [rem]
    exact Nat.mod_le _ _
  have hk : k ≤ raw.length := by
    dsimp [k]
    omega
  have hprelen : pre.length = k := by
    simp [pre, List.length_take, Nat.min_eq_left hk]
  have hcanon : pre = (raw.reverse.drop rem).reverse := by
    have hrev := List.reverse_drop (l := raw.reverse) (i := rem)
    simpa [pre, k, rem, List.length_reverse] using hrev.symm
  refine ⟨pre, suf, ?_, hcanon, ?_, ?_, ?_⟩
  · exact (List.take_append_drop k raw).symm
  · rw [hprelen]
    dsimp [k, rem]
    exact Nat.dvd_sub_mod raw.length
  · simp [suf, k]
    omega
  · simp [suf, k]
    have hlt := Nat.mod_lt raw.length hn
    omega

def decListRawCount {n : ℕ} (hn : 0 < n) : List Bool → Fin n → Fin n
  | [], i => i
  | _ :: raw, i => decListRawCount hn raw (decListFinNext hn i)

lemma decListFinNext_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (decListFinNext hn i).val = (i.val + 1) % n := by
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    simp [decListFinNext, h]
  · have heq : i.val + 1 = n := by omega
    simp [decListFinNext, heq]

lemma decListRawCount_val {n : ℕ} (hn : 0 < n) (raw : List Bool)
    (i : Fin n) :
    (decListRawCount hn raw i).val = (i.val + raw.length) % n := by
  induction raw generalizing i with
  | nil =>
      simp [decListRawCount, Nat.mod_eq_of_lt i.isLt]
  | cons b raw ih =>
      rw [decListRawCount, ih, decListFinNext_val hn]
      simp only [List.length_cons, Nat.add_mod_mod, Nat.add_comm,
        Nat.add_left_comm]


end NPComplete.CookLevin

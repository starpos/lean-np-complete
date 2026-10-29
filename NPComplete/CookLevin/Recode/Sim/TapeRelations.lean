module

public import NPComplete.CookLevin.Recode.Sim.BlockEncoding

/-!
# Encoded Tape Relations

Raw block encoding has both semantic and physical concerns: `ListBlank` erases trailing blanks, while
cleanup tracks which cells are physically occupied. This module separates these invariants and their
conversion lemmas, letting execution proofs strengthen or weaken tape state as needed.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

inductive RawBlocksRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) : List (List (Option Bool)) → List Γ → Prop
  | nil : RawBlocksRel e [] []
  | cons {b : List (Option Bool)} {a : Γ}
      {bs : List (List (Option Bool))} {as : List Γ} :
      BlockDecodes e b a → RawBlocksRel e bs as →
      RawBlocksRel e (b :: bs) (a :: as)

lemma RawBlocksRel.length_eq {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {bs : List (List (Option Bool))} {as : List Γ}
    (h : RawBlocksRel e bs as) : bs.length = as.length := by
  induction h <;> simp [*]

lemma RawBlocksRel.head {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {b : List (Option Bool)} {a : Γ}
    {bs : List (List (Option Bool))} {as : List Γ}
    (h : RawBlocksRel e (b :: bs) (a :: as)) : BlockDecodes e b a := by
  cases h
  assumption

def rawBlocksLeft (bs : List (List (Option Bool))) : List (Option Bool) :=
  bs.flatMap List.reverse

def rawBlocksRight (bs : List (List (Option Bool))) : List (Option Bool) :=
  bs.flatten

lemma rawBlocksLeft_marked {bs : List (List (Option Bool))}
    (h : BlocksMarked bs) :
    ∀ x ∈ rawBlocksLeft bs, x.isSome := by
  induction bs with
  | nil =>
      simp [rawBlocksLeft]
  | cons b bs ih =>
      intro x hx
      have hb : BlockMarked b := (blocksMarked_cons.mp h).1
      have hbs : BlocksMarked bs := (blocksMarked_cons.mp h).2
      simp only [rawBlocksLeft, List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hb x (by simpa using hx)
      · exact ih hbs x hx

lemma optionListDataCount_eq_length_of_all_some
    {l : List (Option Bool)}
    (h : ∀ x ∈ l, x.isSome) :
    optionListDataCount l = l.length := by
  induction l with
  | nil => simp [optionListDataCount]
  | cons x xs ih =>
      have hx : x.isSome := h x (by simp)
      have hxs : ∀ y ∈ xs, y.isSome := by
        intro y hy
        exact h y (by simp [hy])
      cases x <;> simp_all [optionListDataCount]

lemma rawBlocksLeft_length_of_rel {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {bl : List (List (Option Bool))} {lsrc : List Γ}
    (hbl : RawBlocksRel e bl lsrc) :
    (rawBlocksLeft bl).length = bl.length * e.n := by
  induction hbl with
  | nil => simp [rawBlocksLeft]
  | @cons b a bs as hb hbs ih =>
      change (b.reverse ++ rawBlocksLeft bs).length =
        (bs.length + 1) * e.n
      rw [List.length_append, List.length_reverse, ih,
        blockDecodes_length hb]
      simp [Nat.add_mul, Nat.add_comm]

lemma rawBlocksRight_length_of_rel {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {br : List (List (Option Bool))} {r : List Γ}
    (hbr : RawBlocksRel e br r) :
    (rawBlocksRight br).length = br.length * e.n := by
  induction hbr with
  | nil => simp [rawBlocksRight]
  | @cons b a bs as hb hbs ih =>
      simp only [rawBlocksRight, List.flatten_cons, List.length_append,
        List.length_cons]
      rw [blockDecodes_length hb]
      have ih' : bs.flatten.length = bs.length * e.n := by
        simpa [rawBlocksRight] using ih
      rw [ih']
      simp [Nat.add_mul, Nat.add_comm]

/-! `RawTapeMarkedRel` is a representative-level relation: it records that every finite block in
the chosen physical span is occupied.  `ListBlank` quotients away trailing blanks, so the block-level
relation alone would not say which cells have been visited. -/

def RawTapeMarkedRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop :=
  ∃ (l r : List Γ) (bl br : List (List (Option Bool))) (a : Γ)
    (b : List (Option Bool)),
    T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)) ∧
    U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)) ∧
    RawBlocksRel e bl l ∧ RawBlocksRel e br r ∧ BlockDecodes e b a ∧
    BlocksMarked bl ∧ BlockMarked b ∧ BlocksMarked br

/-! The clean simulator relates its source tape to a raw tape whose left
    blocks are marked, while retaining the block-level semantic relation
    (`RawBlocksRel` and `BlockDecodes`). -/

def RawTapeCleanRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop :=
  ∃ (l r : List Γ) (bl br : List (List (Option Bool))) (a : Γ)
    (b : List (Option Bool)),
    T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)) ∧
    U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)) ∧
    RawBlocksRel e bl l ∧ RawBlocksRel e br r ∧
    BlockDecodes e b a ∧ BlocksMarked bl
def BlocksContentMarked {Γ : Type} [Inhabited Γ]
    (bs : List (List (Option Bool))) (xs : List Γ) : Prop :=
  match bs, xs with
  | [], [] => True
  | b :: bs, x :: xs =>
      (x = default ∨ BlockMarked b) ∧ BlocksContentMarked bs xs
  | _, _ => False

lemma blocksContentMarked_of_marked {Γ : Type} [Inhabited Γ]
    {bs : List (List (Option Bool))} {xs : List Γ}
    (h : bs.length = xs.length)
    (hm : ∀ b ∈ bs, BlockMarked b) :
    BlocksContentMarked bs xs := by
  induction bs generalizing xs with
  | nil =>
      cases xs with
      | nil => simp [BlocksContentMarked]
      | cons x xs =>
          simp only [List.length_cons, List.length_nil] at h
          omega
  | cons b bs ih =>
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at h
          omega
      | cons x xs =>
          simp only [BlocksContentMarked]
          refine ⟨Or.inr (hm b (by simp)), ?_⟩
          apply ih
          · simp only [List.length_cons] at h ⊢
            omega
          · intro b' hb'
            exact hm b' (by simp [hb'])

def RawTapeCleanContentRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop :=
  ∃ (l r : List Γ) (bl br : List (List (Option Bool))) (a : Γ)
    (b : List (Option Bool)),
    T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)) ∧
    U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)) ∧
    RawBlocksRel e bl l ∧ RawBlocksRel e br r ∧
    BlockDecodes e b a ∧ BlocksMarked bl ∧
    BlocksContentMarked br r

def RawTapeCleanContentRelAt {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool))
    (b : List (Option Bool)) (br : List (List (Option Bool))) : Prop :=
  ∃ (l r : List Γ) (bl : List (List (Option Bool))) (a : Γ),
    T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)) ∧
    U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)) ∧
    RawBlocksRel e bl l ∧ RawBlocksRel e br r ∧
    BlockDecodes e b a ∧ BlocksMarked bl ∧
    BlocksContentMarked br r

lemma rawTapeCleanContentRel_to_rawTapeCleanRel {Γ : Type} [Inhabited Γ]
    [Finite Γ] {e : BlockEnc Γ} {T : Tape Γ} {U : Tape (Option Bool)}
    (h : RawTapeCleanContentRel e T U) : RawTapeCleanRel e T U := by
  rcases h with ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm, _⟩
  exact ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm⟩

/-! A boundary configuration records the marker written at the first cell of
the next block while the source head is still on the current cell.  The
current block is complete and marked; only the next block may be partial. -/

def RawTapeCleanBoundaryRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop :=
  ∃ (l r : List Γ) (bl br : List (List (Option Bool)))
    (a x : Γ) (old pref rem : List (Option Bool)),
    T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: x :: r)) ∧
    U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (old ++ pref ++ rem ++ rawBlocksRight br)) ∧
    RawBlocksRel e bl l ∧ RawBlocksRel e br r ∧
    BlockDecodes e old a ∧ BlockMarked old ∧ BlocksMarked bl ∧
    BlockDecodes e (pref ++ rem) x ∧
    0 < pref.length ∧ pref.length + rem.length = e.n ∧
    BlockMarked pref

/-! The state relation used by the clean wrapper.  The ordinary branch is
    retained verbatim so existing block-level proofs continue to use the
    stronger quotient relation; the boundary branch records exactly the
    additional physical state needed by the first read of a fresh block. -/

inductive RawTapeCleanStateRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop where
  | normal : RawTapeCleanRel e T U → RawTapeCleanStateRel e T U
  | boundary : RawTapeCleanBoundaryRel e T U → RawTapeCleanStateRel e T U

/-! A boundary carries a complete marked current block, so it can also be
    viewed as an ordinary clean relation by treating the partial next block as
    the first complete block on the source's right.  This bridge lets the
    ordinary macro preservation lemmas consume a boundary state. -/

lemma rawTapeCleanBoundaryRel_to_rawTapeCleanRel {Γ : Type} [Inhabited Γ]
    [Finite Γ] {e : BlockEnc Γ} {T : Tape Γ} {U : Tape (Option Bool)}
    (h : RawTapeCleanBoundaryRel e T U) : RawTapeCleanRel e T U := by
  rcases h with ⟨l, r, bl, br, a, x, old, pref, rem, hT, hU,
    hbl, hbr, hold, _, hblm, hnext, _, _, _⟩
  have hnextrel : RawBlocksRel e ((pref ++ rem) :: br) (x :: r) :=
    RawBlocksRel.cons hnext hbr
  refine ⟨l, x :: r, bl, (pref ++ rem) :: br, a, old, hT, ?_,
    hbl, hnextrel, hold, hblm⟩
  simpa [rawBlocksRight, List.append_assoc] using hU

lemma listBlank_mk_append_all_none {Γ : Type} [Inhabited Γ]
    (xs ys : List Γ) (hys : ∀ x ∈ ys, x = default) :
    ListBlank.mk (xs ++ ys) = ListBlank.mk xs := by
  apply Quotient.sound'
  apply Or.inr
  refine ⟨ys.length, ?_⟩
  have hy : ys = List.replicate ys.length default := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
        have hy : y = default := hys y (by simp)
        have hys' : ∀ x ∈ ys, x = default := by
          intro x hx
          exact hys x (by simp [hx])
        have hi := ih hys'
        rw [hy, hi]
        simp only [List.length_cons, List.length_replicate,
          List.replicate_succ]
  rw [hy]
  simp only [List.length_replicate]

lemma listBlank_mk_append_default {Γ : Type} [Inhabited Γ]
    (xs : List Γ) :
    ListBlank.mk (xs ++ [default]) = ListBlank.mk xs := by
  apply listBlank_mk_append_all_none
  intro x hx
  simp at hx
  exact hx

lemma listBlank_mk_replicate_none (n : ℕ) :
    ListBlank.mk (List.replicate n (none : Option Bool)) =
      ListBlank.mk [] := by
  have h := listBlank_mk_append_all_none
    ([] : List (Option Bool)) (List.replicate n none) (by
      intro x hx
      simp at hx
      exact hx.2)
  simpa using h

lemma rawTapeMarkedRel_to_rawTapeCleanRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {T : Tape Γ} {U : Tape (Option Bool)}
    (h : RawTapeMarkedRel e T U) : RawTapeCleanRel e T U := by
  rcases h with ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm, _, _⟩
  exact ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm⟩

def rawEncodeBlock {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) : List (Option Bool) :=
  (e.enc a).toList.map some

lemma blockMarked_rawEncodeBlock {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) : BlockMarked (rawEncodeBlock e a) := by
  intro x hx
  simp only [rawEncodeBlock, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  simp

lemma blocksMarked_map_rawEncodeBlock {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (l : List Γ) :
    BlocksMarked (l.map (rawEncodeBlock e)) := by
  induction l with
  | nil => exact blocksMarked_nil
  | cons a l ih =>
      simp only [List.map_cons, blocksMarked_cons]
      exact ⟨blockMarked_rawEncodeBlock e a, ih⟩

lemma rawEncodeBlock_decodes {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) :
    BlockDecodes e (rawEncodeBlock e a) a := by
  exact blockDecodes_enc e a

lemma rawBlocksRel_encodeList {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (l : List Γ) :
    RawBlocksRel e (l.map (rawEncodeBlock e)) l := by
  induction l with
  | nil => exact RawBlocksRel.nil
    | cons a l ih =>
        simp only [List.map_cons]
        exact RawBlocksRel.cons (rawEncodeBlock_decodes e a) ih

lemma rawTapeCleanContentRel_mk₁_encodeList {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (a : Γ) (r : List Γ) :
    RawTapeCleanContentRel e (Tape.mk₁ (a :: r))
      (Tape.mk₁ ((a :: r).flatMap (rawEncodeBlock e))) := by
  have hflat : ∀ xs : List Γ, xs.flatMap (rawEncodeBlock e) =
      (xs.map (rawEncodeBlock e)).flatten := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have hmark : ∀ b ∈ r.map (rawEncodeBlock e), BlockMarked b := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact blockMarked_rawEncodeBlock e x
  have hcontent : BlocksContentMarked (r.map (rawEncodeBlock e)) r := by
    apply blocksContentMarked_of_marked
    · simp
    · exact hmark
  refine ⟨[], r, [], r.map (rawEncodeBlock e), a,
    rawEncodeBlock e a, ?_, ?_, RawBlocksRel.nil,
    rawBlocksRel_encodeList e r, rawEncodeBlock_decodes e a,
    blocksMarked_nil, hcontent⟩
  · simp [Tape.mk₁, Tape.mk₂]
  · simp [Tape.mk₁, Tape.mk₂, rawBlocksLeft, rawBlocksRight, hflat r]

lemma blockDecodes_mark_head_tail {Γ : Type} [Inhabited Γ] [Finite Γ]
    {e : BlockEnc Γ} {b : List (Option Bool)} {a : Γ}
    (h : BlockDecodes e b a) (hn : 0 < e.n) :
    BlockDecodes e (simMarkCell b.headI :: b.tail) a := by
  have hlen : b.length = e.n := blockDecodes_length h
  have hbne : b ≠ [] := by
    intro hnil
    have : e.n = 0 := by simpa [hnil] using hlen.symm
    omega
  cases b with
  | nil => exact (hbne rfl).elim
  | cons z zs =>
      apply blockDecodes_congr h
      · simp
      · simp [simMarkCell_getD]

lemma blockMarked_mark_head_tail {b : List (Option Bool)}
    (h : BlockMarked b) (hb : b ≠ []) :
    BlockMarked (simMarkCell b.headI :: b.tail) := by
  cases b with
  | nil => exact (hb rfl).elim
  | cons z zs =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · cases z <;> simp [simMarkCell]
      · exact h x (List.mem_cons_of_mem z hx)

lemma rawTapeMarkedRel_mk₁_encodeList {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) (r : List Γ) :
    RawTapeMarkedRel e (Tape.mk₁ (a :: r))
      (Tape.mk₁ ((a :: r).flatMap (rawEncodeBlock e))) := by
  have hflat : ∀ xs : List Γ, xs.flatMap (rawEncodeBlock e) =
      (xs.map (rawEncodeBlock e)).flatten := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  refine ⟨[], r, [], r.map (rawEncodeBlock e), a,
    rawEncodeBlock e a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Tape.mk₁, Tape.mk₂]
  · simp [Tape.mk₁, Tape.mk₂, rawBlocksLeft, rawBlocksRight,
      rawEncodeBlock, hflat r]
  · exact RawBlocksRel.nil
  · exact rawBlocksRel_encodeList e r
  · exact rawEncodeBlock_decodes e a
  · exact blocksMarked_nil
  · exact blockMarked_rawEncodeBlock e a
  · exact blocksMarked_map_rawEncodeBlock e r

lemma rawTapeCleanRel_mk₁_encodeList {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) (r : List Γ) :
    RawTapeCleanRel e (Tape.mk₁ (a :: r))
      (Tape.mk₁ ((a :: r).flatMap (rawEncodeBlock e))) := by
  exact rawTapeMarkedRel_to_rawTapeCleanRel
    (rawTapeMarkedRel_mk₁_encodeList e a r)

lemma rawBlocksLeft_cons (b : List (Option Bool))
    (bs : List (List (Option Bool))) :
    rawBlocksLeft (b :: bs) = b.reverse ++ rawBlocksLeft bs := by
  simp [rawBlocksLeft]

lemma rawBlocksRight_cons (b : List (Option Bool))
    (bs : List (List (Option Bool))) :
    rawBlocksRight (b :: bs) = b ++ rawBlocksRight bs := by
  simp [rawBlocksRight]

lemma tape_move_right_block {Γ : Type} [Inhabited Γ]
    (b : List Γ) (L R : ListBlank Γ) :
    (Tape.move Dir.right)^[b.length]
        (Tape.mk' L (ListBlank.append b R)) =
      Tape.mk' (ListBlank.append b.reverse L) R := by
  induction b generalizing L with
  | nil => simp
  | cons a b ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Tape.move_right_mk', ListBlank.append, ListBlank.head_cons,
        ListBlank.tail_cons]
      rw [ih]
      simp [List.reverse_cons, ListBlank.append_assoc, ListBlank.append]

lemma tape_move_left_block {Γ : Type} [Inhabited Γ]
    (b : List Γ) (L R : ListBlank Γ) :
    (Tape.move Dir.left)^[b.length]
        (Tape.mk' (ListBlank.append b.reverse L) R) =
      Tape.mk' L (ListBlank.append b R) := by
  induction b generalizing L with
  | nil => simp
  | cons a b ih =>
      rw [List.length_cons, Function.iterate_succ_apply']
      simp only [List.reverse_cons]
      rw [ListBlank.append_assoc]
      simp only [ListBlank.append]
      rw [ih]
      rw [Tape.move_left_mk']
      simp [ListBlank.head_cons, ListBlank.tail_cons]

lemma tape_take_succ_getI {Γ : Type} [Inhabited Γ]
    (b : List Γ) (k : ℕ) (hk : k < b.length) :
    b.take (k + 1) = b.take k ++ [b.getI k] := by
  rw [List.take_succ_eq_append_getElem hk, List.getI_eq_getElem _ hk]

lemma vector_cons_reverse {k : ℕ} (acc : List.Vector Bool k) (b : Bool) :
    (acc.cons b).toList.reverse = acc.toList.reverse ++ [b] := by
  simp [List.Vector.toList_cons]

lemma map_option_getI_getD (b : List (Option Bool)) (k : ℕ) :
    (b.map (Option.getD · false)).getI k = (b.getI k).getD false := by
  induction b generalizing k with
  | nil =>
      cases k <;> change false = false <;> rfl
  | cons a b ih =>
      cases k with
      | zero => simp [List.getI, List.getD]
      | succ k => simpa [List.getI, List.getD] using ih k


end NPComplete.CookLevin

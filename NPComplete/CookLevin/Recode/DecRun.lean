module

public import NPComplete.CookLevin.Recode.Dec

/-!
To show that the decoder realizes the output conversion, its individual state
transitions must compose into a complete run. This module proves the scan, return,
tape-erasure, and output phases together, identifies the resulting bit, and bounds
the run by the recoding time.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

variable (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)

@[reducible] noncomputable def decN : ℕ :=
  (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n

lemma dec_goHome_fin_pred (left : Fin (decN tm).succ) :
    left.val - 1 < (decN tm).succ :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) left.isLt

lemma decMachine_goHome_pos (b : Bool) (cell : Option Bool)
    (left : Fin (decN tm).succ) (h : 0 < left.val) :
    decMachine tm out (.goHome left b) cell =
      some (.goHome ⟨left.val - 1, dec_goHome_fin_pred tm left⟩ b,
        TM0.Stmt.move Dir.left) := by
  dsimp [decMachine]
  rw [dite_eq_left h]

lemma decMachine_goHome_zero (b : Bool) (cell : Option Bool)
    (left : Fin (decN tm).succ) (h : left.val = 0) :
    decMachine tm out (.goHome left b) cell =
      some (.writeOut b, TM0.Stmt.write (some b)) := by
  dsimp [decMachine]
  split_ifs with h'
  · exact (Nat.ne_of_gt h' h).elim
  · rfl

lemma dec_goHome_pos (b : Bool) (T : Tape (Option Bool))
    (left : Fin (decN tm).succ) (h : 0 < left.val) :
    TM0.step (decMachine tm out) ⟨.goHome left b, T⟩ =
      some ⟨.goHome ⟨left.val - 1, dec_goHome_fin_pred tm left⟩ b,
        T.move Dir.left⟩ := by
  simp [TM0.step, decMachine_goHome_pos tm out b T.head left h]

lemma dec_goHome_zero (b : Bool) (T : Tape (Option Bool))
    (left : Fin (decN tm).succ) (h : left.val = 0) :
    TM0.step (decMachine tm out) ⟨.goHome left b, T⟩ =
      some ⟨.writeOut b, T.write (some b)⟩ := by
  simp [TM0.step, decMachine_goHome_zero tm out b T.head left h]

lemma iterate_move_left_right (T : Tape (Option Bool)) :
    ∀ k, (Tape.move Dir.left)^[k] ((Tape.move Dir.right)^[k] T) = T
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [Tape.move_right_left]
    exact iterate_move_left_right T k

lemma dec_goHome_walk (b : Bool) (T : Tape (Option Bool)) :
    ∀ (k : ℕ) (hk : k < (decN tm).succ),
      StepsTo (TM0.step (decMachine tm out))
        ⟨.goHome ⟨k, hk⟩ b, T⟩
        ⟨.writeOut b, ((Tape.move Dir.left)^[k] T).write (some b)⟩ (k + 1)
  | 0, hk => by
    have hstep := dec_goHome_zero tm out b T ⟨0, hk⟩ rfl
    exact stepsTo_cons _ hstep (stepsTo_zero _ _)
  | k + 1, hk => by
    have hpos : 0 < ((⟨k + 1, hk⟩ : Fin (decN tm).succ).val) := Nat.succ_pos _
    have hstep := dec_goHome_pos tm out b T ⟨k + 1, hk⟩ hpos
    have ih := dec_goHome_walk b (T.move Dir.left) k (Nat.lt_of_succ_lt hk)
    refine stepsTo_cons _ hstep ?_
    simpa [Function.iterate_succ_apply] using ih

lemma decN_pos : 0 < decN tm := by
  set e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  by_contra h
  have hn : e.n = 0 := Nat.eq_zero_of_not_pos (by simpa [decN] using h)
  have inj : Function.Injective e.enc := fun a b hab =>
    (e.dec_enc a).symm.trans ((congrArg e.dec hab).trans (e.dec_enc b))
  let a : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) := (false, fun _ => none)
  let bval : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) := (true, fun _ => none)
  have hab : a ≠ bval := fun heq => Bool.false_ne_true (congrArg Prod.fst heq)
  have hlen_a : (e.enc a).toList.length = 0 := by simp [List.Vector.toList_length, hn]
  have hlen_b : (e.enc bval).toList.length = 0 := by
    simp [List.Vector.toList_length, hn]
  have : e.enc a = e.enc bval := by
    apply Subtype.ext
    change (e.enc a).toList = (e.enc bval).toList
    rw [List.eq_nil_of_length_eq_zero hlen_a,
      List.eq_nil_of_length_eq_zero hlen_b]
  exact hab (inj this)

lemma tape_mk₁_nth_nat_opt (l : List (Option Bool)) (i : ℕ) :
    (Tape.mk₁ l).nth i = l.getI i := by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]

lemma tape_mk₁_move_right_n_head (l : List Bool) (k : ℕ) :
    ((Tape.move Dir.right)^[k] (Tape.mk₁ (tapeSymbols l))).head =
      (tapeSymbols l).getI k := by
  rw [Tape.move_right_n_head, tape_mk₁_nth_nat_opt]

lemma map_some_getI (l : List Bool) (k : ℕ) :
    Option.getD ((l.map some).getI k) false = l.getD k false := by
  induction l generalizing k with
  | nil => cases k <;> simp [List.getI, List.getD, default]
  | cons b l ih =>
    cases k with
    | zero => simp [List.getI, List.getD]
    | succ k =>
      simpa [List.getI, List.getD] using ih k

lemma tape_read_bit (l : List Bool) (k : ℕ) :
    Option.getD
      ((Tape.move Dir.right)^[k] (Tape.mk₁ (tapeSymbols l))).head false =
      l.getD k false := by
  rw [tape_mk₁_move_right_n_head]
  simpa [tapeSymbols] using map_some_getI l k

lemma pad_take_length (l : List Bool) (n k : ℕ) (h : k ≤ n) :
    ((l ++ List.replicate n false).take k).length = k := by
  simp [List.length_take, List.length_append, List.length_replicate]
  omega

lemma pad_take_getElem (l : List Bool) (n k : ℕ) (hk : k < n) :
    (l ++ List.replicate n false)[k]'(by
      simp [List.length_append, List.length_replicate]; omega) =
      l.getD k false := by
  by_cases hlt : k < l.length
  · simp [List.getElem_append_left hlt, List.getD, hlt]
  · simp [List.getElem_append_right (Nat.not_lt.mp hlt),
      List.getElem_replicate, List.getD, hlt]

lemma pad_take_succ (l : List Bool) (n k : ℕ) (hk : k < n) :
    (l ++ List.replicate n false).take (k + 1) =
      (l ++ List.replicate n false).take k ++ [l.getD k false] := by
  have hlen : k < (l ++ List.replicate n false).length := by
    simp [List.length_append, List.length_replicate]
    omega
  rw [List.take_succ_eq_append_getElem hlen, pad_take_getElem l n k hk]

noncomputable def decResult (bits : List.Vector Bool (decN tm)) : Bool :=
  match ((BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).dec bits).2
      tm.k₁ with
  | some x => out x.1
  | none => false

lemma decodePackedOutputBool_eq_decResult (l : List Bool) :
    decodePackedOutputBool tm out l =
      decResult tm out
        ⟨(l ++ List.replicate (decN tm) false).take (decN tm),
          pad_take_length l (decN tm) (decN tm) le_rfl⟩ := by
  set e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  have hlen : ((l ++ List.replicate e.n false).take e.n).length = e.n :=
    pad_take_length l e.n e.n le_rfl
  simp [decodePackedOutputBool, decodePackedOutput, decResult, decN]
  generalize hcell :
    ((BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).dec
      ⟨(l ++ List.replicate e.n false).take e.n, hlen⟩).2 tm.k₁ = cell
  cases cell <;> simp [encodeBool]

lemma dec_read_fin_succ {i : Fin (decN tm).succ} (h : i.val + 1 < decN tm) :
    i.val + 1 < (decN tm).succ :=
  Nat.lt_succ_of_lt h

lemma decMachine_read_continue (i : Fin (decN tm).succ)
    (acc : List.Vector Bool i.val) (cell : Option Bool)
    (h : i.val + 1 < decN tm) :
    decMachine tm out (.read i acc) cell =
      some (.read ⟨i.val + 1, dec_read_fin_succ tm h⟩
        (acc.cons (Option.getD cell false)), TM0.Stmt.move Dir.right) := by
  have hne : i.val + 1 ≠ decN tm := Nat.ne_of_lt h
  dsimp [decMachine]
  rw [dite_eq_left (dec_read_fin_succ tm h), dite_eq_right hne]

lemma dec_read_continue (i : Fin (decN tm).succ)
    (acc : List.Vector Bool i.val) (T : Tape (Option Bool))
    (h : i.val + 1 < decN tm) :
    TM0.step (decMachine tm out) ⟨.read i acc, T⟩ =
      some ⟨.read ⟨i.val + 1, dec_read_fin_succ tm h⟩
        (acc.cons (Option.getD T.head false)), T.move Dir.right⟩ := by
  simp [TM0.step, decMachine_read_continue tm out i acc T.head h]

lemma dec_read_last_len (i : Fin (decN tm).succ) (acc : List.Vector Bool i.val)
    (b : Bool) (h : i.val + 1 = decN tm) :
    ((acc.cons b).toList.reverse).length = decN tm := by
  simp [List.Vector.toList_cons, List.length_reverse, List.Vector.toList_length, h]

lemma decMachine_read_last (i : Fin (decN tm).succ)
    (acc : List.Vector Bool i.val) (cell : Option Bool)
    (h : i.val + 1 = decN tm) :
    decMachine tm out (.read i acc) cell =
      some (.goHome ⟨decN tm, Nat.lt_succ_self _⟩
        (decResult tm out ⟨(acc.cons (Option.getD cell false)).toList.reverse,
          dec_read_last_len tm i acc _ h⟩),
        TM0.Stmt.move Dir.right) := by
  have hlt : i.val + 1 < (decN tm).succ := by omega
  dsimp [decMachine]
  rw [dite_eq_left hlt, dite_eq_left h]
  rfl

lemma dec_read_last (i : Fin (decN tm).succ)
    (acc : List.Vector Bool i.val) (T : Tape (Option Bool))
    (h : i.val + 1 = decN tm) :
    TM0.step (decMachine tm out) ⟨.read i acc, T⟩ =
      some ⟨.goHome ⟨decN tm, Nat.lt_succ_self _⟩
        (decResult tm out ⟨(acc.cons (Option.getD T.head false)).toList.reverse,
          dec_read_last_len tm i acc _ h⟩),
        T.move Dir.right⟩ := by
  simp [TM0.step, decMachine_read_last tm out i acc T.head h]

lemma acc_cons_reverse (k : ℕ) (acc : List.Vector Bool k) (b : Bool) :
    (acc.cons b).toList.reverse = acc.toList.reverse ++ [b] := by
  simp [List.Vector.toList_cons]

lemma iterate_move_right_succ (T : Tape (Option Bool)) (k : ℕ) :
    (Tape.move Dir.right)^[k + 1] T =
      ((Tape.move Dir.right)^[k] T).move Dir.right :=
  Function.iterate_succ_apply' _ _ _

lemma dec_read_continue_iterate (l : List Bool) (k : ℕ)
    (acc : List.Vector Bool k) (hk : k + 1 < decN tm) :
    TM0.step (decMachine tm out)
        ⟨.read ⟨k, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt hk)⟩ acc,
          (Tape.move Dir.right)^[k] (Tape.mk₁ (tapeSymbols l))⟩ =
      some ⟨.read ⟨k + 1, Nat.lt_succ_of_lt hk⟩
          (acc.cons (l.getD k false)),
          (Tape.move Dir.right)^[k + 1] (Tape.mk₁ (tapeSymbols l))⟩ := by
  have h :=
    dec_read_continue tm out ⟨k, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt hk)⟩ acc
      ((Tape.move Dir.right)^[k] (Tape.mk₁ (tapeSymbols l))) (by simpa using hk)
  rw [tape_read_bit, ← iterate_move_right_succ] at h
  exact h

lemma dec_read_last_iterate (l : List Bool) (acc : List.Vector Bool (decN tm - 1))
    (hn : 0 < decN tm) :
    TM0.step (decMachine tm out)
        ⟨.read ⟨decN tm - 1, Nat.lt_succ_of_lt (Nat.sub_one_lt_of_lt hn)⟩ acc,
          (Tape.move Dir.right)^[decN tm - 1] (Tape.mk₁ (tapeSymbols l))⟩ =
      some ⟨.goHome ⟨decN tm, Nat.lt_succ_self _⟩
          (decResult tm out
            ⟨(acc.cons (l.getD (decN tm - 1) false)).toList.reverse, by
              simp [List.Vector.toList_cons, List.length_reverse,
                List.Vector.toList_length, Nat.sub_add_cancel hn]⟩),
          (Tape.move Dir.right)^[decN tm] (Tape.mk₁ (tapeSymbols l))⟩ := by
  have hlast : (decN tm - 1) + 1 = decN tm := Nat.sub_add_cancel hn
  have h :=
    dec_read_last tm out ⟨decN tm - 1, Nat.lt_succ_of_lt (Nat.sub_one_lt_of_lt hn)⟩
      acc ((Tape.move Dir.right)^[decN tm - 1] (Tape.mk₁ (tapeSymbols l))) hlast
  rw [tape_read_bit] at h
  have hT :
      (Tape.move Dir.right)^[decN tm] (Tape.mk₁ (tapeSymbols l)) =
        ((Tape.move Dir.right)^[decN tm - 1]
          (Tape.mk₁ (tapeSymbols l))).move Dir.right := by
    conv_lhs => rw [← hlast]
    rw [iterate_move_right_succ]
  rw [hT]
  exact h

lemma dec_read_prefix (l : List Bool) :
    ∀ (k : ℕ) (hk : k < decN tm),
      ∃ (acc : List.Vector Bool k),
        acc.toList.reverse = (l ++ List.replicate (decN tm) false).take k ∧
        StepsTo (TM0.step (decMachine tm out))
          ⟨.read ⟨0, Nat.succ_pos _⟩ .nil, Tape.mk₁ (tapeSymbols l)⟩
          ⟨.read ⟨k, Nat.lt_succ_of_lt hk⟩ acc,
            (Tape.move Dir.right)^[k] (Tape.mk₁ (tapeSymbols l))⟩ k
  | 0, hk =>
    ⟨.nil, rfl, stepsTo_zero _ _⟩
  | k + 1, hk => by
    have hk' : k < decN tm := Nat.lt_of_succ_lt hk
    obtain ⟨acc, hacc, hsteps⟩ := dec_read_prefix l k hk'
    have hstep := dec_read_continue_iterate tm out l k acc hk
    refine ⟨acc.cons (l.getD k false), ?_, ?_⟩
    · rw [acc_cons_reverse, hacc, pad_take_succ _ _ _ hk']
    · have hone := stepsTo_cons _ hstep (stepsTo_zero _ _)
      have htotal := stepsTo_trans (t₁ := k) (t₂ := 1) _ hsteps hone
      simpa [Nat.add_comm] using htotal

lemma dec_read_to_goHome (l : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.read ⟨0, Nat.succ_pos _⟩ .nil, Tape.mk₁ (tapeSymbols l)⟩
      ⟨.goHome ⟨decN tm, Nat.lt_succ_self _⟩ (decodePackedOutputBool tm out l),
        (Tape.move Dir.right)^[decN tm] (Tape.mk₁ (tapeSymbols l))⟩
      (decN tm) := by
  have hn := decN_pos tm
  have hpred : decN tm - 1 < decN tm := Nat.sub_one_lt_of_lt hn
  obtain ⟨acc, hacc, hsteps⟩ := dec_read_prefix tm out l (decN tm - 1) hpred
  have hlast : (decN tm - 1) + 1 = decN tm := Nat.sub_add_cancel hn
  have hstep := dec_read_last_iterate tm out l acc hn
  have hbits :
      (acc.cons (l.getD (decN tm - 1) false)).toList.reverse =
        (l ++ List.replicate (decN tm) false).take (decN tm) := by
    rw [acc_cons_reverse, hacc, ← pad_take_succ _ _ _ hpred, hlast]
  have hres := decodePackedOutputBool_eq_decResult tm out l
  have hone :
      StepsTo (TM0.step (decMachine tm out))
        ⟨.read ⟨decN tm - 1, Nat.lt_succ_of_lt hpred⟩ acc,
          (Tape.move Dir.right)^[decN tm - 1] (Tape.mk₁ (tapeSymbols l))⟩
        ⟨.goHome ⟨decN tm, Nat.lt_succ_self _⟩ (decodePackedOutputBool tm out l),
          (Tape.move Dir.right)^[decN tm] (Tape.mk₁ (tapeSymbols l))⟩ 1 := by
    refine stepsTo_cons _ ?_ (stepsTo_zero _ _)
    rw [hstep]
    congr 1
    congr 1
    rw [hres]
    congr
  have htotal :=
    stepsTo_trans (t₁ := decN tm - 1) (t₂ := 1) _ hsteps hone
  have ht : 1 + (decN tm - 1) = decN tm := by omega
  simpa [ht] using htotal

lemma dec_to_writeOut (l : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.read ⟨0, Nat.succ_pos _⟩ .nil, Tape.mk₁ (tapeSymbols l)⟩
      ⟨.writeOut (decodePackedOutputBool tm out l),
        (Tape.mk₁ (tapeSymbols l)).write
          (some (decodePackedOutputBool tm out l))⟩
      (2 * decN tm + 1) := by
  have hread := dec_read_to_goHome tm out l
  have hhome :=
    dec_goHome_walk tm out (decodePackedOutputBool tm out l)
      ((Tape.move Dir.right)^[decN tm] (Tape.mk₁ (tapeSymbols l)))
      (decN tm) (Nat.lt_succ_self _)
  have hT := iterate_move_left_right (Tape.mk₁ (tapeSymbols l)) (decN tm)
  have htotal :=
    stepsTo_trans (t₁ := decN tm) (t₂ := decN tm + 1) _ hread hhome
  rw [hT] at htotal
  simpa [Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htotal

lemma tape_mk₁_write_bit_list (b : Bool) (l : List Bool) :
    (Tape.mk₁ (tapeSymbols l)).write (some b) =
      Tape.mk₁ (tapeSymbols (b :: l.tail)) := by
  cases l with
  | nil =>
    simpa [tapeSymbols, List.tail] using tape_mk₁_write_bit b
  | cons x xs =>
    simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
      ListBlank.head_mk, ListBlank.tail_mk]

lemma tape_mk₁_cons_move_right (b : Bool) (rest : List Bool) :
    (Tape.mk₁ (tapeSymbols (b :: rest))).move Dir.right =
      Tape.mk' (ListBlank.mk [some b]) (ListBlank.mk (tapeSymbols rest)) := by
  simp only [tapeSymbols, Tape.mk₁, Tape.mk₂]
  rw [Tape.move_right_mk']
  simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

lemma tape_mk'_write_none (L : List (Option Bool)) (a : Option Bool)
    (R : List (Option Bool)) :
    (Tape.mk' (ListBlank.mk L) (ListBlank.mk (a :: R))).write none =
      Tape.mk' (ListBlank.mk L) (ListBlank.mk (none :: R)) := by
  simp [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]

lemma tape_mk'_move_right_cons (L : List (Option Bool)) (a : Option Bool)
    (R : List (Option Bool)) :
    (Tape.mk' (ListBlank.mk L) (ListBlank.mk (a :: R))).move Dir.right =
      Tape.mk' (ListBlank.mk (a :: L)) (ListBlank.mk R) := by
  rw [Tape.move_right_mk']
  simp [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

lemma listBlank_none_nil :
    ListBlank.mk ([none] : List (Option Bool)) = ListBlank.mk [] := by
  apply Quotient.sound
  refine Or.inr ⟨1, ?_⟩
  simp [default]

lemma tape_mk'_empty_head (L : List (Option Bool)) :
    (Tape.mk' (ListBlank.mk L) (ListBlank.mk [])).head = none := by
  simp [Tape.mk', ListBlank.head_mk, default]

lemma dec_erase_one (b r : Bool) (rs : List Bool) (k : ℕ) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.eraseRest,
        Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
          (ListBlank.mk (tapeSymbols (r :: rs)))⟩
      ⟨.eraseRest,
        Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++ [some b]))
          (ListBlank.mk (tapeSymbols rs))⟩ 2 := by
  set L := List.replicate k none ++ [some b]
  have hhead :
      (Tape.mk' (ListBlank.mk L) (ListBlank.mk (tapeSymbols (r :: rs)))).head =
        some r := by
    simp [tapeSymbols]
  have s1 :=
    dec_eraseRest_some tm out
      (Tape.mk' (ListBlank.mk L) (ListBlank.mk (tapeSymbols (r :: rs)))) hhead
  have s2 :
      TM0.step (decMachine tm out)
          ⟨.eraseRestGo,
            (Tape.mk' (ListBlank.mk L)
              (ListBlank.mk (tapeSymbols (r :: rs)))).write none⟩ =
        some ⟨.eraseRest,
          Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++ [some b]))
            (ListBlank.mk (tapeSymbols rs))⟩ := by
    simp only [tapeSymbols, List.map_cons]
    rw [dec_eraseRestGo_step, tape_mk'_write_none, tape_mk'_move_right_cons]
    simp [L, List.replicate_succ, List.cons_append]
  exact stepsTo_cons _ s1 (stepsTo_cons _ s2 (stepsTo_zero _ _))

lemma dec_eraseRest_list (b : Bool) :
    ∀ (rest : List Bool) (k : ℕ),
      StepsTo (TM0.step (decMachine tm out))
        ⟨.eraseRest,
          Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
            (ListBlank.mk (tapeSymbols rest))⟩
        ⟨.eraseRest,
          Tape.mk' (ListBlank.mk (List.replicate (k + rest.length) none ++ [some b]))
            (ListBlank.mk (tapeSymbols ([] : List Bool)))⟩
        (2 * rest.length)
  | [], k => by
    simp [tapeSymbols]
    exact stepsTo_zero _ _
  | r :: rs, k => by
    have hone := dec_erase_one tm out b r rs k
    have ih := dec_eraseRest_list b rs (k + 1)
    have htotal := stepsTo_trans (t₁ := 2) (t₂ := 2 * rs.length) _ hone ih
    have hlen :
        List.replicate (k + 1 + rs.length) none ++ [some b] =
          List.replicate (k + (r :: rs).length) none ++ [some b] := by
      simp [List.length_cons, Nat.add_comm, Nat.add_left_comm]
    have htm : 2 * rs.length + 2 = 2 * (r :: rs).length := by
      simp [List.length_cons, Nat.mul_succ, Nat.add_comm]
    rw [hlen] at htotal
    rwa [htm] at htotal

lemma tape_mk'_k0_move_left (b : Bool) :
    (Tape.mk' (ListBlank.mk [some b]) (ListBlank.mk [])).move Dir.left =
      Tape.mk₁ (tapeSymbols [b]) := by
  simp [Tape.move, Tape.mk', Tape.mk₁, Tape.mk₂, tapeSymbols,
    ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, default,
    listBlank_none_nil]

lemma tape_mk'_succ_move_left (b : Bool) (k : ℕ) :
    (Tape.mk' (ListBlank.mk (List.replicate (k + 1) none ++ [some b]))
        (ListBlank.mk [])).move Dir.left =
      Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
        (ListBlank.mk [none]) := by
  simp [Tape.move, Tape.mk', ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk, List.replicate_succ, default, listBlank_none_nil]

lemma dec_backToBit_hit (b : Bool) :
    TM0.step (decMachine tm out)
        ⟨.backToBit, Tape.mk₁ (tapeSymbols [b])⟩ =
      some ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ := by
  have h := dec_backToBit_some tm out (Tape.mk₁ (tapeSymbols [b]))
    (by simp [mk₁_bit_head])
  rw [h, mk₁_bit_head, mk₁_bit_write_self]

lemma tape_mk'_none_right (L : List (Option Bool)) :
    Tape.mk' (ListBlank.mk L) (ListBlank.mk [none]) =
      Tape.mk' (ListBlank.mk L) (ListBlank.mk []) := by
  simp [Tape.mk', ListBlank.head_mk, ListBlank.tail_mk, default]

lemma dec_backToBit_after_left (b : Bool) :
    ∀ (k : ℕ),
      StepsTo (TM0.step (decMachine tm out))
        ⟨.backToBit,
          (Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
            (ListBlank.mk [])).move Dir.left⟩
        ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (k + 1)
  | 0 => by
    change StepsTo (TM0.step (decMachine tm out))
      ⟨.backToBit,
        (Tape.mk' (ListBlank.mk [some b]) (ListBlank.mk [])).move Dir.left⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ 1
    rw [tape_mk'_k0_move_left]
    exact stepsTo_cons _ (dec_backToBit_hit tm out b) (stepsTo_zero _ _)
  | k + 1 => by
    rw [tape_mk'_succ_move_left]
    have hstep :=
      dec_backToBit_none tm out
        (Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
          (ListBlank.mk [none]))
        (by simp [Tape.mk', ListBlank.head_mk])
    refine stepsTo_cons _ hstep ?_
    rw [tape_mk'_none_right]
    exact dec_backToBit_after_left b k

lemma dec_from_eraseRest_blank (b : Bool) (k : ℕ) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.eraseRest,
        Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
          (ListBlank.mk (tapeSymbols ([] : List Bool)))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (k + 2) := by
  have hnone :=
    dec_eraseRest_none tm out
      (Tape.mk' (ListBlank.mk (List.replicate k none ++ [some b]))
        (ListBlank.mk []))
      (tape_mk'_empty_head _)
  refine stepsTo_cons _ hnone (dec_backToBit_after_left tm out b k)

lemma dec_from_eraseRest (b : Bool) (rest : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.eraseRest,
        Tape.mk' (ListBlank.mk [some b]) (ListBlank.mk (tapeSymbols rest))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (3 * rest.length + 2) := by
  have herase := dec_eraseRest_list tm out b rest 0
  have hblank := dec_from_eraseRest_blank tm out b rest.length
  have herase' :
      StepsTo (TM0.step (decMachine tm out))
        ⟨.eraseRest,
          Tape.mk' (ListBlank.mk [some b]) (ListBlank.mk (tapeSymbols rest))⟩
        ⟨.eraseRest,
          Tape.mk' (ListBlank.mk (List.replicate rest.length none ++ [some b]))
            (ListBlank.mk (tapeSymbols ([] : List Bool)))⟩
        (2 * rest.length) := by
    simpa [List.replicate] using herase
  have htotal :=
    stepsTo_trans (t₁ := 2 * rest.length) (t₂ := rest.length + 2) _ herase' hblank
  have ht : rest.length + 2 + 2 * rest.length = 3 * rest.length + 2 := by omega
  simpa [ht] using htotal

lemma dec_from_skipBit (b : Bool) (rest : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.skipBit, Tape.mk₁ (tapeSymbols (b :: rest))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (3 * rest.length + 3) := by
  have hskip := dec_skipBit_step tm out (Tape.mk₁ (tapeSymbols (b :: rest)))
  have herase := dec_from_eraseRest tm out b rest
  refine stepsTo_cons _ ?_ herase
  rw [hskip, tape_mk₁_cons_move_right]

lemma dec_from_writeOut (b : Bool) (rest : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.writeOut b, Tape.mk₁ (tapeSymbols (b :: rest))⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (3 * rest.length + 4) := by
  have hwrite :
      TM0.step (decMachine tm out)
          ⟨.writeOut b, Tape.mk₁ (tapeSymbols (b :: rest))⟩ =
        some ⟨.skipBit, Tape.mk₁ (tapeSymbols (b :: rest))⟩ := by
    rw [dec_writeOut_step]
    simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
      ListBlank.head_mk]
  exact stepsTo_cons _ hwrite (dec_from_skipBit tm out b rest)

lemma dec_from_writeOut_list (b : Bool) (l : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.writeOut b, (Tape.mk₁ (tapeSymbols l)).write (some b)⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [b])⟩ (3 * l.tail.length + 4) := by
  rw [tape_mk₁_write_bit_list]
  exact dec_from_writeOut tm out b l.tail

lemma dec_run (l : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      ⟨.read ⟨0, Nat.succ_pos _⟩ .nil, Tape.mk₁ (tapeSymbols l)⟩
      ⟨.done, Tape.mk₁ (tapeSymbols [decodePackedOutputBool tm out l])⟩
      (3 * l.tail.length + 4 + (2 * decN tm + 1)) := by
  exact stepsTo_trans (t₁ := 2 * decN tm + 1) (t₂ := 3 * l.tail.length + 4) _
    (dec_to_writeOut tm out l)
    (dec_from_writeOut_list tm out (decodePackedOutputBool tm out l) l)

lemma dec_run_init (l : List Bool) :
    StepsTo (TM0.step (decMachine tm out))
      (TM0.init (tapeSymbols l))
      ⟨.done, Tape.mk₁ (tapeSymbols [decodePackedOutputBool tm out l])⟩
      (3 * l.tail.length + 4 + (2 * decN tm + 1)) := by
  simpa [TM0.init, default] using dec_run tm out l

lemma dec_time_bound_erase (n L : ℕ) (hn : 0 < n) :
    2 * n + 3 * L + 8 ≤ (recodeTime 1 n + 16 + 2 * X).eval L := by
  have hpoly :
      (recodeTime 1 n + 16 + 2 * X).eval L =
        n * (2 * (L + n) + 4) * n + L * n + n + 16 + 2 * L := by
    simp [recodeTime, recodeTimeG_eval, eval_add, eval_X]
  rw [hpoly]
  have hsq : 2 * L + 2 * n + 4 ≤ n * (2 * (L + n) + 4) * n := by
    have hnn : 1 ≤ n * n := Nat.mul_le_mul hn hn
    have := Nat.mul_le_mul_right (2 * (L + n) + 4) hnn
    simp [Nat.mul_comm, Nat.mul_assoc] at this ⊢
    omega
  have hLn : L ≤ L * n := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left L hn
  omega

lemma dec_outputs (l : List Bool) :
    MachineOutputsInTime (decMachine tm out)
      (tapeSymbols l)
      (tapeSymbols (encodeBool (decodePackedOutputBool tm out l)))
      ((recodeTime 1 (decN tm) + 16 + 2 * X).eval l.length) := by
  refine ⟨.done, 3 * l.tail.length + 4 + (2 * decN tm + 1), ?_, ?_, ?_⟩
  · have hn := decN_pos tm
    have hle : 3 * l.tail.length + 4 + (2 * decN tm + 1) ≤
        2 * decN tm + 3 * l.length + 8 := by
      have : l.tail.length ≤ l.length := by cases l <;> simp
      omega
    exact hle.trans (dec_time_bound_erase (decN tm) l.length hn)
  · simpa [encodeBool] using dec_run_init tm out l
  · exact dec_done_halt tm out _

noncomputable def decComputable :
    TM0ComputableInPolyTime (fun l : List Bool => l) encodeBool
      (decodePackedOutputBool tm out) where
  toTM0ComputableAux := decAux tm out
  time := recodeTime 1 (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n
    + 16 + 2 * X
  outputsFun l := dec_outputs tm out l

end NPComplete.CookLevin

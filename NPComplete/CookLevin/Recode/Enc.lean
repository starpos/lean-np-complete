module

public import NPComplete.CookLevin.Recode
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
A finite-state expander: each input bit becomes one `Γ'` block. The last
input bit is the bottom cell. Lists never enter the state, so support
stays finite.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial

/-- Control states for the input expander. `i` indexes the current block bit. -/
inductive EncPhase (n : ℕ)
  | toEnd
  | checkLast (hasOutput : Bool) (b : Bool)
  | lookAhead (hasOutput : Bool) (b : Bool)
  | seekOutLeft (hasOutput : Bool) (isBottom : Bool) (b : Bool)
  | seekOutBlock (isBottom : Bool) (b : Bool)
  | writeLeft (isBottom : Bool) (b : Bool) (i : Fin n)
  | writeLeftMove (isBottom : Bool) (b : Bool) (i : Fin n)
  | returnRight
  | returnGap
  | writeBlank (i : Fin n)
  | writeBlankMove (i : Fin n)
  | shiftHome
  | done
  deriving DecidableEq

instance {n : ℕ} : Inhabited (EncPhase n) :=
  ⟨EncPhase.toEnd⟩

/-- The `n`-bit block for one packed input bit. `isBottom` marks `trInit`'s
    first cell. -/
noncomputable def encBlock (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (isBottom b : Bool) : List Bool :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let packed : TM2to1.PackΓ tm tm.k₀ :=
    ⟨inp.symm b, TM2to1.mem_usedSymbols_k₀ tm _⟩
  let cell : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) :=
    (isBottom, Function.update (fun _ => none) tm.k₀ (some packed))
  (eΓ.enc cell).toList

/-- Empty input is a single bottom blank cell (`trInit []`). -/
noncomputable def encBottomBlank (tm : FinTM2) : List Bool :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let cell : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) := (true, fun _ => none)
  (eΓ.enc cell).toList

/-- Finite-state expander on `Option Bool`. -/
noncomputable def encMachine (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) :
    TM0.Machine (Option Bool) (EncPhase
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n) :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  fun phase cell =>
    match phase with
    | EncPhase.toEnd =>
        match cell with
        | some b => some (EncPhase.checkLast false b, TM0.Stmt.write none)
        | none =>
            if h : 0 < eΓ.n then
              some (EncPhase.writeBlank ⟨0, h⟩,
                TM0.Stmt.write (some ((encBottomBlank tm).getD 0 false)))
            else
              some (EncPhase.done, TM0.Stmt.write none)
    | EncPhase.checkLast hasOutput b =>
        some (EncPhase.lookAhead hasOutput b, TM0.Stmt.move Dir.right)
    | EncPhase.lookAhead hasOutput b =>
        match cell with
        | some _ => some (EncPhase.seekOutLeft hasOutput false b, TM0.Stmt.move Dir.left)
        | none => some (EncPhase.seekOutLeft hasOutput true b, TM0.Stmt.move Dir.left)
    | EncPhase.seekOutLeft hasOutput isBottom b =>
        if hasOutput then
          match cell with
          | some _ => some (EncPhase.seekOutBlock isBottom b, TM0.Stmt.move Dir.left)
          | none => some (EncPhase.seekOutLeft true isBottom b, TM0.Stmt.move Dir.left)
        else
          if h : 0 < eΓ.n then
            some (EncPhase.writeLeft isBottom b ⟨eΓ.n - 1, Nat.sub_lt h (by omega)⟩,
              TM0.Stmt.move Dir.left)
          else
            some (EncPhase.done, TM0.Stmt.move Dir.right)
    | EncPhase.seekOutBlock isBottom b =>
        match cell with
        | some _ => some (EncPhase.seekOutBlock isBottom b, TM0.Stmt.move Dir.left)
        | none =>
            if h : 0 < eΓ.n then
              let i : Fin eΓ.n := ⟨eΓ.n - 1, Nat.sub_lt h (by omega)⟩
              if hi : i.val = 0 then
                if isBottom then
                  some (EncPhase.done,
                    TM0.Stmt.write (some ((encBlock tm inp isBottom b).getD i.val false)))
                else
                  some (EncPhase.writeLeftMove isBottom b i,
                    TM0.Stmt.write (some ((encBlock tm inp isBottom b).getD i.val false)))
              else
                some (EncPhase.writeLeftMove isBottom b i,
                  TM0.Stmt.write (some ((encBlock tm inp isBottom b).getD i.val false)))
            else
              some (EncPhase.done, TM0.Stmt.move Dir.right)
    | EncPhase.writeLeft isBottom b i =>
        let bit := some ((encBlock tm inp isBottom b).getD i.val false)
        if h : i.val = 0 then
          if isBottom then
            some (EncPhase.done, TM0.Stmt.write bit)
          else
            some (EncPhase.writeLeftMove isBottom b i, TM0.Stmt.write bit)
        else
          some (EncPhase.writeLeftMove isBottom b i, TM0.Stmt.write bit)
    | EncPhase.writeLeftMove isBottom b i =>
        if h : i.val = 0 then
          some (EncPhase.returnRight, TM0.Stmt.move Dir.right)
        else
          some (EncPhase.writeLeft isBottom b ⟨i.val - 1, by omega⟩,
            TM0.Stmt.move Dir.left)
    | EncPhase.returnRight =>
        match cell with
        | some _ => some (EncPhase.returnRight, TM0.Stmt.move Dir.right)
        | none => some (EncPhase.returnGap, TM0.Stmt.move Dir.right)
    | EncPhase.returnGap =>
        match cell with
        | none => some (EncPhase.returnGap, TM0.Stmt.move Dir.right)
        | some b => some (EncPhase.checkLast true b, TM0.Stmt.write none)
    | EncPhase.writeBlank i =>
        if h : i.val + 1 < eΓ.n then
          some (EncPhase.writeBlankMove i, TM0.Stmt.move Dir.right)
        else
          some (EncPhase.shiftHome, TM0.Stmt.move Dir.left)
    | EncPhase.writeBlankMove i =>
        if h : i.val + 1 < eΓ.n then
          some (EncPhase.writeBlank ⟨i.val + 1, h⟩,
            TM0.Stmt.write (some ((encBottomBlank tm).getD (i.val + 1) false)))
        else
          some (EncPhase.shiftHome, TM0.Stmt.move Dir.left)
    | EncPhase.shiftHome =>
        match cell with
        | some _ => some (EncPhase.shiftHome, TM0.Stmt.move Dir.left)
        | none => some (EncPhase.done, TM0.Stmt.move Dir.right)
    | EncPhase.done => none

def encElems (n : ℕ) : List (EncPhase n) :=
    [EncPhase.toEnd, EncPhase.returnRight, EncPhase.returnGap, EncPhase.shiftHome,
    EncPhase.done] ++
    ([false, true].flatMap fun hasOutput =>
      [false, true].map (EncPhase.checkLast hasOutput)) ++
    ([false, true].flatMap fun hasOutput =>
      [false, true].map (EncPhase.lookAhead hasOutput)) ++
    ([false, true].flatMap fun hasOutput =>
      [false, true].flatMap fun isB =>
        [false, true].map (EncPhase.seekOutLeft hasOutput isB)) ++
    ([false, true].flatMap fun isB =>
      [false, true].map (EncPhase.seekOutBlock isB)) ++
    ([false, true].flatMap fun isB =>
      [false, true].flatMap fun b =>
        (List.finRange n).map fun i => EncPhase.writeLeft isB b i) ++
    ([false, true].flatMap fun isB =>
      [false, true].flatMap fun b =>
        (List.finRange n).map fun i => EncPhase.writeLeftMove isB b i) ++
    (List.finRange n).map EncPhase.writeBlank ++
    (List.finRange n).map EncPhase.writeBlankMove

def encSupport (n : ℕ) : Finset (EncPhase n) :=
  encElems n |>.toFinset

lemma mem_encSupport_toEnd (n : ℕ) : EncPhase.toEnd ∈ encSupport n := by
  simp [encSupport, encElems]

lemma mem_encSupport_done (n : ℕ) : EncPhase.done ∈ encSupport n := by
  simp [encSupport, encElems]

lemma mem_encSupport_checkLast (n : ℕ) (hasOutput b : Bool) :
    EncPhase.checkLast hasOutput b ∈ encSupport n := by
  cases hasOutput <;> cases b <;> simp [encSupport, encElems]

lemma mem_encSupport_lookAhead (n : ℕ) (hasOutput b : Bool) :
    EncPhase.lookAhead hasOutput b ∈ encSupport n := by
  cases hasOutput <;> cases b <;> simp [encSupport, encElems]

lemma mem_encSupport_seekOutLeft (n : ℕ) (hasOutput isB b : Bool) :
    EncPhase.seekOutLeft hasOutput isB b ∈ encSupport n := by
  cases hasOutput <;> cases isB <;> cases b <;> simp [encSupport, encElems]

lemma mem_encSupport_seekOutBlock (n : ℕ) (isB b : Bool) :
    EncPhase.seekOutBlock isB b ∈ encSupport n := by
  cases isB <;> cases b <;> simp [encSupport, encElems]

lemma mem_encSupport_writeLeft (n : ℕ) (isB b : Bool) (i : Fin n) :
    EncPhase.writeLeft isB b i ∈ encSupport n := by
  cases isB <;> cases b <;> simp [encSupport, encElems, List.mem_finRange]

lemma mem_encSupport_writeLeftMove (n : ℕ) (isB b : Bool) (i : Fin n) :
    EncPhase.writeLeftMove isB b i ∈ encSupport n := by
  cases isB <;> cases b <;> simp [encSupport, encElems, List.mem_finRange]

lemma mem_encSupport_returnRight (n : ℕ) : EncPhase.returnRight ∈ encSupport n := by
  simp [encSupport, encElems]

lemma mem_encSupport_returnGap (n : ℕ) : EncPhase.returnGap ∈ encSupport n := by
  simp [encSupport, encElems]

lemma mem_encSupport_shiftHome (n : ℕ) : EncPhase.shiftHome ∈ encSupport n := by
  simp [encSupport, encElems]

lemma mem_encSupport_writeBlank (n : ℕ) (i : Fin n) :
    EncPhase.writeBlank i ∈ encSupport n := by
  simp [encSupport, encElems, List.mem_finRange]

lemma mem_encSupport_writeBlankMove (n : ℕ) (i : Fin n) :
    EncPhase.writeBlankMove i ∈ encSupport n := by
  simp [encSupport, encElems, List.mem_finRange]

lemma encMachine_supports (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) :
    TM0.Supports (encMachine tm inp)
      ↑(encSupport (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n) := by
  refine ⟨?_, ?_⟩
  · simpa [default] using
      mem_encSupport_toEnd (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n
  · intro q a q' s hstep hq
    revert q' s hstep
    cases q <;> intro q' s hstep <;>
      simp [encMachine] at hstep <;>
      (try cases a) <;> (try split_ifs at hstep) <;>
      (try rcases hstep with ⟨rfl, rfl⟩) <;>
      first
      | exact mem_encSupport_done _
       | exact mem_encSupport_checkLast _ _ _
       | exact mem_encSupport_lookAhead _ _ _
       | exact mem_encSupport_seekOutLeft _ _ _ _
       | exact mem_encSupport_seekOutBlock _ _ _
       | exact mem_encSupport_writeLeft _ _ _ _
       | exact mem_encSupport_writeLeftMove _ _ _ _
       | exact mem_encSupport_returnRight _
       | exact mem_encSupport_returnGap _
       | exact mem_encSupport_shiftHome _
      | exact mem_encSupport_writeBlank _ _
      | exact mem_encSupport_writeBlankMove _ _

@[reducible] noncomputable def encN (tm : FinTM2) : ℕ :=
  (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n

lemma encN_pos (tm : FinTM2) : 0 < encN tm := by
  set e := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  by_contra h
  have hn : e.n = 0 := Nat.eq_zero_of_not_pos (by simpa [encN] using h)
  have inj : Function.Injective e.enc := fun a b hab =>
    (e.dec_enc a).symm.trans ((congrArg e.dec hab).trans (e.dec_enc b))
  let a : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) := (false, fun _ => none)
  let bval : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) := (true, fun _ => none)
  have hab : a ≠ bval := fun heq => Bool.false_ne_true (congrArg Prod.fst heq)
  have hlen_a : (e.enc a).toList.length = 0 := by
    simp [List.Vector.toList_length, hn]
  have hlen_b : (e.enc bval).toList.length = 0 := by
    simp [List.Vector.toList_length, hn]
  have : e.enc a = e.enc bval := by
    apply Subtype.ext
    change (e.enc a).toList = (e.enc bval).toList
    rw [List.eq_nil_of_length_eq_zero hlen_a, List.eq_nil_of_length_eq_zero hlen_b]
  exact hab (inj this)

lemma encBlock_length (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (isBottom b : Bool) :
    (encBlock tm inp isBottom b).length = encN tm := by
  simp [encBlock, encN, List.Vector.toList_length]

lemma encBottomBlank_length (tm : FinTM2) :
    (encBottomBlank tm).length = encN tm := by
  simp [encBottomBlank, encN, List.Vector.toList_length]

lemma trInit_nil {K : Type*} [DecidableEq K] (k : K) (Γ : K → Type*) :
    TM2to1.trInit k ([] : List (Γ k)) = [(true, fun _ => none)] := by
  unfold TM2to1.trInit
  simp [List.reverse_nil, List.headI, default]
  rfl

section

lemma trInit_snoc {K : Type*} [DecidableEq K] (k : K) {Γ : K → Type*}
    (xs : List (Γ k)) (last : Γ k) :
    TM2to1.trInit k (xs ++ [last]) =
      (true, Function.update (fun _ => none) k (some last)) ::
        xs.reverse.map fun a =>
          (false, Function.update (fun _ => none) k (some a)) := by
  unfold TM2to1.trInit
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  rfl

lemma trInit_snoc_length {K : Type*} [DecidableEq K] (k : K) {Γ : K → Type*}
    (xs : List (Γ k)) (last : Γ k) :
    (TM2to1.trInit k (xs ++ [last])).length = xs.length + 1 :=
  (congrArg List.length (trInit_snoc k xs last)).trans
    (congrArg (· + 1) ((List.length_map ..).trans (List.length_reverse ..)))

lemma length_le_trInit_length {K : Type*} [DecidableEq K] (k : K) {Γ : K → Type*}
    (ys : List (Γ k)) : ys.length ≤ (TM2to1.trInit k ys).length := by
  rcases List.eq_nil_or_concat ys with rfl | ⟨xs, last, rfl⟩
  · exact Nat.zero_le _
  · rw [List.concat_eq_append, trInit_snoc_length, List.length_append]
    exact Nat.le_refl _

lemma trInit_length_pos {K : Type*} [DecidableEq K] (k : K) {Γ : K → Type*}
    (ys : List (Γ k)) : 0 < (TM2to1.trInit k ys).length := by
  rcases List.eq_nil_or_concat ys with rfl | ⟨xs, last, rfl⟩
  · rw [trInit_nil]
    exact Nat.one_pos
  · rw [List.concat_eq_append, trInit_snoc_length]
    exact Nat.succ_pos _

lemma packList_map_symm (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) :
    ∀ (l : List Bool),
      TM2to1.packList tm tm.k₀ (l.map inp.symm)
          (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x) =
        l.map fun b => ⟨inp.symm b, TM2to1.mem_usedSymbols_k₀ tm _⟩
  | [] => rfl
  | b :: l => by
    exact congrArg _ (packList_map_symm tm inp l)

lemma map_reverse_map_comp {α β γ : Type*} (f : α → β) (g : β → γ) (xs : List α) :
    (xs.map f).reverse.map g = xs.reverse.map fun a => g (f a) := by
  rw [← List.map_reverse, List.map_map]
  rfl

lemma trInit_packList_snoc (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (xs : List Bool) (b : Bool) :
    @Eq (List (TM2to1.Γ' tm.K (TM2to1.PackΓ tm)))
    (TM2to1.trInit tm.k₀ (TM2to1.packList tm tm.k₀ ((xs ++ [b]).map inp.symm)
        (fun x _ => TM2to1.mem_usedSymbols_k₀ tm x)))
      ((true, Function.update (fun _ => none) tm.k₀
          (some (⟨inp.symm b, TM2to1.mem_usedSymbols_k₀ tm _⟩ : TM2to1.PackΓ tm tm.k₀))) ::
        xs.reverse.map fun a => (false, Function.update (fun _ => none) tm.k₀
          (some (⟨inp.symm a, TM2to1.mem_usedSymbols_k₀ tm _⟩ : TM2to1.PackΓ tm tm.k₀)))) := by
  rw [packList_map_symm]
  refine (congrArg (TM2to1.trInit tm.k₀) (List.map_append ..)).trans
    ((trInit_snoc ..).trans ?_)
  refine congrArg₂ List.cons rfl ?_
  exact map_reverse_map_comp _ _ _

end

lemma encodePackedInput_nil (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) :
    encodePackedInput tm inp [] = encBottomBlank tm := by
  simp [encodePackedInput, encBottomBlank, List.reverse_nil]

lemma encodePackedInput_snoc (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool)
    (xs : List Bool) (last : Bool) :
    encodePackedInput tm inp (xs ++ [last]) =
      encBlock tm inp true last ++
        xs.reverse.flatMap (encBlock tm inp false) := by
  simp [encodePackedInput, encBlock, List.reverse_append, List.reverse_cons,
    List.reverse_nil]
  rfl

noncomputable def encAux (tm : FinTM2) (inp : tm.Γ tm.k₀ ≃ Bool) :
    TM0ComputableAux Bool where
  Λ := EncPhase (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n
  M := encMachine tm inp
  S := encSupport _
  supports := encMachine_supports tm inp

end NPComplete.CookLevin

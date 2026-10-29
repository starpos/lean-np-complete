module

public import NPComplete.CookLevin.Generate.ExecMapSAT

/-!
# Executable clause shapes

Compact variable numbering changes the identifiers used by executable tableau
clauses, so SAT-preserving remapping needs a precise account of which identifiers
can occur. This module proves that shape condition and its closure under clause
construction.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT
open Polynomial
open scoped Polynomial
open Computability (encodeBool)
open NPComplete.BitEncoding (encodeNat encodeList encodeNat_length)

variable {Γ Λ : Type*}

def ExecClauseShape (c : Clause) : Prop :=
  ∀ l ∈ c.lits, ExecEncodableVar l.var

def ExecClausesShape (cs : List Clause) : Prop :=
  ∀ c ∈ cs, ExecClauseShape c

lemma execEncodableVar_state (t q : ℕ) : ExecEncodableVar (stateVar t q) :=
  Or.inl ⟨t, q, rfl⟩

lemma execEncodableVar_head (t p : ℕ) : ExecEncodableVar (headVar t p) :=
  Or.inr (Or.inl ⟨t, p, rfl⟩)

lemma execEncodableVar_cell (t p a : ℕ) : ExecEncodableVar (cellVar t p a) :=
  Or.inr (Or.inr ⟨t, p, a, rfl⟩)

lemma execClauseShape_of_lits {ls : List Literal}
    (hls : ∀ l ∈ ls, ExecEncodableVar l.var) :
    ExecClauseShape ⟨ls⟩ := by
  intro l hl
  exact hls l hl

lemma execClausesShape_map {α : Type} (f : α → Clause) (xs : List α)
    (hf : ∀ x ∈ xs, ExecClauseShape (f x)) :
    ExecClausesShape (xs.map f) := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  exact hf x hx

lemma execClausesShape_append (xs ys : List Clause)
    (hxs : ExecClausesShape xs) (hys : ExecClausesShape ys) :
    ExecClausesShape (xs ++ ys) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hxs c h
  · exact hys c h

lemma execClausesShape_cons (c : Clause) (cs : List Clause)
    (hc : ExecClauseShape c) (hcs : ExecClausesShape cs) :
    ExecClausesShape (c :: cs) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact hcs d hd

lemma execClausesShape_flatMap {α : Type} (f : α → List Clause)
    (xs : List α) (hf : ∀ x ∈ xs, ExecClausesShape (f x)) :
    ExecClausesShape (xs.flatMap f) := by
  intro c hc
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
  exact hf x hx c hc

lemma execClauseShape_unitPos (v : ℕ) (hv : ExecEncodableVar v) :
    ExecClauseShape (unitPos v) := by
  apply execClauseShape_of_lits
  intro l hl
  simp at hl
  rcases hl with rfl
  exact hv

lemma execClauseShape_imply2 (a b d : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) (hd : ExecEncodableVar d) :
    ExecClauseShape (imply2 a b d) := by
  apply execClauseShape_of_lits
  intro l hl
  simp at hl
  rcases hl with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hd

lemma execClauseShape_imply3 (a b c d : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) (hc : ExecEncodableVar c)
    (hd : ExecEncodableVar d) : ExecClauseShape (imply3 a b c d) := by
  apply execClauseShape_of_lits
  intro l hl
  simp at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hd

lemma execClauseShape_implyPos (a b : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) :
    ExecClauseShape (implyPos a b) := by
  apply execClauseShape_of_lits
  intro l hl
  simp at hl
  rcases hl with rfl | rfl
  · exact ha
  · exact hb

lemma execClauseShape_forbid3 (a b c : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) (hc : ExecEncodableVar c) :
    ExecClauseShape (forbid3 a b c) := by
  apply execClauseShape_of_lits
  intro l hl
  simp at hl
  rcases hl with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

lemma execClauseShape_atLeastOne (vs : List ℕ)
    (hvs : ∀ v ∈ vs, ExecEncodableVar v) :
    ExecClauseShape (atLeastOne vs) := by
  apply execClauseShape_of_lits
  intro l hl
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (by simpa [atLeastOne] using hl)
  exact hvs v hv

lemma execClausesShape_atMostOne (vs : List ℕ)
    (hvs : ∀ v ∈ vs, ExecEncodableVar v) :
    ExecClausesShape (atMostOne vs) := by
  induction vs with
  | nil =>
      intro c hc
      cases hc
  | cons v vs ih =>
      apply execClausesShape_append
      · apply execClausesShape_map
        intro w hw
        apply execClauseShape_of_lits
        intro l hl
        simp at hl
        rcases hl with rfl | rfl
        · exact hvs v (by simp)
        · exact hvs w (by simp [hw])
      · apply ih
        intro w hw
        exact hvs w (by simp [hw])

lemma execClausesShape_exactlyOne (vs : List ℕ)
    (hvs : ∀ v ∈ vs, ExecEncodableVar v) :
    ExecClausesShape (exactlyOne vs) := by
  intro c hc
  simp only [exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact execClauseShape_atLeastOne vs hvs
  · exact execClausesShape_atMostOne vs hvs c hc

lemma execClausesShape_uniqueness (S A : List ℕ) (W T : ℕ) :
    ExecClausesShape (execUniquenessClauses S A W T) := by
  unfold execUniquenessClauses
  apply execClausesShape_flatMap
  intro t ht
  apply execClausesShape_append
  · apply execClausesShape_append
    · apply execClausesShape_exactlyOne
      intro q hq
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq
      exact execEncodableVar_state t q
    · apply execClausesShape_exactlyOne
      intro p hp
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp
      exact execEncodableVar_head t p
  · apply execClausesShape_flatMap
    intro p hp
    apply execClausesShape_exactlyOne
    intro a ha
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha
    exact execEncodableVar_cell t p a

lemma execClausesShape_persist (A : List ℕ) (W T : ℕ) :
    ExecClausesShape (execPersistClauses A W T) := by
  unfold execPersistClauses
  apply execClausesShape_flatMap
  intro t ht
  apply execClausesShape_flatMap
  intro pHead hpHead
  apply execClausesShape_flatMap
  intro pCell hpCell
  by_cases heq : pHead = pCell
  · simp [heq, ExecClausesShape]
  · simp only [ite_eq_right heq]
    apply execClausesShape_map
    intro a ha
    exact execClauseShape_imply2 (headVar t pHead)
      (cellVar t pCell a) (cellVar (t + 1) pCell a)
      (execEncodableVar_head t pHead) (execEncodableVar_cell t pCell a)
      (execEncodableVar_cell (t + 1) pCell a)

lemma execClausesShape_three_imply3 (a b c d e f : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) (hc : ExecEncodableVar c)
    (hd : ExecEncodableVar d) (he : ExecEncodableVar e) (hf : ExecEncodableVar f) :
    ExecClausesShape [imply3 a b c d, imply3 a b c e,
      imply3 a b c f] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil] at hk
  rcases hk with hk | hk
  · subst k
    exact execClauseShape_imply3 a b c d ha hb hc hd
  · rcases hk with hk | hk
    · subst k
      exact execClauseShape_imply3 a b c e ha hb hc he
    · rcases hk with hk | hk
      · subst k
        exact execClauseShape_imply3 a b c f ha hb hc hf
      · contradiction

lemma execClausesShape_one_forbid3 (a b c : ℕ)
    (ha : ExecEncodableVar a) (hb : ExecEncodableVar b) (hc : ExecEncodableVar c) :
    ExecClausesShape [forbid3 a b c] := by
  intro k hk
  simp only [List.mem_singleton] at hk
  subst k
  exact execClauseShape_forbid3 a b c ha hb hc

lemma execClausesShape_transOne {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W t p : ℕ) (q : Λ) (a : Δ) :
    ExecClausesShape (execTransOne M S A W t p q a) := by
  cases hM : M q a with
  | none =>
      simp only [execTransOne, hM]
      exact execClausesShape_three_imply3
        (stateVar t (execStateIdx S q)) (headVar t p)
        (cellVar t p (execLetterIdx A a))
        (stateVar (t + 1) (execStateIdx S q))
        (headVar (t + 1) p)
        (cellVar (t + 1) p (execLetterIdx A a))
        (execEncodableVar_state _ _) (execEncodableVar_head _ _)
        (execEncodableVar_cell _ _ _) (execEncodableVar_state _ _)
        (execEncodableVar_head _ _) (execEncodableVar_cell _ _ _)
  | some z =>
      rcases z with ⟨q', stmt⟩
      by_cases hq : q' ∈ S
      · cases stmt with
        | write b =>
            simp only [execTransOne, hM, hq]
            exact execClausesShape_three_imply3
              (stateVar t (execStateIdx S q)) (headVar t p)
              (cellVar t p (execLetterIdx A a))
              (stateVar (t + 1) (execStateIdx S q'))
              (headVar (t + 1) p)
              (cellVar (t + 1) p (execLetterIdx A b))
              (execEncodableVar_state _ _) (execEncodableVar_head _ _)
              (execEncodableVar_cell _ _ _) (execEncodableVar_state _ _)
              (execEncodableVar_head _ _) (execEncodableVar_cell _ _ _)
        | move d =>
            cases hnext : nextIdx W p d with
            | none =>
                simp only [execTransOne, hM, hq, hnext]
                exact execClausesShape_one_forbid3
                  (stateVar t (execStateIdx S q)) (headVar t p)
                  (cellVar t p (execLetterIdx A a))
                  (execEncodableVar_state _ _) (execEncodableVar_head _ _)
                  (execEncodableVar_cell _ _ _)
            | some p' =>
                simp only [execTransOne, hM, hq, hnext]
                exact execClausesShape_three_imply3
                  (stateVar t (execStateIdx S q)) (headVar t p)
                  (cellVar t p (execLetterIdx A a))
                  (stateVar (t + 1) (execStateIdx S q'))
                  (headVar (t + 1) p')
                  (cellVar (t + 1) p (execLetterIdx A a))
                  (execEncodableVar_state _ _) (execEncodableVar_head _ _)
                  (execEncodableVar_cell _ _ _) (execEncodableVar_state _ _)
                  (execEncodableVar_head _ _) (execEncodableVar_cell _ _ _)
      · simp only [execTransOne, hM, hq]
        exact execClausesShape_one_forbid3
          (stateVar t (execStateIdx S q)) (headVar t p)
          (cellVar t p (execLetterIdx A a))
          (execEncodableVar_state _ _) (execEncodableVar_head _ _)
          (execEncodableVar_cell _ _ _)

lemma execClausesShape_trans {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W T : ℕ) : ExecClausesShape (execTransClauses M S A W T) := by
  unfold execTransClauses
  apply execClausesShape_flatMap
  intro t ht
  apply execClausesShape_flatMap
  intro p hp
  apply execClausesShape_flatMap
  intro q hq
  apply execClausesShape_flatMap
  intro a ha
  exact execClausesShape_transOne M S A W t p q a

lemma execClausesShape_accept {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A output : List Δ) (W T : ℕ) :
    ExecClausesShape (execAcceptClauses M S A output W T) := by
  unfold execAcceptClauses
  apply execClausesShape_append
  · apply execClausesShape_flatMap
    intro pHead _
    apply execClausesShape_map
    intro p _
    exact execClauseShape_implyPos _ _ (execEncodableVar_head _ _) (execEncodableVar_cell _ _ _)
  · intro c hc
    have hc' := List.mem_singleton.mp hc
    subst c
    apply execClauseShape_atLeastOne
    intro q hq
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq
    exact execEncodableVar_state _ _

lemma execClauseShape_execInitStateClause {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (S : List Λ) : ExecClauseShape (execInitStateClause S) := by
  by_cases hd : default ∈ S
  · simp only [execInitStateClause, hd, ↓reduceIte]
    exact execClauseShape_unitPos _ (execEncodableVar_state _ _)
  · simp only [execInitStateClause, hd, ↓reduceIte]
    intro l hl
    cases hl

lemma execClausesShape_execBoundedPrefixInitClauses
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (S : List Λ) (A : List Δ) (pref : List Δ)
    (freeLen : ℕ) (allowed : List Δ) (blank : Δ) (W T : ℕ) :
    ExecClausesShape
      (execBoundedPrefixInitClauses S A pref freeLen allowed blank W T) := by
  unfold execBoundedPrefixInitClauses
  apply execClausesShape_append
  · apply execClausesShape_cons
    · exact execClauseShape_execInitStateClause S
    · apply execClausesShape_cons
      · exact execClauseShape_unitPos _ (execEncodableVar_head _ _)
      · apply execClausesShape_map
        intro p hp
        by_cases hfix : p < T + pref.length
        · simp only [hfix, ↓reduceIte]
          exact execClauseShape_unitPos _ (execEncodableVar_cell _ _ _)
        · by_cases hfree : p < T + pref.length + freeLen
          · simp only [hfix, hfree, ↓reduceIte]
            exact execClauseShape_atLeastOne _ (by
              intro a ha
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha
              exact execEncodableVar_cell _ _ _)
          · simp only [hfix, hfree, ↓reduceIte]
            exact execClauseShape_unitPos _ (execEncodableVar_cell _ _ _)
  · apply execClausesShape_map
    intro i hi
    exact execClauseShape_implyPos _ _
      (execEncodableVar_cell _ _ _) (execEncodableVar_cell _ _ _)

lemma execTableauMachineWithInit_shape
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (input output : List Δ) (T : ℕ) (initial : List Clause)
    (hinit : ExecClausesShape initial) :
    ExecClausesShape
      (execTableauMachineWithInit M S A input output T initial).clauses := by
  simp only [execTableauMachineWithInit]
  simp only [List.append_assoc]
  apply execClausesShape_append
  · exact execClausesShape_uniqueness
      (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a)
      (windowSize input.length output.length T) T
  · apply execClausesShape_append
    · exact hinit
    · apply execClausesShape_append
      · exact execClausesShape_trans M S A
          (windowSize input.length output.length T) T
      · apply execClausesShape_append
        · exact execClausesShape_persist
            (A.map fun a => A.idxOf a)
            (windowSize input.length output.length T) T
        · exact execClausesShape_accept M S A output
            (windowSize input.length output.length T) T

lemma execGenerateBoundedVerifierCNF_shape
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T : ℕ) :
    ExecClausesShape
      (execGenerateBoundedVerifierCNF tm x certificateBound T).clauses := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length (tapeSymbols [true]).length T
  have hinit : ExecClausesShape
      (execBoundedPrefixInitClauses tm.stateList tm.letterList pref
        certificateBound [some false, some true] none W T) := by
    exact execClausesShape_execBoundedPrefixInitClauses tm.stateList tm.letterList
      pref certificateBound [some false, some true] none W T
  simpa [execGenerateBoundedVerifierCNF, pref, shape, W] using
    (execTableauMachineWithInit_shape tm.base.M tm.stateList tm.letterList
      shape (tapeSymbols [true]) T
      (execBoundedPrefixInitClauses tm.stateList tm.letterList pref
        certificateBound [some false, some true] none W T) hinit)

lemma execGenerateBoundedVerifierCNF_cnfUsedVars_shape
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T v : ℕ)
    (hv : v ∈ cnfUsedVars
      (execGenerateBoundedVerifierCNF tm x certificateBound T)) :
    ExecEncodableVar v := by
  have hv' : v ∈
      (execGenerateBoundedVerifierCNF tm x certificateBound T).clauses.flatMap
        (fun c => c.lits.map Literal.var) :=
    List.mem_dedup.mp hv
  obtain ⟨c, hc, hcl⟩ := List.mem_flatMap.mp hv'
  obtain ⟨l, hl, hvar⟩ := List.mem_map.mp hcl
  have hshape := (execGenerateBoundedVerifierCNF_shape tm x certificateBound T)
    c hc l hl
  simpa [hvar] using hshape

lemma execPairGenerateBoundedVerifierCNF_sat_iff
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T : ℕ) :
    SAT (execPairGenerateBoundedVerifierCNF (executableTableauMachineOf tm)
      x certificateBound T) ↔
      SAT (execGenerateBoundedVerifierCNF tm x certificateBound T) := by
  rw [execPairGenerateBoundedVerifierCNF_eq_map]
  change SAT (execMapCNF execVarMap
      (execGenerateBoundedVerifierCNF tm x certificateBound T)) ↔ _
  apply execMapCNF_sat_iff
  intro u v hu hv hmap
  exact execVarMap_injective_encodable
    (execGenerateBoundedVerifierCNF_cnfUsedVars_shape tm x certificateBound T u hu)
    (execGenerateBoundedVerifierCNF_cnfUsedVars_shape tm x certificateBound T v hv)
    hmap

/-- `execTableauMachineWithInit_shape` generalized to an explicit window: no
relationship to `windowSize` is needed since every family shape lemma it
composes is already `W`-polymorphic. -/
lemma execTableauMachineWithInitAtWindow_shape_encodable
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (T W : ℕ) (initial : List Clause)
    (hinit : ExecClausesShape initial) :
    ExecClausesShape
      (execEncodableTableauMachineWithInitAtWindow M S A output T W initial).clauses := by
  simp only [execEncodableTableauMachineWithInitAtWindow]
  simp only [List.append_assoc]
  apply execClausesShape_append
  · exact execClausesShape_uniqueness
      (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a) W T
  · apply execClausesShape_append
    · exact hinit
    · apply execClausesShape_append
      · exact execClausesShape_trans M S A W T
      · apply execClausesShape_append
        · exact execClausesShape_persist (A.map fun a => A.idxOf a) W T
        · exact execClausesShape_accept M S A output W T

lemma execGenerateBoundedVerifierCNFAtWindow_shape
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T W : ℕ) :
    ExecClausesShape
      (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W).clauses := by
  let pref : List (Option Bool) := (pairBits x []).map some
  have hinit : ExecClausesShape
      (execBoundedPrefixInitClauses tm.stateList tm.letterList pref
        certificateBound [some false, some true] none W T) := by
    exact execClausesShape_execBoundedPrefixInitClauses tm.stateList tm.letterList
      pref certificateBound [some false, some true] none W T
  simpa [execGenerateBoundedVerifierCNFAtWindow, pref] using
    (execTableauMachineWithInitAtWindow_shape_encodable tm.base.M tm.stateList tm.letterList
      (tapeSymbols [true]) T W
      (execBoundedPrefixInitClauses tm.stateList tm.letterList pref
        certificateBound [some false, some true] none W T) hinit)

lemma execGenerateBoundedVerifierCNFAtWindow_cnfUsedVars_shape
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T W v : ℕ)
    (hv : v ∈ cnfUsedVars
      (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W)) :
    ExecEncodableVar v := by
  have hv' : v ∈
      (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W).clauses.flatMap
        (fun c => c.lits.map Literal.var) :=
    List.mem_dedup.mp hv
  obtain ⟨c, hc, hcl⟩ := List.mem_flatMap.mp hv'
  obtain ⟨l, hl, hvar⟩ := List.mem_map.mp hcl
  have hshape := (execGenerateBoundedVerifierCNFAtWindow_shape tm x certificateBound T W)
    c hc l hl
  simpa [hvar] using hshape

/-- `execPairGenerateBoundedVerifierCNF_sat_iff` generalized to an explicit
window. -/
lemma execPairGenerateBoundedVerifierCNFAtWindow_sat_iff
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T W : ℕ) :
    SAT (execPairGenerateBoundedVerifierCNFAtWindow (executableTableauMachineOf tm)
      x certificateBound T W) ↔
      SAT (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W) := by
  rw [execPairGenerateBoundedVerifierCNFAtWindow_eq_map]
  change SAT (execMapCNF execVarMap
      (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W)) ↔ _
  apply execMapCNF_sat_iff
  intro u v hu hv hmap
  exact execVarMap_injective_encodable
    (execGenerateBoundedVerifierCNFAtWindow_cnfUsedVars_shape tm x certificateBound T W u hu)
    (execGenerateBoundedVerifierCNFAtWindow_cnfUsedVars_shape tm x certificateBound T W v hv)
    hmap

end NPComplete.CookLevin

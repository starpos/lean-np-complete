module

public import NPComplete.CookLevin.Generate.CompactLayout

/-!
# Tableau Numbering Bridge

The executable layout and the established Encodable-numbered tableau use different variable indices.
This module keeps that proof-only mismatch out of runtime generation by establishing a clause renaming
bridge, so semantic correctness can reuse results for the established encoding.
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

/-! ## Variable-map bridge for the compact executable generator

The direct compiler uses `Nat.pair`, whereas the Encodable-numbered tableau
uses generic product numbering.  The following map is only a proof bridge:
the executable generator itself never evaluates it. -/
noncomputable def execVarMap (v : ℕ) : ℕ :=
  if _h0 : v % 3 = 0 then
    match Encodable.decode (α := ℕ × ℕ × ℕ) (v / 3) with
    | some z => execCompactLayout.cell z.1 z.2.1 z.2.2
    | none => 0
  else if _h1 : v % 3 = 1 then
    match Encodable.decode (α := ℕ × ℕ) (v / 3) with
    | some z => execCompactLayout.state z.1 z.2
    | none => 1
  else
    match Encodable.decode (α := ℕ × ℕ) (v / 3) with
    | some z => execCompactLayout.head z.1 z.2
    | none => 2

lemma execVarMap_cell (t p a : ℕ) :
    execVarMap (cellVar t p a) = execCompactLayout.cell t p a := by
  simp [execVarMap, cellVar]

lemma execVarMap_state (t q : ℕ) :
    execVarMap (stateVar t q) = execCompactLayout.state t q := by
  simp [execVarMap, stateVar, div3_mul3_add1]

lemma execVarMap_head (t p : ℕ) :
    execVarMap (headVar t p) = execCompactLayout.head t p := by
  simp [execVarMap, headVar, div3_mul3_add2]

def execMapLiteral (m : ℕ → ℕ) : Literal → Literal
  | .pos v => .pos (m v)
  | .neg v => .neg (m v)

def execMapClause (m : ℕ → ℕ) (c : Clause) : Clause :=
  ⟨c.lits.map (execMapLiteral m)⟩

def execMapClauses (m : ℕ → ℕ) (cs : List Clause) : List Clause :=
  cs.map (execMapClause m)

lemma execMapClause_unitPos (m : ℕ → ℕ) (v : ℕ) :
    execMapClause m (unitPos v) = unitPos (m v) := by
  simp [execMapClause, execMapLiteral, unitPos]

lemma execMapClause_imply2 (m : ℕ → ℕ) (a b d : ℕ) :
    execMapClause m (imply2 a b d) = imply2 (m a) (m b) (m d) := by
  simp [execMapClause, execMapLiteral, imply2]

lemma execMapClause_imply3 (m : ℕ → ℕ) (a b c d : ℕ) :
    execMapClause m (imply3 a b c d) = imply3 (m a) (m b) (m c) (m d) := by
  simp [execMapClause, execMapLiteral, imply3]

lemma execMapClause_implyPos (m : ℕ → ℕ) (a b : ℕ) :
    execMapClause m (implyPos a b) = implyPos (m a) (m b) := by
  simp [execMapClause, execMapLiteral, implyPos]

lemma execMapClause_forbid3 (m : ℕ → ℕ) (a b c : ℕ) :
    execMapClause m (forbid3 a b c) = forbid3 (m a) (m b) (m c) := by
  simp [execMapClause, execMapLiteral, forbid3]

lemma execMapClause_atLeastOne (m : ℕ → ℕ) (vs : List ℕ) :
    execMapClause m (atLeastOne vs) = atLeastOne (vs.map m) := by
  simp [execMapClause, execMapLiteral, atLeastOne]

lemma execMapClauses_atMostOne (m : ℕ → ℕ) (vs : List ℕ) :
    execMapClauses m (atMostOne vs) = atMostOne (vs.map m) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [atMostOne_cons, execMapClauses, List.map_append]
      rw [List.map_map]
      have ih' : List.map (execMapClause m) (atMostOne vs) =
          atMostOne (List.map m vs) := by
        simpa [execMapClauses] using ih
      rw [ih']
      simp [execMapClause, execMapLiteral, List.map_map, Function.comp_def,
        atMostOne_cons]

lemma execMapClauses_exactlyOne (m : ℕ → ℕ) (vs : List ℕ) :
    execMapClauses m (exactlyOne vs) = exactlyOne (vs.map m) := by
  change execMapClause m (atLeastOne vs) ::
      execMapClauses m (atMostOne vs) =
    atLeastOne (vs.map m) :: atMostOne (vs.map m)
  rw [execMapClause_atLeastOne, execMapClauses_atMostOne]

lemma execMapClauses_append (m : ℕ → ℕ) (xs ys : List Clause) :
    execMapClauses m (xs ++ ys) = execMapClauses m xs ++ execMapClauses m ys := by
  simp [execMapClauses]

lemma execMapClauses_flatMap {α : Type} (m : ℕ → ℕ)
    (f : α → List Clause) (xs : List α) :
    execMapClauses m (xs.flatMap f) =
      xs.flatMap (fun x => execMapClauses m (f x)) := by
  simp [execMapClauses, List.map_flatMap]

lemma execMapClauses_execUniquenessClauses (m : ℕ → ℕ) (v : ExecVarLayout)
    (S A : List ℕ) (W T : ℕ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execUniquenessClauses S A W T) =
      execUniquenessClausesAt v S A W T := by
  simp only [execUniquenessClauses, execUniquenessClausesAt,
    execMapClauses_flatMap, execMapClauses_append]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro t ht
  simp only [execMapClauses_exactlyOne, List.map_map]
  have hs' : m ∘ (fun q => stateVar t q) = fun q => v.state t q := by
    funext q
    exact hs t q
  have hh' : m ∘ (fun p => headVar t p) = fun p => v.head t p := by
    funext p
    exact hh t p
  have ha' : ∀ p, m ∘ (fun a => cellVar t p a) =
      (fun a => v.cell t p a) := by
    intro p
    funext a
    exact ha t p a
  simp_rw [hs', hh', ha']

lemma execMapClause_execInitStateClause {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout) (S : List Λ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q) :
    execMapClause m (execInitStateClause S) =
      execInitStateClauseAt v S := by
  by_cases hd : default ∈ S
  · unfold execInitStateClause execInitStateClauseAt
    simp only [ite_eq_left hd]
    rw [execMapClause_unitPos]
    exact congrArg unitPos (hs 0 (S.idxOf default))
  · simp [execInitStateClause, execInitStateClauseAt, hd, execMapClause]

lemma execMapClauses_execPersistClauses (m : ℕ → ℕ) (v : ExecVarLayout)
    (A : List ℕ) (W T : ℕ)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execPersistClauses A W T) =
      execPersistClausesAt v A W T := by
  have flatMap_congr : ∀ {α β : Type} (xs : List α)
      (f g : α → List β), (∀ x ∈ xs, f x = g x) →
      xs.flatMap f = xs.flatMap g := by
    intro α β xs f g h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.flatMap_cons]
        rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
  unfold execPersistClauses execPersistClausesAt
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro t ht
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro pHead hpHead
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro pCell hpCell
  by_cases h : pHead = pCell
  · simp [h, execMapClauses]
  · simp [h, execMapClauses, execMapClause_imply2, hh, ha]

lemma execMapClauses_execTransOne {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout)
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W t p : ℕ) (q : Λ) (a : Δ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execTransOne M S A W t p q a) =
      execTransOneAt v M S A W t p q a := by
  cases hM : M q a with
  | none =>
      simp [execTransOne, execTransOneAt, execMapClauses,
        execMapClause_imply3, execStateIdx, execLetterIdx,
        hM, hs, hh, ha]
  | some z =>
      rcases z with ⟨q', stmt⟩
      by_cases hq : q' ∈ S
      · cases stmt with
        | write b =>
            simp [execTransOne, execTransOneAt, execMapClauses,
              execMapClause_imply3, execStateIdx, execLetterIdx,
              hM, hq, hs, hh, ha]
        | move d =>
            cases hnext : nextIdx W p d with
            | none =>
                simp [execTransOne, execTransOneAt, execMapClauses,
                  execMapClause_forbid3, execStateIdx, execLetterIdx,
                  hM, hq, hnext, hs, hh, ha]
            | some p' =>
                simp [execTransOne, execTransOneAt, execMapClauses,
                  execMapClause_imply3, execStateIdx, execLetterIdx,
                  hM, hq, hnext, hs, hh, ha]
      · simp [execTransOne, execTransOneAt, execMapClauses,
          execMapClause_forbid3, execStateIdx, execLetterIdx,
          hM, hq, hs, hh, ha]

lemma execMapClauses_execTransClauses {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout)
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (W T : ℕ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execTransClauses M S A W T) =
      execTransClausesAt v M S A W T := by
  have flatMap_congr : ∀ {α β : Type} (xs : List α)
      (f g : α → List β), (∀ x ∈ xs, f x = g x) →
      xs.flatMap f = xs.flatMap g := by
    intro α β xs f g h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.flatMap_cons]
        rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
  unfold execTransClauses execTransClausesAt
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro t ht
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro p hp
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro q hq
  rw [execMapClauses_flatMap]
  apply flatMap_congr
  intro a ha'
  exact execMapClauses_execTransOne m v M S A W t p q a hs hh ha

lemma execMapClauses_execAcceptClauses {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout)
    (M : Machine Δ Λ) (S : List Λ) (A output : List Δ) (W T : ℕ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execAcceptClauses M S A output W T) =
      execAcceptClausesAt v M S A output W T := by
  have flatMap_congr : ∀ {α β : Type} (xs : List α)
      (f g : α → List β), (∀ x ∈ xs, f x = g x) →
      xs.flatMap f = xs.flatMap g := by
    intro α β xs f g h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.flatMap_cons]
        rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
  unfold execAcceptClauses execAcceptClausesAt
  rw [execMapClauses_append]
  congr 1
  · rw [execMapClauses_flatMap]
    apply flatMap_congr
    intro pHead _
    simp only [execMapClauses, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp [Function.comp_apply, execMapClause_implyPos, execLetterIdx, hh, ha]
  · simp only [execMapClauses, List.map_cons, List.map_nil]
    rw [execMapClause_atLeastOne]
    congr 1
    apply congrArg atLeastOne
    rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hs T (S.idxOf q)

lemma execMapClauses_execBoundedPrefixInitClauses
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout) (S : List Λ) (A : List Δ)
    (pref : List Δ) (freeLen : ℕ) (allowed : List Δ) (blank : Δ)
    (W T : ℕ)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a) :
    execMapClauses m (execBoundedPrefixInitClauses S A pref freeLen
      allowed blank W T) =
      execBoundedPrefixInitClausesAt v S A pref freeLen
        allowed blank W T := by
  simp only [execBoundedPrefixInitClauses,
    execBoundedPrefixInitClausesAt, execMapClauses,
    List.map_append, List.map_cons, List.map_map]
  rw [execMapClause_execInitStateClause m v S hs]
  rw [execMapClause_unitPos, hh 0 (originIdx T)]
  have hcell :
      List.map (execMapClause m ∘ fun p =>
        if p < T + pref.length then
          unitPos (cellVar 0 p (execLetterIdx A
            (initSymbol pref (idxToPos T p))))
        else if p < T + pref.length + freeLen then
          atLeastOne ((blank :: allowed).map fun a =>
            cellVar 0 p (execLetterIdx A a))
        else unitPos (cellVar 0 p (execLetterIdx A blank)))
        (List.range W) =
      List.map (fun p =>
        if p < T + pref.length then
          unitPos (v.cell 0 p (A.idxOf
            (initSymbol pref (idxToPos T p))))
        else if p < T + pref.length + freeLen then
          atLeastOne ((blank :: allowed).map fun a =>
            v.cell 0 p (A.idxOf a))
        else unitPos (v.cell 0 p (A.idxOf blank)))
        (List.range W) := by
    apply List.map_congr_left
    intro p hp
    by_cases hfix : p < T + pref.length
    · simp [hfix, Function.comp_apply, execMapClause_unitPos,
        execLetterIdx, ha]
    · by_cases hfree : p < T + pref.length + freeLen
      · simp [hfix, hfree, Function.comp_apply,
          execMapClause_atLeastOne, execLetterIdx, ha,
          List.map_map, Function.comp_def]
      · simp [hfix, hfree, Function.comp_apply,
          execMapClause_unitPos, execLetterIdx, ha]
  have hcell' := hcell
  simp only [List.map_cons] at hcell'
  rw [hcell']
  have htail :
      List.map (execMapClause m ∘ fun i =>
        implyPos (cellVar 0 (T + pref.length + i)
          (execLetterIdx A blank))
          (cellVar 0 (T + pref.length + i + 1)
            (execLetterIdx A blank))) (List.range freeLen) =
      List.map (fun i =>
        implyPos (v.cell 0 (T + pref.length + i) (A.idxOf blank))
          (v.cell 0 (T + pref.length + i + 1) (A.idxOf blank)))
        (List.range freeLen) := by
    apply List.map_congr_left
    intro i hi
    simp [Function.comp_apply, execMapClause_implyPos,
      execLetterIdx, ha]
  rw [htail]

lemma execMapClauses_execTableauMachineWithInit
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout)
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (input output : List Δ) (T : ℕ)
    (initial initialAt : List Clause)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a)
    (hinit : execMapClauses m initial = initialAt) :
    execMapClauses m (execTableauMachineWithInit M S A input output T initial).clauses =
      (execTableauMachineWithInitAt v M S A input output T initialAt).clauses := by
  simp only [execTableauMachineWithInit, execTableauMachineWithInitAt,
    execMapClauses_append]
  have hu : execMapClauses m
      (execUniquenessClauses (S.map (execStateIdx S))
        (A.map (execLetterIdx A))
        (windowSize input.length output.length T) T) =
      execUniquenessClausesAt v
        (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a)
        (windowSize input.length output.length T) T := by
    change execMapClauses m
        (execUniquenessClauses
          (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a)
          (windowSize input.length output.length T) T) = _
    exact execMapClauses_execUniquenessClauses m v
      (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a)
      (windowSize input.length output.length T) T hs hh ha
  rw [hu]
  rw [hinit]
  rw [execMapClauses_execTransClauses m v M S A
    (windowSize input.length output.length T) T hs hh ha]
  have hp : execMapClauses m
      (execPersistClauses (A.map (execLetterIdx A))
        (windowSize input.length output.length T) T) =
      execPersistClausesAt v (A.map (execLetterIdx A))
        (windowSize input.length output.length T) T :=
    execMapClauses_execPersistClauses m v (A.map (execLetterIdx A))
      (windowSize input.length output.length T) T hh ha
  rw [hp]
  have hA : A.map (execLetterIdx A) =
      A.map (fun a => A.idxOf a) := by
    apply List.map_congr_left
    intro a ha'
    rfl
  rw [hA]
  rw [execMapClauses_execAcceptClauses m v M S A output
    (windowSize input.length output.length T) T hs hh ha]

/-- `execMapClauses_execTableauMachineWithInit` generalized to an explicit window: the
Encodable-numbered family maps to the `ExecVarLayout`-numbered family at any
common `W`, since every family bridge lemma it composes is `W`-polymorphic. -/
lemma execMapClauses_execEncodableTableauMachineWithInitAtWindow
    {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (m : ℕ → ℕ) (v : ExecVarLayout)
    (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (T W : ℕ)
    (initial initialAt : List Clause)
    (hs : ∀ t q, m (stateVar t q) = v.state t q)
    (hh : ∀ t p, m (headVar t p) = v.head t p)
    (ha : ∀ t p a, m (cellVar t p a) = v.cell t p a)
    (hinit : execMapClauses m initial = initialAt) :
    execMapClauses m
      (execEncodableTableauMachineWithInitAtWindow M S A output T W initial).clauses =
      (execTableauMachineWithInitAtWindow v M S A output T W initialAt).clauses := by
  simp only [execEncodableTableauMachineWithInitAtWindow, execTableauMachineWithInitAtWindow,
    execMapClauses_append]
  have hu : execMapClauses m
      (execUniquenessClauses (S.map (execStateIdx S))
        (A.map (execLetterIdx A)) W T) =
      execUniquenessClausesAt v
        (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a) W T := by
    change execMapClauses m
        (execUniquenessClauses
          (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a) W T) = _
    exact execMapClauses_execUniquenessClauses m v
      (S.map fun q => S.idxOf q) (A.map fun a => A.idxOf a) W T hs hh ha
  rw [hu]
  rw [hinit]
  rw [execMapClauses_execTransClauses m v M S A W T hs hh ha]
  have hp : execMapClauses m
      (execPersistClauses (A.map (execLetterIdx A)) W T) =
      execPersistClausesAt v (A.map (execLetterIdx A)) W T :=
    execMapClauses_execPersistClauses m v (A.map (execLetterIdx A)) W T hh ha
  rw [hp]
  have hA : A.map (execLetterIdx A) =
      A.map (fun a => A.idxOf a) := by
    apply List.map_congr_left
    intro a ha'
    rfl
  rw [hA]
  rw [execMapClauses_execAcceptClauses m v M S A output W T hs hh ha]

def executableTableauMachineOf (tm : ExecutableTableauAux) :
    ExecutableTableauMachine where
  Λ := tm.base.Λ
  M := tm.base.M
  stateList := tm.stateList
  letterList := tm.letterList

lemma execPairGenerateBoundedVerifierCNF_eq_map
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T : ℕ) :
    execPairGenerateBoundedVerifierCNF (executableTableauMachineOf tm)
        x certificateBound T =
      ⟨execMapClauses execVarMap
        (execGenerateBoundedVerifierCNF tm x certificateBound T).clauses⟩ := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let shape : List (Option Bool) := pref ++ List.replicate certificateBound none
  let W := windowSize shape.length (tapeSymbols [true]).length T
  let initial := execBoundedPrefixInitClauses tm.stateList tm.letterList
    pref certificateBound [some false, some true] none W T
  let initialAt := execBoundedPrefixInitClausesAt execCompactLayout
    tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T
  have hs : ∀ t q, execVarMap (stateVar t q) =
      execCompactLayout.state t q := by
    intro t q
    exact execVarMap_state t q
  have hh : ∀ t p, execVarMap (headVar t p) =
      execCompactLayout.head t p := by
    intro t p
    exact execVarMap_head t p
  have ha : ∀ t p a, execVarMap (cellVar t p a) =
      execCompactLayout.cell t p a := by
    intro t p a
    exact execVarMap_cell t p a
  have hinit : execMapClauses execVarMap initial = initialAt := by
    exact execMapClauses_execBoundedPrefixInitClauses execVarMap execCompactLayout
      tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T hs hh ha
  have htable := execMapClauses_execTableauMachineWithInit execVarMap execCompactLayout
    tm.base.M tm.stateList tm.letterList shape (tapeSymbols [true]) T
    initial initialAt hs hh ha hinit
  exact congrArg (fun cs : List Clause => (⟨cs⟩ : CNF)) htable.symm

lemma execPairGenerateBoundedVerifierCNFAtWindow_eq_map
    (tm : ExecutableTableauAux) (x : List Bool)
    (certificateBound T W : ℕ) :
    execPairGenerateBoundedVerifierCNFAtWindow (executableTableauMachineOf tm)
        x certificateBound T W =
      ⟨execMapClauses execVarMap
        (execGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W).clauses⟩ := by
  let pref : List (Option Bool) := (pairBits x []).map some
  let initial := execBoundedPrefixInitClauses tm.stateList tm.letterList
    pref certificateBound [some false, some true] none W T
  let initialAt := execBoundedPrefixInitClausesAt execCompactLayout
    tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T
  have hs : ∀ t q, execVarMap (stateVar t q) =
      execCompactLayout.state t q := fun t q => execVarMap_state t q
  have hh : ∀ t p, execVarMap (headVar t p) =
      execCompactLayout.head t p := fun t p => execVarMap_head t p
  have ha : ∀ t p a, execVarMap (cellVar t p a) =
      execCompactLayout.cell t p a := fun t p a => execVarMap_cell t p a
  have hinit : execMapClauses execVarMap initial = initialAt :=
    execMapClauses_execBoundedPrefixInitClauses execVarMap execCompactLayout
      tm.stateList tm.letterList pref certificateBound
      [some false, some true] none W T hs hh ha
  have htable := execMapClauses_execEncodableTableauMachineWithInitAtWindow execVarMap execCompactLayout
    tm.base.M tm.stateList tm.letterList (tapeSymbols [true]) T W
    initial initialAt hs hh ha hinit
  exact congrArg (fun cs : List Clause => (⟨cs⟩ : CNF)) htable.symm

end NPComplete.CookLevin

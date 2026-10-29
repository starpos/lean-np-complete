module

public import NPComplete.CookLevin.Tableau.DenseLayout

/-!
`execMapClauses_sat_iff` transports a CNF to the dense layout once every
occurring variable is known to round-trip, but the clause generators never
state that fact directly.  This module supplies it: a range certificate per
clause family, built once per clause constructor and lifted through
`List.append` / `List.flatMap`, culminating in the satisfiability-equivalence of the
dense-layout descriptor CNF with the bounded-verifier map.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Turing.TM0

/-! ## Range certificates for generated clauses

`execMapClauses_sat_iff` asks for a per-literal round-trip, so the remaining
obligation is that every variable a clause family emits is a layout value with
in-range indices.  The clause constructors are shared across the five families,
so the certificates are proved once per constructor and lifted with
`List.append` / `List.flatMap`. -/

/-- Every variable occurring in a clause list satisfies `P`. -/
def ClausesVarsSat (P : ℕ → Prop) (cs : List Clause) : Prop :=
  ∀ c ∈ cs, ∀ l ∈ c.lits, P l.var

lemma clausesVarsSat_nil {P : ℕ → Prop} : ClausesVarsSat P [] := by
  intro c hc; simp at hc

lemma clausesVarsSat_append {P : ℕ → Prop} {xs ys : List Clause}
    (hx : ClausesVarsSat P xs) (hy : ClausesVarsSat P ys) :
    ClausesVarsSat P (xs ++ ys) := by
  intro c hc l hl
  rcases List.mem_append.mp hc with h | h
  · exact hx c h l hl
  · exact hy c h l hl

lemma clausesVarsSat_cons {P : ℕ → Prop} {c : Clause} {cs : List Clause}
    (hc : ∀ l ∈ c.lits, P l.var) (hcs : ClausesVarsSat P cs) :
    ClausesVarsSat P (c :: cs) := by
  intro d hd l hl
  rcases List.mem_cons.mp hd with rfl | h
  · exact hc l hl
  · exact hcs d h l hl

lemma clausesVarsSat_flatMap {P : ℕ → Prop} {α : Type} {l : List α}
    {f : α → List Clause} (h : ∀ a ∈ l, ClausesVarsSat P (f a)) :
    ClausesVarsSat P (l.flatMap f) := by
  intro c hc lit hlit
  obtain ⟨a, ha, hca⟩ := List.mem_flatMap.mp hc
  exact h a ha c hca lit hlit

lemma clausesVarsSat_atLeastOne {P : ℕ → Prop} {vs : List ℕ}
    (h : ∀ v ∈ vs, P v) : ∀ l ∈ (atLeastOne vs).lits, P l.var := by
  intro l hl
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (by simpa [atLeastOne] using hl)
  exact h v hv

lemma clausesVarsSat_atMostOne {P : ℕ → Prop} {vs : List ℕ}
    (h : ∀ v ∈ vs, P v) : ClausesVarsSat P (atMostOne vs) := by
  induction vs with
  | nil => intro c hc; simp [atMostOne] at hc
  | cons v vs ih =>
      intro c hc l hl
      rw [atMostOne_cons] at hc
      rcases List.mem_append.mp hc with hc' | hc'
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc'
        rcases (by simpa using hl :
            l = NPComplete.SAT.Literal.neg v ∨
            l = NPComplete.SAT.Literal.neg w) with rfl | rfl
        · exact h v (by simp)
        · exact h w (by simp [hw])
      · exact ih (fun x hx => h x (by simp [hx])) c hc' l hl

lemma clausesVarsSat_exactlyOne {P : ℕ → Prop} {vs : List ℕ}
    (h : ∀ v ∈ vs, P v) : ClausesVarsSat P (exactlyOne vs) :=
  clausesVarsSat_cons (clausesVarsSat_atLeastOne h) (clausesVarsSat_atMostOne h)

/-! ### Per-constructor variable certificates

Each clause constructor only ever mentions the variables it was given, so
its certificate is a direct case split on `Clause.lits` membership. -/

lemma unitPos_vars {P : ℕ → Prop} {a : ℕ} (ha : P a) :
    ∀ l ∈ (unitPos a).lits, P l.var := by
  intro l hl
  simp [unitPos] at hl
  subst hl
  exact ha

lemma forbid3_vars {P : ℕ → Prop} {a b c : ℕ} (ha : P a) (hb : P b) (hc : P c) :
    ∀ l ∈ (forbid3 a b c).lits, P l.var := by
  intro l hl
  simp only [forbid3, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

lemma imply2_vars {P : ℕ → Prop} {a b d : ℕ} (ha : P a) (hb : P b) (hd : P d) :
    ∀ l ∈ (imply2 a b d).lits, P l.var := by
  intro l hl
  simp only [imply2, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hd

lemma imply3_vars {P : ℕ → Prop} {a b c d : ℕ} (ha : P a) (hb : P b) (hc : P c) (hd : P d) :
    ∀ l ∈ (imply3 a b c d).lits, P l.var := by
  intro l hl
  simp only [imply3, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hd

lemma implyPos_vars {P : ℕ → Prop} {a b : ℕ} (ha : P a) (hb : P b) :
    ∀ l ∈ (implyPos a b).lits, P l.var := by
  intro l hl
  simp only [implyPos, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact ha
  · exact hb

/-- `nextIdx` never leaves the window: `.left` decrements, `.right` increments
by one and only succeeds while the result stays below `W`. -/
lemma nextIdx_lt {W p : ℕ} {d : Dir} {p' : ℕ} (hp : p < W)
    (h : nextIdx W p d = some p') : p' < W := by
  cases d with
  | left =>
      simp only [nextIdx] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h; omega
  | right =>
      simp only [nextIdx] at h
      split at h
      · injection h with h; omega
      · exact absurd h (by simp)

/-! ### The transition-entry family

`natTransClausesOf` is `Λ`-free, so its certificate needs only bounds on the
integer indices it is handed: the current cell's `qi`/`ai`/`p`, plus (for a
`.write` entry) the letter index it writes. -/

lemma natTransClausesOf_vars {v : ExecVarLayout} {n W m t p qi ai : ℕ} {e : NatTrans}
    (hqi : qi < n) (hai : ai < m) (hp : p < W)
    (hbi : ∀ qi' bi, e = .write qi' bi → bi < m) :
    ClausesVarsSat (LayoutVarIn v n W m) (natTransClausesOf v n W t p qi ai e) := by
  have hst : LayoutVarIn v n W m (v.state t qi) := Or.inl ⟨t, qi, hqi, rfl⟩
  have hhd : LayoutVarIn v n W m (v.head t p) := Or.inr (Or.inl ⟨t, p, hp, rfl⟩)
  have hcl : LayoutVarIn v n W m (v.cell t p ai) := Or.inr (Or.inr ⟨t, p, ai, hp, hai, rfl⟩)
  cases e with
  | halt =>
      have hst1 : LayoutVarIn v n W m (v.state (t + 1) qi) := Or.inl ⟨t + 1, qi, hqi, rfl⟩
      have hhd1 : LayoutVarIn v n W m (v.head (t + 1) p) := Or.inr (Or.inl ⟨t + 1, p, hp, rfl⟩)
      have hcl1 : LayoutVarIn v n W m (v.cell (t + 1) p ai) :=
        Or.inr (Or.inr ⟨t + 1, p, ai, hp, hai, rfl⟩)
      simp only [natTransClausesOf]
      exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
        (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
          (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
  | write qi' bi =>
      have hbi' := hbi qi' bi rfl
      simp only [natTransClausesOf]
      split
      · rename_i hqi'
        have hst1 : LayoutVarIn v n W m (v.state (t + 1) qi') := Or.inl ⟨t + 1, qi', hqi', rfl⟩
        have hhd1 : LayoutVarIn v n W m (v.head (t + 1) p) := Or.inr (Or.inl ⟨t + 1, p, hp, rfl⟩)
        have hcl1 : LayoutVarIn v n W m (v.cell (t + 1) p bi) :=
          Or.inr (Or.inr ⟨t + 1, p, bi, hp, hbi', rfl⟩)
        exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
          (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
            (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
      · exact clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil
  | move qi' d =>
      simp only [natTransClausesOf]
      split
      · rename_i hqi'
        cases hnext : nextIdx W p d with
        | none => exact clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil
        | some p' =>
            have hp' := nextIdx_lt hp hnext
            have hst1 : LayoutVarIn v n W m (v.state (t + 1) qi') :=
              Or.inl ⟨t + 1, qi', hqi', rfl⟩
            have hhd1 : LayoutVarIn v n W m (v.head (t + 1) p') :=
              Or.inr (Or.inl ⟨t + 1, p', hp', rfl⟩)
            have hcl1 : LayoutVarIn v n W m (v.cell (t + 1) p ai) :=
              Or.inr (Or.inr ⟨t + 1, p, ai, hp, hai, rfl⟩)
            exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
              (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
                (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
      · exact clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil

/-! ### The uniqueness and persistence families -/

/-- Range certificate for `execUniquenessClausesAt`: every state index in `S`
and letter index in `A` must already be bounded by `n`/`m`, since this family
only reproduces indices it is handed. -/
lemma execUniquenessClausesAt_vars (v : ExecVarLayout) (S A : List ℕ) (W T : ℕ)
    (n m : ℕ) (hS : ∀ q ∈ S, q < n) (hA : ∀ a ∈ A, a < m) :
    ClausesVarsSat (LayoutVarIn v n W m) (execUniquenessClausesAt v S A W T) := by
  unfold execUniquenessClausesAt
  apply clausesVarsSat_flatMap
  intro t _
  apply clausesVarsSat_append
  apply clausesVarsSat_append
  · apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact Or.inl ⟨t, q, hS q hq, rfl⟩
  · apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Or.inr (Or.inl ⟨t, p, List.mem_range.mp hp, rfl⟩)
  · apply clausesVarsSat_flatMap
    intro p hp
    apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inr (Or.inr ⟨t, p, a, List.mem_range.mp hp, hA a ha, rfl⟩)

/-- Range certificate for `execPersistClausesAt`: every letter index in `A`
must already be bounded by `m`. -/
lemma execPersistClausesAt_vars (v : ExecVarLayout) (A : List ℕ) (W T : ℕ)
    (n m : ℕ) (hA : ∀ a ∈ A, a < m) :
    ClausesVarsSat (LayoutVarIn v n W m) (execPersistClausesAt v A W T) := by
  unfold execPersistClausesAt
  apply clausesVarsSat_flatMap
  intro t _
  apply clausesVarsSat_flatMap
  intro pHead hpHead
  apply clausesVarsSat_flatMap
  intro pCell hpCell
  split
  · exact clausesVarsSat_nil
  · intro c hc l hl
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact imply2_vars
      (Or.inr (Or.inl ⟨t, pHead, List.mem_range.mp hpHead, rfl⟩))
      (Or.inr (Or.inr ⟨t, pCell, a, List.mem_range.mp hpCell, hA a ha, rfl⟩))
      (Or.inr (Or.inr ⟨t + 1, pCell, a, List.mem_range.mp hpCell, hA a ha, rfl⟩)) l hl

/-! ### The accept-clause and bounded-init families

Both families are still `Λ`-polymorphic: the certificate only needs every
`S.idxOf` / `A.idxOf` result bounded by `List.idxOf_le_length`, so the `+ 1`
convention from `LayoutVarIn`'s design lets it go through without any
membership hypothesis on `S` or `A`. -/

/-- Range certificate for `execAcceptClausesAt`. -/
lemma execAcceptClausesAt_vars {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine Δ Λ) (S : List Λ) (A : List Δ)
    (output : List Δ) (W T : ℕ) :
    ClausesVarsSat (LayoutVarIn v (S.length + 1) W (A.length + 1))
      (execAcceptClausesAt v M S A output W T) := by
  unfold execAcceptClausesAt
  apply clausesVarsSat_append
  · apply clausesVarsSat_flatMap
    intro pHead hpHead c hc l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hai : A.idxOf (initSymbol output ((p : ℤ) - (pHead : ℤ))) < A.length + 1 := by
      have := List.idxOf_le_length (l := A)
        (a := initSymbol output ((p : ℤ) - (pHead : ℤ)))
      omega
    exact implyPos_vars
      (Or.inr (Or.inl ⟨T, pHead, List.mem_range.mp hpHead, rfl⟩))
      (Or.inr (Or.inr ⟨T, p, _, List.mem_range.mp hp, hai, rfl⟩)) l hl
  · exact clausesVarsSat_cons
      (clausesVarsSat_atLeastOne (fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        have hqi : S.idxOf q < S.length + 1 := by
          have := List.idxOf_le_length (l := S) (a := q)
          omega
        exact Or.inl ⟨T, S.idxOf q, hqi, rfl⟩))
      clausesVarsSat_nil

/-- Range certificate for `execBoundedPrefixInitClausesAt`.  The window must
already accommodate the fixed prefix and the free suffix, matching how
`windowSize` is chosen at call sites. -/
lemma execBoundedPrefixInitClausesAt_vars {Δ Λ : Type} [Inhabited Δ] [Inhabited Λ]
    [DecidableEq Δ] [DecidableEq Λ]
    (v : ExecVarLayout) (S : List Λ) (A : List Δ) (pref : List Δ)
    (freeLen : ℕ) (allowed : List Δ) (blank : Δ) (W T : ℕ)
    (hbound : T + pref.length + freeLen < W) :
    ClausesVarsSat (LayoutVarIn v (S.length + 1) W (A.length + 1))
      (execBoundedPrefixInitClausesAt v S A pref freeLen allowed blank W T) := by
  have hTW : T < W := by omega
  have hAidx (a : Δ) : A.idxOf a < A.length + 1 := by
    have h := List.idxOf_le_length (l := A) (a := a)
    omega
  unfold execBoundedPrefixInitClausesAt
  apply clausesVarsSat_append
  · apply clausesVarsSat_cons
    · intro l hl
      unfold execInitStateClauseAt at hl
      split at hl
      · simp [unitPos] at hl
        subst hl
        have hqi : S.idxOf default < S.length + 1 := by
          have := List.idxOf_le_length (l := S) (a := (default : Λ))
          omega
        exact Or.inl ⟨0, S.idxOf default, hqi, rfl⟩
      · simp at hl
    · apply clausesVarsSat_cons
      · exact unitPos_vars (Or.inr (Or.inl ⟨0, originIdx T, by simpa [originIdx] using hTW, rfl⟩))
      · intro c hc l hl
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        have hpW : p < W := List.mem_range.mp hp
        split at hl
        · have hai := hAidx (initSymbol pref (idxToPos T p))
          exact unitPos_vars (Or.inr (Or.inr ⟨0, p, _, hpW, hai, rfl⟩)) l hl
        · split at hl
          · simp only [atLeastOne, List.map_map] at hl
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
            have hai := hAidx a
            exact Or.inr (Or.inr ⟨0, p, _, hpW, hai, rfl⟩)
          · have hai := hAidx blank
            exact unitPos_vars (Or.inr (Or.inr ⟨0, p, _, hpW, hai, rfl⟩)) l hl
  · intro c hc l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hiF : i < freeLen := List.mem_range.mp hi
    have hai := hAidx blank
    exact implyPos_vars
      (Or.inr (Or.inr ⟨0, T + pref.length + i, _, by omega, hai, rfl⟩))
      (Or.inr (Or.inr ⟨0, T + pref.length + i + 1, _, by omega, hai, rfl⟩)) l hl

/-- The window a call site picks always accommodates the prefix and the free
suffix, so `execBoundedPrefixInitClausesAt_vars`'s hypothesis is automatic
there. -/
lemma init_bound_of_windowSize (prefLen certificateBound T : ℕ) :
    T + prefLen + certificateBound <
      windowSize (prefLen + certificateBound) 1 T := by
  unfold windowSize
  omega

/-! ### Index bounds from `List.idxOf`

Stating these about `execStateIdx` / `execLetterIdx` (rather than `List.idxOf`
directly) keeps the `BEq (Option Bool)` instance aligned with the generators;
`List.idxOf_le_length` otherwise elaborates at `Option.instBEq` and `omega` then
sees two unrelated terms. -/

lemma execLetterIdx_lt (A : List (Option Bool)) (a : Option Bool) :
    execLetterIdx A a < A.length + 1 := by
  have h : execLetterIdx A a ≤ A.length := by
    unfold execLetterIdx
    exact @List.idxOf_le_length (Option Bool) instBEqOfDecidableEq inferInstance A a
  omega

lemma execStateIdx_lt {Λ : Type} [DecidableEq Λ] (S : List Λ) (q : Λ) :
    execStateIdx S q < S.length + 1 := by
  have h : execStateIdx S q ≤ S.length := by
    unfold execStateIdx
    exact List.idxOf_le_length
  omega

/-- A `.write` entry produced by `transOf` writes an in-range letter index.
This discharges `natTransClausesOf_vars`'s `hbi` obligation. -/
lemma transOf_write_bound {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) (qi' bi : ℕ)
    (h : transOf M S A q a = .write qi' bi) : bi < A.length + 1 := by
  unfold transOf at h
  cases hM : M q a with
  | none => rw [hM] at h; exact absurd h (by simp)
  | some qs =>
      obtain ⟨q', stmt⟩ := qs
      cases stmt with
      | write b =>
          rw [hM] at h
          simp only [NatTrans.write.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact execLetterIdx_lt A b
      | move d => rw [hM] at h; exact absurd h (by simp)

/-- Range certificate for the `Λ`-indexed transition family, obtained by moving
to the table-driven form and applying the cellwise certificate. -/
lemma execTransClausesAt_vars {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W T : ℕ) :
    ClausesVarsSat (LayoutVarIn v (S.length + 1) W (A.length + 1))
      (execTransClausesAt v M S A W T) := by
  rw [execTransClausesAt_eq_nat]
  refine clausesVarsSat_flatMap (fun t _ => ?_)
  refine clausesVarsSat_flatMap (fun p hp => ?_)
  refine clausesVarsSat_flatMap (fun q hq => ?_)
  refine clausesVarsSat_flatMap (fun a _ => ?_)
  have hqi : execStateIdx S q < S.length := List.idxOf_lt_length_iff.mpr hq
  refine fun c hc l hl => layoutVarIn_mono (Nat.le_succ _) (le_refl _)
    (natTransClausesOf_vars (v := v) (n := S.length) (m := A.length + 1)
      hqi (execLetterIdx_lt A a) (List.mem_range.mp hp)
      (fun qi' bi h => transOf_write_bound M S A q a qi' bi h) c hc l hl)

/-- Whole-generator certificate at an explicit window: the five families are joined by `++`, and
the index lists the uniqueness and persistence families receive are the `idxOf` images of `S`
and `A`.  No relationship between `W` and `windowSize` is needed since every family lemma it
composes is `W`-polymorphic. -/
lemma execTableauMachineWithInitAtWindow_vars {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (output : List (Option Bool)) (T W : ℕ)
    (initial : List Clause)
    (hinit : ClausesVarsSat
      (LayoutVarIn v (S.length + 1) W (A.length + 1)) initial) :
    ClausesVarsSat
      (LayoutVarIn v (S.length + 1) W (A.length + 1))
      (execTableauMachineWithInitAtWindow v M S A output T W initial).clauses := by
  have hA : ∀ a ∈ A.map (fun a => execLetterIdx A a), a < A.length + 1 := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
    exact execLetterIdx_lt A a'
  unfold execTableauMachineWithInitAtWindow
  simp only []
  refine clausesVarsSat_append (clausesVarsSat_append (clausesVarsSat_append
    (clausesVarsSat_append ?_ hinit) ?_) ?_) ?_
  · refine execUniquenessClausesAt_vars v _ _ _ _ _ _ (fun q hq => ?_) hA
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
    exact execStateIdx_lt S q'
  · exact execTransClausesAt_vars v M S A _ T
  · exact execPersistClausesAt_vars v _ _ _ _ _ hA
  · exact execAcceptClausesAt_vars v M S A output _ T

/-- Range certificate for the bounded-verifier generator at an explicit window `W`,
holding whenever the window still accommodates the fixed prefix and the free
certificate cells. -/
lemma execPairGenerateBoundedVerifierCNFAtWindow_vars (tm : ExecutableTableauMachine)
    (x : List Bool) (certificateBound T W : ℕ)
    (hspan : T + (pairBits x []).length + certificateBound < W) :
    ClausesVarsSat
      (LayoutVarIn execCompactLayout (tm.stateList.length + 1) W
        (tm.letterList.length + 1))
      (execPairGenerateBoundedVerifierCNFAtWindow tm x certificateBound T W).clauses := by
  unfold execPairGenerateBoundedVerifierCNFAtWindow
  simp only []
  refine execTableauMachineWithInitAtWindow_vars _ tm.M tm.stateList tm.letterList _ _ _ _ ?_
  exact execBoundedPrefixInitClausesAt_vars execCompactLayout tm.stateList
    tm.letterList ((pairBits x []).map some) certificateBound
    [some false, some true] none W T (by simpa using hspan)

/-! ## Transporting a generated CNF to the dense layout -/

/-- Once every variable of a CNF is known to be an in-range layout value, the
dense-layout copy is satisfiability-equivalent.  This is the payoff of the range
certificates: a producer may emit dense numbers directly, and `cnfVarBound` is
then bounded by `(T + 1) * denseBlock` instead of the `Nat.pair` spread. -/
lemma sat_denseOfCompact_of_range {n W m : ℕ} {φ : CNF}
    (hrange : ClausesVarsSat (LayoutVarIn execCompactLayout n W m) φ.clauses) :
    SAT ⟨execMapClauses (denseOfCompact n W m) φ.clauses⟩ ↔ SAT φ := by
  refine execMapClauses_sat_iff _ (compactOfDense n W m) φ ?_
  intro c hc l hl
  exact compactOfDense_denseOfCompact (hrange c hc l hl)

/-! ## Reaching the generator the rest of the development uses

`execPairGenerateBoundedVerifierCNF` fixes the layout, the shape of the tape
prefix, and the output, so the descriptor-driven family instantiated at those
choices is satisfiability-equivalent to it.  This is the point at which a
producer may work from the descriptor alone. -/

/-- The descriptor-driven family at an explicit window is satisfiability-equivalent to the
generator at that window: no relationship to `windowSize` is needed, since `descTableauCNF_sat_iff` and
`execTableauMachineWithInitAtWindow` are already `W`-polymorphic. -/
lemma descTableauCNF_pair_generate_at_window (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T W : ℕ) :
    SAT (descTableauCNF execCompactLayout
          (descriptorOf tm.base.M tm.stateList tm.letterList)
          (((pairBits x []).map some).map (execLetterIdx tm.letterList))
          certificateBound
          (([some false, some true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          ((tapeSymbols [true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          W T) ↔
      SAT (execPairGenerateBoundedVerifierCNFAtWindow (executableTableauMachineOf tm) x
            certificateBound T W) := by
  have hmem : ∀ a : Option Bool, a ∈ tm.letterList :=
    fun a => (tm.letterList_complete a).mpr (Finset.mem_univ a)
  rw [execPairGenerateBoundedVerifierCNFAtWindow, execTableauMachineWithInitAtWindow]
  exact descTableauCNF_sat_iff execCompactLayout tm.base.M tm.stateList tm.letterList
    ((pairBits x []).map some) [some false, some true] (tapeSymbols [true])
    certificateBound W T tm.stateList_nodup tm.letterList_nodup
    (fun a _ => hmem a) (hmem none)

/-- Clause-membership equivalence between the descriptor-driven family and the generator at an
explicit window.  It is stated on its own so that the range certificate below transports through
`descTableauCNF_mem` instead of through a satisfiability equivalence. -/
lemma descTableauCNF_pair_generate_mem_at_window (tm : ExecutableTableauAux)
    (x : List Bool) (certificateBound T W : ℕ) (c : Clause) :
    c ∈ (descTableauCNF execCompactLayout
          (descriptorOf tm.base.M tm.stateList tm.letterList)
          (((pairBits x []).map some).map (execLetterIdx tm.letterList))
          certificateBound
          (([some false, some true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          ((tapeSymbols [true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          W T).clauses ↔
      c ∈ (execPairGenerateBoundedVerifierCNFAtWindow (executableTableauMachineOf tm) x
            certificateBound T W).clauses := by
  have hmem : ∀ a : Option Bool, a ∈ tm.letterList :=
    fun a => (tm.letterList_complete a).mpr (Finset.mem_univ a)
  rw [execPairGenerateBoundedVerifierCNFAtWindow, execTableauMachineWithInitAtWindow]
  exact descTableauCNF_mem execCompactLayout tm.base.M tm.stateList tm.letterList
    ((pairBits x []).map some) [some false, some true] (tapeSymbols [true])
    certificateBound W T tm.stateList_nodup tm.letterList_nodup
    (fun a _ => hmem a) (hmem none) c

/-- The compact descriptor CNF at an explicit window stays inside the range
`execPairGenerateBoundedVerifierCNFAtWindow_vars` certifies, whenever the window still
accommodates the fixed prefix and the free certificate cells. -/
lemma descTableauCNF_pair_generate_vars_at_window (tm : ExecutableTableauAux) (x : List Bool)
    (cb T W : ℕ) (hspan : T + (pairBits x []).length + cb < W) :
    ClausesVarsSat (LayoutVarIn execCompactLayout (tm.stateList.length + 1) W
        (tm.letterList.length + 1))
      (descTableauCNF execCompactLayout (descriptorOf tm.base.M tm.stateList tm.letterList)
        (((pairBits x []).map some).map (execLetterIdx tm.letterList)) cb
        (([some false, some true] : List (Option Bool)).map (execLetterIdx tm.letterList))
        ((tapeSymbols [true] : List (Option Bool)).map (execLetterIdx tm.letterList))
        W T).clauses :=
  fun c hc l hl =>
    execPairGenerateBoundedVerifierCNFAtWindow_vars (executableTableauMachineOf tm) x cb T W hspan c
      ((descTableauCNF_pair_generate_mem_at_window tm x cb T W c).mp hc) l hl

/-! ## The target a RAM producer has to hit

`inNP_has_reduction_of_sat_equivalent_map` accepts any satisfiability-equivalent
CNF in place of `boundedCookLevinCNFMap`, so these two lemmas pin down exactly
what the producer must emit: the descriptor-driven family at a window no smaller than the
generator's own tight `windowSize`, with the generator's prefix and output.  Nothing below mentions the machine's state type or
its transition function. -/

/-- The descriptor-driven family at an explicit window is satisfiability-equivalent to the
compacted generator at that window. -/
lemma descTableauCNF_compact_sat_iff_at_window (tm : ExecutableTableauAux) (x : List Bool)
    (cb T W : ℕ) :
    SAT (descTableauCNF execCompactLayout
          (descriptorOf tm.base.M tm.stateList tm.letterList)
          (((pairBits x []).map some).map (execLetterIdx tm.letterList)) cb
          (([some false, some true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          ((tapeSymbols [true] : List (Option Bool)).map (execLetterIdx tm.letterList))
          W T) ↔
      SAT (compactCNF (generateBoundedVerifierCNFAtWindow tm.base x cb T W)) := by
  rw [compactCNF_sat_iff, ← execGenerateBoundedVerifierCNFAtWindow_eq tm,
    ← execPairGenerateBoundedVerifierCNFAtWindow_sat_iff]
  exact descTableauCNF_pair_generate_at_window tm x cb T W

/-- The descriptor-driven family at any window at least as large as the generator's own tight
`windowSize` is satisfiability-equivalent to `boundedCookLevinCNFMap`. -/
lemma descTableauCNF_boundedCookLevinCNFMap_sat_iff_at_window {α : Type}
    (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      Computability.encodeBool (fun xw => V xw.1 xw.2)) (x : α) (W : ℕ)
    (hW : windowSize ((pairBits (enc x) []).length + boundedCertificateBound enc p x)
        (tapeSymbols [true] : List (Option Bool)).length
        (boundedVerifierTimeBound enc p hV x) ≤ W) :
    SAT (descTableauCNF execCompactLayout
          (descriptorOf hV.toTM0ComputableAux.M
            (executableTableauAuxOf hV.toTM0ComputableAux).stateList
            (executableTableauAuxOf hV.toTM0ComputableAux).letterList)
          (((pairBits (enc x) []).map some).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          (boundedCertificateBound enc p x)
          (([some false, some true] : List (Option Bool)).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          ((tapeSymbols [true] : List (Option Bool)).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          W (boundedVerifierTimeBound enc p hV x)) ↔
      SAT (boundedCookLevinCNFMap enc p hV x) := by
  have h1 := descTableauCNF_compact_sat_iff_at_window
    (executableTableauAuxOf hV.toTM0ComputableAux) (enc x)
    (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x) W
  have h2 : SAT (compactCNF (generateBoundedVerifierCNFAtWindow hV.toTM0ComputableAux (enc x)
      (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x) W)) ↔
      SAT (boundedCookLevinCNFMap enc p hV x) := by
    rw [compactCNF_sat_iff, generateBoundedVerifierCNFAtWindow_sat_iff _ _ _ _ _ hW,
      show boundedCookLevinCNFMap enc p hV x =
        compactCNF (generateBoundedVerifierCNF hV.toTM0ComputableAux (enc x)
          (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x)) from rfl,
      compactCNF_sat_iff]
    exact (generateBoundedVerifierCNF_sat_iff hV.toTM0ComputableAux (enc x)
      (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x)).symm
  exact h1.trans h2

/-! ## Reaching the dense layout

`descTableauCNF_denseOfCompact` turns the range certificate above into a CNF
equality, so `sat_denseOfCompact_of_range` transports along it directly: a
producer emitting `denseLayout` numbers lands on a CNF that is
satisfiability-equivalent to the whole chain proved above, all the way to
`boundedCookLevinCNFMap`. This establishes that the dense layout preserves satisfiability across
the Cook-Levin reduction chain. -/

/-- The dense-layout descriptor CNF is satisfiability-equivalent to the
compact one, given the same range certificate `sat_denseOfCompact_of_range`
already asks for. Parametric in `n`/`W`/`mLet`/`T`/`d`, the three index lists, and `freeLen`, so
any call site of `descTableauCNF` can reuse it once it has its own range
certificate. -/
lemma descTableauCNF_dense_sat_iff {n W mLet T : ℕ} {d : TableauDescriptor}
    {prefIdx : List ℕ} {freeLen : ℕ} {allowedIdx outIdx : List ℕ}
    (hrange : ClausesVarsSat (LayoutVarIn execCompactLayout n W mLet)
      (descTableauCNF execCompactLayout d prefIdx freeLen allowedIdx outIdx W T).clauses) :
    SAT (descTableauCNF (denseLayout n W mLet) d prefIdx freeLen allowedIdx outIdx W T) ↔
      SAT (descTableauCNF execCompactLayout d prefIdx freeLen allowedIdx outIdx W T) := by
  have hCNF : descTableauCNF (denseLayout n W mLet) d prefIdx freeLen allowedIdx outIdx W T
      = ⟨execMapClauses (denseOfCompact n W mLet)
          (descTableauCNF execCompactLayout d prefIdx freeLen allowedIdx outIdx W T).clauses⟩ := by
    rw [descTableauCNF_denseOfCompact]
  rw [hCNF]
  exact sat_denseOfCompact_of_range hrange

/-- The dense-layout descriptor CNF at any window `W` at least as large as the generator's own
tight `windowSize` is satisfiability-equivalent to `boundedCookLevinCNFMap`: the range certificate
`descTableauCNF_pair_generate_vars_at_window` moves it to the compact layout, and
`descTableauCNF_boundedCookLevinCNFMap_sat_iff_at_window` finishes. -/
lemma descTableauCNF_dense_boundedCookLevinCNFMap_sat_iff_at_window {α : Type}
    (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      Computability.encodeBool (fun xw => V xw.1 xw.2)) (x : α) (W : ℕ)
    (hW : windowSize ((pairBits (enc x) []).length + boundedCertificateBound enc p x)
        (tapeSymbols [true] : List (Option Bool)).length
        (boundedVerifierTimeBound enc p hV x) ≤ W) :
    SAT (descTableauCNF
          (denseLayout ((executableTableauAuxOf hV.toTM0ComputableAux).stateList.length + 1)
            W
            ((executableTableauAuxOf hV.toTM0ComputableAux).letterList.length + 1))
          (descriptorOf hV.toTM0ComputableAux.M
            (executableTableauAuxOf hV.toTM0ComputableAux).stateList
            (executableTableauAuxOf hV.toTM0ComputableAux).letterList)
          (((pairBits (enc x) []).map some).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          (boundedCertificateBound enc p x)
          (([some false, some true] : List (Option Bool)).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          ((tapeSymbols [true] : List (Option Bool)).map
            (execLetterIdx (executableTableauAuxOf hV.toTM0ComputableAux).letterList))
          W
          (boundedVerifierTimeBound enc p hV x)) ↔
      SAT (boundedCookLevinCNFMap enc p hV x) := by
  have hspan : boundedVerifierTimeBound enc p hV x +
      (pairBits (enc x) []).length + boundedCertificateBound enc p x < W :=
    lt_of_lt_of_le (init_bound_of_windowSize (pairBits (enc x) []).length
      (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x)) hW
  exact Iff.trans (descTableauCNF_dense_sat_iff
      (descTableauCNF_pair_generate_vars_at_window (executableTableauAuxOf hV.toTM0ComputableAux)
        (enc x) (boundedCertificateBound enc p x) (boundedVerifierTimeBound enc p hV x) W hspan))
    (descTableauCNF_boundedCookLevinCNFMap_sat_iff_at_window enc p hV x W hW)

end NPComplete.CookLevin

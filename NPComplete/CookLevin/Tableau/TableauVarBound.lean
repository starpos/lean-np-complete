module

public import NPComplete.CookLevin.ReductionProg.OutputLengthBound
public import NPComplete.CookLevin.Tableau.TableauVarRange

/-!
`encodeCNF_length_le` bounds the encoded output by the clause count, the
widest clause and the largest occurring variable.  The clause count is already
a closed formula (`descTableauCNF_length`); this module supplies the other two
inputs for `descTableauCNF` at the dense layout, so the output-length bound can
be instantiated on the tableau compiler's own generator.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Turing.TM0
open NPComplete.SAT

/-! ## Variable bound

`LayoutVarIn` leaves the time index `t` unconstrained, which is exactly right
for the compact layout (its blocks are `Nat.pair`-spread and do not tile
`ℕ`), but the dense layout's blocks do tile `ℕ`, so a variable bound needs the
occurring `t` capped at `T` as well.  `DenseVarIn` adds that cap; every family
already iterates `t` over `range T` or `range (T + 1)` or fixes it at a
literal `≤ T` value, so threading the cap through is the same case split as
`TableauVarRange.lean`'s certificates, just against `denseLayout` instead of
an arbitrary layout. -/

/-- A dense-layout variable with all three indices in range and the time step
capped at `T`. -/
def DenseVarIn (n W m T x : ℕ) : Prop :=
  (∃ t q, t ≤ T ∧ q < n ∧ x = (denseLayout n W m).state t q) ∨
  (∃ t p, t ≤ T ∧ p < W ∧ x = (denseLayout n W m).head t p) ∨
  (∃ t p a, t ≤ T ∧ p < W ∧ a < m ∧ x = (denseLayout n W m).cell t p a)

/-- Every dense block below the cap stays below the `(T + 1)`-th block
boundary; each of the three index kinds is an offset less than one block. -/
lemma denseVarIn_lt {n W m T x : ℕ} (h : DenseVarIn n W m T x) :
    x < (T + 1) * denseBlock n W m := by
  rcases h with ⟨t, q, ht, hq, rfl⟩ | ⟨t, p, ht, hp, rfl⟩ | ⟨t, p, a, ht, hp, ha, rfl⟩
  · have h1 : t * denseBlock n W m + q < (t + 1) * denseBlock n W m := by
      unfold denseBlock; nlinarith
    calc t * denseBlock n W m + q < (t + 1) * denseBlock n W m := h1
      _ ≤ (T + 1) * denseBlock n W m := Nat.mul_le_mul_right _ (by omega)
  · rw [denseLayout_head_eq]
    have h1 : t * denseBlock n W m + (n + p) < (t + 1) * denseBlock n W m := by
      unfold denseBlock; nlinarith
    calc t * denseBlock n W m + (n + p) < (t + 1) * denseBlock n W m := h1
      _ ≤ (T + 1) * denseBlock n W m := Nat.mul_le_mul_right _ (by omega)
  · rw [denseLayout_cell_eq]
    have hoff : p * m + a < W * m := cell_offset_lt hp ha
    have h1 : t * denseBlock n W m + (n + W + (p * m + a)) < (t + 1) * denseBlock n W m := by
      unfold denseBlock; nlinarith
    calc t * denseBlock n W m + (n + W + (p * m + a)) < (t + 1) * denseBlock n W m := h1
      _ ≤ (T + 1) * denseBlock n W m := Nat.mul_le_mul_right _ (by omega)

/-- `natInitSymbol` falls back to `blank` outside the list, so it stays inside
whatever bound covers both the list's entries and the blank. -/
lemma natInitSymbol_lt {blank mLet : ℕ} {xs : List ℕ} (hblank : blank < mLet)
    (hxs : ∀ a ∈ xs, a < mLet) (p : ℤ) :
    natInitSymbol blank xs p < mLet := by
  unfold natInitSymbol
  split
  · rw [List.getD_eq_getElem?_getD]
    cases h : xs[p.toNat]? with
    | none => simpa using hblank
    | some x =>
        simp only [Option.getD_some]
        exact hxs x (List.mem_of_getElem? h)
  · exact hblank

/-! ### Per-family certificates against the dense layout, time-capped at `T`

Each proof mirrors its `TableauVarRange.lean` counterpart against
`LayoutVarIn`, with the extra `t ≤ T` witness read off the same `range`
membership the family already establishes. -/

/-- Range certificate for one padded transition cell: the successor indices
`natTransClausesPadded` may emit are `qi` unchanged, `qi'` from a `.write`/
`.move` guarded by `qi' < nCheck`, and `bi` from a `.write` bounded by the
`hbi` hypothesis — exactly `natTransClausesOf_vars`'s shape, with `t` capped
by `t + 1 ≤ T` instead of left free. -/
lemma natTransClausesPadded_vars {n W mLet T nCheck t p qi ai : ℕ} {e : NatTrans}
    (hnCheck : nCheck ≤ n) (ht : t + 1 ≤ T) (hqi : qi < n) (hai : ai < mLet) (hp : p < W)
    (hbi : ∀ qi' bi, e = .write qi' bi → bi < mLet) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (natTransClausesPadded (denseLayout n W mLet) nCheck W t p qi ai e) := by
  have ht0 : t ≤ T := by omega
  have hst : DenseVarIn n W mLet T ((denseLayout n W mLet).state t qi) :=
    Or.inl ⟨t, qi, ht0, hqi, rfl⟩
  have hhd : DenseVarIn n W mLet T ((denseLayout n W mLet).head t p) :=
    Or.inr (Or.inl ⟨t, p, ht0, hp, rfl⟩)
  have hcl : DenseVarIn n W mLet T ((denseLayout n W mLet).cell t p ai) :=
    Or.inr (Or.inr ⟨t, p, ai, ht0, hp, hai, rfl⟩)
  cases e with
  | halt =>
      have hst1 : DenseVarIn n W mLet T ((denseLayout n W mLet).state (t + 1) qi) :=
        Or.inl ⟨t + 1, qi, ht, hqi, rfl⟩
      have hhd1 : DenseVarIn n W mLet T ((denseLayout n W mLet).head (t + 1) p) :=
        Or.inr (Or.inl ⟨t + 1, p, ht, hp, rfl⟩)
      have hcl1 : DenseVarIn n W mLet T ((denseLayout n W mLet).cell (t + 1) p ai) :=
        Or.inr (Or.inr ⟨t + 1, p, ai, ht, hp, hai, rfl⟩)
      simp only [natTransClausesPadded]
      exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
        (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
          (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
  | write qi' bi =>
      have hbi' := hbi qi' bi rfl
      simp only [natTransClausesPadded]
      split
      · rename_i hqi'
        have hqi'n : qi' < n := lt_of_lt_of_le hqi' hnCheck
        have hst1 : DenseVarIn n W mLet T ((denseLayout n W mLet).state (t + 1) qi') :=
          Or.inl ⟨t + 1, qi', ht, hqi'n, rfl⟩
        have hhd1 : DenseVarIn n W mLet T ((denseLayout n W mLet).head (t + 1) p) :=
          Or.inr (Or.inl ⟨t + 1, p, ht, hp, rfl⟩)
        have hcl1 : DenseVarIn n W mLet T ((denseLayout n W mLet).cell (t + 1) p bi) :=
          Or.inr (Or.inr ⟨t + 1, p, bi, ht, hp, hbi', rfl⟩)
        exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
          (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
            (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
      · exact clausesVarsSat_cons (forbid3_vars hst hhd hcl)
          (clausesVarsSat_cons (forbid3_vars hst hhd hcl)
            (clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil))
  | move qi' d =>
      simp only [natTransClausesPadded]
      split
      · rename_i hqi'
        have hqi'n : qi' < n := lt_of_lt_of_le hqi' hnCheck
        cases hnext : nextIdx W p d with
        | none =>
            exact clausesVarsSat_cons (forbid3_vars hst hhd hcl)
              (clausesVarsSat_cons (forbid3_vars hst hhd hcl)
                (clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil))
        | some p' =>
            have hp' := nextIdx_lt hp hnext
            have hst1 : DenseVarIn n W mLet T ((denseLayout n W mLet).state (t + 1) qi') :=
              Or.inl ⟨t + 1, qi', ht, hqi'n, rfl⟩
            have hhd1 : DenseVarIn n W mLet T ((denseLayout n W mLet).head (t + 1) p') :=
              Or.inr (Or.inl ⟨t + 1, p', ht, hp', rfl⟩)
            have hcl1 : DenseVarIn n W mLet T ((denseLayout n W mLet).cell (t + 1) p ai) :=
              Or.inr (Or.inr ⟨t + 1, p, ai, ht, hp, hai, rfl⟩)
            exact clausesVarsSat_cons (imply3_vars hst hhd hcl hst1)
              (clausesVarsSat_cons (imply3_vars hst hhd hcl hhd1)
                (clausesVarsSat_cons (imply3_vars hst hhd hcl hcl1) clausesVarsSat_nil))
      · exact clausesVarsSat_cons (forbid3_vars hst hhd hcl)
          (clausesVarsSat_cons (forbid3_vars hst hhd hcl)
            (clausesVarsSat_cons (forbid3_vars hst hhd hcl) clausesVarsSat_nil))

/-- Range certificate for `descTransClauses`: `t` ranges over `range T`, so
`t + 1 ≤ T` for every iteration, and each cell's `qi`/`ai` are bounded by the
descriptor's own dimensions before being widened to `n`/`mLet`. -/
lemma descTransClauses_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (hn : d.numStates ≤ n) (hm : d.numLetters ≤ mLet)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < mLet) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descTransClauses (denseLayout n W mLet) d W T) := by
  unfold descTransClauses
  apply clausesVarsSat_flatMap
  intro t ht
  have ht' : t + 1 ≤ T := List.mem_range.mp ht
  apply clausesVarsSat_flatMap
  intro p hp
  have hpW : p < W := List.mem_range.mp hp
  apply clausesVarsSat_flatMap
  intro qi hqi
  have hqin : qi < n := lt_of_lt_of_le (List.mem_range.mp hqi) hn
  apply clausesVarsSat_flatMap
  intro ai hai
  have hain : ai < mLet := lt_of_lt_of_le (List.mem_range.mp hai) hm
  exact natTransClausesPadded_vars hn ht' hqin hain hpW (fun qi' bi h => hwrite qi ai qi' bi h)

/-- Range certificate for `descUniquenessClauses`: `t` ranges over
`range (T + 1)`, i.e. `t ≤ T`, and the state/letter ranges are bounded by the
descriptor's own dimensions. -/
lemma descUniquenessClauses_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (hn : d.numStates ≤ n) (hm : d.numLetters ≤ mLet) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descUniquenessClauses (denseLayout n W mLet) d W T) := by
  unfold descUniquenessClauses execUniquenessClausesAt
  apply clausesVarsSat_flatMap
  intro t ht
  have ht' : t ≤ T := by have := List.mem_range.mp ht; omega
  apply clausesVarsSat_append
  apply clausesVarsSat_append
  · apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact Or.inl ⟨t, q, ht', lt_of_lt_of_le (List.mem_range.mp hq) hn, rfl⟩
  · apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Or.inr (Or.inl ⟨t, p, ht', List.mem_range.mp hp, rfl⟩)
  · apply clausesVarsSat_flatMap
    intro p hp
    apply clausesVarsSat_exactlyOne
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inr (Or.inr ⟨t, p, a, ht', List.mem_range.mp hp,
      lt_of_lt_of_le (List.mem_range.mp ha) hm, rfl⟩)

/-- Range certificate for `descPersistClauses`: `t` ranges over `range T`, so
both `t` and `t + 1` stay `≤ T`. -/
lemma descPersistClauses_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (hm : d.numLetters ≤ mLet) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descPersistClauses (denseLayout n W mLet) d W T) := by
  unfold descPersistClauses execPersistClausesAt
  apply clausesVarsSat_flatMap
  intro t ht
  have ht' : t < T := List.mem_range.mp ht
  apply clausesVarsSat_flatMap
  intro pHead hpHead
  have hpHead' : pHead < W := List.mem_range.mp hpHead
  apply clausesVarsSat_flatMap
  intro pCell hpCell
  have hpCell' : pCell < W := List.mem_range.mp hpCell
  split
  · exact clausesVarsSat_nil
  · intro c hc l hl
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    have ha' : a < mLet := lt_of_lt_of_le (List.mem_range.mp ha) hm
    exact imply2_vars
      (Or.inr (Or.inl ⟨t, pHead, by omega, hpHead', rfl⟩))
      (Or.inr (Or.inr ⟨t, pCell, a, by omega, hpCell', ha', rfl⟩))
      (Or.inr (Or.inr ⟨t + 1, pCell, a, by omega, hpCell', ha', rfl⟩)) l hl

/-- Range certificate for `descAcceptClauses`: every clause is stated at the
literal time index `T`, and the state indices come from `descHaltStates`,
which filters `range d.numStates`. -/
lemma descAcceptClauses_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (outIdx : List ℕ) (hn : d.numStates ≤ n)
    (hblank : d.blankIdx < mLet) (hout : ∀ a ∈ outIdx, a < mLet) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descAcceptClauses (denseLayout n W mLet) d outIdx W T) := by
  apply clausesVarsSat_append
  · apply clausesVarsSat_flatMap
    intro pHead hpHead
    have hpHead' : pHead < W := List.mem_range.mp hpHead
    intro c hc l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hp' : p < W := List.mem_range.mp hp
    have hai : natInitSymbol d.blankIdx outIdx ((p : ℤ) - (pHead : ℤ)) < mLet :=
      natInitSymbol_lt hblank hout _
    exact implyPos_vars
      (Or.inr (Or.inl ⟨T, pHead, le_refl _, hpHead', rfl⟩))
      (Or.inr (Or.inr ⟨T, p, _, le_refl _, hp', hai, rfl⟩)) l hl
  · exact clausesVarsSat_cons
      (clausesVarsSat_atLeastOne (fun x hx => by
        obtain ⟨qi, hqi, rfl⟩ := List.mem_map.mp hx
        unfold descHaltStates at hqi
        have hqin : qi < n := lt_of_lt_of_le (List.mem_range.mp (List.mem_filter.mp hqi).1) hn
        exact Or.inl ⟨T, qi, le_refl _, hqin, rfl⟩))
      clausesVarsSat_nil

/-- Range certificate for `descBoundedPrefixInitClauses`: every clause is
stated at time `0`, and the window bound `hbound` (matching how call sites
choose `W`, c.f. `init_bound_of_windowSize`) keeps the free-suffix indices
inside `range W`. -/
lemma descBoundedPrefixInitClauses_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx : List ℕ)
    (hn : d.numStates ≤ n) (hblank : d.blankIdx < mLet)
    (hpref : ∀ a ∈ prefIdx, a < mLet) (hallowed : ∀ a ∈ allowedIdx, a < mLet)
    (hbound : T + prefIdx.length + freeLen < W) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descBoundedPrefixInitClauses (denseLayout n W mLet) d prefIdx freeLen allowedIdx W T) := by
  have hT0 : (0 : ℕ) ≤ T := Nat.zero_le T
  unfold descBoundedPrefixInitClauses
  apply clausesVarsSat_append
  · apply clausesVarsSat_cons
    · intro l hl
      unfold descInitStateClause at hl
      split at hl
      · rename_i hlt
        simp [unitPos] at hl
        subst hl
        exact Or.inl ⟨0, d.startState, hT0, lt_of_lt_of_le hlt hn, rfl⟩
      · simp at hl
    · apply clausesVarsSat_cons
      · refine unitPos_vars (Or.inr (Or.inl ⟨0, originIdx T, hT0, ?_, rfl⟩))
        unfold originIdx; omega
      · intro c hc l hl
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        have hpW : p < W := List.mem_range.mp hp
        split at hl
        · have hai : natInitSymbol d.blankIdx prefIdx (idxToPos T p) < mLet :=
            natInitSymbol_lt hblank hpref _
          exact unitPos_vars (Or.inr (Or.inr ⟨0, p, _, hT0, hpW, hai, rfl⟩)) l hl
        · split at hl
          · simp only [atLeastOne, List.map_map] at hl
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
            simp only [List.mem_cons] at ha
            have hai : a < mLet := by
              rcases ha with rfl | ha
              · exact hblank
              · exact hallowed a ha
            exact Or.inr (Or.inr ⟨0, p, a, hT0, hpW, hai, rfl⟩)
          · exact unitPos_vars (Or.inr (Or.inr ⟨0, p, d.blankIdx, hT0, hpW, hblank, rfl⟩)) l hl
  · intro c hc l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hiF : i < freeLen := List.mem_range.mp hi
    exact implyPos_vars
      (Or.inr (Or.inr ⟨0, T + prefIdx.length + i, d.blankIdx, hT0, by omega, hblank, rfl⟩))
      (Or.inr (Or.inr ⟨0, T + prefIdx.length + i + 1, d.blankIdx, hT0, by omega, hblank, rfl⟩))
      l hl

/-- Range certificate for the whole generator: the five families are joined
by `++`, so their certificates combine with `clausesVarsSat_append`. -/
lemma descTableauCNF_vars {n W mLet T : ℕ} (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ)
    (hn : d.numStates ≤ n) (hm : d.numLetters ≤ mLet)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < mLet)
    (hblank : d.blankIdx < mLet) (hpref : ∀ a ∈ prefIdx, a < mLet)
    (hallowed : ∀ a ∈ allowedIdx, a < mLet) (hout : ∀ a ∈ outIdx, a < mLet)
    (hbound : T + prefIdx.length + freeLen < W) :
    ClausesVarsSat (DenseVarIn n W mLet T)
      (descTableauCNF (denseLayout n W mLet) d prefIdx freeLen allowedIdx outIdx W T).clauses := by
  unfold descTableauCNF
  simp only []
  refine clausesVarsSat_append (clausesVarsSat_append (clausesVarsSat_append
    (clausesVarsSat_append ?_ ?_) ?_) ?_) ?_
  · exact descUniquenessClauses_vars d hn hm
  · exact descBoundedPrefixInitClauses_vars d prefIdx freeLen allowedIdx hn hblank hpref hallowed
      hbound
  · exact descTransClauses_vars d hn hm hwrite
  · exact descPersistClauses_vars d hm
  · exact descAcceptClauses_vars d outIdx hn hblank hout

/-- Under the stated width and symbol bounds, every variable in the dense-layout
CNF is below `(T + 1) * (n + W + W * mLet)`, one block per time step through `T`. -/
lemma descTableauCNF_var_le (n W mLet T : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ)
    (hn : d.numStates ≤ n) (hm : d.numLetters ≤ mLet)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < mLet)
    (hblank : d.blankIdx < mLet) (hpref : ∀ a ∈ prefIdx, a < mLet)
    (hallowed : ∀ a ∈ allowedIdx, a < mLet) (hout : ∀ a ∈ outIdx, a < mLet)
    (hbound : T + prefIdx.length + freeLen < W) :
    ∀ c ∈ (descTableauCNF (denseLayout n W mLet) d prefIdx freeLen allowedIdx outIdx W T).clauses,
      ∀ l ∈ c.lits, litVar l < (T + 1) * (n + W + W * mLet) := by
  have hvars := descTableauCNF_vars d prefIdx freeLen allowedIdx outIdx hn hm hwrite hblank hpref
    hallowed hout hbound
  intro c hc l hl
  show l.var < (T + 1) * (n + W + W * mLet)
  have := denseVarIn_lt (hvars c hc l hl)
  unfold denseBlock at this
  exact this

/-! ## Clause width bound

The clauses use a fixed set of constructors, and each family uses only a subset.
Its width is bounded by the largest constructor width or by the list length
required for a one-of-many constraint. Combining these bounds gives the nested
maximum below rather than a sum of the per-family maxima. -/

/-- `(atLeastOne vs) :: atMostOne vs` reproduces `vs` once and then pairs it
with itself, so its width is exactly `vs.length`. -/
lemma atLeastOne_lits_length (vs : List ℕ) : (atLeastOne vs).lits.length = vs.length := by
  simp [atLeastOne]

/-- Range certificate for `descUniquenessClauses`'s width: every `exactlyOne`
call is over an index list of length `d.numStates`, `W` or `d.numLetters`. -/
lemma descUniquenessClauses_width_le (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ)
    {c : Clause} (hc : c ∈ descUniquenessClauses v d W T) :
    c.lits.length ≤ max (max d.numStates W) d.numLetters + 2 := by
  unfold descUniquenessClauses execUniquenessClausesAt at hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨t, _, hc⟩ := hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · have h := exactlyOne_clause_lits_length_le
      ((List.range d.numStates).map fun q => v.state t q) hc
    simp only [List.length_map, List.length_range] at h
    omega
  · have h := exactlyOne_clause_lits_length_le ((List.range W).map fun p => v.head t p) hc
    simp only [List.length_map, List.length_range] at h
    omega
  · simp only [List.mem_flatMap] at hc
    obtain ⟨p, _, hc⟩ := hc
    have h := exactlyOne_clause_lits_length_le
      ((List.range d.numLetters).map fun a => v.cell t p a) hc
    simp only [List.length_map, List.length_range] at h
    omega

/-- The transition cell emits three clauses, each an implication or prohibition
    clause with at most four literals. -/
lemma natTransClausesPadded_width_le (v : ExecVarLayout) (n W t p qi ai : ℕ) (e : NatTrans)
    {c : Clause} (hc : c ∈ natTransClausesPadded v n W t p qi ai e) : c.lits.length ≤ 4 := by
  cases e with
  | halt =>
      simp only [natTransClausesPadded, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [imply3]
  | write qi' bi =>
      simp only [natTransClausesPadded] at hc
      split at hc <;>
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> simp [imply3, forbid3]
  | move qi' d =>
      simp only [natTransClausesPadded] at hc
      split at hc
      · split at hc <;>
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl <;> simp [imply3, forbid3]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [forbid3]

/-- Range certificate for `descTransClauses`'s width: every cell reduces to
`natTransClausesPadded`'s own bound. -/
lemma descTransClauses_width_le (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ)
    {c : Clause} (hc : c ∈ descTransClauses v d W T) :
    c.lits.length ≤ 4 := by
  unfold descTransClauses at hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨t, _, p, _, qi, _, ai, _, hc⟩ := hc
  exact natTransClausesPadded_width_le v d.numStates W t p qi ai (d.entry qi ai) hc

/-- Every clause `descPersistClauses` emits is an `imply2`. -/
lemma descPersistClauses_width_le (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ)
    {c : Clause} (hc : c ∈ descPersistClauses v d W T) :
    c.lits.length ≤ 3 := by
  unfold descPersistClauses execPersistClausesAt at hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨t, _, pHead, _, pCell, _, hc⟩ := hc
  split at hc
  · simp at hc
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    simp [imply2]

/-- `descHaltStates` filters `range d.numStates`, so it never grows past it. -/
lemma descHaltStates_length_le (d : TableauDescriptor) (ai : ℕ) :
    (descHaltStates d ai).length ≤ d.numStates := by
  unfold descHaltStates
  calc _ ≤ (List.range d.numStates).length := List.length_filter_le _ _
    _ = d.numStates := List.length_range

/-- Range certificate for `descAcceptClauses`'s width: the `implyPos` clauses
have width two, and the single `atLeastOne` clause is over `descHaltStates`,
bounded above by `descHaltStates_length_le`. -/
lemma descAcceptClauses_width_le (v : ExecVarLayout) (d : TableauDescriptor)
    (outIdx : List ℕ) (W T : ℕ) {c : Clause}
    (hc : c ∈ descAcceptClauses v d outIdx W T) :
    c.lits.length ≤ max 2 d.numStates := by
  unfold descAcceptClauses at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [List.mem_flatMap] at hc
    obtain ⟨pHead, _, hc⟩ := hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    have hlen : (implyPos (v.head T pHead)
        (v.cell T p (natInitSymbol d.blankIdx outIdx ((p : ℤ) - (pHead : ℤ))))).lits.length
        = 2 := rfl
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    have h := descHaltStates_length_le d (natInitSymbol d.blankIdx outIdx 0)
    have hlen : (atLeastOne ((descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).map
        fun qi => v.state T qi)).lits.length
        = (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length := by
      rw [atLeastOne_lits_length, List.length_map]
    omega

/-- Range certificate for `descBoundedPrefixInitClauses`'s width: the state
and head clauses are `unitPos` (width one), the window cells are `unitPos` or
the `atLeastOne` over `d.blankIdx :: allowedIdx` (width `1 + allowedIdx.length`),
and the free-suffix clauses are `implyPos` (width two). -/
lemma descBoundedPrefixInitClauses_width_le (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx : List ℕ) (W T : ℕ) {c : Clause}
    (hc : c ∈ descBoundedPrefixInitClauses v d prefIdx freeLen allowedIdx W T) :
    c.lits.length ≤ max 2 (1 + allowedIdx.length) := by
  unfold descBoundedPrefixInitClauses at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · unfold descInitStateClause
      split <;> simp [unitPos]
    · simp [unitPos]
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
      split
      · simp [unitPos]
      · split
        · have : (atLeastOne ((d.blankIdx :: allowedIdx).map fun a => v.cell 0 p a)).lits.length
              = (d.blankIdx :: allowedIdx).length := by
            rw [atLeastOne_lits_length, List.length_map]
          simp only [List.length_cons] at this
          omega
        · simp [unitPos]
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp [implyPos]

/-- Every clause `descTableauCNF` emits is at most as wide as the widest of
the five families: `exactlyOne` over `d.numStates`/`W`/`d.numLetters` (plus
two, for `atLeastOne` and its own successor bound), the padded transition
family's fixed width four, the window's `atLeastOne` over
`d.blankIdx :: allowedIdx`, or the accept family's `descHaltStates` bound. -/
lemma descTableauCNF_width_le (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) (W T : ℕ) :
    ∀ c ∈ (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses,
      c.lits.length ≤
        max (max (max d.numStates W) d.numLetters + 2) (max (1 + allowedIdx.length) 4) := by
  intro c hc
  unfold descTableauCNF at hc
  simp only [List.mem_append] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · have := descUniquenessClauses_width_le v d W T hc
    omega
  · have := descBoundedPrefixInitClauses_width_le v d prefIdx freeLen allowedIdx W T hc
    omega
  · have := descTransClauses_width_le v d W T hc
    omega
  · have := descPersistClauses_width_le v d W T hc
    omega
  · have := descAcceptClauses_width_le v d outIdx W T hc
    omega

end NPComplete.CookLevin

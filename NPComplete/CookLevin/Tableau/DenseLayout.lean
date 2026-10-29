module

public import NPComplete.CookLevin.Tableau.NatTableau

/-!
`execCompactLayout`'s `Nat.pair` numbering is injective but spreads variables
far apart, so `compactCNF` is needed afterwards to keep the encoded length
polynomial — at the cost of a numbering that cannot be predicted before the
whole clause list is seen.  This module gives a dense, mixed-radix layout
instead, together with the round-trip maps to and from the compact layout, so
a generator can emit compact clause numbers as usual and transport the result
to the dense layout once it is known to be satisfiability-preserving.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Turing.TM0

/-- Satisfiability depends only on which clauses occur, not on multiplicity or
order.  Padding a clause family to a fixed width by repetition — needed because
`encodeList` writes its length prefix before any element — is therefore free. -/
lemma sat_of_clauses_mem_iff {φ ψ : CNF}
    (h : ∀ c, c ∈ ψ.clauses ↔ c ∈ φ.clauses) : SAT ψ ↔ SAT φ := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨τ, fun c hc => hτ c ((h c).mpr hc)⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ, fun c hc => hτ c ((h c).mp hc)⟩

/-! ## Renaming variables freely

`compactCNF` exists to keep `cnfVarBound` proportional to the number of
variables actually used, so the encoded length stays polynomial — not because
its particular numbering matters.  Its order comes from `List.dedup`, which
keeps the *last* occurrence, so a producer that reproduced it would have to see
the whole clause list before fixing any number.  A generator is free to pick its
own dense numbering instead, provided the renaming can be undone on the
variables that occur. -/

/-- Any renaming with a left inverse on the occurring variables preserves
satisfiability.  Unlike `compactCNF_sat_iff` this does not fix the numbering,
so a generator may emit whatever dense layout it finds convenient. -/
lemma execMapClauses_sat_iff (m inv : ℕ → ℕ) (φ : CNF)
    (hinv : ∀ c ∈ φ.clauses, ∀ l ∈ c.lits, inv (m l.var) = l.var) :
    SAT ⟨execMapClauses m φ.clauses⟩ ↔ SAT φ := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => τ (m v), ?_⟩
    intro c hc
    have hc' : execMapClause m c ∈ execMapClauses m φ.clauses :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    obtain ⟨l, hl, hev⟩ := hτ _ hc'
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp (by
      simpa [execMapClause] using hl)
    exact ⟨l', hl', by cases l' <;> simpa [execMapLiteral, NPComplete.SAT.Literal.eval]
      using hev⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => τ (inv i), ?_⟩
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨l, hl, hev⟩ := hτ _ hd
    refine ⟨execMapLiteral m l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    have hlv := hinv d hd l hl
    cases l with
    | pos v =>
        simp only [execMapLiteral, NPComplete.SAT.Literal.eval]
        rw [show inv (m v) = v from hlv]
        simpa [NPComplete.SAT.Literal.eval] using hev
    | neg v =>
        simp only [execMapLiteral, NPComplete.SAT.Literal.eval]
        rw [show inv (m v) = v from hlv]
        simpa [NPComplete.SAT.Literal.eval] using hev

/-! ## A dense variable layout

`execCompactLayout` numbers variables through `Nat.pair`, which is injective but
extremely sparse: the resulting bound can be far larger than the number of
variables that occur.  `compactCNF` repairs this after the fact, but its order
comes from `List.dedup` (last occurrence), so a producer cannot predict a number
before seeing the whole clause list.

A mixed-radix layout avoids the problem entirely: each time step owns a block of
`n` state, `W` head and `W * m` cell variables.  Only `+` and `*` are needed to
compute a number, and `/` and `%` recover the triple. -/

/-- Variables per time step. -/
def denseBlock (n W m : ℕ) : ℕ := n + W + W * m

/-- Mixed-radix layout: time step selects a block, kind selects a range inside it. -/
def denseLayout (n W m : ℕ) : ExecVarLayout where
  state t q := t * denseBlock n W m + q
  head t p := t * denseBlock n W m + n + p
  cell t p a := t * denseBlock n W m + n + W + (p * m + a)

lemma denseLayout_head_eq (n W m t p : ℕ) :
    (denseLayout n W m).head t p = t * denseBlock n W m + (n + p) := by
  unfold denseLayout; simp only []; ring

lemma denseLayout_cell_eq (n W m t p a : ℕ) :
    (denseLayout n W m).cell t p a
      = t * denseBlock n W m + (n + W + (p * m + a)) := by
  unfold denseLayout; simp only []; ring

/-- The cell offsets stay inside one block. -/
lemma cell_offset_lt {W m p a : ℕ} (hp : p < W) (ha : a < m) :
    p * m + a < W * m := by
  calc p * m + a < p * m + m := by omega
    _ = (p + 1) * m := by ring
    _ ≤ W * m := Nat.mul_le_mul_right m hp

/-- Splitting `t * B + r` with `r < B` recovers `t` and `r`. -/
lemma div_mod_block (B t r : ℕ) (hB : 0 < B) (hr : r < B) :
    (t * B + r) / B = t ∧ (t * B + r) % B = r := by
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-! ### Transporting between the compact and dense layouts -/

/-- Compact variable numbers (tagged `mod 3`, paired by `Nat.pair`) to dense ones. -/
def denseOfCompact (n W m : ℕ) (v : ℕ) : ℕ :=
  if v % 3 = 1 then
    let z := Nat.unpair (v / 3); (denseLayout n W m).state z.1 z.2
  else if v % 3 = 2 then
    let z := Nat.unpair (v / 3); (denseLayout n W m).head z.1 z.2
  else
    let z := Nat.unpair (v / 3)
    let y := Nat.unpair z.1
    (denseLayout n W m).cell y.1 y.2 z.2

lemma denseOfCompact_state (n W m t q : ℕ) :
    denseOfCompact n W m (execCompactLayout.state t q)
      = (denseLayout n W m).state t q := by
  unfold denseOfCompact execCompactLayout
  simp only []
  rw [ite_eq_left (by omega : (3 * execPair t q + 1) % 3 = 1)]
  simp only [execPair]
  rw [show (3 * Nat.pair t q + 1) / 3 = Nat.pair t q by omega, Nat.unpair_pair]

lemma denseOfCompact_head (n W m t p : ℕ) :
    denseOfCompact n W m (execCompactLayout.head t p)
      = (denseLayout n W m).head t p := by
  unfold denseOfCompact execCompactLayout
  simp only []
  rw [ite_eq_right (by omega : ¬ (3 * execPair t p + 2) % 3 = 1),
    ite_eq_left (by omega : (3 * execPair t p + 2) % 3 = 2)]
  simp only [execPair]
  rw [show (3 * Nat.pair t p + 2) / 3 = Nat.pair t p by omega, Nat.unpair_pair]

lemma denseOfCompact_cell (n W m t p a : ℕ) :
    denseOfCompact n W m (execCompactLayout.cell t p a)
      = (denseLayout n W m).cell t p a := by
  unfold denseOfCompact execCompactLayout
  simp only []
  rw [ite_eq_right (by omega : ¬ (3 * execPair (execPair t p) a) % 3 = 1),
    ite_eq_right (by omega : ¬ (3 * execPair (execPair t p) a) % 3 = 2)]
  simp only [execPair]
  rw [show (3 * Nat.pair (Nat.pair t p) a) / 3 = Nat.pair (Nat.pair t p) a by omega,
    Nat.unpair_pair, Nat.unpair_pair]

/-- Left inverse of `denseOfCompact` on in-range variables: split off the time
step, then classify the offset by which of the three ranges it lands in. -/
def compactOfDense (n W m : ℕ) (v : ℕ) : ℕ :=
  let t := v / denseBlock n W m
  let r := v % denseBlock n W m
  if r < n then execCompactLayout.state t r
  else if r < n + W then execCompactLayout.head t (r - n)
  else execCompactLayout.cell t ((r - (n + W)) / m) ((r - (n + W)) % m)

lemma compactOfDense_state {n W m t q : ℕ} (hq : q < n) :
    compactOfDense n W m ((denseLayout n W m).state t q)
      = execCompactLayout.state t q := by
  have hB : 0 < denseBlock n W m := by unfold denseBlock; omega
  have hr : q < denseBlock n W m := by unfold denseBlock; omega
  obtain ⟨hdiv, hmod⟩ := div_mod_block (denseBlock n W m) t q hB hr
  unfold compactOfDense
  simp only [denseLayout, hdiv, hmod]
  rw [ite_eq_left hq]

lemma compactOfDense_head {n W m t p : ℕ} (hp : p < W) :
    compactOfDense n W m ((denseLayout n W m).head t p)
      = execCompactLayout.head t p := by
  have hB : 0 < denseBlock n W m := by unfold denseBlock; omega
  have hr : n + p < denseBlock n W m := by unfold denseBlock; omega
  obtain ⟨hdiv, hmod⟩ := div_mod_block (denseBlock n W m) t (n + p) hB hr
  unfold compactOfDense
  simp only [denseLayout_head_eq, hdiv, hmod]
  have hsub : n + p - n = p := by omega
  rw [ite_eq_right (by omega : ¬ n + p < n), ite_eq_left (by omega : n + p < n + W), hsub]

lemma compactOfDense_cell {n W m t p a : ℕ} (hp : p < W) (ha : a < m) :
    compactOfDense n W m ((denseLayout n W m).cell t p a)
      = execCompactLayout.cell t p a := by
  have hpm : p * m + a < W * m := cell_offset_lt hp ha
  have hB : 0 < denseBlock n W m := by unfold denseBlock; omega
  have hr : n + W + (p * m + a) < denseBlock n W m := by unfold denseBlock; omega
  obtain ⟨hdiv, hmod⟩ := div_mod_block (denseBlock n W m) t (n + W + (p * m + a)) hB hr
  unfold compactOfDense
  simp only [denseLayout_cell_eq, hdiv, hmod]
  have hsub : n + W + (p * m + a) - (n + W) = p * m + a := by omega
  have hBm : 0 < m := by omega
  obtain ⟨hdiv2, hmod2⟩ := div_mod_block m p a hBm ha
  rw [ite_eq_right (by omega : ¬ n + W + (p * m + a) < n),
    ite_eq_right (by omega : ¬ n + W + (p * m + a) < n + W), hsub, hdiv2, hmod2]

/-- A variable is a layout value whose indices lie in the tableau's ranges.
The time step is unconstrained: the dense blocks tile all of `ℕ`, so only the
offset within a block has to be bounded. -/
def LayoutVarIn (v : ExecVarLayout) (n W m : ℕ) (x : ℕ) : Prop :=
  (∃ t q, q < n ∧ x = v.state t q) ∨
  (∃ t p, p < W ∧ x = v.head t p) ∨
  (∃ t p a, p < W ∧ a < m ∧ x = v.cell t p a)

/-- On in-range compact variables `compactOfDense` inverts `denseOfCompact`.
This is the hypothesis `execMapClauses_sat_iff` needs, so a generated CNF can be
transported to the dense layout once every occurring variable is known to be in
range. -/
lemma compactOfDense_denseOfCompact {n W m x : ℕ}
    (h : LayoutVarIn execCompactLayout n W m x) :
    compactOfDense n W m (denseOfCompact n W m x) = x := by
  rcases h with ⟨t, q, hq, rfl⟩ | ⟨t, p, hp, rfl⟩ | ⟨t, p, a, hp, ha, rfl⟩
  · rw [denseOfCompact_state, compactOfDense_state hq]
  · rw [denseOfCompact_head, compactOfDense_head hp]
  · rw [denseOfCompact_cell, compactOfDense_cell hp ha]

/-- The predicate only gets weaker as the index bounds grow.  The transition
family is naturally stated at `S.length`, while the families that go through
`List.idxOf` need `S.length + 1`; this reconciles them. -/
lemma layoutVarIn_mono {v : ExecVarLayout} {n n' W m m' x : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (h : LayoutVarIn v n W m x) :
    LayoutVarIn v n' W m' x := by
  rcases h with ⟨t, q, hq, rfl⟩ | ⟨t, p, hp, rfl⟩ | ⟨t, p, a, hp, ha, rfl⟩
  · exact Or.inl ⟨t, q, lt_of_lt_of_le hq hn, rfl⟩
  · exact Or.inr (Or.inl ⟨t, p, hp, rfl⟩)
  · exact Or.inr (Or.inr ⟨t, p, a, hp, lt_of_lt_of_le ha hm, rfl⟩)

/-! ## The whole generator, driven by the descriptor

All five families now consult nothing but the descriptor and `ℕ` index lists, so
the generator does too.  `W` is left free rather than recomputed from the input
lengths: `execTableauMachineWithInitAt` derives its own `W`, and keeping the
window a parameter here lets the call site supply whichever one it used. -/

def descTableauCNF (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ)
    (W T : ℕ) : CNF :=
  ⟨descUniquenessClauses v d W T ++
    descBoundedPrefixInitClauses v d prefIdx freeLen allowedIdx W T ++
    descTransClauses v d W T ++
    descPersistClauses v d W T ++
    descAcceptClauses v d outIdx W T⟩

/-- The RAM cost analysis needs an exact clause count, not just an upper
bound; doubled to match the doubled uniqueness count, which carries the only
`/2` among the five families. -/
lemma descTableauCNF_length (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) (W T : ℕ) :
    2 * (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses.length =
      (T + 1) * ((d.numStates * (d.numStates - 1) + 2) +
                 (W * (W - 1) + 2) +
                 W * (d.numLetters * (d.numLetters - 1) + 2)) +
      2 * (2 + W + freeLen) +
      2 * (T * W * d.numStates * d.numLetters * 3) +
      2 * (T * W * (W - 1) * d.numLetters) +
      2 * (W * W + 1) := by
  unfold descTableauCNF
  simp only [List.length_append]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [descUniquenessClauses_length, descBoundedPrefixInitClauses_length,
    descTransClauses_length, descPersistClauses_length, descAcceptClauses_length]

/-- Four of the five families match by equality; only the padded transition
family needs the clause-set reading, so the generator as a whole matches as a
set of clauses. -/
lemma descTableauCNF_mem {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (pref allowed output : List (Option Bool))
    (freeLen W T : ℕ) (hS : S.Nodup) (hA : A.Nodup)
    (hout : ∀ a ∈ output, a ∈ A) (hnone : (none : Option Bool) ∈ A) (c : Clause) :
    c ∈ (descTableauCNF v (descriptorOf M S A) (pref.map (execLetterIdx A)) freeLen
          (allowed.map (execLetterIdx A)) (output.map (execLetterIdx A)) W T).clauses ↔
      c ∈ (execUniquenessClausesAt v (S.map fun q => execStateIdx S q)
              (A.map fun a => execLetterIdx A a) W T ++
            execBoundedPrefixInitClausesAt v S A pref freeLen allowed none W T ++
            execTransClausesAt v M S A W T ++
            execPersistClausesAt v (A.map fun a => execLetterIdx A a) W T ++
            execAcceptClausesAt v M S A output W T) := by
  unfold descTableauCNF
  rw [descUniquenessClauses_eq v M S A W T hS hA,
    descBoundedPrefixInitClauses_eq v M S A pref freeLen allowed W T,
    descPersistClauses_eq v M S A W T hA,
    descAcceptClauses_eq v M S A output W T hS hout hnone]
  simp only [List.mem_append]
  rw [descTransClauses_mem v M S A W T hS hA c]

lemma descTableauCNF_sat_iff {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (pref allowed output : List (Option Bool))
    (freeLen W T : ℕ) (hS : S.Nodup) (hA : A.Nodup)
    (hout : ∀ a ∈ output, a ∈ A) (hnone : (none : Option Bool) ∈ A) :
    SAT (descTableauCNF v (descriptorOf M S A) (pref.map (execLetterIdx A)) freeLen
          (allowed.map (execLetterIdx A)) (output.map (execLetterIdx A)) W T) ↔
      SAT ⟨execUniquenessClausesAt v (S.map fun q => execStateIdx S q)
              (A.map fun a => execLetterIdx A a) W T ++
            execBoundedPrefixInitClausesAt v S A pref freeLen allowed none W T ++
            execTransClausesAt v M S A W T ++
            execPersistClausesAt v (A.map fun a => execLetterIdx A a) W T ++
            execAcceptClausesAt v M S A output W T⟩ :=
  sat_of_clauses_mem_iff
    (descTableauCNF_mem v M S A pref allowed output freeLen W T hS hA hout hnone)

/-! ## Renaming a descriptor-driven CNF to the dense layout

Each of the five families only ever emits the layout's own `state`/`head`/`cell`
values, so renaming through `denseOfCompact` and rebuilding the family at
`denseLayout` land on the same clause list — not merely an equivalent one.
Proving this per family, rather than appealing to `execMapClauses_sat_iff`
directly, is what lets a producer emit `denseLayout` numbers outright: the
equalities below are exactly `descTableauCNF_denseOfCompact`. -/

/-- `natTransClausesPadded` only ever writes `v.state`/`v.head`/`v.cell` at the
indices it was handed, so renaming commutes with rebuilding it at another
layout. -/
lemma natTransClausesPadded_denseOfCompact (n W mLet t p qi ai numStates : ℕ)
    (e : NatTrans) :
    execMapClauses (denseOfCompact n W mLet)
        (natTransClausesPadded execCompactLayout numStates W t p qi ai e)
      = natTransClausesPadded (denseLayout n W mLet) numStates W t p qi ai e := by
  cases e with
  | halt =>
      simp only [natTransClausesPadded, execMapClauses, List.map_cons, List.map_nil]
      simp [execMapClause_imply3, denseOfCompact_state, denseOfCompact_head,
        denseOfCompact_cell]
  | write qi' bi =>
      simp only [natTransClausesPadded]
      split
      · simp only [execMapClauses, List.map_cons, List.map_nil]
        simp [execMapClause_imply3, denseOfCompact_state, denseOfCompact_head,
          denseOfCompact_cell]
      · simp only [execMapClauses, List.map_cons, List.map_nil]
        simp [execMapClause_forbid3, denseOfCompact_state, denseOfCompact_head,
          denseOfCompact_cell]
  | move qi' d =>
      simp only [natTransClausesPadded]
      split
      · split
        · simp only [execMapClauses, List.map_cons, List.map_nil]
          simp [execMapClause_forbid3, denseOfCompact_state, denseOfCompact_head,
            denseOfCompact_cell]
        · simp only [execMapClauses, List.map_cons, List.map_nil]
          simp [execMapClause_imply3, denseOfCompact_state, denseOfCompact_head,
            denseOfCompact_cell]
      · simp only [execMapClauses, List.map_cons, List.map_nil]
        simp [execMapClause_forbid3, denseOfCompact_state, denseOfCompact_head,
          denseOfCompact_cell]

lemma descTransClauses_denseOfCompact (n W mLet T : ℕ) (dd : TableauDescriptor) :
    execMapClauses (denseOfCompact n W mLet) (descTransClauses execCompactLayout dd W T)
      = descTransClauses (denseLayout n W mLet) dd W T := by
  unfold descTransClauses
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro t _
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro p _
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro qi _
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro ai _
  exact natTransClausesPadded_denseOfCompact n W mLet t p qi ai dd.numStates (dd.entry qi ai)

lemma execUniquenessClausesAt_denseOfCompact (n W mLet T : ℕ) (S A : List ℕ) :
    execMapClauses (denseOfCompact n W mLet) (execUniquenessClausesAt execCompactLayout S A W T)
      = execUniquenessClausesAt (denseLayout n W mLet) S A W T := by
  unfold execUniquenessClausesAt
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro t _
  rw [execMapClauses_append, execMapClauses_append,
    execMapClauses_exactlyOne, execMapClauses_exactlyOne]
  congr 1
  congr 1
  · congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro q _
    exact denseOfCompact_state n W mLet t q
  · congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact denseOfCompact_head n W mLet t p
  · rw [execMapClauses_flatMap]
    apply List.flatMap_congr
    intro p _
    rw [execMapClauses_exactlyOne]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact denseOfCompact_cell n W mLet t p a

lemma descUniquenessClauses_denseOfCompact (n W mLet T : ℕ) (dd : TableauDescriptor) :
    execMapClauses (denseOfCompact n W mLet) (descUniquenessClauses execCompactLayout dd W T)
      = descUniquenessClauses (denseLayout n W mLet) dd W T :=
  execUniquenessClausesAt_denseOfCompact n W mLet T _ _

lemma execPersistClausesAt_denseOfCompact (n W mLet T : ℕ) (A : List ℕ) :
    execMapClauses (denseOfCompact n W mLet) (execPersistClausesAt execCompactLayout A W T)
      = execPersistClausesAt (denseLayout n W mLet) A W T := by
  unfold execPersistClausesAt
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro t _
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro pHead _
  rw [execMapClauses_flatMap]
  apply List.flatMap_congr
  intro pCell _
  by_cases h : pHead = pCell
  · simp [h, execMapClauses]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [execMapClauses, List.map_map]
    apply List.map_congr_left
    intro a _
    rw [Function.comp_apply, execMapClause_imply2, denseOfCompact_head, denseOfCompact_cell,
      denseOfCompact_cell]

lemma descPersistClauses_denseOfCompact (n W mLet T : ℕ) (dd : TableauDescriptor) :
    execMapClauses (denseOfCompact n W mLet) (descPersistClauses execCompactLayout dd W T)
      = descPersistClauses (denseLayout n W mLet) dd W T :=
  execPersistClausesAt_denseOfCompact n W mLet T _

lemma descAcceptClauses_denseOfCompact (n W mLet T : ℕ) (d : TableauDescriptor)
    (outIdx : List ℕ) :
    execMapClauses (denseOfCompact n W mLet) (descAcceptClauses execCompactLayout d outIdx W T)
      = descAcceptClauses (denseLayout n W mLet) d outIdx W T := by
  unfold descAcceptClauses
  rw [execMapClauses_append]
  congr 1
  · rw [execMapClauses_flatMap]
    apply List.flatMap_congr
    intro pHead _
    simp only [execMapClauses, List.map_map]
    apply List.map_congr_left
    intro p _
    rw [Function.comp_apply, execMapClause_implyPos, denseOfCompact_head, denseOfCompact_cell]
  · simp only [execMapClauses, List.map_cons, List.map_nil]
    rw [execMapClause_atLeastOne]
    congr 1
    apply congrArg atLeastOne
    rw [List.map_map]
    apply List.map_congr_left
    intro qi _
    exact denseOfCompact_state n W mLet T qi

lemma descInitStateClause_denseOfCompact (n W mLet : ℕ) (d : TableauDescriptor) :
    execMapClause (denseOfCompact n W mLet) (descInitStateClause execCompactLayout d)
      = descInitStateClause (denseLayout n W mLet) d := by
  unfold descInitStateClause
  split
  · simp [execMapClause, unitPos, execMapLiteral, denseOfCompact_state]
  · simp [execMapClause]

lemma descBoundedPrefixInitClauses_denseOfCompact (n W mLet T : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx : List ℕ) :
    execMapClauses (denseOfCompact n W mLet)
        (descBoundedPrefixInitClauses execCompactLayout d prefIdx freeLen allowedIdx W T)
      = descBoundedPrefixInitClauses (denseLayout n W mLet) d prefIdx freeLen allowedIdx W T := by
  unfold descBoundedPrefixInitClauses
  rw [execMapClauses_append]
  congr 1
  · simp only [execMapClauses, List.map_cons]
    rw [descInitStateClause_denseOfCompact, execMapClause_unitPos, denseOfCompact_head]
    congr 1
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_apply]
    split
    · rw [execMapClause_unitPos, denseOfCompact_cell]
    · split
      · rw [execMapClause_atLeastOne, List.map_cons, List.map_map]
        congr 1
        congr 1
        · exact denseOfCompact_cell n W mLet 0 p d.blankIdx
        · apply List.map_congr_left
          intro a _
          exact denseOfCompact_cell n W mLet 0 p a
      · rw [execMapClause_unitPos, denseOfCompact_cell]
  · simp only [execMapClauses, List.map_map]
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    rw [execMapClause_implyPos, denseOfCompact_cell, denseOfCompact_cell]

/-- The five families' equalities compose along `descTableauCNF`'s `++`, so a
producer that already emits compact numbers can rename the whole CNF and land
exactly on the dense-layout generator's own output — not merely an
equisatisfiable copy of it. -/
lemma descTableauCNF_denseOfCompact (n W mLet T : ℕ) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) :
    execMapClauses (denseOfCompact n W mLet)
        (descTableauCNF execCompactLayout d prefIdx freeLen allowedIdx outIdx W T).clauses
      = (descTableauCNF (denseLayout n W mLet) d prefIdx freeLen allowedIdx outIdx W T).clauses := by
  unfold descTableauCNF
  simp only
  rw [execMapClauses_append, execMapClauses_append, execMapClauses_append, execMapClauses_append]
  rw [descUniquenessClauses_denseOfCompact, descBoundedPrefixInitClauses_denseOfCompact,
    descTransClauses_denseOfCompact, descPersistClauses_denseOfCompact,
    descAcceptClauses_denseOfCompact]

end NPComplete.CookLevin

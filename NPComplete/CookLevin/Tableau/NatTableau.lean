module

public import NPComplete.CookLevin.Generate

/-!
The tableau compiler still mentions the verifier's state type `Λ`, but a RAM
program can only manipulate natural numbers.  This module isolates the finite
integer data a machine contributes — a transition entry per (state, letter)
index pair — so the clause generators downstream never mention `Λ` at all.

`Λ` is arbitrary (only `Inhabited`/`DecidableEq`, with finite support given by
an explicit `stateList`), so re-indexing is by list position rather than by a
`Fintype` equivalence.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Turing.TM0

/-! ## Equation lemmas for the `Λ`-indexed generator

`execTransOneAt` matches on `M q a` under a `let`-bound clause prefix, so the
three branches do not reduce definitionally.  Stating them through
`execStateIdx` / `execLetterIdx` also keeps the `BEq (Option Bool)` instance the
one `execTransOneAt` itself elaborates with; spelling the same index as
`A.idxOf a` picks `Option.instBEq` and blocks `rfl`. -/

lemma execTransOneAt_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W t p : ℕ) (q : Λ) (a : Option Bool)
    (hM : M q a = none) :
    execTransOneAt v M S A W t p q a =
      [imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
          (v.state (t + 1) (execStateIdx S q)),
        imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
          (v.head (t + 1) p),
        imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
          (v.cell (t + 1) p (execLetterIdx A a))] := by
  simp only [execTransOneAt, hM, execStateIdx, execLetterIdx]

lemma execTransOneAt_write {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W t p : ℕ) (q : Λ) (a : Option Bool)
    (q' : Λ) (b : Option Bool) (hM : M q a = some (q', .write b)) :
    execTransOneAt v M S A W t p q a =
      if q' ∈ S then
        [imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
            (v.state (t + 1) (execStateIdx S q')),
          imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
            (v.head (t + 1) p),
          imply3 (v.state t (execStateIdx S q)) (v.head t p) (v.cell t p (execLetterIdx A a))
            (v.cell (t + 1) p (execLetterIdx A b))]
      else
        [forbid3 (v.state t (execStateIdx S q)) (v.head t p)
          (v.cell t p (execLetterIdx A a))] := by
  simp only [execTransOneAt, hM, execStateIdx, execLetterIdx]

lemma execTransOneAt_move {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W t p : ℕ) (q : Λ) (a : Option Bool)
    (q' : Λ) (d : Dir) (hM : M q a = some (q', .move d)) :
    execTransOneAt v M S A W t p q a =
      if q' ∈ S then
        (match nextIdx W p d with
         | none =>
             [forbid3 (v.state t (execStateIdx S q)) (v.head t p)
               (v.cell t p (execLetterIdx A a))]
         | some p' =>
             [imply3 (v.state t (execStateIdx S q)) (v.head t p)
                 (v.cell t p (execLetterIdx A a)) (v.state (t + 1) (execStateIdx S q')),
               imply3 (v.state t (execStateIdx S q)) (v.head t p)
                 (v.cell t p (execLetterIdx A a)) (v.head (t + 1) p'),
               imply3 (v.state t (execStateIdx S q)) (v.head t p)
                 (v.cell t p (execLetterIdx A a)) (v.cell (t + 1) p (execLetterIdx A a))])
      else
        [forbid3 (v.state t (execStateIdx S q)) (v.head t p)
          (v.cell t p (execLetterIdx A a))] := by
  simp only [execTransOneAt, hM, execStateIdx, execLetterIdx]
  rfl

/-! ## The `Λ`-free transition entry -/

/-- One transition, already reduced to natural-number indices.  `write`/`move`
carry the successor state's index into `stateList`; an index equal to the list
length encodes a successor outside the support. -/
inductive NatTrans where
  | halt
  | write (qi' bi : ℕ)
  | move (qi' : ℕ) (d : Dir)
  deriving DecidableEq

/-- The entry a concrete machine contributes at a state/letter pair. -/
def transOf {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) : NatTrans :=
  match M q a with
  | none => .halt
  | some (q', .write b) => .write (execStateIdx S q') (execLetterIdx A b)
  | some (q', .move d) => .move (execStateIdx S q') d

/-- Transition clauses for one tableau cell, driven only by integer data. -/
def natTransClausesOf (v : ExecVarLayout) (n W t p qi ai : ℕ) : NatTrans → List Clause
  | .halt =>
      [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
  | .write qi' bi =>
      if qi' < n then
        [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi'),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p bi)]
      else [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
  | .move qi' d =>
      if qi' < n then
        match nextIdx W p d with
        | none => [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
        | some p' =>
            [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi'),
              imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p'),
              imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
      else [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]

@[simp] lemma transOf_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) (hM : M q a = none) :
    transOf M S A q a = .halt := by
  simp only [transOf, hM]

@[simp] lemma transOf_write {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) (q' : Λ) (b : Option Bool)
    (hM : M q a = some (q', .write b)) :
    transOf M S A q a = .write (execStateIdx S q') (execLetterIdx A b) := by
  simp only [transOf, hM]

@[simp] lemma transOf_move {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) (q' : Λ) (d : Dir)
    (hM : M q a = some (q', .move d)) :
    transOf M S A q a = .move (execStateIdx S q') d := by
  simp only [transOf, hM]

/-- The integer-driven generator reproduces the `Λ`-indexed one exactly.  The
`q' ∈ S` test becomes the index bound `execStateIdx S q' < S.length`. -/
lemma natTransClausesOf_transOf {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W t p : ℕ) (q : Λ) (a : Option Bool) :
    natTransClausesOf v S.length W t p (execStateIdx S q) (execLetterIdx A a)
        (transOf M S A q a) =
      execTransOneAt v M S A W t p q a := by
  cases hM : M q a with
  | none =>
      rw [transOf_halt M S A q a hM, execTransOneAt_halt v M S A W t p q a hM]
      rfl
  | some qs =>
      obtain ⟨q', stmt⟩ := qs
      cases stmt with
      | write b =>
          rw [transOf_write M S A q a q' b hM,
            execTransOneAt_write v M S A W t p q a q' b hM, natTransClausesOf,
            execStateIdx]
          by_cases hq' : q' ∈ S
          · rw [ite_eq_left (List.idxOf_lt_length_iff.mpr hq'), ite_eq_left hq']
          · rw [ite_eq_right (fun h => hq' (List.idxOf_lt_length_iff.mp h)), ite_eq_right hq']
      | move d =>
          rw [transOf_move M S A q a q' d hM,
            execTransOneAt_move v M S A W t p q a q' d hM, natTransClausesOf,
            execStateIdx]
          by_cases hq' : q' ∈ S
          · rw [ite_eq_left (List.idxOf_lt_length_iff.mpr hq'), ite_eq_left hq']
          · rw [ite_eq_right (fun h => hq' (List.idxOf_lt_length_iff.mp h)), ite_eq_right hq']

/-! ## A fixed-width transition cell

`encodeList` writes the element count as a unary prefix, so a producer must know
the clause count before it emits any bit — there is no backpatching.  The count
is not uniform, though: the rejecting branches emit one clause where the others
emit three.  Repeating that clause to width three makes the total a closed
formula in `T`, `W`, `n` and `m`, and repetition changes the multiset of clauses
but not the set, so satisfiability is untouched. -/

/-- Transition clauses for one cell, always exactly three. -/
def natTransClausesPadded (v : ExecVarLayout) (n W t p qi ai : ℕ) :
    NatTrans → List Clause
  | .halt =>
      [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
        imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
  | .write qi' bi =>
      if qi' < n then
        [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi'),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p),
          imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p bi)]
      else
        [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
  | .move qi' d =>
      if qi' < n then
        match nextIdx W p d with
        | none =>
            [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
              forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
              forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]
        | some p' =>
            [imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.state (t + 1) qi'),
              imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.head (t + 1) p'),
              imply3 (v.state t qi) (v.head t p) (v.cell t p ai) (v.cell (t + 1) p ai)]
      else
        [forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai),
          forbid3 (v.state t qi) (v.head t p) (v.cell t p ai)]

lemma natTransClausesPadded_length (v : ExecVarLayout) (n W t p qi ai : ℕ)
    (e : NatTrans) :
    (natTransClausesPadded v n W t p qi ai e).length = 3 := by
  cases e with
  | halt => rfl
  | write qi' bi => simp only [natTransClausesPadded]; split <;> rfl
  | move qi' d =>
      simp only [natTransClausesPadded]
      split
      · split <;> rfl
      · rfl

/-- Padding repeats a clause, so the set of clauses is unchanged. -/
lemma natTransClausesPadded_mem (v : ExecVarLayout) (n W t p qi ai : ℕ)
    (e : NatTrans) (c : Clause) :
    c ∈ natTransClausesPadded v n W t p qi ai e ↔
      c ∈ natTransClausesOf v n W t p qi ai e := by
  cases e with
  | halt => simp only [natTransClausesPadded, natTransClausesOf]
  | write qi' bi =>
      simp only [natTransClausesPadded, natTransClausesOf]
      split <;> simp
  | move qi' d =>
      simp only [natTransClausesPadded, natTransClausesOf]
      split
      · cases nextIdx W p d <;> simp
      · simp

/-! ## Re-indexing list-driven loops as range loops

A RAM program iterates over `[0, n)`, not over a list of states.  When the loop
body consults an element only through its index — which is what the `Λ`-free
cells do — the two agree as soon as the list is duplicate-free, and
`ExecutableTableauAux` carries exactly that (`stateList_nodup`). -/

/-- For a duplicate-free list, mapping each element to its index enumerates
`range` exactly. -/
lemma map_idxOf_eq_range {α : Type} [DecidableEq α] (S : List α) (h : S.Nodup) :
    S.map (fun q => S.idxOf q) = List.range S.length := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact List.Nodup.idxOf_getElem h i (by simpa using h1)

/-- Instance-aligned twin of `map_idxOf_eq_range` for the letter list: written
through `execLetterIdx` so it rewrites against the generators. -/
lemma map_execLetterIdx_eq_range (A : List (Option Bool)) (h : A.Nodup) :
    A.map (fun a => execLetterIdx A a) = List.range A.length := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    unfold execLetterIdx
    exact @List.Nodup.idxOf_getElem (Option Bool) instBEqOfDecidableEq inferInstance A h i
      (by simpa using h1)

/-! ## Lifting the cell-level bridge to the whole transition family -/

/-- Cellwise agreement lifts to the whole family: only the entry consulted at
each cell differs, and `natTransClausesOf_transOf` matches those. -/
lemma execTransClausesAt_eq_nat {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W T : ℕ) :
    execTransClausesAt v M S A W T =
      (List.range T).flatMap fun t =>
        (List.range W).flatMap fun p =>
          S.flatMap fun q => A.flatMap fun a =>
            natTransClausesOf v S.length W t p (execStateIdx S q) (execLetterIdx A a)
              (transOf M S A q a) := by
  rw [execTransClausesAt]
  refine List.flatMap_congr (fun t _ => ?_)
  refine List.flatMap_congr (fun p _ => ?_)
  refine List.flatMap_congr (fun q _ => ?_)
  refine List.flatMap_congr (fun a _ => ?_)
  exact (natTransClausesOf_transOf v M S A W t p q a).symm

/-! ## The halt-state family

`execAcceptClausesAt` is the second and last place the generator inspects `M`
directly.  The halting test is also a function of the transition entry alone. -/

/-- Halting is decided by the entry, so the accept clauses need no `M` either. -/
lemma execHaltStates_eq_transOf {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (a : Option Bool) :
    execHaltStates M S a = S.filter fun q => transOf M S A q a == NatTrans.halt := by
  rw [execHaltStates]
  refine List.filter_congr (fun q _ => ?_)
  cases hM : M q a with
  | none => simp [hM]
  | some qs =>
      obtain ⟨q', stmt⟩ := qs
      cases stmt with
      | write b => simp [transOf_write M S A q a q' b hM]
      | move d => simp [transOf_move M S A q a q' d hM]

/-! ### Instance-aligned `idxOf` facts

Same trap as the equation lemmas: spelling these through `execStateIdx` /
`execLetterIdx` keeps the `BEq (Option Bool)` instance the one the generators
elaborate with.  Using `List.idxOf` directly picks `Option.instBEq`, and the two
then look like unrelated terms to `rw` and `omega`. -/

lemma getElem?_execStateIdx {Λ : Type} [DecidableEq Λ] {S : List Λ} {q : Λ}
    (hq : q ∈ S) : S[execStateIdx S q]? = some q := by
  unfold execStateIdx; exact List.getElem?_idxOf hq

lemma getElem?_execLetterIdx {A : List (Option Bool)} {a : Option Bool}
    (ha : a ∈ A) : A[execLetterIdx A a]? = some a := by
  unfold execLetterIdx
  exact @List.getElem?_idxOf (Option Bool) instBEqOfDecidableEq inferInstance a A ha

lemma execStateIdx_lt_of_mem {Λ : Type} [DecidableEq Λ] {S : List Λ} {q : Λ}
    (hq : q ∈ S) : execStateIdx S q < S.length := by
  unfold execStateIdx; exact List.idxOf_lt_length_iff.mpr hq

lemma execLetterIdx_lt_of_mem {A : List (Option Bool)} {a : Option Bool}
    (ha : a ∈ A) : execLetterIdx A a < A.length := by
  unfold execLetterIdx
  exact (@List.idxOf_lt_length_iff (Option Bool) instBEqOfDecidableEq inferInstance A a).mpr ha

/-! ## The machine as finite integer data

A RAM program cannot hold a `Machine`, but it can hold the table one induces.
`TableauDescriptor` is that table plus the handful of scalars the generators
read, with no `Λ` and no functions — exactly what can be baked into a program
whose size does not depend on the input. -/

/-- Everything the clause families consult about a verifier, as finite integer
data.  `table` is row-major: the entry for `(qi, ai)` sits at
`qi * numLetters + ai`.

The three letter indices are carried explicitly because `letterList` is
`Finset.univ.toList`, whose *order* is not pinned down by anything the
`ExecutableTableauAux` fields guarantee — only that it is duplicate-free and
complete.  A producer that has to turn an input bit into a letter index
therefore cannot compute it; it must be told. -/
structure TableauDescriptor where
  numStates : ℕ
  startState : ℕ
  numLetters : ℕ
  blankIdx : ℕ
  falseIdx : ℕ
  trueIdx : ℕ
  table : List NatTrans

/-- Row-major lookup; a flattened offset `qi * d.numLetters + ai` outside the table reads as
`halt`. -/
def TableauDescriptor.entry (d : TableauDescriptor) (qi ai : ℕ) : NatTrans :=
  d.table.getD (qi * d.numLetters + ai) NatTrans.halt

/-- Row-major indexing into a flattened range-of-ranges. -/
lemma getElem?_flatMap_range {α : Type} (m : ℕ) (f : ℕ → ℕ → α) :
    ∀ (n qi ai : ℕ), qi < n → ai < m →
      ((List.range n).flatMap fun q => (List.range m).map fun a => f q a)[qi * m + ai]?
        = some (f qi ai) := by
  intro n
  induction n with
  | zero => intro qi ai hq _; omega
  | succ n ih =>
      intro qi ai hq ha
      rw [List.range_succ, List.flatMap_append]
      have hlen : ((List.range n).flatMap
          fun q => (List.range m).map fun a => f q a).length = n * m := by simp
      by_cases hlt : qi < n
      · rw [List.getElem?_append_left (by rw [hlen]; calc qi * m + ai < qi * m + m := by omega
              _ = (qi + 1) * m := by ring
              _ ≤ n * m := Nat.mul_le_mul_right m hlt)]
        exact ih qi ai hlt ha
      · have hqn : qi = n := by omega
        subst hqn
        rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [show qi * m + ai - qi * m = ai by omega]
        rw [List.getElem?_map, List.getElem?_range ha]
        rfl

/-- The descriptor a concrete machine induces.  `noncomputable` only because
`transOf` is stated over an arbitrary `Λ`; the value is finite data. -/
noncomputable def descriptorOf {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool)) :
    TableauDescriptor where
  numStates := S.length
  startState := execStateIdx S default
  numLetters := A.length
  blankIdx := execLetterIdx A none
  falseIdx := execLetterIdx A (some false)
  trueIdx := execLetterIdx A (some true)
  table := (List.range S.length).flatMap fun qi =>
    (List.range A.length).map fun ai =>
      match S[qi]?, A[ai]? with
      | some q, some a => transOf M S A q a
      | _, _ => NatTrans.halt

/-- The descriptor reproduces the machine's transition entries exactly, so the
clause families may consult it instead of `M`. -/
lemma descriptorOf_entry {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (q : Λ) (a : Option Bool) (hq : q ∈ S) (ha : a ∈ A) :
    (descriptorOf M S A).entry (execStateIdx S q) (execLetterIdx A a)
      = transOf M S A q a := by
  unfold TableauDescriptor.entry descriptorOf
  simp only []
  rw [List.getD_eq_getElem?_getD,
    getElem?_flatMap_range A.length _ S.length _ _
      (execStateIdx_lt_of_mem hq) (execLetterIdx_lt_of_mem ha)]
  simp only [Option.getD_some]
  rw [getElem?_execStateIdx hq, getElem?_execLetterIdx ha]

/-! ## The transition family a RAM loop refines

The family `descTransClauses` iterates over ranges rather than lists, pads each cell's
clauses so every iteration writes the same number of them, and takes all machine data from
the descriptor. A RAM loop can refine this form directly. -/

def descTransClauses (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    List Clause :=
  (List.range T).flatMap fun t =>
    (List.range W).flatMap fun p =>
      (List.range d.numStates).flatMap fun qi =>
        (List.range d.numLetters).flatMap fun ai =>
          natTransClausesPadded v d.numStates W t p qi ai (d.entry qi ai)

/-- The clause count is a closed formula, which is what `encodeList`'s unary
length prefix requires of a producer. -/
lemma descTransClauses_length (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    (descTransClauses v d W T).length = T * W * d.numStates * d.numLetters * 3 := by
  unfold descTransClauses
  simp only [List.length_flatMap, natTransClausesPadded_length]
  simp
  ring

/-- Membership in the descriptor-driven family matches the `Λ`-indexed one,
for a duplicate-free state and letter support. -/
lemma descTransClauses_mem {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W T : ℕ)
    (hS : S.Nodup) (hA : A.Nodup) (c : Clause) :
    c ∈ descTransClauses v (descriptorOf M S A) W T ↔
      c ∈ execTransClausesAt v M S A W T := by
  rw [execTransClausesAt_eq_nat]
  unfold descTransClauses
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, p, hp, qi, hqi, ai, hai, hc⟩
    simp only [List.mem_range] at hqi hai
    have hqi' : qi < S.length := hqi
    have hai' : ai < A.length := hai
    refine ⟨t, ht, p, hp, S[qi], List.getElem_mem hqi', A[ai], List.getElem_mem hai', ?_⟩
    have hSq : execStateIdx S S[qi] = qi := by
      unfold execStateIdx; exact List.Nodup.idxOf_getElem hS qi hqi'
    have hAa : execLetterIdx A A[ai] = ai := by
      unfold execLetterIdx
      exact @List.Nodup.idxOf_getElem (Option Bool) instBEqOfDecidableEq inferInstance A hA ai hai'
    have hentry : (descriptorOf M S A).entry qi ai = transOf M S A S[qi] A[ai] := by
      have h0 := descriptorOf_entry M S A S[qi] A[ai] (List.getElem_mem hqi') (List.getElem_mem hai')
      rwa [hSq, hAa] at h0
    rw [hentry, natTransClausesPadded_mem] at hc
    have hnum : (descriptorOf M S A).numStates = S.length := rfl
    rw [hnum] at hc
    rw [hSq, hAa]
    exact hc
  · rintro ⟨t, ht, p, hp, q, hq, a, ha, hc⟩
    refine ⟨t, ht, p, hp, execStateIdx S q, ?_, execLetterIdx A a, ?_, ?_⟩
    · simp only [List.mem_range]; exact execStateIdx_lt_of_mem hq
    · simp only [List.mem_range]; exact execLetterIdx_lt_of_mem ha
    · rw [descriptorOf_entry M S A q a hq ha]
      rw [natTransClausesPadded_mem]
      exact hc

/-! ### Reading a tape symbol by index

The accept and init families consult `initSymbol L p`, which falls back to the
blank outside the list.  Indexing the list once and reading the result needs the
blank supplied explicitly: `List.getD`'s default for `ℕ` would be `0`, which is
the blank's index only by accident. -/

/-- `initSymbol` on an already-indexed list. -/
def natInitSymbol (blank : ℕ) (xs : List ℕ) (p : ℤ) : ℕ :=
  if 0 ≤ p then xs.getD p.toNat blank else blank

/-- Indexing the list first agrees with indexing the symbol, given the blank's
own index. -/
lemma natInitSymbol_eq (A L : List (Option Bool)) (blank : ℕ)
    (hblank : blank = execLetterIdx A default) (p : ℤ) :
    natInitSymbol blank (L.map (execLetterIdx A)) p
      = execLetterIdx A (initSymbol L p) := by
  unfold natInitSymbol initSymbol
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getI_eq_getElem?_getD]
    cases h : L[p.toNat]? with
    | none => simp [hblank]
    | some x => simp
  · exact hblank

/-! ### Closed-form clause counts for `atMostOne` / `exactlyOne`

The RAM cost analysis needs an exact clause count for the CNF the tableau
compiler emits, not just an upper bound.  Doubling avoids `ℕ` division: each
`atMostOne` count is a triangular number, so a `/2` would carry a side
condition through every arithmetic step downstream. -/

/-- Doubled to avoid `ℕ` division; `atMostOne vs` pairs every element of `vs`
with every later element, so its count is the triangular number below
`vs.length`. -/
lemma atMostOne_length (vs : List ℕ) :
    2 * (atMostOne vs).length = vs.length * (vs.length - 1) := by
  induction vs with
  | nil => simp [atMostOne]
  | cons v vs ih =>
      rw [atMostOne_cons, List.length_append, List.length_map]
      simp only [List.length_cons, Nat.add_sub_cancel]
      generalize hL : (atMostOne vs).length = L at ih
      generalize hn : vs.length = n at ih
      cases n with
      | zero => simp at ih; omega
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih
          nlinarith

lemma exactlyOne_length (vs : List ℕ) :
    2 * (exactlyOne vs).length = vs.length * (vs.length - 1) + 2 := by
  unfold exactlyOne
  rw [List.length_cons]
  have := atMostOne_length vs
  omega

/-! ### The uniqueness and persistence families

These already take `ℕ` index lists, and the call site hands them the `idxOf`
images of `stateList` / `letterList`.  For duplicate-free lists those images are
ranges, so the descriptor versions are the same functions at `range` — an
equality, not merely a satisfiability match. -/

def descUniquenessClauses (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    List Clause :=
  execUniquenessClausesAt v (List.range d.numStates) (List.range d.numLetters) W T

def descPersistClauses (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    List Clause :=
  execPersistClausesAt v (List.range d.numLetters) W T

lemma descUniquenessClauses_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W T : ℕ) (hS : S.Nodup) (hA : A.Nodup) :
    descUniquenessClauses v (descriptorOf M S A) W T =
      execUniquenessClausesAt v (S.map (fun q => execStateIdx S q))
        (A.map (fun a => execLetterIdx A a)) W T := by
  unfold descUniquenessClauses
  rw [map_execLetterIdx_eq_range A hA]
  unfold execStateIdx
  rw [map_idxOf_eq_range S hS]
  rfl

/-- Doubled to avoid `ℕ` division in the callers below: pairing a fixed count
`2 * f p = c` across `List.range W` sums to `W * c`, one `c` per element. -/
lemma double_sum_range_const (W : ℕ) (f : ℕ → ℕ) (c : ℕ) (hf : ∀ p, 2 * f p = c) :
    2 * ((List.range W).map f).sum = W * c := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      have := hf n
      ring_nf
      ring_nf at ih
      omega

/-- Each row of the tableau contributes one `exactlyOne` clause set for the
state, one for the head, and `W` for the cells; summing across `T + 1` rows
gives the total, doubled to avoid `ℕ` division. -/
lemma descUniquenessClauses_length (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    2 * (descUniquenessClauses v d W T).length =
      (T + 1) * ((d.numStates * (d.numStates - 1) + 2) +
                 (W * (W - 1) + 2) +
                 W * (d.numLetters * (d.numLetters - 1) + 2)) := by
  unfold descUniquenessClauses execUniquenessClausesAt
  rw [List.length_flatMap]
  apply double_sum_range_const
  intro t
  rw [List.length_append, List.length_append, List.length_flatMap]
  have h1 : 2 * (exactlyOne ((List.range d.numStates).map fun q => v.state t q)).length
      = d.numStates * (d.numStates - 1) + 2 := by
    rw [exactlyOne_length, List.length_map, List.length_range]
  have h2 : 2 * (exactlyOne ((List.range W).map fun p => v.head t p)).length
      = W * (W - 1) + 2 := by
    rw [exactlyOne_length, List.length_map, List.length_range]
  have h3 : 2 * ((List.range W).map (fun p =>
      (exactlyOne ((List.range d.numLetters).map fun a => v.cell t p a)).length)).sum
      = W * (d.numLetters * (d.numLetters - 1) + 2) := by
    apply double_sum_range_const
    intro p
    rw [exactlyOne_length, List.length_map, List.length_range]
  omega

/-- Every element of `List.range W` other than `pHead` itself contributes `m`
to the sum; only `pHead`'s own position contributes `0`. -/
lemma sum_range_ite_eq_self (W pHead m : ℕ) (hp : pHead < W) :
    ((List.range W).map (fun pCell => if pHead = pCell then 0 else m)).sum = (W - 1) * m := by
  induction W with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      by_cases heq : pHead = n
      · subst heq
        have hconst : (List.range pHead).map (fun pCell => if pHead = pCell then 0 else m)
            = List.replicate pHead m := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
            rw [List.length_map, List.length_range] at h1
            rw [ite_eq_right (by omega)]
        rw [hconst, List.sum_replicate, smul_eq_mul, ite_eq_left rfl]
        simp
      · have hlt : pHead < n := by omega
        have hsum := ih hlt
        rw [hsum, ite_eq_right heq]
        have hW1 : n + 1 - 1 = n := by omega
        rw [hW1]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
        subst hk
        simp [Nat.succ_mul]

/-- The persist family skips the diagonal `pHead = pCell`, so each of the `W`
head positions contributes `W - 1` cell clauses per letter, across `T` rows. -/
lemma descPersistClauses_length (v : ExecVarLayout) (d : TableauDescriptor) (W T : ℕ) :
    (descPersistClauses v d W T).length = T * W * (W - 1) * d.numLetters := by
  unfold descPersistClauses execPersistClausesAt
  rw [List.length_flatMap]
  have hterm : ∀ t : ℕ,
      (((List.range W).flatMap fun pHead =>
        (List.range W).flatMap fun pCell =>
          if pHead = pCell then ([] : List Clause)
          else (List.range d.numLetters).map fun a =>
            imply2 (v.head t pHead) (v.cell t pCell a) (v.cell (t + 1) pCell a))).length
        = W * (W - 1) * d.numLetters := by
    intro t
    rw [List.length_flatMap]
    have hinner : ∀ pHead ∈ List.range W,
        ((List.range W).flatMap fun pCell =>
          if pHead = pCell then ([] : List Clause)
          else (List.range d.numLetters).map fun a =>
            imply2 (v.head t pHead) (v.cell t pCell a) (v.cell (t + 1) pCell a)).length
          = (W - 1) * d.numLetters := by
      intro pHead hpHead
      rw [List.length_flatMap]
      have heq : (List.range W).map (fun pCell =>
          (if pHead = pCell then ([] : List Clause)
          else (List.range d.numLetters).map fun a =>
            imply2 (v.head t pHead) (v.cell t pCell a) (v.cell (t + 1) pCell a)).length)
          = (List.range W).map (fun pCell =>
            if pHead = pCell then 0 else d.numLetters) := by
        apply List.map_congr_left
        intro pCell _
        by_cases h : pHead = pCell
        · simp [h]
        · simp [h]
      rw [heq]
      exact sum_range_ite_eq_self W pHead d.numLetters (List.mem_range.mp hpHead)
    rw [List.map_congr_left hinner, List.map_const', List.sum_const_nat, List.length_range]
    ring
  rw [List.map_congr_left (fun t _ => hterm t), List.map_const', List.sum_const_nat,
    List.length_range]
  ring

lemma descPersistClauses_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (W T : ℕ) (hA : A.Nodup) :
    descPersistClauses v (descriptorOf M S A) W T =
      execPersistClausesAt v (A.map (fun a => execLetterIdx A a)) W T := by
  unfold descPersistClauses
  rw [map_execLetterIdx_eq_range A hA]
  rfl

/-- The start-state clause.  "The default state is in the support" becomes the
index test `startState < numStates`, matching `List.idxOf_lt_length_iff`. -/
def descInitStateClause (v : ExecVarLayout) (d : TableauDescriptor) : Clause :=
  if d.startState < d.numStates then unitPos (v.state 0 d.startState) else ⟨[]⟩

lemma descInitStateClause_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) :
    descInitStateClause v (descriptorOf M S A) = execInitStateClauseAt v S := by
  unfold descInitStateClause execInitStateClauseAt descriptorOf execStateIdx
  simp only []
  by_cases h : (default : Λ) ∈ S
  · rw [ite_eq_left (List.idxOf_lt_length_iff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hlt => h (List.idxOf_lt_length_iff.mp hlt)), ite_eq_right h]

/-! ## Refining a `filter` loop over a `Nodup` list to `range`

`map_idxOf_eq_range` covers a plain re-indexing loop; the halt-state family
adds a `filter` on top, so the boolean test at each list element must line up
with the test at its index. -/

/-- The `filter` counterpart of `map_idxOf_eq_range`: re-indexing a filtered
sublist matches filtering the index range, given a test that agrees with the
element-level test at each position. -/
lemma map_idxOf_filter_eq_range_filter {α : Type} [DecidableEq α] (S : List α)
    (h : S.Nodup) (P : α → Bool) (Q : ℕ → Bool)
    (hPQ : ∀ (i : ℕ) (hi : i < S.length), Q i = P S[i]) :
    (S.filter P).map (fun q => S.idxOf q) = (List.range S.length).filter Q := by
  rw [← map_idxOf_eq_range S h, List.filter_map]
  congr 1
  apply List.filter_congr
  intro q hq
  simp only [Function.comp_apply]
  have hi : S.idxOf q < S.length := List.idxOf_lt_length_iff.mpr hq
  rw [hPQ (S.idxOf q) hi, List.getElem_idxOf hi]

/-! ## Halting as descriptor data

The last place `execAcceptClausesAt` reads `M` directly: which states halt on
a letter. `execHaltStates_eq_transOf` already reduces that to the transition
entry, so re-indexing by `map_idxOf_filter_eq_range_filter` gives a `range`
version driven purely by the descriptor. -/

/-- Which state indices halt on a letter index, read off the descriptor. -/
def descHaltStates (d : TableauDescriptor) (ai : ℕ) : List ℕ :=
  (List.range d.numStates).filter (fun qi => d.entry qi ai == NatTrans.halt)

lemma descHaltStates_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (a : Option Bool) (hS : S.Nodup) (ha : a ∈ A) :
    descHaltStates (descriptorOf M S A) (execLetterIdx A a)
      = (execHaltStates M S a).map (fun q => execStateIdx S q) := by
  rw [execHaltStates_eq_transOf M S A a]
  unfold descHaltStates
  have hnum : (descriptorOf M S A).numStates = S.length := rfl
  rw [hnum]
  symm
  apply map_idxOf_filter_eq_range_filter S hS
  intro i hi
  have hentry : (descriptorOf M S A).entry i (execLetterIdx A a) = transOf M S A S[i] a := by
    have h0 := descriptorOf_entry M S A S[i] a (List.getElem_mem hi) ha
    have hSq : execStateIdx S S[i] = i := by
      unfold execStateIdx; exact List.Nodup.idxOf_getElem hS i hi
    rwa [hSq] at h0
  rw [hentry]

/-! ## The accept family as descriptor data

`execAcceptClausesAt` mentions `M` only through `execHaltStates`, already
handled above, and `A` only through `execLetterIdx`, already handled by
`natInitSymbol_eq`. The accept clauses at the final tableau row therefore
refine to a descriptor-only, `range`-driven family. -/

/-- The blank/none fallback of `initSymbol` never leaves a list closed under
membership, so a re-indexed `initSymbol` on an integer index list stays inside
the letter support that produced it. -/
lemma initSymbol_mem_of_forall_mem (L A : List (Option Bool))
    (hout : ∀ a ∈ L, a ∈ A) (hnone : (none : Option Bool) ∈ A) (p : ℤ) :
    initSymbol L p ∈ A := by
  unfold initSymbol
  split
  · by_cases hidx : p.toNat < L.length
    · rw [List.getI_eq_getElem _ hidx]
      exact hout _ (List.getElem_mem hidx)
    · rw [List.getI_eq_default _ (not_lt.mp hidx)]
      exact hnone
  · exact hnone

def descAcceptClauses (v : ExecVarLayout) (d : TableauDescriptor)
    (outIdx : List ℕ) (W T : ℕ) : List Clause :=
  ((List.range W).flatMap fun pHead =>
      (List.range W).map fun p =>
        implyPos (v.head T pHead)
          (v.cell T p (natInitSymbol d.blankIdx outIdx ((p : ℤ) - (pHead : ℤ))))) ++
    [atLeastOne ((descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).map
      fun qi => v.state T qi)]

lemma descAcceptClauses_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (output : List (Option Bool)) (W T : ℕ)
    (hS : S.Nodup) (hout : ∀ a ∈ output, a ∈ A) (hnone : (none : Option Bool) ∈ A) :
    descAcceptClauses v (descriptorOf M S A) (output.map (execLetterIdx A)) W T
      = execAcceptClausesAt v M S A output W T := by
  have hblank : (descriptorOf M S A).blankIdx = execLetterIdx A default := rfl
  unfold descAcceptClauses execAcceptClausesAt
  congr 1
  · refine List.flatMap_congr (fun pHead _ => ?_)
    refine List.map_congr_left (fun p _ => ?_)
    rw [natInitSymbol_eq A output (descriptorOf M S A).blankIdx hblank]
    rfl
  · have hp0 : natInitSymbol (descriptorOf M S A).blankIdx (output.map (execLetterIdx A)) 0
        = execLetterIdx A (initSymbol output 0) :=
      natInitSymbol_eq A output (descriptorOf M S A).blankIdx hblank 0
    rw [hp0, descHaltStates_eq M S A (initSymbol output 0) hS
      (initSymbol_mem_of_forall_mem output A hout hnone 0), List.map_map]
    rfl

/-- The accept family emits one clause per `(pHead, p)` pair in the `W × W`
grid, plus the single halt-state clause. -/
lemma descAcceptClauses_length (v : ExecVarLayout) (d : TableauDescriptor)
    (outIdx : List ℕ) (W T : ℕ) :
    (descAcceptClauses v d outIdx W T).length = W * W + 1 := by
  unfold descAcceptClauses
  rw [List.length_append, List.length_flatMap]
  simp [List.length_map]

/-! ## The initial family as descriptor data

The initial clauses read `A` only through `execLetterIdx` and the blank, both
already available as descriptor data, so re-indexing the prefix and the allowed
suffix symbols turns this family into one over `ℕ` lists. -/

def descBoundedPrefixInitClauses (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx : List ℕ) (W T : ℕ) : List Clause :=
  (descInitStateClause v d ::
      unitPos (v.head 0 (originIdx T)) ::
        (List.range W).map fun p =>
          if p < T + prefIdx.length then
            unitPos (v.cell 0 p (natInitSymbol d.blankIdx prefIdx (idxToPos T p)))
          else if p < T + prefIdx.length + freeLen then
            atLeastOne ((d.blankIdx :: allowedIdx).map fun a => v.cell 0 p a)
          else unitPos (v.cell 0 p d.blankIdx)) ++
    (List.range freeLen).map fun i =>
      implyPos (v.cell 0 (T + prefIdx.length + i) d.blankIdx)
        (v.cell 0 (T + prefIdx.length + i + 1) d.blankIdx)

/-- The three-way branch at one window index, split off so the family proof
stays a `map` congruence. -/
lemma desc_init_cell_eq (v : ExecVarLayout) {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : Machine (Option Bool) Λ) (S : List Λ) (A : List (Option Bool))
    (pref allowed : List (Option Bool)) (freeLen T p : ℕ) :
    (if p < T + pref.length then
        unitPos (v.cell 0 p (natInitSymbol (descriptorOf M S A).blankIdx
          (pref.map (execLetterIdx A)) (idxToPos T p)))
      else if p < T + pref.length + freeLen then
        atLeastOne (((descriptorOf M S A).blankIdx ::
          allowed.map (execLetterIdx A)).map fun a => v.cell 0 p a)
      else unitPos (v.cell 0 p (descriptorOf M S A).blankIdx)) =
    (if p < T + pref.length then
        unitPos (v.cell 0 p (execLetterIdx A (initSymbol pref (idxToPos T p))))
      else if p < T + pref.length + freeLen then
        atLeastOne (((none : Option Bool) :: allowed).map fun a =>
          v.cell 0 p (execLetterIdx A a))
      else unitPos (v.cell 0 p (execLetterIdx A none))) := by
  have hblank : (descriptorOf M S A).blankIdx = execLetterIdx A default := rfl
  rw [natInitSymbol_eq A pref (descriptorOf M S A).blankIdx hblank, hblank]
  simp only [List.map_cons, List.map_map, Function.comp_def]
  rfl

lemma descBoundedPrefixInitClauses_eq {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (v : ExecVarLayout) (M : Machine (Option Bool) Λ) (S : List Λ)
    (A : List (Option Bool)) (pref : List (Option Bool)) (freeLen : ℕ)
    (allowed : List (Option Bool)) (W T : ℕ) :
    descBoundedPrefixInitClauses v (descriptorOf M S A) (pref.map (execLetterIdx A))
        freeLen (allowed.map (execLetterIdx A)) W T
      = execBoundedPrefixInitClausesAt v S A pref freeLen allowed none W T := by
  unfold descBoundedPrefixInitClauses execBoundedPrefixInitClausesAt
  rw [List.length_map]
  congr 1
  rw [descInitStateClause_eq v M S A]
  congr 2
  exact List.map_congr_left (fun p _ => desc_init_cell_eq v M S A pref allowed freeLen T p)

/-- The init family emits two fixed clauses, one per window cell, and one per
free-suffix index (the blank-propagation implications). -/
lemma descBoundedPrefixInitClauses_length (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx : List ℕ) (W T : ℕ) :
    (descBoundedPrefixInitClauses v d prefIdx freeLen allowedIdx W T).length
      = 2 + W + freeLen := by
  unfold descBoundedPrefixInitClauses
  rw [List.length_append, List.length_cons, List.length_cons, List.length_map, List.length_map,
    List.length_range, List.length_range]
  omega

end NPComplete.CookLevin

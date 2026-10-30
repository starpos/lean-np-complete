module

public import NPComplete.CookLevin.Tableau.TableauRamLoops
public import NPComplete.CookLevin.ToThreeCNF

/-!
The generic emit toolkit already knows how to write a length-prefixed list whose
elements are "one tag bit followed by a unary datum", and how to write a table of
such lists.  A literal is exactly that shape — a polarity bit and a unary
variable index — so a CNF's encoding is already in the toolkit's format and no
clause-specific emitter has to be written.

Establishing that here, as list equalities, separates the question "what bits
does a clause encode to" from "what does the program write", so the program's
correctness proof can consume a bit string in the toolkit's own vocabulary.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BitEncoding
open NPComplete.SAT

/-- A literal's polarity, as the tag bit the emitter writes. -/
def litTag : Literal → Bool
  | .pos _ => false
  | .neg _ => true

/-- A literal's variable index, as the unary datum the emitter writes. -/
def litVar : Literal → ℕ
  | .pos v => v
  | .neg v => v

lemma encodeLiteral_eq_tag_var (l : Literal) :
    NPComplete.SAT.encodeLiteral l = [litTag l] ++ encodeNat (litVar l) := by
  cases l <;> rfl

/-- Re-indexing a mapped concatenation through the list's own range.  A RAM loop
can only iterate over a range, so every family stated by mapping over a list has
to be moved to this form before a program can refine it. -/
lemma flatten_map_eq_range_flatMap {α β : Type} [Inhabited α] (f : α → List β) (L : List α) :
    (L.map f).flatten = (List.range L.length).flatMap (fun i => f (L.getD i default)) := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.flatten_cons, ih, List.length_cons,
        List.range_succ_eq_map, List.flatMap_cons]
      congr 1
      rw [List.flatMap_map]
      apply List.flatMap_congr
      intro i _
      simp [List.getD_eq_getElem?_getD]

/-- A clause encodes to a length prefix followed by one tag/datum pair per
literal — the payload format the generic list emitter already produces. -/
lemma encodeClause_eq_ops (c : Clause) :
    encodeClause c = encodeNat c.lits.length
      ++ (List.range c.lits.length).flatMap
           (fun i => [litTag (c.lits.getD i default)]
             ++ encodeNat (litVar (c.lits.getD i default))) := by
  unfold encodeClause encodeList
  congr 1
  rw [flatten_map_eq_range_flatMap]
  apply List.flatMap_congr
  intro i _
  exact encodeLiteral_eq_tag_var _

/-- A CNF encodes to a clause count followed by the clauses' own encodings,
indexed by range — the outer level of a two-level emit loop. -/
lemma encodeCNF_eq_rows (φ : CNF) :
    encodeCNF φ = encodeNat φ.clauses.length
      ++ (List.range φ.clauses.length).flatMap
           (fun k => encodeClause (φ.clauses.getD k default)) := by
  unfold encodeCNF encodeList
  congr 1
  exact flatten_map_eq_range_flatMap _ _

/-! ## The three columns a producer has to materialize

Three index-driven column functions carry everything the encoding depends on, which
fixes the contract between the two halves of the producer: whatever writes the clause
table only has to place these values, and whatever emits the bits only has to read
them.  Neither half needs to mention `Clause` or `Literal`. -/

/-- Literal count of clause `k`. -/
def cnfCnt (φ : CNF) (k : ℕ) : ℕ := (φ.clauses.getD k default).lits.length

/-- Polarity of literal `i` of clause `k`. -/
def cnfTag (φ : CNF) (k i : ℕ) : Bool :=
  litTag ((φ.clauses.getD k default).lits.getD i default)

/-- Variable index of literal `i` of clause `k`. -/
def cnfVar (φ : CNF) (k i : ℕ) : ℕ :=
  litVar ((φ.clauses.getD k default).lits.getD i default)

/-! ## Where the cursor sits partway through the emission

The emit loop's invariant has to say exactly where the output cursor is after
some prefix of the clauses, because each iteration's separation conditions are
stated against the cursor's current position.  Carrying the exact prefix length
rather than an estimate keeps those conditions provable from a single global
bound on the total. -/

/-- Bits written by the first `m` clauses. -/
def clausePrefixBitsLen (φ : CNF) (m : ℕ) : ℕ :=
  ((List.range m).flatMap (fun k => encodeClause (φ.clauses.getD k default))).length

lemma clausePrefixBitsLen_succ (φ : CNF) (m : ℕ) :
    clausePrefixBitsLen φ (m + 1)
      = clausePrefixBitsLen φ m + (encodeClause (φ.clauses.getD m default)).length := by
  unfold clausePrefixBitsLen
  rw [List.range_succ, List.flatMap_append]
  simp

/-- Once every clause has been written, the cursor has advanced past the whole
encoding — the length prefix included. -/
lemma clausePrefixBitsLen_full (φ : CNF) :
    clausePrefixBitsLen φ φ.clauses.length + (φ.clauses.length + 1)
      = (encodeCNF φ).length := by
  unfold clausePrefixBitsLen
  rw [encodeCNF_eq_rows, List.length_append, encodeNat_length]
  omega

/-- The generator always emits at least one clause, so the two-bit lower bound on
its encoding — which the raw tape decode needs — is unconditional here.  The
accept family alone contributes `W * W + 1` clauses, which the doubled closed
form already records. -/
lemma descTableauCNF_clauses_ne_nil (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) (W T : ℕ) :
    (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses ≠ [] := by
  intro hnil
  have hlen : (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses.length = 0 := by
    rw [hnil]; rfl
  have h2 := descTableauCNF_length v d prefIdx freeLen allowedIdx outIdx W T
  rw [hlen] at h2
  omega

end NPComplete.CookLevin

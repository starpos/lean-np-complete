module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.SAT.ThreeSAT
public import NPComplete.BitEncoding

/-!
# Bit encoding of `ThreeCNF` and `ValidThreeCNF`

The prefix-free encoding makes the size of a 3-CNF instance explicit as a bit list. Its length
bounds both the declared variable count and the clause count, so size estimates in those parameters
can be expressed in terms of the encoded input length. The bounded-instance proof is a proposition,
so `ValidThreeCNF.encode` uses the same encoding as the underlying formula.
-/

@[expose] public section

namespace NPComplete.SAT

open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_append_inj encodeList_append_inj
   encodeNat_length)

/-- Encode a `Literal` as a polarity bit (`pos` → `false`, `neg` → `true`) followed by the
    variable index. -/
@[stable_api] def encodeLiteral : Literal → Bits
  | Literal.pos i => false :: encodeNat i
  | Literal.neg i => true :: encodeNat i

@[construction_api] lemma encodeLiteral_ends_true (l : Literal) :
    ∃ xs, encodeLiteral l = xs ++ [true] := by
  have hn (n : ℕ) : ∃ xs, encodeNat n = xs ++ [true] := by
    induction n with
    | zero => exact ⟨[], rfl⟩
    | succ n ih =>
      obtain ⟨xs, hxs⟩ := ih
      exact ⟨false :: xs, by simp [NPComplete.BitEncoding.encodeNat_succ, hxs]⟩
  cases l with
  | pos n =>
    obtain ⟨xs, hxs⟩ := hn n
    exact ⟨false :: xs, by simp [encodeLiteral, hxs]⟩
  | neg n =>
    obtain ⟨xs, hxs⟩ := hn n
    exact ⟨true :: xs, by simp [encodeLiteral, hxs]⟩

lemma encodeLiteral_append_inj {a b : Literal} {xs ys : Bits}
    (h : encodeLiteral a ++ xs = encodeLiteral b ++ ys) : a = b ∧ xs = ys := by
  cases a <;> cases b <;> simp only [encodeLiteral, List.cons_append, List.cons.injEq] at h
  · obtain ⟨heq, htail⟩ := encodeNat_append_inj h.2
    exact ⟨by rw [heq], htail⟩
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · obtain ⟨heq, htail⟩ := encodeNat_append_inj h.2
    exact ⟨by rw [heq], htail⟩

/-- Encode a `ThreeClause` as the concatenation of its three literal encodings — fixed arity, so
    no length prefix is needed (unlike `encodeList`). -/
@[stable_api] def encodeThreeClause (c : ThreeClause) : Bits :=
  encodeLiteral c.l1 ++ encodeLiteral c.l2 ++ encodeLiteral c.l3

lemma encodeThreeClause_append_inj {a b : ThreeClause} {xs ys : Bits}
    (h : encodeThreeClause a ++ xs = encodeThreeClause b ++ ys) : a = b ∧ xs = ys := by
  simp only [encodeThreeClause, List.append_assoc] at h
  obtain ⟨h1, hrest⟩ := encodeLiteral_append_inj h
  obtain ⟨h2, hrest⟩ := encodeLiteral_append_inj hrest
  obtain ⟨h3, htail⟩ := encodeLiteral_append_inj hrest
  refine ⟨?_, htail⟩
  cases a; cases b; simp_all

/-- Encode a `ThreeCNF` as `numVars` followed by the length-prefixed list of clause encodings. -/
@[stable_api] def encodeThreeCNF (f : ThreeCNF) : Bits :=
  encodeNat f.numVars ++ encodeList encodeThreeClause f.clauses

lemma encodeThreeCNF_append_inj {a b : ThreeCNF} {xs ys : Bits}
    (h : encodeThreeCNF a ++ xs = encodeThreeCNF b ++ ys) : a = b ∧ xs = ys := by
  simp only [encodeThreeCNF, List.append_assoc] at h
  obtain ⟨h1, hrest⟩ := encodeNat_append_inj h
  obtain ⟨h2, htail⟩ := encodeList_append_inj
    (fun {_ _ _ _} h => encodeThreeClause_append_inj h) hrest
  refine ⟨?_, htail⟩
  cases a; cases b; simp_all

lemma encodeThreeCNF_injective : Function.Injective encodeThreeCNF := by
  intro a b h
  exact (encodeThreeCNF_append_inj (xs := []) (ys := []) (by simpa using h)).1

/-- `encodeThreeCNF`'s two length contributors (`encodeNat numVars`'s prefix, `encodeList`'s
    length-prefix) both lower-bound the total, giving a two-for-one bound useful for converting
    a `numVars`/`clauses.length`-indexed polynomial into one indexed by the encoding length. -/
@[construction_api] lemma encodeThreeCNF_numVars_add_clauses_length_le (f : ThreeCNF) :
    f.numVars + f.clauses.length ≤ (encodeThreeCNF f).length := by
  unfold encodeThreeCNF
  simp only [List.length_append]
  have h1 := encodeNat_length f.numVars
  have h2 := encodeList_length_ge encodeThreeClause f.clauses
  omega

/-- Encode a `ValidThreeCNF`: the `Bounded` proof carries no data, so this is just
    `encodeThreeCNF` on the underlying formula. -/
@[stable_api] def ValidThreeCNF.encode (f : ValidThreeCNF) : Bits := encodeThreeCNF f.1

@[stable_api] lemma ValidThreeCNF.encode_injective : Function.Injective ValidThreeCNF.encode := by
  intro a b h
  exact Subtype.ext (encodeThreeCNF_injective h)

end NPComplete.SAT

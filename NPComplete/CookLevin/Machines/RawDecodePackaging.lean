module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.CookLevin.Machines.Drop
public import NPComplete.CookLevin.Machines.RawDecodeGeneric
public import NPComplete.SAT.ThreeCNFEncoding
public import NPComplete.CookLevin.ToThreeCNF.Encode

/-!
The step from a `TM2ComputableInPolyTime` producer to a `TM0ComputableInPolyTime`
one goes through a raw tape decode whose argument never inspects the produced
value: the simulation reads the output tape as an opaque bit list. Stating that
step once, against an abstract target encoding, keeps a second producer from
carrying its own copy of the same tape reasoning.

Two facts about the target encoding are all the decode needs: the encoded value
ends with a `true` (so trailing simulator padding can be dropped unambiguously)
and it is at least two bits long (so the decoded prefix has a nonempty tail).
Both are supplied here for the length-prefixed encodings this development uses.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BitEncoding
open NPComplete.SAT

/-! ## Encodings that end with a `true` bit -/

/-- `encodeNat` is unary with a terminating `1`. -/
@[construction_api] lemma encodeNat_ends_true (n : ℕ) : ∃ xs, encodeNat n = xs ++ [true] := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      obtain ⟨xs, hxs⟩ := ih
      exact ⟨false :: xs, by simp [encodeNat_succ, hxs]⟩

/-- A length-prefixed list inherits its last bit from its last element, or from
the `encodeNat` prefix when the list is empty.  Stating it once for an arbitrary
element encoder collapses the per-type repetitions this file would otherwise
need. -/
@[construction_api] lemma encodeList_ends_true {α : Type} (enc : α → Bits)
    (henc : ∀ a, ∃ ys, enc a = ys ++ [true]) (l : List α) :
    ∃ xs, encodeList enc l = xs ++ [true] := by
  induction l using List.reverseRecOn with
  | nil =>
      obtain ⟨xs, hxs⟩ := encodeNat_ends_true 0
      exact ⟨xs, by simpa [encodeList] using hxs⟩
  | append_singleton pre a _ =>
      obtain ⟨ys, hys⟩ := henc a
      refine ⟨encodeNat (pre.length + 1) ++ (pre.map enc).flatten ++ ys, ?_⟩
      simp [encodeList, hys, List.append_assoc]

lemma encodeLiteral_ends_true (l : Literal) :
    ∃ xs, encodeLiteral l = xs ++ [true] := by
  cases l with
  | pos n =>
      obtain ⟨xs, hxs⟩ := encodeNat_ends_true n
      exact ⟨false :: xs, by simp [encodeLiteral, hxs]⟩
  | neg n =>
      obtain ⟨xs, hxs⟩ := encodeNat_ends_true n
      exact ⟨true :: xs, by simp [encodeLiteral, hxs]⟩

lemma encodeClause_ends_true (c : Clause) :
    ∃ xs, encodeClause c = xs ++ [true] :=
  encodeList_ends_true _ encodeLiteral_ends_true _

lemma encodeCNF_ends_true (φ : CNF) : ∃ xs, encodeCNF φ = xs ++ [true] :=
  encodeList_ends_true _ encodeClause_ends_true _

/-! ## Length of an encoded CNF

`encodeCNF ⟨[]⟩` is the single bit `[true]`, so the two-bit lower bound the raw
decode needs holds exactly when the clause list is nonempty — which every
generator in this development satisfies, its accept and initial families each
contributing at least one clause. -/

lemma encodeCNF_length_two_of_ne_nil {φ : CNF} (h : φ.clauses ≠ []) :
    2 ≤ (encodeCNF φ).length := by
  have hge := encodeList_length_ge encodeClause φ.clauses
  have hpos : 0 < φ.clauses.length := List.length_pos_iff.mpr h
  simpa [encodeCNF] using by omega

end NPComplete.CookLevin

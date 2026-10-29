module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseEmitShape

/-!
The producer has to know how much room its output needs before it writes any of
it: the emitted region must stay clear of the control block, and the packaging
obligation asks for the output length to be polynomially bounded.

Both follow from three run-time quantities — how many clauses there are, how wide
the widest is, and how large the largest variable index is — without any argument
about the degree of the underlying polynomials.  The unary encoding is what makes
this work: a number costs its own value in bits, so a bound on the values bounds
the bits.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.BitEncoding
open NPComplete.SAT

lemma encodeLiteral_length_le (l : Literal) (V : ℕ) (h : litVar l ≤ V) :
    (NPComplete.SAT.encodeLiteral l).length ≤ V + 2 := by
  rw [encodeLiteral_eq_tag_var, List.length_append, encodeNat_length]
  simp only [List.length_singleton]
  omega

lemma flatten_length_le (L : List Literal) (V : ℕ) (hV : ∀ l ∈ L, litVar l ≤ V) :
    ((L.map NPComplete.SAT.encodeLiteral).flatten).length
      ≤ L.length * (V + 2) := by
  induction L with
  | nil => simp
  | cons l ls ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have h1 := encodeLiteral_length_le l V (hV l (by simp))
      have h2 := ih (fun l' hl' => hV l' (by simp [hl']))
      have h3 : (ls.length + 1) * (V + 2) = (V + 2) + ls.length * (V + 2) := by ring
      omega

lemma encodeClause_length_le (c : Clause) (V : ℕ) (hV : ∀ l ∈ c.lits, litVar l ≤ V) :
    (encodeClause c).length ≤ (c.lits.length + 1) + c.lits.length * (V + 2) := by
  rw [encodeClause, encodeList, List.length_append, encodeNat_length]
  have := flatten_length_le c.lits V hV
  omega

lemma clauses_flatten_length_le (cs : List Clause) (V L : ℕ)
    (hV : ∀ c ∈ cs, ∀ l ∈ c.lits, litVar l ≤ V)
    (hL : ∀ c ∈ cs, c.lits.length ≤ L) :
    ((cs.map encodeClause).flatten).length ≤ cs.length * ((L + 1) + L * (V + 2)) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have h1 : (encodeClause c).length ≤ (L + 1) + L * (V + 2) := by
        have hc := encodeClause_length_le c V (hV c (by simp))
        have hcL := hL c (by simp)
        have : c.lits.length * (V + 2) ≤ L * (V + 2) := Nat.mul_le_mul_right _ hcL
        omega
      have h2 := ih (fun c' hc' => hV c' (by simp [hc']))
        (fun c' hc' => hL c' (by simp [hc']))
      have h3 : (cs.length + 1) * ((L + 1) + L * (V + 2))
          = ((L + 1) + L * (V + 2)) + cs.length * ((L + 1) + L * (V + 2)) := by ring
      omega

/-- The encoded output's length, bounded by the clause count, the widest clause
and the largest variable index.  Every factor is a value the producer computes
anyway, so the room it must reserve is available before it starts writing. -/
lemma encodeCNF_length_le (φ : CNF) (V L : ℕ)
    (hV : ∀ c ∈ φ.clauses, ∀ l ∈ c.lits, litVar l ≤ V)
    (hL : ∀ c ∈ φ.clauses, c.lits.length ≤ L) :
    (encodeCNF φ).length
      ≤ (φ.clauses.length + 1) + φ.clauses.length * ((L + 1) + L * (V + 2)) := by
  rw [encodeCNF, encodeList, List.length_append, encodeNat_length]
  have := clauses_flatten_length_le φ.clauses V L hV hL
  omega

end NPComplete.CookLevin

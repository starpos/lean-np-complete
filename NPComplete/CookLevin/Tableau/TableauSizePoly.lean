module

public import NPComplete.CookLevin.ReductionProg.OutputLengthBound

/-!
Everything the producer must size in advance — where the control block sits, how
much room the output needs, how large an operand can get — has to be bounded by a
polynomial in the input length, because that is the shape the packaging
obligations are stated in.  The tableau's own dimensions are not polynomials on
the nose: the window size takes a `max`, and the time bound is the verifier's own
polynomial composed with another.

Replacing the `max` by a sum (`windowSize_le`) gives a majorant with non-negative
coefficients, which is monotone, so a single evaluation bounds every quantity
derived from it.  The verifier's polynomial and the certificate
polynomial are fixed once an implementation is chosen, so composing them is
legitimate even though their degrees are not literals.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial

lemma windowSize_le (inputLen outputLen T : ℕ) :
    windowSize inputLen outputLen T ≤ inputLen + outputLen + 2 * T + 1 := by
  unfold windowSize
  have : max inputLen outputLen ≤ inputLen + outputLen := by omega
  omega

/-- The verifier's time bound as a polynomial in the input length alone: its own
polynomial composed with the length of the paired input and certificate. -/
noncomputable def timePoly (p time : Polynomial ℕ) : Polynomial ℕ :=
  time.comp (2 * Polynomial.X + 1 + p)

lemma timePoly_eval (p time : Polynomial ℕ) (N : ℕ) :
    (timePoly p time).eval N = time.eval (2 * N + 1 + p.eval N) := by
  unfold timePoly
  simp [Polynomial.eval_comp]

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.Tableau.TableauSizePoly
public import NPComplete.CookLevin.Generate
public import NPComplete.CookLevin.Tableau.DenseLayout
public import NPComplete.CookLevin.Tableau.TableauRamLoops
public import NPComplete.CookLevin.Tableau.TableauVarBound

/-!
The packaging obligations are stated as bounds polynomial in the input length,
so every quantity the producer sizes in advance has to be pushed into that
shape.  The generator's window is taken at the *paired* input: `pairBits x []`
doubles the instance bits and adds a separator, so the input side is
`2 * N + 1 + p.eval N` (the time side is `timePoly`).

The paired majorant is given its own name here, and tied directly to
`boundedVerifierTimeBound`'s definition so downstream users never have to
unfold the pairing arithmetic again.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open Computability (encodeBool)
open NPComplete.RAMToTM

/-- The window majorant at the paired input: the instance contributes `2N + 1`
bits, the certificate `p.eval N`, the output one bit, and the tableau twice its
time bound. -/
noncomputable def cookWindowPoly (p time : Polynomial ℕ) : Polynomial ℕ :=
  (2 * Polynomial.X + 1 + p) + 1 + 2 * timePoly p time + 1

lemma cookWindowPoly_eval (p time : Polynomial ℕ) (N : ℕ) :
    (cookWindowPoly p time).eval N
      = (2 * N + 1 + p.eval N) + 1 + 2 * time.eval (2 * N + 1 + p.eval N) + 1 := by
  unfold cookWindowPoly
  simp [timePoly_eval]

/-- The generator's own window, bounded by a polynomial in the input length
alone.  Stated at `boundedVerifierTimeBound` and `boundedCertificateBound`
themselves, so a caller sizing the tableau needs no arithmetic of its own. -/
lemma cookWindowPoly_ge_target {α : Type} (enc : α → List Bool) (p : Polynomial ℕ)
    {V : α → List Bool → Bool}
    (hV : TM0ComputableInPolyTime
      (fun xw : α × List Bool => pairBits (enc xw.1) xw.2)
      encodeBool (fun xw => V xw.1 xw.2)) (x : α) :
    windowSize ((pairBits (enc x) []).length + boundedCertificateBound enc p x)
        (tapeSymbols [true]).length (boundedVerifierTimeBound enc p hV x)
      ≤ (cookWindowPoly p hV.time).eval (enc x).length := by
  have hlen : (pairBits (enc x) []).length = 2 * (enc x).length + 1 := by
    rw [pairBits_length]; simp
  have htape : (tapeSymbols [true]).length = 1 := rfl
  have h1 := windowSize_le ((pairBits (enc x) []).length + boundedCertificateBound enc p x)
    (tapeSymbols [true]).length (boundedVerifierTimeBound enc p hV x)
  rw [cookWindowPoly_eval, hlen, htape] at *
  unfold boundedVerifierTimeBound boundedCertificateBound at *
  omega

/-! ## The clause count, in a shape a polynomial can dominate

The exact count is a closed formula, but it carries truncated subtractions
(`k * (k - 1)`, from the pair counts the uniqueness family emits).  Truncated
subtraction is not monotone in the way a polynomial majorant needs — evaluating a
polynomial at a larger argument may not dominate a term the subtraction shrank —
so the count is first raised to a subtraction-free form.  The slack is one factor
of `k` on quadratic terms, which the majorant absorbs. -/

/-- The clause count without truncated subtraction, which makes every term
monotone in `W`, `T` and `freeLen` — the property a polynomial majorant needs. -/
lemma descTableauCNF_length_le_mono (v : ExecVarLayout) (d : TableauDescriptor)
    (prefIdx : List ℕ) (freeLen : ℕ) (allowedIdx outIdx : List ℕ) (W T : ℕ) :
    (descTableauCNF v d prefIdx freeLen allowedIdx outIdx W T).clauses.length
      ≤ (T + 1) * (d.numStates * d.numStates + 2 + (W * W + 2)
            + W * (d.numLetters * d.numLetters + 2))
        + (2 + W + freeLen)
        + T * W * d.numStates * d.numLetters * 3
        + T * W * W * d.numLetters
        + (W * W + 1) := by
  have h := descTableauCNF_length v d prefIdx freeLen allowedIdx outIdx W T
  have hn : d.numStates * (d.numStates - 1) ≤ d.numStates * d.numStates :=
    Nat.mul_le_mul_left _ (by omega)
  have hm : d.numLetters * (d.numLetters - 1) ≤ d.numLetters * d.numLetters :=
    Nat.mul_le_mul_left _ (by omega)
  have hW : W * (W - 1) ≤ W * W := Nat.mul_le_mul_left _ (by omega)
  have hTW : T * W * (W - 1) ≤ T * W * W := Nat.mul_le_mul_left _ (by omega)
  have hTWm : T * W * (W - 1) * d.numLetters ≤ T * W * W * d.numLetters :=
    Nat.mul_le_mul_right _ hTW
  have hmul : (T + 1) * (d.numStates * (d.numStates - 1) + 2 + (W * (W - 1) + 2)
        + W * (d.numLetters * (d.numLetters - 1) + 2))
      ≤ (T + 1) * (d.numStates * d.numStates + 2 + (W * W + 2)
        + W * (d.numLetters * d.numLetters + 2)) := by
    apply Nat.mul_le_mul_left
    have := Nat.mul_le_mul_left W (Nat.add_le_add_right hm 2)
    omega
  omega

/-! ## Variable numbers

A dense-layout variable number is an offset inside one of `T + 1` blocks, so it
is under `(T + 1) * denseBlock`.  With the state and letter counts fixed by the
verifier, that is a polynomial in the input length. -/

/-- Majorant for the variable numbers the generator writes. -/
noncomputable def varBoundPoly (p time : Polynomial ℕ) (n m : ℕ) : Polynomial ℕ :=
  (timePoly p time + 1) * (C n + cookWindowPoly p time + cookWindowPoly p time * C m)

lemma varBoundPoly_eval (p time : Polynomial ℕ) (n m N : ℕ) :
    (varBoundPoly p time n m).eval N
      = ((timePoly p time).eval N + 1) *
          (n + (cookWindowPoly p time).eval N + (cookWindowPoly p time).eval N * m) := by
  simp [varBoundPoly]

/-! ## The output length, in a shape a polynomial can dominate

`descTableauCNF_length_le_mono` gives the clause count; `descTableauCNF_var_le`
and `descTableauCNF_width_le` (`TableauVarBound.lean`) give the largest
variable and widest clause.  `encodeCNF_length_le` combines the three into an
output-length bound, so embedding all three as polynomials in the input length
is what lets the setup workspace be sized against the generator's own output
without any per-input arithmetic. -/

/-- `descTableauCNF_length_le_mono` with the window, time, and free-input
length embedded as polynomial expressions. -/
noncomputable def clauseCountPoly (p time : Polynomial ℕ) (n m : ℕ) : Polynomial ℕ :=
  (timePoly p time + 1) * (Polynomial.C (n * n) + 2
      + (cookWindowPoly p time * cookWindowPoly p time + 2)
      + cookWindowPoly p time * (Polynomial.C (m * m) + 2))
    + (2 + cookWindowPoly p time + p)
    + timePoly p time * cookWindowPoly p time * Polynomial.C (n * m * 3)
    + timePoly p time * (cookWindowPoly p time * cookWindowPoly p time) * Polynomial.C m
    + (cookWindowPoly p time * cookWindowPoly p time + 1)

/-- A sum majorizes the maximum clause width for the dense tableau. -/
noncomputable def emitWidthPoly (p time : Polynomial ℕ) (n m al : ℕ) : Polynomial ℕ :=
  Polynomial.C n + cookWindowPoly p time + Polynomial.C m + Polynomial.C al + Polynomial.C 7

/-- The polynomial output-length majorant obtained from clause count, width,
and variable-number bounds. -/
noncomputable def emitLenPoly (p time : Polynomial ℕ) (n m al : ℕ) : Polynomial ℕ :=
  clauseCountPoly p time n m + 1 +
    clauseCountPoly p time n m *
      ((emitWidthPoly p time n m al + 1)
        + emitWidthPoly p time n m al * (varBoundPoly p time n m + 2))

/-- The clause count fits under `clauseCountPoly` at the paired input size, using the
    subtraction-free generic bound and the layout's `n + 1`/`m + 1` clause-count shape. -/
lemma emitLenPoly_ge_encodeCNF_clause_count (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval N) (d.numLetters + 1))
      d prefIdx (p.eval N) allowedIdx outIdx
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)).clauses.length
    ≤ (clauseCountPoly p time (d.numStates + 1) (d.numLetters + 1)).eval N := by
  set W := (cookWindowPoly p time).eval N with hWdef
  set T := (timePoly p time).eval N with hTdef
  set P := p.eval N with hPdef
  set n := d.numStates + 1 with hndef
  set m := d.numLetters + 1 with hmdef
  have hc := descTableauCNF_length_le_mono (denseLayout n W m) d prefIdx P allowedIdx
    outIdx W T
  have heval : (clauseCountPoly p time n m).eval N =
      (T + 1) * (n * n + 2 + (W * W + 2) + W * (m * m + 2))
        + (2 + W + P)
        + T * W * (n * m * 3)
        + T * (W * W) * m
        + (W * W + 1) := by
    simp [clauseCountPoly, hTdef, hWdef, hPdef, hndef, hmdef]
  rw [heval, hndef, hmdef]
  have hn : d.numStates * d.numStates ≤ (d.numStates + 1) * (d.numStates + 1) := by
    nlinarith
  have hm : d.numLetters * d.numLetters ≤ (d.numLetters + 1) * (d.numLetters + 1) := by
    nlinarith
  have hi : d.numStates * d.numStates + 2 + (W * W + 2)
        + W * (d.numLetters * d.numLetters + 2) ≤
      (d.numStates + 1) * (d.numStates + 1) + 2 + (W * W + 2)
        + W * ((d.numLetters + 1) * (d.numLetters + 1) + 2) := by
    have hwm := Nat.mul_le_mul_left W (Nat.add_le_add_right hm 2)
    omega
  have hfirst := Nat.mul_le_mul_left (T + 1) hi
  have hcross : d.numStates * d.numLetters * 3
      ≤ (d.numStates + 1) * (d.numLetters + 1) * 3 := by
    nlinarith
  have hthird : T * W * d.numStates * d.numLetters * 3 ≤
      T * W * ((d.numStates + 1) * (d.numLetters + 1) * 3) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (T * W) hcross
  have hfourth : T * W * W * d.numLetters ≤ T * (W * W) * (d.numLetters + 1) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (T * (W * W)) (by omega)
  have hs :
      (T + 1) * (d.numStates * d.numStates + 2 + (W * W + 2)
          + W * (d.numLetters * d.numLetters + 2))
        + (2 + W + P)
        + T * W * d.numStates * d.numLetters * 3
        + T * W * W * d.numLetters
        + (W * W + 1)
      ≤
      (T + 1) * ((d.numStates + 1) * (d.numStates + 1) + 2 + (W * W + 2)
          + W * ((d.numLetters + 1) * (d.numLetters + 1) + 2))
        + (2 + W + P)
        + T * W * ((d.numStates + 1) * (d.numLetters + 1) * 3)
        + T * (W * W) * (d.numLetters + 1)
        + (W * W + 1) := by
    omega
  exact hc.trans hs

/-- The dense tableau's clause-width bound fits the additive shape used by `emitWidthPoly`. -/
lemma emitLenPoly_ge_encodeCNF_width_shape (d : TableauDescriptor) (W al : ℕ) :
    max (max (max d.numStates W) d.numLetters + 2) (max (1 + al) 4) ≤
      d.numStates + 1 + W + (d.numLetters + 1) + al + 7 := by
  have hstate : max (max d.numStates W) d.numLetters ≤ d.numStates + W + d.numLetters := by
    refine Nat.max_le.mpr ?_
    constructor
    · refine Nat.max_le.mpr ?_
      constructor <;> omega
    · omega
  have hA : max (max d.numStates W) d.numLetters + 2 ≤
      d.numStates + 1 + W + (d.numLetters + 1) + al + 7 := by omega
  have hB : max (1 + al) 4 ≤
      d.numStates + 1 + W + (d.numLetters + 1) + al + 7 := by omega
  exact Nat.max_le.mpr ⟨hA, hB⟩

/-- The output-length polynomial is monotone in the clause-count argument. -/
lemma emitLenPoly_ge_encodeCNF_from_count (p time : Polynomial ℕ) (n m al N c : ℕ)
    (hc : c ≤ (clauseCountPoly p time n m).eval N) :
    c + 1 + c * ((emitWidthPoly p time n m al).eval N + 1
        + (emitWidthPoly p time n m al).eval N * ((varBoundPoly p time n m).eval N + 2)) ≤
      (emitLenPoly p time n m al).eval N := by
  have heval : (emitLenPoly p time n m al).eval N =
      (clauseCountPoly p time n m).eval N + 1
        + (clauseCountPoly p time n m).eval N *
          ((emitWidthPoly p time n m al).eval N + 1
            + (emitWidthPoly p time n m al).eval N * ((varBoundPoly p time n m).eval N + 2)) := by
    simp [emitLenPoly]
  rw [heval]
  gcongr

/-- The encoded tableau CNF fits under `emitLenPoly` at the paired input size. -/
lemma emitLenPoly_ge_encodeCNF (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefIdx, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1)
    (hprefLen : prefIdx.length ≤ 2 * N + 1) :
    (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval N) (d.numLetters + 1))
      d prefIdx (p.eval N) allowedIdx outIdx
      ((cookWindowPoly p time).eval N) ((timePoly p time).eval N))).length
    ≤ (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N := by
  let W := (cookWindowPoly p time).eval N
  let T := (timePoly p time).eval N
  let P := p.eval N
  let n := d.numStates + 1
  let m := d.numLetters + 1
  let al := allowedIdx.length
  let φ := descTableauCNF (denseLayout n W m) d prefIdx P allowedIdx outIdx W T
  have hbound : T + prefIdx.length + P < W := by
    dsimp [W, T, P]
    have hT : time.eval (2 * N + 1 + p.eval N) = (timePoly p time).eval N := by
      symm
      exact timePoly_eval p time N
    rw [cookWindowPoly_eval, hT]
    omega
  have hv := descTableauCNF_var_le n W m T d prefIdx P allowedIdx outIdx
    (by dsimp [n]; omega) (by dsimp [m]; omega) hwrite hblank hpref hallowed hout hbound
  have hV : ∀ c ∈ φ.clauses, ∀ l ∈ c.lits, litVar l ≤
      (varBoundPoly p time n m).eval N := by
    intro c hc l hl
    have hlt := hv c hc l hl
    have heval : (varBoundPoly p time n m).eval N = (T + 1) * (n + W + W * m) := by
      simpa [T, W, n, m] using varBoundPoly_eval p time n m N
    rw [heval]
    exact Nat.le_of_lt hlt
  have hw := descTableauCNF_width_le (denseLayout n W m) d prefIdx P allowedIdx outIdx W T
  have hL : ∀ c ∈ φ.clauses, c.lits.length ≤
      (emitWidthPoly p time n m al).eval N := by
    intro c hc
    have hmax := hw c hc
    have hsum : max (max (max d.numStates W) d.numLetters + 2)
        (max (1 + allowedIdx.length) 4) ≤ n + W + m + al + 7 := by
      simpa [n, m, al] using
        emitLenPoly_ge_encodeCNF_width_shape d W allowedIdx.length
    have heval : (emitWidthPoly p time n m al).eval N = n + W + m + al + 7 := by
      simp [emitWidthPoly, W, n, m, al]
    rw [heval]
    exact hmax.trans hsum
  have hC := emitLenPoly_ge_encodeCNF_clause_count p time d prefIdx allowedIdx outIdx N
  have henc := encodeCNF_length_le φ
      (Polynomial.eval N (varBoundPoly p time n m))
      (Polynomial.eval N (emitWidthPoly p time n m al)) hV hL
  have hfinal := emitLenPoly_ge_encodeCNF_from_count p time n m al N φ.clauses.length
    (by simpa [φ, n, m, W, T, P] using hC)
  simpa [φ] using henc.trans hfinal

end NPComplete.CookLevin

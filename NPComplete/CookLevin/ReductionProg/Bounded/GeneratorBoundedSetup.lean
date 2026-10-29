module

public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelope
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedWrite
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyInitCheck

/-!
The setup layer is the one place a Horner expression's *own constants* sit as
subterms rather than merely shaping an evaluation, and the one place
`paramSetupWrites`'s uniform write engine has to be discharged for a bound
rather than for a value.  Both obligations are proved here in the general
shape the coefficients or the pair list come in, so a concrete instance
(`setupProg`, `generatorLayoutProg`) only has to supply the arithmetic
inequalities its own envelope satisfies.

The Horner bound needs two majorants of a polynomial `q`, not one:
`q.eval 1` for the constants (`ExprBoundedIn` charges a `.const` by its own
value, so the coefficients are subterms no evaluation bound reaches), and
`q.eval (N + 1)` for every suffix's intermediate value — `q.comp (X + 1)` is
the shift `GeneratorEnvelope`'s module comment names for exactly this. The
multiplicative step additionally needs the product `N * q.eval (N + 1)`
bounded on its own: folding it into the same envelope as the factors would
force `N * B ≤ B`, which holds only at `N = 0`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Horner's evaluation is monotone in its argument

Every coefficient is non-negative, so increasing the point of evaluation can
only raise `hornerVal`. -/

lemma hornerVal_mono (coeffs : List ℕ) :
    ∀ x y : ℕ, x ≤ y → hornerVal coeffs x ≤ hornerVal coeffs y := by
  induction coeffs with
  | nil => intro x y _; simp [hornerVal]
  | cons c cs ih =>
    intro x y hxy
    show c + x * hornerVal cs x ≤ c + y * hornerVal cs y
    have h1 := ih x y hxy
    have h2 : x * hornerVal cs x ≤ y * hornerVal cs y := by
      calc x * hornerVal cs x ≤ y * hornerVal cs x := Nat.mul_le_mul_right _ hxy
        _ ≤ y * hornerVal cs y := Nat.mul_le_mul_left _ h1
    omega

/-- Every suffix of a Horner list evaluates at `x` under the full list's value
at `x + 1`: dropping a prefix only removes non-negative leading terms, and the
remaining terms carry one fewer power of `x` each, which `x < x + 1` covers. -/
lemma hornerVal_drop_le (coeffs : List ℕ) (x k : ℕ) :
    hornerVal (coeffs.drop k) x ≤ hornerVal coeffs (x + 1) := by
  induction coeffs generalizing k with
  | nil => simp [hornerVal]
  | cons c cs ih =>
    cases k with
    | zero =>
      simp only [List.drop_zero]
      exact hornerVal_mono (c :: cs) x (x + 1) (by omega)
    | succ k' =>
      simp only [List.drop_succ_cons]
      have h1 := ih k'
      show hornerVal (cs.drop k') x ≤ c + (x + 1) * hornerVal cs (x + 1)
      have h2 : hornerVal cs (x + 1) ≤ (x + 1) * hornerVal cs (x + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

/-! ## `ExprBoundedIn` for a Horner expression

`V` bounds every suffix's value at the shifted point, kept apart from `B` so
the multiplicative step reads `e.eval σ * V ≤ B` instead of collapsing to the
vacuous `N * B ≤ B`. -/

/-- A Horner expression is bounded once its coefficients are all `≤ B`, its
base expression is bounded, and every suffix's value at the base's evaluation
stays under a separate cap `V` whose product with that evaluation fits `B`. -/
lemma exprBoundedIn_hornerExpr (B V : ℕ) (σ : Store) (e : Expr) (coeffs : List ℕ)
    (he : ExprBoundedIn B σ e) (hVB : V ≤ B) (hmul : e.eval σ * V ≤ B)
    (hC : ∀ c ∈ coeffs, c ≤ B)
    (hV : ∀ k, hornerVal (coeffs.drop k) (e.eval σ) ≤ V) :
    ExprBoundedIn B σ (hornerExpr coeffs e) := by
  induction coeffs with
  | nil => simp [hornerExpr, ExprBoundedIn]
  | cons c cs ih =>
    have hstep : hornerExpr (c :: cs) e =
        Expr.add (Expr.const c) (Expr.mul e (hornerExpr cs e)) := rfl
    rw [hstep]
    have hCtail : ∀ c' ∈ cs, c' ≤ B := fun c' hc' => hC c' (List.mem_cons_of_mem _ hc')
    have hVtail : ∀ k, hornerVal (cs.drop k) (e.eval σ) ≤ V := fun k => by
      have := hV (k + 1); simpa using this
    have hIH : ExprBoundedIn B σ (hornerExpr cs e) := ih hCtail hVtail
    have hc0 : c ≤ B := hC c List.mem_cons_self
    have hval : (hornerExpr cs e).eval σ = hornerVal cs (e.eval σ) := hornerExpr_eval cs e σ
    have hV1 : hornerVal cs (e.eval σ) ≤ V := by simpa using hVtail 0
    have hmulcs : e.eval σ * (hornerExpr cs e).eval σ ≤ B := by
      rw [hval]
      calc e.eval σ * hornerVal cs (e.eval σ) ≤ e.eval σ * V := Nat.mul_le_mul_left _ hV1
        _ ≤ B := hmul
    refine ⟨hc0, ⟨he, hIH, hmulcs⟩, ?_⟩
    have hV0 : hornerVal (c :: cs) (e.eval σ) ≤ V := by simpa using hV 0
    have hval2 : hornerVal (c :: cs) (e.eval σ) = c + e.eval σ * hornerVal cs (e.eval σ) := rfl
    simp only [Expr.eval, hval]
    omega

/-- The setup layer's own shape: `coeffList q` on `Expr.reg 0`, where `V` is
resolved to `q.eval (N + 1)` and the coefficient cap to `q.eval 1`. -/
lemma exprBoundedIn_hornerExpr_reg0 (B N : ℕ) (σ : Store) (h0 : σ 0 = N)
    (q : Polynomial ℕ) (h1 : q.eval 1 ≤ B) (hshift : q.eval (N + 1) ≤ B)
    (hmul : N * q.eval (N + 1) ≤ B) :
    ExprBoundedIn B σ (hornerExpr (coeffList q) (Expr.reg 0)) := by
  have he : ExprBoundedIn B σ (Expr.reg 0) := by simp only [ExprBoundedIn]; omega
  have heval : (Expr.reg 0).eval σ = N := by simp [Expr.eval, h0]
  refine exprBoundedIn_hornerExpr B (q.eval (N + 1)) σ (Expr.reg 0) (coeffList q) he hshift
    ?_ ?_ ?_
  · rw [heval]; exact hmul
  · intro c hc
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < polyLen q ∧ c = q.coeff i := by
      obtain ⟨i, hilt, hival⟩ := List.mem_iff_getElem.mp hc
      simp only [coeffList, List.getElem_map, List.getElem_range] at hival
      exact ⟨i, by simpa [coeffList_length] using hilt, hival.symm⟩
    exact (coeff_le_eval_one q i).trans h1
  · intro k
    rw [heval]
    calc hornerVal ((coeffList q).drop k) N ≤ hornerVal (coeffList q) (N + 1) :=
          hornerVal_drop_le (coeffList q) N k
      _ = q.eval (N + 1) := hornerVal_coeffList q (N + 1)

/-! ## `ProgramBoundedIn` for `paramSetupWrites`

The engine's `.seq` unfolds one write at a time, each changing the store, so a
per-store hypothesis on address and value expressions must hold at every store
reached by the induction, not only at the entry store `σ`.

`Reg0Expr e` guarantees equal evaluations at stores with the same register `0`,
but it does not preserve `ExprBoundedIn`: for `e = .sub (.reg 5) (.reg 5)`,
`e` evaluates to `0` everywhere while `ExprBoundedIn` also requires the left
operand `τ 5` to be bounded.  Thus the hypotheses below quantify over all stores
whose register `0` contains the entry length `N`, providing the required bounds
at every intermediate store. -/

/-- Every write in `paramSetupWrites mE pairs` stays bounded, given that the
address expression `mE` and each pair's value expression are bounded — and
land within `B` at address `mE + j` — at *every* store whose register `0`
holds the input length `N`, not merely at the entry store. -/
lemma programBoundedIn_paramSetupWrites (B N : ℕ) (mE : Expr)
    (pairs : List (ℕ × Expr)) (σ : Store) (hσ0 : σ 0 = N)
    (hpos : ∀ j ∈ pairs.map Prod.fst, 1 ≤ j)
    (hmEb : ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ mE)
    (haddr : ∀ j ∈ pairs.map Prod.fst, ∀ τ : Store, τ 0 = N → mE.eval τ + j ≤ B)
    (hval : ∀ q ∈ pairs, ∀ τ : Store, τ 0 = N → ExprBoundedIn B τ q.2) :
    ProgramBoundedIn B σ (paramSetupWrites mE pairs) := by
  induction pairs generalizing σ with
  | nil => simp [paramSetupWrites, ProgramBoundedIn]
  | cons q rest ih =>
    obtain ⟨j, e⟩ := q
    have hj1 : 1 ≤ j := hpos j (by simp)
    have hmEσ : ExprBoundedIn B σ mE := hmEb σ hσ0
    have haddrσ : mE.eval σ + j ≤ B := haddr j (by simp) σ hσ0
    have hvalσ : ExprBoundedIn B σ e := hval (j, e) List.mem_cons_self σ hσ0
    have hassign : ProgramBoundedIn B σ (paramSetupAssign mE j e) := by
      unfold paramSetupAssign
      refine ⟨⟨hmEσ, by simp only [ExprBoundedIn]; omega, ?_⟩, hvalσ, ?_⟩ <;>
        · simp only [Expr.eval]; omega
    have hσ'0 : (paramSetupAssign mE j e).eval σ 0 = N := by
      rw [paramSetupAssign_zero mE j e σ hj1, hσ0]
    have htail : ProgramBoundedIn B ((paramSetupAssign mE j e).eval σ)
        (paramSetupWrites mE rest) := by
      apply ih ((paramSetupAssign mE j e).eval σ) hσ'0
      · intro j' hj'; exact hpos j' (by simp [hj'])
      · intro j' hj' τ hτ; exact haddr j' (by simp [hj']) τ hτ
      · intro q' hq' τ hτ; exact hval q' (by simp [hq']) τ hτ
    simpa [paramSetupWrites, ProgramBoundedIn] using ⟨hassign, htail⟩

/-! ## The workspace base's own expressions

`setupSpanE p` and `setupME p` are exactly the shape `exprBoundedIn_hornerExpr`
and its `.mul`/`.add` combinators cover: a Horner term for `p`'s coefficients,
a `2 * reg 0 + 3` term, and a cube of the sum plus a compile-time constant.
Bounding them once here is what lets every parameter cell that reads `setupME
p` — nine of them in `setupPairs`, eight more in `generatorLayoutPairs` —
discharge its own address bound by a single lemma application. -/

/-- A cheap generic step: `.add e (.const c)` is bounded once `e` is and the
sum with `c` fits `B`. -/
lemma exprBoundedIn_add_const (B c : ℕ) (σ : Store) (e : Expr)
    (he : ExprBoundedIn B σ e) (hvc : e.eval σ + c ≤ B) :
    ExprBoundedIn B σ (Expr.add e (Expr.const c)) := by
  refine ⟨he, by simp only [ExprBoundedIn]; omega, ?_⟩
  simp only [Expr.eval]; omega

/-- `setupSpanE p`'s bound: the `2N + 3` term is direct arithmetic, the Horner
term is `exprBoundedIn_hornerExpr_reg0`, and their sum is `setupSpan p N`
itself. -/
lemma exprBoundedIn_setupSpanE (B N : ℕ) (p : Polynomial ℕ) (σ : Store) (h0 : σ 0 = N)
    (h1 : p.eval 1 ≤ B) (hshift : p.eval (N + 1) ≤ B) (hmul : N * p.eval (N + 1) ≤ B)
    (hspan : setupSpan p N ≤ B) :
    ExprBoundedIn B σ (setupSpanE p) := by
  unfold setupSpanE
  have hB2 : 2 ≤ B := by unfold setupSpan at hspan; omega
  have h2N : ExprBoundedIn B σ (Expr.mul (Expr.const 2) (Expr.reg 0)) := by
    refine ⟨hB2, by simp only [ExprBoundedIn]; omega, ?_⟩
    simp only [Expr.eval, h0]; unfold setupSpan at hspan; omega
  have h2Neval : (Expr.mul (Expr.const 2) (Expr.reg 0)).eval σ = 2 * N := by simp [Expr.eval, h0]
  have hleft : ExprBoundedIn B σ (Expr.add (Expr.mul (Expr.const 2) (Expr.reg 0)) (Expr.const 3)) :=
    exprBoundedIn_add_const B 3 σ _ h2N (by rw [h2Neval]; unfold setupSpan at hspan; omega)
  have hlefteval :
      (Expr.add (Expr.mul (Expr.const 2) (Expr.reg 0)) (Expr.const 3)).eval σ = 2 * N + 3 := by
    simp [Expr.eval, h0]
  have hright : ExprBoundedIn B σ (hornerExpr (coeffList p) (Expr.reg 0)) :=
    exprBoundedIn_hornerExpr_reg0 B N σ h0 p h1 hshift hmul
  refine ⟨hleft, hright, ?_⟩
  rw [hlefteval, hornerExpr_coeffList_eval]
  simp only [Expr.eval, h0]
  unfold setupSpan at hspan; omega

/-- `setupME p time d allowedIdx`'s bound: the cube of `setupSpanE p`, from the
intermediate square's own bound and the constant `30`, then the Horner term
for `emitLenPoly`'s output-length majorant via `exprBoundedIn_hornerExpr_reg0`
— the same pattern already used for `p`, `cookWindowPoly` and `timePoly`. -/
lemma exprBoundedIn_setupME (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store)
    (hspanE : ExprBoundedIn B σ (setupSpanE p))
    (hspaneval : (setupSpanE p).eval σ = setupSpan p N)
    (h0 : σ 0 = N)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hmule : N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hM : setupM p time d allowedIdx N ≤ B) :
    ExprBoundedIn B σ (setupME p time d allowedIdx) := by
  unfold setupME
  have hspanpos : 1 ≤ setupSpan p N := by unfold setupSpan; omega
  have hMdef : setupM p time d allowedIdx N =
      setupSpan p N * (setupSpan p N * setupSpan p N) + 30
        + (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
            allowedIdx.length).eval N := rfl
  have hcube : setupSpan p N * (setupSpan p N * setupSpan p N) ≤ B := by omega
  have hsqle : setupSpan p N * setupSpan p N ≤ setupSpan p N * (setupSpan p N * setupSpan p N) := by
    calc setupSpan p N * setupSpan p N = setupSpan p N * setupSpan p N * 1 := by ring
      _ ≤ setupSpan p N * setupSpan p N * setupSpan p N := Nat.mul_le_mul_left _ hspanpos
      _ = setupSpan p N * (setupSpan p N * setupSpan p N) := by ring
  have hsq : ExprBoundedIn B σ (Expr.mul (setupSpanE p) (setupSpanE p)) :=
    ⟨hspanE, hspanE, by rw [hspaneval]; exact hsqle.trans hcube⟩
  have hcubeE :
      ExprBoundedIn B σ (Expr.mul (setupSpanE p) (Expr.mul (setupSpanE p) (setupSpanE p))) := by
    refine ⟨hspanE, hsq, ?_⟩
    show (setupSpanE p).eval σ * ((setupSpanE p).eval σ * (setupSpanE p).eval σ) ≤ B
    rw [hspaneval]; exact hcube
  have h30 : (30 : ℕ) ≤ B := by omega
  have hleft : ExprBoundedIn B σ (Expr.add
      (Expr.mul (setupSpanE p) (Expr.mul (setupSpanE p) (setupSpanE p))) (Expr.const 30)) := by
    refine ⟨hcubeE, h30, ?_⟩
    show (setupSpanE p).eval σ * ((setupSpanE p).eval σ * (setupSpanE p).eval σ) + 30 ≤ B
    rw [hspaneval]; omega
  have hright : ExprBoundedIn B σ (hornerExpr (coeffList (emitLenPoly p time
      (d.numStates + 1) (d.numLetters + 1) allowedIdx.length)) (Expr.reg 0)) :=
    exprBoundedIn_hornerExpr_reg0 B N σ h0
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length)
      h1e hshifte hmule
  refine ⟨hleft, hright, ?_⟩
  have hlefteval :
      (Expr.add (Expr.mul (setupSpanE p) (Expr.mul (setupSpanE p) (setupSpanE p)))
        (Expr.const 30)).eval σ
      = setupSpan p N * (setupSpan p N * setupSpan p N) + 30 := by
    simp only [Expr.eval]; rw [hspaneval]
  have hrighteval : (hornerExpr (coeffList (emitLenPoly p time (d.numStates + 1)
      (d.numLetters + 1) allowedIdx.length)) (Expr.reg 0)).eval σ
      = (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval N := by
    rw [hornerExpr_coeffList_eval]; simp [Expr.eval, h0]
  rw [hlefteval, hrighteval]; omega

/-- The bound for `setupME p time d allowedIdx` composed with a constant add,
    as used for the five base cells in `setupPairs` at offsets `30` through `70`. -/
lemma exprBoundedIn_setupME_add_const (B N c : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (h1 : p.eval 1 ≤ B) (hshift : p.eval (N + 1) ≤ B) (hmul : N * p.eval (N + 1) ≤ B)
    (hspan : setupSpan p N ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hmule : N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hMc : setupM p time d allowedIdx N + c ≤ B) :
    ExprBoundedIn B σ (Expr.add (setupME p time d allowedIdx) (Expr.const c)) := by
  have hspanE := exprBoundedIn_setupSpanE B N p σ h0 h1 hshift hmul hspan
  have hspaneval := setupSpanE_eval p σ N h0
  have hMe := exprBoundedIn_setupME B N p time d allowedIdx σ hspanE hspaneval h0
    h1e hshifte hmule (by omega)
  have hMeval := setupME_eval p time d allowedIdx σ N h0
  exact exprBoundedIn_add_const B c σ (setupME p time d allowedIdx) hMe
    (by rw [hMeval]; exact hMc)

/-! ## `setupProg`

`setupPairs` supplies nine cells: three Horner evaluations at register `0`
(the window, the time bound, the free length), the staged prefix length
`2N + 1`, and five constant offsets from `setupME p`. Every bound below is a
direct application of one lemma above, so the proof only routes
`setupPairs`'s own case split to the matching lemma. -/

/-- `generatorPrefLenE`'s own bound: `2 * reg 0 + 1`, direct from `2N + 1 ≤ B`. -/
lemma exprBoundedIn_generatorPrefLenE (B N : ℕ) (τ : Store) (hτ : τ 0 = N) (hB2 : 2 ≤ B)
    (hpref : 2 * N + 1 ≤ B) :
    ExprBoundedIn B τ generatorPrefLenE := by
  unfold generatorPrefLenE
  have hmulB : ExprBoundedIn B τ (Expr.mul (Expr.const 2) (Expr.reg 0)) := by
    refine ⟨hB2, by simp only [ExprBoundedIn]; omega, ?_⟩
    simp only [Expr.eval, hτ]; omega
  refine ⟨hmulB, by simp only [ExprBoundedIn]; omega, ?_⟩
  simp only [Expr.eval, hτ]; omega

/-- `setupProg p time d allowedIdx` stays bounded by `B` at any store holding
the input length `N`, given the coefficient/shift/product majorants of `p`,
`time`'s composed time and window polynomials and of `emitLenPoly`, the
staged prefix length, and enough room past `setupME p time d allowedIdx` for
the five constant-offset cells. -/
lemma programBoundedIn_setupProg (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (hσ0 : σ 0 = N)
    (h1p : p.eval 1 ≤ B) (hsp : p.eval (N + 1) ≤ B) (hmp : N * p.eval (N + 1) ≤ B)
    (hspan : setupSpan p N ≤ B)
    (h1w : (cookWindowPoly p time).eval 1 ≤ B) (hsw : (cookWindowPoly p time).eval (N + 1) ≤ B)
    (hmw : N * (cookWindowPoly p time).eval (N + 1) ≤ B)
    (h1t : (timePoly p time).eval 1 ≤ B) (hst : (timePoly p time).eval (N + 1) ≤ B)
    (hmt : N * (timePoly p time).eval (N + 1) ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hmule : N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hpref : 2 * N + 1 ≤ B) (hM70 : setupM p time d allowedIdx N + 70 ≤ B) :
    ProgramBoundedIn B σ (setupProg p time d allowedIdx) := by
  unfold setupProg
  apply programBoundedIn_paramSetupWrites B N (setupME p time d allowedIdx)
    (setupPairs p time d allowedIdx) σ hσ0 (setupPairs_pos p time d allowedIdx)
  · intro τ hτ
    exact exprBoundedIn_setupME B N p time d allowedIdx τ
      (exprBoundedIn_setupSpanE B N p τ hτ h1p hsp hmp hspan) (setupSpanE_eval p τ N hτ) hτ
      h1e hshifte hmule (by omega)
  · intro j hj τ hτ
    have hMeval := setupME_eval p time d allowedIdx τ N hτ
    have hj23 : j ≤ 23 := by
      simp only [setupPairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [persistWReg, persistTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg,
          transKindBaseReg, transArg1BaseReg, transArg2BaseReg, acceptOutBaseReg]
    rw [hMeval]; omega
  · intro q hq τ hτ
    simp only [setupPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact exprBoundedIn_hornerExpr_reg0 B N τ hτ (cookWindowPoly p time) h1w hsw hmw
    · exact exprBoundedIn_hornerExpr_reg0 B N τ hτ (timePoly p time) h1t hst hmt
    · exact exprBoundedIn_hornerExpr_reg0 B N τ hτ p h1p hsp hmp
    · exact exprBoundedIn_generatorPrefLenE B N τ hτ (by omega) hpref
    · exact exprBoundedIn_setupME_add_const B N 30 p time d allowedIdx τ hτ h1p hsp hmp hspan
        h1e hshifte hmule (by omega)
    · exact exprBoundedIn_setupME_add_const B N 40 p time d allowedIdx τ hτ h1p hsp hmp hspan
        h1e hshifte hmule (by omega)
    · exact exprBoundedIn_setupME_add_const B N 50 p time d allowedIdx τ hτ h1p hsp hmp hspan
        h1e hshifte hmule (by omega)
    · exact exprBoundedIn_setupME_add_const B N 60 p time d allowedIdx τ hτ h1p hsp hmp hspan
        h1e hshifte hmule (by omega)
    · exact exprBoundedIn_setupME_add_const B N 70 p time d allowedIdx τ hτ h1p hsp hmp hspan
        h1e hshifte hmule (by omega)

/-! ## `generatorLayoutProg`

`generatorLayoutPairs` chains five staged-word bases (`generatorPrefBaseE` up
to `generatorOutBaseE`), each a constant offset from the one before, and the
table base repeated three times.  Each bound below is `setupME`'s or its
predecessor's bound composed with one more `.add`/`.const`, using the
generator's own `_eval` lemmas to identify the evaluation each step needs. -/

lemma exprBoundedIn_generatorPrefBaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store)
    (hMe : ExprBoundedIn B σ (setupME p time d allowedIdx))
    (hMeval : (setupME p time d allowedIdx).eval σ = setupM p time d allowedIdx N)
    (hMc : setupM p time d allowedIdx N + generatorPrefOffset ≤ B) :
    ExprBoundedIn B σ (generatorPrefBaseE p time d allowedIdx) :=
  exprBoundedIn_add_const B generatorPrefOffset σ (setupME p time d allowedIdx) hMe
    (by rw [hMeval]; exact hMc)

lemma exprBoundedIn_generatorKindBaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (hprefB : ExprBoundedIn B σ (generatorPrefBaseE p time d allowedIdx))
    (hlenB : ExprBoundedIn B σ generatorPrefLenE)
    (hsum : generatorPrefBase p time d allowedIdx N + generatorPrefLen N + 2 ≤ B) :
    ExprBoundedIn B σ (generatorKindBaseE p time d allowedIdx) := by
  unfold generatorKindBaseE
  have hprefeval := generator_pref_base_e_eval p time d allowedIdx σ N h0
  have hleneval := generator_pref_len_e_eval σ N h0
  have hinner : ExprBoundedIn B σ
      (Expr.add (generatorPrefBaseE p time d allowedIdx) generatorPrefLenE) :=
    ⟨hprefB, hlenB, by rw [hprefeval, hleneval]; omega⟩
  refine exprBoundedIn_add_const B 2 σ _ hinner ?_
  show (generatorPrefBaseE p time d allowedIdx).eval σ + generatorPrefLenE.eval σ + 2 ≤ B
  rw [hprefeval, hleneval]; omega

lemma exprBoundedIn_generatorArg1BaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (hkindB : ExprBoundedIn B σ (generatorKindBaseE p time d allowedIdx))
    (hsum : generatorKindBase p time d allowedIdx N + (d.table.length + 2) ≤ B) :
    ExprBoundedIn B σ (generatorArg1BaseE p time d allowedIdx) := by
  unfold generatorArg1BaseE
  have hkindeval := generator_kind_base_e_eval p time d allowedIdx σ N h0
  exact exprBoundedIn_add_const B (d.table.length + 2) σ _ hkindB (by rw [hkindeval]; exact hsum)

lemma exprBoundedIn_generatorArg2BaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (harg1B : ExprBoundedIn B σ (generatorArg1BaseE p time d allowedIdx))
    (hsum : generatorArg1Base p time d allowedIdx N + (d.table.length + 2) ≤ B) :
    ExprBoundedIn B σ (generatorArg2BaseE p time d allowedIdx) := by
  unfold generatorArg2BaseE
  have harg1eval := generator_arg1_base_e_eval p time d allowedIdx σ N h0
  exact exprBoundedIn_add_const B (d.table.length + 2) σ _ harg1B (by rw [harg1eval]; exact hsum)

lemma exprBoundedIn_generatorOutBaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (harg2B : ExprBoundedIn B σ (generatorArg2BaseE p time d allowedIdx))
    (hsum : generatorArg2Base p time d allowedIdx N + (d.table.length + 2) ≤ B) :
    ExprBoundedIn B σ (generatorOutBaseE p time d allowedIdx) := by
  unfold generatorOutBaseE
  have harg2eval := generator_arg2_base_e_eval p time d allowedIdx σ N h0
  exact exprBoundedIn_add_const B (d.table.length + 2) σ _ harg2B (by rw [harg2eval]; exact hsum)

lemma exprBoundedIn_generatorTableBaseE (B N : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) (σ : Store) (h0 : σ 0 = N)
    (houtB : ExprBoundedIn B σ (generatorOutBaseE p time d allowedIdx))
    (hsum : generatorOutBase p time d allowedIdx N + (outIdx.length + 1) ≤ B) :
    ExprBoundedIn B σ (generatorTableBaseE p time d allowedIdx outIdx) := by
  unfold generatorTableBaseE
  have houteval := generator_out_base_e_eval p time d allowedIdx σ N h0
  exact exprBoundedIn_add_const B (outIdx.length + 1) σ _ houtB (by rw [houteval]; exact hsum)

/-- `generatorLayoutProg p time d allowedIdx outIdx` stays bounded by `B` at
any store holding the input length `N`, given `p`'s coefficient/shift/product
majorants, `emitLenPoly`'s own, enough room past `setupME p time d allowedIdx`
for the parameter block, and the chain of sums the five staged-word bases and
the table base accumulate. -/
lemma programBoundedIn_generatorLayoutProg (B N : ℕ) (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (hσ0 : σ 0 = N)
    (h1p : p.eval 1 ≤ B) (hsp : p.eval (N + 1) ≤ B) (hmp : N * p.eval (N + 1) ≤ B)
    (hspan : setupSpan p N ≤ B)
    (h1e : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval 1 ≤ B)
    (hshifte : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hmule : N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval (N + 1) ≤ B)
    (hM24 : setupM p time d allowedIdx N + 24 ≤ B)
    (hpref30 : setupM p time d allowedIdx N + generatorPrefOffset ≤ B)
    (hpref2b : 2 * N + 1 ≤ B)
    (hkindsum : generatorPrefBase p time d allowedIdx N + generatorPrefLen N + 2 ≤ B)
    (harg1sum : generatorKindBase p time d allowedIdx N + (d.table.length + 2) ≤ B)
    (harg2sum : generatorArg1Base p time d allowedIdx N + (d.table.length + 2) ≤ B)
    (houtsum : generatorArg2Base p time d allowedIdx N + (d.table.length + 2) ≤ B)
    (htablesum : generatorOutBase p time d allowedIdx N + (outIdx.length + 1) ≤ B) :
    ProgramBoundedIn B σ (generatorLayoutProg p time d allowedIdx outIdx) := by
  unfold generatorLayoutProg
  apply programBoundedIn_paramSetupWrites B N (setupME p time d allowedIdx)
    (generatorLayoutPairs p time d allowedIdx outIdx) σ
    hσ0 (generator_layout_pairs_pos p time d allowedIdx outIdx)
  · intro τ hτ
    exact exprBoundedIn_setupME B N p time d allowedIdx τ
      (exprBoundedIn_setupSpanE B N p τ hτ h1p hsp hmp hspan) (setupSpanE_eval p τ N hτ) hτ
      h1e hshifte hmule (by omega)
  · intro j hj τ hτ
    have hMeval := setupME_eval p time d allowedIdx τ N hτ
    have hj24 : j ≤ 24 := by
      simp only [generatorLayoutPairs, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [initPrefBaseReg, transKindBaseReg, transArg1BaseReg, transArg2BaseReg,
          acceptOutBaseReg, wpJ, emTblJ, generatorTableBaseReg]
    rw [hMeval]; omega
  · intro q hq τ hτ
    have hMeB : ExprBoundedIn B τ (setupME p time d allowedIdx) :=
      exprBoundedIn_setupME B N p time d allowedIdx τ
        (exprBoundedIn_setupSpanE B N p τ hτ h1p hsp hmp hspan) (setupSpanE_eval p τ N hτ) hτ
        h1e hshifte hmule (by omega)
    have hMeval := setupME_eval p time d allowedIdx τ N hτ
    have hprefB : ExprBoundedIn B τ (generatorPrefBaseE p time d allowedIdx) :=
      exprBoundedIn_generatorPrefBaseE B N p time d allowedIdx τ hMeB hMeval hpref30
    have hlenB : ExprBoundedIn B τ generatorPrefLenE :=
      exprBoundedIn_generatorPrefLenE B N τ hτ (by omega) hpref2b
    have hkindB : ExprBoundedIn B τ (generatorKindBaseE p time d allowedIdx) :=
      exprBoundedIn_generatorKindBaseE B N p time d allowedIdx τ hτ hprefB hlenB hkindsum
    have harg1B : ExprBoundedIn B τ (generatorArg1BaseE p time d allowedIdx) :=
      exprBoundedIn_generatorArg1BaseE B N p time d allowedIdx τ hτ hkindB harg1sum
    have harg2B : ExprBoundedIn B τ (generatorArg2BaseE p time d allowedIdx) :=
      exprBoundedIn_generatorArg2BaseE B N p time d allowedIdx τ hτ harg1B harg2sum
    have houtB : ExprBoundedIn B τ (generatorOutBaseE p time d allowedIdx) :=
      exprBoundedIn_generatorOutBaseE B N p time d allowedIdx τ hτ harg2B houtsum
    have htableB : ExprBoundedIn B τ (generatorTableBaseE p time d allowedIdx outIdx) :=
      exprBoundedIn_generatorTableBaseE B N p time d allowedIdx outIdx τ hτ houtB htablesum
    simp only [generatorLayoutPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hprefB
    · exact hkindB
    · exact harg1B
    · exact harg2B
    · exact houtB
    · exact htableB
    · exact htableB
    · exact htableB

/-! ## `generatorSetupProg` and the mid-generator reassignment

`generatorSetupProg` is `setupProg` followed by `generatorLayoutProg`, so its
bound is the two pieces above composed through `ProgramBoundedIn`'s `.seq`
case — the only new fact needed is that `setupProg` preserves register `0`
(`setup_prog_zero`), which lets `generatorLayoutProg`'s hypotheses be
discharged at the store `setupProg` produces. The later `.assign 0 (setupME
p)` inside `generatorProg` reuses `setupME`'s own bound directly, since
`ProgramBoundedIn` on `.assign` asks nothing beyond the target register and
the value expression. -/

/-- `generatorSetupProg p time d allowedIdx outIdx` stays bounded by `B` at
any store holding the input length `N`, from the two stage bounds above. -/
lemma programBoundedIn_generatorSetupProg (B N : ℕ) (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (σ : Store) (hσ0 : σ 0 = N)
    (h1 : ProgramBoundedIn B σ (setupProg p time d allowedIdx))
    (h2 : ∀ τ : Store, τ 0 = N →
      ProgramBoundedIn B τ (generatorLayoutProg p time d allowedIdx outIdx)) :
    ProgramBoundedIn B σ (generatorSetupProg p time d allowedIdx outIdx) := by
  unfold generatorSetupProg
  refine ⟨h1, h2 ((setupProg p time d allowedIdx).eval σ) ?_⟩
  rw [setup_prog_zero]; exact hσ0

/-- The reassignment `.assign 0 (setupME p time d allowedIdx)` inside
`generatorProg` stays bounded by `B` once `setupME p time d allowedIdx` itself
does — `ProgramBoundedIn` on `.assign` asks only that the target register and
the value expression fit `B`, and register `0` always does. -/
lemma programBoundedIn_setupME_assign (B : ℕ) (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ : Store)
    (hMe : ExprBoundedIn B σ (setupME p time d allowedIdx)) :
    ProgramBoundedIn B σ (Program.assign 0 (setupME p time d allowedIdx)) :=
  ⟨Nat.zero_le B, hMe⟩

end NPComplete.CookLevin

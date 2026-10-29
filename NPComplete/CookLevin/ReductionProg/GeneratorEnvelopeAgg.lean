module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedStage
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedSetup

/-!
# The global envelope, aggregated

The boundedness lemmas of the stage layer (`clauseWriterBounded_tableWriterProgParam`)
and of the setup layer (`programBoundedIn_setupProg`,
`programBoundedIn_generatorLayoutProg`) each state their own arithmetic
hypotheses at abstract `K`, `S`, `B`, `wid`.  This file defines the four
envelopes as polynomials in the input length `N` and discharges every one of
those hypotheses at them, in the dependency order `K` → `wid` → `S` → `B` —
no envelope feeds into itself, and none collapses onto another: `K` bounds
the control and parameter cells, `wid` the clause-table width (cubic in `K`),
`S` the whole store (`K` plus the width plus the variable numbers), and `B`
the expression intermediates (`S` plus `K`'s quadratics plus the setup layer's
shifted evaluations `q.comp (X + 1)`).

`K` deliberately does not depend on the write pointer's runtime value: the
staged-word bases it must dominate end at `outBase + outIdx.length + 1`, which
is `setupM + 2N + 40 + 3·|table| + |outIdx|` — a polynomial in `N` alone, since
the descriptor is a fixed parameter of `generatorProg`.  The one genuinely
`N`-dependent term beyond `setupMPoly` is `timePoly`: `cookWindowPoly` contains
`2 * timePoly`, and `time`'s degree is unrelated to `p`'s, so `K` must carry
`timePoly` additively rather than through `setupMPoly` alone.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM

/-! ## Max over the concrete index lists

Every "each element of this list is at most `K`" hypothesis is discharged at
one shared maximum, so a single constant block in `envK` covers all of them. -/

lemma foldr_max_ge_of_mem {l : List ℕ} {v : ℕ} (hv : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hv
  | cons a as ih =>
    simp only [List.foldr]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact le_max_left _ _
    · exact Nat.le_trans (ih hv) (le_max_right _ _)

/-- Maximum of all index lists and descriptor columns the envelopes cover. -/
def envIdxMax (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) : ℕ :=
  (prefIdx ++ allowedIdx ++ outIdx ++ d.table.map transKind ++ d.table.map transArg1 ++
    d.table.map transArg2 ++ descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).foldr max 0

lemma envIdxMax_ge {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ prefIdx ++ allowedIdx ++ outIdx ++ d.table.map transKind ++
      d.table.map transArg1 ++ d.table.map transArg2 ++
      descHaltStates d (natInitSymbol d.blankIdx outIdx 0)) :
    v ≤ envIdxMax d prefIdx allowedIdx outIdx :=
  foldr_max_ge_of_mem hv

lemma envIdxMax_ge_pref {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ prefIdx) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_allowed {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ allowedIdx) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_out {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ outIdx) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_kind {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ d.table.map transKind) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_arg1 {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ d.table.map transArg1) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_arg2 {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ d.table.map transArg2) : v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto

lemma envIdxMax_ge_halt {d : TableauDescriptor} {prefIdx allowedIdx outIdx : List ℕ} {v : ℕ}
    (hv : v ∈ descHaltStates d (natInitSymbol d.blankIdx outIdx 0)) :
    v ≤ envIdxMax d prefIdx allowedIdx outIdx := by
  apply envIdxMax_ge; simp only [List.mem_append]; tauto


/-! ## Polynomial evaluation helpers

Every inequality below is decided by `omega` once the polynomials are unfolded
into `eval`-sums, so the only reusable facts needed are the two shapes a
shifted evaluation takes. -/

lemma eval_comp_shift (q : Polynomial ℕ) (N : ℕ) :
    (q.comp (X + 1)).eval N = q.eval (N + 1) := by
  rw [Polynomial.eval_comp]
  simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-! ## The four envelopes

`K` bounds the control and parameter cells; `wid` the clause-table width the
writer still owes (cubic in `K`); `S` the whole store; `B` the expression
intermediates.  Each is a sum of the earlier ones plus its own terms, so the
four stay distinct and the nesting `K ≤ S ≤ B` is real rather than vacuous. -/

/-- Constant block of `envK`: the descriptor quantities, the list maxima and
slack `200` for the staged-word offsets (`40 + 3·|table| + |outIdx|` beyond
what `cookWindowPoly`'s `2N` term covers). -/
def envKConst (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) : ℕ :=
  d.numStates + d.numLetters + d.blankIdx + d.startState +
    (allowedIdx.length + 1) + (outIdx.length + 1) +
    (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length +
    envIdxMax d prefIdx allowedIdx outIdx + 4 * d.table.length + 200

/-- Envelope over the control and parameter cells. -/
noncomputable def envK (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) : Polynomial ℕ :=
  setupMPoly p time d allowedIdx + cookWindowPoly p time + timePoly p time + C 1 +
    C (envKConst d prefIdx allowedIdx outIdx)

lemma envK_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envK p time d prefIdx allowedIdx outIdx).eval N
      = setupM p time d allowedIdx N + (cookWindowPoly p time).eval N + (timePoly p time).eval N + 1 +
        envKConst d prefIdx allowedIdx outIdx := by
  simp only [envK, Polynomial.eval_add, Polynomial.eval_C, setupMPoly_eval]

/-- Constant multiplier of `K³` in `envWid`, sized to dominate every
coefficient of the five stage-width sums at `W ≤ K`, `T + 1 ≤ K`,
`freeLen ≤ K`.  The halt-state count is covered through `d.numStates`
because `descHaltStates` filters a range of that length. -/
def envWidConst (d : TableauDescriptor) (allowedIdx : List ℕ) : ℕ :=
  10 * d.numStates + 24 * d.numLetters + 30 * d.numStates * d.numLetters +
    2 * allowedIdx.length + 60

/-- Envelope over the clause-table width the writer still owes. -/
noncomputable def envWid (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) : Polynomial ℕ :=
  envK p time d prefIdx allowedIdx outIdx * envK p time d prefIdx allowedIdx outIdx *
    envK p time d prefIdx allowedIdx outIdx * C (envWidConst d allowedIdx)

lemma envWid_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envWid p time d prefIdx allowedIdx outIdx).eval N
      = (envK p time d prefIdx allowedIdx outIdx).eval N *
          ((envK p time d prefIdx allowedIdx outIdx).eval N *
            ((envK p time d prefIdx allowedIdx outIdx).eval N *
              envWidConst d allowedIdx)) := by
  simp only [envWid, Polynomial.eval_mul, Polynomial.eval_C]; ring_nf

/-- Envelope over the whole store: `K`, the table width, and the dense-layout
variable numbers, plus `4` for the `2 ≤ S`, `3 ≤ S`, `4 ≤ S` demands. -/
noncomputable def envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) : Polynomial ℕ :=
  envK p time d prefIdx allowedIdx outIdx +
    envWid p time d prefIdx allowedIdx outIdx +
    varBoundPoly p time (d.numStates + 1) (d.numLetters + 1) + C 4

lemma envS_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envS p time d prefIdx allowedIdx outIdx).eval N
      = (envK p time d prefIdx allowedIdx outIdx).eval N +
        (envWid p time d prefIdx allowedIdx outIdx).eval N +
        (varBoundPoly p time (d.numStates + 1) (d.numLetters + 1)).eval N + 4 := by
  simp only [envS, Polynomial.eval_add, Polynomial.eval_C]

/-- Envelope over the expression intermediates: everything `S` covers, the
`K`-quadratics the five family envelopes need, and the setup layer's shifted
evaluations with their constant counterparts. -/
noncomputable def envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) : Polynomial ℕ :=
  envS p time d prefIdx allowedIdx outIdx +
    envK p time d prefIdx allowedIdx outIdx * envK p time d prefIdx allowedIdx outIdx *
      C (4 + 3 * d.numLetters) +
    setupMPoly p time d allowedIdx +
    X * (p.comp (X + 1)) + X * ((cookWindowPoly p time).comp (X + 1)) +
    X * ((timePoly p time).comp (X + 1)) +
    X * ((emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).comp
      (X + 1)) +
    p.comp (X + 1) + (cookWindowPoly p time).comp (X + 1) +
    (timePoly p time).comp (X + 1) +
    (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).comp (X + 1) +
    C (p.eval 1 + (cookWindowPoly p time).eval 1 + (timePoly p time).eval 1 +
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval 1)

lemma envB_eval (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envB p time d prefIdx allowedIdx outIdx).eval N
      = (envS p time d prefIdx allowedIdx outIdx).eval N +
        (envK p time d prefIdx allowedIdx outIdx).eval N *
          ((envK p time d prefIdx allowedIdx outIdx).eval N * (4 + 3 * d.numLetters)) +
        setupM p time d allowedIdx N +
        N * p.eval (N + 1) + N * (cookWindowPoly p time).eval (N + 1) +
        N * (timePoly p time).eval (N + 1) +
        N * (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval
          (N + 1) +
        p.eval (N + 1) + (cookWindowPoly p time).eval (N + 1) +
        (timePoly p time).eval (N + 1) +
        (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval (N + 1) +
        (p.eval 1 + (cookWindowPoly p time).eval 1 + (timePoly p time).eval 1 +
          (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval 1) := by
  simp only [envB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, setupMPoly_eval, eval_comp_shift]
  ring_nf

/-! ## `envK` dominates its components

Each lemma below is one of the stage or setup layer's `≤ K` obligations,
stated directly against the envelope's evaluation.  The pattern is uniform:
rewrite by `envK_eval` (and `cookWindowPoly_eval` when the `2N` part of a
staged-word offset needs identifying), unfold the offset chain, then `omega`. -/

lemma envK_ge_setupM (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    setupM p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; omega

lemma envK_ge_one (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    1 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; omega

lemma envK_ge_window (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (cookWindowPoly p time).eval N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; omega

lemma envK_ge_time (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (timePoly p time).eval N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]; omega

/-- `p.eval N` reaches `envK` through `setupSpan ≤ setupM`: the span already
carries `p.eval N` additively. -/
lemma envK_ge_freeLen (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    p.eval N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  have h1 : p.eval N ≤ setupSpan p N := by unfold setupSpan; omega
  have hs : 1 ≤ setupSpan p N := by unfold setupSpan; omega
  have h3 : setupSpan p N ≤ setupSpan p N * setupSpan p N :=
    Nat.le_mul_of_pos_right _ hs
  have h4 : setupSpan p N * setupSpan p N ≤
      setupSpan p N * (setupSpan p N * setupSpan p N) :=
    Nat.mul_le_mul_left _ h3
  have h2 : setupSpan p N * (setupSpan p N * setupSpan p N) ≤ setupM p time d allowedIdx N := by
    unfold setupM; omega
  omega

lemma envK_ge_two_n (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    2 * N + 1 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]; omega

lemma envK_ge_prefLen (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorPrefLen N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold envKConst generatorPrefLen; omega

lemma envK_ge_prefBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorPrefBase p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  unfold generatorPrefBase generatorPrefOffset envKConst; omega

lemma envK_ge_kindBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorKindBase p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorKindBase generatorKindOffset generatorPrefOffset envKConst generatorPrefLen
  omega

lemma envK_ge_arg1Base (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorArg1Base p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorArg1Base generatorArg1Offset generatorKindOffset generatorPrefOffset envKConst
    generatorPrefLen
  omega

lemma envK_ge_arg2Base (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorArg2Base p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorArg2Base generatorArg2Offset generatorArg1Offset generatorKindOffset
    generatorPrefOffset envKConst generatorPrefLen
  omega

lemma envK_ge_outBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorOutBase p time d allowedIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
    generatorKindOffset generatorPrefOffset envKConst generatorPrefLen
  omega

lemma envK_ge_tableBase (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorTableBase p time d allowedIdx outIdx N ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorTableBase generatorJmax generatorOutOffset generatorArg2Offset
    generatorArg1Offset generatorKindOffset generatorPrefOffset envKConst generatorPrefLen
  omega

lemma envK_ge_out_base_len (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    generatorOutBase p time d allowedIdx N + outIdx.length + 1 ≤
      (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval, cookWindowPoly_eval]
  unfold generatorOutBase generatorOutOffset generatorArg2Offset generatorArg1Offset
    generatorKindOffset generatorPrefOffset envKConst generatorPrefLen
  omega

lemma envK_eval_ge_setupM_add_70 (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    setupM p time d allowedIdx N + 70 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envK_eval]
  unfold envKConst; omega

/-- `envK` is at least `setupM`'s constant `30`, which is what the nonlinear
domination steps below use. -/
lemma envK_ge_thirty (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    30 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  have h1 : 30 ≤ setupM p time d allowedIdx N := by unfold setupM; omega
  have h2 := envK_ge_setupM p time d prefIdx allowedIdx outIdx N
  omega

/-! ## The nonlinear core

`envWid` evaluates to `K³ · wc` with `wc ≥ 40` and `K ≥ 30`, and the five
family envelopes ask for `K·(n + K + K·m)`-shaped sums with `n, m ≤ K + 1`.
Both obligations below reduce to `K³ + 4K² + 7K + 1 ≤ K³ · 40`, which holds
from `2 ≤ K` alone. -/

lemma cube_bound_core (K wc : ℕ) (hK : 2 ≤ K) (hwc : 40 ≤ wc) :
    K * K * K + 4 * (K * K) + 7 * K + 1 ≤ K * K * (K * wc) := by
  have e1 : K * K * (K * wc) = (K * K * K) * wc := by ring
  rw [e1]
  have hK3 : 8 ≤ K * K * K := by nlinarith
  have hsplit : (K * K * K) * wc = (K * K * K) * 40 + (K * K * K) * (wc - 40) := by
    have h : 40 + (wc - 40) = wc := by omega
    conv => lhs; rw [← h]
    rw [Nat.mul_add]
  have hmid : K * K * K + 4 * (K * K) + 7 * K + 1 ≤ (K * K * K) * 40 := by
    nlinarith
  rw [hsplit]
  omega

/-- `UniqEnv`'s sum: the largest `K`-multiplied piece plus the plain tail. -/
lemma cube_dom (K wc n m : ℕ) (hK : 2 ≤ K) (hwc : 40 ≤ wc) (hn : n ≤ K + 1) (hm : m ≤ K + 1) :
    K * (n + K + K * m) + n + K + K * m + K + K + K ≤ K * K * (K * wc) := by
  have h1 : K * n ≤ K * (K + 1) := Nat.mul_le_mul_left K hn
  have h2 : K * K * m ≤ K * K * (K + 1) := Nat.mul_le_mul_left (K * K) hm
  have h3 : n + K + K * m + K + K + K ≤ (K + 1) + K + (K * (K + 1)) + K + K + K := by
    have hb : K * m ≤ K * (K + 1) := Nat.mul_le_mul_left K hm
    omega
  have heq : K * (n + K + K * m) = K * n + (K * K + K * K * m) := by ring
  have h4 : K * n + (K * K + K * K * m) + (n + K + K * m + K + K + K) ≤
      K * (K + 1) + (K * K + K * K * (K + 1)) + ((K + 1) + K + (K * (K + 1)) + K + K + K) := by
    omega
  have h5 : K * (K + 1) + (K * K + K * K * (K + 1)) + ((K + 1) + K + (K * (K + 1)) + K + K + K)
      = K * K * K + 4 * (K * K) + 7 * K + 1 := by ring
  have h6 := cube_bound_core K wc hK hwc
  have h7 := le_trans (le_trans h4 (le_of_eq h5)) h6
  calc K * (n + K + K * m) + n + K + K * m + K + K + K
      = K * n + (K * K + K * K * m) + (n + K + K * m + K + K + K) := by rw [heq]; ring
    _ ≤ K * K * (K * wc) := h7

/-- `PersistEnv`'s full sum: the widest of the five, `K`-multiplied head plus
the widest tail. -/
lemma persist_tail_dom (K wc n m : ℕ) (hK : 2 ≤ K) (hwc : 40 ≤ wc) (hn : n ≤ K + 1)
    (hm : m ≤ K + 1) :
    K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) + K ≤
      K * K * (K * wc) := by
  have h3 : K * m ≤ K * (K + 1) := Nat.mul_le_mul_left K hm
  have h1 : K * n ≤ K * (K + 1) := Nat.mul_le_mul_left K hn
  have hsplit : K * K * (K * wc) = (K * K * K) * wc := by ring
  rw [hsplit]
  have hK3 : 8 ≤ K * K * K := by nlinarith
  have hsplit2 : (K * K * K) * wc = (K * K * K) * 40 + (K * K * K) * (wc - 40) := by
    have h : 40 + (wc - 40) = wc := by omega
    conv => lhs; rw [← h]
    rw [Nat.mul_add]
  rw [hsplit2]
  have hmid : K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) + K
      ≤ (K * K * K) * 40 := by nlinarith
  omega

/-! ## `envS` and `envB` dominate the family envelopes

Each of the five `*Env` inequalities is discharged twice — at `S` and at `B` —
and both reduce to `cube_dom` or `persist_tail_dom` once `n`, `m` are under
`K + 1` and `envWid`'s evaluation is identified with `K³ · wc`. -/

lemma envK_ge_two (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    2 ≤ (envK p time d prefIdx allowedIdx outIdx).eval N := by
  have h := envK_ge_thirty p time d prefIdx allowedIdx outIdx N; omega

lemma envS_ge_envK (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envK p time d prefIdx allowedIdx outIdx).eval N ≤
      (envS p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envS_eval]; omega

lemma envS_ge_envWid (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envWid p time d prefIdx allowedIdx outIdx).eval N ≤
      (envS p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envS_eval]; omega

/-- Every envelope-satisfaction proof needs the same three facts, so they are
bundled as one hypothesis pair on the descriptor. -/
lemma envWid_ge_cube (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (K n m : ℕ)
    (hKeq : (envK p time d prefIdx allowedIdx outIdx).eval N = K)
    (hn : n ≤ K + 1) (hm : m ≤ K + 1) :
    K * (n + K + K * m) + n + K + K * m + K + K + K ≤
      (envS p time d prefIdx allowedIdx outIdx).eval N := by
  have hK2 : 2 ≤ K := by rw [← hKeq]; exact envK_ge_two p time d prefIdx allowedIdx outIdx N
  have hwc : 40 ≤ envWidConst d allowedIdx := by unfold envWidConst; omega
  have hcube := cube_dom K (envWidConst d allowedIdx) n m hK2 hwc hn hm
  have hW := envWid_eval p time d prefIdx allowedIdx outIdx N
  rw [hKeq] at hW
  have hS := envS_ge_envWid p time d prefIdx allowedIdx outIdx N
  have hrew : K * (K * (K * envWidConst d allowedIdx)) = K * K * (K * envWidConst d allowedIdx) :=
    by ring
  omega

lemma envWid_ge_persist (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (K n m : ℕ)
    (hKeq : (envK p time d prefIdx allowedIdx outIdx).eval N = K)
    (hn : n ≤ K + 1) (hm : m ≤ K + 1) :
    K * (n + K + K * m) + (n + K + K * m) + n + K + ((2 * K + 1) * m + K) + K ≤
      (envS p time d prefIdx allowedIdx outIdx).eval N := by
  have hK2 : 2 ≤ K := by rw [← hKeq]; exact envK_ge_two p time d prefIdx allowedIdx outIdx N
  have hwc : 40 ≤ envWidConst d allowedIdx := by unfold envWidConst; omega
  have hcube := persist_tail_dom K (envWidConst d allowedIdx) n m hK2 hwc hn hm
  have hW := envWid_eval p time d prefIdx allowedIdx outIdx N
  rw [hKeq] at hW
  have hS := envS_ge_envWid p time d prefIdx allowedIdx outIdx N
  have hrew : K * (K * (K * envWidConst d allowedIdx)) = K * K * (K * envWidConst d allowedIdx) :=
    by ring
  omega

/-- `InitEnv`'s sum: linear in `K`, `n`, `m` but with a `3·K·m` term the
`UniqEnv`-shaped bound does not name, so it gets its own domination. -/
lemma init_tail_dom (K wc n m : ℕ) (hK : 2 ≤ K) (hwc : 40 ≤ wc) (hn : n ≤ K + 1)
    (hm : m ≤ K + 1) :
    n + K + K * m + (3 * K * m + m) + 3 * K + 1 ≤ K * K * (K * wc) := by
  have hcore := cube_bound_core K wc hK hwc
  have h1 : n ≤ K + 1 := hn
  have h2 : m ≤ K + 1 := hm
  have h3 : K * m ≤ K * (K + 1) := Nat.mul_le_mul_left K hm
  have h4 : 3 * K * m ≤ 3 * K * (K + 1) := by nlinarith
  nlinarith

/-- `TransEnv`'s sum: the `K`-multiplied piece plus a doubled plain tail. -/
lemma trans_tail_dom (K wc n m : ℕ) (hK : 2 ≤ K) (hwc : 40 ≤ wc) (hn : n ≤ K + 1)
    (hm : m ≤ K + 1) :
    K * (n + K + K * m) + (n + K + K * m) + n + K + K * m + 2 * K ≤ K * K * (K * wc) := by
  have h3 : K * m ≤ K * (K + 1) := Nat.mul_le_mul_left K hm
  have h1 : K * n ≤ K * (K + 1) := Nat.mul_le_mul_left K hn
  have hsplit : K * K * (K * wc) = (K * K * K) * wc := by ring
  rw [hsplit]
  have hK3 : 8 ≤ K * K * K := by nlinarith
  have hsplit2 : (K * K * K) * wc = (K * K * K) * 40 + (K * K * K) * (wc - 40) := by
    have h : 40 + (wc - 40) = wc := by omega
    conv => lhs; rw [← h]
    rw [Nat.mul_add]
  rw [hsplit2]
  have hmid : K * (n + K + K * m) + (n + K + K * m) + n + K + K * m + 2 * K
      ≤ (K * K * K) * 40 := by nlinarith
  omega

lemma envWid_ge_trans (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (K n m : ℕ)
    (hKeq : Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) = K)
    (hn : n ≤ K + 1) (hm : m ≤ K + 1) :
    K * (n + K + K * m) + (n + K + K * m) + n + K + K * m + 2 * K ≤
      Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx) := by
  have hK2 : 2 ≤ K := by rw [← hKeq]; exact envK_ge_two p time d prefIdx allowedIdx outIdx N
  have hwc : 40 ≤ envWidConst d allowedIdx := by unfold envWidConst; omega
  have hcube := trans_tail_dom K (envWidConst d allowedIdx) n m hK2 hwc hn hm
  have hW := envWid_eval p time d prefIdx allowedIdx outIdx N
  rw [hKeq] at hW
  have hS := envS_ge_envWid p time d prefIdx allowedIdx outIdx N
  have hrew : K * (K * (K * envWidConst d allowedIdx)) = K * K * (K * envWidConst d allowedIdx) :=
    by ring
  omega

lemma envWid_ge_init (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (K n m : ℕ)
    (hKeq : Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) = K)
    (hn : n ≤ K + 1) (hm : m ≤ K + 1) :
    n + K + K * m + (3 * K * m + m) + 3 * K + 1 ≤
      Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx) := by
  have hK2 : 2 ≤ K := by rw [← hKeq]; exact envK_ge_two p time d prefIdx allowedIdx outIdx N
  have hwc : 40 ≤ envWidConst d allowedIdx := by unfold envWidConst; omega
  have hcube := init_tail_dom K (envWidConst d allowedIdx) n m hK2 hwc hn hm
  have hW := envWid_eval p time d prefIdx allowedIdx outIdx N
  rw [hKeq] at hW
  have hS := envS_ge_envWid p time d prefIdx allowedIdx outIdx N
  have hrew : K * (K * (K * envWidConst d allowedIdx)) = K * K * (K * envWidConst d allowedIdx) :=
    by ring
  omega

/-! ## The nesting `K ≤ S ≤ B` -/

lemma envS_le_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    (envS p time d prefIdx allowedIdx outIdx).eval N ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  rw [envB_eval]; omega

/-! ## The five family envelopes at `S`

Each reduces to `envWid_ge_cube` (or `..._persist`, the widest tail) once the
descriptor's `n`, `m` are under `K + 1`, which the stage layer's own
`d.numStates ≤ K` demands provide.  The statements use prefix `Polynomial.eval`
because a dot-notation argument inside a curried `def` application elaborates
before its expected type is known. -/

lemma uniqEnv_envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    UniqEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) := by
  have hcube := envWid_ge_cube p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (d.numStates + 1) (d.numLetters + 1) rfl (by omega) (by omega)
  unfold UniqEnv
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

lemma initEnv_envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    InitEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) := by
  have hcube := envWid_ge_init p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (d.numStates + 1) (d.numLetters + 1) rfl (by omega) (by omega)
  unfold InitEnv
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

lemma transEnv_envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    TransEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) := by
  have hcube := envWid_ge_trans p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (d.numStates + 1) (d.numLetters + 1) rfl (by omega) (by omega)
  unfold TransEnv
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

lemma persistEnv_envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    PersistEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) := by
  have hpersist := envWid_ge_persist p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (d.numStates + 1) (d.numLetters + 1) rfl (by omega) (by omega)
  unfold PersistEnv
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

lemma acceptEnv_envS (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    AcceptEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envS p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) := by
  have hcube := envWid_ge_cube p time d prefIdx allowedIdx outIdx N
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (d.numStates + 1) (d.numLetters + 1) rfl (by omega) (by omega)
  unfold AcceptEnv
  have hKS := envS_ge_envK p time d prefIdx allowedIdx outIdx N
  omega

/-! The same five at `B`: `envB ≥ envS` transports each obligation upward. -/

lemma uniqEnv_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    UniqEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) :=
  uniqEnv_of_le (uniqEnv_envS p time d prefIdx allowedIdx outIdx N hn hm)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

lemma initEnv_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    InitEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) :=
  initEnv_of_le (initEnv_envS p time d prefIdx allowedIdx outIdx N hn hm)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

lemma transEnv_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    TransEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) :=
  transEnv_of_le (transEnv_envS p time d prefIdx allowedIdx outIdx N hn hm)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

lemma persistEnv_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    PersistEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) :=
  persistEnv_of_le (persistEnv_envS p time d prefIdx allowedIdx outIdx N hn hm)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

lemma acceptEnv_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ)
    (hn : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (hm : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx)) :
    AcceptEnv (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
      (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
      (d.numStates + 1) (d.numLetters + 1) :=
  acceptEnv_of_le (acceptEnv_envS p time d prefIdx allowedIdx outIdx N hn hm)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

/-! ## The remaining linear obligations

`M + 24 ≤ B`, `K + 1 ≤ B`, `K * m + K + K ≤ B` and the table-length bounds
all follow from `envB ≥ envK ≥ setupM` plus `envB ≥ envK * envK` (the same
quadratic term `envWid` already exceeds). -/

lemma envB_ge_envK (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) ≤
      Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) :=
  le_trans (envS_ge_envK p time d prefIdx allowedIdx outIdx N)
    (envS_le_envB p time d prefIdx allowedIdx outIdx N)

lemma envB_ge_env_ksq (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) *
        (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) *
          (4 + 3 * d.numLetters)) ≤
      Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) := by
  rw [envB_eval]
  omega

/-! ## The stage-width sum under `envWid`

`clauseWriterBounded_tableWriterProgParam`'s `wid` conclusion is a five-term
sum in `T`, `W`, `freeLen` and `K`.  At `T + 1 ≤ K`, `W ≤ K`, `freeLen ≤ K`
every term is under `K³ · wc`, which is what `envWid` evaluates to.

`n` and `m` are unbounded by `K` in the sum itself, so each term's bound
keeps the descriptor variables as literal coefficients of a `K · K · K`
monomial — the `K`-powers only absorb the constants and the `T`, `W`,
`freeLen` factors, never `n`, `m`, `al` or `hl`.  Matching the monomial shape
on both sides is what lets `omega` chain the casts. -/

/-- Arithmetic core of `envWid_ge_stage_wid`: the five-term stage-width sum at
`W ≤ K`, `T + 1 ≤ K`, `freeLen ≤ K`, `hl ≤ n` is under `K · K · K · wc` once
`wc` dominates `10·n + 24·m + 30·n·m + 2·al + 60`, which `envWidConst` does. -/
lemma stage_wid_dom (K W T n m al freeLen hl wc : ℕ) (hK : 2 ≤ K) (hWK : W ≤ K)
    (hTK : T + 1 ≤ K) (hfreeK : freeLen ≤ K) (hhl : hl ≤ n)
    (hwc : 10 * n + 24 * m + 30 * n * m + 2 * al + 60 = wc) :
    (((((T + 1) * (((2 + 2 * n) + n * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
          + W * ((2 + 2 * m) + m * (K * 6))))
        + (4 + (4 + (W * (2 + 2 * (al + 1)) + freeLen * 6)) + 0))
        + (T * (W * (n * (m * 30))) + 0))
        + (T * (W * (K * (m * 8) + K * (m * 8))))
        + (W * (W * 6) + (2 + 2 * hl) + 0))
      ≤ K * (K * (K * wc)) := by
  have hKK : 2 ≤ K * K := by nlinarith
  have hKKK : 8 ≤ K * K * K := by nlinarith
  have hT : T ≤ K := by omega
  have hresh : K * (K * (K * wc)) = wc * (K * K * K) := by ring
  rw [hresh]
  have ht1 : (T + 1) * (((2 + 2 * n) + n * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
      + W * ((2 + 2 * m) + m * (K * 6))) ≤ (16 + 8 * n + 8 * m) * (K * K * K) := by
    have hA : (2 + 2 * n) + n * (K * 6) ≤ (2 + 8 * n) * (K * K) := by
      have hnKK : n * K ≤ n * (K * K) := Nat.mul_le_mul_left n (by nlinarith : K ≤ K * K)
      nlinarith
    have hB : (2 + 2 * W) + W * (K * 6) ≤ 10 * (K * K) := by
      have hWKK : W * K ≤ W * (K * K) := Nat.mul_le_mul_left W (by nlinarith : K ≤ K * K)
      have hW2 : W * (K * K) ≤ K * (K * K) := Nat.mul_le_mul_right (K * K) hWK
      nlinarith
    have hC : W * ((2 + 2 * m) + m * (K * 6)) ≤ (2 + 8 * m) * (K * K) := by
      have hcast : W * ((2 + 2 * m) + m * (K * 6)) ≤ K * ((2 + 2 * m) + m * (K * 6)) :=
        Nat.mul_le_mul_right _ hWK
      have hsplit : K * ((2 + 2 * m) + m * (K * 6))
          = 2 * K + (2 * m) * K + 6 * ((m * K) * K) := by ring
      have hsplit2 : (2 + 8 * m) * (K * K) = 2 * (K * K) + (2 * m) * (K * K) + 6 * ((m * K) * K) :=
        by ring
      have hp1 : 2 * K ≤ 2 * (K * K) := by nlinarith
      have hp2 : (2 * m) * K ≤ (2 * m) * (K * K) := by nlinarith
      omega
    have hinner : ((2 + 2 * n) + n * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
        + W * ((2 + 2 * m) + m * (K * 6)) ≤ (14 + 8 * n + 8 * m) * (K * K) := by
      have hsplit3 : (2 + 8 * n) * (K * K) + 10 * (K * K) + (2 + 8 * m) * (K * K)
          = (14 + 8 * n + 8 * m) * (K * K) := by ring
      omega
    have hmon : (T + 1) * ((14 + 8 * n + 8 * m) * (K * K))
        ≤ K * ((14 + 8 * n + 8 * m) * (K * K)) := Nat.mul_le_mul hTK (le_refl _)
    have hsplit4 : K * ((14 + 8 * n + 8 * m) * (K * K))
        = (14 + 8 * n + 8 * m) * (K * K * K) := by ring
    have hlast : (14 + 8 * n + 8 * m) * (K * K * K) ≤ (16 + 8 * n + 8 * m) * (K * K * K) :=
      Nat.mul_le_mul (by omega : 14 + 8 * n + 8 * m ≤ 16 + 8 * n + 8 * m) (le_refl _)
    calc (T + 1) * (((2 + 2 * n) + n * (K * 6)) + ((2 + 2 * W) + W * (K * 6))
          + W * ((2 + 2 * m) + m * (K * 6)))
        ≤ (T + 1) * ((14 + 8 * n + 8 * m) * (K * K)) := Nat.mul_le_mul (le_refl _) hinner
      _ ≤ K * ((14 + 8 * n + 8 * m) * (K * K)) := hmon
      _ = (14 + 8 * n + 8 * m) * (K * K * K) := hsplit4
      _ ≤ (16 + 8 * n + 8 * m) * (K * K * K) := hlast
  have ht2 : 4 + (4 + (W * (2 + 2 * (al + 1)) + freeLen * 6)) + 0
      ≤ (10 + 2 * al) * (K * K * K) := by
    have hW : (2 + 2 * (al + 1)) * W ≤ (2 + 2 * (al + 1)) * K := Nat.mul_le_mul_left _ hWK
    have hK3 : K ≤ K * K * K := by nlinarith
    have hstep2 : (2 + 2 * (al + 1)) * K ≤ (2 + 2 * (al + 1)) * (K * K * K) :=
      Nat.mul_le_mul_left _ hK3
    have habsorb : (2 + 2 * (al + 1)) * (K * K * K)
        = (2 + 2 * al) * (K * K * K) + 2 * (K * K * K) := by ring
    have hfree : freeLen * 6 ≤ 6 * (K * K * K) := by
      have h2 : 6 * freeLen ≤ 6 * K := Nat.mul_le_mul_left 6 hfreeK
      have h3 : 6 * K ≤ 6 * (K * K * K) := Nat.mul_le_mul_left 6 hK3
      omega
    have hshape : W * (2 + 2 * (al + 1)) = (2 + 2 * (al + 1)) * W := by ring
    nlinarith
  have ht3 : T * (W * (n * (m * 30))) + 0 ≤ 30 * (n * m) * (K * K * K) := by
    have hcast : T * (W * (n * (m * 30))) ≤ K * (W * (n * (m * 30))) := Nat.mul_le_mul_right _ hT
    have hcast2 : W * (n * (m * 30)) ≤ K * (n * (m * 30)) := Nat.mul_le_mul_right _ hWK
    have hcast2' : K * (W * (n * (m * 30))) ≤ K * (K * (n * (m * 30))) :=
      Nat.mul_le_mul_left K hcast2
    have hfinal : K * (K * (n * (m * 30))) ≤ 30 * (n * m) * (K * K * K) := by
      have hsplit : K * (K * (n * (m * 30))) = 30 * (n * m) * (K * K) := by ring
      have hlast : 30 * (n * m) * (K * K) ≤ 30 * (n * m) * (K * K * K) :=
        Nat.mul_le_mul_left _ (by nlinarith : K * K ≤ K * K * K)
      omega
    omega
  have ht4 : T * (W * (K * (m * 8) + K * (m * 8))) ≤ 16 * m * (K * K * K) := by
    have hsplit : T * (W * (K * (m * 8) + K * (m * 8))) = 16 * (m * (T * (W * K))) := by ring
    have hinner : T * (W * K) ≤ K * K * K := by
      have hsplit2 : T * (W * K) = (T * W) * K := by ring
      have hTW : T * W ≤ K * K := by
        have hstep3 : T * W ≤ K * W := Nat.mul_le_mul_right _ hT
        have hstep4 : K * W ≤ K * K := Nat.mul_le_mul_left K hWK
        omega
      have hlast : (T * W) * K ≤ K * K * K := Nat.mul_le_mul_right _ hTW
      omega
    have hfin : 16 * (m * (T * (W * K))) ≤ 16 * m * (K * K * K) := by
      have hcast : m * (T * (W * K)) ≤ m * (K * K * K) := Nat.mul_le_mul_left m hinner
      have hshape : 16 * m * (K * K * K) = 16 * (m * (K * K * K)) := by ring
      omega
    omega
  have ht5 : W * (W * 6) + (2 + 2 * hl) + 0 ≤ (8 + 2 * n) * (K * K * K) := by
    have hWW : W * (W * 6) ≤ 6 * (K * K) := by nlinarith
    have h2hl : 2 + 2 * hl ≤ 2 + 2 * n := by omega
    nlinarith
  have hsum : (16 + 8 * n + 8 * m) * (K * K * K) + (10 + 2 * al) * (K * K * K)
      + 30 * (n * m) * (K * K * K) + 16 * m * (K * K * K) + (8 + 2 * n) * (K * K * K)
      ≤ wc * (K * K * K) := by
    have hconst : (16 + 8 * n + 8 * m) + (10 + 2 * al) + 30 * (n * m) + 16 * m + (8 + 2 * n)
        ≤ wc := by
      have hnm : 30 * (n * m) = 30 * n * m := by ring
      omega
    have hshape : (16 + 8 * n + 8 * m) * (K * K * K) + (10 + 2 * al) * (K * K * K)
        + 30 * (n * m) * (K * K * K) + 16 * m * (K * K * K) + (8 + 2 * n) * (K * K * K)
        = ((16 + 8 * n + 8 * m) + (10 + 2 * al) + 30 * (n * m) + 16 * m + (8 + 2 * n))
            * (K * K * K) := by ring
    exact le_trans (le_of_eq hshape) (Nat.mul_le_mul_right _ hconst)
  omega

lemma envWid_ge_stage_wid (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N K W T freeLen : ℕ)
    (hKeq : Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) = K)
    (hWK : W ≤ K) (hTK : T + 1 ≤ K) (hfreeK : freeLen ≤ K) :
    (((((T + 1) * (((2 + 2 * d.numStates) + d.numStates * (K * 6))
          + ((2 + 2 * W) + W * (K * 6))
          + W * ((2 + 2 * d.numLetters) + d.numLetters * (K * 6)))
        + (4 + (4 + (W * (2 + 2 * (allowedIdx.length + 1)) + freeLen * 6)) + 0))
        + (T * (W * (d.numStates * (d.numLetters * 30))) + 0))
        + (T * (W * (K * (d.numLetters * 8) + K * (d.numLetters * 8)))))
        + (W * (W * 6) + (2 + 2 * (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length)
          + 0))
      ≤ Polynomial.eval N (envWid p time d prefIdx allowedIdx outIdx) := by
  rw [envWid_eval, hKeq]
  have hK2 : 2 ≤ K := by rw [← hKeq]; exact envK_ge_two p time d prefIdx allowedIdx outIdx N
  have hhl : (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length ≤ d.numStates := by
    unfold descHaltStates
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hwcval : 10 * d.numStates + 24 * d.numLetters + 30 * d.numStates * d.numLetters +
      2 * allowedIdx.length + 60 = envWidConst d allowedIdx := by
    unfold envWidConst
    rfl
  exact stage_wid_dom K W T d.numStates d.numLetters allowedIdx.length freeLen
    (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)).length (envWidConst d allowedIdx)
    hK2 hWK hTK hfreeK hhl hwcval

end NPComplete.CookLevin

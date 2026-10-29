module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyStrideCheck
public import NPComplete.CookLevin.ReductionProg.GeneratorSizePoly

/-!
The five clause families read their run-time parameters (window, time bound,
certificate length, staged word bases) through fixed cells, so a producer has to
fill those cells before the first family runs.  `BoundedWhileDecider.p` demands
one fixed program, so neither the values nor the workspace base `M` may appear
in the syntax: everything input-dependent must be computed from the input length
sitting in register `0`.

That register is the crux.  The Horner evaluations of the
size polynomials expect register `0` to hold the input length `N`; the clause
writers expect it to hold `M`, since every control cell is addressed as
`cell 0 + j`.  Staging `N` into a spare absolute cell before overwriting
register `0` needs a cell that the input does not occupy, and the input occupies
`[1, N]` for unbounded `N`, so no fixed absolute cell is safe.

The resolution is to stop addressing through register `0` altogether.  Each
write's address is the *expression* `mE + j` where `mE` computes `M` from
register `0`, so the store-level address is `M + j` — exactly the cell the
writers read — while every value expression still sees `N` in register `0`.
Register `0` is never written (all offsets are at least `1`), so the two
conventions never conflict inside the setup; the handoff to the writers, which
repoints register `0` to `M`, is a separate single assignment this file does not
perform.

`M` itself is the majorant `(2N + 3 + p.eval N)^3 + 30 + (emitLenPoly …).eval N`. The cube keeps
the workspace clear of the input word and the emitter window, and the output-length term leaves room
for the emitted CNF.
The parameter cells occupy offsets `15..23`; the control block ends at
`M + generatorTableBaseReg` (`M + 24`). `setupPairs` sets the first
staged-word base at `M + 30`, then the remaining bases at `M + 40`, `M + 50`,
`M + 60`, and `M + 70`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The write engine

A list of `(cell, value expression)` pairs turned into a straight-line program.
Every write carries `mE` in its own address expression, so the whole program
floats with the workspace base without any per-input constant. -/

/-- Write `e` to the cell at address `mE + j`. -/
def paramSetupAssign (mE : Expr) (j : ℕ) (e : Expr) : Program :=
  .assignInd (.add mE (.const j)) e

lemma paramSetupAssign_eval_same (mE : Expr) (j : ℕ) (e : Expr) (σ : Store) :
    ((paramSetupAssign mE j e).eval σ) (mE.eval σ + j) = e.eval σ := by
  simp only [paramSetupAssign, eval_assignInd, Expr.eval, writeReg_same]

lemma paramSetupAssign_eval_diff (mE : Expr) (j : ℕ) (e : Expr) (σ : Store) (r : ℕ)
    (hr : r ≠ mE.eval σ + j) :
    ((paramSetupAssign mE j e).eval σ) r = σ r := by
  simp only [paramSetupAssign, eval_assignInd, Expr.eval]
  exact writeReg_diff σ (mE.eval σ + j) (e.eval σ) r hr

/-- No write touches register `0`, which is what keeps the value expressions'
    reading of the input length valid throughout. -/
lemma paramSetupAssign_zero (mE : Expr) (j : ℕ) (e : Expr) (σ : Store) (hj : 1 ≤ j) :
    ((paramSetupAssign mE j e).eval σ) 0 = σ 0 :=
  paramSetupAssign_eval_diff mE j e σ 0 (by omega)

/-- One write per pair. -/
def paramSetupWrites (mE : Expr) : List (ℕ × Expr) → Program
  | [] => .skip
  | (j, e) :: rest => .seq (paramSetupAssign mE j e) (paramSetupWrites mE rest)

/-- The value of `e` depends only on the register `0` entry. -/
def Reg0Expr (e : Expr) : Prop :=
  ∀ τ τ' : Store, τ 0 = τ' 0 → e.eval τ = e.eval τ'

lemma reg0Expr_const (c : ℕ) : Reg0Expr (Expr.const c) := by
  intro τ τ' _; simp only [Expr.eval]

lemma reg0Expr_reg0 : Reg0Expr (Expr.reg 0) := by
  intro τ τ' h; simpa only [Expr.eval] using h

lemma reg0Expr_add (a b : Expr) (ha : Reg0Expr a) (hb : Reg0Expr b) :
    Reg0Expr (Expr.add a b) := by
  intro τ τ' h
  simp only [Expr.eval]
  rw [ha τ τ' h, hb τ τ' h]

lemma reg0Expr_mul (a b : Expr) (ha : Reg0Expr a) (hb : Reg0Expr b) :
    Reg0Expr (Expr.mul a b) := by
  intro τ τ' h
  simp only [Expr.eval]
  rw [ha τ τ' h, hb τ τ' h]

lemma reg0Expr_horner (coeffs : List ℕ) (e : Expr) (he : Reg0Expr e) :
    Reg0Expr (hornerExpr coeffs e) := by
  induction coeffs with
  | nil => intro τ τ' _; simp only [hornerExpr, List.foldr_nil, Expr.eval]
  | cons c cs ih =>
      intro τ τ' h
      have h1 : hornerExpr (c :: cs) e = Expr.add (Expr.const c)
          (Expr.mul e (hornerExpr cs e)) := rfl
      rw [h1]
      show (Expr.add (Expr.const c) (Expr.mul e (hornerExpr cs e))).eval τ
          = (Expr.add (Expr.const c) (Expr.mul e (hornerExpr cs e))).eval τ'
      exact reg0Expr_add (Expr.const c) (Expr.mul e (hornerExpr cs e))
        (reg0Expr_const c) (reg0Expr_mul e (hornerExpr cs e) he ih) τ τ' h

/-- Every write preserves any cell it does not target. -/
lemma paramSetupWrites_frame (mE : Expr) (hmE : Reg0Expr mE)
    (pairs : List (ℕ × Expr)) (σ : Store) (r : ℕ)
    (hmin : ∀ j ∈ pairs.map Prod.fst, 1 ≤ j)
    (hr : ∀ j ∈ pairs.map Prod.fst, r ≠ mE.eval σ + j) :
    ((paramSetupWrites mE pairs).eval σ) r = σ r := by
  induction pairs generalizing σ with
  | nil => simp [paramSetupWrites]
  | cons q rest ih =>
    obtain ⟨j, e⟩ := q
    have hj1 : 1 ≤ j := hmin j (by simp)
    have hz : ((paramSetupAssign mE j e).eval σ) 0 = σ 0 :=
      paramSetupAssign_zero mE j e σ hj1
    have hnext : ∀ j' ∈ rest.map Prod.fst,
        r ≠ mE.eval ((paramSetupAssign mE j e).eval σ) + j' := by
      intro j' hj'
      rw [hmE _ _ hz]
      exact hr j' (by simp [hj'])
    have htail := ih ((paramSetupAssign mE j e).eval σ)
      (fun j' hj' => hmin j' (by simp [hj'])) hnext
    simp only [paramSetupWrites, eval_seq]
    rw [htail]
    exact paramSetupAssign_eval_diff mE j e σ r (hr j (by simp))

/-- A cell index that appears in the tail cannot equal the head's index when the
    head's index is absent from the tail's own index list. -/
lemma map_fst_ne_of_nodup (rest : List (ℕ × Expr)) (j j' : ℕ)
    (hnodup : j ∉ rest.map Prod.fst) (hj' : j' ∈ rest.map Prod.fst) : j' ≠ j := by
  intro hc
  have hx : ∃ x : Expr, (j', x) ∈ rest := by simpa using hj'
  obtain ⟨x, hx⟩ := hx
  rw [hc] at hx
  exact hnodup (List.mem_map_of_mem (f := Prod.fst) hx)

/-! ## Correctness of the engine

Each write lands at `M + p.1` and leaves the value the pair's expression takes
at the reference store, provided (i) the cell indices are distinct, so no later
write clobbers an earlier one, and (ii) every expression — the address
expression included — depends only on register `0`, which no write disturbs. -/

lemma paramSetupWrites_pins (mE : Expr) (hmE : Reg0Expr mE) (M : ℕ)
    (pairs : List (ℕ × Expr)) :
    ∀ (τ τ0 : Store), τ 0 = τ0 0 → mE.eval τ0 = M →
    (∀ q ∈ pairs, Reg0Expr q.2) →
    (pairs.map Prod.fst).Nodup →
    (∀ j ∈ pairs.map Prod.fst, 1 ≤ j) →
    ∀ p ∈ pairs.map (fun q : ℕ × Expr => (q.1, q.2.eval τ0)),
      ((paramSetupWrites mE pairs).eval τ) (M + p.1) = p.2 := by
  induction pairs with
  | nil =>
    intro τ τ0 h0 hM hdep hnodup hmin p hp
    exact absurd hp (List.not_mem_nil)
  | cons q rest ih =>
    obtain ⟨j, e⟩ := q
    intro τ τ0 h0 hM hdep hnodup hmin p hp
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hj1 : 1 ≤ j := hmin j (by simp)
    have hz : ((paramSetupAssign mE j e).eval τ) 0 = τ 0 :=
      paramSetupAssign_zero mE j e τ hj1
    have hmEt : mE.eval τ = M := by rw [hmE _ _ h0, hM]
    have hmEz : mE.eval ((paramSetupAssign mE j e).eval τ) = M := by
      rw [hmE _ _ hz, hmEt]
    have htail := ih ((paramSetupAssign mE j e).eval τ) τ0 (hz.trans h0) hM
      (fun q' hq' => hdep q' (by simp [hq'])) hnodup.2
      (fun j' hj' => hmin j' (by simp [hj']))
    rcases List.mem_cons.mp hp with hp | hp
    · have hp2 : p = (j, e.eval τ0) := by simpa using hp
      subst hp2
      have hframe : ((paramSetupWrites mE rest).eval ((paramSetupAssign mE j e).eval τ))
          (mE.eval τ + j) = ((paramSetupAssign mE j e).eval τ) (mE.eval τ + j) := by
        refine paramSetupWrites_frame mE hmE rest ((paramSetupAssign mE j e).eval τ)
          (mE.eval τ + j) (fun j' hj' => hmin j' (by simp [hj'])) ?_
        intro j' hj'
        show mE.eval τ + j ≠ mE.eval ((paramSetupAssign mE j e).eval τ) + j'
        rw [hmE _ _ hz]
        have hne := map_fst_ne_of_nodup rest j j' hnodup.1 hj'
        omega
      have hhead : ((paramSetupAssign mE j e).eval τ) (mE.eval τ + j) = e.eval τ :=
        paramSetupAssign_eval_same mE j e τ
      have hval : e.eval τ = e.eval τ0 := hdep (j, e) (by simp) τ τ0 h0
      show ((paramSetupWrites mE ((j, e) :: rest)).eval τ) (M + j) = e.eval τ0
      simp only [paramSetupWrites, eval_seq]
      have hMj : M + j = mE.eval τ + j := by rw [hmEt]
      rw [hMj, hframe, hhead, hval]
    · have hPeq : ((paramSetupWrites mE ((j, e) :: rest)).eval τ) (M + p.1)
          = ((paramSetupWrites mE rest).eval ((paramSetupAssign mE j e).eval τ))
            (M + p.1) := by
        simp only [paramSetupWrites, eval_seq]
      rw [hPeq]
      exact htail p hp

/-! ## The workspace base and the nine value expressions

`M` is a majorant of the input word and the emitter window, so the workspace
sits clear of everything the producer's earlier phases wrote.  Four values are
then computed from the input length: the window majorant, the time bound, the
certificate length, and the staged word length.  The remaining five are the base
addresses of the staged words, placed one word each after the parameter block.

Every expression — `mE` included — is built from register `0` and constants
alone, which is exactly `Reg0Expr` and what lets the engine thread values from
the entry store to the last write. -/

/-- The span `s = 2N + 3 + p.eval N`, whose cube is the main term of the workspace base `M`. -/
noncomputable def setupSpanE (p : Polynomial ℕ) : Expr :=
  Expr.add (Expr.add (Expr.mul (Expr.const 2) (Expr.reg 0)) (Expr.const 3))
    (hornerExpr (coeffList p) (Expr.reg 0))

/-- The workspace base expression: `s^3 + 30`, plus the output-length majorant
`emitLenPoly` computed by Horner's rule, so the block that follows clears the
tableau's own emitted CNF at every input length. -/
noncomputable def setupME (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Expr :=
  Expr.add
    (Expr.add
      (Expr.mul (setupSpanE p) (Expr.mul (setupSpanE p) (setupSpanE p)))
      (Expr.const 30))
    (hornerExpr (coeffList (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length)) (Expr.reg 0))

/-- The span at input length `N`. -/
noncomputable def setupSpan (p : Polynomial ℕ) (N : ℕ) : ℕ :=
  2 * N + 3 + p.eval N

/-- The workspace base at input length `N`: the cube of the span, plus the
output-length majorant at the descriptor's own dimensions. -/
noncomputable def setupM (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (N : ℕ) : ℕ :=
  (setupSpan p N) * ((setupSpan p N) * (setupSpan p N)) + 30
    + (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1) allowedIdx.length).eval N

lemma setupSpanE_reg0 (p : Polynomial ℕ) : Reg0Expr (setupSpanE p) :=
  reg0Expr_add _ _ (reg0Expr_add _ _ (reg0Expr_mul _ _ (reg0Expr_const _) reg0Expr_reg0)
    (reg0Expr_const _)) (reg0Expr_horner _ _ reg0Expr_reg0)

lemma setupME_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) :
    Reg0Expr (setupME p time d allowedIdx) :=
  reg0Expr_add _ _ (reg0Expr_add _ _ (reg0Expr_mul _ _ (setupSpanE_reg0 p)
    (reg0Expr_mul _ _ (setupSpanE_reg0 p) (setupSpanE_reg0 p))) (reg0Expr_const _))
    (reg0Expr_horner _ _ reg0Expr_reg0)

lemma setupSpanE_eval (p : Polynomial ℕ) (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (setupSpanE p).eval σ = setupSpan p N := by
  simp only [setupSpanE, Expr.eval, h0]
  rw [hornerExpr_coeffList_eval]
  simp only [Expr.eval, h0]
  simp [setupSpan]

lemma setupME_eval (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    (setupME p time d allowedIdx).eval σ = setupM p time d allowedIdx N := by
  have hspan : (setupSpanE p).eval σ = setupSpan p N :=
    setupSpanE_eval p σ N h0
  have hhorner : (hornerExpr (coeffList (emitLenPoly p time (d.numStates + 1)
      (d.numLetters + 1) allowedIdx.length)) (Expr.reg 0)).eval σ
      = (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
          allowedIdx.length).eval N := by
    rw [hornerExpr_coeffList_eval]
    simp only [Expr.eval, h0]
  simp only [setupME, Expr.eval, hspan, hhorner]
  simp [setupM]

/-! ## The nine parameters

The window and the time bound are polynomial evaluations, computed by Horner's
rule from register `0`.  The certificate length is the certificate polynomial
itself; the staged word length is `2N + 1`, the length of the paired input.  The
five staged word bases are placed one region apart above the parameter block, so
they clear both the block and each other.

The cells are the ones the five families already read, named through their own
definitions rather than as literals: a later change to the cell map moves this
list with it. -/

/-- The nine parameter cells with the expressions that fill them. -/
noncomputable def setupPairs (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : List (ℕ × Expr) :=
  [(persistWReg, hornerExpr (coeffList (cookWindowPoly p time)) (Expr.reg 0)),
   (persistTReg, hornerExpr (coeffList (timePoly p time)) (Expr.reg 0)),
   (initFreeLenReg, hornerExpr (coeffList p) (Expr.reg 0)),
   (initPrefLenReg, Expr.add (Expr.mul (Expr.const 2) (Expr.reg 0)) (Expr.const 1)),
   (initPrefBaseReg, Expr.add (setupME p time d allowedIdx) (Expr.const 30)),
   (transKindBaseReg, Expr.add (setupME p time d allowedIdx) (Expr.const 40)),
   (transArg1BaseReg, Expr.add (setupME p time d allowedIdx) (Expr.const 50)),
   (transArg2BaseReg, Expr.add (setupME p time d allowedIdx) (Expr.const 60)),
   (acceptOutBaseReg, Expr.add (setupME p time d allowedIdx) (Expr.const 70))]

lemma setupPairs_reg0 (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ∀ q ∈ setupPairs p time d allowedIdx, Reg0Expr q.2 := by
  intro q hq
  simp only [setupPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  have hM := setupME_reg0 p time d allowedIdx
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reg0Expr_horner _ _ reg0Expr_reg0
  · exact reg0Expr_horner _ _ reg0Expr_reg0
  · exact reg0Expr_horner _ _ reg0Expr_reg0
  · exact reg0Expr_add _ _ (reg0Expr_mul _ _ (reg0Expr_const _) reg0Expr_reg0)
      (reg0Expr_const _)
  · exact reg0Expr_add _ _ hM (reg0Expr_const _)
  · exact reg0Expr_add _ _ hM (reg0Expr_const _)
  · exact reg0Expr_add _ _ hM (reg0Expr_const _)
  · exact reg0Expr_add _ _ hM (reg0Expr_const _)
  · exact reg0Expr_add _ _ hM (reg0Expr_const _)

lemma setupPairs_nodup (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) :
    (List.map Prod.fst (setupPairs p time d allowedIdx)).Nodup := by
  simp [setupPairs, persistWReg, persistTReg, initFreeLenReg, initPrefLenReg,
    initPrefBaseReg, transKindBaseReg, transArg1BaseReg, transArg2BaseReg,
    acceptOutBaseReg]

lemma setupPairs_pos (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ) :
    ∀ j ∈ List.map Prod.fst (setupPairs p time d allowedIdx), 1 ≤ j := by
  intro j hj
  simp only [setupPairs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [persistWReg, persistTReg, initFreeLenReg, initPrefLenReg, initPrefBaseReg,
      transKindBaseReg, transArg1BaseReg, transArg2BaseReg, acceptOutBaseReg]

/-! ## The setup program

Its only arguments are the two polynomials, both fixed once the verifier is
chosen, so this is one program rather than a family indexed by the input — which
is what `BoundedWhileDecider.p` asks for. -/

/-- Fill the parameter block from the input length in register `0`. -/
noncomputable def setupProg (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) : Program :=
  paramSetupWrites (setupME p time d allowedIdx) (setupPairs p time d allowedIdx)

/-- Every parameter cell holds its intended value after the setup runs. -/
lemma setupProg_pins (p time : Polynomial ℕ) (d : TableauDescriptor) (allowedIdx : List ℕ)
    (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    ∀ q ∈ List.map (fun q : ℕ × Expr => (q.1, q.2.eval σ)) (setupPairs p time d allowedIdx),
      (setupProg p time d allowedIdx).eval σ (setupM p time d allowedIdx N + q.1) = q.2 :=
  paramSetupWrites_pins (setupME p time d allowedIdx) (setupME_reg0 p time d allowedIdx)
    (setupM p time d allowedIdx N) (setupPairs p time d allowedIdx)
    σ σ rfl (setupME_eval p time d allowedIdx σ N h0) (setupPairs_reg0 p time d allowedIdx)
    (setupPairs_nodup p time d allowedIdx) (setupPairs_pos p time d allowedIdx)

/-! ## One program, any input

A setup that worked at a single input length would prove nothing: the defect this
file exists to avoid is a program family, and any one member of a family is
correct at its own index.  Running the same program term at two unrelated input
lengths is what distinguishes the two. -/

/-- The same program term fills the block correctly at two unrelated input
lengths, so nothing input-dependent survives in its syntax. -/
lemma setupProg_serves_any_input (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx : List ℕ) (σ₁ σ₂ : Store) (N₁ N₂ : ℕ)
    (h₁ : σ₁ 0 = N₁) (h₂ : σ₂ 0 = N₂) :
    (∀ q ∈ List.map (fun q : ℕ × Expr => (q.1, q.2.eval σ₁)) (setupPairs p time d allowedIdx),
      (setupProg p time d allowedIdx).eval σ₁ (setupM p time d allowedIdx N₁ + q.1) = q.2) ∧
    (∀ q ∈ List.map (fun q : ℕ × Expr => (q.1, q.2.eval σ₂)) (setupPairs p time d allowedIdx),
      (setupProg p time d allowedIdx).eval σ₂ (setupM p time d allowedIdx N₂ + q.1) = q.2) :=
  ⟨setupProg_pins p time d allowedIdx σ₁ N₁ h₁, setupProg_pins p time d allowedIdx σ₂ N₂ h₂⟩

end NPComplete.CookLevin

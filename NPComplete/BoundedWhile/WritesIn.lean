module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BoundedWhile.Frame

/-!
# Store-relative write footprint

`AvoidsAbove` certifies a footprint from syntax alone, but only when every indirect
destination has a static lower bound. A destination computed from the store is invisible
to that check. `WritesIn S p σ` conservatively checks that the write destinations of `p`
from `σ` satisfy `S`; the predicate stays fixed as stores change, and some clauses add
safe extra conditions, such as checking a `scanList` base even for an empty list. This
certificate supports frame proofs without unfolding each program.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

/-- Every address `p` writes, starting from `σ`, satisfies `S`.

`S` is fixed against the initial store: do not re-index it as the store changes.
The `scanList` clause requires `S x` even when `xs = []`.  That is a safe
over-approximation — a sufficient condition, not an exact description of the writes. -/
@[construction_api] def WritesIn (S : ℕ → Prop) : Program → Store → Prop
  | .skip, _ => True
  | .assign r _, _ => S r
  | .assignInd eA _, σ => S (eA.eval σ)
  | .seq p q, σ => WritesIn S p σ ∧ WritesIn S q (p.eval σ)
  | .ifNZ e t f, σ => if e.eval σ ≠ 0 then WritesIn S t σ else WritesIn S f σ
  | .forN n b, σ => ∀ m < n.eval σ, WritesIn S b (loopEval b m σ)
  | .scanList xs x b, σ => S x ∧ ∀ i < xs.length,
      WritesIn S b (writeReg (scanListEval b (xs.take i) x σ) x xs[i]!)
  | .lookup _ _ v, _ => S v

/-- Loop-count induction, kept apart from the program induction in `WritesIn.eval_frame`. -/
@[construction_api] lemma loopEval_eq_of_writesIn {S : ℕ → Prop} {b : Program} {r : ℕ}
    (hbody : ∀ τ, WritesIn S b τ → b.eval τ r = τ r) :
    ∀ (k : ℕ) (σ : Store), (∀ m < k, WritesIn S b (loopEval b m σ)) →
      loopEval b k σ r = σ r := by
  intro k
  induction k with
  | zero => intro σ _; simp
  | succ k ih =>
    intro σ h
    rw [loopEval_succ]
    have h0 : WritesIn S b σ := by simpa [loopEval_zero] using h 0 (by omega)
    have htail : ∀ m < k, WritesIn S b (loopEval b m (b.eval σ)) := by
      intro m hm
      simpa [loopEval_succ] using h (m + 1) (by omega)
    rw [ih (b.eval σ) htail, hbody σ h0]

/-- List induction, kept apart from the program induction in `WritesIn.eval_frame`.
The binder is not the framed register, so binding each element leaves it unchanged. -/
@[construction_api] lemma scanListEval_eq_of_writesIn {S : ℕ → Prop} {b : Program} {x r : ℕ}
    (hbody : ∀ τ, WritesIn S b τ → b.eval τ r = τ r) (hrx : r ≠ x) :
    ∀ (xs : List ℕ) (σ : Store),
      (∀ i, i < xs.length →
        WritesIn S b (writeReg (scanListEval b (xs.take i) x σ) x xs[i]!)) →
      scanListEval b xs x σ r = σ r := by
  intro xs
  induction xs with
  | nil => intro σ _; simp
  | cons y ys ih =>
    intro σ h
    rw [scanListEval_cons]
    have h0 : WritesIn S b (writeReg σ x y) := by
      simpa [scanListEval_nil, List.take_zero, List.getElem!_cons_zero] using h 0 (by simp)
    have htail : ∀ i, i < ys.length →
        WritesIn S b
          (writeReg (scanListEval b (ys.take i) x (b.eval (writeReg σ x y))) x ys[i]!) := by
      intro i hi
      simpa [List.take_succ_cons, scanListEval_cons, List.getElem!_cons_succ] using
        h (i + 1) (by simp [List.length_cons]; omega)
    rw [ih _ htail, hbody _ h0, writeReg_diff _ _ _ _ hrx]

/-- A register outside `S` is unchanged. -/
@[construction_api] lemma WritesIn.eval_frame {S : ℕ → Prop} :
    ∀ (p : Program) (σ : Store), WritesIn S p σ → ∀ {r : ℕ}, ¬ S r → p.eval σ r = σ r := by
  intro p
  induction p with
  | skip => intro σ _ r _; simp
  | assign a _ =>
    intro σ h r hr
    rw [eval_assign, writeReg_diff _ _ _ _ (fun hra : r = a => hr (hra ▸ h))]
  | assignInd eA _ =>
    intro σ h r hr
    rw [eval_assignInd, writeReg_diff _ _ _ _ (fun hra : r = eA.eval σ => hr (hra ▸ h))]
  | seq _ _ ihp ihq =>
    intro σ h r hr
    rw [eval_seq, ihq _ h.2 hr, ihp _ h.1 hr]
  | ifNZ e t f iht ihf =>
    intro σ h r hr
    rw [eval_ifNZ]
    by_cases he : e.eval σ ≠ 0
    · rw [ite_eq_left he]
      exact iht σ (by simpa [WritesIn, he] using h) hr
    · rw [ite_eq_right he]
      exact ihf σ (by simpa [WritesIn, he] using h) hr
  | forN _ b ih =>
    intro σ h r hr
    rw [eval_forN]
    exact loopEval_eq_of_writesIn (fun τ hτ => ih τ hτ hr) _ _ h
  | scanList _ x b ih =>
    intro σ h r hr
    rw [eval_scanList]
    by_cases hrx : r = x
    · exact absurd h.1 (hrx ▸ hr)
    · exact scanListEval_eq_of_writesIn (fun τ hτ => ih τ hτ hr) hrx _ _ h.2
  | lookup _ _ v =>
    intro σ h r hr
    rw [eval_lookup, writeReg_diff _ _ _ _ (fun hrv : r = v => hr (hrv ▸ h))]

/-- A larger predicate still covers every write. -/
@[construction_api] lemma WritesIn.mono {S T : ℕ → Prop} (hST : ∀ a, S a → T a) :
    ∀ (p : Program) (σ : Store), WritesIn S p σ → WritesIn T p σ := by
  intro p
  induction p with
  | skip => intro _ _; trivial
  | assign r _ => intro _ h; exact hST r h
  | assignInd _ _ => intro _ h; exact hST _ h
  | seq _ _ ihp ihq => intro σ h; exact ⟨ihp σ h.1, ihq _ h.2⟩
  | ifNZ e _ _ iht ihf =>
    intro σ h
    by_cases he : e.eval σ ≠ 0
    · simpa [WritesIn, he] using iht σ (by simpa [WritesIn, he] using h)
    · simpa [WritesIn, he] using ihf σ (by simpa [WritesIn, he] using h)
  | forN _ _ ih => intro σ h m hm; exact ih _ (h m hm)
  | scanList _ x _ ih => intro σ h; exact ⟨hST x h.1, fun i hi => ih _ (h.2 i hi)⟩
  | lookup _ _ v => intro _ h; exact hST v h

/-- A static `AvoidsAbove` certificate is a `WritesIn` certificate for the complement of
the protected range, at every store. -/
@[construction_api] lemma Program.AvoidsAbove.writesIn {p : Program} {P : ℕ → Prop} {B : ℕ}
    (h : p.AvoidsAbove P B) : ∀ σ, WritesIn (fun a => ¬ (P a ∧ a < B)) p σ := by
  induction p with
  | skip => intro _; trivial
  | assign r _ => intro _; exact fun hp => h hp.1
  | assignInd eA _ =>
    intro σ ⟨_, hrB⟩
    have hB : B ≤ eA.lb := h
    have hle : eA.lb ≤ eA.eval σ := eA.lb_le σ
    omega
  | seq _ _ ihp ihq => intro σ; exact ⟨ihp h.1 σ, ihq h.2 _⟩
  | ifNZ _ _ _ iht ihf =>
    intro σ
    simp only [WritesIn]
    split
    · exact iht h.1 σ
    · exact ihf h.2 σ
  | forN _ _ ih => intro σ m _; exact ih h _
  | scanList _ _ _ ih => intro σ; exact ⟨fun hp => h.1 hp.1, fun _ _ => ih h.2 _⟩
  | lookup _ _ v => intro _; exact fun hp => h hp.1

/-- Both branches write inside `S`, so the conditional does, whichever branch is taken. -/
@[construction_api] lemma WritesIn.ifNZ_of {S : ℕ → Prop} {e : Expr} {t f : Program} {σ : Store}
    (ht : WritesIn S t σ) (hf : WritesIn S f σ) : WritesIn S (.ifNZ e t f) σ := by
  simp only [WritesIn]
  split <;> assumption

/-- An invariant that carries a `WritesIn` step discharges the visited-store obligations
of `forN` without unfolding `loopEval`. -/
@[construction_api] lemma WritesIn.forN_of_inv {S : ℕ → Prop} {n : Expr} {b : Program} {σ : Store}
    (I : Store → Prop) (hI : I σ)
    (hstep : ∀ τ, I τ → WritesIn S b τ ∧ I (b.eval τ)) :
    WritesIn S (.forN n b) σ := by
  intro m _
  exact (hstep _ (loopEval_inv b I (fun τ hτ => (hstep τ hτ).2) m σ hI)).1

/-- An indexed invariant preserved by one iteration holds at iteration `k`.
The index counts iterations from the entry store; it is not a value stored in a register. -/
@[stable_api] lemma loopEval_index_inv (b : Program) (N : ℕ) (I : ℕ → Store → Prop)
    (hstep : ∀ m τ, m < N → I m τ → I (m + 1) (b.eval τ)) :
    ∀ (k : ℕ) (σ : Store), k ≤ N → I 0 σ → I k (loopEval b k σ) := by
  intro k
  induction k with
  | zero => intro σ _ h0; simpa using h0
  | succ k ih =>
    intro σ hk h0
    rw [loopEval_succ_snoc]
    exact hstep k _ (by omega) (ih σ (by omega) h0)

/-- Indexed form of `forN_of_inv`: the invariant may mention the iteration index. -/
@[construction_api] lemma WritesIn.forN_of_indexed {S : ℕ → Prop} {n : Expr} {b : Program} {σ : Store}
    (I : ℕ → Store → Prop) (hI : I 0 σ)
    (hstep : ∀ m τ, m < n.eval σ → I m τ → WritesIn S b τ ∧ I (m + 1) (b.eval τ)) :
    WritesIn S (.forN n b) σ := by
  intro m hm
  have hIm : I m (loopEval b m σ) :=
    loopEval_index_inv b (n.eval σ) I (fun m τ hm hτ => (hstep m τ hm hτ).2)
      m σ (le_of_lt hm) hI
  exact (hstep m _ hm hIm).1

/-- An invariant that carries a `WritesIn` step for every list element discharges
`scanList` without mentioning prefixes or intermediate stores. -/
@[construction_api] lemma WritesIn.scanList_of_inv {S : ℕ → Prop} {xs : List ℕ} {x : ℕ} {b : Program}
    {σ : Store} (I : Store → Prop) (hx : S x) (hI : I σ)
    (hstep : ∀ τ y, y ∈ xs → I τ →
      WritesIn S b (writeReg τ x y) ∧ I (b.eval (writeReg τ x y))) :
    WritesIn S (.scanList xs x b) σ := by
  refine ⟨hx, ?_⟩
  suffices ∀ (ys : List ℕ) (σ' : Store), (∀ y, y ∈ ys → y ∈ xs) → I σ' →
      ∀ i, i < ys.length →
        WritesIn S b (writeReg (scanListEval b (ys.take i) x σ') x ys[i]!) from
    this xs σ (fun _ hy => hy) hI
  intro ys
  induction ys with
  | nil => intro _ _ _ i hi; simp at hi
  | cons y ys ih =>
    intro σ' hsub hI' i hi
    cases i with
    | zero =>
      have hy : y ∈ y :: ys := by simp
      simpa [scanListEval_nil, List.take_zero, List.getElem!_cons_zero] using
        (hstep σ' y (hsub y hy) hI').1
    | succ i =>
      have hy : y ∈ y :: ys := by simp
      have htail := ih (b.eval (writeReg σ' x y))
        (fun z hz => hsub z (List.mem_cons_of_mem y hz))
        ((hstep σ' y (hsub y hy) hI').2)
        i (by simp [List.length_cons] at hi; omega)
      simpa [List.take_succ_cons, scanListEval_cons, List.getElem!_cons_succ] using htail

end NPComplete.BoundedWhile

module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteLoop

/-!
Four of the reduction's five clause families end in a clause constructor of
compile-time fixed width, and each such leaf is the same instance of
`clauseLoopBody_leaf`: the tag cells are literal constants, so the combinator's
two per-literal obligations degenerate to "this variable expression reads only
control cells" and "it evaluates to the clause's variable number".  Discharging
that degeneration once per constructor is what lets a family's own file state
only the arithmetic of its variable numbering.

The literal lists mirror the constructors' own literal order, so a caller reads
off which expression feeds which position without unfolding `Clause`.  The tag
constants follow `litTag`: a positive literal writes `0`, a negative one `1`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

lemma map_eq_flatMap_singleton {α : Type} (L : List α) (c : α → Clause) :
    L.map c = L.flatMap (fun i => [c i]) := by
  induction L with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.flatMap_cons, ih, List.singleton_append]

/-! ## `unitPos`: one positive literal -/

lemma unitPos_len (v : ℕ) : (unitPos v).lits.length = 1 := rfl

lemma unitPos_var0 (v : ℕ) : litVar ((unitPos v).lits.getD 0 default) = v := rfl

/-- The single literal expression of a `unitPos` clause. -/
def unitPosLits (aE : Expr) : List (Expr × Expr) := [(.const 0, aE)]

lemma unitPosLits_length (aE : Expr) : (unitPosLits aE).length = 1 := rfl

lemma unitPosLits_get0 (aE : Expr) : (unitPosLits aE).getD 0 defLit = (.const 0, aE) := rfl

/-! ## `forbid3`: three negative literals -/

lemma forbid3_var0 (a b c : ℕ) : litVar ((forbid3 a b c).lits.getD 0 default) = a := rfl
lemma forbid3_var1 (a b c : ℕ) : litVar ((forbid3 a b c).lits.getD 1 default) = b := rfl
lemma forbid3_var2 (a b c : ℕ) : litVar ((forbid3 a b c).lits.getD 2 default) = c := rfl

/-- The three literal expressions of a `forbid3` clause. -/
def forbid3Lits (aE bE cE : Expr) : List (Expr × Expr) :=
  [(.const 1, aE), (.const 1, bE), (.const 1, cE)]

lemma forbid3Lits_length (aE bE cE : Expr) : (forbid3Lits aE bE cE).length = 3 := rfl

lemma forbid3Lits_get0 (aE bE cE : Expr) :
    (forbid3Lits aE bE cE).getD 0 defLit = (.const 1, aE) := rfl
lemma forbid3Lits_get1 (aE bE cE : Expr) :
    (forbid3Lits aE bE cE).getD 1 defLit = (.const 1, bE) := rfl
lemma forbid3Lits_get2 (aE bE cE : Expr) :
    (forbid3Lits aE bE cE).getD 2 defLit = (.const 1, cE) := rfl

/-! ## `imply2`: two negative literals and a positive conclusion -/

lemma imply2_var0 (a b d : ℕ) : litVar ((imply2 a b d).lits.getD 0 default) = a := rfl
lemma imply2_var1 (a b d : ℕ) : litVar ((imply2 a b d).lits.getD 1 default) = b := rfl
lemma imply2_var2 (a b d : ℕ) : litVar ((imply2 a b d).lits.getD 2 default) = d := rfl

/-- The three literal expressions of an `imply2` clause. -/
def imply2Lits (aE bE dE : Expr) : List (Expr × Expr) :=
  [(.const 1, aE), (.const 1, bE), (.const 0, dE)]

lemma imply2Lits_length (aE bE dE : Expr) : (imply2Lits aE bE dE).length = 3 := rfl

lemma imply2Lits_get0 (aE bE dE : Expr) :
    (imply2Lits aE bE dE).getD 0 defLit = (.const 1, aE) := rfl
lemma imply2Lits_get1 (aE bE dE : Expr) :
    (imply2Lits aE bE dE).getD 1 defLit = (.const 1, bE) := rfl
lemma imply2Lits_get2 (aE bE dE : Expr) :
    (imply2Lits aE bE dE).getD 2 defLit = (.const 0, dE) := rfl

/-- Specializes the leaf combinator to `imply2`. -/
lemma clauseLoopBody_imply2 (M Jmax wpJ iJ : ℕ) (aE bE dE : Expr)
    (pins : List (ℕ × ℕ)) (av bv dv : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hdepA : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → aE.eval σ' = aE.eval σ)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → bE.eval σ' = bE.eval σ)
    (hdepD : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → dE.eval σ' = dE.eval σ)
    (hvalA : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      aE.eval τ = av i)
    (hvalB : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      bE.eval τ = bv i)
    (hvalD : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      dE.eval τ = dv i) :
    ClauseLoopBody (leafProg wpJ iJ (imply2Lits aE bE dE)) M Jmax wpJ iJ (PinsHold M pins)
      (fun i => [imply2 (av i) (bv i) (dv i)]) := by
  refine clauseLoopBody_leaf M Jmax wpJ iJ (imply2Lits aE bE dE) pins
    (fun i => imply2 (av i) (bv i) (dv i)) hwpJ hwpJmax hiJ hiJmax hne hpin ?_ ?_ ?_
  · intro p hp σ σ' hσ hσ' hagree
    simp only [imply2Lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨rfl, hdepA σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepB σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepD σ σ' hσ hσ' hagree⟩
  · intro i; rfl
  · intro τ i k hF h0 hi hk
    rw [imply2Lits_length] at hk
    interval_cases k
    · rw [imply2Lits_get0]
      exact ⟨rfl, by rw [imply2_var0]; exact hvalA τ i hF h0 hi⟩
    · rw [imply2Lits_get1]
      exact ⟨rfl, by rw [imply2_var1]; exact hvalB τ i hF h0 hi⟩
    · rw [imply2Lits_get2]
      exact ⟨rfl, by rw [imply2_var2]; exact hvalD τ i hF h0 hi⟩

/-! ## `imply3`: three negative literals and a positive conclusion -/

lemma imply3_var0 (a b c d : ℕ) : litVar ((imply3 a b c d).lits.getD 0 default) = a := rfl
lemma imply3_var1 (a b c d : ℕ) : litVar ((imply3 a b c d).lits.getD 1 default) = b := rfl
lemma imply3_var2 (a b c d : ℕ) : litVar ((imply3 a b c d).lits.getD 2 default) = c := rfl
lemma imply3_var3 (a b c d : ℕ) : litVar ((imply3 a b c d).lits.getD 3 default) = d := rfl

/-- The four literal expressions of an `imply3` clause. -/
def imply3Lits (aE bE cE dE : Expr) : List (Expr × Expr) :=
  [(.const 1, aE), (.const 1, bE), (.const 1, cE), (.const 0, dE)]

lemma imply3Lits_length (aE bE cE dE : Expr) : (imply3Lits aE bE cE dE).length = 4 := rfl

lemma imply3Lits_get0 (aE bE cE dE : Expr) :
    (imply3Lits aE bE cE dE).getD 0 defLit = (.const 1, aE) := rfl
lemma imply3Lits_get1 (aE bE cE dE : Expr) :
    (imply3Lits aE bE cE dE).getD 1 defLit = (.const 1, bE) := rfl
lemma imply3Lits_get2 (aE bE cE dE : Expr) :
    (imply3Lits aE bE cE dE).getD 2 defLit = (.const 1, cE) := rfl
lemma imply3Lits_get3 (aE bE cE dE : Expr) :
    (imply3Lits aE bE cE dE).getD 3 defLit = (.const 0, dE) := rfl

/-- Specializes the leaf combinator to `imply3`. -/
lemma clauseLoopBody_imply3 (M Jmax wpJ iJ : ℕ) (aE bE cE dE : Expr)
    (pins : List (ℕ × ℕ)) (av bv cv dv : ℕ → ℕ)
    (hwpJ : 1 ≤ wpJ) (hwpJmax : wpJ ≤ Jmax)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hdepA : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → aE.eval σ' = aE.eval σ)
    (hdepB : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → bE.eval σ' = bE.eval σ)
    (hdepC : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → cE.eval σ' = cE.eval σ)
    (hdepD : ∀ σ σ' : Store, σ 0 = M → σ' 0 = M →
      (∀ j, 1 ≤ j → j ≤ Jmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) → dE.eval σ' = dE.eval σ)
    (hvalA : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      aE.eval τ = av i)
    (hvalB : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      bE.eval τ = bv i)
    (hvalC : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      cE.eval τ = cv i)
    (hvalD : ∀ (τ : Store) (i : ℕ), PinsHold M pins τ → τ 0 = M → τ (M + iJ) = i →
      dE.eval τ = dv i) :
    ClauseLoopBody (leafProg wpJ iJ (imply3Lits aE bE cE dE)) M Jmax wpJ iJ (PinsHold M pins)
      (fun i => [imply3 (av i) (bv i) (cv i) (dv i)]) := by
  refine clauseLoopBody_leaf M Jmax wpJ iJ (imply3Lits aE bE cE dE) pins
    (fun i => imply3 (av i) (bv i) (cv i) (dv i)) hwpJ hwpJmax hiJ hiJmax hne hpin ?_ ?_ ?_
  · intro p hp σ σ' hσ hσ' hagree
    simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨rfl, hdepA σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepB σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepC σ σ' hσ hσ' hagree⟩
    · exact ⟨rfl, hdepD σ σ' hσ hσ' hagree⟩
  · intro i; rfl
  · intro τ i k hF h0 hi hk
    rw [imply3Lits_length] at hk
    interval_cases k
    · rw [imply3Lits_get0]
      exact ⟨rfl, by rw [imply3_var0]; exact hvalA τ i hF h0 hi⟩
    · rw [imply3Lits_get1]
      exact ⟨rfl, by rw [imply3_var1]; exact hvalB τ i hF h0 hi⟩
    · rw [imply3Lits_get2]
      exact ⟨rfl, by rw [imply3_var2]; exact hvalC τ i hF h0 hi⟩
    · rw [imply3Lits_get3]
      exact ⟨rfl, by rw [imply3_var3]; exact hvalD τ i hF h0 hi⟩

end NPComplete.CookLevin

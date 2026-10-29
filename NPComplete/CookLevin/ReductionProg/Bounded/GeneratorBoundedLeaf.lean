module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedClause

/-!
Between a clause row and a family stand the two combinators every family shares:
a leaf, which writes one row and bumps its counter, and a loop, which resets a
counter and runs a body.  Both are bounded for the same reason — the counter
cells live in the tight block, so a bump moves a value the tight envelope already
covers — and both need that fact stated as an effect as well as an obligation,
since the next iteration starts from the store they leave.

The counter bump is where the tight envelope has to have slack: after the last
iteration the counter holds the trip count, and the bump that ends that iteration
pushes it one past.  Asking `K` to cover `count + 1` rather than `count` is what
keeps the bound true at the loop's final store, and costs nothing downstream.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Counter bumps -/

/-- A counter bump keeps both envelopes, provided the tight one covers where the
    counter lands. -/
lemma ctlAssign_bump_preserves (K S M iJ c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) (hK : σ (M + iJ) + c ≤ K)
    (hKS : K ≤ S) :
    (ctlAssign iJ (.add (ctlCell iJ) (.const c))).eval σ 0 = M ∧
      TightCells K M ((ctlAssign iJ (.add (ctlCell iJ) (.const c))).eval σ) ∧
      StoreValuesLe S ((ctlAssign iJ (.add (ctlCell iJ) (.const c))).eval σ) := by
  have hev : (ctlAssign iJ (.add (ctlCell iJ) (.const c))).eval σ
      = writeReg σ (M + iJ) (σ (M + iJ) + c) := by
    unfold ctlAssign
    rw [eval_assignInd]
    simp only [Expr.eval, ctlAddr, ctlCell, h0]
  rw [hev]
  refine ⟨by rw [writeReg_diff σ (M + iJ) _ 0 (by omega), h0], fun j h2 h24 => ?_,
    fun i => ?_⟩
  · by_cases hj : j = iJ
    · rw [hj, writeReg_same]; exact hK
    · rw [writeReg_diff σ (M + iJ) _ (M + j) (by omega)]; exact ht j h2 h24
  · by_cases hi : i = M + iJ
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ (M + iJ) _ i hi]; exact hst i

/-- A counter reset keeps both envelopes unconditionally. -/
lemma ctlAssign_zero_preserves (K S M iJ : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) :
    (ctlAssign iJ (.const 0)).eval σ 0 = M ∧
      (ctlAssign iJ (.const 0)).eval σ (M + iJ) = 0 ∧
      TightCells K M ((ctlAssign iJ (.const 0)).eval σ) ∧
      StoreValuesLe S ((ctlAssign iJ (.const 0)).eval σ) := by
  have hev : (ctlAssign iJ (.const 0)).eval σ = writeReg σ (M + iJ) 0 := by
    unfold ctlAssign
    rw [eval_assignInd]
    simp only [Expr.eval, ctlAddr, h0]
  rw [hev]
  refine ⟨by rw [writeReg_diff σ (M + iJ) 0 0 (by omega), h0], writeReg_same _ _ _,
    fun j h2 h24 => ?_, fun i => ?_⟩
  · by_cases hj : j = iJ
    · rw [hj, writeReg_same]; omega
    · rw [writeReg_diff σ (M + iJ) 0 (M + j) (by omega)]; exact ht j h2 h24
  · by_cases hi : i = M + iJ
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ (M + iJ) 0 i hi]; exact hst i

/-! ## The leaf -/

/-- The innermost body of every family: one clause row, then a counter bump. -/
lemma programBoundedIn_leafProg (K S B M wp iJ : ℕ) (σ : Store)
    (lits : List (Expr × Expr))
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hlen : wp + 2 + 2 * lits.length ≤ S) (hSB : S ≤ B) (hcnt : lits.length ≤ S)
    (hlits : LitsBounded K S B M lits) (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hK1 : K + 1 ≤ B) :
    ProgramBoundedIn B σ (leafProg wpJ iJ lits) := by
  obtain ⟨hpb, e0, _, et, _, _⟩ := writeClauseProg_bounded K S B M wp σ lits h0 hwp hsep hMB
    hlen hSB hcnt hlits ht hst
  refine ⟨hpb, programBoundedIn_ctlAssign_bump B M _ iJ 1 _ e0 (by omega) rfl ?_⟩
  have := et iJ hiJ hiJ2
  omega

/-- The leaf's effect on the envelopes, for the next iteration's entry. -/
lemma leafProg_exit (K S B M wp iJ : ℕ) (σ : Store) (lits : List (Expr × Expr))
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hlen : wp + 2 + 2 * lits.length ≤ S) (hSB : S ≤ B) (hcnt : lits.length ≤ S)
    (hlits : LitsBounded K S B M lits) (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hbump : σ (M + iJ) + 1 ≤ K) (hKS : K ≤ S) :
    (leafProg wpJ iJ lits).eval σ 0 = M ∧
      (leafProg wpJ iJ lits).eval σ (M + wpJ) = wp + 2 + 2 * lits.length ∧
      TightCells K M ((leafProg wpJ iJ lits).eval σ) ∧
      StoreValuesLe S ((leafProg wpJ iJ lits).eval σ) := by
  obtain ⟨_, e0, ew, et, es, efr⟩ := writeClauseProg_bounded K S B M wp σ lits h0 hwp hsep hMB
    hlen hSB hcnt hlits ht hst
  obtain ⟨g0, gt, gs⟩ := ctlAssign_bump_preserves K S M iJ 1 _ e0 hiJ hiJ2 et es (by
    have hiv2 : (writeClauseProg wpJ lits).eval σ (M + iJ) = σ (M + iJ) :=
      efr (M + iJ) (by omega) (by simp only [wpJ]; omega)
    omega) hKS
  unfold leafProg
  rw [eval_seq]
  refine ⟨g0, ?_, gt, gs⟩
  have hne : M + wpJ ≠ M + iJ := by simp only [wpJ]; omega
  rw [show (ctlAssign iJ (.add (ctlCell iJ) (.const 1))).eval
      ((writeClauseProg wpJ lits).eval σ) (M + wpJ)
    = (writeClauseProg wpJ lits).eval σ (M + wpJ) from
    ctlAssign_eval_diff iJ _ _ (M + wpJ) (by rw [e0]; omega), ew]

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedPersist

/-!
The trans family's leaf writes one of four blocks: one of three `imply3` blocks
for halt, write, or move, or a `forbid3` block when the write or move is invalid.
Each block uses three `writeClauseProg` calls with the same antecedent literals
(state, head, cell); an `imply3` block varies the consequent across its three
clauses, while the `forbid3` block writes the same clause three times.  As with
the other families, one inequality, `TransEnv`, dominates every majorant the
nine expressions use.

`transHeadMoveEParam` is an exception in this file.  Its builder folds two
`.sub` layers around each control cell it reads, so a packaged lemma for its bound
would ask for a blanket `∀ j ≤ 23, σ (M+j) ≤ K` rather than per-cell hypotheses.
That blanket covers
indices `0` (the store's base marker) and `1` (`wpJ`, the write pointer), neither
of which `TightCells`/`StoreValuesLe` bounds by `K`.  In particular, `wpJ`
grows past `K` as the table fills, so weakening from `S` cannot close the gap
(`K ≤ S` runs the wrong direction).  The expression itself reads only `lvJ0`,
`lvJ1`, `tmpJ`, and `wReg`, all within `TightCells`'s range `[2,24]`, so
`litsBounded_trans_head_move` proves its two obligations by inlining that
arithmetic against those four per-cell facts, rather than using the blanket
hypothesis.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- One inequality dominating every majorant the trans expressions use.  The
    tail term covers both the cell-same/cell-write shapes (`K * mS + K`) and
    the head-move shape (`2 * K`), since neither dominates the other when
    `mS = 0`. -/
def TransEnv (K X nS mS : ℕ) : Prop :=
  K * (nS + K + K * mS) + (nS + K + K * mS) + nS + K + K * mS + 2 * K ≤ X

lemma transEnv_of_le {K X X' nS mS : ℕ} (h : TransEnv K X nS mS) (hX : X ≤ X') :
    TransEnv K X' nS mS := le_trans h hX

/-! ## The `forbid3` block (`transForbidBlockProgParam`)

All three rows of the block write the same three literals, so one lemma
covers every `writeClauseProg` call inside it. -/

/-- The leaf writing the `forbid3` block: the same three literals, at every
    row of the fixed three-row block. -/
lemma litsBounded_trans_forbid (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (forbid3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [forbid3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)

/-! ## The `imply3` blocks (halt / write / move)

Each block writes three `imply3` rows sharing the same antecedent — state,
head, cell — and differing only in the consequent, so one lemma per
consequent covers the three `writeClauseProg` calls with that shape across
`transHaltBlockProgParam`, `transWriteBlockProgParam`, and
`transMoveBlockProgParam`. -/

/-- The leaf writing the state-same consequence: state/head/cell imply
    state-same. -/
lemma litsBounded_trans_state_same (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateSameEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_transStateSameEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateSameEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)

/-- The leaf writing the head-same consequence: state/head/cell imply
    head-same. -/
lemma litsBounded_trans_head_same (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadSameEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_transHeadSameEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadSameEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)

/-- The leaf writing the cell-same consequence: state/head/cell imply
    cell-same. -/
lemma litsBounded_trans_cell_same (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellSameEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_transCellSameEParam M K B nS mS wReg τ hK1 h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellSameEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)

/-- The leaf writing the state-next consequence: state/head/cell imply
    state-next. -/
lemma litsBounded_trans_state_next (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transStateNextEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have g6 : τ (M + litJ) ≤ K := ht litJ (by norm_num [litJ]) (by norm_num [litJ])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_transStateNextEParam M K B nS mS wReg τ hK1 h0 g2 g6 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateNextEParam_eval_le M K nS mS wReg τ h0 g2 g6 gw) (by omega)

/-- The leaf writing the cell-write consequence: state/head/cell imply
    cell-write. -/
lemma litsBounded_trans_cell_write (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transCellWriteEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have g7 : τ (M + tmpJ) ≤ K := ht tmpJ (by norm_num [tmpJ]) (by norm_num [tmpJ])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · exact exprBoundedIn_transCellWriteEParam M K B nS mS wReg τ hK1 h0 g2 g3 g7 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellWriteEParam_eval_le M K nS mS wReg τ h0 g2 g3 g7 gw) (by omega)

/-- The leaf writing the head-move consequence: state/head/cell imply
    head-move.  See the module docstring for why this proof is inlined
    rather than going through a blanket bound on the control cells. -/
lemma litsBounded_trans_head_move (K S B M nS mS wReg : ℕ) (hK1 : 1 ≤ K)
    (hwR : 2 ≤ wReg) (hwR2 : wReg ≤ 23) (hMB : M + 24 ≤ B)
    (henvB : TransEnv K B nS mS) (henvS : TransEnv K S nS mS)
    (hnS : nS ≤ B) (hmS : mS ≤ B) :
    LitsBounded K S B M (imply3Lits (transStateEParam nS mS wReg)
      (transHeadEParam nS mS wReg) (transCellEParam nS mS wReg)
      (transHeadMoveEParam nS mS wReg)) := by
  unfold TransEnv at henvB henvS
  intro q hq τ h0 ht hst
  have g2 : τ (M + lvJ0) ≤ K := ht lvJ0 (by norm_num [lvJ0]) (by norm_num [lvJ0])
  have g3 : τ (M + lvJ1) ≤ K := ht lvJ1 (by norm_num [lvJ1]) (by norm_num [lvJ1])
  have g4 : τ (M + lvJ2) ≤ K := ht lvJ2 (by norm_num [lvJ2]) (by norm_num [lvJ2])
  have g5 : τ (M + lvJ3) ≤ K := ht lvJ3 (by norm_num [lvJ3]) (by norm_num [lvJ3])
  have g7 : τ (M + tmpJ) ≤ K := ht tmpJ (by norm_num [tmpJ]) (by norm_num [tmpJ])
  have gw : τ (M + wReg) ≤ K := ht wReg hwR (by omega)
  have hb : τ (M + wReg) * mS ≤ K * mS := Nat.mul_le_mul_right _ gw
  have hsum : nS + τ (M + wReg) + τ (M + wReg) * mS ≤ nS + K + K * mS := by omega
  have hmul : (τ (M + lvJ0) + 1) * (nS + τ (M + wReg) + τ (M + wReg) * mS)
      ≤ K * (nS + K + K * mS) + (nS + K + K * mS) := by
    calc (τ (M + lvJ0) + 1) * (nS + τ (M + wReg) + τ (M + wReg) * mS)
        ≤ (K + 1) * (nS + K + K * mS) := Nat.mul_le_mul (by omega) hsum
      _ = K * (nS + K + K * mS) + (nS + K + K * mS) := by ring
  simp only [imply3Lits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transStateEParam M K B nS mS wReg τ hK1 h0 g2 g4 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transStateEParam_eval_le M K nS mS wReg τ h0 g2 g4 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transHeadEParam M K B nS mS wReg τ hK1 h0 g2 g3 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transHeadEParam_eval_le M K nS mS wReg τ h0 g2 g3 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn]; omega, ?_, by simp [Expr.eval]; omega, ?_⟩
    · exact exprBoundedIn_transCellEParam M K B nS mS wReg τ h0 g2 g3 g5 gw hwR2
        (by omega) (by omega) hnS hmS
    · exact le_trans (transCellEParam_eval_le M K nS mS wReg τ h0 g2 g3 g5 gw) (by omega)
  · refine ⟨by simp [ExprBoundedIn], ?_, by simp [Expr.eval], ?_⟩
    · simp only [lvJ0, lvJ1, tmpJ] at g2 g3 g7 hmul
      unfold transHeadMoveEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 tmpJ
      simp only [ExprBoundedIn, Expr.eval, h0]
      repeat' apply And.intro
      all_goals omega
    · simp only [lvJ0, lvJ1, tmpJ] at g2 g3 g7 hmul
      unfold transHeadMoveEParam denseHeadE denseBlockE ctlCell ctlAddr lvJ0 lvJ1 tmpJ
      simp only [Expr.eval, h0]
      omega

end NPComplete.CookLevin

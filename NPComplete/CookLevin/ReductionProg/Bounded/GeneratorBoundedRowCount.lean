module

public import NPComplete.CookLevin.ReductionProg.GeneratorEnvelopeAgg
public import NPComplete.CookLevin.ReductionProg.GeneratorScanFree
public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedLoad

/-!
The row-count fragment is inserted between setup and table emission.  Its
boundedness needs both the triangular-loop invariant and an envelope bound for
the arithmetic clause-count expression; keeping those obligations here lets
the top-level proof transport the writer contract across the new stage.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

lemma triAcc_le_square (x : ℕ) : triAcc x ≤ x * x := by
  induction x with
  | zero => simp [triAcc]
  | succ x ih => rw [triAcc]; nlinarith

lemma triAcc_mono (x y : ℕ) (h : x ≤ y) : triAcc x ≤ triAcc y := by
  induction y generalizing x with
  | zero =>
      have hx : x = 0 := by omega
      subst x
      simp [triAcc]
  | succ y ih =>
      by_cases hx : x = y + 1
      · subst x
        rfl
      · have hxy : x ≤ y := by omega
        have hi := ih x hxy
        rw [triAcc]
        exact hi.trans (by omega)

lemma programBoundedIn_ctlAssign_add (B M j a b : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hj : M + j ≤ B) (ha : M + a ≤ B) (hb : M + b ≤ B)
    (hval : σ (M + a) + σ (M + b) ≤ B) :
    ProgramBoundedIn B σ (ctlAssign j (.add (ctlCell a) (ctlCell b))) := by
  unfold ctlAssign
  refine ⟨exprBoundedIn_ctlAddr B M j σ h0 hj,
    ⟨exprBoundedIn_ctlCell B M a σ h0 ha, exprBoundedIn_ctlCell B M b σ h0 hb, ?_⟩,
    by rw [ctlAddr_eval_at M j σ h0]; omega⟩
  simp only [ctlCell_eval, h0]
  omega

lemma clauseCount_small_bounds (B K n m W : ℕ)
    (hKsq : K * (K * (4 + 3 * m)) ≤ B) (hnK : n ≤ K) (hmK : m ≤ K)
    (hWK : W ≤ K) :
    n * (m * 3) ≤ B ∧ W * (n * (m * 3)) ≤ B ∧
      W * ((W - 1) * m) ≤ B ∧ W * W ≤ B := by
  have hnm : n * m ≤ K * K := Nat.mul_le_mul hnK hmK
  have hnm3 : n * (m * 3) ≤ K * (K * (4 + 3 * m)) := by
    have hnm3' : n * m * 3 ≤ K * K * 3 := Nat.mul_le_mul_right 3 hnm
    have hcoef : K * K * 3 ≤ K * K * (4 + 3 * m) :=
      Nat.mul_le_mul_left (K * K) (by omega)
    simpa [Nat.mul_assoc] using hnm3'.trans hcoef
  have hWn : W * n ≤ K * K := Nat.mul_le_mul hWK hnK
  have hWnm : W * n * m ≤ K * K * m := Nat.mul_le_mul_right m hWn
  have hWnm3 : W * (n * (m * 3)) ≤ K * (K * (4 + 3 * m)) := by
    have hWnm3' : W * n * m * 3 ≤ K * K * m * 3 := Nat.mul_le_mul_right 3 hWnm
    have hcoef : K * K * m * 3 ≤ K * K * (4 + 3 * m) := by
      have htmp := Nat.mul_le_mul_left (K * K) (show m * 3 ≤ 4 + 3 * m by omega)
      simpa [Nat.mul_assoc] using htmp
    simpa [Nat.mul_assoc] using hWnm3'.trans hcoef
  have hWm : (W - 1) * m ≤ W * m := Nat.mul_le_mul_right m (Nat.sub_le _ _)
  have hWsub0 : W * ((W - 1) * m) ≤ W * (W * m) := Nat.mul_le_mul_left W hWm
  have hWsub1 : W * (W * m) ≤ K * (K * m) :=
    Nat.mul_le_mul hWK (Nat.mul_le_mul_right m hWK)
  have hWsub2 : W * ((W - 1) * m) ≤ K * (K * (4 + 3 * m)) := by
    have h2 : K * m ≤ K * (4 + 3 * m) := Nat.mul_le_mul_left K (by omega)
    have hcoef : K * (K * m) ≤ K * (K * (4 + 3 * m)) := Nat.mul_le_mul_left K h2
    simpa [Nat.mul_assoc] using hWsub0.trans (hWsub1.trans hcoef)
  have hWsquare : W * W ≤ K * (K * (4 + 3 * m)) := by
    have hWW : W * W ≤ K * K := Nat.mul_le_mul hWK hWK
    have h2 : K ≤ K * (4 + 3 * m) := by
      simpa using (Nat.mul_le_mul_left K (show 1 ≤ 4 + 3 * m by omega))
    have hcoef : K * K ≤ K * (K * (4 + 3 * m)) := by
      have := Nat.mul_le_mul_left K h2
      simpa [Nat.mul_assoc] using this
    simpa [Nat.mul_assoc] using hWW.trans hcoef
  exact ⟨hnm3.trans hKsq, hWnm3.trans hKsq, hWsub2.trans hKsq, hWsquare.trans hKsq⟩

lemma clauseCount_le_formula (n m T W F : ℕ) :
    clauseCount n m T W F ≤
      (T + 1) * (n * n + 2 + (W * W + 2) + W * (m * m + 2))
        + (2 + W + F) + T * W * (n * m * 3) + T * (W * W) * m + (W * W + 1) := by
  have hn : triAcc n ≤ n * n := triAcc_le_square n
  have hm : triAcc m ≤ m * m := triAcc_le_square m
  have hW : triAcc W ≤ W * W := triAcc_le_square W
  have hinner : triAcc n + 1 + (triAcc W + 1) + W * (triAcc m + 1) ≤
      n * n + 2 + (W * W + 2) + W * (m * m + 2) := by
    have hnm : triAcc n + 1 ≤ n * n + 1 := Nat.add_le_add_right hn 1
    have hwm : triAcc m + 1 ≤ m * m + 1 := Nat.add_le_add_right hm 1
    have hwterm : W * (triAcc m + 1) ≤ W * (m * m + 1) := Nat.mul_le_mul_left W hwm
    have hright0 : W * (m * m + 1) ≤ W * (m * m + 2) := Nat.mul_le_mul_left W (by omega)
    have hright : W * (triAcc m + 1) ≤ W * (m * m + 2) := hwterm.trans hright0
    have hleft : triAcc n + 1 + (triAcc W + 1) ≤ n * n + 1 + (W * W + 1) := by
      have hW1 : triAcc W + 1 ≤ W * W + 1 := Nat.add_le_add_right hW 1
      omega
    omega
  have hfirst := Nat.mul_le_mul_left (T + 1) hinner
  have hfourth : T * W * (W - 1) * m ≤ T * (W * W) * m := by
    have hs : W - 1 ≤ W := Nat.sub_le _ _
    have hsw : W * (W - 1) ≤ W * W := Nat.mul_le_mul_left W hs
    have hst := Nat.mul_le_mul_left T hsw
    exact Nat.mul_le_mul_right m (by simpa [Nat.mul_assoc] using hst)
  have hthird : T * W * n * m * 3 = T * W * (n * m * 3) := by ring
  simp only [clauseCount]
  omega

lemma clauseCount_le_poly (p time : Polynomial ℕ) (n m N : ℕ) :
    clauseCount n m ((timePoly p time).eval N) ((cookWindowPoly p time).eval N) (p.eval N) ≤
      (clauseCountPoly p time (n + 1) (m + 1)).eval N := by
  set T := (timePoly p time).eval N with hT
  set W := (cookWindowPoly p time).eval N with hW
  set F := p.eval N with hF
  change clauseCount n m T W F ≤ (clauseCountPoly p time (n + 1) (m + 1)).eval N
  have hbase := clauseCount_le_formula n m T W F
  have heval : (clauseCountPoly p time (n + 1) (m + 1)).eval N =
      (T + 1) * ((n + 1) * (n + 1) + 2 + (W * W + 2) + W * ((m + 1) * (m + 1) + 2))
        + (2 + W + F) + T * W * ((n + 1) * (m + 1) * 3)
        + T * (W * W) * (m + 1) + (W * W + 1) := by
    simp [clauseCountPoly, T, W, F]
  rw [heval]
  have hn : n * n ≤ (n + 1) * (n + 1) := by nlinarith
  have hm : m * m ≤ (m + 1) * (m + 1) := by nlinarith
  have hinner : n * n + 2 + (W * W + 2) + W * (m * m + 2) ≤
      (n + 1) * (n + 1) + 2 + (W * W + 2) + W * ((m + 1) * (m + 1) + 2) := by
    have hwm := Nat.mul_le_mul_left W (Nat.add_le_add_right hm 2)
    omega
  have hfirst := Nat.mul_le_mul_left (T + 1) hinner
  have hcross : n * m * 3 ≤ (n + 1) * (m + 1) * 3 := by nlinarith
  have hthird := Nat.mul_le_mul_left (T * W) hcross
  have hfourth : T * (W * W) * m ≤ T * (W * W) * (m + 1) := by
    exact Nat.mul_le_mul_left (T * (W * W)) (by omega)
  have hthird' : T * W * n * m * 3 = T * W * (n * m * 3) := by ring
  have hcross' : T * W * ((n + 1) * (m + 1) * 3) =
      T * W * (n + 1) * (m + 1) * 3 := by ring
  simp only [clauseCount] at hbase ⊢
  omega

lemma poly_eval_mono_nat (q : Polynomial ℕ) {x y : ℕ} (hxy : x ≤ y) : q.eval x ≤ q.eval y := by
  rw [← hornerVal_coeffList q x, ← hornerVal_coeffList q y]
  exact hornerVal_mono (coeffList q) x y hxy

lemma clauseCount_le_emitLenPoly (p time : Polynomial ℕ) (n m al N : ℕ) :
    clauseCount n m ((timePoly p time).eval N) ((cookWindowPoly p time).eval N) (p.eval N) ≤
      (emitLenPoly p time (n + 1) (m + 1) al).eval N := by
  have hcp := clauseCount_le_poly p time n m N
  have hce : (clauseCountPoly p time (n + 1) (m + 1)).eval N ≤
      (emitLenPoly p time (n + 1) (m + 1) al).eval N := by
    simp [emitLenPoly]
    omega
  exact hcp.trans hce

lemma clauseCount_le_envB (p time : Polynomial ℕ) (d : TableauDescriptor)
    (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) :
    clauseCount d.numStates d.numLetters ((timePoly p time).eval N)
        ((cookWindowPoly p time).eval N) (p.eval N) ≤
      (envB p time d prefIdx allowedIdx outIdx).eval N := by
  have hce := clauseCount_le_emitLenPoly p time d.numStates d.numLetters allowedIdx.length N
  have hE0 : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
      allowedIdx.length).eval N ≤
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval (N + 1) :=
    poly_eval_mono_nat _ (by omega)
  have hB := envB_eval p time d prefIdx allowedIdx outIdx N
  omega

lemma exprBoundedIn_clauseCountExpr (B K M n m T W F : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hT : σ (M + persistTReg) = T)
    (hW : σ (M + persistWReg) = W) (hF : σ (M + initFreeLenReg) = F)
    (hA : σ (M + rowCountReg) = triAcc W) (hM70 : M + 70 ≤ B)
    (hKsq : K * (K * (4 + 3 * m)) ≤ B) (hKB : K ≤ B)
    (hnK : n ≤ K) (hmK : m ≤ K) (hWK : W ≤ K)
    (hcount : clauseCount n m T W F ≤ B) :
    ExprBoundedIn B σ (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg) := by
  have hsmall := clauseCount_small_bounds B K n m W hKsq hnK hmK hWK
  have hT' : σ (M + 16) = T := by simpa [persistTReg] using hT
  have hW' : σ (M + 15) = W := by simpa [persistWReg] using hW
  have hF' : σ (M + 17) = F := by simpa [initFreeLenReg] using hF
  have hA' : σ (M + 25) = triAcc W := by simpa [rowCountReg] using hA
  have hcount' :
      (T + 1) * (triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)))
        + (2 + W + F) + T * (W * (n * (m * 3)))
        + T * (W * ((W - 1) * m)) + (W * W + 1) ≤ B := by
    simpa [clauseCount, Nat.mul_assoc, Nat.add_assoc] using hcount
  have hfirst : (T + 1) * (triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1))) ≤ B := by omega
  have hsecond : 2 + W + F ≤ B := by omega
  have hthird : T * (W * (n * (m * 3))) ≤ B := by omega
  have hfourth : T * (W * ((W - 1) * m)) ≤ B := by omega
  have hlast : W * W + 1 ≤ B := by omega
  have hinter : 1 ≤ triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)) := by omega
  have hfirst_inner : triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)) ≤
      (T + 1) * (triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1))) := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hT1 : T + 1 ≤ (T + 1) * (triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1))) := by
    exact Nat.le_mul_of_pos_right _ hinter
  have hTle : T ≤ B := by omega
  have hWle : W ≤ B := by omega
  have hFle : F ≤ B := by omega
  have hKK : K * K ≤ B := by
    have h1 : 1 ≤ 4 + 3 * m := by omega
    have h2 : K ≤ K * (4 + 3 * m) := by simpa using (Nat.mul_le_mul_left K h1)
    have h3 : K * K ≤ K * (K * (4 + 3 * m)) := by
      have := Nat.mul_le_mul_left K h2
      simpa [Nat.mul_assoc] using this
    exact h3.trans hKsq
  have htri_add_one : ∀ x : ℕ, x ≤ K → triAcc x + 1 ≤ B := by
    intro x hxK
    have htx : triAcc x ≤ x * x := triAcc_le_square x
    by_cases hK0 : K = 0
    · have hx0 : x = 0 := by omega
      subst x
      simp [triAcc]
      omega
    · have hKpos : 1 ≤ K := by omega
      have hstrict : K * K < K * (K * (4 + 3 * m)) := by nlinarith
      have hlt : triAcc x < B := by
        exact lt_of_le_of_lt (htx.trans (Nat.mul_le_mul hxK hxK))
          (lt_of_lt_of_le hstrict hKsq)
      omega
  have htnle : triAcc n ≤ B := by have := htri_add_one n hnK; omega
  have htmle : triAcc m ≤ B := by have := htri_add_one m hmK; omega
  have hAW : triAcc W ≤ B := by have := htri_add_one W hWK; omega
  have hAm : W * (triAcc m + 1) ≤ B := by
    have hsub : W * (triAcc m + 1) ≤ triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)) := by omega
    have hmul := Nat.mul_le_mul_left (T + 1) hsub
    have hmul_le := Nat.mul_le_mul_left (T + 1) (show triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)) ≤
      triAcc n + 1 + (triAcc W + 1 + W * (triAcc m + 1)) by omega)
    omega
  have hnle : n ≤ B := le_trans hnK hKB
  have hmle : m ≤ B := le_trans hmK hKB
  have h3 : 3 ≤ B := by omega
  have hT1B : T + 1 ≤ B := hT1.trans hfirst
  have htn1B : triAcc n + 1 ≤ B := htri_add_one n hnK
  have htm1B : triAcc m + 1 ≤ B := htri_add_one m hmK
  have hAW1B : triAcc W + 1 ≤ B := htri_add_one W hWK
  have hm3B : m * 3 ≤ B := by
    have hmk : m * 3 ≤ K * (K * (4 + 3 * m)) := by
      by_cases hK0 : K = 0
      · have hm0 : m = 0 := by omega
        simp [hK0, hm0]
      · have h1 : m * 3 ≤ K * 3 := Nat.mul_le_mul_right 3 hmK
        have h2 : K * 3 ≤ K * (4 + 3 * m) := Nat.mul_le_mul_left K (by omega)
        have hK1 : 1 ≤ K := by omega
        have h3' : K * (4 + 3 * m) ≤ K * (K * (4 + 3 * m)) := by
          have hc : 4 + 3 * m ≤ K * (4 + 3 * m) := by
            simpa using (Nat.mul_le_mul_right (4 + 3 * m) hK1)
          exact Nat.mul_le_mul_left K hc
        exact h1.trans (h2.trans h3')
    exact hmk.trans hKsq
  have hsubm : (W - 1) * m ≤ B := by
    have hs : W - 1 ≤ K := le_trans (Nat.sub_le _ _) hWK
    exact (Nat.mul_le_mul hs hmK).trans hKK
  simp only [clauseCountExpr, ctlCell, ctlAddr, ExprBoundedIn, Expr.eval, h0,
    persistTReg, persistWReg, initFreeLenReg, rowCountReg]
  rw [hT', hW', hF', hA']
  clear h0 hT hW hF hA hT' hW' hF' hA'
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals (try constructor)
  all_goals omega

lemma triAccStep_bounded (B K M W m' : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrow : σ (M + rowCountReg) = triAcc m')
    (hiter : σ (M + iterReg) = m') (hW : W ≤ K) (hKB : K ≤ B)
    (hM70 : M + 70 ≤ B) (htriW : triAcc W ≤ B) (hm' : m' < W) :
    ProgramBoundedIn B σ (triAccStep rowCountReg iterReg) := by
  have hmp1 : m' + 1 ≤ W := by omega
  have htri : triAcc (m' + 1) ≤ triAcc W := triAcc_mono _ _ hmp1
  have hrowval : triAcc m' + m' ≤ B := by
    have : triAcc m' + m' = triAcc (m' + 1) := by rw [triAcc]
    rw [this]
    exact htri.trans htriW
  have hiterB : m' + 1 ≤ B := by omega
  have hpb1 := programBoundedIn_ctlAssign_add B M rowCountReg rowCountReg iterReg σ h0
    (by norm_num [rowCountReg]; omega) (by norm_num [rowCountReg]; omega)
    (by norm_num [iterReg]; omega) (by rw [hrow, hiter]; omega)
  let σ1 := (ctlAssign rowCountReg (.add (ctlCell rowCountReg) (ctlCell iterReg))).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    rw [ctlAssign_zero rowCountReg _ σ (by norm_num [rowCountReg]), h0]
  have hσ1iter : σ1 (M + iterReg) = m' := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff rowCountReg _ σ (M + iterReg)
      (by rw [h0]; norm_num [rowCountReg, iterReg])]
    exact hiter
  have hpb2 := programBoundedIn_ctlAssign_bump B M m' iterReg 1 σ1 hσ10
    (by norm_num [iterReg]; omega) hσ1iter hiterB
  unfold triAccStep
  exact ⟨hpb1, hpb2⟩

lemma programBoundedIn_triAccLoop (B K M n m : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hrow : σ (M + rowCountReg) = 0)
    (hW : σ (M + persistWReg) ≤ K) (hM70 : M + 70 ≤ B)
    (hKsq : K * (K * (4 + 3 * m)) ≤ B) (hKB : K ≤ B)
    (hnK : n ≤ K) (hmK : m ≤ K) :
    ProgramBoundedIn B σ (triAccLoop rowCountReg iterReg persistWReg) := by
  have hrowPos : 1 ≤ rowCountReg := by norm_num [rowCountReg]
  have hiterPos : 1 ≤ iterReg := by norm_num [iterReg]
  have hrowW : rowCountReg ≠ persistWReg := by norm_num [rowCountReg, persistWReg]
  have hiterW : iterReg ≠ persistWReg := by norm_num [iterReg, persistWReg]
  have hrowIter : rowCountReg ≠ iterReg := by norm_num [rowCountReg, iterReg]
  have hreset := programBoundedIn_ctlAssign_const B M iterReg 0 σ h0
    (by norm_num [iterReg]; omega) (by omega)
  let σ1 := (ctlAssign iterReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero iterReg _ σ hiterPos).trans h0
  have hσ1row : σ1 (M + rowCountReg) = 0 := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff iterReg _ σ (M + rowCountReg)
      (by rw [h0]; norm_num [iterReg, rowCountReg])]
    exact hrow
  have hσ1W : σ1 (M + persistWReg) = σ (M + persistWReg) := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff iterReg _ σ (M + persistWReg)
      (by rw [h0]; norm_num [iterReg, persistWReg])]
  have htriW : triAcc (σ (M + persistWReg)) ≤ B := by
    have hsm := clauseCount_small_bounds B K n m (σ (M + persistWReg)) hKsq hnK hmK hW
    exact (triAcc_le_square _).trans hsm.2.2.2
  unfold triAccLoop
  simp only [ProgramBoundedIn]
  refine ⟨hreset, ?_⟩
  change ExprBoundedIn B σ1 (ctlCell persistWReg) ∧
    ∀ m' < (ctlCell persistWReg).eval σ1,
      ProgramBoundedIn B (loopEval (triAccStep rowCountReg iterReg) m' σ1)
        (triAccStep rowCountReg iterReg)
  refine ⟨exprBoundedIn_ctlCell B M persistWReg σ1 hσ10 (by norm_num [persistWReg]; omega), ?_⟩
  intro m' hm'
  have hm'W : m' < σ (M + persistWReg) := by
    simpa [ctlCell, ctlAddr, Expr.eval, hσ10, hσ1W] using hm'
  have hgen := triAccStep_loop_gen M rowCountReg iterReg hrowPos hiterPos hrowIter
    m' σ1 0 0 hσ10 hσ1row
    (by
      dsimp [σ1]
      rw [show M + iterReg = σ 0 + iterReg by rw [h0]]
      rw [ctlAssign_eval_same]
      simp [Expr.eval])
  let τ := loopEval (triAccStep rowCountReg iterReg) m' σ1
  have hτ0 : τ 0 = M := by
    dsimp [τ]
    exact triAccStep_loop_zero rowCountReg iterReg hrowPos hiterPos m' σ1 |>.trans hσ10
  have hτrow : τ (M + rowCountReg) = triAcc m' := by simpa [τ] using hgen.1
  have hτiter : τ (M + iterReg) = m' := by simpa [τ] using hgen.2
  exact triAccStep_bounded B K M (σ (M + persistWReg)) m' τ hτ0 hτrow hτiter
    hW hKB hM70 htriW hm'W

lemma programBoundedIn_clauseCountProg_of_bounds (B K M n m T W F : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hT : σ (M + persistTReg) = T)
    (hW : σ (M + persistWReg) = W) (hF : σ (M + initFreeLenReg) = F)
    (hM70 : M + 70 ≤ B) (hKsq : K * (K * (4 + 3 * m)) ≤ B)
    (hKB : K ≤ B) (hnK : n ≤ K) (hmK : m ≤ K) (hWK : W ≤ K)
    (hcount : clauseCount n m T W F ≤ B) :
    ProgramBoundedIn B σ (clauseCountProg n m) := by
  have hrowPos : 1 ≤ rowCountReg := by norm_num [rowCountReg]
  have hiterPos : 1 ≤ iterReg := by norm_num [iterReg]
  have hreset := programBoundedIn_ctlAssign_const B M rowCountReg 0 σ h0
    (by norm_num [rowCountReg]; omega) (by omega)
  let σ1 := (ctlAssign rowCountReg (.const 0)).eval σ
  have hσ10 : σ1 0 = M := by
    dsimp [σ1]
    exact (ctlAssign_zero rowCountReg _ σ hrowPos).trans h0
  have hσ1row : σ1 (M + rowCountReg) = 0 := by
    dsimp [σ1]
    rw [show M + rowCountReg = σ 0 + rowCountReg by rw [h0]]
    rw [ctlAssign_eval_same]
    simp [Expr.eval]
  have hσ1T : σ1 (M + persistTReg) = T := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff rowCountReg _ σ (M + persistTReg)
      (by rw [h0]; norm_num [rowCountReg, persistTReg])]
    exact hT
  have hσ1W : σ1 (M + persistWReg) = W := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff rowCountReg _ σ (M + persistWReg)
      (by rw [h0]; norm_num [rowCountReg, persistWReg])]
    exact hW
  have hσ1F : σ1 (M + initFreeLenReg) = F := by
    dsimp [σ1]
    rw [ctlAssign_eval_diff rowCountReg _ σ (M + initFreeLenReg)
      (by rw [h0]; norm_num [rowCountReg, initFreeLenReg])]
    exact hF
  have hloop := programBoundedIn_triAccLoop B K M n m σ1 hσ10 hσ1row
    (by rw [hσ1W]; exact hWK) hM70 hKsq hKB hnK hmK
  let σ2 := (triAccLoop rowCountReg iterReg persistWReg).eval σ1
  have hσ20 : σ2 0 = M := by
    dsimp [σ2]
    exact triAccLoop_zero M rowCountReg iterReg persistWReg σ1 hσ10
      (by norm_num [rowCountReg]) (by norm_num [iterReg])
  have hrowIter : rowCountReg ≠ iterReg := by norm_num [rowCountReg, iterReg]
  have hrowW : rowCountReg ≠ persistWReg := by norm_num [rowCountReg, persistWReg]
  have hiterW : iterReg ≠ persistWReg := by norm_num [iterReg, persistWReg]
  have hloopEval := triAccLoop_eval M rowCountReg iterReg persistWReg W 0 σ1
    hσ10 hσ1row hσ1W (by norm_num [rowCountReg]) (by norm_num [iterReg]) hrowIter hrowW hiterW
  have hσ2row : σ2 (M + rowCountReg) = triAcc W := by simpa [σ2] using hloopEval.1
  have hσ2T : σ2 (M + persistTReg) = T := by
    have hframe := triAccLoop_frame M rowCountReg iterReg persistWReg persistTReg σ1 hσ10
      (by norm_num [rowCountReg]) (by norm_num [iterReg])
      (by norm_num [persistTReg, rowCountReg]) (by norm_num [persistTReg, iterReg]) hiterW
    exact hframe.trans hσ1T
  have hσ2W : σ2 (M + persistWReg) = W := by
    have hframe := triAccLoop_frame M rowCountReg iterReg persistWReg persistWReg σ1 hσ10
      (by norm_num [rowCountReg]) (by norm_num [iterReg])
      (by norm_num [persistWReg, rowCountReg]) (by norm_num [persistWReg, iterReg]) hiterW
    exact hframe.trans hσ1W
  have hσ2F : σ2 (M + initFreeLenReg) = F := by
    have hframe := triAccLoop_frame M rowCountReg iterReg persistWReg initFreeLenReg σ1 hσ10
      (by norm_num [rowCountReg]) (by norm_num [iterReg])
      (by norm_num [initFreeLenReg, rowCountReg]) (by norm_num [initFreeLenReg, iterReg]) hiterW
    exact hframe.trans hσ1F
  have hexpr := exprBoundedIn_clauseCountExpr B K M n m T W F σ2 hσ20 hσ2T hσ2W hσ2F
    hσ2row hM70 hKsq hKB hnK hmK hWK hcount
  have hassign : ProgramBoundedIn B σ2
      (ctlAssign rowCountReg (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg)) := by
    unfold ctlAssign
    refine ⟨exprBoundedIn_ctlAddr B M rowCountReg σ2 hσ20 (by norm_num [rowCountReg]; omega), hexpr,
      by rw [ctlAddr_eval_at M rowCountReg σ2 hσ20]; norm_num [rowCountReg]; omega⟩
  have htail : ProgramBoundedIn B σ1
      ((triAccLoop rowCountReg iterReg persistWReg).seq
        (ctlAssign rowCountReg (clauseCountExpr n m persistTReg persistWReg initFreeLenReg rowCountReg))) := by
    unfold ProgramBoundedIn
    exact ⟨hloop, by simpa [σ2] using hassign⟩
  unfold clauseCountProg
  simp only [ProgramBoundedIn]
  exact ⟨hreset, htail⟩

lemma programBoundedIn_clauseCountProg (p time : Polynomial ℕ)
    (d : TableauDescriptor) (prefIdx allowedIdx outIdx : List ℕ) (N : ℕ) (σ : Store)
    (h0 : σ 0 = setupM p time d allowedIdx N)
    (hT : σ (setupM p time d allowedIdx N + persistTReg) = (timePoly p time).eval N)
    (hW : σ (setupM p time d allowedIdx N + persistWReg) = (cookWindowPoly p time).eval N)
    (hfree : σ (setupM p time d allowedIdx N + initFreeLenReg) = p.eval N) :
    ProgramBoundedIn (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx)) σ
      (clauseCountProg d.numStates d.numLetters) := by
  have hM70K := envK_eval_ge_setupM_add_70 p time d prefIdx allowedIdx outIdx N
  have hKB := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  have hM70 : setupM p time d allowedIdx N + 70 ≤
      Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx) := by omega
  have hKsq := envB_ge_env_ksq p time d prefIdx allowedIdx outIdx N
  have hK_B := envB_ge_envK p time d prefIdx allowedIdx outIdx N
  have hnK : d.numStates ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) := by
    rw [envK_eval]
    unfold envKConst
    omega
  have hmK : d.numLetters ≤ Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx) := by
    rw [envK_eval]
    unfold envKConst
    omega
  have hWK := envK_ge_window p time d prefIdx allowedIdx outIdx N
  have hcount := clauseCount_le_envB p time d prefIdx allowedIdx outIdx N
  exact programBoundedIn_clauseCountProg_of_bounds
    (Polynomial.eval N (envB p time d prefIdx allowedIdx outIdx))
    (Polynomial.eval N (envK p time d prefIdx allowedIdx outIdx))
    (setupM p time d allowedIdx N) d.numStates d.numLetters
    ((timePoly p time).eval N) ((cookWindowPoly p time).eval N) (p.eval N) σ
    h0 hT hW hfree hM70 hKsq hK_B hnK hmK hWK hcount

end NPComplete.CookLevin

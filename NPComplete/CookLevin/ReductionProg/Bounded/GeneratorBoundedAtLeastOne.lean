module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedLeaf

/-!
Three of the five families emit a clause whose width is not known until run time
— "the head is at one of these `W` positions", "the tape symbol is one of these
letters", "the machine halts in one of these states".  `writeAtLeastOneProg`
writes such a row by staging the width into the count cell and then running one
positive literal per iteration, so unlike a fixed-width row it is a loop, and its
bound needs the loop treatment rather than the literal-list one.

Its body writes at the pointer and bumps the literal counter, which is the same
pair the fixed-width leaf uses, so the pieces are already here.  What differs is
that the literal expression is evaluated at each iteration's own store, with the
counter holding that iteration's index — hence the hypotheses quantify over the
stores the loop actually visits rather than naming one.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## One iteration -/

/-- One positive literal plus the literal counter's bump. -/
lemma programBoundedIn_writeAtLeastOneBody (K B M wp iJ : ℕ) (σ : Store) (varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hwpB : wp + 2 ≤ B) (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hKB : K + 1 ≤ B)
    (hvar : ExprBoundedIn B (writeReg σ wp ((Expr.const 0).eval σ)) varE)
    (ht : TightCells K M σ) :
    ProgramBoundedIn B σ (writeAtLeastOneBody wpJ iJ varE) := by
  unfold writeAtLeastOneBody
  refine ⟨programBoundedIn_writeLitProg B M wp σ (.const 0) varE h0 hwp hsep hMB hwpB
    (by simp [ExprBoundedIn]) hvar, ?_⟩
  rw [writeLitProg_eval_direct M wp σ (.const 0) varE h0 hwp hsep]
  set σ2 := writeReg (writeReg σ wp ((Expr.const 0).eval σ)) (wp + 1)
    (varE.eval (writeReg σ wp ((Expr.const 0).eval σ))) with hs2
  have h20 : σ2 0 = M := by
    rw [hs2, writeReg_diff _ (wp + 1) _ 0 (by omega),
      writeReg_diff σ wp _ 0 (by omega), h0]
  have h30 : (writeReg σ2 (M + wpJ) (wp + 2)) 0 = M := by
    rw [writeReg_diff σ2 (M + wpJ) (wp + 2) 0 (by simp only [wpJ]; omega), h20]
  have h3i : (writeReg σ2 (M + wpJ) (wp + 2)) (M + iJ) = σ (M + iJ) := by
    rw [writeReg_diff σ2 (M + wpJ) (wp + 2) (M + iJ) (by simp only [wpJ]; omega), hs2,
      writeReg_diff _ (wp + 1) _ (M + iJ) (by omega),
      writeReg_diff σ wp _ (M + iJ) (by omega)]
  refine programBoundedIn_ctlAssign_bump B M _ iJ 1 _ h30 (by omega) h3i ?_
  have := ht iJ hiJ hiJ2
  omega

/-- The body's effect on both envelopes, for the next iteration's entry. -/
lemma writeAtLeastOneBody_exit (K S M wp iJ : ℕ) (σ : Store) (varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hKS : K ≤ S)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ)
    (hvarK : varE.eval (writeReg σ wp ((Expr.const 0).eval σ)) ≤ S) (hwpK : wp + 2 ≤ S)
    (hbump : σ (M + iJ) + 1 ≤ K) :
    (writeAtLeastOneBody wpJ iJ varE).eval σ 0 = M ∧
      (writeAtLeastOneBody wpJ iJ varE).eval σ (M + wpJ) = wp + 2 ∧
      TightCells K M ((writeAtLeastOneBody wpJ iJ varE).eval σ) ∧
      StoreValuesLe S ((writeAtLeastOneBody wpJ iJ varE).eval σ) := by
  obtain ⟨e0, ew, et, es⟩ := writeLitProg_exit K S M wp σ (.const 0) varE h0 hwp hsep ht hst
    (by simp [Expr.eval]) hvarK hwpK
  have hfr := writeLitProg_frame_below M wp σ (.const 0) varE h0 hwp hsep
  have hi : (writeLitProg wpJ (.const 0) varE).eval σ (M + iJ) = σ (M + iJ) :=
    hfr (M + iJ) (by omega) (by simp only [wpJ]; omega)
  obtain ⟨g0, gt, gs⟩ := ctlAssign_bump_preserves K S M iJ 1 _ e0 hiJ hiJ2 et es
    (by omega) hKS
  unfold writeAtLeastOneBody
  rw [eval_seq]
  refine ⟨g0, ?_, gt, gs⟩
  rw [ctlAssign_eval_diff iJ _ _ (M + wpJ) (by rw [e0]; simp only [wpJ]; omega), ew]

/-! ## The row header

The count cell, the pointer bump and the counter reset run before the loop, so
the loop's entry store is the one they leave.  Computing it outright keeps the
loop's hypotheses free of any side condition about what the width expression
reads. -/

/-- The header's exit conditions, in the shape the loop needs on entry. -/
lemma write_at_least_one_prefix_exit (K S M wp iJ c : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hsep : M + 24 < wp) (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) (hc : c ≤ S) (hwpS : wp + 2 ≤ S) :
    (writeReg (writeReg (writeReg σ (wp + 1) c) (M + wpJ) (wp + 2)) (M + iJ) 0) 0 = M ∧
      (writeReg (writeReg (writeReg σ (wp + 1) c) (M + wpJ) (wp + 2)) (M + iJ) 0)
        (M + wpJ) = wp + 2 ∧
      (writeReg (writeReg (writeReg σ (wp + 1) c) (M + wpJ) (wp + 2)) (M + iJ) 0)
        (M + iJ) = 0 ∧
      TightCells K M (writeReg (writeReg (writeReg σ (wp + 1) c) (M + wpJ) (wp + 2))
        (M + iJ) 0) ∧
      StoreValuesLe S (writeReg (writeReg (writeReg σ (wp + 1) c) (M + wpJ) (wp + 2))
        (M + iJ) 0) := by
  set σ1 := writeReg σ (wp + 1) c with hs1
  set σ2 := writeReg σ1 (M + wpJ) (wp + 2) with hs2
  have h10 : σ1 0 = M := by rw [hs1, writeReg_diff σ (wp + 1) c 0 (by omega), h0]
  have h20 : σ2 0 = M := by
    rw [hs2, writeReg_diff σ1 (M + wpJ) _ 0 (by simp only [wpJ]; omega), h10]
  refine ⟨by rw [writeReg_diff σ2 (M + iJ) 0 0 (by omega), h20], ?_,
    writeReg_same _ _ _, fun j hj hj24 => ?_, fun i => ?_⟩
  · rw [writeReg_diff σ2 (M + iJ) 0 (M + wpJ) (by simp only [wpJ]; omega), hs2,
      writeReg_same]
  · by_cases hji : j = iJ
    · rw [hji, writeReg_same]; omega
    · rw [writeReg_diff σ2 (M + iJ) 0 (M + j) (by omega), hs2]
      by_cases hjw : j = wpJ
      · exact absurd hjw (by simp only [wpJ]; omega)
      · rw [writeReg_diff σ1 (M + wpJ) _ (M + j) (by omega), hs1,
          writeReg_diff σ (wp + 1) c (M + j) (by omega)]
        exact ht j hj hj24
  · by_cases hi : i = M + iJ
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ2 (M + iJ) 0 i hi, hs2]
      by_cases hiw : i = M + wpJ
      · rw [hiw, writeReg_same]; omega
      · rw [writeReg_diff σ1 (M + wpJ) _ i hiw, hs1]
        by_cases hi1 : i = wp + 1
        · rw [hi1, writeReg_same]; exact hc
        · rw [writeReg_diff σ (wp + 1) c i hi1]; exact hst i

/-! ## The loop over trip counts -/

/-- The counter's value after one iteration, isolated from the row write's own
    exit facts so the loop induction can chain it without unfolding the row. -/
lemma writeAtLeastOneBody_iJ_eval (M wp iJ : ℕ) (σ : Store) (varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) :
    (writeAtLeastOneBody wpJ iJ varE).eval σ (M + iJ) = σ (M + iJ) + 1 := by
  have hfr : (writeLitProg wpJ (.const 0) varE).eval σ (M + iJ) = σ (M + iJ) :=
    writeLitProg_frame_below M wp σ (.const 0) varE h0 hwp hsep (M + iJ) (by omega)
      (by simp only [wpJ]; omega)
  have h0' : (writeLitProg wpJ (.const 0) varE).eval σ 0 = σ 0 :=
    writeLitProg_frame_below M wp σ (.const 0) varE h0 hwp hsep 0 (by omega)
      (by simp only [wpJ]; omega)
  unfold writeAtLeastOneBody
  rw [eval_seq]
  unfold ctlAssign
  rw [eval_assignInd, ctlAddr_eval, h0', h0]
  simp only [Expr.eval, ctlCell_eval, h0', h0, hfr, writeReg_same]

/-- Loop induction over trip count `k`, tracking the invariant "pointer =
    `wp + 2 * m`, counter = `idx + m`" after `m` iterations.  `varE` is asked to
    be bounded and under the tight envelope at *any* store satisfying the two
    envelope predicates, mirroring `LitsBounded`'s shape: the body's own writes
    only ever transform one such store into another
    (`writeReg_above_preserves` covers the tag write, `ctlAssign_bump_preserves`
    the counter bump), so the same hypothesis discharges every iteration without
    naming a store.  `idx + k ≤ K` is what keeps every iteration's counter bump
    inside the tight envelope, since `TightCells` alone permits a counter to sit
    exactly at `K`.  The marker, pointer, and counter are carried in the
    conclusion alongside the two envelopes so the whole-program exit lemma can
    read them off directly. -/
lemma writeAtLeastOneBody_loop_bounded (K S B M iJ : ℕ) (varE : Expr) :
    ∀ (k idx wp : ℕ) (σ : Store), σ 0 = M → σ (M + wpJ) = wp → σ (M + iJ) = idx →
      M + 24 < wp → M + 24 ≤ B → wp + 2 * k ≤ S → S ≤ B → idx + k ≤ K → K ≤ S →
      2 ≤ iJ → iJ ≤ 24 → K + 1 ≤ B →
      (∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
        ExprBoundedIn B τ varE ∧ varE.eval τ ≤ S) →
      TightCells K M σ → StoreValuesLe S σ →
      (∀ m' < k, ProgramBoundedIn B (loopEval (writeAtLeastOneBody wpJ iJ varE) m' σ)
        (writeAtLeastOneBody wpJ iJ varE)) ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) 0 = M ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) (M + wpJ) = wp + 2 * k ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) (M + iJ) = idx + k ∧
      TightCells K M (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) ∧
      StoreValuesLe S (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) := by
  intro k
  induction k with
  | zero =>
      intro idx wp σ h0 hwp hiJv hsep hMB hlen hSB hidxK hKS hiJ hiJ2 hKB hvarE ht hst
      refine ⟨fun m' hm' => absurd hm' (by omega), ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [loopEval_zero, Nat.mul_zero, Nat.add_zero]
      exacts [h0, hwp, hiJv, ht, hst]
  | succ k ih =>
      intro idx wp σ h0 hwp hiJv hsep hMB hlen hSB hidxK hKS hiJ hiJ2 hKB hvarE ht hst
      obtain ⟨h0w, htw, hsw⟩ := writeReg_above_preserves K S M wp 0 σ h0 hsep ht hst (by omega)
      obtain ⟨hveB, hveS⟩ := hvarE (writeReg σ wp 0) h0w htw hsw
      have hpb0 := programBoundedIn_writeAtLeastOneBody K B M wp iJ σ varE h0 hwp hsep hMB
        (by omega) hiJ hiJ2 hKB hveB ht
      have hbump : σ (M + iJ) + 1 ≤ K := by rw [hiJv]; omega
      obtain ⟨e0, ew, et, es⟩ := writeAtLeastOneBody_exit K S M wp iJ σ varE h0 hwp hsep hiJ hiJ2
        hKS ht hst hveS (by omega) hbump
      have hiJ' : (writeAtLeastOneBody wpJ iJ varE).eval σ (M + iJ) = idx + 1 := by
        rw [writeAtLeastOneBody_iJ_eval M wp iJ σ varE h0 hwp hsep hiJ hiJ2, hiJv]
      obtain ⟨hrec, g0, gw, gi, gt, gs⟩ := ih (idx + 1) (wp + 2)
        ((writeAtLeastOneBody wpJ iJ varE).eval σ)
        e0 ew hiJ' (by omega) hMB (by omega) hSB (by omega) hKS hiJ hiJ2 hKB hvarE et es
      refine ⟨fun m' hm' => ?_, by rw [loopEval_succ]; exact g0, by rw [loopEval_succ]; omega,
        by rw [loopEval_succ]; omega, by rw [loopEval_succ]; exact gt,
        by rw [loopEval_succ]; exact gs⟩
      rcases Nat.eq_zero_or_pos m' with rfl | hpos
      · rw [loopEval_zero]; exact hpb0
      · have hm'eq : m' = (m' - 1) + 1 := by omega
        rw [hm'eq, loopEval_succ]
        exact hrec (m' - 1) (by omega)

/-! ## The whole program -/

/-- The whole `writeAtLeastOneProg` is bounded: the header three commands, then
    the loop over `n = cntE.eval σ` iterations of `writeAtLeastOneBody`, whose
    trip-count induction is `writeAtLeastOneBody_loop_bounded`.  `cntE` is asked for
    twice — at the entry store and at the header's exit store — since `.forN`
    evaluates it at the latter but the caller typically only knows the value at
    the former; both hypotheses are trivial to discharge when `cntE` does not
    read the two cells the header changes. -/
lemma programBoundedIn_writeAtLeastOneProg (K S B M wp iJ n : ℕ) (σ : Store) (cntE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hKB : K + 1 ≤ B) (hKS : K ≤ S) (hSB : S ≤ B)
    (hnK : n ≤ K) (hlen : wp + 2 + 2 * n ≤ S)
    (hcntE0 : ExprBoundedIn B σ cntE) (hn0 : cntE.eval σ = n)
    (hcntE' : ExprBoundedIn B
      (writeReg (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + iJ) 0) cntE)
    (hn' : cntE.eval
      (writeReg (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + iJ) 0) = n)
    (hvarE : ∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ →
      ExprBoundedIn B τ varE ∧ varE.eval τ ≤ S)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) :
    ProgramBoundedIn B σ (writeAtLeastOneProg wpJ iJ cntE varE) := by
  have hwpJ1 : wpJ = 1 := rfl
  have hjb : M + wpJ ≤ B := by omega
  have hib : M + iJ ≤ B := by omega
  set σA := (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) cntE).eval σ with hσAdef
  have hσAeq : σA = writeReg σ (wp + 1) n := by
    rw [hσAdef, eval_assignInd]; simp only [Expr.eval, ctlCell_eval, h0, hwp, hn0]
  have hσA0 : σA 0 = M := by rw [hσAeq, writeReg_diff σ (wp + 1) n 0 (by omega), h0]
  have hσActl : σA (M + wpJ) = wp := by
    rw [hσAeq, writeReg_diff σ (wp + 1) n (M + wpJ) (by omega), hwp]
  have hpb1 : ProgramBoundedIn B σ (.assignInd (.add (ctlCell wpJ) (.const 1)) cntE) := by
    refine ⟨⟨exprBoundedIn_ctlCell B M wpJ σ h0 hjb, by simp only [ExprBoundedIn]; omega, ?_⟩,
      hcntE0, ?_⟩
    · simp only [Expr.eval, ctlCell_eval, h0, hwp]; omega
    · simp only [Expr.eval, ctlCell_eval, h0, hwp]; omega
  set σB := (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σA with hσBdef
  have hσBeq : σB = writeReg σA (M + wpJ) (wp + 2) := by
    unfold ctlAssign at hσBdef; rw [hσBdef, eval_assignInd, ctlAddr_eval, hσA0]
    simp only [Expr.eval, ctlCell_eval, hσA0, hσActl]
  have hσB0 : σB 0 = M := by
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) 0 (by omega), hσA0]
  have hpb2 : ProgramBoundedIn B σA (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2))) :=
    programBoundedIn_ctlAssign_bump B M wp wpJ 2 σA hσA0 hjb hσActl (by omega)
  set σC := (ctlAssign iJ (Expr.const 0)).eval σB with hσCdef
  have hσCeq : σC = writeReg σB (M + iJ) 0 := by
    unfold ctlAssign at hσCdef; rw [hσCdef, eval_assignInd, ctlAddr_eval, hσB0]
    simp only [Expr.eval]
  have hpb3 : ProgramBoundedIn B σB (ctlAssign iJ (.const 0)) :=
    programBoundedIn_ctlAssign_const B M iJ 0 σB hσB0 hib (by omega)
  have hσCform : σC = writeReg (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + iJ) 0 := by
    rw [hσCeq, hσBeq, hσAeq]
  have hcntEC : ExprBoundedIn B σC cntE := by rw [hσCform]; exact hcntE'
  have hnC : cntE.eval σC = n := by rw [hσCform]; exact hn'
  obtain ⟨e0, ew, ei, et, es⟩ := write_at_least_one_prefix_exit K S M wp iJ n σ h0 hsep hiJ hiJ2 ht
    hst (by omega) (by omega)
  rw [← hσCform] at e0 ew ei et es
  have hpbLoop := (writeAtLeastOneBody_loop_bounded K S B M iJ varE n 0 (wp + 2) σC e0 ew ei
    (by omega) hMB (by omega) hSB (by omega) hKS hiJ hiJ2 hKB hvarE et es).1
  unfold writeAtLeastOneProg
  refine ⟨hpb1, ?_⟩
  rw [← hσAdef]
  refine ⟨hpb2, ?_⟩
  rw [← hσBdef]
  refine ⟨hpb3, ?_⟩
  rw [← hσCdef]
  refine ⟨hcntEC, ?_⟩
  rw [hnC]
  exact hpbLoop

/-- Loop induction covering only the exit facts, without an expression bound:
    the same invariant as `writeAtLeastOneBody_loop_bounded`, but asking `varE` just
    for its value under the tight envelope.  This is what lets
    `writeAtLeastOneProg_exit` avoid manufacturing a freeze bound for `varE`
    when the caller only wants the exit envelopes. -/
lemma writeAtLeastOneBody_loop_exit (K S M iJ : ℕ) (varE : Expr) :
    ∀ (k idx wp : ℕ) (σ : Store), σ 0 = M → σ (M + wpJ) = wp → σ (M + iJ) = idx →
      M + 24 < wp → wp + 2 * k ≤ S → idx + k ≤ K → K ≤ S → 2 ≤ iJ → iJ ≤ 24 →
      (∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ → varE.eval τ ≤ S) →
      TightCells K M σ → StoreValuesLe S σ →
      (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) 0 = M ∧
      (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) (M + wpJ) = wp + 2 * k ∧
      TightCells K M (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) ∧
      StoreValuesLe S (loopEval (writeAtLeastOneBody wpJ iJ varE) k σ) := by
  intro k
  induction k with
  | zero =>
      intro idx wp σ h0 hwp hiJv hsep hlen hidxK hKS hiJ hiJ2 hvarE ht hst
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [loopEval_zero, Nat.mul_zero, Nat.add_zero]
      exacts [h0, hwp, ht, hst]
  | succ k ih =>
      intro idx wp σ h0 hwp hiJv hsep hlen hidxK hKS hiJ hiJ2 hvarE ht hst
      obtain ⟨h0w, htw, hsw⟩ := writeReg_above_preserves K S M wp 0 σ h0 hsep ht hst (by omega)
      have hveS := hvarE (writeReg σ wp 0) h0w htw hsw
      have hbump : σ (M + iJ) + 1 ≤ K := by rw [hiJv]; omega
      obtain ⟨e0, ew, et, es⟩ := writeAtLeastOneBody_exit K S M wp iJ σ varE h0 hwp hsep hiJ hiJ2
        hKS ht hst hveS (by omega) hbump
      have hiJ' : (writeAtLeastOneBody wpJ iJ varE).eval σ (M + iJ) = idx + 1 := by
        rw [writeAtLeastOneBody_iJ_eval M wp iJ σ varE h0 hwp hsep hiJ hiJ2, hiJv]
      obtain ⟨g0, gw, gt, gs⟩ := ih (idx + 1) (wp + 2) ((writeAtLeastOneBody wpJ iJ varE).eval σ)
        e0 ew hiJ' (by omega) (by omega) (by omega) hKS hiJ hiJ2 hvarE et es
      refine ⟨by rw [loopEval_succ]; exact g0, by rw [loopEval_succ]; omega,
        by rw [loopEval_succ]; exact gt, by rw [loopEval_succ]; exact gs⟩

/-- The exit envelopes, marker, and pointer, for whatever runs after
    `writeAtLeastOneProg` — the same shape `writeAtLeastOneProg_eval_state`'s
    pointer clause reports, but for the bounded companions rather than the
    writer contract. -/
lemma writeAtLeastOneProg_exit (K S M wp iJ n : ℕ) (σ : Store) (cntE varE : Expr)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (hiJ : 2 ≤ iJ) (hiJ2 : iJ ≤ 24) (hKS : K ≤ S)
    (hnK : n ≤ K) (hlen : wp + 2 + 2 * n ≤ S)
    (hn0 : cntE.eval σ = n)
    (hn' : cntE.eval
      (writeReg (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + iJ) 0) = n)
    (hvarE : ∀ τ : Store, τ 0 = M → TightCells K M τ → StoreValuesLe S τ → varE.eval τ ≤ S)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) :
    (writeAtLeastOneProg wpJ iJ cntE varE).eval σ 0 = M ∧
      (writeAtLeastOneProg wpJ iJ cntE varE).eval σ (M + wpJ) = wp + 2 + 2 * n ∧
      TightCells K M ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) ∧
      StoreValuesLe S ((writeAtLeastOneProg wpJ iJ cntE varE).eval σ) := by
  have hwpJ1 : wpJ = 1 := rfl
  set σA := (Program.assignInd (Expr.add (ctlCell wpJ) (Expr.const 1)) cntE).eval σ with hσAdef
  have hσAeq : σA = writeReg σ (wp + 1) n := by
    rw [hσAdef, eval_assignInd]; simp only [Expr.eval, ctlCell_eval, h0, hwp, hn0]
  have hσA0 : σA 0 = M := by rw [hσAeq, writeReg_diff σ (wp + 1) n 0 (by omega), h0]
  have hσActl : σA (M + wpJ) = wp := by
    rw [hσAeq, writeReg_diff σ (wp + 1) n (M + wpJ) (by omega), hwp]
  set σB := (ctlAssign wpJ (Expr.add (ctlCell wpJ) (Expr.const 2))).eval σA with hσBdef
  have hσBeq : σB = writeReg σA (M + wpJ) (wp + 2) := by
    unfold ctlAssign at hσBdef; rw [hσBdef, eval_assignInd, ctlAddr_eval, hσA0]
    simp only [Expr.eval, ctlCell_eval, hσA0, hσActl]
  have hσB0 : σB 0 = M := by
    rw [hσBeq, writeReg_diff σA (M + wpJ) (wp + 2) 0 (by omega), hσA0]
  set σC := (ctlAssign iJ (Expr.const 0)).eval σB with hσCdef
  have hσCeq : σC = writeReg σB (M + iJ) 0 := by
    unfold ctlAssign at hσCdef; rw [hσCdef, eval_assignInd, ctlAddr_eval, hσB0]
    simp only [Expr.eval]
  have hσCform : σC = writeReg (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + iJ) 0 := by
    rw [hσCeq, hσBeq, hσAeq]
  have hnC : cntE.eval σC = n := by rw [hσCform]; exact hn'
  obtain ⟨e0, ew, ei, et, es⟩ := write_at_least_one_prefix_exit K S M wp iJ n σ h0 hsep hiJ hiJ2 ht
    hst (by omega) (by omega)
  rw [← hσCform] at e0 ew ei et es
  obtain ⟨g0, gw, gt, gs⟩ := writeAtLeastOneBody_loop_exit K S M iJ varE n 0 (wp + 2) σC e0 ew ei
    (by omega) (by omega) (by omega) hKS hiJ hiJ2 hvarE et es
  unfold writeAtLeastOneProg
  rw [eval_seq, eval_seq, eval_seq, ← hσAdef, ← hσBdef, ← hσCdef, eval_forN, hnC]
  exact ⟨g0, gw, gt, gs⟩

end NPComplete.CookLevin

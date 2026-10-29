module

public import NPComplete.CookLevin.UniformEmit.SplitTailProgram

/-!
# Split-tail relation transport

The long-clause program has normalized paths whose state changes must match the split-tail
relation. This module proves that transport and the required bound-register frames, leaving clause
dispatch to compose the verified paths.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral)


/-- `boundReg` is outside the split-tail write set and below the output window. -/
structure SplitTailBoundRegOk
    (boundReg start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ) : Prop where
  below : boundReg < start
  ne_cursor : boundReg ≠ cursorReg
  ne_pol : boundReg ≠ polReg
  ne_var : boundReg ≠ varReg
  ne_done : boundReg ≠ doneReg
  ne_remaining : boundReg ≠ remainingReg
  ne_pol2 : boundReg ≠ pol2Reg
  ne_var2 : boundReg ≠ var2Reg
  ne_pol3 : boundReg ≠ pol3Reg
  ne_var3 : boundReg ≠ var3Reg
  ne_carry_pol : boundReg ≠ carryPolReg
  ne_carry_val : boundReg ≠ carryValReg
  ne_pos_pol : boundReg ≠ posPolReg
  ne_fresh : boundReg ≠ freshReg

lemma SplitTailBoundRegOk.ne_write_set
    {boundReg start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg : ℕ}
    (h : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    boundReg ≠ cursorReg ∧ boundReg ≠ polReg ∧ boundReg ≠ varReg ∧ boundReg ≠ doneReg ∧
      boundReg ≠ remainingReg ∧ boundReg ≠ pol2Reg ∧ boundReg ≠ var2Reg ∧
      boundReg ≠ pol3Reg ∧ boundReg ≠ var3Reg ∧ boundReg ≠ carryPolReg ∧
      boundReg ≠ carryValReg ∧ boundReg ≠ posPolReg ∧ boundReg ≠ freshReg :=
  ⟨h.ne_cursor, h.ne_pol, h.ne_var, h.ne_done, h.ne_remaining, h.ne_pol2, h.ne_var2,
    h.ne_pol3, h.ne_var3, h.ne_carry_pol, h.ne_carry_val, h.ne_pos_pol, h.ne_fresh⟩

/-- Induction contract for equating indexed and unindexed loop evaluations. -/
def SplitTailEmitStepAtLoopEvalGoal
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (tail : Bits) (ls : List Literal) : Prop :=
  ∀ (base : ℕ) (carry : Literal) (pref : Bits) (addr : ℕ) (σ : Store) (n : ℕ),
    (∀ l ∈ ls, l.var + 1 ≤ bound) →
    SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg →
    σ boundReg = bound →
    loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      n σ =
    loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      n σ

/-- One- and two-literal terminal cases both reach the same zero-counter loop frame. -/
lemma splitTailEmitStepProgAt_loopEval_eq_of_rel_done
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) (n : ℕ)
    (hshort : rest.length ≤ 1)
    (hbound : ∀ x ∈ l :: rest, x.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry (l :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      n σ =
    loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      n σ := by
  induction n with
  | zero => simp
  | succ n _ =>
      rw [loopEval_succ, loopEval_succ]
      have hstep := splitTailEmitStepProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg bound σ hb hok.ne_cursor hok.ne_pol hok.ne_var
        hok.ne_done hok.ne_pol2 hok.ne_var2 hok.ne_pol3 hok.ne_var3
      rw [hstep]
      cases rest with
      | nil =>
          obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_one_to_done
            M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
            pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
            base carry l pref tail addr σ (hbound l (by simp)) hrel
          have hbody := splitTailEmitStepProg_one_eval curJ tmpJ cursorReg polReg varReg doneReg
            remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
            posPolReg freshReg bound σ (by simpa using hrel.remaining)
          have hτ' : (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg
              remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
              posPolReg freshReg bound).eval σ = τ := hbody.trans hτ.symm
          rw [hτ']
          exact splitTailEmitStepProgAt_loopEval_of_zero curJ tmpJ cursorReg polReg varReg doneReg
            remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
            freshReg boundReg bound n τ hdone.remaining
      | cons l2 rest =>
          cases rest with
          | nil =>
              obtain ⟨τ, hτ, hdone⟩ := splitTailEmitRel_two_to_done
                M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
                pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
                base carry l l2 pref tail addr σ (hbound l (by simp)) (hbound l2 (by simp)) hrel
              have hbody := splitTailEmitStepProg_two_eval curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                posPolReg freshReg bound σ (by simpa using hrel.remaining)
              have hτ' : (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg
                  remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                  posPolReg freshReg bound).eval σ = τ := hbody.trans hτ.symm
              rw [hτ']
              exact splitTailEmitStepProgAt_loopEval_of_zero curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
                freshReg boundReg bound n τ hdone.remaining
          | cons l3 rest =>
              simp only [List.length_cons] at hshort
              omega

/-- Longer lists recur after one indexed step to an intermediate related state. -/
lemma splitTailEmitStepProgAt_loopEval_eq_of_rel_next
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) (n : ℕ)
    (hrest : SplitTailEmitStepAtLoopEvalGoal M curJ tmpJ start cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
      boundReg bound tail (l2 :: l3 :: rest))
    (hbound : ∀ x ∈ l :: l2 :: l3 :: rest, x.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry (l :: l2 :: l3 :: rest) pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      n σ =
    loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      n σ := by
  induction n with
  | zero => simp
  | succ n _ =>
      rw [loopEval_succ, loopEval_succ]
      have hstep := splitTailEmitStepProgAt_eq curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
        posPolReg freshReg boundReg bound σ hb hok.ne_cursor hok.ne_pol hok.ne_var
        hok.ne_done hok.ne_pol2 hok.ne_var2 hok.ne_pol3 hok.ne_var3
      rw [hstep]
      obtain ⟨τ1, hτ1, hrel1⟩ := splitTailEmitRel_intermediate_to_rel
        M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound base carry l l2 l3 rest
        pref tail addr σ (hbound l (by simp)) hrel
      have hbody : (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg
          remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
          posPolReg freshReg bound).eval σ = τ1 := by
        calc
          (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                posPolReg freshReg bound).eval σ =
              (splitTailEmitIntermediateProg curJ tmpJ cursorReg polReg varReg doneReg
                remainingReg carryPolReg carryValReg posPolReg freshReg bound).eval σ := by
            simp [splitTailEmitStepProg, hrel.remaining, Expr.eval]
          _ = τ1 := hτ1.symm
      rw [hbody]
      have hb1 : τ1 boundReg = bound := by
        have hf := splitTailEmitStepProg_low_frame_of_rel
          M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
          pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
          base carry (l :: l2 :: l3 :: rest) pref tail addr σ hbound hrel
          hok.below hok.ne_write_set
        exact (hbody ▸ hf).trans hb
      have hbound1 : ∀ x ∈ l2 :: l3 :: rest, x.var + 1 ≤ bound := by
        intro x hx
        exact hbound x (by simp [hx])
      exact hrest (base + 1) (Literal.neg base)
        (pref ++ encodedThreeLiteralBits 1 carry.var (literalPolarity l) l.var 0 base)
        (addr + l.var + 2) τ1 n hbound1 hrel1 hb1


lemma splitTailEmitStepProgAt_loopEval_eq_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store) (n : ℕ)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        n σ =
      loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        n σ := by
  induction ls generalizing σ pref addr base carry n with
  | nil =>
      exact splitTailEmitStepProgAt_loopEval_of_zero curJ tmpJ cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
        freshReg boundReg bound n σ (by simpa using hrel.remaining)
  | cons l rest ih =>
      change SplitTailEmitStepAtLoopEvalGoal M curJ tmpJ start cursorReg polReg varReg doneReg
        remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg
        boundReg bound tail rest at ih
      cases rest with
      | nil =>
          exact splitTailEmitStepProgAt_loopEval_eq_of_rel_done M curJ tmpJ start cursorReg polReg
            varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
            posPolReg freshReg boundReg bound base carry l [] pref tail addr σ n (by simp)
            hbound hrel hb hok
      | cons l2 rest =>
          cases rest with
          | nil =>
              exact splitTailEmitStepProgAt_loopEval_eq_of_rel_done M curJ tmpJ start cursorReg polReg
                varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                posPolReg freshReg boundReg bound base carry l [l2] pref tail addr σ n (by simp)
                hbound hrel hb hok
          | cons l3 rest =>
              exact splitTailEmitStepProgAt_loopEval_eq_of_rel_next M curJ tmpJ start cursorReg polReg
                varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
                posPolReg freshReg boundReg bound base carry l l2 l3 rest pref tail addr σ n ih
                hbound hrel hb hok

lemma splitTailEmitStepProgAt_pad_after_zero
    (curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg : ℕ)
    (σ : Store) (n k : ℕ)
    (hrem : (loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      n σ) remainingReg = 0) :
    loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      (n + k) σ =
      loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        n σ := by
  let body := splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg
  rw [splitTail_loopEval_add_right body n k σ]
  exact splitTailEmitStepProgAt_zero_loop curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg
    (loopEval body n σ) k hrem

lemma splitTailEmitProgAt_eval_of_rel
    (M curJ tmpJ start : ℕ)
    (cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg boundReg bound tailBound : ℕ)
    (base : ℕ) (carry : Literal) (ls : List Literal)
    (pref tail : Bits) (addr : ℕ) (σ : Store)
    (hbound : ∀ l ∈ ls, l.var + 1 ≤ bound)
    (hne : ls ≠ []) (hls : ls.length ≤ tailBound)
    (hrel : SplitTailEmitRel σ M curJ tmpJ start base carry ls pref tail addr
      cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg pol3Reg var3Reg
      carryPolReg carryValReg posPolReg freshReg)
    (hb : σ boundReg = bound)
    (hok : SplitTailBoundRegOk boundReg start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg) :
    (splitTailEmitProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
      pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg).eval σ =
      (splitTailEmitProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
        pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound).eval σ := by
  have hkpos : 0 < ls.length := List.length_pos_of_ne_nil hne
  have hAt := splitTailEmitProgAt_pos_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg
    ls.length σ hrel.remaining hkpos
  have hC := splitTailEmitProg_pos_eval curJ tmpJ cursorReg polReg varReg doneReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound tailBound
    ls.length σ hrel.remaining hkpos
  obtain ⟨k, τ, _, _, _, _, _, hk, hloop, hdone, _, _, _⟩ :=
    splitTailEmitRel_nonempty_to_done
      M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound
      base carry ls pref tail addr σ hbound hne hrel
  have hEqK := splitTailEmitStepProgAt_loopEval_eq_of_rel
    M curJ tmpJ start cursorReg polReg varReg doneReg remainingReg pol2Reg var2Reg
    pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg bound
    base carry ls pref tail addr σ k hbound hrel hb hok
  have hAt0 : (loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      k σ) remainingReg = 0 := by
    rw [hEqK, ← hloop]
    exact hdone.remaining
  have hkLen : k ≤ ls.length + 1 := hk
  have hpadAt : loopEval
      (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
      (ls.length + 1) σ =
      loopEval
        (splitTailEmitStepProgAt curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg boundReg)
        k σ := by
    rw [show ls.length + 1 = k + (ls.length + 1 - k) by omega]
    exact splitTailEmitStepProgAt_pad_after_zero curJ tmpJ cursorReg polReg varReg doneReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg
      freshReg boundReg σ k (ls.length + 1 - k) hAt0
  have hpadC : loopEval
      (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
      (tailBound + 1) σ = τ := by
    have h0 : (loopEval
        (splitTailEmitStepProg curJ tmpJ cursorReg polReg varReg doneReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound)
        k σ) remainingReg = 0 := by
      rw [← hloop]
      exact hdone.remaining
    rw [show tailBound + 1 = k + (tailBound + 1 - k) by omega,
      splitTailEmitProg_pad_after_zero curJ tmpJ cursorReg polReg varReg doneReg remainingReg
        pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg posPolReg freshReg bound σ
        k (tailBound + 1 - k) h0, hloop]
  rw [hAt, hC, hpadAt, hEqK, hpadC, hloop]

end NPComplete.CookLevin

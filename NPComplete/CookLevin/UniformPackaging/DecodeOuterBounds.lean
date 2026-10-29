module

public import NPComplete.CookLevin.UniformPackaging.ProducerProgram
public import NPComplete.BoundedWhile.Frame

/-!
# Outer CNF decoder invariants

Per-clause decoding facts are insufficient to bound the decoder after a whole
formula scan. This module carries the cursor, variable maximum, and fresh-variable
statistics through the outer loop, tying parser state to the encoded input
prefix.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

def DecodeCNFOuterInvariant
    (B N inputEnd : ℕ) (clauses : List (List NPComplete.SAT.Literal))
    (tail : Bits) (addr m base c s : ℕ) (σ : Store) : Prop :=
  σ uctOuterReg = clauses.length ∧
  σ uctCursorReg = addr ∧
  σ uctMaxReg = m ∧
  σ uctFreshReg = base ∧
  σ uctCountReg = c ∧
  σ uctSeenReg = s ∧
  σ uctRemainingReg = 0 ∧
  σ uctBoundReg = N ∧
  StoreValuesLe B σ ∧
  CellsZeroFrom inputEnd σ ∧
  25 ≤ addr ∧
  σ uctCursorReg + 1 + σ uctBoundReg ≤ B ∧
  σ uctFreshReg + σ uctLengthReg + 2 ≤ B ∧
  σ uctCountReg + σ uctLengthReg + 2 ≤ B ∧
  σ uctFreshReg + (σ uctOuterReg + 1) * (N + 1) + 2 ≤ B ∧
  σ uctCountReg + (σ uctOuterReg + 1) * (N + 1) + 2 ≤ B ∧
  addr + (clauses.map (encodeList encodeLiteral)).flatten.length ≤ inputEnd ∧
  BitsFrom σ addr ((clauses.map (encodeList encodeLiteral)).flatten ++ tail)

lemma programBoundedIn_decodeCNFStepAtSeen_of_parts
    (B cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
      freshReg countReg tmpReg boundReg seenReg : ℕ) (σ : Store)
    (hB1 : 1 ≤ B)
    (hparser : ProgramBoundedIn B σ
      (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg boundReg))
    (hparserStore : StoreValuesLe B
      ((decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg boundReg).eval σ))
    (hstats : ProgramBoundedIn B
      ((decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg boundReg).eval σ)
      (clauseStatsProgram lengthReg freshReg countReg tmpReg))
    (hidx : outerReg ≤ B ∧ lengthReg ≤ B ∧ seenReg ≤ B) :
    ProgramBoundedIn B σ
      (decodeCNFStepAtSeen cursorReg polReg varReg doneReg outerReg remainingReg maxReg
        lengthReg freshReg countReg tmpReg boundReg seenReg) := by
  have hstatsStore : StoreValuesLe B
      ((clauseStatsProgram lengthReg freshReg countReg tmpReg).eval
        ((decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
          lengthReg boundReg).eval σ)) :=
    program_eval_storeValuesLe _ _ hB1 hparserStore hstats
      (scanFree_clauseStatsProgram lengthReg freshReg countReg tmpReg)
  let σp := (decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
    lengthReg boundReg).eval σ
  let σs := (clauseStatsProgram lengthReg freshReg countReg tmpReg).eval σp
  have houterVal : σs outerReg ≤ B := by
    simpa [σp, σs] using hstatsStore outerReg
  have houter : ProgramBoundedIn B σs
      (.assign outerReg (.sub (.reg outerReg) (.const 1))) := by
    simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
    exact ⟨by omega, by omega, hB1, houterVal⟩
  have houter' : ProgramBoundedIn B
      (((decodeClauseWithLengthProgramAt cursorReg polReg varReg doneReg remainingReg maxReg
        lengthReg boundReg).seq (clauseStatsProgram lengthReg freshReg countReg tmpReg)).eval σ)
      (.assign outerReg (.sub (.reg outerReg) (.const 1))) := by
    rw [eval_seq]
    simpa [σp, σs] using houter
  have hstep : ProgramBoundedIn B σ
      (decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg boundReg) := by
    unfold decodeCNFStepAt decodeCNFClauseStepWithStatsAt
    exact ⟨⟨hparser, hstats⟩, houter'⟩
  have hmark : ProgramBoundedIn B
      ((decodeCNFStepAt cursorReg polReg varReg doneReg outerReg remainingReg maxReg lengthReg
        freshReg countReg tmpReg boundReg).eval σ)
      (decodeCNFMarkSeenProg lengthReg seenReg) := by
    unfold decodeCNFMarkSeenProg
    simp only [ProgramBoundedIn, ExprBoundedIn]
    exact ⟨hidx.2.1, ⟨⟨hidx.2.2, hB1⟩, trivial⟩⟩
  unfold decodeCNFStepAtSeen
  exact ⟨hstep, hmark⟩

lemma programBoundedIn_clauseStatsProgram_of_bounds
    (B lengthReg freshReg countReg tmpReg : ℕ) (σ : Store)
    (hB1 : 1 ≤ B)
    (hidx : lengthReg ≤ B ∧ freshReg ≤ B ∧ countReg ≤ B ∧ tmpReg ≤ B)
    (hdist : lengthReg ≠ freshReg ∧ lengthReg ≠ countReg ∧ lengthReg ≠ tmpReg ∧
      freshReg ≠ countReg ∧ freshReg ≠ tmpReg ∧ countReg ≠ tmpReg)
    (hfresh : σ freshReg + σ lengthReg + 2 ≤ B)
    (hcount : σ countReg + σ lengthReg + 2 ≤ B) :
    ProgramBoundedIn B σ (clauseStatsProgram lengthReg freshReg countReg tmpReg) := by
  rcases hidx with ⟨hlen, hfreshIdx, hcountIdx, htmpIdx⟩
  rcases hdist with ⟨hlf, hlc, hlt, hfc, hft, hct⟩
  simp [clauseStatsProgram, ProgramBoundedIn, ExprBoundedIn,
    eval_assign, Expr.eval, writeReg_diff _ freshReg _ countReg (Ne.symm hfc),
    writeReg_diff _ freshReg _ lengthReg hlf]
  omega

lemma programBoundedIn_decodeCNFStepAtSeen_of_invariant
    (B N inputEnd : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest : List (List NPComplete.SAT.Literal)) (tail : Bits)
    (addr m base c s : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B)
    (hglobal : inputEnd + N + 1 + N * (N + 1) + 1 + N ≤ B)
    (hInv : DecodeCNFOuterInvariant B N inputEnd (ls :: rest) tail addr m base c s σ)
    (hls : ls.length + 1 ≤ N)
    (hvarbound : ∀ l ∈ ls, l.var + 1 ≤ N) :
    ProgramBoundedIn B σ
      (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg) := by
  rcases hInv with ⟨houter, hcursor, hmax, hfresh, hcount, hseen, hrem, hbound,
    hstore, hzero, ha, hcursorBudget, hfreshBudget, hcountBudget, hfreshCountdown,
    hcountCountdown, hwindow, hbits⟩
  have haddr : addr ≤ inputEnd := by omega
  have hcoarse : addr + N + 1 + N * (N + 1) + 1 + N ≤ B := by omega
  have hbits' : BitsFrom σ addr (encodeList encodeLiteral ls ++
      ((rest.map (encodeList encodeLiteral)).flatten ++ tail)) := by
    have hshape : ((ls :: rest).map (encodeList encodeLiteral)).flatten ++ tail =
        encodeList encodeLiteral ls ++ ((rest.map (encodeList encodeLiteral)).flatten ++ tail) := by
      simp
    rw [hshape] at hbits
    exact hbits
  obtain ⟨π, hπ, hparser, hparserStore, hlenπ, hfreshπ, hcountπ⟩ :=
    programBoundedIn_decodeClauseWithLengthProgramAt_of_input B N addr m ls
      ((rest.map (encodeList encodeLiteral)).flatten ++ tail) σ hB1 hB25 ha hstore
      hcursor hmax hbound hls hvarbound hbits' hcoarse
  have hfreshStats : π uctFreshReg + π uctLengthReg + 2 ≤ B := by
    rw [hfreshπ, hlenπ]
    have hq : N + 1 ≤ (σ uctOuterReg + 1) * (N + 1) := by
      have hp : 1 ≤ σ uctOuterReg + 1 := by omega
      have := Nat.le_mul_of_pos_right (N + 1) hp
      rw [Nat.mul_comm]
      exact this
    omega
  have hcountStats : π uctCountReg + π uctLengthReg + 2 ≤ B := by
    rw [hcountπ, hlenπ]
    have hq : N + 1 ≤ (σ uctOuterReg + 1) * (N + 1) := by
      have hp : 1 ≤ σ uctOuterReg + 1 := by omega
      have := Nat.le_mul_of_pos_right (N + 1) hp
      rw [Nat.mul_comm]
      exact this
    omega
  have hstats : ProgramBoundedIn B π
      (clauseStatsProgram uctLengthReg uctFreshReg uctCountReg uctTmpReg) := by
    apply programBoundedIn_clauseStatsProgram_of_bounds B uctLengthReg uctFreshReg
      uctCountReg uctTmpReg π hB1
      ⟨by simp [uctLengthReg]; omega, by simp [uctFreshReg]; omega,
        by simp [uctCountReg]; omega, by simp [uctTmpReg]; omega⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      hfreshStats hcountStats
  rw [hπ] at hparserStore hstats
  apply programBoundedIn_decodeCNFStepAtSeen_of_parts B uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
    uctTmpReg uctBoundReg uctSeenReg σ hB1 hparser hparserStore hstats
  exact ⟨by simp [uctOuterReg]; omega, by simp [uctLengthReg]; omega,
    by simp [uctSeenReg]; omega⟩

/-- The per-clause fresh-variable increment fits the countdown slice width. -/
lemma decode_cnf_outer_prefix_invariant_fresh_inc (n N : ℕ) (h : n + 1 ≤ N) :
    clauseFreshIncByLength n ≤ N + 1 := by
  rcases n with _ | _ | _ | n <;> simp [clauseFreshIncByLength] at h ⊢
  omega

/-- The per-clause three-clause count increment fits the countdown slice width. -/
lemma decode_cnf_outer_prefix_invariant_count_inc (n N : ℕ) (h : n + 1 ≤ N) :
    clauseThreeCountByLength n ≤ N + 1 := by
  rcases n with _ | _ | _ | n <;> simp [clauseThreeCountByLength] at h ⊢ <;> omega

/-- One clause step consumes one slice of the countdown budget. -/
lemma decode_cnf_outer_prefix_invariant_countdown (F inc k N B : ℕ)
    (hinc : inc ≤ N + 1) (hold : F + (k + 1 + 1) * (N + 1) + 2 ≤ B) :
    F + inc + (k + 1) * (N + 1) + 2 ≤ B := by
  have h2 : (k + 1 + 1) * (N + 1) = (k + 1) * (N + 1) + (N + 1) := Nat.succ_mul (k + 1) (N + 1)
  omega

/-- Under `hframe`, the clause step leaves every cell at or above 25 unchanged. -/
lemma decode_cnf_outer_prefix_invariant_cell (σ σ1 : Store) (i : ℕ) (hi : 25 ≤ i)
    (hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg →
      σ1 r = σ r) :
    σ1 i = σ i :=
  hframe i (by simp [uctCursorReg]; omega) (by simp [uctPolReg]; omega)
    (by simp [uctVarReg]; omega) (by simp [uctDoneReg]; omega)
    (by simp [uctOuterReg]; omega) (by simp [uctRemainingReg]; omega)
    (by simp [uctMaxReg]; omega) (by simp [uctLengthReg]; omega)
    (by simp [uctFreshReg]; omega) (by simp [uctCountReg]; omega)
    (by simp [uctTmpReg]; omega) (by simp [uctSeenReg]; omega)

/-- Under `hframe`, the input bits after the consumed clause remain readable. -/
lemma decode_cnf_outer_prefix_invariant_bits_tail (σ σ1 : Store) (a : ℕ)
    (X T : Bits) (ha : 25 ≤ a) (hbits : BitsFrom σ a (X ++ T))
    (hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctPolReg → r ≠ uctVarReg → r ≠ uctDoneReg →
      r ≠ uctOuterReg → r ≠ uctRemainingReg → r ≠ uctMaxReg → r ≠ uctLengthReg →
      r ≠ uctFreshReg → r ≠ uctCountReg → r ≠ uctTmpReg → r ≠ uctSeenReg →
      σ1 r = σ r) :
    BitsFrom σ1 (a + X.length) T := by
  obtain ⟨_, htail⟩ := bitsFrom_append σ a X T hbits
  intro i hi
  rw [decode_cnf_outer_prefix_invariant_cell σ σ1 _ (by omega) hframe]
  exact htail i hi

/-- One clause step of the decoder preserves the outer invariant for the
remaining clauses; the new store is returned as the step's result. -/
lemma decodeCNFStepAtSeen_outer_prefix_invariant_step
    (B N inputEnd : ℕ) (ls : List NPComplete.SAT.Literal)
    (rest : List (List NPComplete.SAT.Literal)) (tail : Bits)
    (addr m base c s : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B)
    (hglobal : inputEnd + N + 1 + N * (N + 1) + 1 + N ≤ B)
    (hhead : ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N)
    (hInv : DecodeCNFOuterInvariant B N inputEnd (ls :: rest) tail addr m base c s σ) :
    ∃ σ1, σ1 = (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
        uctTmpReg uctBoundReg uctSeenReg).eval σ ∧
      DecodeCNFOuterInvariant B N inputEnd rest tail
        (addr + (encodeList encodeLiteral ls).length)
        (max m (literalVarMax ls)) (base + clauseFreshIncByLength ls.length)
        (c + clauseThreeCountByLength ls.length)
        (if ls.length = 0 then s else 1) σ1 := by
  have hbody := programBoundedIn_decodeCNFStepAtSeen_of_invariant B N inputEnd ls rest
    tail addr m base c s σ hB1 hB25 hglobal hInv hhead.1 hhead.2
  rcases hInv with ⟨houter, hcursor, hmax, hfresh, hcount, hseen, hrem, hbound,
    hstore, hzero, ha, hcursorBudget, hfreshBudget, hcountBudget, hfreshCountdown,
    hcountCountdown, hwindow, hbits⟩
  have hshape : ((ls :: rest).map (encodeList encodeLiteral)).flatten ++ tail =
      encodeList encodeLiteral ls ++ ((rest.map (encodeList encodeLiteral)).flatten ++ tail) := by
    simp
  rw [hshape] at hbits
  have houter' : σ uctOuterReg = rest.length + 1 := by simpa using houter
  obtain ⟨hcur1, houter1, hrem1, hmax1, hlen1, hfresh1, hcount1, hseen1,
    hbound1, hframe1⟩ := decodeCNFStepAtSeen_uct_eval N addr m base c rest.length s ls
      ((rest.map (encodeList encodeLiteral)).flatten ++ tail) σ ha houter' hcursor hmax
      hfresh hcount hseen hbound hhead.1 hhead.2 hbits
  have hstore1 := program_eval_storeValuesLe σ _ hB1 hstore hbody
    (scanFree_decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
      uctTmpReg uctBoundReg uctSeenReg)
  generalize hσ1 : (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
    uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
    uctTmpReg uctBoundReg uctSeenReg).eval σ = σ1 at *
  have hincFresh := decode_cnf_outer_prefix_invariant_fresh_inc ls.length N hhead.1
  have hincCount := decode_cnf_outer_prefix_invariant_count_inc ls.length N hhead.1
  rw [houter', hfresh] at hfreshCountdown
  rw [houter', hcount] at hcountCountdown
  have hfc : σ1 uctFreshReg + (σ1 uctOuterReg + 1) * (N + 1) + 2 ≤ B := by
    rw [hfresh1, houter1]
    exact decode_cnf_outer_prefix_invariant_countdown _ _ _ _ _ hincFresh hfreshCountdown
  have hcc : σ1 uctCountReg + (σ1 uctOuterReg + 1) * (N + 1) + 2 ≤ B := by
    rw [hcount1, houter1]
    exact decode_cnf_outer_prefix_invariant_countdown _ _ _ _ _ hincCount hcountCountdown
  have hwindow1 : addr + (encodeList encodeLiteral ls).length +
      (rest.map (encodeList encodeLiteral)).flatten.length ≤ inputEnd := by
    simpa [List.length_append, List.length_flatten, Nat.add_assoc] using hwindow
  have hQ : N + 1 ≤ (σ1 uctOuterReg + 1) * (N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨σ1, rfl, houter1, hcur1, hmax1, hfresh1, hcount1, hseen1, hrem1, hbound1,
    hstore1, ?_, by omega, ?_, ?_, ?_, hfc, hcc, ?_, ?_⟩
  · intro i hi
    rw [decode_cnf_outer_prefix_invariant_cell σ σ1 i (by omega) hframe1]
    exact hzero i hi
  · rw [hcur1, hbound1]
    omega
  · rw [hfresh1, hlen1]
    omega
  · rw [hcount1, hlen1]
    omega
  · exact hwindow1
  · exact decode_cnf_outer_prefix_invariant_bits_tail σ σ1 addr _ _ ha hbits hframe1

lemma decodeCNFStepAtSeen_outer_prefix_invariant
    (B N inputEnd : ℕ) (clauses : List (List NPComplete.SAT.Literal))
    (tail : Bits) (addr m base c s : ℕ) (σ : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B)
    (hglobal : inputEnd + N + 1 + N * (N + 1) + 1 + N ≤ B)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N)
    (hInv : DecodeCNFOuterInvariant B N inputEnd clauses tail addr m base c s σ) :
    ∀ q ≤ clauses.length, ∃ τ addr' m' base' c' s',
      τ = loopEval
        (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
          uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
          uctBoundReg uctSeenReg) q σ ∧
      DecodeCNFOuterInvariant B N inputEnd (clauses.drop q) tail addr' m' base' c' s' τ := by
  induction clauses generalizing addr m base c s σ with
  | nil =>
      intro q hq
      have hq0 : q = 0 := by simpa using hq
      subst q
      exact ⟨σ, addr, m, base, c, s, by simp, by simpa using hInv⟩
  | cons ls rest ih =>
      intro q hq
      cases q with
      | zero =>
          exact ⟨σ, addr, m, base, c, s, by simp, by simpa using hInv⟩
      | succ q =>
          have hq' : q ≤ rest.length := by simpa using hq
          have hboundsRest : ∀ d ∈ rest,
              d.length + 1 ≤ N ∧ ∀ l ∈ d, l.var + 1 ≤ N :=
            fun d hd => hbounds d (by simp [hd])
          obtain ⟨σ1, hσ1, hInv1⟩ := decodeCNFStepAtSeen_outer_prefix_invariant_step B N inputEnd
            ls rest tail addr m base c s σ hB1 hB25 hglobal (hbounds ls (by simp)) hInv
          obtain ⟨τ, addr', m', base', c', s', hτ, hInv'⟩ := ih _ _ _ _ _ σ1 hboundsRest hInv1 q hq'
          refine ⟨τ, addr', m', base', c', s', ?_, hInv'⟩
          rw [loopEval_succ, ← hσ1]
          exact hτ

lemma programBoundedIn_decodeCNFProgramAtSeen_of_outer_state
    (B N inputEnd addr0 : ℕ) (clauses : List (List NPComplete.SAT.Literal))
    (σ0 σpre σ2 : Store)
    (hB1 : 1 ≤ B) (hB25 : 25 ≤ B)
    (hglobal : inputEnd + N + 1 + N * (N + 1) + 1 + N ≤ B)
    (hpre : σpre =
      (Program.assign uctOuterReg (.const 0)).eval
        ((Program.assign uctDoneReg (.const 0)).eval σ0))
    (hprefix : ProgramBoundedIn B σpre
      (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg))
    (hprefixEval :
      (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval σpre = σ2)
    (hbounds : ∀ ls ∈ clauses,
      ls.length + 1 ≤ N ∧ ∀ l ∈ ls, l.var + 1 ≤ N)
    (hInv2 : DecodeCNFOuterInvariant B N inputEnd clauses ([] : Bits) addr0 0 0 0 0 σ2) :
    ProgramBoundedIn B σ0
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg) := by
  have hdone : ProgramBoundedIn B σ0 (.assign uctDoneReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn, uctDoneReg]
    omega
  have houter : ProgramBoundedIn B
      ((Program.assign uctDoneReg (.const 0)).eval σ0)
      (.assign uctOuterReg (.const 0)) := by
    simp [ProgramBoundedIn, ExprBoundedIn, uctOuterReg]
    omega
  have hpref := decodeCNFStepAtSeen_outer_prefix_invariant B N inputEnd clauses ([] : Bits) addr0 0 0 0 0 σ2
    hB1 hB25 hglobal hbounds hInv2
  unfold decodeCNFProgramAtSeen
  simp only [ProgramBoundedIn]
  refine ⟨hdone, ?_⟩
  refine ⟨houter, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact hprefix
  · rw [← hpre, hprefixEval]
    refine ⟨?_, ?_⟩
    · simp [ExprBoundedIn, uctOuterReg]
      omega
    · intro q hq
      change q < σ2 uctOuterReg at hq
      have houter2 := hInv2.1
      rw [houter2] at hq
      have hqle : q ≤ clauses.length := by omega
      obtain ⟨τ, addr', m', base', c', s', hτ, hInvτ⟩ := hpref q hqle
      cases hd : clauses.drop q with
      | nil =>
          have hlen := congrArg List.length hd
          simp only [List.length_drop, List.length_nil] at hlen
          omega
      | cons ls rest =>
          have hInv' : DecodeCNFOuterInvariant B N inputEnd (ls :: rest) ([] : Bits)
              addr' m' base' c' s' τ := by
            rw [hd] at hInvτ
            exact hInvτ
          have hmem : ls ∈ clauses := by
            apply List.mem_of_mem_drop
            rw [hd]
            simp
          have hhead := hbounds ls hmem
          have hbody := programBoundedIn_decodeCNFStepAtSeen_of_invariant B N inputEnd ls rest
            ([] : Bits) addr' m' base' c' s' τ hB1 hB25 hglobal hInv' hhead.1 hhead.2
          rw [← hτ]
          exact hbody

/-- Numeric facts about the envelope bound `B` used by the decoder bound proof. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_global_bounds
    (N B : ℕ) (hB : uniformEmitDispatchEnvelope N ≤ B) :
    1 ≤ B ∧ 25 ≤ B ∧ 25 ≤ uniformAddrNat N + N ∧
      uniformAddrNat N + N + N + 1 + N * (N + 1) + 1 + N ≤ B := by
  have h25 := uniformEmitDispatchEnvelope_ge_25 N
  have hC := uniformAddrNat_ge_25 N
  refine ⟨by omega, by omega, by omega, ?_⟩
  simp [uniformEmitDispatchEnvelope, writerAppendRawSixBound,
    writerAppendRawThreeBound, writerAppendRawStepBound, uniformEmitSyntaxEnvelope,
    uniformEmitLongValueEnvelope, uniformEmitTightEnvelope, uniformAddrNat, uniformMNat,
    uniformStartNat, uniformSlackNat, uniformAddrOffset, relocateControlGap, uctCurJ] at hB ⊢
  nlinarith

/-- Control registers right after the uniform startup of the decoder. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_init_values
    (bits : Bits) (σ0 : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))) :
    σ0 uctBoundReg = bits.length ∧ σ0 uctCursorReg = uniformAddrNat bits.length ∧
      σ0 uctOuterReg = 0 ∧ σ0 uctRemainingReg = 0 ∧ σ0 uctMaxReg = 0 ∧
      σ0 uctFreshReg = 0 ∧ σ0 uctCountReg = 0 ∧ σ0 uctSeenReg = 0 ∧
      σ0 uctLengthReg = 0 := by
  obtain ⟨hb, -, hcursor, -, -, -, houter, hrem, hmax, hlen, hfresh, hcount, -, hseen⟩ :=
    uniformControlInitProg_after_cursor bits
  subst hσ0
  exact ⟨hb, hcursor, houter, hrem, hmax, hfresh, hcount, hseen, hlen⟩

/-- The startup keeps every store value within the supplied bound `B`. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_init_store_le
    (φ : CNF) (B : ℕ) (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B)
    (σ0 : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))) :
    StoreValuesLe B σ0 := by
  have hK25 : 25 ≤ uniformEmitTightEnvelope (encodeCNF φ).length := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
  have hKtoB : uniformEmitTightEnvelope (encodeCNF φ).length ≤ B :=
    ((uniformEmitTightEnvelope_le_long_value_envelope _).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope _)).trans hB
  have hNK : (encodeCNF φ).length ≤ uniformEmitTightEnvelope (encodeCNF φ).length := by
    simp [uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
    omega
  have hσI : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      (bitInputStore (encodeCNF φ)) := by
    intro r
    cases r with
    | zero => exact hNK
    | succ r =>
        simp [bitInputStore]
        split <;> omega
  have hR0 : (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))) 0 =
      (encodeCNF φ).length := (uniformRelocateProg_bitInputStore (encodeCNF φ)).1
  have haddr : uniformAddrE.eval (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))) ≤
      uniformEmitTightEnvelope (encodeCNF φ).length := by
    rw [uniformAddrE_eval, hR0]
    have h := uniform_split_tail_input_end_le_tight (encodeCNF φ).length
    simp [uniformAddrNat] at h ⊢
    omega
  have hσ1 := storeValuesLe_assign (r := uctInputBaseReg)
    (storeValuesLe_uniformRelocateProg_tight φ) haddr
  have hσC : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length)
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))) := by
    have hcursorExpr : (.reg uctInputBaseReg : Expr).eval
        ((Program.assign uctInputBaseReg uniformAddrE).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))) ≤
        uniformEmitTightEnvelope (encodeCNF φ).length := by
      simpa [Expr.eval] using hσ1 uctInputBaseReg
    simpa [uniformCursorInitProg, eval_seq] using storeValuesLe_assign hσ1 hcursorExpr
  subst hσ0
  have hσ0K := program_eval_storeValuesLe _ uniformControlInitProg (by omega) hσC
    (programBoundedIn_uniformControlInitProg _ _ hK25) scanFree_uniformControlInitProg
  exact fun r => (hσ0K r).trans hKtoB

/-- Cells at and above the end of the relocated input are zero after startup. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_init_zero
    (bits : Bits) (σ0 : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))) :
    CellsZeroFrom (uniformAddrNat bits.length + bits.length) σ0 := by
  have hC := uniformAddrNat_ge_25 bits.length
  have hzeroI : CellsZeroFrom (uniformAddrNat bits.length + bits.length) (bitInputStore bits) :=
    fun i hi => bitInputStore_eq_zero_of_ge_inputEnd bits i (by omega)
  have hzeroR : CellsZeroFrom (uniformAddrNat bits.length + bits.length)
      (uniformRelocateProg.eval (bitInputStore bits)) :=
    cellsZeroFrom_of_frame (fun r hr => uniformRelocateProg_frame_ge (bitInputStore bits)
      bits.length _ rfl le_rfl r hr) hzeroI
  have hzeroC : CellsZeroFrom (uniformAddrNat bits.length + bits.length)
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits))) :=
    cellsZeroFrom_of_frame (fun r hr => uniformCursorInitProg_frame uctCursorReg
      uctInputBaseReg r _ (by simp [uctCursorReg]; omega)
      (by simp [uctInputBaseReg]; omega)) hzeroR
  subst hσ0
  exact cellsZeroFrom_of_frame (fun r hr => uniformControlInitProg_frame r _
    (not_mem_uctControlRegs_of_ge r (by omega))) hzeroC

/-- The relocated input window holds the encoded CNF after startup. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_init_bits
    (φ : CNF) (σ0 : Store)
    (hσ0 : σ0 = uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore (encodeCNF φ))))) :
    BitsFrom σ0 (uniformAddrNat (encodeCNF φ).length)
      (encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
        ([] : Bits)) := by
  have henc : encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
      ([] : Bits) = encodeCNF φ := by
    simp [encodeCNF_eq_lists, List.append_nil]
  rw [henc, hσ0]
  exact uniformControlInitProg_bitsFrom _

/-- The two assignments before the outer-count decode keep the store bounded and
leave the decode program bounded. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_pre_bounds
    (B N C : ℕ) (σ0 σpre : Store)
    (hB25 : 25 ≤ B) (hCN : C + N ≤ B) (hNB : N ≤ B)
    (hσ0 : StoreValuesLe B σ0) (hcursor0 : σ0 uctCursorReg = C)
    (hb0 : σ0 uctBoundReg = N)
    (hpre : σpre = (Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval σ0)) :
    StoreValuesLe B σpre ∧
      ProgramBoundedIn B σpre
        (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg) ∧
      σpre uctBoundReg = N := by
  have hσpre : StoreValuesLe B σpre := by
    rw [hpre]
    exact storeValuesLe_assign (storeValuesLe_assign hσ0 (by simp [Expr.eval]))
      (by simp [Expr.eval])
  have hσpreCursor : σpre uctCursorReg = C := by
    rw [hpre]
    simpa [eval_assign, Expr.eval,
      writeReg_diff (writeReg σ0 uctDoneReg 0) uctOuterReg 0 uctCursorReg (by decide),
      writeReg_diff σ0 uctDoneReg 0 uctCursorReg (by decide)] using hcursor0
  have hσpreBound : σpre uctBoundReg = N := by
    rw [hpre]
    simpa [eval_assign, Expr.eval,
      writeReg_diff (writeReg σ0 uctDoneReg 0) uctOuterReg 0 uctBoundReg (by decide),
      writeReg_diff σ0 uctDoneReg 0 uctBoundReg (by decide)] using hb0
  have hσpreOuter : σpre uctOuterReg = 0 := by
    rw [hpre]
    simp [eval_assign, Expr.eval]
  refine ⟨hσpre, ?_, hσpreBound⟩
  apply programBoundedIn_decodeNatProgramAt_of_bounds uctCursorReg uctOuterReg uctDoneReg
    uctBoundReg B σpre (by decide) (by decide) (by decide)
    ⟨by simp [uctCursorReg]; omega, by simp [uctOuterReg]; omega,
      by simp [uctDoneReg]; omega, by simp [uctBoundReg]⟩
  · rw [hσpreCursor, hσpreBound]
    exact hCN
  · rw [hσpreOuter, hσpreBound]
    omega

/-- Effect of decoding the clause count: new cursor and outer count, and a frame
away from the three decoder registers. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_frame
    (cls : List (List NPComplete.SAT.Literal)) (N C : ℕ) (σ0 σpre σ2 : Store)
    (hpre : σpre = (Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval σ0))
    (hcursor0 : σ0 uctCursorReg = C) (houterLe : cls.length + 1 ≤ N) (hC25 : 25 ≤ C)
    (hbits0 : BitsFrom σ0 C (encodeList (encodeList encodeLiteral) cls ++ ([] : Bits)))
    (hσ2 : σ2 = (decodeNatProgram uctCursorReg uctOuterReg uctDoneReg N).eval σpre) :
    σ2 uctCursorReg = C + cls.length + 1 ∧ σ2 uctOuterReg = cls.length ∧
      ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r := by
  have hbelow : uctCursorReg < C ∧ uctOuterReg < C ∧ uctDoneReg < C := by
    simp [uctCursorReg, uctOuterReg, uctDoneReg]
    omega
  obtain ⟨hc, ho, -, hf⟩ := decode_cnf_outer_decode uctCursorReg uctOuterReg uctDoneReg N C
    cls ([] : Bits) σ0 (by decide) (by decide) (by decide) hbelow hcursor0 houterLe hbits0
  subst hpre hσ2
  exact ⟨hc, ho, hf⟩

/-- Under `hf`, the listed registers retain their startup values after clause-count decoding. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_registers
    (N : ℕ) (σ0 σ2 : Store)
    (hf : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r)
    (hb0 : σ0 uctBoundReg = N) (hrem0 : σ0 uctRemainingReg = 0) (hmax0 : σ0 uctMaxReg = 0)
    (hfresh0 : σ0 uctFreshReg = 0) (hcount0 : σ0 uctCountReg = 0)
    (hseen0 : σ0 uctSeenReg = 0) (hlen0 : σ0 uctLengthReg = 0) :
    σ2 uctRemainingReg = 0 ∧ σ2 uctMaxReg = 0 ∧ σ2 uctFreshReg = 0 ∧
      σ2 uctCountReg = 0 ∧ σ2 uctSeenReg = 0 ∧ σ2 uctBoundReg = N ∧ σ2 uctLengthReg = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hf _ (by decide) (by decide) (by decide)).trans hrem0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hmax0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hfresh0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hcount0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hseen0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hb0
  · exact (hf _ (by decide) (by decide) (by decide)).trans hlen0

/-- Under `hf`, cells above the input end that start at zero remain zero after decoding. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_zero
    (inputEnd : ℕ) (σ0 σ2 : Store) (hinput25 : 25 ≤ inputEnd)
    (hf : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r)
    (hzero0 : CellsZeroFrom inputEnd σ0) :
    CellsZeroFrom inputEnd σ2 := by
  intro i hi
  rw [hf i (by simp [uctCursorReg]; omega) (by simp [uctOuterReg]; omega)
    (by simp [uctDoneReg]; omega)]
  exact hzero0 i hi

/-- Under `hf`, the clause encodings remain readable after the clause-count prefix. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_bits
    (cls : List (List NPComplete.SAT.Literal)) (C : ℕ) (σ0 σ2 : Store) (hC25 : 25 ≤ C)
    (hf : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r)
    (hbits0 : BitsFrom σ0 C (encodeList (encodeList encodeLiteral) cls ++ ([] : Bits))) :
    BitsFrom σ2 (C + cls.length + 1)
      (((cls.map (encodeList encodeLiteral)).flatten) ++ ([] : Bits)) := by
  have hshape : encodeList (encodeList encodeLiteral) cls ++ ([] : Bits) =
      encodeNat cls.length ++ ((cls.map (encodeList encodeLiteral)).flatten ++ ([] : Bits)) := by
    simp [encodeList]
  rw [hshape] at hbits0
  obtain ⟨_, htail⟩ := bitsFrom_append σ0 C (encodeNat cls.length) _ hbits0
  intro i hi
  rw [hf (C + cls.length + 1 + i) (by simp [uctCursorReg]; omega)
    (by simp [uctOuterReg]; omega) (by simp [uctDoneReg]; omega)]
  have haddrEq : C + cls.length + 1 + i = C + (encodeNat cls.length).length + i := by
    simp only [encodeNat_length]
    omega
  rw [haddrEq]
  exact htail i hi

/-- The encoded clauses fit inside the input window. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_window (φ : CNF) :
    uniformAddrNat (encodeCNF φ).length + (φ.clauses.map (fun c => c.lits)).length + 1 +
      (((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten).length ≤
      uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
  have henc : ((φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral)).flatten =
      (φ.clauses.map encodeClause).flatten := by
    rw [List.map_map]
    have hfun : (encodeList encodeLiteral ∘ fun c : Clause => c.lits) = encodeClause := by
      funext c
      simp [NPComplete.CookLevin.encodeClause]
    rw [hfun]
  rw [henc]
  simpa [List.length_map] using uniform_producer_input_end_window φ

/-- Assembly of the outer-loop invariant at the state after the clause-count decode. -/
lemma programBoundedIn_decodeCNFProgramAtSeen_of_input_outer_invariant
    (B N inputEnd C : ℕ) (cls : List (List NPComplete.SAT.Literal)) (σ2 : Store)
    (hglobal : inputEnd + N + 1 + N * (N + 1) + 1 + N ≤ B) (hC25 : 25 ≤ C)
    (houterLe : cls.length + 1 ≤ N) (hσ2 : StoreValuesLe B σ2)
    (houter : σ2 uctOuterReg = cls.length) (hcursor : σ2 uctCursorReg = C + cls.length + 1)
    (hrem : σ2 uctRemainingReg = 0) (hmax : σ2 uctMaxReg = 0) (hfresh : σ2 uctFreshReg = 0)
    (hcount : σ2 uctCountReg = 0) (hseen : σ2 uctSeenReg = 0) (hbound : σ2 uctBoundReg = N)
    (hlength : σ2 uctLengthReg = 0) (hzero2 : CellsZeroFrom inputEnd σ2)
    (hbits2 : BitsFrom σ2 (C + cls.length + 1)
      (((cls.map (encodeList encodeLiteral)).flatten) ++ ([] : Bits)))
    (hwindow2 : C + cls.length + 1 + ((cls.map (encodeList encodeLiteral)).flatten).length ≤
      inputEnd) :
    DecodeCNFOuterInvariant B N inputEnd cls ([] : Bits) (C + cls.length + 1) 0 0 0 0 σ2 := by
  have hmul : (cls.length + 1) * (N + 1) ≤ N * (N + 1) := Nat.mul_le_mul_right _ houterLe
  refine ⟨houter, hcursor, hmax, hfresh, hcount, hseen, hrem, hbound, hσ2, hzero2,
    by omega, ?_, ?_, ?_, ?_, ?_, hwindow2, hbits2⟩
  · rw [hcursor, hbound]
    omega
  · rw [hfresh, hlength]
    omega
  · rw [hcount, hlength]
    omega
  · rw [hfresh, houter]
    omega
  · rw [hcount, houter]
    omega

lemma programBoundedIn_decodeCNFProgramAtSeen_of_input
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ProgramBoundedIn B
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg) := by
  obtain ⟨hB1, hB25, hinput25, hglobal⟩ :=
    programBoundedIn_decodeCNFProgramAtSeen_of_input_global_bounds (encodeCNF φ).length B hB
  generalize hσ0 : uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))) = σ0
  have hσ0' := hσ0.symm
  obtain ⟨hb0, hcursor0, -, hrem0, hmax0, hfresh0, hcount0, hseen0, hlen0⟩ :=
    programBoundedIn_decodeCNFProgramAtSeen_of_input_init_values (encodeCNF φ) σ0 hσ0'
  have hσ0le := programBoundedIn_decodeCNFProgramAtSeen_of_input_init_store_le φ B hB σ0 hσ0'
  have hzero0 := programBoundedIn_decodeCNFProgramAtSeen_of_input_init_zero (encodeCNF φ) σ0 hσ0'
  have hbits0 := programBoundedIn_decodeCNFProgramAtSeen_of_input_init_bits φ σ0 hσ0'
  have hbounds : ∀ ls ∈ φ.clauses.map (fun c => c.lits),
      ls.length + 1 ≤ (encodeCNF φ).length ∧ ∀ l ∈ ls, l.var + 1 ≤ (encodeCNF φ).length := by
    simpa using encodeCNF_scan_bounds φ
  have houterLe : (φ.clauses.map (fun c => c.lits)).length + 1 ≤ (encodeCNF φ).length := by
    simpa using encodeCNF_length_ge_clauseCount φ
  have hC25 := uniformAddrNat_ge_25 (encodeCNF φ).length
  obtain ⟨σpre, hpre⟩ : ∃ σpre : Store, σpre = (Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval σ0) := ⟨_, rfl⟩
  obtain ⟨hσpre, hpreBound, hσpreBound⟩ :=
    programBoundedIn_decodeCNFProgramAtSeen_of_input_pre_bounds B (encodeCNF φ).length
      (uniformAddrNat (encodeCNF φ).length) σ0 σpre hB25 (by omega) (by omega) hσ0le
      hcursor0 hb0 hpre
  obtain ⟨σ2, hσ2⟩ : ∃ σ2 : Store,
      (decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg).eval σpre = σ2 :=
    ⟨_, rfl⟩
  have hσ2le : StoreValuesLe B σ2 := by
    rw [← hσ2]
    exact program_eval_storeValuesLe σpre _ hB1 hσpre hpreBound
      (scanFree_decodeNatProgramAt uctCursorReg uctOuterReg uctDoneReg uctBoundReg)
  have hAtEq := decodeNatProgramAt_eq uctCursorReg uctOuterReg uctDoneReg uctBoundReg
    (encodeCNF φ).length σpre hσpreBound
  obtain ⟨hσ2cursor, hσ2outer, hframe⟩ :=
    programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_frame
      (φ.clauses.map (fun c => c.lits)) (encodeCNF φ).length
      (uniformAddrNat (encodeCNF φ).length) σ0 σpre σ2 hpre hcursor0 houterLe hC25 hbits0
      (by rw [← hAtEq, hσ2])
  obtain ⟨hσ2rem, hσ2max, hσ2fresh, hσ2count, hσ2seen, hσ2bound, hσ2length⟩ :=
    programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_registers (encodeCNF φ).length
      σ0 σ2 hframe hb0 hrem0 hmax0 hfresh0 hcount0 hseen0 hlen0
  have hInv2 := programBoundedIn_decodeCNFProgramAtSeen_of_input_outer_invariant B
    (encodeCNF φ).length (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length)
    (uniformAddrNat (encodeCNF φ).length) (φ.clauses.map (fun c => c.lits)) σ2 hglobal hC25
    houterLe hσ2le hσ2outer hσ2cursor hσ2rem hσ2max hσ2fresh hσ2count hσ2seen hσ2bound
    hσ2length
    (programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_zero _ σ0 σ2 hinput25 hframe hzero0)
    (programBoundedIn_decodeCNFProgramAtSeen_of_input_decode_bits _ _ σ0 σ2 hC25 hframe hbits0)
    (programBoundedIn_decodeCNFProgramAtSeen_of_input_window φ)
  exact programBoundedIn_decodeCNFProgramAtSeen_of_outer_state B (encodeCNF φ).length
    (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length)
    (uniformAddrNat (encodeCNF φ).length + (φ.clauses.map (fun c => c.lits)).length + 1)
    (φ.clauses.map (fun c => c.lits)) σ0 σpre σ2 hB1 hB25 hglobal hpre hpreBound
    hσ2 hbounds hInv2

lemma programBoundedIn_uniformProducerFinalizeProg
    (B N : ℕ) (σ : Store)
    (hσ : StoreValuesLe B σ)
    (h0 : σ 0 = uniformMNat N)
    (hMC : uniformMNat N + uctCurJ ≤ B)
    (hstart : uniformStartNat ≤ B) :
    ProgramBoundedIn B σ uniformProducerFinalizeProg := by
  have hstart' : 100 ≤ B := by
    simpa [uniformStartNat, relocateControlGap] using hstart
  have hB1 : 1 ≤ B := by
    omega
  have hOutBase : uctOutBaseReg ≤ B := by
    simp [uctOutBaseReg]
    exact Nat.le_trans (by decide) hstart'
  have hOutLen : uctOutLenReg ≤ B := by
    simp [uctOutLenReg]
    exact Nat.le_trans (by decide) hstart'
  have hσb : StoreValuesLe B
      ((Program.assign uctOutBaseReg uniformStartE).eval σ) := by
    intro r
    by_cases hr : r = uctOutBaseReg
    · subst r
      simp [uniformStartE, uctOutBaseReg, eval_assign, Expr.eval]
      exact hstart
    · simpa [eval_assign, Expr.eval, writeReg_diff _ uctOutBaseReg _ _ hr] using hσ r
  let σb := (Program.assign uctOutBaseReg uniformStartE).eval σ
  have h0b : σb 0 = uniformMNat N := by
    have hne : (0 : ℕ) ≠ uctOutBaseReg := by simp [uctOutBaseReg]
    simpa [σb, uniformStartE, eval_assign, Expr.eval,
      writeReg_diff σ uctOutBaseReg _ 0 hne] using h0
  have haddr : σb 0 + uctCurJ ≤ B := by
    rw [h0b]
    exact hMC
  have hcell : σb (σb 0 + uctCurJ) ≤ B := hσb _
  have hcell' : σb (uniformMNat N + uctCurJ) ≤ B := by
    simpa [h0b] using hcell
  have hctl : ExprBoundedIn B σb (ctlCell uctCurJ) := by
    simp only [ctlCell, ctlAddr, ExprBoundedIn, Expr.eval]
    exact ⟨⟨by omega, by omega, haddr⟩, haddr⟩
  have hstartE : ExprBoundedIn B σb uniformStartE := by
    simp [uniformStartE, ExprBoundedIn]
    omega
  have hlenE : ExprBoundedIn B σb (.sub (ctlCell uctCurJ) uniformStartE) := by
    refine ⟨hctl, hstartE, ?_⟩
    simp only [ctlCell, ctlAddr, Expr.eval]
    simpa [h0b] using hcell'
  let σl := (Program.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)).eval σb
  have hpBase : ProgramBoundedIn B σ (.assign uctOutBaseReg uniformStartE) := by
    exact ⟨hOutBase, by simpa [uniformStartE, ExprBoundedIn] using hstart⟩
  have hpLen : ProgramBoundedIn B σb
      (.assign uctOutLenReg (.sub (ctlCell uctCurJ) uniformStartE)) := by
    exact ⟨hOutLen, hlenE⟩
  have hpFinal : ProgramBoundedIn B σl (finalizeOutputProg uctOutBaseReg uctOutLenReg) := by
    unfold finalizeOutputProg
    have hp1 : ProgramBoundedIn B σl
        (.assign outLenCell (.reg uctOutLenReg)) := by
      exact ⟨hB1, hOutLen⟩
    let σ1 := (Program.assign outLenCell (.reg uctOutLenReg)).eval σl
    have hp2 : ProgramBoundedIn B σ1
        (.assign outAddrCell (.reg uctOutBaseReg)) := by
      exact ⟨Nat.zero_le _, hOutBase⟩
    exact ⟨hp1, hp2⟩
  unfold uniformProducerFinalizeProg
  exact ⟨hpBase, ⟨hpLen, hpFinal⟩⟩

lemma exprBoundedIn_uniformAddrE_of_input
    (φ : CNF) (B : ℕ) (σ : Store)
    (h0 : σ 0 = (encodeCNF φ).length)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ExprBoundedIn B σ uniformAddrE := by
  set N := (encodeCNF φ).length
  have haddr : uniformAddrNat N ≤ B := by
    have hlong := uniformEmitLongValueEnvelope_le_dispatch_envelope N
    have ht := uniform_split_tail_input_end_le_tight N
    have htight : uniformAddrNat N ≤ uniformEmitTightEnvelope N := by omega
    exact htight.trans (uniformEmitTightEnvelope_le_long_value_envelope N |>.trans hlong |>.trans hB)
  have hK : uniformEmitTightEnvelope N ≤ B :=
    (uniformEmitTightEnvelope_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans hB)
  have hN : N ≤ B := by
    exact (uniform_emit_n_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N) |>.trans hB
  have hM : uniformMNat N ≤ B := by
    have h := hK
    simp [uniformEmitTightEnvelope] at h ⊢
    omega
  have hslack : (N + 1) * (N + 1) * (N + 1) + 16 ≤ B := by
    have h := hK
    simp [uniformEmitTightEnvelope, uniformMNat, uniformSlackNat, uniformStartNat,
      relocateControlGap] at h
    omega
  have h25 : 25 ≤ B := by
    exact (uniformEmitDispatchEnvelope_ge_25 N).trans hB
  have hsEval : uniformSlackE.eval σ ≤ B := by
    have hsEvalExact : uniformSlackE.eval σ = uniformSlackNat N := by
      simp [uniformSlackE, Expr.eval, h0, uniformSlackNat, N]
      ring
    rw [hsEvalExact]
    simpa [uniformSlackNat] using hslack
  have hsEvalExact : uniformSlackE.eval σ = uniformSlackNat N := by
    simp [uniformSlackE, Expr.eval, h0, uniformSlackNat, N]
    ring
  have hslack' : uniformSlackNat N ≤ B := by
    simpa [uniformSlackNat] using hslack
  have hsval : (σ 0 + 1) * (σ 0 + 1) * (σ 0 + 1) + 16 ≤ B := by
    rw [h0]
    simpa [N] using hslack
  have hsE : ExprBoundedIn B σ uniformSlackE := by
    unfold uniformSlackE
    simp [ExprBoundedIn, Expr.eval, h0]
    rw [h0] at hsval
    ring_nf at hslack hsval ⊢
    repeat' apply And.intro
    all_goals nlinarith
  have hstart : uniformStartNat ≤ B := by
    have h := hM
    simp [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap] at h
    have h100 : 100 ≤ B := by omega
    simpa [uniformStartNat, relocateControlGap] using h100
  have hmE : ExprBoundedIn B σ uniformMFromN := by
    refine ⟨hstart, hsE, ?_⟩
    have hM' : uniformStartNat + uniformSlackNat N ≤ B := by
      simpa [uniformMNat] using hM
    calc
      uniformMFromN.eval σ = uniformStartNat + uniformSlackNat N := by
        simp [uniformMFromN, uniformSlackNat, uniformStartNat, relocateControlGap,
          Expr.eval, hsEvalExact]
      _ ≤ B := hM'
  unfold uniformAddrE
  refine ⟨hmE, ?_, ?_⟩
  · simp [ExprBoundedIn, uniformAddrOffset]
    omega
  have haddrExpr : uniformAddrE.eval σ ≤ B := by
    rw [uniformAddrE_eval, h0]
    exact haddr
  simpa [uniformAddrE, Expr.eval] using haddrExpr

lemma exprBoundedIn_uniformME_of_input
    (φ : CNF) (B : ℕ) (σ : Store)
    (hN : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ExprBoundedIn B σ uniformME := by
  set N := (encodeCNF φ).length
  have hK : uniformEmitTightEnvelope N ≤ B :=
    (uniformEmitTightEnvelope_le_long_value_envelope N).trans
      (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans hB)
  have hslack : (N + 1) * (N + 1) * (N + 1) + 16 ≤ B := by
    have h := hK
    simp [uniformEmitTightEnvelope, uniformMNat, uniformSlackNat, uniformStartNat,
      relocateControlGap] at h
    omega
  have h25 : 25 ≤ B := by
    exact (uniformEmitDispatchEnvelope_ge_25 N).trans hB
  have hN' : σ 23 = N := by simpa [uctSavedBoundReg] using hN
  unfold uniformME
  simp [ExprBoundedIn, Expr.eval, hN', N, uctSavedBoundReg, uniformStartNat,
    relocateControlGap]
  have hK' := hK
  simp [uniformEmitTightEnvelope, uniformMNat, uniformSlackNat, uniformStartNat,
    relocateControlGap] at hK'
  dsimp [N] at hslack ⊢
  ring_nf at hslack hK' ⊢
  repeat' apply And.intro
  all_goals nlinarith

lemma programBoundedIn_uniformRelocateProg_of_input
    (φ : CNF) (B : ℕ)
    (hB : uniformEmitDispatchEnvelope (encodeCNF φ).length ≤ B) :
    ProgramBoundedIn B (bitInputStore (encodeCNF φ)) uniformRelocateProg := by
  have h : (encodeCNF φ).length + relocateControlGap + (encodeCNF φ).length ≤ B := by
    have hlong := uniformEmitLongValueEnvelope_le_dispatch_envelope (encodeCNF φ).length
    have hreq : (encodeCNF φ).length + relocateControlGap + (encodeCNF φ).length ≤
        uniformEmitLongValueEnvelope (encodeCNF φ).length := by
      simp [uniformEmitLongValueEnvelope, uniformEmitTightEnvelope,
        uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap, uctCurJ]
      nlinarith
    exact hreq.trans (hlong.trans hB)
  let N := (encodeCNF φ).length
  let σ := bitInputStore (encodeCNF φ)
  have h0 : σ 0 = N := rfl
  have h25 : 25 ≤ B := by
    exact (uniformEmitDispatchEnvelope_ge_25 N).trans hB
  have haddrE : ExprBoundedIn B σ uniformAddrE :=
    exprBoundedIn_uniformAddrE_of_input φ B σ (by rfl) hB
  have hNctl : N + relocateControlGap + N ≤ B := by simpa [N] using h
  have hC : uniformAddrNat N + N ≤ B :=
    (uniform_split_tail_input_end_le_tight N).trans
      (uniformEmitTightEnvelope_le_long_value_envelope N |>.trans
        (uniformEmitLongValueEnvelope_le_dispatch_envelope N |>.trans hB))
  have hN1 : N + relocateSrcJ ≤ B := by
    simp [relocateSrcJ, relocateControlGap] at hNctl ⊢
    omega
  have hN2 : N + relocateDstJ ≤ B := by
    simp [relocateDstJ, relocateControlGap] at hNctl ⊢
    omega
  have hN3 : N + relocateLenJ ≤ B := by
    simp [relocateLenJ, relocateControlGap] at hNctl ⊢
    omega
  have hN4 : N + relocateBaseJ ≤ B := by
    simp [relocateBaseJ, relocateControlGap] at hNctl ⊢
    omega
  have he1 : ExprBoundedIn B σ (.const 1) := by
    simp [ExprBoundedIn]
    omega
  have hp1 := relocateCtlAssign_programBoundedIn σ N B relocateSrcJ (.const 1) h0 he1 hN1
  let σ1 := (relocateCtlAssign relocateSrcJ (.const 1)).eval σ
  have h01 : σ1 0 = N := by
    simp [σ1, relocateCtlAssign, relocateCtlAddr, relocateSrcJ,
      Expr.eval, writeReg, h0]
  have haddrE1 : ExprBoundedIn B σ1 uniformAddrE :=
    exprBoundedIn_uniformAddrE_of_input φ B σ1 h01 hB
  have hp2 := relocateCtlAssign_programBoundedIn σ1 N B relocateDstJ uniformAddrE
    h01 haddrE1 hN2
  let σ2 := (relocateCtlAssign relocateDstJ uniformAddrE).eval σ1
  have h02 : σ2 0 = N := by
    simp [σ2, relocateCtlAssign, relocateCtlAddr, relocateDstJ,
      Expr.eval, writeReg, h01]
  have he3 : ExprBoundedIn B σ2 (.reg 0) := by
    simp [ExprBoundedIn]
  have hp3 := relocateCtlAssign_programBoundedIn σ2 N B relocateLenJ (.reg 0) h02 he3 hN3
  let σ3 := (relocateCtlAssign relocateLenJ (.reg 0)).eval σ2
  have h03 : σ3 0 = N := by
    simp [σ3, relocateCtlAssign, relocateCtlAddr, relocateLenJ,
      Expr.eval, writeReg, h02]
  have haddrE3 : ExprBoundedIn B σ3 uniformAddrE :=
    exprBoundedIn_uniformAddrE_of_input φ B σ3 h03 hB
  have hp4 := relocateCtlAssign_programBoundedIn σ3 N B relocateBaseJ uniformAddrE
    h03 haddrE3 hN4
  have hsetup : ProgramBoundedIn B σ uniformRelocateSetup := by
    unfold uniformRelocateSetup
    exact ⟨hp1, ⟨hp2, ⟨hp3, hp4⟩⟩⟩
  have hbody : ∀ m' < N,
      ProgramBoundedIn B (loopEval relocateStep m' (uniformRelocateSetup.eval σ))
        relocateStep := by
    intro m' hm'
    have hInv := uniform_relocate_loop_invariant σ N h0 m' (by omega)
    exact relocateStep_programBoundedIn _ N (uniformAddrNat N) m' B hInv.1
      hInv.2.1 hInv.2.2.1 (uniformAddrNat_ge_gap _) hm' hC
  have hsetup0 : (uniformRelocateSetup.eval σ) 0 = N := by
    rw [uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  have hlen : ExprBoundedIn B (uniformRelocateSetup.eval σ)
      (relocateCtlCell relocateLenJ) :=
    relocateCtlCell_exprBoundedIn _ _ _ relocateLenJ hsetup0 (by omega)
  have hbound : (relocateCtlCell relocateLenJ).eval
      (uniformRelocateSetup.eval σ) = N := by
    rw [relocateCtlCell_eval, uniformRelocateSetup_eval N σ h0]
    simp [relocateSrcJ, relocateDstJ, relocateLenJ, relocateBaseJ, h0]
  change ProgramBoundedIn B σ
      (uniformRelocateSetup.seq (.forN (relocateCtlCell relocateLenJ) relocateStep))
  exact ⟨hsetup, ⟨hlen, by simpa [hbound] using hbody⟩⟩

lemma programBoundedIn_uniformCursorInitProg_of_bounds
    (B : ℕ) (σ : Store) (hB25 : 25 ≤ B)
    (haddr : ExprBoundedIn B σ uniformAddrE) :
    ProgramBoundedIn B σ (uniformCursorInitProg uctCursorReg uctInputBaseReg) := by
  unfold uniformCursorInitProg
  simp only [ProgramBoundedIn]
  refine ⟨⟨by simp [uctInputBaseReg]; omega, haddr⟩, ?_⟩
  refine ⟨by simp [uctCursorReg]; omega, ?_⟩
  simp [ExprBoundedIn, uctInputBaseReg]
  omega

lemma programBoundedIn_uniformPostDecodeStatsProg_of_bounds
    (B : ℕ) (σ : Store) (hB25 : 25 ≤ B)
    (hσ : StoreValuesLe B σ)
    (hmax : σ uctMaxReg + 1 ≤ B)
    (hsum : σ uctMaxReg + 1 + σ uctFreshReg ≤ B) :
    ProgramBoundedIn B σ uniformPostDecodeStatsProg := by
  let σ1 := (Program.assign uctTmpReg (.reg uctFreshReg)).eval σ
  have hσ1 : StoreValuesLe B σ1 :=
    storeValuesLe_assign hσ (by simp [Expr.eval]; omega)
  have hmax1 : σ1 uctMaxReg = σ uctMaxReg := by
    simp [σ1, eval_assign, Expr.eval,
      writeReg_diff _ uctTmpReg _ uctMaxReg (by decide)]
  have hseen1 : σ1 uctSeenReg = σ uctSeenReg := by
    simp [σ1, eval_assign, Expr.eval,
      writeReg_diff _ uctTmpReg _ uctSeenReg (by decide)]
  have htmp1 : σ1 uctTmpReg = σ uctFreshReg := by
    simp [σ1, eval_assign, Expr.eval, writeReg_same]
  have hmax1' : σ1 7 = σ uctMaxReg := by
    simpa [uctMaxReg] using hmax1
  have hif : ProgramBoundedIn B σ1
      (Program.ifNZ (.reg uctSeenReg)
        (.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1))) .skip) := by
    unfold ProgramBoundedIn
    refine ⟨?_, ?_, trivial⟩
    · simp [ExprBoundedIn, uctSeenReg]
      omega
    · have hmaxIdx : uctMaxReg ≤ B := by
        have : 7 ≤ B := by omega
        simpa [uctMaxReg] using this
      refine ⟨hmaxIdx, ?_⟩
      simp only [ExprBoundedIn]
      simp only [Expr.eval]
      exact ⟨hmaxIdx, by omega, by rw [hmax1]; exact hmax⟩
  let σ2 := (Program.ifNZ (.reg uctSeenReg)
      (.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1))) .skip).eval σ1
  have hσ2 : StoreValuesLe B σ2 :=
    program_eval_storeValuesLe σ1 _ (by omega) hσ1 hif (by simp [ScanFree])
  have hsum2 : σ2 uctMaxReg + σ2 uctTmpReg ≤ B := by
    rw [show σ2 = (Program.ifNZ (.reg uctSeenReg)
      (.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1))) .skip).eval σ1 from rfl]
    rw [eval_ifNZ]
    by_cases hz : σ1 uctSeenReg = 0
    · rw [ite_eq_right (by simpa [Expr.eval] using hz)]
      simp [eval_skip, hmax1, htmp1]
      omega
    · rw [ite_eq_left (by simpa [Expr.eval] using hz)]
      simp [eval_assign, Expr.eval, hmax1, htmp1,
        writeReg_diff _ uctMaxReg _ uctTmpReg (by decide)]
      omega
  have hlast : ProgramBoundedIn B σ2
    (.assign uctFreshReg (.add (.reg uctMaxReg) (.reg uctTmpReg))) := by
    have hfreshIdx : uctFreshReg ≤ B := by
      have : 9 ≤ B := by omega
      simpa [uctFreshReg] using this
    refine ⟨hfreshIdx, ?_⟩
    simp only [ExprBoundedIn, Expr.eval]
    have hmaxIdx : uctMaxReg ≤ B := by
      have : 7 ≤ B := by omega
      simpa [uctMaxReg] using this
    have htmpIdx : uctTmpReg ≤ B := by
      have : 11 ≤ B := by omega
      simpa [uctTmpReg] using this
    exact ⟨hmaxIdx, htmpIdx, hsum2⟩
  unfold uniformPostDecodeStatsProg
  refine ⟨?_, ?_⟩
  · simpa [σ1] using
      (show ProgramBoundedIn B σ (.assign uctTmpReg (.reg uctFreshReg)) from
        ⟨by
          have : 11 ≤ B := by omega
          simpa [uctTmpReg] using this, by
            have : uctFreshReg ≤ B := by
              have : 9 ≤ B := by omega
              simpa [uctFreshReg] using this
            simpa [ExprBoundedIn] using this⟩)
  · simpa [σ1, σ2] using (show ProgramBoundedIn B σ1
      ((Program.ifNZ (.reg uctSeenReg)
        (.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1))) .skip).seq
        (.assign uctFreshReg (.add (.reg uctMaxReg) (.reg uctTmpReg)))) from
      ⟨hif, hlast⟩)

lemma decodeCNFProgramAtSeen_uct_bound_frame (σ : Store) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctBoundReg = σ uctBoundReg := by
  exact (of_decide_eq_true (by decide +kernel) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).Avoids (fun r => r = uctBoundReg)).eval_frame σ rfl

end NPComplete.CookLevin

module

public import NPComplete.CookLevin.UniformEmit.LowRegisterBounds

/-!
# Producer layout bounds

Register placement and output sizing must be fixed before the producer can be shown to fit its
store. This module proves the address, capacity, and output-length bounds that support the semantic
emission arguments.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral encodeThreeCNF encodeThreeClause)


/-! ## Exit-state value bounds of the full decode phase -/

lemma cnfSeenStat_le_one (s : ℕ) (cs : List (List Literal)) (hs : s ≤ 1) :
    cnfSeenStat s cs ≤ 1 := by
  induction cs generalizing s with
  | nil => simpa [cnfSeenStat] using hs
  | cons ls rest ih =>
      simp only [cnfSeenStat]
      split_ifs
      · exact ih _ hs
      · exact ih _ le_rfl

lemma cnfLiteralVarMaxStat_le (bound : ℕ) (m : ℕ) (cs : List (List Literal))
    (hm : m ≤ bound)
    (hb : ∀ ls ∈ cs, ∀ l ∈ ls, l.var + 1 ≤ bound) :
    cnfLiteralVarMaxStat m cs ≤ bound := by
  have hlitmax : ∀ ls : List Literal, (∀ l ∈ ls, l.var + 1 ≤ bound) →
      literalVarMax ls ≤ bound := by
    intro ls
    induction ls with
    | nil => intro _; simp [literalVarMax]
    | cons l ls' ih =>
        intro hmem
        simp only [literalVarMax]
        refine max_le ?_ (ih (fun l' hl' => hmem l' (by simp [hl'])))
        have := hmem l (by simp)
        omega
  induction cs generalizing m with
  | nil => simpa [cnfLiteralVarMaxStat] using hm
  | cons ls rest ih =>
      simp only [cnfLiteralVarMaxStat]
      exact ih (max m (literalVarMax ls))
        (max_le hm (hlitmax ls (fun l hl => hb ls (by simp) l hl)))
        (fun ls' hl' l' hl'' => hb ls' (by simp [hl']) l' hl'')

/-- Given the initial encoded list and the frame hypothesis, its clause payload
bits remain readable in the resulting store after the length prefix. -/
lemma uniform_decode_state_low_regs_tail_bits (σ σ2 : Store) (A : ℕ)
    (clauses : List (List Literal))
    (hlists : BitsFrom σ A (encodeList (encodeList encodeLiteral) clauses ++ ([] : Bits)))
    (hA : 25 ≤ A)
    (hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ r) :
    BitsFrom σ2 (A + clauses.length + 1)
      ((clauses.map (encodeList encodeLiteral)).flatten ++ ([] : Bits)) := by
  have hshape : encodeList (encodeList encodeLiteral) clauses ++ ([] : Bits) =
      encodeNat clauses.length ++ ((clauses.map (encodeList encodeLiteral)).flatten ++
        ([] : Bits)) := by
    simp [encodeList]
  rw [hshape] at hlists
  obtain ⟨_, htail⟩ := bitsFrom_append _ A (encodeNat clauses.length)
    ((clauses.map (encodeList encodeLiteral)).flatten ++ ([] : Bits)) hlists
  intro i hi
  have hfr := hframe (A + clauses.length + 1 + i)
    (by simp [uctCursorReg]; omega) (by simp [uctOuterReg]; omega)
    (by simp [uctDoneReg]; omega)
  have haddrEq : A + clauses.length + 1 + i = A + (encodeNat clauses.length).length + i := by
    simp only [encodeNat_length]
    omega
  rw [hfr, haddrEq]
  exact htail i hi

/-- The decode program equals its clause loop run from the state after the outer-count decode,
so the loop lemmas apply to the program's exit state. -/
lemma uniform_decode_state_low_regs_prog_eq (N n : ℕ) (σ σ2 : Store)
    (hb : σ uctBoundReg = N)
    (hσ2 : σ2 = (decodeNatProgram uctCursorReg uctOuterReg uctDoneReg N).eval
      ((Program.assign uctOuterReg (.const 0)).eval
        ((Program.assign uctDoneReg (.const 0)).eval σ)))
    (hout : σ2 uctOuterReg = n) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ =
    loopEval (decodeCNFStepAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg
      uctOuterReg uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg
      uctTmpReg uctBoundReg uctSeenReg) n σ2 := by
  have hb2 : ((Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval σ)) uctBoundReg = N := by
    simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ uctOuterReg 0 uctBoundReg (by decide),
      writeReg_diff _ uctDoneReg 0 uctBoundReg (by decide), hb]
  have hAtEq := decodeNatProgramAt_eq uctCursorReg uctOuterReg uctDoneReg uctBoundReg N _ hb2
  unfold decodeCNFProgramAtSeen
  rw [eval_seq, eval_seq, eval_seq, eval_forN, hAtEq, ← hσ2]
  simp only [Expr.eval, hout]

/-- Under the frame hypothesis, the specified scratch-register values in the
resulting store equal their initial values. -/
lemma uniform_decode_state_low_regs_cells (σ2 σ0 : Store)
    (hframe : ∀ r, r ≠ uctCursorReg → r ≠ uctOuterReg → r ≠ uctDoneReg → σ2 r = σ0 r)
    (N : ℕ) (hmax : σ0 uctMaxReg = 0) (hfresh : σ0 uctFreshReg = 0)
    (hcount : σ0 uctCountReg = 0) (hseen : σ0 uctSeenReg = 0) (hrem : σ0 uctRemainingReg = 0)
    (hb : σ0 uctBoundReg = N) (hpol : σ0 uctPolReg = 0) (hvar : σ0 uctVarReg = 0)
    (hlen : σ0 uctLengthReg = 0) :
    σ2 uctMaxReg = 0 ∧ σ2 uctFreshReg = 0 ∧ σ2 uctCountReg = 0 ∧ σ2 uctSeenReg = 0 ∧
      σ2 uctRemainingReg = 0 ∧ σ2 uctBoundReg = N ∧ σ2 uctPolReg = 0 ∧ σ2 uctVarReg = 0 ∧
      σ2 uctLengthReg = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe _ (by decide) (by decide) (by decide), hmax]
  · rw [hframe _ (by decide) (by decide) (by decide), hfresh]
  · rw [hframe _ (by decide) (by decide) (by decide), hcount]
  · rw [hframe _ (by decide) (by decide) (by decide), hseen]
  · rw [hframe _ (by decide) (by decide) (by decide), hrem]
  · rw [hframe _ (by decide) (by decide) (by decide), hb]
  · rw [hframe _ (by decide) (by decide) (by decide), hpol]
  · rw [hframe _ (by decide) (by decide) (by decide), hvar]
  · rw [hframe _ (by decide) (by decide) (by decide), hlen]

/-- The relocated CNF encoding, read as a clause list with empty tail, is readable from the
decode phase's initial store. -/
lemma uniform_decode_state_low_regs_lists (φ : CNF) :
    BitsFrom (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      (uniformAddrNat (encodeCNF φ).length)
      (encodeList (encodeList encodeLiteral)
        (φ.clauses.map (fun c => c.lits)) ++ ([] : Bits)) := by
  have henc : encodeList (encodeList encodeLiteral) (φ.clauses.map (fun c => c.lits)) ++
      ([] : Bits) = encodeCNF φ := by
    simp [← encodeCNF_eq_lists φ, List.append_nil]
  rw [henc]
  exact uniformControlInitProg_bitsFrom (encodeCNF φ)

/-- The decode phase's exit state: the scratch registers `pol`, `var`,
    `done`, `length`, and the seen flag all stay within the tight envelope's
    basic ingredients (Boolean, input bound, or the bound itself). -/
lemma uniform_decode_state_low_regs (φ : CNF) :
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      uctPolReg ≤ 1 ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      uctVarReg ≤ (encodeCNF φ).length ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      uctDoneReg ≤ 1 ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      uctLengthReg ≤ (encodeCNF φ).length ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore (encodeCNF φ)))))
      uctSeenReg ≤ 1 := by
  set bits := encodeCNF φ with hbitsdef
  set N := bits.length
  obtain ⟨hb0, hbase0, hcursor0, hpol0, hvar0, hdone0, houter0, hrem0, hmax0, hlen0,
    hfresh0, hcount0, htmp0, hseen0⟩ :=
    uniformControlInitProg_after_cursor bits
  have haddr : 25 ≤ uniformAddrNat N := uniformAddrNat_ge_25 N
  have hlists := uniform_decode_state_low_regs_lists φ
  have houterLe : (φ.clauses.map (fun c => c.lits)).length + 1 ≤ N := by
    simpa using encodeCNF_length_ge_clauseCount φ
  have houterBelow :
      uctCursorReg < uniformAddrNat N ∧ uctOuterReg < uniformAddrNat N ∧
        uctDoneReg < uniformAddrNat N := by
    simp [uctCursorReg, uctOuterReg, uctDoneReg]; omega
  obtain ⟨hcur0, houter0', hdone0', hframe0⟩ :=
    decode_cnf_outer_decode uctCursorReg uctOuterReg uctDoneReg N (uniformAddrNat N)
      (φ.clauses.map (fun c => c.lits)) ([] : Bits)
      (uniformControlInitProg.eval
        ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
          (uniformRelocateProg.eval (bitInputStore bits))))
      (by decide) (by decide) (by decide) houterBelow hcursor0 houterLe hlists
  set σ2 := (decodeNatProgram uctCursorReg uctOuterReg uctDoneReg N).eval
    ((Program.assign uctOuterReg (.const 0)).eval
      ((Program.assign uctDoneReg (.const 0)).eval
        (uniformControlInitProg.eval
          ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
            (uniformRelocateProg.eval (bitInputStore bits)))))) with hσ2def
  have hprogeq := uniform_decode_state_low_regs_prog_eq N
    (φ.clauses.map (fun c => c.lits)).length _ σ2 hb0 hσ2def houter0'
  have hcells := uniform_decode_state_low_regs_cells σ2 _ hframe0 N hmax0 hfresh0 hcount0 hseen0
    hrem0 hb0 hpol0 hvar0 hlen0
  have hloop := decodeCNFStepAtSeen_loop_low_regs N
    (φ.clauses.map (fun c => c.lits)) ([] : Bits)
    (uniformAddrNat N + (φ.clauses.map (fun c => c.lits)).length + 1)
    0 0 0 0 σ2
    houter0' hcur0
    hcells.1 hcells.2.1 hcells.2.2.1 hcells.2.2.2.1 hcells.2.2.2.2.1 hcells.2.2.2.2.2.1
    (by omega)
    (encodeCNF_scan_bounds φ)
    (by rw [hcells.2.2.2.2.2.2.1]; omega) (by rw [hcells.2.2.2.2.2.2.2.1]; omega)
    (by rw [hdone0'])
    (by rw [hcells.2.2.2.2.2.2.2.2]; omega)
    (uniform_decode_state_low_regs_tail_bits _ σ2 _ _ hlists haddr hframe0)
  have hseen := (decodeCNFProgramAtSeen_uct_encodeCNF_zero_seed φ).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hprogeq]; exact hloop.1
  · rw [hprogeq]; exact hloop.2.1
  · rw [hprogeq]; exact hloop.2.2.1
  · rw [hprogeq]; exact hloop.2.2.2
  · rw [hseen]; exact cnfSeenStat_le_one 0 _ (by decide)

lemma uniformEmitAuxInitProg_eval (σ : Store) :
    (uniformEmitAuxInitProg.eval σ) uctPosPolReg = 0 ∧
    (uniformEmitAuxInitProg.eval σ) uctNegPolReg = 1 := by
  constructor
  · simp [uniformEmitAuxInitProg, eval_seq, eval_assign, Expr.eval,
      writeReg_diff _ uctNegPolReg 1 uctPosPolReg (by decide), writeReg_same]
  · simp [uniformEmitAuxInitProg, eval_seq, eval_assign, Expr.eval, writeReg_same]

lemma uniformEmitResetProg_frame (σ : Store) {r : ℕ}
    (hl : r ≠ uctLengthReg) (hd : r ≠ uctDoneReg) :
    uniformEmitResetProg.eval σ r = σ r :=
  emitClauseResetProg_frame uctLengthReg uctDoneReg σ hl hd

lemma uniform_layout_inputAbove (N : ℕ) :
    uniformMNat N + uctTmpJ < uniformAddrNat N := by
  simp [uctTmpJ, uniformMNat_add_two_lt_addr N]

lemma uniform_layout_start_lt_M (N : ℕ) :
    uniformStartNat < uniformMNat N + uctCurJ := by
  simp [uctCurJ, uniformMNat, uniformStartNat, uniformSlackNat]

lemma uniform_clauseEmitSafety :
    ClauseEmitSafety uniformStartNat uctCursorReg uctLengthReg uctPolReg
      uctVarReg uctDoneReg uctOuterReg uctFreshReg uctPosPolReg uctNegPolReg := by
  simp [uniformStartNat, uctCursorReg, uctLengthReg, uctPolReg, uctVarReg,
    uctDoneReg, uctOuterReg, uctFreshReg, uctPosPolReg, uctNegPolReg,
    relocateControlGap]
  exact
    { cursor_below := by decide
      length_below := by decide
      pol_below := by decide
      var_below := by decide
      done_below := by decide
      outer_below := by decide
      fresh_below := by decide
      pos_below := by decide
      neg_below := by decide
      cursor_nonzero := by decide
      length_nonzero := by decide
      pol_nonzero := by decide
      var_nonzero := by decide
      done_nonzero := by decide
      outer_nonzero := by decide
      fresh_nonzero := by decide
      pos_nonzero := by decide
      neg_nonzero := by decide
      register_nodup := by decide }

lemma uniform_longClauseRegisterSafety :
    LongClauseRegisterSafety uniformStartNat uctCursorReg uctLengthReg uctPolReg
      uctVarReg uctDoneReg uctOuterReg uctNegPolReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg uctCarryValReg
      uctPosPolReg uctFreshReg := by
  simp [uniformStartNat, uctCursorReg, uctLengthReg, uctPolReg, uctVarReg,
    uctDoneReg, uctOuterReg, uctNegPolReg, uctRemainingReg, uctPol2Reg,
    uctVar2Reg, uctPol3Reg, uctVar3Reg, uctCarryPolReg, uctCarryValReg,
    uctPosPolReg, uctFreshReg, relocateControlGap]
  refine { register_nodup := ?_, below := ?_, nonzero := ?_ }
  · decide
  · intro r hr
    simp [longClauseRegisterList] at hr
    omega
  · intro r hr
    simp [longClauseRegisterList] at hr
    omega

lemma uniformAddrNat_gt_length_done (N : ℕ) :
    uctLengthReg < uniformAddrNat N ∧ uctDoneReg < uniformAddrNat N := by
  have h := uniformAddrNat_ge_25 N
  simp [uctLengthReg, uctDoneReg]
  omega

export NPComplete.SAT (encodeLiteral_length_eq)

lemma encodeThreeClause_length_le (c : ThreeClause) {n : ℕ}
    (h1 : c.l1.var < n) (h2 : c.l2.var < n) (h3 : c.l3.var < n) :
    (encodeThreeClause c).length ≤ 3 * (n + 1) := by
  simp [encodeThreeClause, List.length_append, encodeLiteral_length_eq]
  omega

lemma encodeThreeClausesPayload_length_le (cs : List ThreeClause) (n : ℕ)
    (h : ∀ c ∈ cs, ∀ l ∈ c.literals, l.var < n) :
    (encodeThreeClausesPayload cs).length ≤ 3 * cs.length * (n + 1) := by
  induction cs with
  | nil => simp [encodeThreeClausesPayload]
  | cons c rest ih =>
      have hc := encodeThreeClause_length_le c
        (h c (by simp) c.l1 (by simp [ThreeClause.literals]))
        (h c (by simp) c.l2 (by simp [ThreeClause.literals]))
        (h c (by simp) c.l3 (by simp [ThreeClause.literals]))
      have hrest := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
      simp only [encodeThreeClausesPayload, List.map_cons, List.flatten_cons,
        List.length_append, List.length_cons] at hrest ⊢
      have hexp : 3 * (rest.length + 1) * (n + 1) =
          3 * rest.length * (n + 1) + 3 * (n + 1) := by ring
      omega

lemma encodeCNF_sum_lits_succ_le (φ : CNF) :
    (φ.clauses.map (fun c => c.lits.length + 1)).sum + φ.clauses.length + 1 ≤
      (encodeCNF φ).length := by
  have hsum : (φ.clauses.map (fun c => c.lits.length + 1)).sum ≤
      (φ.clauses.map (fun c => (encodeClause c).length)).sum := by
    refine List.sum_le_sum ?_
    intro c _
    exact encodeList_length_ge encodeLiteral c.lits
  have heq : (φ.clauses.map (fun c => (encodeClause c).length)).sum +
      φ.clauses.length + 1 = (encodeCNF φ).length := by
    simp [encodeCNF, encodeList, encodeNat_length, List.length_flatten,
      Function.comp_def]
    ac_rfl
  omega

lemma cnfVarBound_le_encodeCNF (φ : CNF) :
    cnfVarBound φ ≤ (encodeCNF φ).length := by
  have h := encodeCNF_scan_bounds φ
  have haux : ∀ cs,
      (∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ (encodeCNF φ).length) →
        clausesVarBound cs ≤ (encodeCNF φ).length := by
    intro cs
    induction cs with
    | nil => intro _; simp [clausesVarBound]
    | cons c rest ih =>
        intro hcs
        simp only [clausesVarBound, clauseVarBound]
        have hlits := litsVarBound_le_of_forall
          (ls := c.lits) (B := (encodeCNF φ).length) (fun l hl =>
            Nat.lt_of_succ_le (hcs c (by simp) l hl))
        have hrest := ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
        exact max_le hlits hrest
  apply haux φ.clauses
  intro c hc l hl
  exact encodeCNF_literal_var_bound φ c hc l hl

lemma map_clause_lits_succ_two_sum (cs : List Clause) :
    (cs.map (fun c => c.lits.length + 2)).sum =
      (cs.map (fun c => c.lits.length + 1)).sum + cs.length := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
      simp [List.sum_cons, ih]; omega

lemma toThreeCNF_count_le_encodeCNF (φ : CNF) :
    (toThreeCNF φ).clauses.length + 1 ≤ (encodeCNF φ).length := by
  have hlen := toThreeCNF_clauses_length_le φ
  have hsum := encodeCNF_sum_lits_succ_le φ
  have h := map_clause_lits_succ_two_sum φ.clauses
  omega

lemma toThreeCNF_numVars_le_two_mul_encodeCNF (φ : CNF) :
    (toThreeCNF φ).numVars ≤ 2 * (encodeCNF φ).length := by
  have hnv := toThreeCNF_numVars_le φ
  have hb := cnfVarBound_le_encodeCNF φ
  have hsum := encodeCNF_sum_lits_succ_le φ
  omega

lemma encodeThreeCNF_toThreeCNF_length_le (φ : CNF) :
    (encodeThreeCNF (toThreeCNF φ)).length ≤
      (toThreeCNF φ).numVars + (toThreeCNF φ).clauses.length + 2 +
        3 * (toThreeCNF φ).clauses.length * ((toThreeCNF φ).numVars + 1) := by
  have hpay := encodeThreeClausesPayload_length_le (toThreeCNF φ).clauses
    (toThreeCNF φ).numVars (toThreeCNF_bounded φ)
  simp [encodeThreeCNF, encodeList, encodeThreeClausesPayload, List.length_append,
    encodeNat_length, List.length_flatten, List.map_map] at hpay ⊢
  omega

lemma expand_succ_cube (N : ℕ) :
    (N + 1) * (N + 1) * (N + 1) = N * N * N + 3 * N * N + 3 * N + 1 := by
  ring

lemma poly_quad_le_cube_slack (N : ℕ) :
    6 * N * N + 6 * N + 2 ≤ (N + 1) * (N + 1) * (N + 1) + 14 := by
  rw [expand_succ_cube]
  match N with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | n + 4 =>
      nlinarith

lemma encodeCNF_split (φ : CNF) :
    encodeCNF φ =
      encodeNat φ.clauses.length ++ (φ.clauses.map encodeClause).flatten := by
  simp [encodeCNF, encodeList]

lemma bitsFrom_encodeCNF_flatten (φ : CNF) (σ : Store) (addr : ℕ)
    (h : BitsFrom σ addr (encodeCNF φ)) :
    BitsFrom σ (addr + φ.clauses.length + 1)
      (φ.clauses.map encodeClause).flatten := by
  have hsplit := encodeCNF_split φ
  have hbits : BitsFrom σ addr
      (encodeNat φ.clauses.length ++ (φ.clauses.map encodeClause).flatten) := by
    simpa [hsplit] using h
  obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeNat φ.clauses.length)
    (φ.clauses.map encodeClause).flatten hbits
  intro i hi
  have hi' : addr + φ.clauses.length + 1 + i =
      addr + (encodeNat φ.clauses.length).length + i := by
    simp [encodeNat_length]; omega
  simpa [hi'] using htail i hi

lemma uniform_flatten_addr_inputAbove (N n : ℕ) :
    uniformMNat N + uctTmpJ < uniformAddrNat N + n + 1 := by
  have h := uniform_layout_inputAbove N
  omega

lemma uniformStartNat_le_uniformAddrNat_add_n_add_one (N n : ℕ) :
    uniformStartNat ≤ uniformAddrNat N + n + 1 := by
  have h := uniformAddrNat_ge_start N
  omega

lemma uniform_flatten_addr_gt_length_done (N n : ℕ) :
    uctLengthReg < uniformAddrNat N + n + 1 ∧
      uctDoneReg < uniformAddrNat N + n + 1 := by
  have h := uniformAddrNat_gt_length_done N
  omega

lemma uniform_capacity_of_encodeCNF (φ : CNF) :
    uniformStartNat + (encodeThreeCNF (toThreeCNF φ)).length + 2 <
      uniformMNat (encodeCNF φ).length + uctCurJ := by
  set N := (encodeCNF φ).length
  have henc := encodeThreeCNF_toThreeCNF_length_le φ
  have hc : (toThreeCNF φ).clauses.length ≤ N :=
    Nat.le_of_succ_le (toThreeCNF_count_le_encodeCNF φ)
  have hn := toThreeCNF_numVars_le_two_mul_encodeCNF φ
  have hprod :
      3 * ((toThreeCNF φ).clauses.length * ((toThreeCNF φ).numVars + 1)) ≤
        3 * (N * (2 * N + 1)) :=
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul hc (Nat.add_le_add_right hn 1))
  have htot : (encodeThreeCNF (toThreeCNF φ)).length ≤
      6 * N * N + 6 * N + 2 := by
    have hr : 2 * N + N + 2 + 3 * (N * (2 * N + 1)) = 6 * N * N + 6 * N + 2 := by
      ring
    have henc' := henc
    simp only [Nat.mul_assoc] at henc' hprod
    omega
  have hslack := poly_quad_le_cube_slack N
  simp [uctCurJ, uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap]
  nlinarith

end NPComplete.CookLevin

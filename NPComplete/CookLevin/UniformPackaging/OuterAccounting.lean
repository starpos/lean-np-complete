module

public import NPComplete.CookLevin.UniformPackaging.DispatchAssembly

/-!
# Outer-loop output accounting

The outer loop's quantitative bound depends on its emitted prefix, fresh-variable
base, and input cursor at each iteration, not just at termination. This module
expresses those quantities in terms of consumed clauses and proves the tight
accounting facts needed by the loop invariant.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.SAT (encodeLiteral encodeThreeCNF)
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitCostRAM
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
open Polynomial

/-! ## Outer output-size accounting

The outer clause loop is driven by the semantic relation `CNFEmitRel`, which
already tracks the emitted prefix, the fresh-variable base, and the input
cursor.  The accounting template below records how these three quantities are
determined by the list of already-consumed clauses, so the quantitative facts
(prefix length below the writer wall, fresh base below `numVars`, input cursor
inside the relocated window, hence every named control cell inside the tight
envelope) hold at each outer-loop state instead of being recovered from the
terminal `CNFEmitDone`. -/

lemma uniformMNat_cur_j_le_tight_envelope (N : ℕ) :
    uniformMNat N + uctCurJ ≤ uniformEmitTightEnvelope N := by
  simp only [uniformEmitTightEnvelope]
  omega

lemma toThreeCNF_numVars_le_tight_envelope (φ : CNF) :
    (toThreeCNF φ).numVars ≤ uniformEmitTightEnvelope (encodeCNF φ).length := by
  have h := toThreeCNF_numVars_le_two_mul_encodeCNF φ
  have h1 := uniformSlackNat_ge_succ (encodeCNF φ).length
  simp only [uniformEmitTightEnvelope, uniformMNat, uniformSlackNat] at *
  omega

/-- Output-size accounting, prefix form: the writer cursor value stays strictly
below the writer wall `M + curJ`, hence inside the tight envelope. -/
lemma cnfEmitRel_pref_length_lt_wall (N : ℕ) (clauses : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      clauses tail pref addr σ) :
    uniformStartNat + pref.length < uniformMNat N + uctCurJ := by
  have hc := hrel.capacity
  omega

lemma cnfEmitRel_pref_length_le_tight_envelope (N : ℕ) (clauses : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat N) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg N N base
      clauses tail pref addr σ) :
    uniformStartNat + pref.length ≤ uniformEmitTightEnvelope N := by
  have h1 := cnfEmitRel_pref_length_lt_wall N clauses tail pref addr base σ hrel
  have h2 := uniformMNat_cur_j_le_tight_envelope N
  omega

lemma clausesToThree_single_fresh (base : ℕ) (c : Clause) :
    (clausesToThree base [c]).2 = (clauseToThree base c.lits).2 := by
  simp [clausesToThree_cons, clausesToThree_nil]

lemma clausesToThree_single_payload (base : ℕ) (c : Clause) :
    encodeThreeClausesPayload (clausesToThree base [c]).1 =
      encodeThreeClausesPayload (clauseToThree base c.lits).1 := by
  simp [clausesToThree_cons, clausesToThree_nil]

lemma clausesToThree_fresh_append (base : ℕ) (l₁ l₂ : List Clause) :
    (clausesToThree base (l₁ ++ l₂)).2 =
      (clausesToThree (clausesToThree base l₁).2 l₂).2 := by
  induction l₁ generalizing base with
  | nil => simp [clausesToThree_nil]
  | cons d rest ih =>
      rw [List.cons_append, clausesToThree_cons, clausesToThree_cons, ih]

lemma clausesToThree_payload_cons' (base : ℕ) (c : Clause) (cs : List Clause) :
    encodeThreeClausesPayload ((clauseToThree base c.lits).1 ++
        (clausesToThree (clauseToThree base c.lits).2 cs).1) =
      encodeThreeClausesPayload (clauseToThree base c.lits).1 ++
        encodeThreeClausesPayload (clausesToThree (clauseToThree base c.lits).2 cs).1 :=
  clausesToThree_payload_cons base c cs

lemma clausesToThree_payload_append (base : ℕ) (l₁ l₂ : List Clause) :
    encodeThreeClausesPayload (clausesToThree base (l₁ ++ l₂)).1 =
      encodeThreeClausesPayload (clausesToThree base l₁).1 ++
        encodeThreeClausesPayload (clausesToThree (clausesToThree base l₁).2 l₂).1 := by
  induction l₁ generalizing base with
  | nil => simp [clausesToThree_nil, encodeThreeClausesPayload]
  | cons d rest ih =>
      simp only [List.cons_append, clausesToThree_cons]
      rw [clausesToThree_payload_cons', clausesToThree_payload_cons',
        ih (clauseToThree base d.lits).2, List.append_assoc]

lemma clausesToThree_fresh_mono (base : ℕ) (l₁ l₂ : List Clause) :
    (clausesToThree base l₁).2 ≤ (clausesToThree base (l₁ ++ l₂)).2 := by
  rw [clausesToThree_fresh_append]
  exact clausesToThree_base_le _ _

/-- How the fresh base, the emitted prefix, and the input cursor of an
outer-loop state are determined by the list of already-consumed clauses.
`base₀` is the initial fresh base, `header` the header emitted before the
loop, and `addr₀` the input position when the loop starts. -/
structure OuterEmitAccounting (base₀ addr₀ : ℕ) (header : Bits)
    (consumed : List Clause) (base : ℕ) (pref : Bits) (addr : ℕ) : Prop where
  fresh_eq : base = (clausesToThree base₀ consumed).2
  pref_eq : pref = header ++ encodeThreeClausesPayload (clausesToThree base₀ consumed).1
  addr_eq : addr = addr₀ + (consumed.map encodeClause).flatten.length

/-- The semantic clause step matches the accounting template: consuming one
more clause exactly updates the fresh base, the prefix, and the input cursor
the way `OuterEmitAccounting` prescribes. -/
lemma OuterEmitAccounting.step (base₀ addr₀ : ℕ) (header : Bits)
    (consumed : List Clause) (c : Clause) (base : ℕ) (pref : Bits) (addr : ℕ)
    (hacc : OuterEmitAccounting base₀ addr₀ header consumed base pref addr) :
    OuterEmitAccounting base₀ addr₀ header (consumed ++ [c])
      (clauseToThree base c.lits).2
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) := by
  have hfresh : (clausesToThree base₀ (consumed ++ [c])).2 =
      (clauseToThree base c.lits).2 := by
    rw [clausesToThree_fresh_append, clausesToThree_single_fresh, hacc.fresh_eq]
  have hpayload : encodeThreeClausesPayload (clausesToThree base₀ (consumed ++ [c])).1 =
      encodeThreeClausesPayload (clausesToThree base₀ consumed).1 ++
        encodeThreeClausesPayload (clauseToThree base c.lits).1 := by
    rw [clausesToThree_payload_append, clausesToThree_single_payload, hacc.fresh_eq]
  have haddr : ((consumed ++ [c]).map encodeClause).flatten.length =
      (consumed.map encodeClause).flatten.length +
        (encodeList encodeLiteral c.lits).length := by
    simp [encodeClause]
  refine ⟨hfresh.symm, ?_, ?_⟩
  · rw [hpayload, ← List.append_assoc, ← hacc.pref_eq]
  · rw [haddr, ← Nat.add_assoc, ← hacc.addr_eq]

/-- The producer's state before the first iteration satisfies the accounting
template: nothing consumed, base at `cnfVarBound`, prefix exactly the header,
cursor at the input start. -/
lemma OuterEmitAccounting.producer_init (φ : CNF) :
    OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      [] (cnfVarBound φ)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [clausesToThree_nil]
  · simp [clausesToThree_nil, encodeThreeClausesPayload]
  · simp

/-- Fresh/base growth: a partially consumed clause list never pushes the fresh
base past the final `numVars`. -/
lemma OuterEmitAccounting.fresh_le_numVars (φ : CNF) (addr₀ : ℕ) (header : Bits)
    (consumed rest : List Clause) (base : ℕ) (pref : Bits) (addr : ℕ)
    (hsplit : consumed ++ rest = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ) addr₀ header consumed base pref addr) :
    base ≤ (toThreeCNF φ).numVars := by
  have hmono := clausesToThree_fresh_mono (cnfVarBound φ) consumed rest
  rw [hsplit] at hmono
  rw [hacc.fresh_eq]
  simpa [toThreeCNF] using hmono

/-- Window shift: the input cursor of a partially consumed producer never
passes the relocated input window end. -/
lemma OuterEmitAccounting.addr_le_window (φ : CNF) (addr₀ : ℕ) (header : Bits)
    (consumed rest : List Clause) (base : ℕ) (pref : Bits) (addr : ℕ)
    (hsplit : consumed ++ rest = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ) addr₀ header consumed base pref addr)
    (haddr₀ : addr₀ = uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1) :
    addr ≤ uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
  have h1 := uniform_producer_input_end_window φ
  have h2 : (consumed.map encodeClause).flatten.length ≤
      (φ.clauses.map encodeClause).flatten.length := by
    rw [← hsplit]
    simp only [List.map_append, List.flatten_append, List.length_append]
    omega
  rw [hacc.addr_eq, haddr₀]
  omega

lemma OuterEmitAccounting.clause_window_end
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (base : ℕ) (pref : Bits) (addr : ℕ)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr) :
    addr + (encodeList encodeLiteral c.lits).length +
      ((cs.map encodeClause).flatten ++ ([] : Bits)).length =
      uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
  have hfull :
      (consumed.map encodeClause).flatten ++ (encodeClause c ++
        (cs.map encodeClause).flatten) = (φ.clauses.map encodeClause).flatten := by
    rw [← hsplit]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
  have hlenfull := congrArg List.length hfull
  simp only [List.length_append] at hlenfull
  rw [hacc.addr_eq]
  simp only [List.length_append, List.length_nil]
  simp only [encodeCNF_split, List.length_append, encodeNat_length] at hlenfull ⊢
  simp only [encodeClause, NPComplete.BitEncoding.encodeList,
    List.length_append, encodeNat_length] at hlenfull ⊢
  omega

lemma OuterEmitAccounting.clause_window
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (base : ℕ) (pref : Bits) (addr : ℕ)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr) :
    SplitTailEmitWindow
      (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length)
      (uniformEmitLongValueEnvelope (encodeCNF φ).length) base c.lits
      ((cs.map encodeClause).flatten ++ ([] : Bits))
      (addr + c.lits.length + 1) := by
  have hc : c ∈ φ.clauses := by
    rw [← hsplit]
    simp
  have hcl : c.lits ∈ φ.clauses.map (fun d : Clause => d.lits) := by
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  have hlen := (encodeCNF_scan_bounds φ c.lits hcl).1
  have hbase0 := OuterEmitAccounting.fresh_le_numVars φ
    (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed (c :: cs) base pref addr hsplit hacc
  have hnum := toThreeCNF_numVars_le_tight_envelope φ
  have hbase : base + c.lits.length ≤
      uniformEmitLongValueEnvelope (encodeCNF φ).length := by
    simp only [uniformEmitLongValueEnvelope] at ⊢
    omega
  have hfull :
      (consumed.map encodeClause).flatten ++ (encodeClause c ++
        (cs.map encodeClause).flatten) = (φ.clauses.map encodeClause).flatten := by
    rw [← hsplit]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
  have hlenfull := congrArg List.length hfull
  simp only [List.length_append] at hlenfull
  have haddr : addr + (encodeList encodeLiteral c.lits).length +
      ((cs.map encodeClause).flatten ++ ([] : Bits)).length ≤
      uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length := by
    rw [hacc.addr_eq]
    simp only [List.length_append, List.length_nil]
    simp only [encodeCNF_split, List.length_append, encodeNat_length] at hlenfull ⊢
    simp only [encodeClause, NPComplete.BitEncoding.encodeList,
      List.length_append, encodeNat_length] at hlenfull ⊢
    omega
  exact splitTailEmitWindow_shift_after_clause _ _ _ c _ addr haddr (by omega)

lemma OuterEmitAccounting.clause_input_cells_le_one
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (base : ℕ) (pref : Bits) (addr : ℕ) (σ : Store)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base (c :: cs) ([] : Bits) pref addr σ)
    (hzero : CellsZeroFrom
      (uniformAddrNat (encodeCNF φ).length + (encodeCNF φ).length) σ) :
    ∀ i, addr + c.lits.length + 1 ≤ i →
      i < addr + c.lits.length + 1 + 2 + 2 * (encodeCNF φ).length →
      (decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ) i ≤ 1 := by
  let N := (encodeCNF φ).length
  let inputEnd := uniformAddrNat N + N
  let shift := addr + c.lits.length + 1
  let suffix : Bits := (cs.map encodeClause).flatten ++ []
  let bits : Bits := (c.lits.map encodeLiteral).flatten ++ suffix
  have hhead := cnfEmitRel_head_input
    (uniformMNat N) uctCurJ uctTmpJ uniformStartNat uctCursorReg uctPolReg uctVarReg
    uctDoneReg uctLengthReg uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg
    uctPosPolReg uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
    N N base c cs ([] : Bits) pref addr σ hrel
  have hhead' : BitsFrom σ addr (encodeNat c.lits.length ++ bits) := by
    simpa [bits, suffix, encodeList, encodeClause, List.append_assoc] using hhead
  have hbits : BitsFrom σ shift bits := by
    obtain ⟨_, ht⟩ := bitsFrom_append σ addr (encodeNat c.lits.length) bits hhead'
    have heq : addr + (encodeNat c.lits.length).length = shift := by
      simp [shift, encodeNat_length]
      omega
    rw [heq] at ht
    exact ht
  have hend := OuterEmitAccounting.clause_window_end φ consumed c cs base pref addr hsplit hacc
  have hlen : shift + bits.length = inputEnd := by
    simp [shift, bits, suffix, inputEnd, N, encodeList,
      List.length_append, encodeNat_length] at hend ⊢
    omega
  have hlow : ∀ r ∈ uniformEmitScratchRegs, r < inputEnd := by
    intro r hr
    have hr20 := uniformEmitScratchRegs_mem_le r hr
    have h25 := uniformAddrNat_ge_25 N
    simp only [inputEnd]
    omega
  have hzR : CellsZeroFrom inputEnd (uniformEmitScratchResetProg.eval σ) := by
    exact cellsZeroFrom_uniformEmitScratchResetProg σ hlow
      (by have h25 := uniformAddrNat_ge_25 N; simp [uctPosPolReg, inputEnd]; omega)
      (by have h25 := uniformAddrNat_ge_25 N; simp [uctNegPolReg, inputEnd]; omega)
      (by simpa [inputEnd] using hzero)
  have hshift : 25 ≤ shift := by
    have hs0 : uniformStartNat ≤ addr := hrel.start_at_input
    simp only [shift, uniformStartNat, relocateControlGap] at hs0 ⊢
    omega
  have hbitsR : BitsFrom (uniformEmitScratchResetProg.eval σ) shift bits := by
    apply bitsFrom_of_eq_on (hb := hbits)
    intro j hj
    apply uniformEmitScratchResetProg_frame σ
    · intro hmem
      have hr20 := uniformEmitScratchRegs_mem_le (shift + j) hmem
      omega
    · have : shift + j ≠ uctPosPolReg := by norm_num [uctPosPolReg]; omega
      exact this
    · have : shift + j ≠ uctNegPolReg := by norm_num [uctNegPolReg]; omega
      exact this
  have hzD : CellsZeroFrom inputEnd
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) := by
    exact cellsZeroFrom_decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg
      (uniformEmitScratchResetProg.eval σ)
      (by have h25 := uniformAddrNat_ge_25 N; norm_num [uctCursorReg, inputEnd]; omega)
      (by have h25 := uniformAddrNat_ge_25 N; norm_num [uctLengthReg, inputEnd]; omega)
      (by have h25 := uniformAddrNat_ge_25 N; norm_num [uctDoneReg, inputEnd]; omega)
      hzR
  have hbitsD : BitsFrom
      ((decodeNatProgramAt uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg).eval
        (uniformEmitScratchResetProg.eval σ)) shift bits := by
    apply bitsFrom_of_eq_on (hb := hbitsR)
    intro j hj
    have h1 : shift + j ≠ uctCursorReg := by norm_num [uctCursorReg]; omega
    have h2 : shift + j ≠ uctLengthReg := by norm_num [uctLengthReg]; omega
    have h3 : shift + j ≠ uctDoneReg := by norm_num [uctDoneReg]; omega
    exact decodeNatProgramAt_frame uctCursorReg uctLengthReg uctDoneReg uctSavedBoundReg
      (shift + j) (uniformEmitScratchResetProg.eval σ) h1 h2 h3
  intro i hi hupper
  exact cells_le_one_of_window_zero _ shift inputEnd bits hbitsD hlen hzD i (by omega)

lemma cnfEmitRel_uniform_values_le_tight_envelope (φ : CNF)
    (consumed rest : List Clause) (hsplit : consumed ++ rest = φ.clauses)
    (tail pref : Bits) (addr base : ℕ) (σ : Store)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ
      uniformStartNat uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg
      uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg
      uctNegPolReg uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base rest tail pref addr σ)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr) :
    σ uctCursorReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctOuterReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctFreshReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctLengthReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctDoneReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctPosPolReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ uctNegPolReg ≤ uniformEmitTightEnvelope (encodeCNF φ).length ∧
      σ (uniformMNat (encodeCNF φ).length + uctCurJ) ≤
        uniformEmitTightEnvelope (encodeCNF φ).length := by
  have hbase := OuterEmitAccounting.fresh_le_numVars φ _
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed rest base pref addr hsplit hacc
  have hnum := toThreeCNF_numVars_le_tight_envelope φ
  have haddr := OuterEmitAccounting.addr_le_window φ _
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed rest base pref addr hsplit hacc rfl
  have hend := uniform_split_tail_input_end_le_tight (encodeCNF φ).length
  have hcnt := encodeCNF_length_ge_clauseCount φ
  have hlen : consumed.length + rest.length = φ.clauses.length := by
    rw [← hsplit]
    simp [List.length_append]
  have hwall := uniformMNat_cur_j_le_tight_envelope (encodeCNF φ).length
  have hpref := cnfEmitRel_pref_length_le_tight_envelope (encodeCNF φ).length rest
    tail pref addr base σ hrel
  exact cnfEmitRel_named_values_le hrel _ (by omega) (by omega) (by omega)
    hpref

/-- Under the relation, accounting, store-bound, and frame hypotheses, one
outer-loop body step preserves the tight store-value bound. -/
lemma uniformEmitIterBody_tight_of_outer_frames
    (φ : CNF) (consumed : List Clause) (c : Clause) (cs : List Clause)
    (tail pref : Bits) (addr base : ℕ) (σ τ : Store)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr)
    (hrel : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length base (c :: cs) tail pref addr σ)
    (hb : σ uctSavedBoundReg = (encodeCNF φ).length)
    (hσ : StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) σ)
    (hK1 : 1 ≤ uniformEmitTightEnvelope (encodeCNF φ).length)
    (hτ : uniformEmitIterBody.eval σ = τ)
    (hrelτ : CNFEmitRel (uniformMNat (encodeCNF φ).length) uctCurJ uctTmpJ uniformStartNat
      uctCursorReg uctPolReg uctVarReg uctDoneReg uctLengthReg uctRemainingReg
      uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctPosPolReg uctNegPolReg
      uctCarryPolReg uctCarryValReg uctFreshReg uctOuterReg
      (encodeCNF φ).length (encodeCNF φ).length
      (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ)
    (hafter : ∀ r,
      τ (uniformMNat (encodeCNF φ).length + uctCurJ) ≤ r →
      r ≠ uniformMNat (encodeCNF φ).length + uctCurJ →
      r ≠ uniformMNat (encodeCNF φ).length + uctTmpJ → τ r = σ r) :
    StoreValuesLe (uniformEmitTightEnvelope (encodeCNF φ).length) τ := by
  let N := (encodeCNF φ).length
  let K := uniformEmitTightEnvelope N
  have hsplit' : (consumed ++ [c]) ++ cs = φ.clauses := by
    simpa [List.append_assoc] using hsplit
  have hacc' := OuterEmitAccounting.step
    (cnfVarBound φ) (uniformAddrNat N + φ.clauses.length + 1)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed c base pref addr hacc
  have hvals := cnfEmitRel_uniform_values_le_tight_envelope φ
    (consumed ++ [c]) cs hsplit' tail
    (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
    (addr + (encodeList encodeLiteral c.lits).length)
    (clauseToThree base c.lits).2 τ hrelτ hacc'
  have hframeLow : ∀ r, r < uniformStartNat →
      ¬ LongClauseLowWriteSet uctCursorReg uctPolReg uctVarReg uctDoneReg
        uctRemainingReg uctPol2Reg uctVar2Reg uctPol3Reg uctVar3Reg uctCarryPolReg
        uctCarryValReg uctPosPolReg uctFreshReg uctLengthReg uctOuterReg uctNegPolReg r →
      τ r = σ r := by
    intro r hr hnot
    rw [← hτ]
    exact uniformEmitIterBody_low_frame_of_rel N c cs tail pref addr base σ hrel hb r hr hnot
  have hbase0 := OuterEmitAccounting.fresh_le_numVars φ
    (uniformAddrNat N + φ.clauses.length + 1)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed (c :: cs) base pref addr hsplit hacc
  have hnum := toThreeCNF_numVars_le_tight_envelope φ
  have hclause := hrel.clause_bound c (by simp)
  have hvars := toThreeCNF_numVars_le_two_mul_encodeCNF φ
  have hbase : base + c.lits.length ≤ K := by
    have hvars' : (toThreeCNF φ).numVars ≤ 2 * N := by simpa [N] using hvars
    have hclause' : c.lits.length ≤ N := by omega
    simp only [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
    nlinarith
  have hNK : N ≤ K := by
    simp only [K, uniformEmitTightEnvelope, uniformMNat, uniformStartNat, uniformSlackNat,
      relocateControlGap]
    omega
  have htmp : τ (uniformMNat N + uctTmpJ) ≤ K := by
    rw [← hτ]
    exact uniformEmitIterBody_tmp_bound_of_rel N K c cs tail pref addr base σ hrel hb hσ
      hbase hNK
  exact uniformEmitIterBody_store_tight_of_frame N K cs tail
    (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
    (addr + (encodeList encodeLiteral c.lits).length)
    (clauseToThree base c.lits).2 σ τ hτ hrelτ hK1 hσ
     hvals.1 hvals.2.1 hvals.2.2.1 hvals.2.2.2.2.2.2.2 hframeLow htmp hafter

lemma uniform_emit_outer_writer_room (φ : CNF) (consumed : List Clause)
    (c : Clause) (cs : List Clause) (base : ℕ) (pref : Bits) (addr : ℕ)
    (hsplit : consumed ++ c :: cs = φ.clauses)
    (hacc : OuterEmitAccounting (cnfVarBound φ)
      (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
      (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
      consumed base pref addr) :
    uniformStartNat + pref.length + (encodeCNF φ).length + (encodeCNF φ).length + base + 6 <
      uniformMNat (encodeCNF φ).length + uctCurJ := by
  have hbase := OuterEmitAccounting.fresh_le_numVars φ
    (uniformAddrNat (encodeCNF φ).length + φ.clauses.length + 1)
    (encodeNat (toThreeCNF φ).numVars ++ encodeNat (toThreeCNF φ).clauses.length)
    consumed (c :: cs) base pref addr hsplit hacc
  have hpref : pref.length ≤ (encodeThreeCNF (toThreeCNF φ)).length := by
    rw [hacc.pref_eq]
    have hp := clausesToThree_payload_append (cnfVarBound φ) consumed (c :: cs)
    rw [hsplit] at hp
    have hl := congrArg List.length hp
    simp only [encodeThreeCNF_eq_header_payload, clausesToThree_toThreeCNF,
      List.length_append] at hl ⊢
    omega
  have hvars := toThreeCNF_numVars_le_two_mul_encodeCNF φ
  have hcount := toThreeCNF_count_le_encodeCNF φ
  have hout := encodeThreeCNF_toThreeCNF_length_le φ
  have hslack := poly_quad_le_cube_slack (encodeCNF φ).length
  simp only [uniformMNat, uniformStartNat, uniformSlackNat, relocateControlGap] at *
  nlinarith

end NPComplete.CookLevin

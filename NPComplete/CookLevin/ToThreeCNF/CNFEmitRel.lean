module

public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitShapeFrame

/-!
# Outer CNF emission relation

The outer induction should start and finish at clause boundaries rather than
rely on parser intermediate phases. `CNFEmitRel` records the unconsumed encoded
input, emitted prefix, register layout, and capacity needed to lift a
single-clause result through the outer loop.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
  (BitsFrom bitsFrom_append bitsFrom_writeReg bitsFrom_of_eq_on BitsAt bitsAt_of_frame finalizeOutputProg FinalizeRegsOk ctlCell ctlCell_eval)
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same cost_seq
    cost_ifNZ cost_forN eval_ifNZ eval_forN loopEval loopEval_succ
    loopCost loopCost_le_of_body_le)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)
/-! ## Outer CNF emission relation

The relation below records the state at a clause boundary.  The input window
contains exactly the unconsumed encoded clauses, while the writer prefix
contains exactly the already emitted three-CNF clauses.  The endpoint theorem
for one clause can therefore be lifted without exposing the internal parser
phases to the outer induction.
-/

structure CNFEmitRel
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (clauses : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store) : Prop where
  input : BitsFrom σ addr ((clauses.map encodeClause).flatten ++ tail)
  cursor : σ cursorReg = addr
  outer : σ outerReg = clauses.length
  fresh : σ freshReg = base
  length_zero : σ lengthReg = 0
  done_zero : σ doneReg = 0
  pos : σ posPolReg = 0
  neg : σ negPolReg = 1
  writer : WriterState σ M curJ start pref
  capacity : start + pref.length +
      (encodeThreeClausesPayload (clausesToThree base clauses).1).length + 2 < M + curJ
  input_above : M + tmpJ < addr
  start_at_input : start ≤ addr
  safety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg freshReg posPolReg negPolReg
  long_safety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg
  clause_bound : ∀ c ∈ clauses, c.lits.length + 1 ≤ bound
  literal_bound : ∀ c ∈ clauses, ∀ l ∈ c.lits, l.var + 1 ≤ bound
  tail_bound_ok : ∀ c ∈ clauses, c.lits.length ≤ tailBound

lemma clausesToThree_payload_cons
    (base : ℕ) (c : Clause) (cs : List Clause) :
    encodeThreeClausesPayload (clausesToThree base (c :: cs)).1 =
      encodeThreeClausesPayload (clauseToThree base c.lits).1 ++
        encodeThreeClausesPayload
          (clausesToThree (clauseToThree base c.lits).2 cs).1 := by
  rw [clausesToThree_cons]
  simp [encodeThreeClausesPayload, List.flatten_append]

lemma cnfEmitRel_head_input
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ) :
    BitsFrom σ addr (encodeList encodeLiteral c.lits ++
      ((cs.map encodeClause).flatten ++ tail)) := by
  simpa [encodeClause, List.map, List.flatten, List.append_assoc] using hrel.input

/-! The outer relation already contains all data needed to prepare a long
    clause.  This bridge keeps the decode-state construction in one place;
    the subsequent long-branch proof only has to reason about split-tail. -/

lemma cnfEmitRel_long_prepState
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (l1 l2 l3 l4 : Literal) (litRest : List Literal) (restClauses : List Clause)
    (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses) tail pref addr σ) :
    ∃ σ0, EmitClausePrepState M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      outerReg freshReg posPolReg negPolReg bound base
      ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length addr
      (l1 :: l2 :: l3 :: l4 :: litRest) ((restClauses.map encodeClause).flatten ++ tail)
      pref σ σ0 := by
  let c : Clause := ⟨l1 :: l2 :: l3 :: l4 :: litRest⟩
  have hhead := cnfEmitRel_head_input M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base c restClauses tail pref addr σ
    (by simpa [c] using hrel)
  have hinput : BitsFrom σ addr
      (encodeList encodeLiteral (l1 :: l2 :: l3 :: l4 :: litRest) ++
        ((restClauses.map encodeClause).flatten ++ tail)) := by
    simpa [c, encodeClause, List.append_assoc] using hhead
  have hbound : (l1 :: l2 :: l3 :: l4 :: litRest).length + 1 ≤ bound := by
    have hb := hrel.clause_bound c (by simp [c])
    simpa [c] using hb
  have hroomPayload : start + pref.length +
      (encodeThreeClausesPayload
        (clauseToThree base (l1 :: l2 :: l3 :: l4 :: litRest)).1).length + 2 <
      M + curJ := by
    have hc := hrel.capacity
    rw [clausesToThree_payload_cons] at hc
    simp only [List.length_append] at hc
    omega
  have hroom : start + pref.length + l1.var + l2.var + base + 6 < M + curJ := by
    have hlenPayload : l1.var + l2.var + base + 6 ≤
        (encodeThreeClausesPayload
          (clauseToThree base (l1 :: l2 :: l3 :: l4 :: litRest)).1).length + 2 := by
      have h := encodeThreeClausesPayload_length_ge
        (clauseToThree base (l1 :: l2 :: l3 :: l4 :: litRest)).1
      simp only [clauseToThree, List.map_cons, List.sum_cons,
        encodeThreeClausesPayload, List.flatten_cons, List.length_append] at h ⊢
      simp [Literal.var] at h ⊢
      omega
    omega
  have hprep := emitClausePrepState_of_pre M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg outerReg freshReg posPolReg negPolReg bound base
    ((⟨l1 :: l2 :: l3 :: l4 :: litRest⟩ : Clause) :: restClauses).length addr
    (l1 :: l2 :: l3 :: l4 :: litRest) ((restClauses.map encodeClause).flatten ++ tail) pref σ
    hcurJ htmpJ hbound hrel.start_at_input hinput hrel.cursor hrel.length_zero
    hrel.done_zero hrel.outer hrel.fresh hrel.pos hrel.neg hrel.input_above hrel.writer
    hroomPayload hrel.safety
  exact ⟨(decodeNatProgram cursorReg lengthReg doneReg bound).eval σ, hprep⟩

lemma cnf_emit_long_prep_prog_values
    (lengthReg remainingReg carryPolReg carryValReg posPolReg freshReg : ℕ)
    (σ : Store) (base n : ℕ)
    (hlen : σ lengthReg = n) (hfresh : σ freshReg = base)
    (hcp : carryPolReg ≠ remainingReg)
    (hcv : carryValReg ≠ carryPolReg) (hpp : posPolReg ≠ carryValReg)
    (hremCv : remainingReg ≠ carryValReg) (hremPp : remainingReg ≠ posPolReg)
    (hcpPp : carryPolReg ≠ posPolReg)
    (hfreshCp : freshReg ≠ carryPolReg) (hfreshRem : freshReg ≠ remainingReg) :
    let p := (Program.seq (.assign remainingReg (.reg lengthReg))
      (Program.seq (.assign carryPolReg (.const 1))
        (Program.seq (.assign carryValReg (.reg freshReg))
          (Program.seq (.assign posPolReg (.const 0)) (.skip)))))
    let τ := p.eval σ
    τ remainingReg = n ∧ τ carryPolReg = 1 ∧ τ carryValReg = base ∧ τ posPolReg = 0 := by
  dsimp
  simp [eval_seq, eval_assign, Expr.eval, hlen, hfresh,
    writeReg_diff _ _ _ _ hcp.symm,
    writeReg_diff _ _ _ _ hcv.symm,
    writeReg_diff _ _ _ _ hpp.symm,
    writeReg_diff _ _ _ _ hremCv, writeReg_diff _ _ _ _ hremPp,
    writeReg_diff _ _ _ _ hcpPp, writeReg_diff _ _ _ _ hfreshCp, writeReg_diff _ _ _ _ hfreshRem]

lemma cnfEmitRel_next_capacity
    (M curJ start : ℕ) (base : ℕ) (c : Clause) (cs : List Clause)
    (pref payload : Bits) (hcapacity : start + pref.length +
      (encodeThreeClausesPayload (clausesToThree base (c :: cs)).1).length + 2 < M + curJ)
    (hpref : payload = encodeThreeClausesPayload (clauseToThree base c.lits).1) :
    start + (pref ++ payload).length +
      (encodeThreeClausesPayload
        (clausesToThree (clauseToThree base c.lits).2 cs).1).length + 2 < M + curJ := by
  have hcap := hcapacity
  rw [clausesToThree_payload_cons] at hcap
  rw [hpref]
  simp only [List.length_append] at hcap ⊢
  omega

/-! A clause-boundary postcondition packages the endpoint and the control
registers reset by a clause emitter.  Keeping these facts together makes the
outer loop proof independent of the internal branch used by the emitter. -/

structure CNFEmitPost
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ)
    (σ τ : Store) : Prop where
  endpoint : EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
    remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base (c :: cs).length addr pref c.lits σ τ
  input : BitsFrom τ (addr + (encodeList encodeLiteral c.lits).length)
    ((cs.map encodeClause).flatten ++ tail)
  length_zero : τ lengthReg = 0
  done_zero : τ doneReg = 0
  pos : τ posPolReg = 0
  neg : τ negPolReg = 1
  cursor : τ cursorReg = addr + (encodeList encodeLiteral c.lits).length
  fresh : τ freshReg = (clauseToThree base c.lits).2
  outer : τ outerReg = (c :: cs).length - 1
  writer : WriterState τ M curJ start
    (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
  capacity : start +
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1).length +
      (encodeThreeClausesPayload
        (clausesToThree (clauseToThree base c.lits).2 cs).1).length + 2 < M + curJ
  safety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg freshReg posPolReg negPolReg
  long_safety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg
  frame : ∀ r, M + tmpJ < r → τ r = σ r

structure CNFEmitDone
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (tail pref : Bits) (addr : ℕ) (σ : Store) : Prop where
  input : BitsFrom σ addr tail
  cursor : σ cursorReg = addr
  outer : σ outerReg = 0
  fresh : σ freshReg = base
  length_zero : σ lengthReg = 0
  done_zero : σ doneReg = 0
  pos : σ posPolReg = 0
  neg : σ negPolReg = 1
  writer : WriterState σ M curJ start pref
  long_safety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg

structure CNFEmitIterPost
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ)
    (σ τ : Store) : Prop where
  endpoint : EmitClauseIterEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base (c :: cs).length addr
    pref c.lits ((cs.map encodeClause).flatten ++ tail) σ τ
  input : BitsFrom τ (addr + (encodeList encodeLiteral c.lits).length)
    ((cs.map encodeClause).flatten ++ tail)
  cursor : τ cursorReg = addr + (encodeList encodeLiteral c.lits).length
  fresh : τ freshReg = (clauseToThree base c.lits).2
  outer : τ outerReg = (c :: cs).length - 1
  length_zero : τ lengthReg = 0
  done_zero : τ doneReg = 0
  pos : τ posPolReg = 0
  neg : τ negPolReg = 1
  writer : WriterState τ M curJ start
    (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
  capacity : start +
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1).length +
      (encodeThreeClausesPayload
        (clausesToThree (clauseToThree base c.lits).2 cs).1).length + 2 < M + curJ
  safety : ClauseEmitSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg freshReg posPolReg negPolReg
  long_safety : LongClauseRegisterSafety start cursorReg lengthReg polReg varReg doneReg
    outerReg negPolReg remainingReg pol2Reg var2Reg pol3Reg var3Reg carryPolReg carryValReg
    posPolReg freshReg
  frame : ∀ r, M + tmpJ < r → τ r = σ r

lemma cnfEmitIterPost_of_endpoint
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τ₀ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ)
    (hendpoint : EmitClauseEndpoint M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base
      (c :: cs).length addr pref c.lits σ τ₀)
    (hinput : BitsFrom τ₀ (addr + (encodeList encodeLiteral c.lits).length)
      ((cs.map encodeClause).flatten ++ tail))
    (hframe : ∀ r, M + tmpJ < r → τ₀ r = σ r)
    (hpos : τ₀ posPolReg = 0) (hneg : τ₀ negPolReg = 1)
    (htmpJ : curJ < tmpJ)
    (hposLength : posPolReg ≠ lengthReg) (hposDone : posPolReg ≠ doneReg)
    (hnegLength : negPolReg ≠ lengthReg) (hnegDone : negPolReg ≠ doneReg) :
    ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ := by
  obtain ⟨τ, hiter, hpos', hneg'⟩ := emitClauseEndpoint_iter_post_with_polarity
    M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
    pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
    freshReg outerReg bound tailBound base (c :: cs).length addr pref c.lits
    ((cs.map encodeClause).flatten ++ tail) σ τ₀ hendpoint hinput hframe hpos hneg
    hrel.input_above htmpJ hrel.safety hposLength hposDone hnegLength hnegDone
  rcases hiter with ⟨τ0, hendpoint0, hreset, hinput0, hwriter0, hcursor0,
    hfresh0, houter0, hlength0, hdone0, hframe0⟩
  have hcap := cnfEmitRel_next_capacity M curJ start base c cs pref
    (encodeThreeClausesPayload (clauseToThree base c.lits).1) hrel.capacity rfl
  refine ⟨τ, ?_⟩
  exact {
    endpoint := ⟨τ0, hendpoint0, hreset, hinput0, hwriter0, hcursor0,
      hfresh0, houter0, hlength0, hdone0, hframe0⟩
    input := hinput0
    cursor := hcursor0
    fresh := hfresh0
    outer := houter0
    length_zero := hlength0
    done_zero := hdone0
    pos := hpos'
    neg := hneg'
    writer := hwriter0
    capacity := hcap
    safety := hrel.safety
    long_safety := hrel.long_safety
    frame := hframe0 }

lemma cnfEmitIterPost_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τ : Store)
    (hp : CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ) :
    τ = (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ := by
  rcases hp.endpoint with ⟨τ₀, hendpoint, hreset, _hinput, _hwriter, _hcursor,
    _hfresh, _houter, _hlen, _hdone, _hframe⟩
  rcases hendpoint with ⟨hprog, _hwriter0, _hcursor0, _hfresh0, _houter0⟩
  calc
    τ = (emitClauseResetProg lengthReg doneReg).eval τ₀ := hreset
    _ = (emitClauseResetProg lengthReg doneReg).eval
        ((emitClauseProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg remainingReg
          pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
          freshReg outerReg bound tailBound).eval σ) := by rw [← hprog]
    _ = (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ := by
        simp only [emitClauseIterProgram, eval_seq]

/-! `cnfEmitRel_step_of_iter_post_core` is the existential-free core: it consumes a
concrete post-state witness `τ` together with its `CNFEmitIterPost` facts.
Callers that already hold a concrete `τ` (e.g. `cnfEmitRel_step_of_iter_post_eval`)
should call it directly instead of round-tripping through a fresh existential, since
that would produce an unrelated fresh witness variable. -/

lemma cnfEmitRel_step_of_iter_post_core
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ τ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ)
    (hp : CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ) :
    CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound (clauseToThree base c.lits).2
      cs tail (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ := by
  have houter : τ outerReg = cs.length := by
    calc
      τ outerReg = (c :: cs).length - 1 := hp.outer
      _ = cs.length := by simp
  have hcap : start +
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1).length +
      (encodeThreeClausesPayload
        (clausesToThree (clauseToThree base c.lits).2 cs).1).length + 2 < M + curJ := by
    exact cnfEmitRel_next_capacity M curJ start base c cs pref
      (encodeThreeClausesPayload (clauseToThree base c.lits).1) hrel.capacity rfl
  refine {
    input := hp.input
    cursor := hp.cursor
    outer := houter
    fresh := hp.fresh
    length_zero := hp.length_zero
    done_zero := hp.done_zero
    pos := hp.pos
    neg := hp.neg
    writer := hp.writer
    capacity := hcap
    input_above := by
      calc
        M + tmpJ < addr := hrel.input_above
        _ ≤ addr + (encodeList encodeLiteral c.lits).length := by omega
    start_at_input := by
      calc
        start ≤ addr := hrel.start_at_input
        _ ≤ addr + (encodeList encodeLiteral c.lits).length := by omega
    safety := hp.safety
    long_safety := hp.long_safety
    clause_bound := by
      intro d hd
      exact hrel.clause_bound d (by simp [hd])
    literal_bound := by
      intro d hd l hl
      exact hrel.literal_bound d (by simp [hd]) l hl
    tail_bound_ok := by
      intro d hd
      exact hrel.tail_bound_ok d (by simp [hd]) }

lemma cnfEmitRel_step_of_iter_post_eval
    (M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound base : ℕ)
    (c : Clause) (cs : List Clause) (tail pref : Bits) (addr : ℕ) (σ : Store)
    (hrel : CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
      carryValReg freshReg outerReg bound tailBound base (c :: cs) tail pref addr σ)
    (hpost : ∃ τ, CNFEmitIterPost M curJ tmpJ start cursorReg polReg varReg doneReg
      lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
      carryPolReg carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ) :
    ∃ τ, τ = (emitClauseIterProgram curJ tmpJ cursorReg polReg varReg doneReg lengthReg
      remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound).eval σ ∧
      CNFEmitRel M curJ tmpJ start cursorReg polReg varReg doneReg lengthReg remainingReg
      pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg carryValReg
      freshReg outerReg bound tailBound (clauseToThree base c.lits).2 cs tail
      (pref ++ encodeThreeClausesPayload (clauseToThree base c.lits).1)
      (addr + (encodeList encodeLiteral c.lits).length) τ := by
  obtain ⟨τ, hp⟩ := hpost
  have heval := cnfEmitIterPost_eval M curJ tmpJ start cursorReg polReg varReg doneReg
    lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg carryPolReg
    carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ hp
  exact ⟨τ, heval, cnfEmitRel_step_of_iter_post_core M curJ tmpJ start cursorReg polReg varReg
    doneReg lengthReg remainingReg pol2Reg var2Reg pol3Reg var3Reg posPolReg negPolReg
    carryPolReg carryValReg freshReg outerReg bound tailBound base c cs tail pref addr σ τ hrel
    hp⟩


end NPComplete.CookLevin

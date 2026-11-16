module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck
public import NPComplete.CookLevin.Verifier.ClauseLengthEval
public import NPComplete.BoundedWhile.RegLayout
public import NPComplete.RAMToTM.Generic.Api.LayoutSpec
public import NPComplete.RAMToTM.Generic.Api.LayoutStage

/-!
The CNF-level evaluator folds `clauseSatBool`'s per-clause result across the
formula with AND, one length-prefixed clause at a time
(`decodeClauseEvalWithLengthProgram`, `ClauseLengthEval.lean`).  This module
adds only the AND-accumulator step and its loop correctness; the length-
prefix/literal-loop machinery is unchanged and fully reused.

This module also owns the register layout of the CNF-evaluator stages: the role
type, the standard placement and the fact vocabulary the stage contracts state
their boundaries with.  Programs are written once against a role-indexed register
assignment (the `...L` definitions); the numbered programs of the literature are
the same trees at plain numbers, so an implementation change reaches every caller
through one description.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_assign eval_seq writeReg writeReg_diff writeReg_same
    eval_ifNZ eval_forN loopEval loopEval_succ eval_assignInd eval_skip ReadsOnly)
open NPComplete.BoundedWhile (RegLayout LayoutFact)
open NPComplete.BitEncoding (Bits encodeNat_length encodeList encodeNat)
open NPComplete.SAT (Literal)

stage_default boundary

/-! ## Register layout

The roles name the jobs the registers do; the standard placement matches the
numbered instantiation of the wiring (`1 6 7 9 8 10 11 12 13 5 14 15 0`), so a
renumbering edits `stdReg` and the value lemmas below only.  Register 0 holds
the resource bound, register 5 the certificate base. -/

/-- Register roles of the CNF-evaluator stages. -/
@[stage_layout] inductive CNFEvalRole where
  | cursor | pol | var | done | outer | remaining | sat | bit | val | wBase | length | cnf
  | bound | scratch
  deriving DecidableEq

namespace CNFEvalRole

@[stage_layout] def list : List CNFEvalRole :=
  [.cursor, .pol, .var, .done, .outer, .remaining, .sat, .bit, .val, .wBase, .length, .cnf,
    .bound, .scratch]

@[stage_layout] lemma mem_list (role : CNFEvalRole) : role ∈ list := by cases role <;> simp [list]

end CNFEvalRole

/-- The placement used by the standard instantiation. -/
@[stage_layout] def stdReg : CNFEvalRole → Fin 16
  | .bound => ⟨0, by decide⟩
  | .cursor => ⟨1, by decide⟩
  | .wBase => ⟨5, by decide⟩
  | .pol => ⟨6, by decide⟩
  | .var => ⟨7, by decide⟩
  | .outer => ⟨8, by decide⟩
  | .done => ⟨9, by decide⟩
  | .remaining => ⟨10, by decide⟩
  | .sat => ⟨11, by decide⟩
  | .bit => ⟨12, by decide⟩
  | .val => ⟨13, by decide⟩
  | .length => ⟨14, by decide⟩
  | .cnf => ⟨15, by decide⟩
  | .scratch => ⟨2, by decide⟩

@[stage_layout] lemma stdReg_injective : Function.Injective stdReg :=
  RegLayout.pairwise_ne_injective CNFEvalRole.mem_list (by decide)

@[stage_layout] def stdLayout : RegLayout CNFEvalRole := ⟨16, ⟨stdReg, stdReg_injective⟩⟩

@[stage_layout] lemma stdLayout_top : stdLayout.top = 16 := rfl
@[stage_layout] lemma stdLayout_reg_bound : stdLayout.reg .bound = 0 := rfl
@[stage_layout] lemma stdLayout_reg_cursor : stdLayout.reg .cursor = 1 := rfl
@[stage_layout] lemma stdLayout_reg_wBase : stdLayout.reg .wBase = 5 := rfl
@[stage_layout] lemma stdLayout_reg_pol : stdLayout.reg .pol = 6 := rfl
@[stage_layout] lemma stdLayout_reg_var : stdLayout.reg .var = 7 := rfl
@[stage_layout] lemma stdLayout_reg_outer : stdLayout.reg .outer = 8 := rfl
@[stage_layout] lemma stdLayout_reg_done : stdLayout.reg .done = 9 := rfl
@[stage_layout] lemma stdLayout_reg_remaining : stdLayout.reg .remaining = 10 := rfl
@[stage_layout] lemma stdLayout_reg_sat : stdLayout.reg .sat = 11 := rfl
@[stage_layout] lemma stdLayout_reg_bit : stdLayout.reg .bit = 12 := rfl
@[stage_layout] lemma stdLayout_reg_val : stdLayout.reg .val = 13 := rfl
@[stage_layout] lemma stdLayout_reg_length : stdLayout.reg .length = 14 := rfl
@[stage_layout] lemma stdLayout_reg_cnf : stdLayout.reg .cnf = 15 := rfl
@[stage_layout] lemma stdLayout_reg_scratch : stdLayout.reg .scratch = 2 := rfl

/-! ## The AND-accumulator step -/

/-- AND a clause's fold result into the CNF accumulator: once `cnfReg` is `0`
    it stays `0` (short-circuit); a zero `clauseSatReg` clears it. -/
def andIntoProg (clauseSatReg cnfReg : ℕ) : Program :=
  .ifNZ (.reg clauseSatReg) .skip (.assign cnfReg (.const 0))

/-- Layout form of `andIntoProg` at the accumulator roles. -/
def andIntoProgL (reg : CNFEvalRole → ℕ) : Program :=
  andIntoProg (reg .sat) (reg .cnf)

@[stage_impl] lemma andIntoProg_eval (clauseSatReg cnfReg : ℕ) (σ : Store) :
    (andIntoProg clauseSatReg cnfReg).eval σ cnfReg =
      (if σ clauseSatReg = 0 then 0 else σ cnfReg) := by
  unfold andIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases h : σ clauseSatReg = 0
  · simp [eval_assign, Expr.eval, writeReg_same, h]
  · simp [eval_skip, h]

@[stage_impl] lemma andIntoProg_frame (clauseSatReg cnfReg r : ℕ) (σ : Store) (hr : r ≠ cnfReg) :
    (andIntoProg clauseSatReg cnfReg).eval σ r = σ r := by
  unfold andIntoProg
  simp only [eval_ifNZ, Expr.eval]
  by_cases h : σ clauseSatReg = 0
  · simp [eval_assign, Expr.eval, writeReg_diff σ cnfReg 0 r hr, h]
  · simp [eval_skip, h]

/-- Decode one clause (length prefix + literal eval) and AND its Boolean
    value into the CNF accumulator: the one place the clause step's syntax tree
    is written.  `decodeCNFEvalClauseStep` is the same tree at plain numbers. -/
def decodeCNFEvalClauseStepL (reg : CNFEvalRole → ℕ) (bound : ℕ) : Program :=
  .seq (decodeClauseEvalWithLengthProgramL reg .cursor .pol .var .done .remaining .sat .bit .val
      .wBase .length bound)
    (andIntoProgL reg)

/-- Numbered form of `decodeCNFEvalClauseStepL` (the same tree at plain numbers). -/
def decodeCNFEvalClauseStep
    (cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg
      lengthReg cnfReg bound : ℕ) : Program :=
  decodeCNFEvalClauseStepL
    (fun
      | .cursor => cursorReg
      | .pol => polReg
      | .var => varReg
      | .done => doneReg
      | .remaining => remainingReg
      | .sat => satReg
      | .bit => bitReg
      | .val => valReg
      | .wBase => wBaseReg
      | .length => lengthReg
      | .cnf => cnfReg
      | _ => 0)
    bound

/-- One-clause stage of the CNF evaluation loop: the clause evaluator advances the cursor past
`c`, ANDs its Boolean value into `cnfReg`, and leaves the remaining input and witness cells
untouched, so the tail satisfies the same invariants. -/
@[stage_contract] lemma decode_cnf_eval_clause_loop_eval_step
    (R : RegLayout CNFEvalRole) (bound addr s0 wBase : ℕ) (c : Clause) (cs : List Clause)
    (rest : Bits) (σ : Store)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hwbase : σ (R.reg .wBase) = wBase) (hcnf : σ (R.reg .cnf) = s0)
    (hbound_c : c.lits.length + 1 ≤ bound)
    (hvarbound_c : ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ (R.reg .cursor) = addr)
    (hbits : BitsFrom σ addr (encodeClause c ++ rest))
    (w : List Bool)
    (hwbits_c : ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0)
    (hwbits_cs : ∀ cc ∈ cs, ∀ l ∈ cc.lits,
      σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    ∃ σ2, σ2 = (decodeCNFEvalClauseStepL R.reg bound).eval σ ∧
      σ2 (R.reg .cursor) = addr + (encodeClause c).length ∧ σ2 (R.reg .wBase) = wBase ∧
      σ2 (R.reg .cnf) = (if clauseSatBool w c then s0 else 0) ∧
      BitsFrom σ2 (addr + (encodeClause c).length) rest ∧
      (∀ cc ∈ cs, ∀ l ∈ cc.lits,
        σ2 (wBase + l.var) = if w.getD l.var false then 1 else 0) := by
  set cursorReg := R.reg .cursor
  set polReg := R.reg .pol
  set varReg := R.reg .var
  set doneReg := R.reg .done
  set remainingReg := R.reg .remaining
  set satReg := R.reg .sat
  set bitReg := R.reg .bit
  set valReg := R.reg .val
  set wBaseReg := R.reg .wBase
  set lengthReg := R.reg .length
  set cnfReg := R.reg .cnf
  have hdist : cursorReg ≠ polReg ∧ cursorReg ≠ varReg ∧ cursorReg ≠ doneReg ∧
    polReg ≠ varReg ∧ polReg ≠ doneReg ∧ varReg ≠ doneReg ∧ remainingReg ≠ cursorReg ∧
    remainingReg ≠ polReg ∧ remainingReg ≠ varReg ∧ remainingReg ≠ doneReg ∧
    bitReg ≠ cursorReg ∧ bitReg ≠ polReg ∧ bitReg ≠ remainingReg ∧ valReg ≠ cursorReg ∧
    valReg ≠ remainingReg ∧ wBaseReg ≠ cursorReg ∧ wBaseReg ≠ polReg ∧ wBaseReg ≠ varReg ∧
    wBaseReg ≠ doneReg ∧ wBaseReg ≠ remainingReg ∧ wBaseReg ≠ bitReg ∧ wBaseReg ≠ valReg ∧
    wBaseReg ≠ lengthReg ∧ satReg ≠ cursorReg ∧ satReg ≠ polReg ∧ satReg ≠ varReg ∧
    satReg ≠ doneReg ∧ satReg ≠ remainingReg ∧ satReg ≠ bitReg ∧ satReg ≠ valReg ∧
    satReg ≠ wBaseReg ∧ lengthReg ≠ cursorReg ∧ lengthReg ≠ doneReg ∧ cnfReg ≠ cursorReg ∧
    cnfReg ≠ polReg ∧ cnfReg ≠ varReg ∧ cnfReg ≠ doneReg ∧ cnfReg ≠ remainingReg ∧
    cnfReg ≠ satReg ∧ cnfReg ≠ bitReg ∧ cnfReg ≠ valReg ∧ cnfReg ≠ wBaseReg ∧
    cnfReg ≠ lengthReg
    :=
    ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide)⟩
  obtain ⟨hcp, hcv, hcd, hpv, hpd, hvd, hrc, hrp, hrv, hrd, hbc, hbp, hbr, hvc, hvr,
    hwc, hwp, hwv, hwd, hwr, hwb, hwl, hwlen, hsc, hsp, hsv, hsd, hsr, hsb, hsl, hsw,
    hlc, hld, hkc, hkp, hkv, hkd, hkr, hks, hkb, hkval, hkw, hkl⟩ := hdist
  have hbelowW : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
    remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase
    :=
    ⟨R.reg_lt_of_top_le .cursor hb, R.reg_lt_of_top_le .pol hb,
      R.reg_lt_of_top_le .var hb, R.reg_lt_of_top_le .done hb,
      R.reg_lt_of_top_le .remaining hb, R.reg_lt_of_top_le .sat hb,
      R.reg_lt_of_top_le .bit hb, R.reg_lt_of_top_le .val hb⟩
  have hlenW : lengthReg < wBase := R.reg_lt_of_top_le .length hb
  have hcnfregW : cnfReg < wBase := R.reg_lt_of_top_le .cnf hb
  have hbelow : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
    remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧ wBaseReg < addr ∧
    lengthReg < addr ∧ cnfReg < addr
    :=
    ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr,
      R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr,
      R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr,
      R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr,
      R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .length haddr,
      R.reg_lt_of_top_le .cnf haddr⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hbelow
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hbelowW
  have hbelow' : cursorReg < addr ∧ polReg < addr ∧ varReg < addr ∧ doneReg < addr ∧
      remainingReg < addr ∧ satReg < addr ∧ bitReg < addr ∧ valReg < addr ∧
      wBaseReg < addr ∧ lengthReg < addr := ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  have hbelowW' : cursorReg < wBase ∧ polReg < wBase ∧ varReg < wBase ∧ doneReg < wBase ∧
      remainingReg < wBase ∧ satReg < wBase ∧ bitReg < wBase ∧ valReg < wBase :=
    ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩
  obtain ⟨hcurE, hsatE, hwbaseE⟩ := decodeClauseEvalWithLengthProgram_eval
    cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
    bound addr wBase c rest σ
    hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
    hvc hvr hwc hwp hwv hwd hwr hwb hwl hwlen
    hsc hsp hsv hsd hsr hsb hsl hsw hlc hld
    hbelowW' hlenW hbelow' hWA hwbase hbound_c hvarbound_c hc hbits w hwbits_c
  have hfrAll : ∀ r, r ≠ cursorReg → r ≠ polReg → r ≠ varReg → r ≠ doneReg →
      r ≠ remainingReg → r ≠ satReg → r ≠ bitReg → r ≠ valReg →
      r ≠ lengthReg →
      (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg satReg
        bitReg valReg wBaseReg lengthReg bound).eval σ r = σ r := fun r h1 h2 h3 h4 h5 h6 h7 h8
        h10 =>
    decodeClauseEvalWithLengthProgram_frame
      cursorReg polReg varReg doneReg remainingReg satReg bitReg valReg wBaseReg lengthReg
      bound addr wBase c rest σ r
      hcp hcv hcd hpv hpd hvd hrc hrp hrv hrd hbc hbp hbr
      hvc hvr hwc hwp hwv hwd hwr hwb hwl hwlen
      hsc hsp hsv hsd hsr hsb hsl hsw hlc hld
      hbelowW' hlenW hbelow' hWA hwbase hbound_c hvarbound_c hc hbits w hwbits_c
      h1 h2 h3 h4 h5 h6 h7 h8 h10
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = (decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg
      remainingReg satReg bitReg valReg wBaseReg lengthReg bound).eval σ := ⟨_, rfl⟩
  rw [← hσ1] at hcurE hsatE hwbaseE hfrAll
  have hcnf1 : σ1 cnfReg = s0 := (hfrAll cnfReg hkc hkp hkv hkd hkr hks hkb hkval hkl).trans hcnf
  have hbits1 : BitsFrom σ1 (addr + (encodeClause c).length) rest := by
    obtain ⟨_, htail⟩ := bitsFrom_append σ addr (encodeClause c) rest hbits
    intro i hi
    rw [hfrAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact htail i hi
  have hwbits1 : ∀ cc ∈ cs, ∀ l ∈ cc.lits,
      σ1 (wBase + l.var) = if w.getD l.var false then 1 else 0 := by
    intro cc hcc l hl
    rw [hfrAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact hwbits_cs cc hcc l hl
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = (andIntoProg satReg cnfReg).eval σ1 := ⟨_, rfl⟩
  have hfr2 : ∀ r, r ≠ cnfReg → σ2 r = σ1 r := fun r hr => by
    rw [hσ2]; exact andIntoProg_frame satReg cnfReg r σ1 hr
  have h2cnf : σ2 cnfReg = (if σ1 satReg = 0 then 0 else σ1 cnfReg) := by
    rw [hσ2]; exact andIntoProg_eval satReg cnfReg σ1
  refine ⟨σ2, ?_, (hfr2 _ hkc.symm).trans hcurE, (hfr2 _ hkw.symm).trans hwbaseE, ?_,
    bitsFrom_of_eq_on (fun i _ => hfr2 _ (by omega)) hbits1,
    fun cc hcc l hl => (hfr2 _ (by omega)).trans (hwbits1 cc hcc l hl)⟩
  · change σ2 = ((decodeClauseEvalWithLengthProgram cursorReg polReg varReg doneReg remainingReg
        satReg bitReg valReg wBaseReg lengthReg bound).seq (andIntoProg satReg cnfReg)).eval σ
    rw [eval_seq, ← hσ1, ← hσ2]
  · rw [h2cnf, hsatE, hcnf1]
    cases clauseSatBool w c <;> simp

/-! ## Stage facts

The clause loop's boundaries are named facts: the input bits and the witness cells are
passive facts that a register-writing stage preserves without any frame work, and the loop
invariant packages the live register values together with them.  Stage contracts state
their pre- and postconditions over these facts and never over a raw store. -/

/-- The input bits living at cell `b`: a passive fact, read-only above the layout. -/
@[stage_boundary] def bitsFromFact {Role : Type} (R : RegLayout Role) (b : ℕ) (bits : Bits)
    (hb : R.top ≤ b) : LayoutFact R :=
  ⟨fun σ => BitsFrom σ b bits, ⟨∅, Set.Ico b (b + bits.length), fun _ ha => hb.trans ha.1⟩, by
    intro σ σ' he h
    apply bitsFrom_of_eq_on _ h
    intro i hi
    refine he (b + i) (RegLayout.Foot.mem_denote.2 (Or.inr ⟨Nat.le_add_right b i, by omega⟩))⟩

/-- The witness cells of the clauses still to be evaluated: a passive fact, read-only above
the layout. -/
@[stage_boundary] def witnessFact {Role : Type} (R : RegLayout Role) (wBase : ℕ)
    (cs : List Clause) (w : List Bool) (hb : R.top ≤ wBase) : LayoutFact R :=
  ⟨fun σ => ∀ c ∈ cs, ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0,
    ⟨∅, {x | ∃ c ∈ cs, ∃ l ∈ c.lits, x = wBase + l.var},
      fun _ ⟨c, hc, l, hl, he⟩ => by rw [he]; exact le_trans hb (Nat.le_add_right wBase l.var)⟩, by
    intro σ σ' he h c hc l hl
    refine (he (wBase + l.var) ?_).trans (h c hc l hl)
    exact RegLayout.Foot.mem_denote.2 (Or.inr ⟨c, hc, l, hl, rfl⟩)⟩

/-- The clause loop's invariant as facts when the remaining input is `tail` at cell `addr`:
the live register values, the input tail and the witness cells of the remaining clauses. -/
@[stage_boundary] def clauseInvFact (R : RegLayout CNFEvalRole) (addr v wBase bound : ℕ)
    (tail : Bits) (cs : List Clause) (w : List Bool) (haddr : R.top ≤ addr)
    (hb : R.top ≤ wBase) : LayoutFact R :=
  LayoutFact.bigAnd
    [LayoutFact.reg .cursor addr, LayoutFact.reg .cnf v, LayoutFact.reg .wBase wBase,
      LayoutFact.reg .bound bound, bitsFromFact R addr tail haddr, witnessFact R wBase cs w hb]

/-- After one iteration per clause, the cursor has passed the clause-list
    encoding, and the accumulator holds the conjunction of the per-clause
    satisfaction values, seeded by its initial Boolean value. The accumulator
    register is distinct from every other evaluator register and lies below
    the certificate base.  This form exposes the full loop invariant (the witness
    base, the input tail and the witness cells survive the loop); the published
    `decode_cnf_eval_clause_loop_eval` is its first two components. -/
@[stage_contract] lemma decode_cnf_eval_clause_loop_eval_full
    (R : RegLayout CNFEvalRole) (bound addr s0 wBase : ℕ) (cs : List Clause) (rest : Bits)
    (σ : Store)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hwbase : σ (R.reg .wBase) = wBase) (hcnf : σ (R.reg .cnf) = s0) (hs0 : s0 = 0 ∨ s0 = 1)
    (hbound : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ (R.reg .cursor) = addr)
    (hbits : BitsFrom σ addr ((cs.map encodeClause).flatten ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ cs, ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ) (R.reg .cursor) =
      addr + (cs.map encodeClause).flatten.length ∧
    (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ) (R.reg .cnf) =
      (if s0 = 1 ∧ ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) ∧
    (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ) (R.reg .wBase) = wBase ∧
    BitsFrom (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ)
      (addr + (cs.map encodeClause).flatten.length) rest := by
  set cursorReg := R.reg .cursor
  set polReg := R.reg .pol
  set varReg := R.reg .var
  set doneReg := R.reg .done
  set remainingReg := R.reg .remaining
  set satReg := R.reg .sat
  set bitReg := R.reg .bit
  set valReg := R.reg .val
  set wBaseReg := R.reg .wBase
  set lengthReg := R.reg .length
  set cnfReg := R.reg .cnf
  have hdist : cursorReg ≠ polReg∧ cursorReg ≠ varReg∧ cursorReg ≠ doneReg∧
    polReg ≠ varReg∧ polReg ≠ doneReg∧ varReg ≠ doneReg∧ remainingReg ≠ cursorReg∧
    remainingReg ≠ polReg∧ remainingReg ≠ varReg∧ remainingReg ≠ doneReg∧
    bitReg ≠ cursorReg∧ bitReg ≠ polReg∧ bitReg ≠ remainingReg∧ valReg ≠ cursorReg∧
    valReg ≠ remainingReg∧ wBaseReg ≠ cursorReg∧ wBaseReg ≠ polReg∧ wBaseReg ≠ varReg∧
    wBaseReg ≠ doneReg∧ wBaseReg ≠ remainingReg∧ wBaseReg ≠ bitReg∧ wBaseReg ≠ valReg∧
    wBaseReg ≠ lengthReg∧ satReg ≠ cursorReg∧ satReg ≠ polReg∧ satReg ≠ varReg∧
    satReg ≠ doneReg∧ satReg ≠ remainingReg∧ satReg ≠ bitReg∧ satReg ≠ valReg∧
    satReg ≠ wBaseReg∧ lengthReg ≠ cursorReg∧ lengthReg ≠ doneReg∧ cnfReg ≠ cursorReg∧
    cnfReg ≠ polReg∧ cnfReg ≠ varReg∧ cnfReg ≠ doneReg∧ cnfReg ≠ remainingReg∧
    cnfReg ≠ satReg∧ cnfReg ≠ bitReg∧ cnfReg ≠ valReg∧ cnfReg ≠ wBaseReg∧
    cnfReg ≠ lengthReg
    :=
    ⟨R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide), R.reg_ne (by decide), R.reg_ne (by decide),
      R.reg_ne (by decide)⟩
  obtain ⟨hcp, hcv, hcd, hpv, hpd, hvd, hrc, hrp, hrv, hrd, hbc, hbp, hbr, hvc, hvr,
    hwc, hwp, hwv, hwd, hwr, hwb, hwl, hwlen, hsc, hsp, hsv, hsd, hsr, hsb, hsl, hsw,
    hlc, hld, hkc, hkp, hkv, hkd, hkr, hks, hkb, hkval, hkw, hkl⟩ := hdist
  have hbelowW : cursorReg < wBase∧ polReg < wBase∧ varReg < wBase∧ doneReg < wBase∧
    remainingReg < wBase∧ satReg < wBase∧ bitReg < wBase∧ valReg < wBase
    :=
    ⟨R.reg_lt_of_top_le .cursor hb, R.reg_lt_of_top_le .pol hb,
      R.reg_lt_of_top_le .var hb, R.reg_lt_of_top_le .done hb,
      R.reg_lt_of_top_le .remaining hb, R.reg_lt_of_top_le .sat hb,
      R.reg_lt_of_top_le .bit hb, R.reg_lt_of_top_le .val hb⟩
  have hlenW : lengthReg < wBase := R.reg_lt_of_top_le .length hb
  have hcnfregW : cnfReg < wBase := R.reg_lt_of_top_le .cnf hb
  have hbelow : cursorReg < addr∧ polReg < addr∧ varReg < addr∧ doneReg < addr∧
    remainingReg < addr∧ satReg < addr∧ bitReg < addr∧ valReg < addr∧ wBaseReg < addr∧
    lengthReg < addr∧ cnfReg < addr
    :=
    ⟨R.reg_lt_of_top_le .cursor haddr, R.reg_lt_of_top_le .pol haddr,
      R.reg_lt_of_top_le .var haddr, R.reg_lt_of_top_le .done haddr,
      R.reg_lt_of_top_le .remaining haddr, R.reg_lt_of_top_le .sat haddr,
      R.reg_lt_of_top_le .bit haddr, R.reg_lt_of_top_le .val haddr,
      R.reg_lt_of_top_le .wBase haddr, R.reg_lt_of_top_le .length haddr,
      R.reg_lt_of_top_le .cnf haddr⟩
  induction cs generalizing addr s0 σ with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero, loopEval]
      refine ⟨hc, ?_, hwbase, hbits⟩
      rcases hs0 with h0 | h1
      · simp [hcnf, h0]
      · simp [hcnf, h1]
  | cons c cs ih =>
      have hshape : ((c :: cs).map encodeClause).flatten ++ rest =
          encodeClause c ++ ((cs.map encodeClause).flatten ++ rest) := by simp
      rw [hshape] at hbits
      obtain ⟨σ2, hσ2, hcur2, hwb2, hcnf2, hbits2, hwbits2⟩ :=
        decode_cnf_eval_clause_loop_eval_step R bound addr s0 wBase c cs
          ((cs.map encodeClause).flatten ++ rest) σ haddr hb hWA hwbase hcnf
          (hbound c (by simp)) (hvarbound c (by simp)) hc hbits w
          (hwbits c (by simp)) (fun cc hcc => hwbits cc (by simp [hcc]))
      have hs0' : (if clauseSatBool w c then s0 else 0) = 0 ∨
          (if clauseSatBool w c then s0 else 0) = 1 := by
        split_ifs
        · exact hs0
        · exact Or.inl rfl
      have hbelow1 : cursorReg < addr + (encodeClause c).length ∧
          polReg < addr + (encodeClause c).length ∧ varReg < addr + (encodeClause c).length ∧
          doneReg < addr + (encodeClause c).length ∧
          remainingReg < addr + (encodeClause c).length ∧
          satReg < addr + (encodeClause c).length ∧ bitReg < addr + (encodeClause c).length ∧
          valReg < addr + (encodeClause c).length ∧
          wBaseReg < addr + (encodeClause c).length ∧
          lengthReg < addr + (encodeClause c).length ∧ cnfReg < addr + (encodeClause c).length := by
        omega
      obtain ⟨hcurTail, hcnfTail, hwbTail, hbitsTail⟩ :=
        ih (addr + (encodeClause c).length)
        (if clauseSatBool w c then s0 else 0) σ2 (by omega) (by omega) hs0'
        (fun cc hcc => hbound cc (by simp [hcc]))
        (fun cc hcc => hvarbound cc (by simp [hcc])) hbits2 hwbits2 hcur2
        (hwb2.trans rfl) hcnf2 hbelow1
      rw [show (c :: cs).length = cs.length + 1 by simp, loopEval_succ, ← hσ2]
      refine ⟨?_, ?_, hwbTail, ?_⟩
      · rw [hcurTail]
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        ring
      · rw [hcnfTail]
        cases hcs : clauseSatBool w c <;> simp [hcs]
      · simp only [List.map_cons, List.flatten_cons, List.length_append]
        rw [← Nat.add_assoc]
        exact hbitsTail

/-- After one iteration per clause, the cursor has passed the clause-list
    encoding, and the accumulator holds the conjunction of the per-clause
    satisfaction values, seeded by its initial Boolean value. The accumulator
    register is distinct from every other evaluator register and lies below
    the certificate base. -/
@[stage_contract] lemma decode_cnf_eval_clause_loop_eval
    (R : RegLayout CNFEvalRole) (bound addr s0 wBase : ℕ) (cs : List Clause) (rest : Bits)
    (σ : Store)
    (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hwbase : σ (R.reg .wBase) = wBase) (hcnf : σ (R.reg .cnf) = s0) (hs0 : s0 = 0 ∨ s0 = 1)
    (hbound : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound)
    (hc : σ (R.reg .cursor) = addr)
    (hbits : BitsFrom σ addr ((cs.map encodeClause).flatten ++ rest))
    (w : List Bool)
    (hwbits : ∀ c ∈ cs, ∀ l ∈ c.lits, σ (wBase + l.var) = if w.getD l.var false then 1 else 0) :
    (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ) (R.reg .cursor) =
      addr + (cs.map encodeClause).flatten.length ∧
    (loopEval (decodeCNFEvalClauseStepL R.reg bound) cs.length σ) (R.reg .cnf) =
      (if s0 = 1 ∧ ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0) :=
  ⟨(decode_cnf_eval_clause_loop_eval_full R bound addr s0 wBase cs rest σ haddr hb hWA hwbase
      hcnf hs0 hbound hvarbound hc hbits w hwbits).1,
    (decode_cnf_eval_clause_loop_eval_full R bound addr s0 wBase cs rest σ haddr hb hWA hwbase
      hcnf hs0 hbound hvarbound hc hbits w hwbits).2.1⟩

end NPComplete.CookLevin

#check_stage_discipline all

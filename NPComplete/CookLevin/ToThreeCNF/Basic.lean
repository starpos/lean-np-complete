module

public import NPComplete.CookLevin.SAT
public import NPComplete.CookLevin.Classes
public import NPComplete.CookLevin.OutputWriter
public import NPComplete.RAMToTM.ThreeSat.Problem.ReductionMemoryLayout

/-!
# SAT-to-3-CNF foundation

Cook-Levin tableau clauses have unbounded width, whereas the target uses
`ThreeSAT` over `ValidThreeCNF.encode`. This module defines the split-tail,
clause-level, and whole-CNF transformations, together with compact variable
renumbering. It proves compaction correctness and variable and size bounds needed
by the semantic and RAM-based reduction arguments.
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
/-! ## Variable bounds -/

def litsVarBound : List Literal → ℕ
  | [] => 0
  | l :: ls => max (l.var + 1) (litsVarBound ls)

def clauseVarBound (c : Clause) : ℕ := litsVarBound c.lits

def clausesVarBound : List Clause → ℕ
  | [] => 0
  | c :: cs => max (clauseVarBound c) (clausesVarBound cs)

def cnfVarBound (φ : CNF) : ℕ := clausesVarBound φ.clauses

/-! ## Compact variable renumbering -/

/-- The distinct variables occurring in a CNF.

`List.dedup` is executable with the decidable equality on `Nat`; unlike a `Finset.toList`, this
definition does not invoke a classical choice. -/
def cnfUsedVars (φ : CNF) : List ℕ :=
  (φ.clauses.flatMap (fun c => c.lits.map Literal.var)).dedup

def compactVar (φ : CNF) (v : ℕ) : ℕ :=
  (cnfUsedVars φ).idxOf v

def compactLiteral (φ : CNF) : Literal → Literal
  | Literal.pos v => Literal.pos (compactVar φ v)
  | Literal.neg v => Literal.neg (compactVar φ v)

def compactClause (φ : CNF) (c : Clause) : Clause :=
  ⟨c.lits.map (compactLiteral φ)⟩

def compactCNF (φ : CNF) : CNF :=
  ⟨φ.clauses.map (compactClause φ)⟩

lemma cnfUsedVars_mem {φ : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ φ.clauses) (hl : l ∈ c.lits) :
    l.var ∈ cnfUsedVars φ := by
  apply List.mem_dedup.mpr
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨c, hc, l, hl, rfl⟩

lemma compactVar_lt_card {φ : CNF} {v : ℕ} (hv : v ∈ cnfUsedVars φ) :
    compactVar φ v < (cnfUsedVars φ).length := by
  unfold compactVar
  exact List.idxOf_lt_length_of_mem hv

lemma compactVar_getI {φ : CNF} {v : ℕ} (hv : v ∈ cnfUsedVars φ) :
    (cnfUsedVars φ).getI (compactVar φ v) = v := by
  have hi := compactVar_lt_card hv
  change (cnfUsedVars φ).getI ((cnfUsedVars φ).idxOf v) = v
  rw [List.getI_eq_getElem _ (List.idxOf_lt_length_iff.mpr hv)]
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

lemma compactLiteral_eval_forward {φ : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ φ.clauses) (hl : l ∈ c.lits) (τ : Literal.Assignment) :
    (compactLiteral φ l).eval
        (fun i => τ ((cnfUsedVars φ).getI i)) = l.eval τ := by
  have hv := cnfUsedVars_mem hc hl
  cases l with
  | pos v =>
      have hv' : v ∈ cnfUsedVars φ := by
        change v ∈ cnfUsedVars φ at hv
        exact hv
      simp only [compactLiteral, Literal.eval]
      rw [compactVar_getI hv']
  | neg v =>
      have hv' : v ∈ cnfUsedVars φ := by
        change v ∈ cnfUsedVars φ at hv
        exact hv
      simp only [compactLiteral, Literal.eval]
      rw [compactVar_getI hv']

lemma compactClause_sat_forward {φ : CNF} {c : Clause}
    (hc : c ∈ φ.clauses) {τ : Literal.Assignment}
    (hτ : c.Satisfied τ) :
    (compactClause φ c).Satisfied
      (fun i => τ ((cnfUsedVars φ).getI i)) := by
  obtain ⟨l, hl, hev⟩ := hτ
  refine ⟨compactLiteral φ l, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨l, hl, rfl⟩
  · exact (compactLiteral_eval_forward hc hl τ).trans hev

lemma compactClause_sat_backward {φ : CNF} {c : Clause}
    {τ : Literal.Assignment}
    (hτ : (compactClause φ c).Satisfied τ) :
    c.Satisfied (fun v => τ (compactVar φ v)) := by
  obtain ⟨l, hl, hev⟩ := hτ
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp (by
    simpa [compactClause] using hl)
  refine ⟨l', hl', ?_⟩
  cases l' <;> simpa [compactLiteral, Literal.eval] using hev

lemma compactCNF_sat_iff (φ : CNF) :
    SAT (compactCNF φ) ↔ SAT φ := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => τ (compactVar φ v), ?_⟩
    intro c hc
    have hc' : compactClause φ c ∈ (compactCNF φ).clauses := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact compactClause_sat_backward (hτ _ hc')
  · rintro ⟨τ, hτ⟩
    refine ⟨(fun i => τ ((cnfUsedVars φ).getI i)), ?_⟩
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact compactClause_sat_forward hd (hτ _ hd)

lemma litsVarBound_le_of_forall {ls : List Literal} {B : ℕ}
    (h : ∀ l ∈ ls, l.var < B) : litsVarBound ls ≤ B := by
  induction ls with
  | nil => simp [litsVarBound]
  | cons l ls ih =>
      rw [litsVarBound]
      apply max_le
      · have hl := h l (by simp)
        omega
      · apply ih
        intro l' hl'
        exact h l' (List.mem_cons_of_mem l hl')

lemma var_lt_litsVarBound {ls : List Literal} {l : Literal} (h : l ∈ ls) :
    l.var < litsVarBound ls := by
  induction ls with
  | nil => cases h
  | cons l' rest ih =>
      cases h with
      | head => exact Nat.lt_of_succ_le (Nat.le_max_left _ _)
      | tail _ hrest => exact lt_of_lt_of_le (ih hrest) (Nat.le_max_right _ _)

lemma clauseVarBound_of_mem {cs : List Clause} {c : Clause} (h : c ∈ cs) :
    clauseVarBound c ≤ clausesVarBound cs := by
  induction cs with
  | nil => cases h
  | cons c' rest ih =>
      cases h with
      | head => exact Nat.le_max_left _ _
      | tail _ hrest => exact le_trans (ih hrest) (Nat.le_max_right _ _)

lemma var_lt_clausesVarBound {cs : List Clause} {c : Clause} {l : Literal}
    (hc : c ∈ cs) (hl : l ∈ c.lits) : l.var < clausesVarBound cs :=
  lt_of_lt_of_le (var_lt_litsVarBound hl) (clauseVarBound_of_mem hc)

/-! ## Sliding-window rewrite -/

def splitTail (base : ℕ) (carry : Literal) : List Literal → List ThreeClause × ℕ
  | [] => (⟨carry, carry, carry⟩ :: [], base)
  | [l] => (⟨carry, l, l⟩ :: [], base)
  | [l1, l2] => (⟨carry, l1, l2⟩ :: [], base)
  | l :: rest =>
      let p := splitTail (base + 1) (Literal.neg base) rest
      (⟨carry, l, Literal.pos base⟩ :: p.1, p.2)

def clauseToThree (base : ℕ) : List Literal → List ThreeClause × ℕ
  | [] =>
      ([⟨Literal.pos base, Literal.pos base, Literal.pos base⟩,
        ⟨Literal.neg base, Literal.neg base, Literal.neg base⟩],
        base + 1)
  | [l] => ([⟨l, l, l⟩], base)
  | [l1, l2] => ([⟨l1, l2, l2⟩], base)
  | l1 :: l2 :: rest =>
      (⟨l1, l2, Literal.pos base⟩ ::
        (splitTail (base + 1) (Literal.neg base) rest).1,
       (splitTail (base + 1) (Literal.neg base) rest).2)

def clausesToThree (base : ℕ) : List Clause → List ThreeClause × ℕ
  | [] => ([], base)
  | c :: cs =>
      let p := clauseToThree base c.lits
      let q := clausesToThree p.2 cs
      (p.1 ++ q.1, q.2)

def toThreeCNF (φ : CNF) : ThreeCNF :=
  let p := clausesToThree (cnfVarBound φ) φ.clauses
  ⟨p.2, p.1⟩

lemma splitTail_nil (base : ℕ) (carry : Literal) :
    splitTail base carry [] = ([⟨carry, carry, carry⟩], base) :=
  rfl

lemma splitTail_one (base : ℕ) (carry l : Literal) :
    splitTail base carry [l] = ([⟨carry, l, l⟩], base) :=
  rfl

lemma splitTail_two (base : ℕ) (carry l1 l2 : Literal) :
    splitTail base carry [l1, l2] = ([⟨carry, l1, l2⟩], base) :=
  rfl

lemma splitTail_cons3 (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal) :
    splitTail base carry (l :: l2 :: l3 :: rest) =
      (⟨carry, l, Literal.pos base⟩ ::
        (splitTail (base + 1) (Literal.neg base) (l2 :: l3 :: rest)).1,
       (splitTail (base + 1) (Literal.neg base) (l2 :: l3 :: rest)).2) :=
  rfl

lemma clauseToThree_nil (base : ℕ) :
    clauseToThree base [] =
      ([⟨Literal.pos base, Literal.pos base, Literal.pos base⟩,
        ⟨Literal.neg base, Literal.neg base, Literal.neg base⟩],
        base + 1) :=
  rfl

lemma clauseToThree_one (base : ℕ) (l : Literal) :
    clauseToThree base [l] = ([⟨l, l, l⟩], base) :=
  rfl

lemma clauseToThree_two (base : ℕ) (l1 l2 : Literal) :
    clauseToThree base [l1, l2] = ([⟨l1, l2, l2⟩], base) :=
  rfl

lemma clauseToThree_cons4 (base : ℕ) (l1 l2 l3 : Literal) (rest : List Literal) :
    clauseToThree base (l1 :: l2 :: l3 :: rest) =
      (⟨l1, l2, Literal.pos base⟩ ::
        (splitTail (base + 1) (Literal.neg base) (l3 :: rest)).1,
       (splitTail (base + 1) (Literal.neg base) (l3 :: rest)).2) :=
  rfl

lemma clausesToThree_nil (base : ℕ) : clausesToThree base [] = ([], base) :=
  rfl

lemma clausesToThree_cons (base : ℕ) (c : Clause) (cs : List Clause) :
    clausesToThree base (c :: cs) =
      ((clauseToThree base c.lits).1 ++
        (clausesToThree (clauseToThree base c.lits).2 cs).1,
       (clausesToThree (clauseToThree base c.lits).2 cs).2) :=
  rfl

/-! Exact executable statistics for the clause rewrite.  The parser module
keeps these recurrences independent of the semantic CNF definitions; these
lemmas identify them with the actual `splitTail`/`clauseToThree` projections. -/

lemma splitTail_base_stat_eq (base : ℕ) (carry : Literal) (ls : List Literal) :
    (splitTail base carry ls).2 = splitTailBaseStat base ls := by
  induction ls generalizing base carry with
  | nil => rfl
  | cons l rest ih =>
      cases rest with
      | nil => rfl
      | cons l2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons l3 rest3 =>
              rw [splitTail_cons3]
              exact ih (base + 1) (Literal.neg base)

lemma splitTail_count_stat_eq (base : ℕ) (carry : Literal) (ls : List Literal) :
    (splitTail base carry ls).1.length = splitTailCountStat ls := by
  induction ls generalizing base carry with
  | nil => rfl
  | cons l rest ih =>
      cases rest with
      | nil => rfl
      | cons l2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons l3 rest3 =>
              rw [splitTail_cons3, List.length_cons]
              simp only [splitTailCountStat]
              rw [ih (base + 1) (Literal.neg base)]

lemma clauseFreshBaseStat_eq (base : ℕ) (ls : List Literal) :
    (clauseToThree base ls).2 = clauseFreshBaseStat base ls := by
  match ls with
  | [] => rfl
  | [l] => rfl
  | [l1, l2] => rfl
  | l1 :: l2 :: l3 :: rest =>
      rw [clauseToThree_cons4]
      exact splitTail_base_stat_eq (base + 1) (Literal.neg base) (l3 :: rest)

lemma clauseThreeCountStat_eq (base : ℕ) (ls : List Literal) :
    (clauseToThree base ls).1.length = clauseThreeCountStat ls := by
  match ls with
  | [] => rfl
  | [l] => rfl
  | [l1, l2] => rfl
  | l1 :: l2 :: l3 :: rest =>
      rw [clauseToThree_cons4, List.length_cons]
      rw [splitTail_count_stat_eq]
      rfl

lemma clausesToThree_fresh_base_stat_eq (base : ℕ) (cs : List Clause) :
    (clausesToThree base cs).2 =
      cnfFreshBaseStat base (cs.map (fun c => c.lits)) := by
  induction cs generalizing base with
  | nil => rfl
  | cons c rest ih =>
      rw [clausesToThree_cons]
      have h := ih (clauseToThree base c.lits).2
      simpa [cnfFreshBaseStat, clauseFreshBaseStat_eq] using h

lemma clausesToThree_three_count_stat_eq (base : ℕ) (cs : List Clause) :
    (clausesToThree base cs).1.length =
      cnfThreeCountStat (cs.map (fun c => c.lits)) := by
  induction cs generalizing base with
  | nil => rfl
  | cons c rest ih =>
      rw [clausesToThree_cons, List.length_append]
      have h := ih (clauseToThree base c.lits).2
      simpa [cnfThreeCountStat, clauseThreeCountStat_eq] using h

lemma cnfFreshBaseStat_toThreeCNF (φ : CNF) :
    cnfFreshBaseStat (cnfVarBound φ) (φ.clauses.map (fun c => c.lits)) =
      (toThreeCNF φ).numVars := by
  symm
  simpa [toThreeCNF] using
    (clausesToThree_fresh_base_stat_eq (cnfVarBound φ) φ.clauses)

lemma cnfThreeCountStat_toThreeCNF (φ : CNF) :
    cnfThreeCountStat (φ.clauses.map (fun c => c.lits)) =
      (toThreeCNF φ).clauses.length := by
  symm
  simpa [toThreeCNF] using
    (clausesToThree_three_count_stat_eq (cnfVarBound φ) φ.clauses)


end NPComplete.CookLevin

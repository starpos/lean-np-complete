module

public import NPComplete.CookLevin.ToThreeCNF.Basic

/-!
# Satisfiability-preserving rewrite

Splitting a wide clause introduces fresh variables, so equisatisfiability needs both directions:
a satisfying assignment of the 3CNF restricts to one of the original CNF, and an assignment of the
original extends to the fresh variables. This module proves both (`sat_iff_threeSAT`), together
with the variable bounds and size bounds of the rewrite that the bounded producer relies on.
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
/-! ## Assignment helpers -/

lemma var_pos (i : ℕ) : (Literal.pos i).var = i := rfl
lemma var_neg (i : ℕ) : (Literal.neg i).var = i := rfl
lemma eval_pos (τ : Literal.Assignment) (i : ℕ) : (Literal.pos i).eval τ = τ i := rfl
lemma eval_neg (τ : Literal.Assignment) (i : ℕ) : (Literal.neg i).eval τ = !(τ i) := rfl

def assignSet (τ : Literal.Assignment) (v : ℕ) (b : Bool) : Literal.Assignment :=
  fun x => if x = v then b else τ x

lemma assignSet_ne {τ : Literal.Assignment} {v x : ℕ} (b : Bool) (h : x ≠ v) :
    assignSet τ v b x = τ x := by
  simp [assignSet, h]

lemma assignSet_lt {τ : Literal.Assignment} {v x : ℕ} (b : Bool) (h : x < v) :
    assignSet τ v b x = τ x :=
  assignSet_ne b (ne_of_lt h)

lemma eval_assignSet_lt {τ : Literal.Assignment} {v : ℕ} (b : Bool) {l : Literal}
    (h : l.var < v) : l.eval (assignSet τ v b) = l.eval τ := by
  cases l with
  | pos i =>
      have hi : i ≠ v := ne_of_lt (by simpa [var_pos] using h)
      simp [eval_pos, assignSet, hi]
  | neg i =>
      have hi : i ≠ v := ne_of_lt (by simpa [var_neg] using h)
      simp [eval_neg, assignSet, hi]

lemma eval_of_var_eq {τ σ : Literal.Assignment} {l : Literal}
    (h : τ l.var = σ l.var) : l.eval τ = l.eval σ := by
  cases l with
  | pos i => simpa [eval_pos, var_pos] using h
  | neg i => simpa [eval_neg, var_neg] using h

def orLits (τ : Literal.Assignment) (ls : List Literal) : Bool :=
  ls.any (fun l => l.eval τ)

lemma orLits_iff (τ : Literal.Assignment) (ls : List Literal) :
    orLits τ ls = true ↔ ∃ l ∈ ls, l.eval τ = true := by
  simp [orLits, List.any_eq_true]

lemma three_of_or {τ : Literal.Assignment} {a b c : Literal}
    (h : a.eval τ = true ∨ b.eval τ = true ∨ c.eval τ = true) :
    ThreeClause.Satisfied τ ⟨a, b, c⟩ := by
  simpa [ThreeClause.Satisfied] using h

lemma mem_cons_of_mem_tail {α : Type*} {a : α} {l : List α} {x : α} (h : x ∈ l) :
    x ∈ a :: l :=
  List.mem_cons_of_mem a h

lemma mem_cons₂ {α : Type*} {a b : α} {l : List α} {x : α} (h : x ∈ l) :
    x ∈ a :: b :: l :=
  mem_cons_of_mem_tail (mem_cons_of_mem_tail h)

lemma three_satisfied_of_eval_eq {τ σ : Literal.Assignment} {c : ThreeClause}
    (h1 : c.l1.eval τ = c.l1.eval σ) (h2 : c.l2.eval τ = c.l2.eval σ)
    (h3 : c.l3.eval τ = c.l3.eval σ) :
    c.Satisfied τ ↔ c.Satisfied σ := by
  simp [ThreeClause.Satisfied, h1, h2, h3]

/-! ## Width-0/1/2 gadgets -/

lemma repeat1_iff (τ : Literal.Assignment) (l : Literal) :
    ThreeClause.Satisfied τ ⟨l, l, l⟩ ↔ l.eval τ = true := by
  simp [ThreeClause.Satisfied]

lemma repeat2_iff (τ : Literal.Assignment) (l1 l2 : Literal) :
    ThreeClause.Satisfied τ ⟨l1, l2, l2⟩ ↔
      l1.eval τ = true ∨ l2.eval τ = true := by
  simp [ThreeClause.Satisfied]

lemma unsat_pair_not {v : ℕ} {τ : Literal.Assignment} :
    ¬ (ThreeClause.Satisfied τ ⟨Literal.pos v, Literal.pos v, Literal.pos v⟩ ∧
        ThreeClause.Satisfied τ ⟨Literal.neg v, Literal.neg v, Literal.neg v⟩) := by
  simp [ThreeClause.Satisfied, eval_pos, eval_neg]

/-! ## Variable bounds of the rewrite -/

lemma splitTail_base_le (base : ℕ) (carry : Literal) (ls : List Literal) :
    base ≤ (splitTail base carry ls).2 := by
  induction ls generalizing base carry with
  | nil => rw [splitTail_nil]
  | cons l rest ih =>
      match rest with
      | [] => rw [splitTail_one]
      | [l2] => rw [splitTail_two]
      | l2 :: l3 :: rest' =>
          rw [splitTail_cons3]
          exact Nat.le_trans (Nat.le_succ _) (ih _ _)

lemma splitTail_var_lt_nil (base : ℕ) (carry : Literal) (hc : carry.var < base) :
    ∀ c ∈ (splitTail base carry []).1, ∀ l ∈ c.literals,
      l.var < (splitTail base carry []).2 := by
  intro c hc' lit hlit
  rw [splitTail_nil] at hc' ⊢
  simp only [List.mem_singleton] at hc'
  subst hc'
  have : lit = carry := by simpa [ThreeClause.literals] using hlit
  subst this
  exact hc

lemma splitTail_var_lt_one (base : ℕ) (carry l : Literal) (hc : carry.var < base)
    (hl : l.var < base) :
    ∀ c ∈ (splitTail base carry [l]).1, ∀ lit ∈ c.literals,
      lit.var < (splitTail base carry [l]).2 := by
  intro c hc' lit hlit
  rw [splitTail_one] at hc'
  simp only [List.mem_singleton] at hc'
  subst hc'
  simp [ThreeClause.literals] at hlit
  rcases hlit with rfl | rfl | rfl <;> assumption

lemma splitTail_var_lt_two (base : ℕ) (carry l1 l2 : Literal) (hc : carry.var < base)
    (h1 : l1.var < base) (h2 : l2.var < base) :
    ∀ c ∈ (splitTail base carry [l1, l2]).1, ∀ lit ∈ c.literals,
      lit.var < (splitTail base carry [l1, l2]).2 := by
  intro c hc' lit hlit
  rw [splitTail_two] at hc'
  simp only [List.mem_singleton] at hc'
  subst hc'
  simp [ThreeClause.literals] at hlit
  rcases hlit with rfl | rfl | rfl <;> assumption

lemma splitTail_var_lt (base : ℕ) (carry : Literal) (ls : List Literal)
    (hc : carry.var < base) (hls : ∀ l ∈ ls, l.var < base) :
    ∀ c ∈ (splitTail base carry ls).1, ∀ l ∈ c.literals,
      l.var < (splitTail base carry ls).2 := by
  induction ls generalizing base carry with
  | nil => exact splitTail_var_lt_nil base carry hc
  | cons l rest ih =>
      match rest with
      | [] => exact splitTail_var_lt_one base carry l hc (hls l (by simp))
      | [l2] =>
          exact splitTail_var_lt_two base carry l l2 hc (hls l (by simp))
            (hls l2 (by simp))
      | l2 :: l3 :: rest' =>
          intro c hc' lit hlit
          rw [splitTail_cons3] at hc'
          simp only [List.mem_cons] at hc'
          have hrest : ∀ x ∈ l2 :: l3 :: rest', x.var < base + 1 := by
            intro x hx
            exact Nat.lt_trans (hls x (mem_cons_of_mem_tail hx)) (Nat.lt_succ_self _)
          have ih' := ih (base + 1) (Literal.neg base) (by simp [var_neg]) hrest
          rcases hc' with rfl | hc'
          · simp [ThreeClause.literals] at hlit
            have hle := splitTail_base_le (base + 1) (Literal.neg base)
              (l2 :: l3 :: rest')
            have hl := hls l (by simp)
            rcases hlit with rfl | rfl | rfl
            · exact lt_of_lt_of_le hc (le_trans (Nat.le_succ _) hle)
            · exact lt_of_lt_of_le hl (le_trans (Nat.le_succ _) hle)
            · simp [var_pos]
              exact lt_of_lt_of_le (Nat.lt_succ_self _) hle
          · exact ih' c hc' lit hlit

lemma clauseToThree_base_le (base : ℕ) (ls : List Literal) :
    base ≤ (clauseToThree base ls).2 := by
  match ls with
  | [] => rw [clauseToThree_nil]; exact Nat.le_succ _
  | [l] => rw [clauseToThree_one]
  | [l1, l2] => rw [clauseToThree_two]
  | l1 :: l2 :: l3 :: rest =>
      rw [clauseToThree_cons4]
      exact Nat.le_trans (Nat.le_succ _) (splitTail_base_le _ _ _)

lemma clauseToThree_var_lt (base : ℕ) (ls : List Literal)
    (hls : ∀ l ∈ ls, l.var < base) :
    ∀ c ∈ (clauseToThree base ls).1, ∀ l ∈ c.literals,
      l.var < (clauseToThree base ls).2 := by
  match ls with
  | [] =>
      intro c hc lit hlit
      rw [clauseToThree_nil] at hc ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [ThreeClause.literals] at hlit
        subst hlit
        simp [var_pos]
      · simp [ThreeClause.literals] at hlit
        subst hlit
        simp [var_neg]
  | [l] =>
      intro c hc lit hlit
      rw [clauseToThree_one] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      simp [ThreeClause.literals] at hlit
      have hl := hls l (by simp)
      subst hlit
      exact hl
  | [l1, l2] =>
      intro c hc lit hlit
      rw [clauseToThree_two] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      simp [ThreeClause.literals] at hlit
      have h1 := hls l1 (by simp)
      have h2 := hls l2 (by simp)
      rcases hlit with rfl | rfl | rfl <;> assumption
  | l1 :: l2 :: l3 :: rest =>
      intro c hc lit hlit
      rw [clauseToThree_cons4] at hc ⊢
      simp only [List.mem_cons] at hc
      have hrest : ∀ x ∈ l3 :: rest, x.var < base + 1 := by
        intro x hx
        exact Nat.lt_trans (hls x (mem_cons₂ hx)) (Nat.lt_succ_self _)
      have hsplit := splitTail_var_lt (base + 1) (Literal.neg base) (l3 :: rest)
        (by simp [var_neg]) hrest
      have h1 := hls l1 (by simp)
      have h2 := hls l2 (by simp)
      rcases hc with rfl | hc
      · simp [ThreeClause.literals] at hlit
        have hle := splitTail_base_le (base + 1) (Literal.neg base) (l3 :: rest)
        rcases hlit with rfl | rfl | rfl
        · exact lt_of_lt_of_le h1 (le_trans (Nat.le_succ _) hle)
        · exact lt_of_lt_of_le h2 (le_trans (Nat.le_succ _) hle)
        · simp [var_pos]
          exact lt_of_lt_of_le (Nat.lt_succ_self _) hle
      · exact hsplit c hc lit hlit

lemma clausesToThree_base_le (base : ℕ) (cs : List Clause) :
    base ≤ (clausesToThree base cs).2 := by
  induction cs generalizing base with
  | nil => rw [clausesToThree_nil]
  | cons c rest ih =>
      rw [clausesToThree_cons]
      exact Nat.le_trans (clauseToThree_base_le _ _) (ih _)

lemma clausesToThree_var_lt (base : ℕ) (cs : List Clause)
    (hcs : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var < base) :
    ∀ c ∈ (clausesToThree base cs).1, ∀ l ∈ c.literals,
      l.var < (clausesToThree base cs).2 := by
  induction cs generalizing base with
  | nil => intro c hc; cases hc
  | cons c rest ih =>
      intro tc htc lit hlit
      rw [clausesToThree_cons] at htc
      have hc0 : ∀ l ∈ c.lits, l.var < base := fun l hl => hcs c (by simp) l hl
      have hle := clauseToThree_base_le base c.lits
      have hrest : ∀ d ∈ rest, ∀ l ∈ d.lits, l.var < (clauseToThree base c.lits).2 := by
        intro d hd l hl
        exact lt_of_lt_of_le (hcs d (List.mem_cons_of_mem _ hd) l hl) hle
      have hfinal := clausesToThree_base_le (clauseToThree base c.lits).2 rest
      rcases List.mem_append.mp htc with htc | htc
      · exact lt_of_lt_of_le (clauseToThree_var_lt base c.lits hc0 tc htc lit hlit) hfinal
      · exact ih _ hrest tc htc lit hlit

lemma toThreeCNF_bounded (φ : CNF) : (toThreeCNF φ).Bounded := by
  intro c hc l hl
  simp only [toThreeCNF] at hc
  exact clausesToThree_var_lt (cnfVarBound φ) φ.clauses
    (fun d hd lit hlit => var_lt_clausesVarBound hd hlit) c hc l hl

def toValidThreeCNF (φ : CNF) : ValidThreeCNF :=
  ⟨toThreeCNF φ, toThreeCNF_bounded φ⟩

lemma toValidThreeCNF_encode (φ : CNF) :
    NPComplete.SAT.ValidThreeCNF.encode (toValidThreeCNF φ) = encodeThreeCNF (toThreeCNF φ) :=
  rfl

/-! ## Reflection: 3CNF satisfaction implies original SAT -/

lemma splitTail_reflect (base : ℕ) (carry : Literal) (ls : List Literal)
    (σ : Literal.Assignment)
    (hsat : ∀ c ∈ (splitTail base carry ls).1, c.Satisfied σ) :
    carry.eval σ = true ∨ ∃ l ∈ ls, l.eval σ = true := by
  induction ls generalizing base carry with
  | nil =>
      have h0 := hsat ⟨carry, carry, carry⟩ (by simp [splitTail_nil])
      exact Or.inl ((repeat1_iff _ _).mp h0)
  | cons l rest ih =>
      match rest with
      | [] =>
          have h0 := hsat ⟨carry, l, l⟩ (by simp [splitTail_one])
          have h0' : carry.eval σ = true ∨ l.eval σ = true := by
            simp [ThreeClause.Satisfied] at h0
            tauto
          rcases h0' with h | h
          · exact Or.inl h
          · exact Or.inr ⟨l, List.mem_singleton.mpr rfl, h⟩
      | [l2] =>
          have h0 := hsat ⟨carry, l, l2⟩ (by simp [splitTail_two])
          simp [ThreeClause.Satisfied] at h0
          rcases h0 with h | h | h
          · exact Or.inl h
          · exact Or.inr ⟨l, by simp, h⟩
          · exact Or.inr ⟨l2, by simp, h⟩
      | l2 :: l3 :: rest' =>
          have h0 := hsat ⟨carry, l, Literal.pos base⟩ (by simp [splitTail_cons3])
          have hrest := ih (base + 1) (Literal.neg base) (fun c hc =>
            hsat c (by simp [splitTail_cons3, hc]))
          simp [ThreeClause.Satisfied, eval_pos] at h0
          rcases h0 with h | h | hy
          · exact Or.inl h
          · exact Or.inr ⟨l, by simp, h⟩
          · rcases hrest with hneg | ⟨x, hx, hxev⟩
            · simp [eval_neg, hy] at hneg
            · exact Or.inr ⟨x, mem_cons_of_mem_tail hx, hxev⟩

lemma clauseToThree_reflect (base : ℕ) (ls : List Literal) (σ : Literal.Assignment)
    (hsat : ∀ c ∈ (clauseToThree base ls).1, c.Satisfied σ) :
    Clause.Satisfied σ ⟨ls⟩ := by
  match ls with
  | [] =>
      have hp := hsat ⟨Literal.pos base, Literal.pos base, Literal.pos base⟩
        (by simp [clauseToThree_nil])
      have hn := hsat ⟨Literal.neg base, Literal.neg base, Literal.neg base⟩
        (by simp [clauseToThree_nil])
      exact (unsat_pair_not (v := base) ⟨hp, hn⟩).elim
  | [l] =>
      have h0 := hsat ⟨l, l, l⟩ (by simp [clauseToThree_one])
      exact ⟨l, by simp, (repeat1_iff _ _).mp h0⟩
  | [l1, l2] =>
      have h0 := hsat ⟨l1, l2, l2⟩ (by simp [clauseToThree_two])
      rcases (repeat2_iff _ _ _).mp h0 with h | h
      · exact ⟨l1, by simp, h⟩
      · exact ⟨l2, by simp, h⟩
  | l1 :: l2 :: l3 :: rest =>
      have h0 := hsat ⟨l1, l2, Literal.pos base⟩ (by simp [clauseToThree_cons4])
      have hrest := splitTail_reflect (base + 1) (Literal.neg base) (l3 :: rest) σ
        (fun c hc => hsat c (by simp [clauseToThree_cons4, hc]))
      simp [ThreeClause.Satisfied, eval_pos] at h0
      rcases h0 with h | h | hy
      · exact ⟨l1, by simp, h⟩
      · exact ⟨l2, by simp, h⟩
      · rcases hrest with hneg | ⟨x, hx, hxev⟩
        · simp [eval_neg, hy] at hneg
        · exact ⟨x, mem_cons₂ hx, hxev⟩

lemma clausesToThree_reflect (base : ℕ) (cs : List Clause) (σ : Literal.Assignment)
    (hsat : ∀ c ∈ (clausesToThree base cs).1, c.Satisfied σ) :
    ∀ c ∈ cs, c.Satisfied σ := by
  induction cs generalizing base with
  | nil => intro c hc; cases hc
  | cons c rest ih =>
      intro d hd
      have hleft : ∀ tc ∈ (clauseToThree base c.lits).1, tc.Satisfied σ :=
        fun tc htc => hsat tc (by
          rw [clausesToThree_cons]
          exact List.mem_append.mpr (Or.inl htc))
      have hright : ∀ tc ∈ (clausesToThree (clauseToThree base c.lits).2 rest).1,
          tc.Satisfied σ :=
        fun tc htc => hsat tc (by
          rw [clausesToThree_cons]
          exact List.mem_append.mpr (Or.inr htc))
      cases hd with
      | head =>
          simpa [Clause.Satisfied] using clauseToThree_reflect base c.lits σ hleft
      | tail _ hd' =>
          exact ih _ hright d hd'

/-! ## Forward: original SAT extends to the 3CNF -/

lemma splitTail_forward_nil (base : ℕ) (carry : Literal) (τ : Literal.Assignment)
    (hsat : carry.eval τ = true) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (splitTail base carry []).1, c.Satisfied τ' := by
  refine ⟨τ, fun _ _ => rfl, ?_⟩
  intro c hc
  rw [splitTail_nil] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact (repeat1_iff _ _).mpr hsat

lemma splitTail_forward_one (base : ℕ) (carry l : Literal) (τ : Literal.Assignment)
    (hsat : carry.eval τ = true ∨ l.eval τ = true) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (splitTail base carry [l]).1, c.Satisfied τ' := by
  refine ⟨τ, fun _ _ => rfl, ?_⟩
  intro c hc
  rw [splitTail_one] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  simp [ThreeClause.Satisfied]
  exact hsat

lemma splitTail_forward_two (base : ℕ) (carry l1 l2 : Literal) (τ : Literal.Assignment)
    (hsat : carry.eval τ = true ∨ l1.eval τ = true ∨ l2.eval τ = true) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (splitTail base carry [l1, l2]).1, c.Satisfied τ' := by
  refine ⟨τ, fun _ _ => rfl, ?_⟩
  intro c hc
  rw [splitTail_two] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  simpa [ThreeClause.Satisfied] using hsat

lemma or_exists_cons {τ : Literal.Assignment} {l : Literal} {ls : List Literal} :
    (∃ x ∈ l :: ls, x.eval τ = true) ↔
      l.eval τ = true ∨ ∃ x ∈ ls, x.eval τ = true := by
  constructor
  · intro ⟨x, hx, he⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl he
    · exact Or.inr ⟨x, hx, he⟩
  · intro h
    rcases h with h | ⟨x, hx, he⟩
    · exact ⟨l, List.mem_cons_self, h⟩
    · exact ⟨x, List.mem_cons_of_mem _ hx, he⟩

lemma helper_prem {τ : Literal.Assignment} {base : ℕ} {ls : List Literal}
    (hls : ∀ l ∈ ls, l.var < base) :
    (Literal.neg base).eval (assignSet τ base (orLits τ ls)) = true ∨
      ∃ x ∈ ls, x.eval (assignSet τ base (orLits τ ls)) = true := by
  by_cases hy : orLits τ ls = true
  · refine Or.inr ?_
    obtain ⟨x, hx, hxev⟩ := (orLits_iff τ ls).mp hy
    refine ⟨x, hx, ?_⟩
    have := eval_assignSet_lt (τ := τ) (orLits τ ls) (hls x hx)
    exact this ▸ hxev
  · refine Or.inl ?_
    simp [eval_neg, assignSet, hy]

lemma splitTail_forward_long (base : ℕ) (carry l l2 l3 : Literal) (rest : List Literal)
    (τ : Literal.Assignment) (hls : ∀ x ∈ l :: l2 :: l3 :: rest, x.var < base)
    (hc : carry.var < base)
    (hsat : carry.eval τ = true ∨ ∃ x ∈ l :: l2 :: l3 :: rest, x.eval τ = true)
    (ih : ∀ (base' : ℕ) (carry' : Literal) (τ' : Literal.Assignment),
        (∀ x ∈ l2 :: l3 :: rest, x.var < base') →
        carry'.var < base' →
        (carry'.eval τ' = true ∨ ∃ x ∈ l2 :: l3 :: rest, x.eval τ' = true) →
        ∃ σ, (∀ v, v < base' → σ v = τ' v) ∧
          ∀ c ∈ (splitTail base' carry' (l2 :: l3 :: rest)).1, c.Satisfied σ) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (splitTail base carry (l :: l2 :: l3 :: rest)).1, c.Satisfied τ' := by
  set y := orLits τ (l2 :: l3 :: rest)
  set τ0 := assignSet τ base y
  have hrestb : ∀ x ∈ l2 :: l3 :: rest, x.var < base + 1 := by
    intro x hx
    exact Nat.lt_trans (hls x (mem_cons_of_mem_tail hx)) (Nat.lt_succ_self _)
  have hprem := helper_prem (τ := τ) (ls := l2 :: l3 :: rest)
    (fun x hx => hls x (mem_cons_of_mem_tail hx))
  obtain ⟨σ, hσag, hσsat⟩ :=
    ih (base + 1) (Literal.neg base) τ0 hrestb (by simp [var_neg]) hprem
  refine ⟨σ, ?_, ?_⟩
  · intro v hv
    have := hσag v (Nat.lt_trans hv (Nat.lt_succ_self _))
    exact this.trans (assignSet_lt y hv)
  · intro c hcm
    rw [splitTail_cons3] at hcm
    simp only [List.mem_cons] at hcm
    rcases hcm with rfl | hcm
    · have hcar : carry.eval σ = carry.eval τ :=
        eval_of_var_eq ((hσag carry.var (Nat.lt_trans hc (Nat.lt_succ_self _))).trans
          (assignSet_lt y hc))
      have hlv := hls l (by simp)
      have hl : l.eval σ = l.eval τ :=
        eval_of_var_eq ((hσag l.var (Nat.lt_trans hlv (Nat.lt_succ_self _))).trans
          (assignSet_lt y hlv))
      have hyσ : (Literal.pos base).eval σ = y := by
        have := hσag base (Nat.lt_succ_self _)
        simp [eval_pos, this, τ0, assignSet]
      apply three_of_or
      have hsat' : carry.eval τ = true ∨ l.eval τ = true ∨ y = true := by
        rcases hsat with h | h
        · exact Or.inl h
        · rw [or_exists_cons] at h
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ((orLits_iff _ _).mpr h))
      rcases hsat' with h | h | h
      · exact Or.inl (hcar ▸ h)
      · exact Or.inr (Or.inl (hl ▸ h))
      · exact Or.inr (Or.inr (hyσ ▸ h))
    · exact hσsat c hcm

lemma splitTail_forward (base : ℕ) (carry : Literal) (ls : List Literal)
    (τ : Literal.Assignment) (hls : ∀ l ∈ ls, l.var < base) (hc : carry.var < base)
    (hsat : carry.eval τ = true ∨ ∃ l ∈ ls, l.eval τ = true) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (splitTail base carry ls).1, c.Satisfied τ' := by
  induction ls generalizing base carry τ with
  | nil =>
      have : carry.eval τ = true := by
        simpa using hsat
      exact splitTail_forward_nil base carry τ this
  | cons l rest ih =>
      match rest with
      | [] =>
          have : carry.eval τ = true ∨ l.eval τ = true := by
            rw [or_exists_cons] at hsat
            simpa using hsat
          exact splitTail_forward_one base carry l τ this
      | [l2] =>
          have : carry.eval τ = true ∨ l.eval τ = true ∨ l2.eval τ = true := by
            rcases hsat with h | h
            · exact Or.inl h
            · rw [or_exists_cons] at h
              rcases h with h | h
              · exact Or.inr (Or.inl h)
              · have : l2.eval τ = true := by
                  rw [or_exists_cons] at h
                  simpa using h
                exact Or.inr (Or.inr this)
          exact splitTail_forward_two base carry l l2 τ this
      | l2 :: l3 :: rest' =>
          exact splitTail_forward_long base carry l l2 l3 rest' τ hls hc hsat ih

lemma clauseToThree_forward (base : ℕ) (ls : List Literal) (τ : Literal.Assignment)
    (hls : ∀ l ∈ ls, l.var < base) (hsat : Clause.Satisfied τ ⟨ls⟩) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (clauseToThree base ls).1, c.Satisfied τ' := by
  match ls with
  | [] => exact (Clause.not_satisfied_nil τ hsat).elim
  | [l] =>
      refine ⟨τ, fun _ _ => rfl, ?_⟩
      intro c hc
      rw [clauseToThree_one] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      obtain ⟨x, hx, hxev⟩ := hsat
      simp only [List.mem_singleton] at hx
      subst hx
      exact (repeat1_iff _ _).mpr hxev
  | [l1, l2] =>
      refine ⟨τ, fun _ _ => rfl, ?_⟩
      intro c hc
      rw [clauseToThree_two] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      obtain ⟨x, hx, hxev⟩ := hsat
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (repeat2_iff _ _ _).mpr (Or.inl hxev)
      · exact (repeat2_iff _ _ _).mpr (Or.inr hxev)
  | l1 :: l2 :: l3 :: rest =>
      set y := orLits τ (l3 :: rest)
      set τ0 := assignSet τ base y
      have hrestb : ∀ x ∈ l3 :: rest, x.var < base + 1 := by
        intro x hx
        exact Nat.lt_trans (hls x (mem_cons₂ hx)) (Nat.lt_succ_self _)
      have hprem := helper_prem (τ := τ) (ls := l3 :: rest)
        (fun x hx => hls x (mem_cons₂ hx))
      obtain ⟨σ, hσag, hσsat⟩ :=
        splitTail_forward (base + 1) (Literal.neg base) (l3 :: rest) τ0
          hrestb (by simp [var_neg]) hprem
      refine ⟨σ, ?_, ?_⟩
      · intro v hv
        have := hσag v (Nat.lt_trans hv (Nat.lt_succ_self _))
        exact this.trans (assignSet_lt y hv)
      · intro c hcm
        rw [clauseToThree_cons4] at hcm
        simp only [List.mem_cons] at hcm
        rcases hcm with rfl | hcm
        · have h1v := hls l1 (by simp)
          have h2v := hls l2 (by simp)
          have h1 : l1.eval σ = l1.eval τ :=
            eval_of_var_eq ((hσag l1.var (Nat.lt_trans h1v (Nat.lt_succ_self _))).trans
              (assignSet_lt y h1v))
          have h2 : l2.eval σ = l2.eval τ :=
            eval_of_var_eq ((hσag l2.var (Nat.lt_trans h2v (Nat.lt_succ_self _))).trans
              (assignSet_lt y h2v))
          have hyσ : (Literal.pos base).eval σ = y := by
            have := hσag base (Nat.lt_succ_self _)
            simp [eval_pos, this, τ0, assignSet]
          apply three_of_or
          obtain ⟨x, hx, hxev⟩ := hsat
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact Or.inl (h1 ▸ hxev)
          · exact Or.inr (Or.inl (h2 ▸ hxev))
          · exact Or.inr (Or.inr (hyσ ▸ (orLits_iff _ _).mpr
              ⟨x, List.mem_cons.mpr hx, hxev⟩))
        · exact hσsat c hcm

lemma satisfied_of_eval_eq {τ σ : Literal.Assignment} {c : Clause}
    (h : ∀ l ∈ c.lits, l.eval τ = l.eval σ) :
    c.Satisfied τ ↔ c.Satisfied σ := by
  constructor
  · intro ⟨l, hl, he⟩; exact ⟨l, hl, (h l hl) ▸ he⟩
  · intro ⟨l, hl, he⟩; exact ⟨l, hl, (h l hl).symm ▸ he⟩

lemma clausesToThree_forward (base : ℕ) (cs : List Clause) (τ : Literal.Assignment)
    (hcs : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var < base)
    (hsat : ∀ c ∈ cs, c.Satisfied τ) :
    ∃ τ', (∀ v, v < base → τ' v = τ v) ∧
      ∀ c ∈ (clausesToThree base cs).1, c.Satisfied τ' := by
  induction cs generalizing base τ with
  | nil => exact ⟨τ, fun _ _ => rfl, fun c hc => by cases hc⟩
  | cons c rest ih =>
      have hcbound : ∀ l ∈ c.lits, l.var < base := fun l hl => hcs c (by simp) l hl
      obtain ⟨τ1, h1ag, h1sat⟩ :=
        clauseToThree_forward base c.lits τ hcbound (hsat c (by simp))
      have hrestb : ∀ d ∈ rest, ∀ l ∈ d.lits, l.var < (clauseToThree base c.lits).2 := by
        intro d hd l hl
        exact lt_of_lt_of_le (hcs d (List.mem_cons_of_mem _ hd) l hl)
          (clauseToThree_base_le _ _)
      have hrestsat : ∀ d ∈ rest, d.Satisfied τ1 := by
        intro d hd
        refine (satisfied_of_eval_eq (fun l hl => ?_)).mp (hsat d (List.mem_cons_of_mem _ hd))
        exact eval_of_var_eq (h1ag l.var (hcs d (List.mem_cons_of_mem _ hd) l hl)).symm
      obtain ⟨τ2, h2ag, h2sat⟩ := ih (clauseToThree base c.lits).2 τ1 hrestb hrestsat
      refine ⟨τ2, ?_, ?_⟩
      · intro v hv
        have hv' : v < (clauseToThree base c.lits).2 :=
          lt_of_lt_of_le hv (clauseToThree_base_le _ _)
        exact (h2ag v hv').trans (h1ag v hv)
      · intro tc htc
        rw [clausesToThree_cons] at htc
        rcases List.mem_append.mp htc with htc | htc
        · have hsat1 := h1sat tc htc
          have hvars := clauseToThree_var_lt base c.lits hcbound tc htc
          have heq1 : tc.l1.eval τ1 = tc.l1.eval τ2 :=
            eval_of_var_eq (h2ag tc.l1.var (hvars tc.l1 (by simp [ThreeClause.literals]))).symm
          have heq2 : tc.l2.eval τ1 = tc.l2.eval τ2 :=
            eval_of_var_eq (h2ag tc.l2.var (hvars tc.l2 (by simp [ThreeClause.literals]))).symm
          have heq3 : tc.l3.eval τ1 = tc.l3.eval τ2 :=
            eval_of_var_eq (h2ag tc.l3.var (hvars tc.l3 (by simp [ThreeClause.literals]))).symm
          exact (three_satisfied_of_eval_eq heq1 heq2 heq3).mp hsat1
        · exact h2sat tc htc

lemma sat_iff_threeSAT (φ : CNF) : SAT φ ↔ ThreeSAT (toThreeCNF φ) := by
  constructor
  · intro ⟨τ, hτ⟩
    obtain ⟨τ', _, hsat⟩ :=
      clausesToThree_forward (cnfVarBound φ) φ.clauses τ
        (fun c hc l hl => var_lt_clausesVarBound hc hl) hτ
    exact ⟨τ', by simpa [toThreeCNF, ThreeCNF.Satisfied] using hsat⟩
  · intro ⟨τ, hτ⟩
    refine ⟨τ, ?_⟩
    intro c hc
    exact clausesToThree_reflect (cnfVarBound φ) φ.clauses τ
      (by simpa [toThreeCNF, ThreeCNF.Satisfied] using hτ) c hc

/-! ## Size of the rewrite -/

lemma splitTail_length_le (base : ℕ) (carry : Literal) (ls : List Literal) :
    (splitTail base carry ls).1.length ≤ ls.length + 1 := by
  induction ls generalizing base carry with
  | nil => rw [splitTail_nil]; simp
  | cons l rest ih =>
      match rest with
      | [] => rw [splitTail_one]; simp
      | [l2] => rw [splitTail_two]; simp
      | l2 :: l3 :: rest' =>
          rw [splitTail_cons3, List.length_cons]
          exact Nat.succ_le_succ (ih _ _)

lemma clauseToThree_length_le (base : ℕ) (ls : List Literal) :
    (clauseToThree base ls).1.length ≤ ls.length + 2 := by
  match ls with
  | [] => rw [clauseToThree_nil]; simp
  | [l] => rw [clauseToThree_one]; simp
  | [l1, l2] => rw [clauseToThree_two]; simp
  | l1 :: l2 :: l3 :: rest =>
      rw [clauseToThree_cons4, List.length_cons]
      have := splitTail_length_le (base + 1) (Literal.neg base) (l3 :: rest)
      simp only [List.length_cons] at this ⊢
      omega

lemma splitTail_helpers_le (base : ℕ) (carry : Literal) (ls : List Literal) :
    (splitTail base carry ls).2 ≤ base + ls.length := by
  induction ls generalizing base carry with
  | nil => rw [splitTail_nil]; simp
  | cons l rest ih =>
      match rest with
      | [] => rw [splitTail_one]; simp
      | [l2] => rw [splitTail_two]; simp
      | l2 :: l3 :: rest' =>
          rw [splitTail_cons3]
          have := ih (base + 1) (Literal.neg base)
          simp only [List.length_cons] at this ⊢
          omega

lemma clauseToThree_helpers_le (base : ℕ) (ls : List Literal) :
    (clauseToThree base ls).2 ≤ base + ls.length + 1 := by
  match ls with
  | [] => rw [clauseToThree_nil]; omega
  | [l] => rw [clauseToThree_one]; omega
  | [l1, l2] => rw [clauseToThree_two]; omega
  | l1 :: l2 :: l3 :: rest =>
      rw [clauseToThree_cons4]
      have := splitTail_helpers_le (base + 1) (Literal.neg base) (l3 :: rest)
      simp only [List.length_cons] at this ⊢
      omega

lemma clausesToThree_length_le (base : ℕ) (cs : List Clause) :
    (clausesToThree base cs).1.length ≤
      (cs.map (fun c => c.lits.length + 2)).sum := by
  induction cs generalizing base with
  | nil => rw [clausesToThree_nil]; simp
  | cons c rest ih =>
      rw [clausesToThree_cons, List.length_append, List.map_cons, List.sum_cons]
      have h1 := clauseToThree_length_le base c.lits
      have h2 := ih (clauseToThree base c.lits).2
      omega

lemma clausesToThree_numVars_le (base : ℕ) (cs : List Clause) :
    (clausesToThree base cs).2 ≤
      base + (cs.map (fun c => c.lits.length + 1)).sum := by
  induction cs generalizing base with
  | nil => rw [clausesToThree_nil]; simp
  | cons c rest ih =>
      rw [clausesToThree_cons, List.map_cons, List.sum_cons]
      have h1 := clauseToThree_helpers_le base c.lits
      have h2 := ih (clauseToThree base c.lits).2
      omega

lemma toThreeCNF_clauses_length_le (φ : CNF) :
    (toThreeCNF φ).clauses.length ≤
      (φ.clauses.map (fun c => c.lits.length + 2)).sum := by
  simpa [toThreeCNF] using clausesToThree_length_le (cnfVarBound φ) φ.clauses

lemma toThreeCNF_numVars_le (φ : CNF) :
    (toThreeCNF φ).numVars ≤
      cnfVarBound φ + (φ.clauses.map (fun c => c.lits.length + 1)).sum := by
  simpa [toThreeCNF, cnfVarBound] using
    clausesToThree_numVars_le (cnfVarBound φ) φ.clauses


end NPComplete.CookLevin

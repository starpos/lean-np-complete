module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableFrame
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafKinds
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseFamilyAccept
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseLeafAtLeastOne
public import NPComplete.CookLevin.Tableau.NatTableau

/-!
The accept family is the only one whose *cell* variable depends on a tape symbol
rather than on a loop index: the clause at window positions `(pHead, p)` names
the cell holding whatever the output word carries at offset `p - pHead`.  That
offset is signed, and the word is a list — neither of which the expression
language has.

Both reduce, though.  The sign test on a difference of two window positions is
the comparison `pHead ≤ p`, and the word lives in the store, read through
`wordReadE`.  So the family's variable numbers stay expressions, at the cost of
one extra hypothesis: the word must sit below the write pointer, where the
producer stages it before any clause is written.

The time index is the constant `T` throughout — the accept clauses all live on
the tableau's last row — so unlike the other families nothing here reads a time
counter.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## Variable expressions

`pHead` is the outer counter and `p` the inner one, matching the family's own
nesting.  The head variable reads only the outer counter; the cell variable reads
both, plus the staged word. -/

/-- `head T pHead`, over the outer counter. -/
def acceptHeadE (n W m T : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (.const T) (ctlCell lvJ0)

/-- `cell T p s`, where `s` is the output word's symbol at offset `p - pHead`.
The word's length is a compile-time constant, since the producer is chosen per
machine descriptor — which is what bounds the read address statically. -/
def acceptCellE (n W m T outBase blank outLen : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (.const T) (ctlCell lvJ1)
    (symbolAtE outBase blank outLen (ctlCell lvJ1) (ctlCell lvJ0))

/-! ## Frame conditions

The head expression reads only control cells, so the control-block lemma covers
it.  The cell expression also reads the staged word, so it needs the stronger
"agree below the pointer" form — the one `writeClauseProg_eval_state` asks of a
literal expression. -/

lemma acceptHeadE_frame (M n W m T : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (acceptHeadE n W m T).eval σ' = (acceptHeadE n W m T).eval σ := by
  unfold acceptHeadE
  rw [denseHeadE_eval, denseHeadE_eval]
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree]

/-- The head expression under the below-the-pointer form, which is what the
family's leaf actually passes, since the two literals of one clause share a
single frame hypothesis. -/
lemma acceptHeadE_frame_below (M n W m T bound : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hbound : M + ctlJmax < bound)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (acceptHeadE n W m T).eval σ' = (acceptHeadE n W m T).eval σ :=
  acceptHeadE_frame M n W m T σ σ' hσ hσ'
    (fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega))

lemma acceptCellE_frame_below (M n W m T outBase blank outLen bound : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hbound : M + ctlJmax < bound)
    (hw : WordBelow outBase outLen bound) (hbase : M + ctlJmax < outBase)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (acceptCellE n W m T outBase blank outLen).eval σ'
      = (acceptCellE n W m T outBase blank outLen).eval σ := by
  have hctl : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  have e0 := ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hctl
  have e1 := ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hctl
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl rfl e1
    (symbolAtE_frame outBase blank outLen bound (M + wpJ) _ _ σ σ' hw
      (fun k _ => (word_ne_ctl M outBase k hbase).1) hagree e1 e0)

/-! ## Values

With the outer counter pinned and the inner one holding the iteration index, the
expressions are the layout's own numbers — the symbol read included, by
`symbolAtE_eval` at the staged word. -/

lemma acceptHeadE_value (M n W m T pHead : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins1 pHead) τ) (h0 : τ 0 = M) :
    (acceptHeadE n W m T).eval τ = (denseLayout n W m).head T pHead := by
  have e0 : (ctlCell lvJ0).eval τ = pHead :=
    ctlCell_eval_of_pin M (ctlPins1 pHead) lvJ0 pHead τ (by simp [ctlPins1]) hF h0
  unfold acceptHeadE
  rw [denseHeadE_eval, e0]
  simp [Expr.eval]

lemma acceptCellE_value (M n W m T outBase blank pHead : ℕ) (τ : Store) (p : ℕ)
    (outIdx : List ℕ) (hF : PinsHold M (ctlPins1 pHead) τ) (h0 : τ 0 = M)
    (hp : τ (M + lvJ1) = p) (hw : WordAt τ outBase outIdx) :
    (acceptCellE n W m T outBase blank outIdx.length).eval τ
      = (denseLayout n W m).cell T p (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))) := by
  have e0 : (ctlCell lvJ0).eval τ = pHead :=
    ctlCell_eval_of_pin M (ctlPins1 pHead) lvJ0 pHead τ (by simp [ctlPins1]) hF h0
  have e1 : (ctlCell lvJ1).eval τ = p := by rw [ctlCell_eval, h0]; exact hp
  have hsym := symbolAtE_eval τ outBase blank outIdx (ctlCell lvJ1) (ctlCell lvJ0) hw
  rw [e1, e0] at hsym
  unfold acceptCellE
  rw [denseCellE_eval]
  simp only [Expr.eval, e1, hsym]


/-! ## The staged word survives a clause write

A clause writer touches its control cells and the row it writes, both outside the
region the word occupies, so the word is still there afterwards.  Establishing
that separately is what lets the leaf below return a `Frozen` that still carries
the word — the property an outer loop needs in order to run the leaf again. -/

lemma accept_word_preserved (M Jmax outBase wp : ℕ) (outIdx : List ℕ) (τ σ2 : Store)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax)
    (hJ : ctlJmax ≤ Jmax) (hsep : M + Jmax < wp)
    (hword : WordAt τ outBase outIdx)
    (hagree : ∀ r, r < wp → r ≠ M + wpJ → σ2 r = τ r) :
    WordAt σ2 outBase outIdx := by
  have hmax : ctlJmax = 7 := rfl
  have hwp1 : wpJ = 1 := rfl
  have hctlwp : M + ctlJmax < wp :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hJ M) hsep
  obtain ⟨hlen, hdata⟩ := hword
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hagree (outBase - 1) (by omega) (by omega)]; exact hlen
  · rw [hagree (outBase + k) (by omega) (by omega)]; exact hdata k hk


/-! ## Combinators under `PinsAndWord`

`clauseWriter_forN` and `clauseLoopBody_of_writer` freeze only `PinsHold`.
The accept family also freezes the staged output word, so the same two jobs —
a counter bump, a whole `forN` — are restated here with `PinsAndWord` as
`Frozen`. -/

lemma pinsAndWord_cons (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ))
    (base : ℕ) (xs : List ℕ) (τ : Store)
    (h1 : τ (M + p.1) = p.2) (h : PinsAndWord M pins base xs τ) :
    PinsAndWord M (p :: pins) base xs τ :=
  ⟨pinsHold_cons M p pins τ h1 h.1, h.2⟩

lemma pinsAndWord_tail (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ))
    (base : ℕ) (xs : List ℕ) (τ : Store)
    (h : PinsAndWord M (p :: pins) base xs τ) :
    PinsAndWord M pins base xs τ :=
  ⟨pinsHold_tail M p pins τ h.1, h.2⟩

lemma pinsAndWord_writeReg (M : ℕ) (pins : List (ℕ × ℕ))
    (base : ℕ) (xs : List ℕ) (addr v : ℕ) (τ : Store)
    (h : PinsAndWord M pins base xs τ)
    (hpins : ∀ p ∈ pins, M + p.1 ≠ addr)
    (hne1 : base - 1 ≠ addr) (hne2 : ∀ k, k < xs.length → base + k ≠ addr) :
    PinsAndWord M pins base xs (writeReg τ addr v) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [writeReg_diff τ addr v (M + p.1) (hpins p hp)]
    exact h.1 p hp
  · exact ⟨by rw [writeReg_diff τ addr v (base - 1) hne1]; exact h.2.1,
      fun k hk => by
        rw [writeReg_diff τ addr v (base + k) (hne2 k hk)]; exact h.2.2 k hk⟩

lemma pinsAndWord_writeReg_loop (M : ℕ) (pins : List (ℕ × ℕ))
    (base : ℕ) (xs : List ℕ) (iJ v : ℕ) (τ : Store)
    (h : PinsAndWord M pins base xs τ) (hiJ : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, M + p.1 ≠ M + iJ)
    (hbase : M + ctlJmax < base) :
    PinsAndWord M pins base xs (writeReg τ (M + iJ) v) := by
  have hc : ctlJmax = 7 := rfl
  have h3 : lvJ3 = 5 := rfl
  have haddr : M + iJ < M + ctlJmax := by omega
  refine pinsAndWord_writeReg M pins base xs (M + iJ) v τ h hpin
    (word_len_disjoint_ctl M base (M + iJ) hbase haddr)
    (fun k _ => word_disjoint_ctl M base (M + iJ) k hbase haddr)

lemma clauseLoopBody_of_writer_word (prog : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause)
    (base : ℕ) (xs : List ℕ)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ) (hiJctl : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hbase : M + ctlJmax < base)
    (hw : ∀ i, ClauseWriter prog M Jmax wpJ
      (PinsAndWord M ((iJ, i) :: pins) base xs) (g i)) :
    ClauseLoopBody (.seq prog (ctlAssign iJ (.add (ctlCell iJ) (.const 1))))
      M Jmax wpJ iJ (PinsAndWord M pins base xs) g := by
  intro τ i wp hF h0 hi hwp hsep
  have hpins : PinsAndWord M ((iJ, i) :: pins) base xs τ :=
    pinsAndWord_cons M (iJ, i) pins base xs τ hi hF
  obtain ⟨a1, a2, a3, a4, a5⟩ := hw i τ wp hpins h0 hwp hsep
  set σ1 := prog.eval τ with hσ1def
  have hσ1i : σ1 (M + iJ) = i := pinsHold_head M (iJ, i) pins σ1 a1.1
  set σ2 := (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1))).eval σ1 with hσ2def
  have hσ2eq : σ2 = writeReg σ1 (M + iJ) (i + 1) := by
    rw [hσ2def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, a2]
    congr 1
    simp [Expr.eval, ctlCell_eval, a2, hσ1i]
  have hgoal : (Program.seq prog (ctlAssign iJ (Expr.add (ctlCell iJ) (Expr.const 1)))).eval τ
      = σ2 := by rw [hσ2def, hσ1def, eval_seq]
  rw [hgoal]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ2eq]
    exact pinsAndWord_writeReg_loop M pins base xs iJ (i + 1) σ1
      (pinsAndWord_tail M (iJ, i) pins base xs σ1 a1) hiJctl
      (fun p hp => by obtain ⟨_, _, hpne, _⟩ := hpin p hp; omega) hbase
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) 0 (by omega), a2]
  · rw [hσ2eq, writeReg_same]
  · rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) (M + wpJ) (by omega), a3]
  · exact rowsWritten_of_agree σ1 σ2 wp (g i) a4
      (fun r h1 _ => by rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r (by omega)])
  · intro r hr1 hr2
    have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
    rw [hσ2eq, writeReg_diff σ1 (M + iJ) (i + 1) r hrne]
    exact a5 r hr1 hr2

lemma clauseWriter_forN_word (body : Program) (M Jmax wpJ iJ : ℕ)
    (pins : List (ℕ × ℕ)) (g : ℕ → List Clause) (cntE : Expr) (n : ℕ)
    (base : ℕ) (xs : List ℕ)
    (hiJ : 1 ≤ iJ) (hiJmax : iJ ≤ Jmax) (hne : iJ ≠ wpJ) (hiJctl : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ iJ ∧ p.1 ≠ wpJ)
    (hbase : M + ctlJmax < base)
    (hbody : ClauseLoopBody body M Jmax wpJ iJ (PinsAndWord M pins base xs) g)
    (hcnt : ∀ τ : Store, τ 0 = M → PinsAndWord M pins base xs τ → τ (M + iJ) = 0 →
      cntE.eval τ = n) :
    ClauseWriter (loopProg iJ cntE body) M Jmax wpJ (PinsAndWord M pins base xs)
      ((List.range n).flatMap g) := by
  intro τ wp hF h0 hw hsep
  set σ1 := (ctlAssign iJ (Expr.const 0)).eval τ with hσ1def
  have hσ1eq : σ1 = writeReg τ (M + iJ) 0 := by
    rw [hσ1def]; unfold ctlAssign
    rw [eval_assignInd, ctlAddr_eval, h0]; rfl
  have hσ10 : σ1 0 = M := by
    rw [hσ1eq, writeReg_diff τ (M + iJ) 0 0 (by omega), h0]
  have hσ1i : σ1 (M + iJ) = 0 := by rw [hσ1eq, writeReg_same]
  have hσ1w : σ1 (M + wpJ) = wp := by
    rw [hσ1eq, writeReg_diff τ (M + iJ) 0 (M + wpJ) (by omega), hw]
  have hσ1F : PinsAndWord M pins base xs σ1 := by
    rw [hσ1eq]
    exact pinsAndWord_writeReg_loop M pins base xs iJ 0 τ hF hiJctl
      (fun p hp => by obtain ⟨_, _, hpne, _⟩ := hpin p hp; omega) hbase
  obtain ⟨s1, s2, _, s4, s5, s6⟩ :=
    rowsWritten_forN body M Jmax wpJ iJ (PinsAndWord M pins base xs) g cntE n wp σ1 hbody
      hσ1F hσ10 hσ1i hσ1w (hcnt σ1 hσ10 hσ1F hσ1i) hsep
  have hgoal : (loopProg iJ cntE body).eval τ = (Program.forN cntE body).eval σ1 := by
    rw [hσ1def]; unfold loopProg; rw [eval_seq]
  rw [hgoal]
  refine ⟨s1, s2, s4, s5, ?_⟩
  intro r hr1 hr2
  have hrne : r ≠ M + iJ := by rcases hr2 with h | h <;> omega
  rw [s6 r hr1 hr2, hσ1eq, writeReg_diff τ (M + iJ) 0 r hrne]

/-! ## Closing the inner loop

The leaf freezes only the outer counter, reading `p` off `lvJ1` as a
hypothesis.  A loop iteration pins that cell, so the same program is a writer
under `ctlPins2`; wrapping it in `forN` on `lvJ1` then writes the whole `W`-wide
map, once the family's `map` is restated as a `flatMap` of singletons. -/

lemma accept_leaf_writer_pinned (M Jmax n W m T outBase blank pHead p : ℕ)
    (outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (writeClauseProg wpJ
        (implyPosLits (acceptHeadE n W m T)
          (acceptCellE n W m T outBase blank outIdx.length)))
      M Jmax wpJ (PinsAndWord M (ctlPins2 pHead p) outBase outIdx)
      [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))] := by
  intro τ wp hF h0 hw hsep
  have hmax : ctlJmax = 7 := rfl
  have hwp1 : wpJ = 1 := rfl
  have hlv0 : lvJ0 = 2 := rfl
  have hlv1 : lvJ1 = 3 := rfl
  have hpins2 : PinsHold M (ctlPins2 pHead p) τ := hF.1
  have hpins : PinsHold M (ctlPins1 pHead) τ :=
    pinsHold_tail M (lvJ1, p) (ctlPins1 pHead) τ (by simpa [ctlPins2, ctlPins1] using hpins2)
  have hword : WordAt τ outBase outIdx := hF.2
  have hpval : τ (M + lvJ1) = p :=
    pinsHold_head M (lvJ1, p) (ctlPins1 pHead) τ (by simpa [ctlPins2, ctlPins1] using hpins2)
  have hctlwp : M + ctlJmax < wp := by omega
  have hbelow : WordBelow outBase outIdx.length wp := ⟨by omega, by omega⟩
  have hinv : ∀ q ∈ implyPosLits (acceptHeadE n W m T)
        (acceptCellE n W m T outBase blank outIdx.length),
      ∀ σ σ' : Store, σ 0 = M → σ' 0 = M → (∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) →
      q.1.eval σ' = q.1.eval σ ∧ q.2.eval σ' = q.2.eval σ := by
    intro q hq σ σ' hσ hσ' hagree
    simp only [implyPosLits, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨rfl, acceptHeadE_frame_below M n W m T wp σ σ' hσ hσ' hctlwp hagree⟩
    · exact ⟨rfl, acceptCellE_frame_below M n W m T outBase blank outIdx.length wp
        σ σ' hσ hσ' hctlwp hbelow hbase hagree⟩
  obtain ⟨w1, w2, w3, w4, w5⟩ :=
    writeClauseProg_eval_state wpJ _ M wp τ (by omega) h0 hw (by omega) hinv
  refine ⟨⟨?_, ?_⟩, w4, ?_, ?_, ?_⟩
  · intro q hq
    simp only [ctlPins2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [w5 (M + lvJ1) (by omega) (by omega)]; exact hpval
    · rw [w5 (M + lvJ0) (by omega) (by omega)]
      exact hpins (lvJ0, pHead) (by simp [ctlPins1])
  · exact accept_word_preserved M Jmax outBase wp outIdx τ _ hbase hfit hJ hsep hword w5
  · rw [w3, implyPosLits_length,
      show [implyPos ((denseLayout n W m).head T pHead)
        ((denseLayout n W m).cell T p
          (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))].length = 1 from rfl,
      rowTableWidth_singleton, implyPos_len]
  · refine rowsWritten_singleton _ wp _ ?_ ?_ ?_
    · rw [w1, implyPosLits_length, implyPos_len]
    · intro k hk
      rw [implyPos_len] at hk
      rw [(w2 k (by rw [implyPosLits_length]; exact hk)).1]
      interval_cases k
      · rw [implyPosLits_get0]; rfl
      · rw [implyPosLits_get1]; rfl
    · intro k hk
      rw [implyPos_len] at hk
      rw [(w2 k (by rw [implyPosLits_length]; exact hk)).2]
      interval_cases k
      · rw [implyPosLits_get0, implyPos_var0]
        exact acceptHeadE_value M n W m T pHead τ hpins h0
      · rw [implyPosLits_get1, implyPos_var1]
        exact acceptCellE_value M n W m T outBase blank pHead τ p outIdx hpins h0 hpval hword
  · intro r hr1 hr2
    exact w5 r hr1 (by rcases hr2 with h | h <;> omega)

def acceptInnerProg (n W m T outBase blank outLen : ℕ) : Program :=
  loopProg lvJ1 (.const W)
    (.seq (writeClauseProg wpJ
        (implyPosLits (acceptHeadE n W m T)
          (acceptCellE n W m T outBase blank outLen)))
      (ctlAssign lvJ1 (.add (ctlCell lvJ1) (.const 1))))

lemma accept_p_loop_writer (M Jmax n W m T outBase blank pHead : ℕ) (outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptInnerProg n W m T outBase blank outIdx.length)
      M Jmax wpJ (PinsAndWord M (ctlPins1 pHead) outBase outIdx)
      ((List.range W).map fun p =>
        implyPos ((denseLayout n W m).head T pHead)
          ((denseLayout n W m).cell T p
            (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))) := by
  have hpin : ∀ q ∈ ctlPins1 pHead, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ1 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins1_ok pHead lvJ1 (by unfold lvJ0 lvJ1; omega) q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  rw [map_eq_flatMap_singleton]
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ1 (ctlPins1 pHead) _ (.const W) W
    outBase outIdx
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hJ)
    (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega)
    hpin hbase ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ1 (ctlPins1 pHead) _
    outBase outIdx
    (by unfold lvJ1; omega) (Nat.le_trans (by unfold lvJ1 ctlJmax; omega) hJ)
    (by unfold lvJ1 wpJ; omega) (by unfold lvJ1 lvJ3; omega)
    hpin hbase
    (fun p => accept_leaf_writer_pinned M Jmax n W m T outBase blank pHead p outIdx
      hJ hbase hfit)

/-! ## Closing the outer loop

The two-loop half of the family is then the same writer, run `W` times on
`lvJ0`.  Nothing is pinned above that level, so `Frozen` is `PinsAndWord` at
`ctlPins0`. -/

def acceptOuterProg (n W m T outBase blank outLen : ℕ) : Program :=
  loopProg lvJ0 (.const W)
    (.seq (acceptInnerProg n W m T outBase blank outLen)
      (ctlAssign lvJ0 (.add (ctlCell lvJ0) (.const 1))))

lemma accept_pHead_loop_writer (M Jmax n W m T outBase blank : ℕ) (outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptOuterProg n W m T outBase blank outIdx.length)
      M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx)
      ((List.range W).flatMap fun pHead =>
        (List.range W).map fun p =>
          implyPos ((denseLayout n W m).head T pHead)
            ((denseLayout n W m).cell T p
              (natInitSymbol blank outIdx ((p : ℤ) - (pHead : ℤ))))) := by
  have hpin : ∀ q ∈ ctlPins0, 1 ≤ q.1 ∧ q.1 ≤ Jmax ∧ q.1 ≠ lvJ0 ∧ q.1 ≠ wpJ := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := ctlPins0_ok lvJ0 q hq
    exact ⟨h1, Nat.le_trans h2 hJ, h3, h4⟩
  refine clauseWriter_forN_word _ M Jmax wpJ lvJ0 ctlPins0 _ (.const W) W
    outBase outIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase ?_ (fun _ _ _ _ => rfl)
  exact clauseLoopBody_of_writer_word _ M Jmax wpJ lvJ0 ctlPins0 _
    outBase outIdx
    (by unfold lvJ0; omega) (Nat.le_trans (by unfold lvJ0 ctlJmax; omega) hJ)
    (by unfold lvJ0 wpJ; omega) (by unfold lvJ0 lvJ3; omega)
    hpin hbase
    (fun pHead => accept_p_loop_writer M Jmax n W m T outBase blank pHead outIdx
      hJ hbase hfit)

/-! ## The halt-state clause

The family's last row is one `atLeastOne` over `descHaltStates`.  That list is
a compile-time constant of the descriptor, so the producer writes it as a
run-time-width clause whose count is the list's length and whose `k`-th
variable is `state T` at the list's `k`-th entry, read off the inner literal
counter.  The output word is not consulted, but it still travels in `Frozen`
so the two halves of the family share a predicate. -/

def listGetE : List ℕ → Expr → Expr
  | [], _ => .const 0
  | v :: vs, kE =>
      .add (.mul (.eq kE (.const 0)) (.const v))
        (.mul (.sub (.const 1) (.eq kE (.const 0)))
          (listGetE vs (.sub kE (.const 1))))

lemma listGetE_eval (qs : List ℕ) (kE : Expr) (σ : Store) :
    (listGetE qs kE).eval σ = qs.getD (kE.eval σ) 0 := by
  induction qs generalizing kE with
  | nil => rfl
  | cons v vs ih =>
    unfold listGetE
    simp only [Expr.eval]
    by_cases hz : kE.eval σ = 0
    · simp [hz]
    · simp only [hz]
      have hsub : (kE.sub (.const 1)).eval σ = kE.eval σ - 1 := by simp [Expr.eval]
      rw [ih, hsub]
      cases hval : kE.eval σ with
      | zero => exact (hz hval).elim
      | succ k => simp

def acceptHaltVarE (n W m T : ℕ) (qs : List ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (.const T) (listGetE qs (ctlCell litJ))

lemma acceptHaltVarE_frame_bound (M n W m T : ℕ) (qs : List ℕ) (σ1 σ2 : Store)
    (h1 : σ1 0 = M) (h2 : σ2 0 = M)
    (hagree : ∀ r, r < M + ctlJmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) :
    (acceptHaltVarE n W m T qs).eval σ1 = (acceptHaltVarE n W m T qs).eval σ2 := by
  unfold acceptHaltVarE
  rw [denseStateE_eval, denseStateE_eval, listGetE_eval, listGetE_eval]
  simp only [Expr.eval, ctlCell_eval, h1, h2]
  rw [hagree (M + litJ) (by unfold litJ ctlJmax; omega) (by unfold litJ wpJ; omega)]

lemma acceptHaltVarE_value (M n W m T : ℕ) (qs : List ℕ) (τ : Store) (k : ℕ)
    (h0 : τ 0 = M) (hk : τ (M + litJ) = k) :
    (acceptHaltVarE n W m T qs).eval τ
      = (denseLayout n W m).state T (qs.getD k 0) := by
  unfold acceptHaltVarE
  rw [denseStateE_eval, listGetE_eval]
  simp only [Expr.eval, ctlCell_eval, h0, hk]

lemma map_getD_of_lt (qs : List ℕ) (f : ℕ → ℕ) (k : ℕ) (hk : k < qs.length) :
    (qs.map f).getD k 0 = f (qs.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma pinsAndWord_writeReg_ctl (M : ℕ) (pins : List (ℕ × ℕ))
    (base : ℕ) (xs : List ℕ) (iJ v : ℕ) (τ : Store)
    (h : PinsAndWord M pins base xs τ) (hiJ : iJ < ctlJmax)
    (hpin : ∀ p ∈ pins, M + p.1 ≠ M + iJ)
    (hbase : M + ctlJmax < base) :
    PinsAndWord M pins base xs (writeReg τ (M + iJ) v) := by
  have hc : ctlJmax = 7 := rfl
  have haddr : M + iJ < M + ctlJmax := by omega
  refine pinsAndWord_writeReg M pins base xs (M + iJ) v τ h hpin
    (word_len_disjoint_ctl M base (M + iJ) hbase haddr)
    (fun k _ => word_disjoint_ctl M base (M + iJ) k hbase haddr)

lemma clauseWriter_atLeastOne_word (M Jmax iInner : ℕ) (cntE varE : Expr)
    (pins : List (ℕ × ℕ)) (vs : List ℕ) (base : ℕ) (xs : List ℕ)
    (hiIn : 1 ≤ iInner) (hne : iInner ≠ wpJ)
    (hiJctl : iInner < ctlJmax)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ ∧ p.1 ≠ iInner)
    (hbase : M + ctlJmax < base)
    (hfit : base + xs.length ≤ M + Jmax)
    (hcnt : ∀ τ : Store, PinsAndWord M pins base xs τ → τ 0 = M → cntE.eval τ = vs.length)
    (hcntE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → r ≠ M + iInner → σ1 r = σ2 r) →
      cntE.eval σ1 = cntE.eval σ2)
    (hvarE : ∀ σ1 σ2 : Store, σ1 0 = M → σ2 0 = M →
      (∀ r, r < M + Jmax + 1 → r ≠ M + wpJ → σ1 r = σ2 r) → varE.eval σ1 = varE.eval σ2)
    (hvar : ∀ (τ : Store) (k : ℕ), PinsAndWord M pins base xs τ → τ 0 = M →
      τ (M + iInner) = k → k < vs.length → varE.eval τ = vs.getD k 0) :
    ClauseWriter (writeAtLeastOneProg wpJ iInner cntE varE) M Jmax wpJ
      (PinsAndWord M pins base xs) [atLeastOne vs] := by
  intro τ wp hF h0 hw hsep
  have hmax : ctlJmax = 7 := rfl
  have hwp1 : wpJ = 1 := rfl
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    writeAtLeastOneProg_eval_state wpJ iInner cntE varE M (M + Jmax + 1) wp τ
      (by omega) hiIn (Ne.symm hne) h0 hw (by omega) (by omega) (by omega) hcntE hvarE
  have hn : cntE.eval τ = vs.length := hcnt τ hF h0
  set σ2 := (writeAtLeastOneProg wpJ iInner cntE varE).eval τ with hσ2def
  have hwidth : rowTableWidth (rowW [atLeastOne vs]) [atLeastOne vs].length
      = 2 + 2 * vs.length := by
    rw [show [atLeastOne vs].length = 1 from rfl, rowTableWidth_singleton, atLeastOne_length]
  have hvarval : ∀ k, k < vs.length →
      varE.eval (writeReg τ (M + iInner) k) = vs.getD k 0 := by
    intro k hk
    refine hvar (writeReg τ (M + iInner) k) k
      (pinsAndWord_writeReg_ctl M pins base xs iInner k τ hF hiJctl
        (fun p hp => by have := (hpin p hp).2.2.2; omega) hbase)
      ?_ ?_ hk
    · rw [writeReg_diff τ (M + iInner) k 0 (by omega)]; exact h0
    · rw [writeReg_same]
  have hagree : ∀ r, r < wp → r ≠ M + wpJ → r ≠ M + iInner → σ2 r = τ r :=
    fun r hr1 hr2 hr3 => w6 r hr2 hr3 (Or.inl hr1)
  refine ⟨?_, w5, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨hp1, hp2, hpne, hpne2⟩ := hpin p hp
      rw [hagree (M + p.1) (by omega) (by omega) (by omega)]
      exact hF.1 p hp
    · obtain ⟨hlen, hdata⟩ := hF.2
      have hmax : ctlJmax = 7 := rfl
      have hb1 : 1 ≤ base := by omega
      refine ⟨?_, fun k hk => ?_⟩
      · rw [hagree (base - 1) (by omega) (by omega) (by omega)]; exact hlen
      · rw [hagree (base + k) (by omega) (by omega) (by omega)]; exact hdata k hk
  · rw [w3, hn, hwidth]; omega
  · refine rowsWritten_singleton σ2 wp (atLeastOne vs) ?_ ?_ ?_
    · rw [w1, hn, atLeastOne_length]
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [(w2 k (by rw [hn]; exact hk)).1, atLeastOne_tag vs k hk]
      rfl
    · intro k hk
      rw [atLeastOne_length] at hk
      rw [(w2 k (by rw [hn]; exact hk)).2, atLeastOne_var vs k hk]
      exact hvarval k hk
  · intro r hr1 hr2
    refine w6 r ?_ ?_ (Or.inl hr1)
    · rcases hr2 with h | h <;> omega
    · rcases hr2 with h | h <;> omega

def acceptHaltProg (n W m T : ℕ) (qs : List ℕ) : Program :=
  writeAtLeastOneProg wpJ litJ (.const qs.length) (acceptHaltVarE n W m T qs)

lemma accept_halt_writer (M Jmax n W m T outBase : ℕ) (outIdx qs : List ℕ)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter (acceptHaltProg n W m T qs)
      M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx)
      [atLeastOne (qs.map fun qi => (denseLayout n W m).state T qi)] := by
  have hpin : ∀ p ∈ ctlPins0,
      1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ ∧ p.1 ≠ litJ := by
    intro p hp; exact absurd hp (List.not_mem_nil)
  refine clauseWriter_atLeastOne_word M Jmax litJ (.const qs.length)
      (acceptHaltVarE n W m T qs) ctlPins0
      (qs.map fun qi => (denseLayout n W m).state T qi) outBase outIdx
      (by unfold litJ; omega)
      (by unfold litJ wpJ; omega) (by unfold litJ ctlJmax; omega)
      hpin hbase hfit
      (fun τ _ _ => by simp [Expr.eval, List.length_map])
      (fun _ _ _ _ _ => rfl) ?_ ?_
  · intro σ1 σ2 h1 h2 hagree
    exact acceptHaltVarE_frame_bound M n W m T qs σ1 σ2 h1 h2
      (fun r hr1 hr2 => hagree r (by omega) hr2)
  · intro τ k hF h0 hk hlt
    have hlen : (qs.map fun qi => (denseLayout n W m).state T qi).length = qs.length :=
      by simp
    rw [acceptHaltVarE_value M n W m T qs τ k h0 hk, map_getD_of_lt]
    omega

def acceptFamilyProg (n W m T outBase blank outLen : ℕ) (qs : List ℕ) : Program :=
  .seq (acceptOuterProg n W m T outBase blank outLen) (acceptHaltProg n W m T qs)

lemma acceptFamilyProg_writer (M Jmax n W m T outBase : ℕ) (d : TableauDescriptor)
    (outIdx : List ℕ)
    (hJ : ctlJmax ≤ Jmax)
    (hbase : M + ctlJmax < outBase)
    (hfit : outBase + outIdx.length ≤ M + Jmax) :
    ClauseWriter
      (acceptFamilyProg n W m T outBase d.blankIdx outIdx.length
        (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)))
      M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx)
      (descAcceptClauses (denseLayout n W m) d outIdx W T) := by
  unfold descAcceptClauses acceptFamilyProg
  exact clauseWriter_seq _ _ M Jmax wpJ (PinsAndWord M ctlPins0 outBase outIdx) _ _
    (accept_pHead_loop_writer M Jmax n W m T outBase d.blankIdx outIdx hJ hbase hfit)
    (accept_halt_writer M Jmax n W m T outBase outIdx
      (descHaltStates d (natInitSymbol d.blankIdx outIdx 0)) hbase hfit)

end NPComplete.CookLevin

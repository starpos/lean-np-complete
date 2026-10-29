module

public import NPComplete.CookLevin.ReductionProg.Bounded.GeneratorBoundedWrite

/-!
A clause row is a count cell, a pointer bump, and one literal write per literal.
The literals are what make the induction non-trivial: each advances the pointer,
so the next one starts from a store the previous one produced, and the bound has
to be re-established there rather than assumed.

The list-level hypothesis `LitsBounded` is stated at *any* store with the right
control cells precisely so this induction can discharge it at each position
without carrying a frame condition per literal.  The pointer's arithmetic is the
only thing that changes down the list, and the tight envelope has to cover the
row's far end for the last literal's write to be bounded — hence the
`wp + 2 * lits.length ≤ S` shape of the entry condition.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The literal list -/

/-- One clause's literals, in order.  The conclusion carries the exit store's
    marker, pointer, and both envelopes, because the surrounding row and the next
    clause both start from exactly those. -/
lemma writeLitsProg_bounded (K S B M : ℕ) (lits : List (Expr × Expr)) :
    ∀ (wp : ℕ) (σ : Store), σ 0 = M → σ (M + wpJ) = wp → M + 24 < wp →
      M + 24 ≤ B → wp + 2 * lits.length ≤ S → S ≤ B →
      LitsBounded K S B M lits → TightCells K M σ → StoreValuesLe S σ →
      ProgramBoundedIn B σ (writeLitsProg wpJ lits) ∧
        (writeLitsProg wpJ lits).eval σ 0 = M ∧
        (writeLitsProg wpJ lits).eval σ (M + wpJ) = wp + 2 * lits.length ∧
        TightCells K M ((writeLitsProg wpJ lits).eval σ) ∧
        StoreValuesLe S ((writeLitsProg wpJ lits).eval σ) ∧
        (∀ r, r < wp → r ≠ M + wpJ → (writeLitsProg wpJ lits).eval σ r = σ r) := by
  induction lits with
  | nil =>
      intro wp σ h0 hwp _ _ _ _ _ ht hst
      refine ⟨trivial, ?_, ?_, ?_, ?_, fun r _ _ => ?_⟩ <;>
        simp only [writeLitsProg, eval_skip, List.length_nil, Nat.mul_zero, Nat.add_zero]
      · exact h0
      · exact hwp
      · exact ht
      · exact hst
  | cons q rest ih =>
      intro wp σ h0 hwp hsep hMB hlen hSB hlits ht hst
      obtain ⟨htag, _, htagK, _⟩ := hlits q List.mem_cons_self σ h0 ht hst
      obtain ⟨h0', ht', hst'⟩ :=
        writeReg_above_preserves K S M wp (q.1.eval σ) σ h0 hsep ht hst htagK
      obtain ⟨_, hvar', _, hvarK'⟩ := hlits q List.mem_cons_self _ h0' ht' hst'
      have hpb1 : ProgramBoundedIn B σ (writeLitProg wpJ q.1 q.2) :=
        programBoundedIn_writeLitProg B M wp σ q.1 q.2 h0 hwp hsep hMB
          (by simp only [List.length_cons] at hlen; omega) htag hvar'
      obtain ⟨e0, ew, et, es⟩ := writeLitProg_exit K S M wp σ q.1 q.2 h0 hwp hsep ht hst
        htagK hvarK' (by simp only [List.length_cons] at hlen; omega)
      obtain ⟨hpb2, f0, fw, ft, fs, ffr⟩ :=
        ih (wp + 2) ((writeLitProg wpJ q.1 q.2).eval σ) e0 ew (by omega) hMB
          (by simp only [List.length_cons] at hlen; omega) hSB (litsBounded_tail hlits) et es
      simp only [writeLitsProg, List.length_cons]
      rw [eval_seq]
      refine ⟨⟨hpb1, hpb2⟩, f0, by rw [fw]; omega, ft, fs, fun r hr hrne => ?_⟩
      rw [ffr r (by omega) hrne]
      exact writeLitProg_frame_below M wp σ q.1 q.2 h0 hwp hsep r hr hrne

/-! ## The row header

The count cell and the pointer bump run before the literals, so their effect has
to be computed rather than framed: the literals' entry pointer is the one this
prefix leaves behind. -/

lemma writeClauseProg_prefix_eval (M wp n : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) :
    (Program.seq (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const n))
        (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))).eval σ
      = writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2) := by
  have e1 : (Program.assignInd (.add (ctlCell wpJ) (.const 1)) (.const n)).eval σ
      = writeReg σ (wp + 1) n := by
    rw [eval_assignInd]; simp only [Expr.eval, ctlCell_eval, h0, hwp]
  have h10 : (writeReg σ (wp + 1) n) 0 = M := by
    rw [writeReg_diff σ (wp + 1) n 0 (by omega), h0]
  have h1w : (writeReg σ (wp + 1) n) (M + wpJ) = wp := by
    rw [writeReg_diff σ (wp + 1) n (M + wpJ) (by simp only [wpJ]; omega), hwp]
  rw [eval_seq, e1]
  unfold ctlAssign
  rw [eval_assignInd]
  simp only [Expr.eval, ctlAddr, ctlCell, h10, h1w]

lemma writeClauseProg_prefix_exit (K S M wp n : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) (hn : n ≤ S) (hwpK : wp + 2 ≤ S) :
    (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) 0 = M ∧
      (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) (M + wpJ) = wp + 2 ∧
      TightCells K M (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) ∧
      StoreValuesLe S (writeReg (writeReg σ (wp + 1) n) (M + wpJ) (wp + 2)) := by
  set σ1 := writeReg σ (wp + 1) n with hs1
  have h10 : σ1 0 = M := by rw [hs1, writeReg_diff σ (wp + 1) n 0 (by omega), h0]
  refine ⟨by rw [writeReg_diff σ1 (M + wpJ) (wp + 2) 0 (by simp only [wpJ]; omega), h10],
    writeReg_same _ _ _, ?_, fun i => ?_⟩
  · refine tightCells_of_frame ht (fun j h2 h24 => ?_)
    rw [writeReg_diff σ1 (M + wpJ) (wp + 2) (M + j) (by simp only [wpJ]; omega), hs1,
      writeReg_diff σ (wp + 1) n (M + j) (by omega)]
  · by_cases hi : i = M + wpJ
    · rw [hi, writeReg_same]; omega
    · rw [writeReg_diff σ1 (M + wpJ) (wp + 2) i hi, hs1]
      by_cases hi1 : i = wp + 1
      · rw [hi1, writeReg_same]; exact hn
      · rw [writeReg_diff σ (wp + 1) n i hi1]; exact hst i

lemma programBoundedIn_writeClauseProg_prefix (B M wp n : ℕ) (σ : Store)
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hn : n ≤ B) (hwpB : wp + 2 ≤ B) :
    ProgramBoundedIn B σ (.seq (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const n))
      (ctlAssign wpJ (.add (ctlCell wpJ) (.const 2)))) := by
  have hj : M + wpJ ≤ B := by simp only [wpJ]; omega
  have hhead : ProgramBoundedIn B σ
      (.assignInd (.add (ctlCell wpJ) (.const 1)) (.const n)) := by
    refine ⟨⟨exprBoundedIn_ctlCell B M wpJ σ h0 hj, by simp only [ExprBoundedIn]; omega, ?_⟩,
      by simp only [ExprBoundedIn]; omega, ?_⟩
    · simp only [Expr.eval, ctlCell_eval, h0, hwp]; omega
    · simp only [Expr.eval, ctlCell_eval, h0, hwp]; omega
  refine ⟨hhead, ?_⟩
  have e1 : (Program.assignInd (.add (ctlCell wpJ) (.const 1)) (.const n)).eval σ
      = writeReg σ (wp + 1) n := by
    rw [eval_assignInd]; simp only [Expr.eval, ctlCell_eval, h0, hwp]
  rw [e1]
  refine programBoundedIn_ctlAssign_bump B M wp wpJ 2 _ ?_ hj ?_ hwpB
  · rw [writeReg_diff σ (wp + 1) n 0 (by omega), h0]
  · rw [writeReg_diff σ (wp + 1) n (M + wpJ) (by simp only [wpJ]; omega), hwp]

/-! ## A whole clause row -/

/-- One clause: the header, then its literals.  The row occupies
    `2 + 2 * lits.length` cells, which is where the entry condition's shape comes
    from and what the exit pointer reports. -/
lemma writeClauseProg_bounded (K S B M wp : ℕ) (σ : Store) (lits : List (Expr × Expr))
    (h0 : σ 0 = M) (hwp : σ (M + wpJ) = wp) (hsep : M + 24 < wp) (hMB : M + 24 ≤ B)
    (hlen : wp + 2 + 2 * lits.length ≤ S) (hSB : S ≤ B)
    (hcnt : lits.length ≤ S) (hlits : LitsBounded K S B M lits)
    (ht : TightCells K M σ) (hst : StoreValuesLe S σ) :
    ProgramBoundedIn B σ (writeClauseProg wpJ lits) ∧
      (writeClauseProg wpJ lits).eval σ 0 = M ∧
      (writeClauseProg wpJ lits).eval σ (M + wpJ) = wp + 2 + 2 * lits.length ∧
      TightCells K M ((writeClauseProg wpJ lits).eval σ) ∧
      StoreValuesLe S ((writeClauseProg wpJ lits).eval σ) ∧
      (∀ r, r < wp → r ≠ M + wpJ → (writeClauseProg wpJ lits).eval σ r = σ r) := by
  have hpre := programBoundedIn_writeClauseProg_prefix B M wp lits.length σ h0 hwp hsep hMB
    (by omega) (by omega)
  have hev := writeClauseProg_prefix_eval M wp lits.length σ h0 hwp hsep
  obtain ⟨e0, ew, et, es⟩ := writeClauseProg_prefix_exit K S M wp lits.length σ h0 hwp hsep
    ht hst hcnt (by omega)
  rw [← hev] at e0 ew et es
  obtain ⟨hpb2, f0, fw, ft, fs, ffr⟩ := writeLitsProg_bounded K S B M lits (wp + 2) _ e0 ew
    (by omega) hMB (by omega) hSB hlits et es
  unfold writeClauseProg
  rw [eval_seq]
  refine ⟨⟨hpre, hpb2⟩, f0, by rw [fw], ft, fs, fun r hr hrne => ?_⟩
  rw [ffr r (by omega) hrne, hev,
    writeReg_diff _ (M + wpJ) (wp + 2) r hrne, writeReg_diff σ (wp + 1) _ r (by omega)]

end NPComplete.CookLevin

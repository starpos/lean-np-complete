module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableRead
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseWriteSeq

/-!
An expression that reads a word out of the store touches cells above the control
block, so the control-block frame lemma does not apply to it.  What does apply is
the condition `writeClauseProg_eval_state` asks of a literal expression: agreement
everywhere below the write pointer.  A word placed below the pointer is covered by
that, and this file states the frame lemma in exactly that shape.

Placing the word below the write pointer is not a free choice — the table grows
upward from the pointer, so anything the producer stages first and reads later
must sit below where writing starts.  That is the same discipline the control
block follows, one region further out.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-- The word at `base` with length `len` occupies `base - 1 .. base + len - 1`,
    all strictly below `bound`.  Stated as a predicate so a family carries one
    hypothesis rather than two inequalities per read. -/
def WordBelow (base len bound : ℕ) : Prop := 1 ≤ base ∧ base + len ≤ bound

lemma wordBelow_mono (base len b1 b2 : ℕ) (h : WordBelow base len b1) (hle : b1 ≤ b2) :
    WordBelow base len b2 :=
  ⟨h.1, Nat.le_trans h.2 hle⟩

/-- A word read is stable under agreement below a bound that covers the word,
    provided the index expression is too.  The write pointer is excluded from the
    agreement, so the word must not overlap it — which holds because the word is
    staged below the pointer and the pointer's own cell is in the control block.

    The length is the fixed argument `len`, not a store read, so `WordBelow base len bound` covers
    every cell the read can reach; `hne2` keeps those cells off the write pointer. -/
lemma wordReadE_frame (base blank len bound wpAddr : ℕ) (kE : Expr) (σ σ' : Store)
    (hw : WordBelow base len bound)
    (hne2 : ∀ k, k < len → base + k ≠ wpAddr)
    (hagree : ∀ r, r < bound → r ≠ wpAddr → σ' r = σ r)
    (hkE : kE.eval σ' = kE.eval σ) :
    (wordReadE base blank len kE).eval σ' = (wordReadE base blank len kE).eval σ := by
  obtain ⟨_hb1, hb2⟩ := hw
  unfold wordReadE
  simp only [Expr.eval, hkE]
  by_cases h : kE.eval σ < len
  · simp [h]
    rw [hagree (base + kE.eval σ) (by omega) (hne2 _ h)]
  · simp [h]

/-- The guarded symbol read inherits the same frame condition, since the guard is
    built from the two index expressions alone. -/
lemma symbolAtE_frame (base blank len bound wpAddr : ℕ) (pE qE : Expr) (σ σ' : Store)
    (hw : WordBelow base len bound)
    (hne2 : ∀ k, k < len → base + k ≠ wpAddr)
    (hagree : ∀ r, r < bound → r ≠ wpAddr → σ' r = σ r)
    (hpE : pE.eval σ' = pE.eval σ) (hqE : qE.eval σ' = qE.eval σ) :
    (symbolAtE base blank len pE qE).eval σ'
      = (symbolAtE base blank len pE qE).eval σ := by
  unfold symbolAtE
  simp only [Expr.eval, hpE, hqE]
  rw [wordReadE_frame base blank len bound wpAddr (.sub pE qE) σ σ' hw
    hne2 hagree (by simp only [Expr.eval, hpE, hqE])]

/-- A word staged below the write pointer, with the control block below it, meets
    the two disjointness conditions the frame lemma asks for: the pointer's own
    cell is inside the control block, and the word is above it. -/
lemma word_ne_ctl (M base k : ℕ) (hctl : M + ctlJmax < base) :
    base + k ≠ M + wpJ ∧ base - 1 ≠ M + wpJ := by
  have hw : wpJ = 1 := rfl
  have hmax : ctlJmax = 7 := rfl
  exact ⟨by omega, by omega⟩

lemma word_disjoint_ctl (M base addr k : ℕ)
    (hctl : M + ctlJmax < base) (haddr : addr < M + ctlJmax) :
    base + k ≠ addr := by
  have hmax : ctlJmax = 7 := rfl
  omega

lemma word_len_disjoint_ctl (M base addr : ℕ)
    (hctl : M + ctlJmax < base) (haddr : addr < M + ctlJmax) :
    base - 1 ≠ addr := by
  have hmax : ctlJmax = 7 := rfl
  omega

/-! ## Staged data belongs in `Frozen`

`PinsHold` pins control cells, which is all the arithmetic families need.  The
families that read a tape symbol or a transition entry also depend on a *word*
staged in the store, and that dependence has to travel the same way a pinned
counter does: as part of the `Frozen` predicate a writer carries and preserves.

Stating it separately as `∀ σ, WordAt σ base xs` would be worse than useless.
That is refuted by any store holding something else at those cells, so a lemma
assuming it proves nothing — its hypotheses can never all hold.  Bundling the
word into `Frozen` keeps it a claim about the stores the writer actually sees.
The bundle survives a write because the word sits above the control block and
below the entry pointer, where a clause writer does not reach. -/

/-- Control cells pinned as usual, together with a word staged at `base`.  This
is the `Frozen` predicate the table-reading families run under. -/
def PinsAndWord (M : ℕ) (pins : List (ℕ × ℕ)) (base : ℕ) (xs : List ℕ)
    (τ : Store) : Prop :=
  PinsHold M pins τ ∧ WordAt τ base xs

/-- A staged word survives any rewriting that leaves the cells below `bound`
    alone, except that the write pointer may sit below `bound`.  The word itself
    is required not to overlap that cell. -/
lemma wordAt_of_agree_ne (base : ℕ) (xs : List ℕ) (σ σ' : Store) (bound wpAddr : ℕ)
    (h : WordAt σ base xs) (hb : 1 ≤ base) (hbound : base + xs.length ≤ bound)
    (hne1 : base - 1 ≠ wpAddr) (hne2 : ∀ k, k < xs.length → base + k ≠ wpAddr)
    (hagree : ∀ r, r < bound → r ≠ wpAddr → σ' r = σ r) : WordAt σ' base xs := by
  obtain ⟨hlen, hdata⟩ := h
  exact ⟨by rw [hagree (base - 1) (by omega) hne1, hlen],
    fun k hk => by rw [hagree (base + k) (by omega) (hne2 k hk)]; exact hdata k hk⟩

/-- Control cells pinned, together with three staged words.  The transition
family reads three columns of one table, so they travel as a single `Frozen`
predicate rather than three independent `WordAt` hypotheses. -/
def PinsAndWords3 (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) : Prop :=
  PinsHold M pins τ ∧ WordAt τ basek xsk ∧ WordAt τ base1 xs1 ∧ WordAt τ base2 xs2

lemma pinsAndWords3_pins (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ) :
    PinsHold M pins τ := h.1

lemma pinsAndWords3_kind (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ) :
    WordAt τ basek xsk := h.2.1

lemma pinsAndWords3_arg1 (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ) :
    WordAt τ base1 xs1 := h.2.2.1

lemma pinsAndWords3_arg2 (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ) :
    WordAt τ base2 xs2 := h.2.2.2

lemma pinsAndWords3_cons (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h1 : τ (M + p.1) = p.2)
    (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ) :
    PinsAndWords3 M (p :: pins) basek xsk base1 xs1 base2 xs2 τ :=
  ⟨pinsHold_cons M p pins τ h1 h.1, h.2.1, h.2.2.1, h.2.2.2⟩

lemma pinsAndWords3_tail (M : ℕ) (p : ℕ × ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (τ : Store) (h : PinsAndWords3 M (p :: pins) basek xsk base1 xs1 base2 xs2 τ) :
    PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ :=
  ⟨pinsHold_tail M p pins τ h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A single-cell rewrite away from the three words and the pinned cells
    leaves `PinsAndWords3` intact.  Loop counter bumps are exactly this. -/
lemma pinsAndWords3_writeReg (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (addr v : ℕ) (τ : Store)
    (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ)
    (hpins : ∀ p ∈ pins, M + p.1 ≠ addr)
    (hnek1 : basek - 1 ≠ addr) (hnek2 : ∀ k, k < xsk.length → basek + k ≠ addr)
    (hne11 : base1 - 1 ≠ addr) (hne12 : ∀ k, k < xs1.length → base1 + k ≠ addr)
    (hne21 : base2 - 1 ≠ addr) (hne22 : ∀ k, k < xs2.length → base2 + k ≠ addr) :
    PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 (writeReg τ addr v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [writeReg_diff τ addr v (M + p.1) (hpins p hp)]
    exact h.1 p hp
  · exact ⟨by rw [writeReg_diff τ addr v (basek - 1) hnek1]; exact h.2.1.1,
      fun k hk => by
        rw [writeReg_diff τ addr v (basek + k) (hnek2 k hk)]; exact h.2.1.2 k hk⟩
  · exact ⟨by rw [writeReg_diff τ addr v (base1 - 1) hne11]; exact h.2.2.1.1,
      fun k hk => by
        rw [writeReg_diff τ addr v (base1 + k) (hne12 k hk)]; exact h.2.2.1.2 k hk⟩
  · exact ⟨by rw [writeReg_diff τ addr v (base2 - 1) hne21]; exact h.2.2.2.1,
      fun k hk => by
        rw [writeReg_diff τ addr v (base2 + k) (hne22 k hk)]; exact h.2.2.2.2 k hk⟩

/-- Offset past the control block *and* the three staged words, so
    `M + transJmax < wp` puts every table cell strictly below the write
    pointer.  Widening `Jmax` past `ctlJmax` is what makes `WordBelow` at
    the pointer a real arithmetic fact rather than a claim about every
    bound above the control block (which a nonempty word cannot satisfy). -/
def transJmax (M kindBase lenk arg1Base len1 arg2Base len2 : ℕ) : ℕ :=
  max ctlJmax (max (kindBase + lenk - M)
    (max (arg1Base + len1 - M) (arg2Base + len2 - M)))

lemma transJmax_ge_ctl (M kindBase lenk arg1Base len1 arg2Base len2 : ℕ) :
    ctlJmax ≤ transJmax M kindBase lenk arg1Base len1 arg2Base len2 :=
  Nat.le_max_left _ _

lemma wordBelow_transJmax_kind (M kindBase lenk arg1Base len1 arg2Base len2 bound : ℕ)
    (hb : 1 ≤ kindBase)
    (h : M + transJmax M kindBase lenk arg1Base len1 arg2Base len2 < bound) :
    WordBelow kindBase lenk bound := by
  refine ⟨hb, ?_⟩
  have hmax := transJmax_ge_ctl M kindBase lenk arg1Base len1 arg2Base len2
  unfold transJmax at h hmax
  omega

lemma wordBelow_transJmax_arg1 (M kindBase lenk arg1Base len1 arg2Base len2 bound : ℕ)
    (hb : 1 ≤ arg1Base)
    (h : M + transJmax M kindBase lenk arg1Base len1 arg2Base len2 < bound) :
    WordBelow arg1Base len1 bound := by
  refine ⟨hb, ?_⟩
  unfold transJmax at h
  omega

lemma wordBelow_transJmax_arg2 (M kindBase lenk arg1Base len1 arg2Base len2 bound : ℕ)
    (hb : 1 ≤ arg2Base)
    (h : M + transJmax M kindBase lenk arg1Base len1 arg2Base len2 < bound) :
    WordBelow arg2Base len2 bound := by
  refine ⟨hb, ?_⟩
  unfold transJmax at h
  omega

/-- `PinsAndWords3` specialized to the transition family's three columns.
    This is the `Frozen` predicate every trans writer carries. -/
abbrev TransFrozen (M : ℕ) (pins : List (ℕ × ℕ))
    (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) : Store → Prop :=
  PinsAndWords3 M pins kindBase colk arg1Base col1 arg2Base col2

/-- `transJmax` at the three columns' own lengths — the `Jmax` every trans
    writer uses, so `M + transJM < wp` covers the staged words. -/
abbrev transJM (M : ℕ) (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) : ℕ :=
  transJmax M kindBase colk.length arg1Base col1.length arg2Base col2.length

lemma transJM_ge_ctl (M : ℕ) (kindBase : ℕ) (colk : List ℕ) (arg1Base : ℕ) (col1 : List ℕ)
    (arg2Base : ℕ) (col2 : List ℕ) :
    ctlJmax ≤ transJM M kindBase colk arg1Base col1 arg2Base col2 :=
  transJmax_ge_ctl M kindBase colk.length arg1Base col1.length arg2Base col2.length

lemma transJM_wordBelow_kind (M : ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (hb : 1 ≤ kindBase) :
    WordBelow kindBase colk.length
      (M + transJM M kindBase colk arg1Base col1 arg2Base col2 + 1) :=
  wordBelow_transJmax_kind M kindBase colk.length arg1Base col1.length arg2Base col2.length
    _ hb (by unfold transJM; omega)

lemma transJM_wordBelow_arg1 (M : ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (hb : 1 ≤ arg1Base) :
    WordBelow arg1Base col1.length
      (M + transJM M kindBase colk arg1Base col1 arg2Base col2 + 1) :=
  wordBelow_transJmax_arg1 M kindBase colk.length arg1Base col1.length arg2Base col2.length
    _ hb (by unfold transJM; omega)

lemma transJM_wordBelow_arg2 (M : ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ)
    (hb : 1 ≤ arg2Base) :
    WordBelow arg2Base col2.length
      (M + transJM M kindBase colk arg1Base col1 arg2Base col2 + 1) :=
  wordBelow_transJmax_arg2 M kindBase colk.length arg1Base col1.length arg2Base col2.length
    _ hb (by unfold transJM; omega)

lemma transJM_bound_ctl (M : ℕ) (kindBase : ℕ) (colk : List ℕ)
    (arg1Base : ℕ) (col1 : List ℕ) (arg2Base : ℕ) (col2 : List ℕ) (bound : ℕ)
    (h : M + transJM M kindBase colk arg1Base col1 arg2Base col2 < bound) :
    M + ctlJmax < bound :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left
    (transJM_ge_ctl M kindBase colk arg1Base col1 arg2Base col2) M) h

lemma pinsAndWords3_of_agree_ne (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (σ σ' : Store) (bound wpAddr : ℕ)
    (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 σ)
    (hpk : 1 ≤ basek) (hbk : basek + xsk.length ≤ bound)
    (hp1 : 1 ≤ base1) (hb1 : base1 + xs1.length ≤ bound)
    (hp2 : 1 ≤ base2) (hb2 : base2 + xs2.length ≤ bound)
    (nek1 : basek - 1 ≠ wpAddr) (nek2 : ∀ k, k < xsk.length → basek + k ≠ wpAddr)
    (ne11 : base1 - 1 ≠ wpAddr) (ne12 : ∀ k, k < xs1.length → base1 + k ≠ wpAddr)
    (ne21 : base2 - 1 ≠ wpAddr) (ne22 : ∀ k, k < xs2.length → base2 + k ≠ wpAddr)
    (hpins : ∀ p ∈ pins, M + p.1 < bound ∧ M + p.1 ≠ wpAddr)
    (hagree : ∀ r, r < bound → r ≠ wpAddr → σ' r = σ r) :
    PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 σ' :=
  ⟨fun p hp => by
      obtain ⟨hb, hne⟩ := hpins p hp
      rw [hagree (M + p.1) hb hne]; exact h.1 p hp,
    wordAt_of_agree_ne basek xsk σ σ' bound wpAddr h.2.1 hpk hbk nek1 nek2 hagree,
    wordAt_of_agree_ne base1 xs1 σ σ' bound wpAddr h.2.2.1 hp1 hb1 ne11 ne12 hagree,
    wordAt_of_agree_ne base2 xs2 σ σ' bound wpAddr h.2.2.2 hp2 hb2 ne21 ne22 hagree⟩

/-- A clause write (or any rewrite agreeing below the pointer, off the pointer
    cell) preserves the three staged words: they sit above the control block
    and strictly below the pointer. -/
lemma pinsAndWords3_preserve_below (M Jmax : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (σ σ' : Store) (wp : ℕ)
    (hF : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 σ)
    (hbasek : M + ctlJmax < basek) (hbase1 : M + ctlJmax < base1)
    (hbase2 : M + ctlJmax < base2)
    (hwk : WordBelow basek xsk.length wp) (hw1w : WordBelow base1 xs1.length wp)
    (hw2w : WordBelow base2 xs2.length wp)
    (hpin : ∀ p ∈ pins, 1 ≤ p.1 ∧ p.1 ≤ Jmax ∧ p.1 ≠ wpJ)
    (hsep : M + Jmax < wp)
    (hagree : ∀ r, r < wp → r ≠ M + wpJ → σ' r = σ r) :
    PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 σ' := by
  have hw : wpJ = 1 := rfl
  have hc : ctlJmax = 7 := rfl
  refine pinsAndWords3_of_agree_ne M pins basek xsk base1 xs1 base2 xs2 σ σ' wp (M + wpJ) hF
    hwk.1 hwk.2 hw1w.1 hw1w.2 hw2w.1 hw2w.2
    (word_len_disjoint_ctl M basek (M + wpJ) hbasek (by omega))
    (fun k _ => word_disjoint_ctl M basek (M + wpJ) k hbasek (by omega))
    (word_len_disjoint_ctl M base1 (M + wpJ) hbase1 (by omega))
    (fun k _ => word_disjoint_ctl M base1 (M + wpJ) k hbase1 (by omega))
    (word_len_disjoint_ctl M base2 (M + wpJ) hbase2 (by omega))
    (fun k _ => word_disjoint_ctl M base2 (M + wpJ) k hbase2 (by omega))
    (fun p hp => by obtain ⟨hp1, hp2, hpne⟩ := hpin p hp; exact ⟨by omega, by omega⟩)
    hagree

/-- A loop-counter bump (`iJ ≤ lvJ3`) is a single-cell rewrite inside the
    control block, so it misses the three staged words. -/
lemma pinsAndWords3_writeReg_loop (M : ℕ) (pins : List (ℕ × ℕ))
    (basek : ℕ) (xsk : List ℕ) (base1 : ℕ) (xs1 : List ℕ) (base2 : ℕ) (xs2 : List ℕ)
    (iJ v : ℕ) (τ : Store)
    (h : PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 τ)
    (hiJ : iJ ≤ lvJ3)
    (hpin : ∀ p ∈ pins, M + p.1 ≠ M + iJ)
    (hbasek : M + ctlJmax < basek) (hbase1 : M + ctlJmax < base1)
    (hbase2 : M + ctlJmax < base2) :
    PinsAndWords3 M pins basek xsk base1 xs1 base2 xs2 (writeReg τ (M + iJ) v) := by
  have hc : ctlJmax = 7 := rfl
  have h3 : lvJ3 = 5 := rfl
  have haddr : M + iJ < M + ctlJmax := by omega
  refine pinsAndWords3_writeReg M pins basek xsk base1 xs1 base2 xs2 (M + iJ) v τ h hpin
    (word_len_disjoint_ctl M basek (M + iJ) hbasek haddr)
    (fun k _ => word_disjoint_ctl M basek (M + iJ) k hbasek haddr)
    (word_len_disjoint_ctl M base1 (M + iJ) hbase1 haddr)
    (fun k _ => word_disjoint_ctl M base1 (M + iJ) k hbase1 haddr)
    (word_len_disjoint_ctl M base2 (M + iJ) hbase2 haddr)
    (fun k _ => word_disjoint_ctl M base2 (M + iJ) k hbase2 haddr)


end NPComplete.CookLevin

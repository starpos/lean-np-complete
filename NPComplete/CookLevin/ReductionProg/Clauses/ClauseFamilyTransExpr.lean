module

public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseCtlLayout
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseTableFrame
public import NPComplete.CookLevin.ReductionProg.Clauses.ClauseRowLayout
public import NPComplete.CookLevin.Tableau.TableauRamLoops

/-!
The transition family is the reduction's deepest nest — four range counters,
with an innermost lookup in the machine's transition table.  That lookup supplies
the successor state, written symbol, and move direction.

The lookup reduces to three flat numeric columns
(`transKind`/`transArg1`/`transArg2` of `TableauDescriptor.entry`), addressed by the
row-major index `qi * m + ai`.  This file is the RAM-side mirror: it assumes the three columns
sit in the store as `WordAt` words and defines the expression that reads each
one at the current `(qi, ai)`, together with its frame and value obligations.

The row-major index itself is common to all three reads and to nothing else in
the family, so it gets its own expression (`transIdxE`) rather than being
inlined three times — the three column reads then differ only in which word
they read, not in how they compute where to read it.

The five "current/next row" expressions mirror `persistHeadE`/`persistCellE`
exactly: they read only `ctlCell`s, so their frame and value obligations are
the same three-step argument already used throughout `ClauseFamilyPersist`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile

/-! ## The row-major table index

`d.entry qi ai` is read off column `qi * d.numLetters + ai`; `qi` sits at the
level-2 counter and `ai` at the level-3 counter, which is the only place the
whole family reads `lvJ3` — every other expression in this family reads at most
`lvJ2` and above. -/

/-- Row-major index of `(qi, ai)` into a `numLetters`-wide flattened table, read
off the two innermost loop counters. -/
def transIdxE (m : ℕ) : Expr := .add (.mul (ctlCell lvJ2) (.const m)) (ctlCell lvJ3)

lemma transIdxE_frame (M m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transIdxE m).eval σ' = (transIdxE m).eval σ := by
  unfold transIdxE
  simp only [Expr.eval]
  rw [ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree,
    ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree]

lemma transIdxE_value (M m t p qi ai : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) :
    (transIdxE m).eval τ = qi * m + ai := by
  have e2 : (ctlCell lvJ2).eval τ = qi :=
    ctlCell_eval_of_pin M _ lvJ2 qi τ (by simp [ctlPins3]) hF h0
  have e3 : (ctlCell lvJ3).eval τ = ai := by rw [ctlCell_eval, h0]; exact hai
  unfold transIdxE
  simp [Expr.eval, e2, e3]

/-! ## The three table columns

Each column is a word at its own base, read at `transIdxE`.  The blank `0`
matches `NatTrans.halt`'s own numeric encoding (`transKind .halt = 0`,
`transArg1 .halt = 0`, `transArg2 .halt = 0`), which is also
`TableauDescriptor.entry`'s out-of-range fallback — so the read needs no
separate case for indices past the table's own length. -/

def transKindE (kindBase lenk m : ℕ) : Expr := wordReadE kindBase 0 lenk (transIdxE m)
def transArg1E (arg1Base len1 m : ℕ) : Expr := wordReadE arg1Base 0 len1 (transIdxE m)
def transArg2E (arg2Base len2 m : ℕ) : Expr := wordReadE arg2Base 0 len2 (transIdxE m)

/-- Frame for a table-column read, in the "agreement below a bound" shape
`clauseWriter_clause_below_words3` consumes directly.  The three columns share this
one proof since each is `wordReadE` at its own base composed with the same
`transIdxE`.  The length is a compile-time constant, so the frame lemma needs no
length cell to agree across stores. -/
lemma trans_col_e_frame (M base len bound m : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hw : WordBelow base len bound)
    (hbase : M + ctlJmax < base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (wordReadE base 0 len (transIdxE m)).eval σ'
      = (wordReadE base 0 len (transIdxE m)).eval σ := by
  obtain ⟨hb1, hb2⟩ := hw
  have hw1 : wpJ = 1 := rfl
  have hc1 : ctlJmax = 7 := rfl
  have hctl' : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j) :=
    fun j hj1 hj2 hj3 => hagree (M + j) (by omega) (by omega)
  refine wordReadE_frame base 0 len bound (M + wpJ) (transIdxE m) σ σ' ⟨hb1, hb2⟩
    (fun k _ => by omega) hagree (transIdxE_frame M m σ σ' hσ hσ' hctl')

lemma transArg1E_frame (M arg1Base len bound m : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hw : WordBelow arg1Base len bound)
    (hbase : M + ctlJmax < arg1Base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (transArg1E arg1Base len m).eval σ' = (transArg1E arg1Base len m).eval σ :=
  trans_col_e_frame M arg1Base len bound m σ σ' hσ hσ' hw hbase hagree

lemma transArg2E_frame (M arg2Base len bound m : ℕ) (σ σ' : Store)
    (hσ : σ 0 = M) (hσ' : σ' 0 = M) (hw : WordBelow arg2Base len bound)
    (hbase : M + ctlJmax < arg2Base)
    (hagree : ∀ r, r < bound → r ≠ M + wpJ → σ' r = σ r) :
    (transArg2E arg2Base len m).eval σ' = (transArg2E arg2Base len m).eval σ :=
  trans_col_e_frame M arg2Base len bound m σ σ' hσ hσ' hw hbase hagree

/-- Value of a table-column read: with `t`/`p`/`qi` pinned and `ai` held by the
level's own counter, the read is the column list's own `getD` at the row-major
index — the numeric form of `TableauDescriptor.entry`'s lookup. -/
lemma trans_col_e_value (M base m t p qi ai : ℕ) (τ : Store) (col : List ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai)
    (hw : WordAt τ base col) :
    (wordReadE base 0 col.length (transIdxE m)).eval τ = col.getD (qi * m + ai) 0 := by
  rw [wordReadE_eval τ base 0 col (transIdxE m) hw, transIdxE_value M m t p qi ai τ hF h0 hai]

lemma transKindE_value (M kindBase m t p qi ai : ℕ) (τ : Store) (col : List ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai)
    (hw : WordAt τ kindBase col) :
    (transKindE kindBase col.length m).eval τ = col.getD (qi * m + ai) 0 :=
  trans_col_e_value M kindBase m t p qi ai τ col hF h0 hai hw

lemma transArg1E_value (M arg1Base m t p qi ai : ℕ) (τ : Store) (col : List ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai)
    (hw : WordAt τ arg1Base col) :
    (transArg1E arg1Base col.length m).eval τ = col.getD (qi * m + ai) 0 :=
  trans_col_e_value M arg1Base m t p qi ai τ col hF h0 hai hw

lemma transArg2E_value (M arg2Base m t p qi ai : ℕ) (τ : Store) (col : List ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai)
    (hw : WordAt τ arg2Base col) :
    (transArg2E arg2Base col.length m).eval τ = col.getD (qi * m + ai) 0 :=
  trans_col_e_value M arg2Base m t p qi ai τ col hF h0 hai hw

/-! ## The current row's three variable expressions

`state t qi`, `head t p`, and `cell t p ai` are exactly the three antecedents
of every `imply3` clause `natTransClausesPadded` writes.  Each reads only
`ctlCell`s from the levels at or above its own, so their frame and value
obligations mirror `persistHeadE`/`persistCellE` in `ClauseFamilyPersist.lean`
verbatim. -/

/-- `state t qi`, over the time and second-innermost counters. -/
def transStateE (n W m : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ2)

/-- `head t p`, over the time and head counters. -/
def transHeadE (n W m : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1)

/-- `cell t p ai`, over the time, head, and innermost letter counters. -/
def transCellE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m) (ctlCell lvJ0) (ctlCell lvJ1) (ctlCell lvJ3)

lemma transStateE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transStateE n W m).eval σ' = (transStateE n W m).eval σ := by
  unfold transStateE
  exact denseStateE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ2 (Or.inr (Or.inr (Or.inl rfl))) σ σ' hσ hσ' hagree)

lemma transHeadE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transHeadE n W m).eval σ' = (transHeadE n W m).eval σ := by
  unfold transHeadE
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)

lemma transCellE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transCellE n W m).eval σ' = (transCellE n W m).eval σ := by
  unfold transCellE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

lemma transStateE_value (M n W m t p qi : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) :
    (transStateE n W m).eval τ = (denseLayout n W m).state t qi := by
  unfold transStateE
  exact denseStateE_eval_eq _ _ _ _ _ τ n W m t qi rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ2 qi τ (by simp [ctlPins3]) hF h0)

lemma transHeadE_value (M n W m t p qi : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) :
    (transHeadE n W m).eval τ = (denseLayout n W m).head t p := by
  unfold transHeadE
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m t p rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0)

lemma transCellE_value (M n W m t p qi : ℕ) (τ : Store) (ai : ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) :
    (transCellE n W m).eval τ = (denseLayout n W m).cell t p ai := by
  unfold transCellE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m t p ai rfl rfl rfl
    (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0)
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact hai)

/-! ## The next row's five variable expressions

`natTransClausesPadded`'s three branches consult five distinct successor
positions: the moved-on state (`.write`/`.move`), the unmoved head
(`.halt`/`.write`), the moved head (`.move`), the unmoved cell (`.halt`/
`.move`), and the written cell (`.write`).  `transStateNextE`/`transCellWriteE`
read a table column where the successor index is data (the successor state,
the written symbol); `transHeadSameE`/`transCellSameE` need no table read at
all, since the position is unchanged; `transHeadMoveE` is the one case where
the successor position is itself computed from a table value, handled below. -/

/-- `state (t + 1) qi'`, where `qi'` is read off the `arg1` column — the
successor state in the `.write`/`.move` branches. -/
def transStateNextE (n W m arg1Base len1 : ℕ) : Expr :=
  denseStateE (.const n) (.const W) (.const m)
    (.add (ctlCell lvJ0) (.const 1)) (transArg1E arg1Base len1 m)

/-- `head (t + 1) p`, the unmoved successor head — used by the halt and write
branches. -/
def transHeadSameE (n W m : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1)

lemma transHeadSameE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transHeadSameE n W m).eval σ' = (transHeadSameE n W m).eval σ := by
  unfold transHeadSameE
  exact denseHeadE_eval_congr _ _ _ _ _ σ σ' rfl rfl rfl
    (expr_add_one_eval_congr _ σ σ'
      (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)

lemma transHeadSameE_value (M n W m t p qi : ℕ) (τ : Store)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) :
    (transHeadSameE n W m).eval τ = (denseLayout n W m).head (t + 1) p := by
  unfold transHeadSameE
  exact denseHeadE_eval_eq _ _ _ _ _ τ n W m (t + 1) p rfl rfl rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0))
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0)

/-- `cell (t + 1) p ai`, the unmoved successor cell — used by the halt and move
branches, at the same letter index the current row reads. -/
def transCellSameE (n W m : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1) (ctlCell lvJ3)

lemma transCellSameE_frame (M n W m : ℕ) (σ σ' : Store) (hσ : σ 0 = M) (hσ' : σ' 0 = M)
    (hagree : ∀ j, 1 ≤ j → j ≤ ctlJmax → j ≠ wpJ → σ' (M + j) = σ (M + j)) :
    (transCellSameE n W m).eval σ' = (transCellSameE n W m).eval σ := by
  unfold transCellSameE
  exact denseCellE_eval_congr _ _ _ _ _ _ σ σ' rfl rfl rfl
    (expr_add_one_eval_congr _ σ σ'
      (ctlCell_frame_lv M lvJ0 (Or.inl rfl) σ σ' hσ hσ' hagree))
    (ctlCell_frame_lv M lvJ1 (Or.inr (Or.inl rfl)) σ σ' hσ hσ' hagree)
    (ctlCell_frame_lv M lvJ3 (Or.inr (Or.inr (Or.inr rfl))) σ σ' hσ hσ' hagree)

lemma transCellSameE_value (M n W m t p qi : ℕ) (τ : Store) (ai : ℕ)
    (hF : PinsHold M (ctlPins3 t p qi) τ) (h0 : τ 0 = M) (hai : τ (M + lvJ3) = ai) :
    (transCellSameE n W m).eval τ = (denseLayout n W m).cell (t + 1) p ai := by
  unfold transCellSameE
  exact denseCellE_eval_eq _ _ _ _ _ _ τ n W m (t + 1) p ai rfl rfl rfl
    (expr_add_one_eval _ τ t
      (ctlCell_eval_of_pin M _ lvJ0 t τ (by simp [ctlPins3]) hF h0))
    (ctlCell_eval_of_pin M _ lvJ1 p τ (by simp [ctlPins3]) hF h0)
    (by rw [ctlCell_eval, h0]; exact hai)

/-- `cell (t + 1) p bi`, where `bi` is read off the `arg2` column — the written
symbol in the write branch. -/
def transCellWriteE (n W m arg2Base len2 : ℕ) : Expr :=
  denseCellE (.const n) (.const W) (.const m)
    (.add (ctlCell lvJ0) (.const 1)) (ctlCell lvJ1) (transArg2E arg2Base len2 m)

/-! ## The moved head

`nextIdx`'s two successful branches both fit the truncated-subtraction formula
`p + arg2 - (1 - arg2)`, for `arg2` the numeric direction (`0` = left, `1` =
right): left subtracts `1` (since `1 - arg2 = 1`), right adds `1` (since
`1 - arg2 = 0`). -/

/-- `head (t + 1) p'`, where `p' = p + arg2 - (1 - arg2)` for `arg2` the value
read off the `arg2` column at the current row. -/
def transHeadMoveE (n W m arg2Base len2 : ℕ) : Expr :=
  denseHeadE (.const n) (.const W) (.const m) (.add (ctlCell lvJ0) (.const 1))
    (.sub (.add (ctlCell lvJ1) (transArg2E arg2Base len2 m))
      (.sub (.const 1) (transArg2E arg2Base len2 m)))

end NPComplete.CookLevin

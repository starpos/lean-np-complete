module

public import NPComplete.BitEncoding
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.BoundedWhile.Frame
public import NPComplete.RAMToTM.ThreeSat.Problem.ReductionMemoryLayout
public import NPComplete.SAT.ThreeCNFEncoding

/-!
# 3-CNF runtime decoding

This module interprets encoded 3-CNF values in the reduction arena, keeping its layout-specific
literal and clause decoders separate from the generic bit representation and unary scanner.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store Expr writeReg eval_ifNZ eval_seq
  eval_assign eval_assignInd eval_skip eval_forN loopEval loopEval_succ loopEval_zero
  writeReg_same writeReg_diff)
open NPComplete.BitEncoding (Bits encodeNat encodeNat_succ encodeNat_length)
open NPComplete.SAT (Literal ThreeClause encodeLiteral encodeThreeClause)

/-! ## Decoding one literal into the clause arena

`encodeLiteral l = polBit :: encodeNat l.var` (`ThreeCNFEncoding.lean`); `LiteralAt`
(`ReductionMemoryLayout.lean`) is the arena predicate a decoded literal must land in — `0` at
`literalPolCell` for `.pos`, `1` for `.neg`, matching `encodeLiteral`'s `false`/`true` polarity
bit exactly, so the raw bit value doubles as `LiteralAt`'s discriminant with no translation. -/

/-- Decode one literal (`encodeLiteral l = polBit :: encodeNat l.var`) starting at the cursor,
    and write it into the arena at `(clauseBase, i, j)` (`LiteralAt`). `polReg`/`varReg`/
    `doneReg` are scratch: read the polarity bit into `polReg` and advance, reset `varReg`/
    `doneReg`, decode `l.var` via `decodeUnaryProg` into `varReg`, then commit both to the
    arena's two cells for this literal slot. -/
def decodeLiteralProg (cursorReg polReg varReg doneReg bound clauseBase i j : ℕ) : Program :=
  .seq (readBitAdvanceProg cursorReg polReg)
  <| .seq (.assign varReg (.const 0))
  <| .seq (.assign doneReg (.const 0))
  <| .seq (decodeUnaryProg cursorReg varReg doneReg bound)
  <| .seq (.assignInd (.const (literalPolCell clauseBase i j)) (.reg polReg))
      (.assignInd (.const (literalVarCell clauseBase i j)) (.reg varReg))

/-- Resetting `varReg` and `doneReg` after the polarity read leaves the unary payload intact,
with the cursor just past the polarity bit and the polarity stored in `polReg`. -/
lemma decodeLiteralProg_correct_setup
    (cursorReg polReg varReg doneReg addr : ℕ) (bits : Bits) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr) (hda : doneReg < addr)
    (hc : σ cursorReg = addr) (hbits : BitsFrom σ (addr + 1) bits) :
    ∃ σ3, σ3 = (Program.assign doneReg (Expr.const 0)).eval
        ((Program.assign varReg (Expr.const 0)).eval
          ((readBitAdvanceProg cursorReg polReg).eval σ)) ∧
      σ3 polReg = σ addr ∧ σ3 varReg = 0 ∧ σ3 doneReg = 0 ∧ σ3 cursorReg = addr + 1 ∧
      BitsFrom σ3 (addr + 1) bits := by
  obtain ⟨hσ1pol, hσ1cur⟩ := readBitAdvanceProg_eval cursorReg polReg σ hcp
  have hσ1bits : BitsFrom ((readBitAdvanceProg cursorReg polReg).eval σ) (addr + 1) bits := by
    intro k hk
    rw [readBitAdvanceProg_frame cursorReg polReg (addr + 1 + k) σ (by omega) (by omega)]
    exact hbits k hk
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ polReg hpd, writeReg_diff _ varReg _ polReg hpv, hσ1pol, hc]
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ varReg hvd, writeReg_same]
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_same]
  · simp only [eval_assign, Expr.eval]
    rw [writeReg_diff _ doneReg _ cursorReg hcd, writeReg_diff _ varReg _ cursorReg hcv,
      hσ1cur, hc]
  · simp only [eval_assign, Expr.eval]
    exact bitsFrom_writeReg (bitsFrom_writeReg hσ1bits varReg 0 (by omega)) doneReg 0 (by omega)

/-- The two arena commits copy the decoded polarity and variable and keep the cursor. -/
lemma decodeLiteralProg_correct_commit
    (cursorReg polReg varReg clauseBase i j : ℕ) (σ4 : Store)
    (hpol_c : literalPolCell clauseBase i j ≠ cursorReg)
    (hpol_v : literalPolCell clauseBase i j ≠ varReg)
    (hvar_c : literalVarCell clauseBase i j ≠ cursorReg)
    (hpv_ne : literalPolCell clauseBase i j ≠ literalVarCell clauseBase i j) :
    let σ6 := (Program.assignInd (Expr.const (literalVarCell clauseBase i j))
      (Expr.reg varReg)).eval
        ((Program.assignInd (Expr.const (literalPolCell clauseBase i j))
          (Expr.reg polReg)).eval σ4)
    σ6 (literalPolCell clauseBase i j) = σ4 polReg ∧
    σ6 (literalVarCell clauseBase i j) = σ4 varReg ∧ σ6 cursorReg = σ4 cursorReg := by
  simp only [eval_assignInd, Expr.eval]
  refine ⟨?_, ?_, ?_⟩
  · rw [writeReg_diff _ _ _ _ hpv_ne, writeReg_same]
  · rw [writeReg_same, writeReg_diff _ _ _ _ (Ne.symm hpol_v)]
  · rw [writeReg_diff _ _ _ _ (Ne.symm hvar_c), writeReg_diff _ _ _ _ (Ne.symm hpol_c)]


/-- `decodeLiteralProg` on a polarity bit `b` followed by `encodeNat v`: arena cells receive the
raw polarity value and `v`, and the cursor ends just past the literal. Both polarities share this
run, so the literal-level statement is a two-way case split. -/
lemma decodeLiteralProg_correct_run
    (cursorReg polReg varReg doneReg bound clauseBase i j addr v : ℕ) (b : Bool) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr) (hda : doneReg < addr)
    (hpol_c : literalPolCell clauseBase i j ≠ cursorReg)
    (hpol_v : literalPolCell clauseBase i j ≠ varReg)
    (hvar_c : literalVarCell clauseBase i j ≠ cursorReg)
    (hpv_ne : literalPolCell clauseBase i j ≠ literalVarCell clauseBase i j)
    (hbound : v + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (b :: encodeNat v)) :
    (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ
        (literalPolCell clauseBase i j) = (if b then 1 else 0) ∧
    (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ
        (literalVarCell clauseBase i j) = v ∧
    (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ cursorReg
        = addr + v + 2 := by
  obtain ⟨hb0, hbrest⟩ := bitsFrom_cons σ addr b (encodeNat v) hbits
  obtain ⟨σ3, hσ3, hpol, hvar, hdone, hcur, hσ3bits⟩ :=
    decodeLiteralProg_correct_setup cursorReg polReg varReg doneReg addr (encodeNat v) σ
      hcp hcv hcd hpv hpd hvd hca hpa hva hda hc hbrest
  obtain ⟨hfc, hfk, -, hfr⟩ := decodeUnaryProg_correct cursorReg varReg doneReg
    hcv hcd hvd v bound (addr + 1) 0 σ3 hbound (by omega) (by omega) (by omega)
    hcur hvar hdone hσ3bits
  have hσ4pol := hfr polReg (Ne.symm hcp) hpv hpd
  obtain ⟨h1, h2, h3⟩ := decodeLiteralProg_correct_commit cursorReg polReg varReg clauseBase i j
    ((decodeUnaryProg cursorReg varReg doneReg bound).eval σ3) hpol_c hpol_v hvar_c hpv_ne
  simp only [decodeLiteralProg, eval_seq]
  rw [← hσ3]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hσ4pol, hpol, hb0]
  · rw [h2, hfk]; omega
  · rw [h3, hfc]; omega

/-- Correctness of `decodeLiteralProg`: `cursorReg`/`polReg`/`varReg`/`doneReg` pairwise
    distinct and all below the bit region (`addr`, so the decode never corrupts its own input),
    and the two destination cells distinct from each other and from `cursorReg` (so the cursor's
    final value survives both commits). The polarity cell must also differ from `varReg`, since
    its commit runs before the variable-cell commit reads `varReg`; the symmetric
    `literalVarCell ≠ polReg/varReg/doneReg` constraints are *not* needed since the
    `literalVarCell` write happens last and nothing reads those registers afterward. -/
lemma decodeLiteralProg_correct
    (cursorReg polReg varReg doneReg bound clauseBase i j addr : ℕ) (l : Literal) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr) (hda : doneReg < addr)
    (hpol_c : literalPolCell clauseBase i j ≠ cursorReg)
    (hpol_v : literalPolCell clauseBase i j ≠ varReg)
    (hvar_c : literalVarCell clauseBase i j ≠ cursorReg)
    (hpv_ne : literalPolCell clauseBase i j ≠ literalVarCell clauseBase i j)
    (hbound : l.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l)) :
    LiteralAt ((decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ)
      clauseBase i j l ∧
    (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ cursorReg
      = addr + (encodeLiteral l).length := by
  rcases l with v | v
  · obtain ⟨h1, h2, h3⟩ := decodeLiteralProg_correct_run cursorReg polReg varReg doneReg bound
      clauseBase i j addr v false σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hpol_c hpol_v hvar_c
      hpv_ne hbound hc hbits
    refine ⟨⟨by simpa using h1, h2⟩, ?_⟩
    rw [h3]; simp [encodeLiteral, encodeNat_length]; omega
  · obtain ⟨h1, h2, h3⟩ := decodeLiteralProg_correct_run cursorReg polReg varReg doneReg bound
      clauseBase i j addr v true σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hpol_c hpol_v hvar_c
      hpv_ne hbound hc hbits
    refine ⟨⟨by simpa using h1, h2⟩, ?_⟩
    rw [h3]; simp [encodeLiteral, encodeNat_length]; omega

/-- Frame corollary: `decodeLiteralProg` only ever touches `cursorReg`/`polReg`/`varReg`/
    `doneReg` and the two destination arena cells — any other cell is unchanged. Needed to
    compose several `decodeLiteralProg` calls (e.g. the three lanes of a `ThreeClause`) without
    each later call disturbing an earlier call's still-live decoded bits or arena writes. -/
lemma decodeLiteralProg_frame
    (cursorReg polReg varReg doneReg bound clauseBase i j r : ℕ) (σ : Store)
    (h1 : r ≠ cursorReg) (h2 : r ≠ polReg) (h3 : r ≠ varReg) (h4 : r ≠ doneReg)
    (h5 : r ≠ literalPolCell clauseBase i j) (h6 : r ≠ literalVarCell clauseBase i j) :
    (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ r = σ r := by
  simp only [decodeLiteralProg, eval_seq]
  set σ1 := (readBitAdvanceProg cursorReg polReg).eval σ with hσ1def
  have hσ1r : σ1 r = σ r := by
    rw [hσ1def]; exact readBitAdvanceProg_frame cursorReg polReg r σ h1 h2
  set σ2 := (Program.assign varReg (Expr.const 0)).eval σ1 with hσ2def
  have hσ2r : σ2 r = σ1 r := by
    rw [hσ2def]; simp only [eval_assign, Expr.eval]; exact writeReg_diff _ varReg _ r h3
  set σ3 := (Program.assign doneReg (Expr.const 0)).eval σ2 with hσ3def
  have hσ3r : σ3 r = σ2 r := by
    rw [hσ3def]; simp only [eval_assign, Expr.eval]; exact writeReg_diff _ doneReg _ r h4
  set σ4 := (decodeUnaryProg cursorReg varReg doneReg bound).eval σ3 with hσ4def
  have hσ4r : σ4 r = σ3 r := by
    rw [hσ4def]; exact decodeUnaryProg_frame cursorReg varReg doneReg bound r σ3 h1 h3 h4
  set σ5 := (Program.assignInd (Expr.const (literalPolCell clauseBase i j))
    (Expr.reg polReg)).eval σ4 with hσ5def
  have hσ5r : σ5 r = σ4 r := by
    rw [hσ5def]; simp only [eval_assignInd, Expr.eval]
    exact writeReg_diff _ (literalPolCell clauseBase i j) _ r h5
  set σ6 := (Program.assignInd (Expr.const (literalVarCell clauseBase i j))
    (Expr.reg varReg)).eval σ5 with hσ6def
  have hσ6r : σ6 r = σ5 r := by
    rw [hσ6def]; simp only [eval_assignInd, Expr.eval]
    exact writeReg_diff _ (literalVarCell clauseBase i j) _ r h6
  rw [hσ6r, hσ5r, hσ4r, hσ3r, hσ2r, hσ1r]


/-! ## Decoding a full `ThreeClause`: composing three `decodeLiteralProg` lanes

`encodeThreeClause c = encodeLiteral c.l1 ++ encodeLiteral c.l2 ++ encodeLiteral c.l3`
(`ThreeCNFEncoding.lean`) is a fixed-arity concatenation (no length prefix), so decoding it is
three sequential `decodeLiteralProg` calls at lanes `0`/`1`/`2` of the same row `i`, reusing the
same four scratch registers (each call resets `polReg`/`varReg`/`doneReg` internally). Rather
than enumerate every pairwise cell/register disjointness by hand, `literalPolCell`/
`literalVarCell`'s arithmetic form (`clauseBase + 6 * i + 2 * j [+ 1]`) lets a single "all four
registers sit below the row's address range" hypothesis (`hcr`/`hpr`/`hvr`/`hdr`) discharge every
register-vs-cell disjointness via `omega`, and the row's own arithmetic discharges every
cell-vs-cell disjointness the same way. -/

lemma literalPolCell_eq' (clauseBase i j : ℕ) :
    literalPolCell clauseBase i j = clauseBase + 6 * i + 2 * j := by
  unfold literalPolCell clauseCell
  rw [arenaAddr]
  simp [literalStride, clauseStride]

lemma literalVarCell_eq' (clauseBase i j : ℕ) :
    literalVarCell clauseBase i j = clauseBase + 6 * i + 2 * j + 1 := by
  unfold literalVarCell clauseCell
  rw [arenaAddr]
  simp only [literalStride, clauseStride]
  omega

/-- `LiteralAt` only depends on the store's value at the literal's two cells — a frame-equal
    store change (e.g. running a later, disjoint `decodeLiteralProg` call) preserves it. Proved
    against `l` (a bound variable) rather than case-splitting a projection like `c.l1` directly,
    since `rcases`/`cases` on a non-variable term does not substitute into hypotheses already in
    context (a standing Lean 4 gotcha) — callers instantiate `l := c.l1` etc. after the fact. -/
lemma literalAt_of_eq (σ σ' : Store) (clauseBase i j : ℕ) (l : Literal)
    (h1 : σ' (literalPolCell clauseBase i j) = σ (literalPolCell clauseBase i j))
    (h2 : σ' (literalVarCell clauseBase i j) = σ (literalVarCell clauseBase i j))
    (hL : LiteralAt σ clauseBase i j l) : LiteralAt σ' clauseBase i j l := by
  unfold LiteralAt at hL ⊢
  rcases l with v | v <;> simp_all

def decodeThreeClauseProg (cursorReg polReg varReg doneReg bound clauseBase i : ℕ) : Program :=
  .seq (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i 0)
  <| .seq (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i 1)
      (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i 2)

/-- One lane of `decodeThreeClauseProg`: decoding literal `l` at slot `j` of row `i` leaves the
trailing input bits `rest` readable, parks the cursor after `l`, and leaves the other lanes' cells
untouched. -/
lemma decodeThreeClauseProg_correct_lane
    (cursorReg polReg varReg doneReg bound clauseBase i j addr : ℕ) (l : Literal) (rest : Bits)
    (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr) (hda : doneReg < addr)
    (hcr : cursorReg < clauseBase + 6 * i) (hpr : polReg < clauseBase + 6 * i)
    (hvr : varReg < clauseBase + 6 * i) (hdr : doneReg < clauseBase + 6 * i)
    (hj : j < 3) (hsep : addr + (encodeLiteral l ++ rest).length ≤ clauseBase)
    (hb : l.var + 1 ≤ bound) (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeLiteral l ++ rest)) :
    ∃ σ' : Store,
      σ' = (decodeLiteralProg cursorReg polReg varReg doneReg bound clauseBase i j).eval σ ∧
      LiteralAt σ' clauseBase i j l ∧
      σ' cursorReg = addr + (encodeLiteral l).length ∧
      BitsFrom σ' (addr + (encodeLiteral l).length) rest ∧
      (∀ j', j' < 3 → j' ≠ j →
        σ' (literalPolCell clauseBase i j') = σ (literalPolCell clauseBase i j') ∧
        σ' (literalVarCell clauseBase i j') = σ (literalVarCell clauseBase i j')) := by
  obtain ⟨hbl, hbr⟩ := bitsFrom_append σ addr (encodeLiteral l) rest hbits
  simp only [List.length_append] at hsep
  have hpc : literalPolCell clauseBase i j = clauseBase + 6 * i + 2 * j := literalPolCell_eq' _ _ _
  have hvc : literalVarCell clauseBase i j = clauseBase + 6 * i + 2 * j + 1 :=
    literalVarCell_eq' _ _ _
  obtain ⟨hL, hC⟩ := decodeLiteralProg_correct cursorReg polReg varReg doneReg bound
    clauseBase i j addr l σ hcp hcv hcd hpv hpd hvd hca hpa hva hda
    (by omega) (by omega) (by omega) (by omega) hb hc hbl
  refine ⟨_, rfl, hL, hC, ?_, ?_⟩
  · refine bitsFrom_of_eq_on (fun k hk => ?_) hbr
    exact decodeLiteralProg_frame cursorReg polReg varReg doneReg bound clauseBase i j
      (addr + (encodeLiteral l).length + k) σ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · intro j' hj' hne
    have h1 : literalPolCell clauseBase i j' = clauseBase + 6 * i + 2 * j' := literalPolCell_eq' _ _ _
    have h2 : literalVarCell clauseBase i j' = clauseBase + 6 * i + 2 * j' + 1 :=
      literalVarCell_eq' _ _ _
    exact ⟨decodeLiteralProg_frame cursorReg polReg varReg doneReg bound clauseBase i j _ σ
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      decodeLiteralProg_frame cursorReg polReg varReg doneReg bound clauseBase i j _ σ
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- `decodeThreeClauseProg` decodes a full `ThreeClause` into row `i` of the clause arena at
    `clauseBase` (`ThreeClauseAt`). `cursorReg`/`polReg`/`varReg`/`doneReg` pairwise distinct and
    below both the input region (`addr`, `hca`-`hda`) and the arena row (`clauseBase + 6 * i`,
    `hcr`-`hdr`). -/
lemma decodeThreeClauseProg_correct
    (cursorReg polReg varReg doneReg bound clauseBase i addr : ℕ) (c : ThreeClause) (σ : Store)
    (hcp : cursorReg ≠ polReg) (hcv : cursorReg ≠ varReg) (hcd : cursorReg ≠ doneReg)
    (hpv : polReg ≠ varReg) (hpd : polReg ≠ doneReg) (hvd : varReg ≠ doneReg)
    (hca : cursorReg < addr) (hpa : polReg < addr) (hva : varReg < addr) (hda : doneReg < addr)
    (hcr : cursorReg < clauseBase + 6 * i) (hpr : polReg < clauseBase + 6 * i)
    (hvr : varReg < clauseBase + 6 * i) (hdr : doneReg < clauseBase + 6 * i)
    (hsep : addr + (encodeThreeClause c).length ≤ clauseBase)
    (hb0 : c.l1.var + 1 ≤ bound) (hb1 : c.l2.var + 1 ≤ bound) (hb2 : c.l3.var + 1 ≤ bound)
    (hc : σ cursorReg = addr)
    (hbits : BitsFrom σ addr (encodeThreeClause c)) :
    ThreeClauseAt ((decodeThreeClauseProg cursorReg polReg varReg doneReg bound
      clauseBase i).eval σ) clauseBase i c ∧
    (decodeThreeClauseProg cursorReg polReg varReg doneReg bound clauseBase i).eval σ cursorReg
      = addr + (encodeThreeClause c).length := by
  have hassoc : encodeThreeClause c
      = encodeLiteral c.l1 ++ (encodeLiteral c.l2 ++ (encodeLiteral c.l3 ++ [])) := by
    simp [encodeThreeClause, List.append_assoc]
  rw [hassoc] at hsep hbits
  simp only [List.length_append, List.length_nil] at hsep
  obtain ⟨σ1, hσ1, hL1, hc1, hbits1, hfr1⟩ :=
    decodeThreeClauseProg_correct_lane cursorReg polReg varReg doneReg bound clauseBase i 0 addr
      c.l1 _ σ hcp hcv hcd hpv hpd hvd hca hpa hva hda hcr hpr hvr hdr (by norm_num)
      (by simp only [List.length_append, List.length_nil]; omega) hb0 hc hbits
  obtain ⟨σ2, hσ2, hL2, hc2, hbits2, hfr2⟩ :=
    decodeThreeClauseProg_correct_lane cursorReg polReg varReg doneReg bound clauseBase i 1
      (addr + (encodeLiteral c.l1).length) c.l2 _ σ1 hcp hcv hcd hpv hpd hvd
      (by omega) (by omega) (by omega) (by omega) hcr hpr hvr hdr (by norm_num)
      (by simp only [List.length_append, List.length_nil]; omega) hb1 hc1 hbits1
  obtain ⟨σ3, hσ3, hL3, hc3, -, hfr3⟩ :=
    decodeThreeClauseProg_correct_lane cursorReg polReg varReg doneReg bound clauseBase i 2
      (addr + (encodeLiteral c.l1).length + (encodeLiteral c.l2).length) c.l3 _ σ2
      hcp hcv hcd hpv hpd hvd (by omega) (by omega) (by omega) (by omega) hcr hpr hvr hdr
      (by norm_num) (by simp only [List.length_append, List.length_nil]; omega) hb2 hc2 hbits2
  have htop : (decodeThreeClauseProg cursorReg polReg varReg doneReg bound clauseBase i).eval σ
      = σ3 := by
    unfold decodeThreeClauseProg
    rw [eval_seq, eval_seq, ← hσ1, ← hσ2, hσ3]
  have hL1' := literalAt_of_eq σ1 σ2 clauseBase i 0 c.l1
    (hfr2 0 (by norm_num) (by norm_num)).1 (hfr2 0 (by norm_num) (by norm_num)).2 hL1
  rw [htop]
  refine ⟨⟨literalAt_of_eq σ2 σ3 clauseBase i 0 c.l1
      (hfr3 0 (by norm_num) (by norm_num)).1 (hfr3 0 (by norm_num) (by norm_num)).2 hL1',
    literalAt_of_eq σ2 σ3 clauseBase i 1 c.l2
      (hfr3 1 (by norm_num) (by norm_num)).1 (hfr3 1 (by norm_num) (by norm_num)).2 hL2, hL3⟩, ?_⟩
  rw [hc3]; simp only [encodeThreeClause, List.length_append]; omega


end NPComplete.RAMToTM

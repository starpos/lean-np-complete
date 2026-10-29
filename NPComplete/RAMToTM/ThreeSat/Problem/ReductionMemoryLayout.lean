module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiLayout
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.ArenaAddress
public import NPComplete.SAT.ThreeSAT

/-!
# Memory layout for the self-written reduction program `d.p`

`CallerAbiLayout` fixes which two DSL cells publish the final `OutputSlice`
(`outAddrCell`/`outLenCell`) but says nothing about where a concrete reduction
keeps its intermediate clause arrays, work data, or decoded input. A reduction
program therefore needs a fixed convention for those cells; without it, the
decoded store could remain an unconstrained hypothesis. This module gives
reduction programs a shared stride-6 clause-row layout (three literals × two
cells), work-address helpers relative to a caller-supplied base, and a metadata
finalizer that publishes an output range as `ReductionOutput`.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)
open NPComplete.SAT
open Generic (outAddrCell outLenCell ReductionOutput)

/-! ## Literal / clause packing (flat cells, stride 6)

A `Literal` occupies two contiguous cells `(polarity, var)` with `polarity = 0`
for `pos` and `1` for `neg`. A `ThreeClause` is three literals back-to-back, so
clause row `i` lives at `clauseBase + 6 * i` with lanes `0 .. 5`. The reduction
uses this fixed-arity arena and reuses `arenaAddr` rather than inventing a second
address scheme. -/

def literalStride : ℕ := 2
def clauseStride : ℕ := 6

/-- Physical cell of lane `lane` in clause-row `i` of a clause array based at
    `clauseBase`. Lanes `0..5` pack three `(polarity, var)` pairs. -/
def clauseCell (clauseBase i lane : ℕ) : ℕ :=
  arenaAddr clauseBase clauseStride i lane

lemma clauseCell_eq (clauseBase i lane : ℕ) :
    clauseCell clauseBase i lane = clauseBase + clauseStride * i + lane := rfl

/-- Store cells of literal slot `j` (`0..2`) inside clause-row `i`: polarity then
    variable index. -/
def literalPolCell (clauseBase i j : ℕ) : ℕ :=
  clauseCell clauseBase i (literalStride * j)
def literalVarCell (clauseBase i j : ℕ) : ℕ :=
  clauseCell clauseBase i (literalStride * j + 1)

/-- `σ` holds literal `l` at clause-row `i`, slot `j`. -/
def LiteralAt (σ : Store) (clauseBase i j : ℕ) (l : Literal) : Prop :=
  match l with
  | .pos v =>
      σ (literalPolCell clauseBase i j) = 0 ∧ σ (literalVarCell clauseBase i j) = v
  | .neg v =>
      σ (literalPolCell clauseBase i j) = 1 ∧ σ (literalVarCell clauseBase i j) = v

/-- `σ` holds clause `c` as row `i` of the clause array based at `clauseBase`. -/
def ThreeClauseAt (σ : Store) (clauseBase i : ℕ) (c : ThreeClause) : Prop :=
  LiteralAt σ clauseBase i 0 c.l1 ∧
  LiteralAt σ clauseBase i 1 c.l2 ∧
  LiteralAt σ clauseBase i 2 c.l3

/-! ## Dynamic work region (base held in a DSL cell)

The work heap begins at a caller-chosen base that must sit at or past the end of the
input region (one past the encoded input bits) so it never collides with still-live
input bits. The base itself is a *runtime* value (typically that input-end offset
after reading cell `0`), held in a DSL cell the reduction names — no fixed
Fin-register reservation is imposed here. -/

/-- Address `σ baseReg + offset` computed on the DSL surface. -/
def workOffsetAddrExpr (baseReg offset : ℕ) : Expr :=
  Expr.add (Expr.reg baseReg) (Expr.const offset)

@[simp] lemma workOffsetAddrExpr_eval (baseReg offset : ℕ) (σ : Store) :
    (workOffsetAddrExpr baseReg offset).eval σ = σ baseReg + offset := by
  simp [workOffsetAddrExpr, Expr.eval]

@[simp] lemma workOffsetAddrExpr_cost (baseReg offset : ℕ) :
    (workOffsetAddrExpr baseReg offset).cost = 3 := by
  simp [workOffsetAddrExpr, Expr.cost]

/-- Indirect read of cell `σ baseReg + offset`. -/
def workReadExpr (baseReg offset : ℕ) : Expr :=
  Expr.regInd (workOffsetAddrExpr baseReg offset)

@[simp] lemma workReadExpr_eval (baseReg offset : ℕ) (σ : Store) :
    (workReadExpr baseReg offset).eval σ = σ (σ baseReg + offset) := by
  simp [workReadExpr, Expr.eval]

@[simp] lemma workReadExpr_cost (baseReg offset : ℕ) :
    (workReadExpr baseReg offset).cost = 4 := by
  simp [workReadExpr, Expr.cost]

/-- Indirect write of `eV` into cell `σ baseReg + offset`. -/
def workWriteProg (baseReg offset : ℕ) (eV : Expr) : Program :=
  Program.assignInd (workOffsetAddrExpr baseReg offset) eV

@[simp] lemma workWriteProg_eval (baseReg offset : ℕ) (eV : Expr) (σ : Store) :
    (workWriteProg baseReg offset eV).eval σ =
      writeReg σ (σ baseReg + offset) (eV.eval σ) := by
  simp [workWriteProg]

/-- A work write leaves every cell other than the targeted address untouched. -/
lemma workWriteProg_frame (baseReg offset r : ℕ) (eV : Expr) (σ : Store)
    (hne : r ≠ σ baseReg + offset) :
    (workWriteProg baseReg offset eV).eval σ r = σ r := by
  simp [workWriteProg_eval, writeReg, hne]

lemma workWriteProg_cost (baseReg offset : ℕ) (eV : Expr) (σ : Store) :
    (workWriteProg baseReg offset eV).cost σ =
      (workOffsetAddrExpr baseReg offset).cost + eV.cost + 1 := by
  simp [workWriteProg]

/-! ## Metadata finalizer → `ReductionOutput`

Publish a finished output range into the ABI cells. Length is written first
(`outLenCell = 1`), address last (`outAddrCell = 0`), so a stale length cannot
pair with a freshly written address if the two cells ever aliased under a
degenerate layout. Control cells holding the published values must themselves
lie outside `{outAddrCell, outLenCell}`. -/

/-- Write `outLenReg` into `outLenCell`, then `outBaseReg` into `outAddrCell`. -/
def finalizeOutputProg (outBaseReg outLenReg : ℕ) : Program :=
  Program.seq
    (Program.assign outLenCell (Expr.reg outLenReg))
    (Program.assign outAddrCell (Expr.reg outBaseReg))

/-- Control cells that may hold the values being published must not alias the
    two metadata cells the finalizer overwrites. -/
def FinalizeRegsOk (outBaseReg outLenReg : ℕ) : Prop :=
  outBaseReg ≠ outAddrCell ∧ outBaseReg ≠ outLenCell ∧
  outLenReg ≠ outAddrCell ∧ outLenReg ≠ outLenCell

lemma finalizeOutputProg_eval_len (outBaseReg outLenReg : ℕ) (σ : Store) :
    (finalizeOutputProg outBaseReg outLenReg).eval σ outLenCell = σ outLenReg := by
  simp only [finalizeOutputProg, eval_seq, eval_assign, Expr.eval]
  have hne : outLenCell ≠ outAddrCell := by
    simp only [outLenCell, outAddrCell]; omega
  rw [writeReg_diff _ _ _ _ hne, writeReg_same]

lemma finalizeOutputProg_eval_addr (outBaseReg outLenReg : ℕ) (σ : Store)
    (hok : FinalizeRegsOk outBaseReg outLenReg) :
    (finalizeOutputProg outBaseReg outLenReg).eval σ outAddrCell = σ outBaseReg := by
  obtain ⟨_, hBase1, _, _⟩ := hok
  simp only [finalizeOutputProg, eval_seq, eval_assign, Expr.eval]
  rw [writeReg_same]
  exact writeReg_diff σ outLenCell (σ outLenReg) outBaseReg hBase1

lemma finalizeOutputProg_frame (outBaseReg outLenReg r : ℕ) (σ : Store)
    (hr0 : r ≠ outAddrCell) (hr1 : r ≠ outLenCell) :
    (finalizeOutputProg outBaseReg outLenReg).eval σ r = σ r := by
  simp only [finalizeOutputProg, eval_seq, eval_assign, Expr.eval]
  rw [writeReg_diff _ _ _ _ hr0, writeReg_diff _ _ _ _ hr1]

/-- Finalizing does not disturb an output range that lives strictly above the two
    metadata cells (`base ≥ 2`). -/
lemma finalizeOutputProg_preserves_output (outBaseReg outLenReg base len : ℕ) (σ : Store)
    (hbase : 2 ≤ base) :
    ∀ i < len,
      (finalizeOutputProg outBaseReg outLenReg).eval σ (base + i) = σ (base + i) := by
  intro i _hi
  exact finalizeOutputProg_frame outBaseReg outLenReg (base + i) σ
    (by unfold outAddrCell; omega) (by unfold outLenCell; omega)

/-- From bitness of the output range and control cells outside metadata, the
    finalizer establishes `ReductionOutput`. -/
lemma reductionOutput_of_finalize (outBaseReg outLenReg : ℕ) (σ : Store)
    (hok : FinalizeRegsOk outBaseReg outLenReg)
    (hbits : ∀ i < σ outLenReg,
      σ (σ outBaseReg + i) = 0 ∨ σ (σ outBaseReg + i) = 1)
    (hbase : 2 ≤ σ outBaseReg) :
    ReductionOutput ((finalizeOutputProg outBaseReg outLenReg).eval σ)
      (σ outBaseReg) (σ outLenReg) := by
  have haddr := finalizeOutputProg_eval_addr outBaseReg outLenReg σ hok
  have hlen := finalizeOutputProg_eval_len outBaseReg outLenReg σ
  refine ⟨haddr, hlen, ?_⟩
  intro i hi
  have hpres := finalizeOutputProg_preserves_output outBaseReg outLenReg
    (σ outBaseReg) (σ outLenReg) σ hbase i hi
  simpa [hpres] using hbits i hi

end NPComplete.RAMToTM

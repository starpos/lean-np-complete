import NPComplete

/-!
# README example, non-module importer

Generated from `NPComplete/Test/ReadmeExample.lean` by `scripts/gen_readme_importer_tests.py`.
Expected: ok.
-/

open NPComplete.CookLevin NPComplete.RAMToTM NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

namespace ReadmeNonModuleExample

/-- A program that only reads the loaded input keeps every compiled operand within `bitLen (n + 1)`
bits, which is below `2 * (n + 1) ^ 2`. This discharges `compiled_operands_le` below. -/
lemma skip_operands (bits : Bits) :
    ∃ W, W ≤ 2 * (bits.length + 1) ^ 2 ∧ CompiledOperandBound Program.skip bits W := by
  refine ⟨bitLen (bits.length + 1), ?_, compiledOperandBound_of_programBoundedIn Program.skip bits
    (bits.length + 1) (by omega) ?_ trivial trivial⟩
  · have h := bitLen_le_succ (bits.length + 1)
    nlinarith [Nat.zero_le bits.length]
  · intro i
    match i with
    | 0 => simp [bitInputStore]
    | i + 1 => simp only [bitInputStore]; split <;> omega

/-- The language of bit strings whose first bit is `true`. -/
def FirstBit (x : Bits) : Prop := x.getD 0 false = true

/-- The program does nothing; the answer is already in cell `1` (bit `0` as `0`/`1`) of the
canonical input store. -/
def firstBitDecider : BoundedWhileDecider (fun x : Bits => x) (fun _ => True) FirstBit where
  p := Program.skip
  outReg := 1
  c := 1
  correct := fun x _ => by
    cases h : x.getD 0 false <;> simp [FirstBit, bitInputStore]
  cost_le := fun x _ => by simp
  bit_c := 2
  compiled_operands_le := fun x _ => skip_operands x

/-- `InP` from a decider written in the DSL. -/
lemma firstBit_inP : InP (fun x : Bits => x) FirstBit :=
  InP.of_boundedWhileDecider firstBitDecider

/-- Certificates of length at most `1` for the single instance `()`: the verifier sees
`pairBits [] w = false :: w`, so the certificate bit is cell `2`. -/
def verifierDecider :
    BoundedWhileDecider (fun xw : Unit × List Bool => pairBits [] xw.2) (fun _ => True)
      (fun xw => xw.2.getD 0 false = true) where
  p := Program.skip
  outReg := 2
  c := 1
  correct := fun xw _ => by
    obtain ⟨_, w⟩ := xw
    cases w with
    | nil => simp [pairBits, bitInputStore]
    | cons b w => cases b <;> simp [pairBits, bitInputStore]
  cost_le := fun xw _ => by simp
  bit_c := 2
  compiled_operands_le := fun xw _ => skip_operands _

/-- `InNP` from a verifier written in the DSL. -/
lemma unit_inNP : InNP (fun _ : Unit => ([] : Bits)) (fun _ => True) :=
  InNP.of_bounded_while_verifier (fun _ : Unit => ([] : Bits)) (fun _ => True) 1
    (fun _ w => w.getD 0 false = true)
    (fun _ => ⟨fun _ => ⟨[true], by simp, rfl⟩, fun _ => trivial⟩)
    verifierDecider

/-- Writes the output `encodeNat 1 = [false, true]` at base `4` with cell `0` = base and
cell `1` = length, as `of_forwardBitProducer` requires. The output ends with `true` and has
length `2`, the minimum allowed. -/
def constProducer : Program :=
  (Program.assign 0 (.const 4)).seq <|
  (Program.assign 1 (.const 2)).seq <|
  (Program.assign 4 (.const 0)).seq (Program.assign 5 (.const 1))

lemma constProducer_eval (σ : Store) :
    constProducer.eval σ = writeReg (writeReg (writeReg (writeReg σ 0 4) 1 2) 4 0) 5 1 := by
  simp [constProducer, Expr.eval]

/-- Only the two quantitative obligations are supplied; `ofBounds` fills in the rest. -/
def constDecider : BoundedWhileDecider (fun _ : Unit => ([] : Bits)) (fun _ => True)
    (fun _ => constProducer.eval (bitInputStore []) 0 = 1) :=
  BoundedWhileDecider.ofBounds (fun _ : Unit => ([] : Bits)) constProducer 0 8 9
    (fun x => by simp [constProducer, Expr.cost])
    (fun x => ⟨bitLen 8, by simpa using bitLen_le_succ 8,
      compiledOperandBound_of_programBoundedIn constProducer [] 8 (by omega)
        (fun i => by cases i <;> simp [bitInputStore])
        (by simp [constProducer, ProgramBoundedIn, ExprBoundedIn])
        (by simp [constProducer, ScanFree])⟩)

/-- A reduction from a one-point language to "equals `1`" on `ℕ` under `encodeNat`. -/
noncomputable def constReduction :
    PolyTimeReduction (fun _ : Unit => ([] : Bits)) encodeNat (fun _ => True) (fun n => n = 1) :=
  PolyTimeReduction.of_forwardBitProducer (f := fun _ : Unit => 1) constDecider
    4 (Polynomial.C 2)
    (fun x => by simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, writeReg])
    (fun x => by simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, encodeNat, writeReg])
    (fun x i hi => by
      simp [encodeNat] at hi
      interval_cases i <;> simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, encodeNat, writeReg])
    (fun x => by simp [encodeNat])
    (fun x => ⟨[false], by simp [encodeNat]⟩)
    (fun x => by simp [encodeNat])
    (fun x => by simp)

/-- NP-completeness of a language `L` needs `L ∈ NP` and one polynomial-time reduction from 3SAT
to `L`. The Cook-Levin construction is not repeated. -/
lemma target_NPComplete {β : Type} (eb : β → Bits) (L : β → Prop) (hL : InNP eb L)
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L) : NPComplete eb L :=
  NPComplete.of_threeSAT hL r

/-- Without membership in NP, the same reduction still gives NP-hardness. -/
lemma target_NPHard {β : Type} (eb : β → Bits) (L : β → Prop)
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L) : NPHard eb L :=
  NPHard.of_threeSAT r

/-- Hardness moves along a further reduction. -/
lemma target_NPHard_of_reduction {β γ : Type} {eb : β → Bits} {ec : γ → Bits}
    {L : β → Prop} {M : γ → Prop} (hL : NPHard eb L) (r : PolyTimeReduction eb ec L M) :
    NPHard ec M :=
  NPHard.of_reduction hL r

end ReadmeNonModuleExample

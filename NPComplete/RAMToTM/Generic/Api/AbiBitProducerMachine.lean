module

public import NPComplete.RAMToTM.Generic.Api.TransducerMachine
public import NPComplete.RAMToTM.Generic.Machine.CallerAbiMasterMachine
public import NPComplete.RAMToTM.Generic.Machine.CallerAbiContractBounded

/-!
# Bits-valued ABI producers as poly-time `FinTM2` machines

`tmRealizable_of_boundedWhileDecider` packages a `BoundedWhileDecider` as a Boolean
`TM2ComputableInPolyTime`.  Reduction producers instead publish a variable-length bit
string through the ABI (`ReductionOutput` + `masterMachineAbi`).  This file is the
Bits-output analogue: the same dispatcher, a polynomial majorant of
`master_init_to_halt_abi_bound` that never unfolds a concrete `bit_c` exponent, and an
`outputsFun` restricted to inputs whose RAM run is already known to halt.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.RAMToTM.Generic
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)
open NPComplete.BitEncoding (Bits)
open NPComplete.BoundedWhile (Program)
open Polynomial

/-! ## Polynomial majorants, generic in the memory/cost/output polynomials

The `G`-suffixed wrappers take `mP`/`cP`/`outP` as variables so their proofs may
`unfold`/`simp`/`ring` without ever seeing a concrete `bit_c` exponent.  Callers
specialize by rewriting an already-proved generic equation. -/

lemma abi_input_scan_bound (N : ℕ) :
    bitLen N + N * (4 * bitLen N + 10) + 3 ≤
      (N + 1) + N * (4 * (N + 1) + 10) + 3 := by
  have hbit := bitLen_le_succ N
  have hmul : N * (4 * bitLen N + 10) ≤ N * (4 * (N + 1) + 10) :=
    Nat.mul_le_mul_left N (Nat.add_le_add (Nat.mul_le_mul_left 4 hbit) le_rfl)
  exact Nat.add_le_add (Nat.add_le_add hbit hmul) le_rfl

lemma abi_cubic_mono {a b A C : ℕ} (hab : a ≤ b) :
    A * C * a ^ 3 ≤ A * C * b ^ 3 :=
  Nat.mul_le_mul_left (A * C) (Nat.pow_le_pow_left hab 3)

lemma abi_natToDigits_one_le_one : (natToDigits 1).length ≤ 1 := by
  simpa using natToDigits_length_le_bitLen 1

lemma mem0BoundMajorPoly_eval (N : ℕ) :
    mem0BoundMajorPoly.eval N = mem0BoundMajor N := by
  simp only [mem0BoundMajorPoly, mem0BoundMajor, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]

lemma abi_costBoundMajorPoly_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (N : ℕ) :
    (costBoundMajorPoly d).eval N = costBoundMajor d N := by
  unfold costBoundMajorPoly costBoundMajor
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]

noncomputable def abiTimePoly0 : Polynomial ℕ :=
  ((X + 1) + X * (4 * (X + 1) + 10) + 3)

lemma abiTimePoly0_eval (N : ℕ) :
    abiTimePoly0.eval N = (N + 1) + N * (4 * (N + 1) + 10) + 3 := by
  unfold abiTimePoly0
  simp

noncomputable def abiTimePoly1G {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  C (siteCsupAbi d) * (2 * C (siteGsupAbi d) + 1) ^ 2 * (mP + cP + 1) ^ 3

lemma abiTimePoly1G_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly1G d mP cP).eval N =
      siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 * (mP.eval N + cP.eval N + 1) ^ 3 := by
  unfold abiTimePoly1G
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_ofNat]

noncomputable def abiTimePoly2BaseG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  mP + 2 * C (siteGsupAbi d) * cP

lemma abiTimePoly2BaseG_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly2BaseG d mP cP).eval N =
      mP.eval N + 2 * siteGsupAbi d * cP.eval N := by
  unfold abiTimePoly2BaseG
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat]

noncomputable def abiTimePoly2TailG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  C (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
      bitLen 1 + bitLen 0 + 11) +
    C 12 * abiTimePoly2BaseG d mP cP

lemma abiTimePoly2TailG_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly2TailG d mP cP).eval N =
      (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
        bitLen 1 + bitLen 0 + 11) +
      12 * (abiTimePoly2BaseG d mP cP).eval N := by
  unfold abiTimePoly2TailG
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

noncomputable def abiTimePoly2G {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  C (siteCsupAbi d) * (2 * C (siteGsupAbi d) + 1) ^ 2 *
    (abiTimePoly2BaseG d mP cP + abiTimePoly2TailG d mP cP + 1) ^ 3

lemma abiTimePoly2G_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly2G d mP cP).eval N =
      siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
        ((abiTimePoly2BaseG d mP cP).eval N + (abiTimePoly2TailG d mP cP).eval N + 1) ^ 3 := by
  unfold abiTimePoly2G
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_ofNat]

noncomputable def abiTimePoly3 : Polynomial ℕ := 1

noncomputable def abiTimePoly4 (outP : Polynomial ℕ) : Polynomial ℕ :=
  outP * (16 * (2 * (outP + 1) + 2) + 2) + 1

lemma abiTimePoly4_eval (outP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly4 outP).eval N =
      outP.eval N * (16 * (2 * (outP.eval N + 1) + 2) + 2) + 1 := by
  unfold abiTimePoly4
  simp

noncomputable def abiRegPolyInnerG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  C (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
      bitLen 1 + bitLen 0 + 11) +
    C 12 * (mP + C (2 * siteGsupAbi d) * cP)

noncomputable def abiRegPolyG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) : Polynomial ℕ :=
  mP + C (2 * siteGsupAbi d) * cP + C (2 * siteGsupAbi d) * abiRegPolyInnerG d mP cP

lemma abiRegPolyG_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (mP cP : Polynomial ℕ) (N : ℕ) :
    (abiRegPolyG d mP cP).eval N =
      (mP.eval N + 2 * siteGsupAbi d * cP.eval N) +
        2 * siteGsupAbi d *
          (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
            bitLen 1 + bitLen 0 +
            12 * (mP.eval N + 2 * siteGsupAbi d * cP.eval N) + 11) := by
  unfold abiRegPolyG abiRegPolyInnerG
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

noncomputable def abiAddressPoly (outputBase : ℕ) (outP : Polynomial ℕ) : Polynomial ℕ :=
  C outputBase + outP

lemma abiAddressPoly_eval (outputBase : ℕ) (outP : Polynomial ℕ) (N : ℕ) :
    (abiAddressPoly outputBase outP).eval N = outputBase + outP.eval N := by
  unfold abiAddressPoly
  simp only [Polynomial.eval_add, Polynomial.eval_C]

noncomputable def abiRegisterPolyG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) : Polynomial ℕ :=
  abiRegPolyG d mP cP + abiAddressPoly outputBase outP + 1

lemma abiRegisterPolyG_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) (N : ℕ) :
    (abiRegisterPolyG d outputBase mP cP outP).eval N =
      (abiRegPolyG d mP cP).eval N + (abiAddressPoly outputBase outP).eval N + 1 := by
  unfold abiRegisterPolyG
  simp only [Polynomial.eval_add, Polynomial.eval_one]

noncomputable def abiTimePoly5G {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) : Polynomial ℕ :=
  outP *
    (32 * (abiRegisterPolyG d outputBase mP cP outP + 1) ^ 2 +
      16 * (4 * (abiAddressPoly outputBase outP + 1) + 4) + 6) + 1

lemma abiTimePoly5G_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly5G d outputBase mP cP outP).eval N =
      outP.eval N *
        (32 * ((abiRegisterPolyG d outputBase mP cP outP).eval N + 1) ^ 2 +
          16 * (4 * ((abiAddressPoly outputBase outP).eval N + 1) + 4) + 6) + 1 := by
  unfold abiTimePoly5G
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_ofNat]

noncomputable def abiTimePoly6G {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) : Polynomial ℕ :=
  mP + C (regBound (abiProgram d.p d.outReg) + 1) *
      (abiRegisterPolyG d outputBase mP cP outP + 1) + 25

lemma abiTimePoly6G_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) (N : ℕ) :
    (abiTimePoly6G d outputBase mP cP outP).eval N =
      mP.eval N +
        (regBound (abiProgram d.p d.outReg) + 1) *
          ((abiRegisterPolyG d outputBase mP cP outP).eval N + 1) + 25 := by
  unfold abiTimePoly6G
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]

noncomputable def abiTimePolyG {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) : Polynomial ℕ :=
  abiTimePoly0 + abiTimePoly1G d mP cP + abiTimePoly2G d mP cP + abiTimePoly3 +
    abiTimePoly4 outP + abiTimePoly5G d outputBase mP cP outP +
    abiTimePoly6G d outputBase mP cP outP

lemma abiTimePolyG_eval {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ)
    (mP cP outP : Polynomial ℕ) (N : ℕ) :
    (abiTimePolyG d outputBase mP cP outP).eval N =
      abiTimePoly0.eval N + (abiTimePoly1G d mP cP).eval N +
        (abiTimePoly2G d mP cP).eval N + abiTimePoly3.eval N +
        (abiTimePoly4 outP).eval N +
        (abiTimePoly5G d outputBase mP cP outP).eval N +
        (abiTimePoly6G d outputBase mP cP outP).eval N := by
  unfold abiTimePolyG
  simp only [Polynomial.eval_add]

/-- Concrete time polynomial: specialize the generic wrapper at the standard
    memory/cost majorants.  Downstream proofs must `rw` `abiTimePolyG_eval`, never
    `unfold` this definition at a concrete `bit_c`. -/
noncomputable def abiTimePoly {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (outputBase : ℕ) (outP : Polynomial ℕ) :
    Polynomial ℕ :=
  abiTimePolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP

/-! ## Raw `master_init_to_halt_abi_bound` summands -/

@[irreducible] noncomputable def abiRawTerm0 {α : Type} {enc : α → Bits} {D L : α → Prop}
    (_d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  bitLen (enc x).length + (enc x).length * (4 * bitLen (enc x).length + 10) + 3

@[irreducible] noncomputable def abiRawTerm1 {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
    (mem0Bound d x + costBound d x + 1) ^ 3

@[irreducible] noncomputable def abiRawTerm2 {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) : ℕ :=
  siteCsupAbi d * (2 * siteGsupAbi d + 1) ^ 2 *
    (mem0Bound d x + 2 * siteGsupAbi d * costBound d x +
      (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
        bitLen 1 + bitLen 0 +
        12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11) + 1) ^ 3

@[irreducible] def abiRawTerm3 : ℕ := 1

@[irreducible] noncomputable def abiRawTerm4 (outputLength : ℕ) : ℕ :=
  outputLength *
    (16 * (2 * (natToDigits outputLength).length + (natToDigits 1).length + 1) + 2) + 1

@[irreducible] noncomputable def abiRawTerm5 (outputBase outputLength : ℕ) (log : WriteLog) : ℕ :=
  outputLength *
    (32 * ((encodeLog log).length +
        (natToDigits (outputBase + outputLength)).length + 1) ^ 2 +
      16 * (2 * (natToDigits (outputBase + outputLength)).length +
        (natToDigits 1).length + bitLen (outputBase + outputLength) + bitLen 1 + 1) +
      6) + 1

@[irreducible] noncomputable def abiRawTerm6 {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) : ℕ :=
  ((0 + 1) + ((0 + 1) + ((0 + 1 + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) +
        (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1)) +
      (((encodeLog log).length + 1) +
        (regBound (abiProgram d.p d.outReg) *
          ((max (regSizeBoundAbi d x) (natToDigits (outputBase + outputLength)).length)
            + 1) + 1)))) + 1) + 2

@[irreducible] noncomputable def abiRawBound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) : ℕ :=
  abiRawTerm0 d x + abiRawTerm1 d x + abiRawTerm2 d x + abiRawTerm3 +
    abiRawTerm4 outputLength + abiRawTerm5 outputBase outputLength log +
    abiRawTerm6 d x outputBase outputLength log

lemma abiRawTerm0_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    abiRawTerm0 d x ≤ abiTimePoly0.eval (enc x).length := by
  unfold abiRawTerm0
  rw [abiTimePoly0_eval]
  exact abi_input_scan_bound _

lemma abiRawTerm1_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    abiRawTerm1 d x ≤
      (abiTimePoly1G d mem0BoundMajorPoly (costBoundMajorPoly d)).eval (enc x).length := by
  unfold abiRawTerm1
  have hmem := mem0Bound_le_major d x
  have hcost := costBound_le_major d x
  rw [abiTimePoly1G_eval, mem0BoundMajorPoly_eval, abi_costBoundMajorPoly_eval]
  exact abi_cubic_mono (by omega)

lemma abiRawTerm2_inner_mono {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    mem0Bound d x + 2 * siteGsupAbi d * costBound d x +
      (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
        bitLen 1 + bitLen 0 +
        12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11) + 1 ≤
    mem0BoundMajor (enc x).length + 2 * siteGsupAbi d * costBoundMajor d (enc x).length +
      ((2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
          bitLen 1 + bitLen 0 + 11) +
        12 * (mem0BoundMajor (enc x).length +
          2 * siteGsupAbi d * costBoundMajor d (enc x).length)) + 1 := by
  have hmem := mem0Bound_le_major d x
  have hcost := costBound_le_major d x
  have hXY : mem0Bound d x + 2 * siteGsupAbi d * costBound d x ≤
      mem0BoundMajor (enc x).length +
        2 * siteGsupAbi d * costBoundMajor d (enc x).length := by gcongr
  omega

lemma abiRawTerm2_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    abiRawTerm2 d x ≤
      (abiTimePoly2G d mem0BoundMajorPoly (costBoundMajorPoly d)).eval (enc x).length := by
  have hinner := abiRawTerm2_inner_mono d x
  rw [abiTimePoly2G_eval, abiTimePoly2TailG_eval, abiTimePoly2BaseG_eval,
    mem0BoundMajorPoly_eval, abi_costBoundMajorPoly_eval]
  unfold abiRawTerm2
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinner 3)

lemma abiRawTerm4_bound (outputLength : ℕ) (outP : Polynomial ℕ) (N : ℕ)
    (hL : outputLength ≤ outP.eval N) :
    abiRawTerm4 outputLength ≤ (abiTimePoly4 outP).eval N := by
  unfold abiRawTerm4
  rw [abiTimePoly4_eval]
  have hdl : (natToDigits outputLength).length ≤ outP.eval N + 1 := by
    have h1 := natToDigits_length_le_bitLen outputLength
    have h2 := bitLen_le_succ outputLength
    omega
  have h1 := abi_natToDigits_one_le_one
  have hinner : 16 * (2 * (natToDigits outputLength).length +
      (natToDigits 1).length + 1) + 2 ≤
      16 * (2 * (outP.eval N + 1) + 2) + 2 := by
    have : 2 * (natToDigits outputLength).length + (natToDigits 1).length + 1 ≤
        2 * (outP.eval N + 1) + 2 := by omega
    exact Nat.add_le_add (Nat.mul_le_mul_left 16 this) le_rfl
  exact Nat.add_le_add (Nat.mul_le_mul hL hinner) le_rfl

lemma abi_reg_size_le_reg_poly_g {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α) :
    regSizeBoundAbi d x ≤
      (abiRegPolyG d mem0BoundMajorPoly (costBoundMajorPoly d)).eval (enc x).length := by
  have hmem := mem0Bound_le_major d x
  have hcost := costBound_le_major d x
  rw [abiRegPolyG_eval, mem0BoundMajorPoly_eval, abi_costBoundMajorPoly_eval]
  unfold regSizeBoundAbi
  have hab : mem0Bound d x + 2 * siteGsupAbi d * costBound d x ≤
      mem0BoundMajor (enc x).length +
        2 * siteGsupAbi d * costBoundMajor d (enc x).length := by gcongr
  have htail :
      2 * siteGsupAbi d *
          (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
            bitLen 1 + bitLen 0 +
            12 * (mem0Bound d x + 2 * siteGsupAbi d * costBound d x) + 11) ≤
      2 * siteGsupAbi d *
          (2 * bitLen d.outReg + 2 * bitLen outAddrCell + 2 * bitLen outLenCell +
            bitLen 1 + bitLen 0 +
            12 * (mem0BoundMajor (enc x).length +
              2 * siteGsupAbi d * costBoundMajor d (enc x).length) + 11) := by gcongr
  omega

lemma abi_address_digits_le (outputBase outputLength : ℕ) (outP : Polynomial ℕ) (N : ℕ)
    (hL : outputLength ≤ outP.eval N) :
    (natToDigits (outputBase + outputLength)).length ≤
      (abiAddressPoly outputBase outP).eval N + 1 := by
  have h1 := natToDigits_length_le_bitLen (outputBase + outputLength)
  have h2 := bitLen_le_succ (outputBase + outputLength)
  rw [abiAddressPoly_eval]
  omega

lemma abi_address_bitLen_le (outputBase outputLength : ℕ) (outP : Polynomial ℕ) (N : ℕ)
    (hL : outputLength ≤ outP.eval N) :
    bitLen (outputBase + outputLength) ≤
      (abiAddressPoly outputBase outP).eval N + 1 := by
  have h2 := bitLen_le_succ (outputBase + outputLength)
  rw [abiAddressPoly_eval]
  omega

lemma abiRawTerm5_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) (outP : Polynomial ℕ)
    (hL : outputLength ≤ outP.eval (enc x).length)
    (hLog : (encodeLog log).length ≤ regSizeBoundAbi d x) :
    abiRawTerm5 outputBase outputLength log ≤
      (abiTimePoly5G d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
        (enc x).length := by
  have hReg := abi_reg_size_le_reg_poly_g d x
  have hdig := abi_address_digits_le outputBase outputLength outP (enc x).length hL
  have hbit := abi_address_bitLen_le outputBase outputLength outP (enc x).length hL
  have h1 := (natToDigits_length_le_bitLen 1).trans (bitLen_le_succ 1)
  have hbit1 := bitLen_le_succ 1
  have henc : (encodeLog log).length ≤
      (abiRegPolyG d mem0BoundMajorPoly (costBoundMajorPoly d)).eval (enc x).length :=
    hLog.trans hReg
  have hsum : (encodeLog log).length +
      (natToDigits (outputBase + outputLength)).length + 1 ≤
      (abiRegisterPolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
        (enc x).length + 1 := by
    rw [abiRegisterPolyG_eval]
    omega
  have hlin : 2 * (natToDigits (outputBase + outputLength)).length +
      (natToDigits 1).length + bitLen (outputBase + outputLength) + bitLen 1 + 1 ≤
      4 * ((abiAddressPoly outputBase outP).eval (enc x).length + 1) + 4 := by
    omega
  rw [abiTimePoly5G_eval]
  unfold abiRawTerm5
  have hinner :
      32 * ((encodeLog log).length +
          (natToDigits (outputBase + outputLength)).length + 1) ^ 2 +
        16 * (2 * (natToDigits (outputBase + outputLength)).length +
          (natToDigits 1).length + bitLen (outputBase + outputLength) + bitLen 1 + 1) +
        6 ≤
      32 * ((abiRegisterPolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
          (enc x).length + 1) ^ 2 +
        16 * (4 * ((abiAddressPoly outputBase outP).eval (enc x).length + 1) + 4) + 6 := by
    refine Nat.add_le_add (Nat.add_le_add ?_ ?_) le_rfl
    · exact Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hsum 2)
    · exact Nat.mul_le_mul_left 16 hlin
  exact Nat.add_le_add (Nat.mul_le_mul hL hinner) le_rfl

def abiCleanupTerm (lg K M : ℕ) : ℕ :=
  ((0 + 1) + ((0 + 1) + ((0 + 1 + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) +
    (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1)) +
    (((lg + 1) + (K * (M + 1) + 1))))) + 1) + 2

lemma abiCleanupTerm_bound {P K lg M Reg : ℕ}
    (hlg : lg ≤ Reg) (hM : M ≤ Reg) :
    abiCleanupTerm lg K M ≤ P + (K + 1) * (Reg + 1) + 25 := by
  have hmul : K * (M + 1) ≤ K * (Reg + 1) :=
    Nat.mul_le_mul_left K (Nat.add_le_add hM le_rfl)
  unfold abiCleanupTerm
  rw [Nat.add_mul]
  omega

lemma abiRawTerm6_eq_cleanup {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) :
    abiRawTerm6 d x outputBase outputLength log =
      abiCleanupTerm (encodeLog log).length
        (regBound (abiProgram d.p d.outReg))
        (max (regSizeBoundAbi d x)
          (natToDigits (outputBase + outputLength)).length) := by
  unfold abiRawTerm6 abiCleanupTerm
  rfl

lemma abiRawTerm6_bound {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) (outP : Polynomial ℕ)
    (hL : outputLength ≤ outP.eval (enc x).length)
    (hLog : (encodeLog log).length ≤ regSizeBoundAbi d x) :
    abiRawTerm6 d x outputBase outputLength log ≤
      (abiTimePoly6G d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
        (enc x).length := by
  have hReg := abi_reg_size_le_reg_poly_g d x
  have hdig := abi_address_digits_le outputBase outputLength outP (enc x).length hL
  have hlg : (encodeLog log).length ≤
      (abiRegisterPolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
        (enc x).length := by
    rw [abiRegisterPolyG_eval]
    exact hLog.trans (hReg.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hM : max (regSizeBoundAbi d x)
      (natToDigits (outputBase + outputLength)).length ≤
      (abiRegisterPolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP).eval
        (enc x).length := by
    rw [abiRegisterPolyG_eval]
    refine max_le (hReg.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))) ?_
    have haddr : (abiAddressPoly outputBase outP).eval (enc x).length + 1 ≤
        (abiRegPolyG d mem0BoundMajorPoly (costBoundMajorPoly d)).eval (enc x).length +
          (abiAddressPoly outputBase outP).eval (enc x).length + 1 :=
      Nat.le_add_left _ _
    exact hdig.trans haddr
  rw [abiRawTerm6_eq_cleanup, abiTimePoly6G_eval, mem0BoundMajorPoly_eval]
  exact abiCleanupTerm_bound (P := mem0BoundMajor (enc x).length) hlg hM

lemma abiRawBound_le_timePoly {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (x : α)
    (outputBase outputLength : ℕ) (log : WriteLog) (outP : Polynomial ℕ)
    (hL : outputLength ≤ outP.eval (enc x).length)
    (hLog : (encodeLog log).length ≤ regSizeBoundAbi d x) :
    abiRawBound d x outputBase outputLength log ≤
      (abiTimePoly d outputBase outP).eval (enc x).length := by
  have h0 := abiRawTerm0_bound d x
  have h1 := abiRawTerm1_bound d x
  have h2 := abiRawTerm2_bound d x
  have h3 : abiRawTerm3 ≤ abiTimePoly3.eval (enc x).length := by
    unfold abiRawTerm3 abiTimePoly3; simp
  have h4 := abiRawTerm4_bound outputLength outP (enc x).length hL
  have h5 := abiRawTerm5_bound d x outputBase outputLength log outP hL hLog
  have h6 := abiRawTerm6_bound d x outputBase outputLength log outP hL hLog
  unfold abiRawBound
  rw [show abiTimePoly d outputBase outP =
      abiTimePolyG d outputBase mem0BoundMajorPoly (costBoundMajorPoly d) outP from rfl,
    abiTimePolyG_eval]
  omega

/-! ## Closing `TM2ComputableInPolyTime` -/

lemma masterMachineAbi_haltList {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (output : Bits)
    (sf : Generic.MasterState (abiProgram d.p d.outReg))
    (Sgf : ∀ k, List (Generic.EmitΓ (abiProgram d.p d.outReg) k))
    (log : WriteLog) (outputBase : ℕ)
    (hsf : sf = Generic.MasterState.canonical)
    (hout : Sgf Generic.EmitK.out =
      (OutputSlice.physicalBits log ⟨outputBase, output.length⟩).reverse)
    (hReg : ∀ i : Fin (regBound (abiProgram d.p d.outReg)),
      Sgf (Generic.EmitK.base (Generic.Kg.reg i)) = [])
    (hMem : Sgf (Generic.EmitK.base Generic.Kg.mem) = [])
    (hScr : ∀ sk : Generic.ScratchKind, Sgf (Generic.EmitK.base (Generic.Kg.scratch sk)) = [])
    (hIo : Sgf (Generic.EmitK.base Generic.Kg.io) = [])
    (hCd : Sgf Generic.EmitK.countdown = [])
    (hBits : OutputSlice.physicalBits log ⟨outputBase, output.length⟩ = output.reverse) :
    (⟨none, sf, Sgf⟩ : (masterMachineAbi d).Cfg) =
      Turing.haltList (masterMachineAbi d) output := by
  rw [hsf]
  congr 1
  funext k
  cases k with
  | base k =>
      cases k with
      | reg i => exact hReg i
      | mem => exact hMem
      | io => exact hIo
      | scratch sk => exact hScr sk
  | out =>
      have hout' := hout
      rw [hBits] at hout'
      simpa [Turing.haltList, List.reverse_reverse] using hout'
  | countdown => exact hCd

/-- Bits-output analogue of `tmRealizable_of_boundedWhileDecider`: a
    `BoundedWhileDecider` whose program publishes `eb (f x)` through the ABI is a
    poly-time `FinTM2` computer of `f`. -/
noncomputable def tm2ComputableInPolyTime_of_abiBitProducer
    {α β : Type} {enc : α → Bits} {eb : β → Bits} {D L : α → Prop} {f : α → β}
    (d : BoundedWhileDecider enc D L) (hD : ∀ x, D x) (outputBase : ℕ)
    (outP : Polynomial ℕ)
    (hOut : ∀ x, ReductionOutput (d.p.eval (bitInputStore (enc x)))
      outputBase (eb (f x)).length)
    (hBits : ∀ x (log : WriteLog),
      (fun a => lookupD log a 0) = d.p.eval (bitInputStore (enc x)) →
      OutputSlice.physicalBits log ⟨outputBase, (eb (f x)).length⟩ = (eb (f x)).reverse)
    (houtLen : ∀ x, (eb (f x)).length ≤ outP.eval (enc x).length) :
    Turing.TM2ComputableInPolyTime enc eb f := by
  classical
  refine {
    tm := masterMachineAbi d
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := abiTimePoly d outputBase outP
    outputsFun := ?_ }
  intro x
  choose n sf Sgf log hrun hsf hout hReg hMem hScr hIo hCd hLog hlogLookup hn using
    Generic.master_init_to_halt_abi_bound d x (hD x) outputBase (eb (f x)).length (hOut x)
  have hbound : n ≤ (abiTimePoly d outputBase outP).eval (enc x).length := by
    have hraw : n ≤ abiRawBound d x outputBase (eb (f x)).length log := by
      simpa only [abiRawBound, abiRawTerm0, abiRawTerm1, abiRawTerm2, abiRawTerm3,
        abiRawTerm4, abiRawTerm5, abiRawTerm6, Nat.add_assoc] using hn
    exact hraw.trans (abiRawBound_le_timePoly d x outputBase (eb (f x)).length log outP
      (houtLen x) hLog)
  refine ⟨⟨n, ?_⟩, hbound⟩
  have hrun' : (flip Bind.bind (masterMachineAbi d).step)^[n]
      (some (Turing.initList (masterMachineAbi d) (enc x))) =
      some ⟨none, sf, Sgf⟩ := by
    rw [initList_masterMachineAbi, masterMachineAbi_step]
    exact hrun
  have hinput : List.map (Equiv.refl Bool).invFun (enc x) = enc x := by simp
  have houtput : List.map (Equiv.refl Bool).invFun (eb (f x)) = eb (f x) := by simp
  rw [hinput, hrun']
  have hcfg := masterMachineAbi_haltList d (eb (f x)) sf Sgf log outputBase
    hsf hout hReg hMem hScr hIo hCd (hBits x log hlogLookup)
  simp only [houtput, Option.map_some]
  rw [hcfg]

/-- `emit_run_length_bounded` prepends pushed bits, so the TM2 output tape is
    `physicalBits.reverse`. The theorem above therefore requires a RAM buffer with
    `physicalBits = output.reverse`, as produced by a copy/reverse epilogue. Writers
    that emit bits in logical address order use this wrapper; the computed output is
    the reverse of the published RAM bits. -/
noncomputable def tm2ComputableInPolyTime_of_abiBitProducer_forward
    {α β : Type} {enc : α → Bits} {eb : β → Bits} {D L : α → Prop} {f : α → β}
    (d : BoundedWhileDecider enc D L) (hD : ∀ x, D x) (outputBase : ℕ)
    (outP : Polynomial ℕ)
    (hOut : ∀ x, ReductionOutput (d.p.eval (bitInputStore (enc x)))
      outputBase (eb (f x)).length)
    (hBits : ∀ x (log : WriteLog),
      (fun a => lookupD log a 0) = d.p.eval (bitInputStore (enc x)) →
      OutputSlice.physicalBits log ⟨outputBase, (eb (f x)).length⟩ = eb (f x))
    (houtLen : ∀ x, (eb (f x)).length ≤ outP.eval (enc x).length) :
    Turing.TM2ComputableInPolyTime enc (fun l : List Bool => l)
      (fun x => (eb (f x)).reverse) :=
  tm2ComputableInPolyTime_of_abiBitProducer (enc := enc)
    (eb := fun l : List Bool => l) (f := fun x => (eb (f x)).reverse)
    d hD outputBase outP
    (fun x => by simpa [List.length_reverse] using hOut x)
    (fun x log hlog => by
      have h := hBits x log hlog
      simpa [List.reverse_reverse] using h)
    (fun x => by simpa [List.length_reverse] using houtLen x)

end NPComplete.RAMToTM

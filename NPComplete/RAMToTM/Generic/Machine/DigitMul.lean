module

public import NPComplete.RAMToTM.Generic.Machine.Binary
public import NPComplete.RAMToTM.Generic.Machine.DigitAdd
public import NPComplete.RAMToTM.Generic.Machine.DigitSub
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Digit-serial multiply-accumulate on `FinTM2` stacks

`mul rd rs rt`'s RAM semantics is unbounded natural multiplication (`regs rd ← regs rs *
regs rt`, no truncation). Grade-school long multiplication needs, for each digit of `rt`, a full
pass over `rs` — unlike `add`/`sub`, which each need only one pass over the two operands.

The design fuses row-computation and
accumulation into a single Horner-scheme ripple loop instead of materializing an unshifted "row"
and merging it via a separate `addRaw` pass: `mulAddDigit a d b carry` computes `a*d + b + carry`
in one digit-position step (`a` from the multiplicand, `d` the *fixed* multiplier digit for this
outer iteration, `b` from the *already-shifted* accumulator, `carry` threaded through). Iterating
this lockstep over the multiplicand and the shifted accumulator (`mulAddRaw`) computes one full
Horner step `acc ↦ acc*16 + multiplicand*d` directly, with no intermediate row list.

Unlike `DigitAdd.addDigits` (carry a `Bool`, since `a+b+carryIn ≤ 31`) or `DigitSub.subDigits`
(borrow a `Bool`), `mulAddDigit`'s carry must itself be a `Digit`: `a*d+b+carry ≤ 15*15+15+15 =
255`, so the quotient `v/16` can reach up to `15` — still a single digit, but no longer boolean.

`mulAddRaw`'s termination measure is `2*(lhs.length+acc.length) + (carry live?)`, not the plain
sum `DigitAdd.addMeasure` uses: unlike `addDigits` (where a nonempty-vs-empty step, e.g.
`a b:=0,carryIn:=false`, can never itself produce a carry, since `a+0+0 ≤ 15 < 16`),
`mulAddDigit` *can* spawn a fresh nonzero carry from a single nonempty digit against an already-
exhausted other operand (`a*d` alone can reach `225`), so a plain unscaled sum can plateau
exactly at the step that empties the last operand while the carry bonus flips `0 → 1`. The `×2`
gives enough slack for the length term (which strictly drops by at least 1 whenever not both
operands are already empty) to always outweigh that flip.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- Multiply-accumulate one digit position: `a*d + b + carryIn`, split into an output digit and
    an outgoing carry. Unlike `DigitAdd.addDigits`/`DigitSub.subDigits`, the carry here is itself
    a `Digit` (not `Bool`): `a.val*d.val+b.val+carry.val ≤ 15*15+15+15 = 255`, so `v/16 ≤ 15`
    still fits. -/
def mulAddDigit (a d b carry : Digit) : Digit × Digit :=
  let v := a.val * d.val + b.val + carry.val
  (⟨v % 16, by omega⟩, ⟨v / 16, by
    have ha := a.isLt
    have hd := d.isLt
    have hb := b.isLt
    have hc := carry.isLt
    have hv : v ≤ 255 := by simp only [v]; nlinarith
    omega⟩)

/-- `mulAddDigit` is a faithful base-16 multiply-accumulate: output digit plus `16 *` outgoing
    carry equals the full multiply-accumulate value, mirroring `DigitAdd.addDigits_correct`. -/
lemma mulAddDigit_correct (a d b carry : Digit) :
    (mulAddDigit a d b carry).1.val + 16 * (mulAddDigit a d b carry).2.val
      = a.val * d.val + b.val + carry.val := by
  simp only [mulAddDigit]
  have ha := a.isLt
  have hd := d.isLt
  have hb := b.isLt
  have hc := carry.isLt
  have hv : a.val * d.val + b.val + carry.val ≤ 255 := by nlinarith
  omega

/-- Termination measure for `mulAddRaw`'s ripple loop: `2 * (total remaining digits) + (carry
    live?)`. The `×2` gives enough slack to absorb the carry bonus jumping `0 → 1` in the same
    step that both lists become simultaneously exhausted (module docstring) — a plain, unscaled
    sum (`DigitAdd.addMeasure`'s shape) is not enough here, unlike for `addDigits`. -/
def mulAddMeasure (lhs acc : List Digit) (carry : Digit) : ℕ :=
  2 * (lhs.length + acc.length) + (if carry.val = 0 then 0 else 1)

/-- One `mulAddRaw` iteration strictly decreases `mulAddMeasure`, in every case except the
    excluded base case (both lists empty, no carry). -/
lemma mulAddMeasure_decreases (lhs acc : List Digit) (d carry : Digit)
    (hbase : ¬ (lhs = [] ∧ acc = [] ∧ carry.val = 0)) :
    mulAddMeasure lhs.tail acc.tail (mulAddDigit (lhs.headD 0) d (acc.headD 0) carry).2 + 1
      ≤ mulAddMeasure lhs acc carry := by
  have hacctail : acc.tail.length ≤ acc.length := by cases acc <;> simp
  rcases lhs with _ | ⟨la, ls⟩
  · rcases acc with _ | ⟨aa, as⟩
    · have hcne : carry.val ≠ 0 := by
        intro hc0; exact hbase ⟨rfl, rfl, hc0⟩
      have hclt := carry.isLt
      have hcond : (mulAddDigit (([] : List Digit).headD 0) d (([] : List Digit).headD 0)
          carry).2.val = 0 := by
        simp only [mulAddDigit, List.headD_nil, Fin.val_zero, zero_mul, zero_add]
        exact Nat.div_eq_of_lt hclt
      simp only [mulAddMeasure, List.tail_nil, List.length_nil, ite_eq_left hcond, ite_eq_right hcne]
      omega
    · simp only [mulAddMeasure, List.tail_nil, List.tail_cons, List.length_nil, List.length_cons]
      split_ifs <;> omega
  · simp only [mulAddMeasure, List.tail_cons, List.length_cons]
    split_ifs <;> omega

/-- The inner ripple loop: multiply-accumulate `lhs` by the (fixed, throughout this call) digit
    `d` onto `acc`, position-aligned, threading a running carry — the LSB-first pure model of the
    fused `mulAddDigit` core, mirroring `DigitAdd.addRaw`'s shape. Continues while the carry is
    still live (not `DigitSub.subRawFull`'s "stop regardless" discipline): once both `lhs` and
    `acc` are exhausted, a live carry (always `< 16`, so `0*d+0+carry < 16`) drains in exactly one
    more step. -/
-- The termination proof passes `_h`, the stopping condition, to `mulAddMeasure_decreases`.  It is
-- underscored because the unused-variable linter does not look inside termination proofs.
def mulAddRaw (lhs acc : List Digit) (d carry : Digit) : List Digit :=
  if _h : lhs = [] ∧ acc = [] ∧ carry.val = 0 then []
  else
    let dc := mulAddDigit (lhs.headD 0) d (acc.headD 0) carry
    dc.1 :: mulAddRaw lhs.tail acc.tail d dc.2
termination_by mulAddMeasure lhs acc carry
decreasing_by
  have := mulAddMeasure_decreases lhs acc d carry _h
  omega

/-- With both inputs empty, `mulAddRaw` outputs at most one digit: a live carry drains in exactly
    one step. -/
lemma mulAddRaw_nilnil_length_le (d carry : Digit) :
    (mulAddRaw ([] : List Digit) [] d carry).length ≤ 1 := by
  by_cases hc : carry.val = 0
  · rw [mulAddRaw, dite_eq_left ⟨rfl, rfl, hc⟩]; simp
  · have hne : ¬ (([] : List Digit) = [] ∧ ([] : List Digit) = [] ∧ carry.val = 0) :=
      fun ⟨_, _, h⟩ => hc h
    have hcond : (mulAddDigit (([] : List Digit).headD 0) d (([] : List Digit).headD 0)
        carry).2.val = 0 := by
      simp only [mulAddDigit, List.headD_nil, Fin.val_zero, zero_mul, zero_add]
      exact Nat.div_eq_of_lt carry.isLt
    rw [mulAddRaw, dite_eq_right hne]
    simp only [List.tail_nil, List.length_cons]
    rw [mulAddRaw, dite_eq_left ⟨rfl, rfl, hcond⟩]
    simp

/-- `mulAddRaw`'s output is at most one digit longer than its larger input. This tighter bound
    avoids the generic termination-measure slack compounding across the outer multiplication
    loop. When both inputs are empty, any live carry is consumed in one final step. -/
lemma mulAddRaw_length_le (lhs acc : List Digit) (d carry : Digit) :
    (mulAddRaw lhs acc d carry).length ≤ max lhs.length acc.length + 1 := by
  have key : ∀ n (lhs acc : List Digit) (d carry : Digit), lhs.length + acc.length ≤ n →
      (mulAddRaw lhs acc d carry).length ≤ max lhs.length acc.length + 1 := by
    intro n
    induction n with
    | zero =>
        intro lhs acc d carry hle
        have hlhs : lhs = [] := List.length_eq_zero_iff.mp (by omega)
        have hacc : acc = [] := List.length_eq_zero_iff.mp (by omega)
        subst hlhs; subst hacc
        simpa using mulAddRaw_nilnil_length_le d carry
    | succ n ih =>
        intro lhs acc d carry hle
        by_cases hbase : lhs = [] ∧ acc = [] ∧ carry.val = 0
        · rw [mulAddRaw, dite_eq_left hbase]; simp
        · by_cases hempty : lhs = [] ∧ acc = []
          · obtain ⟨hlhs, hacc⟩ := hempty
            subst hlhs; subst hacc
            simpa using mulAddRaw_nilnil_length_le d carry
          · rw [mulAddRaw, dite_eq_right hbase]
            simp only [List.length_cons]
            have hIH := ih lhs.tail acc.tail d
              (mulAddDigit (lhs.headD 0) d (acc.headD 0) carry).2
              (by rw [List.length_tail, List.length_tail]; omega)
            rw [List.length_tail, List.length_tail] at hIH
            have hne : ¬ (lhs.length = 0 ∧ acc.length = 0) := by
              rintro ⟨hl, ha⟩
              exact hempty ⟨List.length_eq_zero_iff.mp hl, List.length_eq_zero_iff.mp ha⟩
            omega
  exact key (lhs.length + acc.length) lhs acc d carry le_rfl

/-- `mulAddRaw`'s numeric semantics: the LSB-first value it represents is `lhs`'s value times
    `d`, plus `acc`'s value, plus the incoming carry — one full multiply-accumulate. Mirrors
    `DigitAdd.digitsToNat_addRaw`. -/
lemma digitsToNat_mulAddRaw (lhs acc : List Digit) (d carry : Digit) :
    digitsToNat (mulAddRaw lhs acc d carry)
      = digitsToNat lhs * d.val + digitsToNat acc + carry.val := by
  induction lhs, acc, carry using mulAddRaw.induct (d := d) with
  | case1 lhs acc carry hbase =>
      obtain ⟨hL, hA, hc⟩ := hbase
      subst hL; subst hA
      have hc0 : carry.val = 0 := hc
      rw [show mulAddRaw ([] : List Digit) [] d carry = [] by
        rw [mulAddRaw]; simp [hc0]]
      simp [digitsToNat, hc0]
  | case2 lhs acc carry hbase dc ih =>
      have hunfold : mulAddRaw lhs acc d carry = dc.1 :: mulAddRaw lhs.tail acc.tail d dc.2 := by
        rw [mulAddRaw, dite_eq_right hbase]
      rw [hunfold]
      have hcons : digitsToNat (dc.1 :: mulAddRaw lhs.tail acc.tail d dc.2)
          = dc.1.val + 16 * digitsToNat (mulAddRaw lhs.tail acc.tail d dc.2) := by
        simp [digitsToNat, Nat.ofDigits_cons]
      rw [hcons, ih]
      have hcorrect := mulAddDigit_correct (lhs.headD 0) d (acc.headD 0) carry
      have hL := digitsToNat_headD_tail lhs
      have hA := digitsToNat_headD_tail acc
      simp only [dc]
      nlinarith [hcorrect, hL, hA]

/-- The sequence of `lhs`-digits `mulAddRaw`'s loop actually consumes (real digit, or `0` once
    `lhs` is exhausted but `acc`/`carry` still need more steps) — same recursion/termination as
    `mulAddRaw`, tracking the *other* half of each step's inputs. What `GenericMul.lean`'s
    `mulAddLoop` pushes onto `copyScratch` while it runs: since the loop's own stopping condition
    depends on *both* `lhs` and `acc` (and `acc`, the running product, typically outgrows `lhs`
    across outer iterations), the loop may keep rippling past the point `lhs` is exhausted, and at
    each such step still stashes a (zero) digit for `restoreLhs` to replay back — harmlessly
    padding `lhs`'s restored representation with trailing (MSB-side) zero digits rather than
    reproducing it verbatim (`digitsToNat_mulAddTraceA` below: this never changes the represented
    *value*, which is all the outer Horner loop's own invariant needs). -/
-- The termination proof passes `_h`, the stopping condition, to `mulAddMeasure_decreases`.  It is
-- underscored because the unused-variable linter does not look inside termination proofs.
def mulAddTraceA (lhs acc : List Digit) (d carry : Digit) : List Digit :=
  if _h : lhs = [] ∧ acc = [] ∧ carry.val = 0 then []
  else
    lhs.headD 0 ::
      mulAddTraceA lhs.tail acc.tail d (mulAddDigit (lhs.headD 0) d (acc.headD 0) carry).2
termination_by mulAddMeasure lhs acc carry
decreasing_by
  have := mulAddMeasure_decreases lhs acc d carry _h
  omega

/-- `mulAddTraceA` and `mulAddRaw` share the same recursion/termination, hence the same
    length. -/
lemma mulAddTraceA_length (lhs acc : List Digit) (d carry : Digit) :
    (mulAddTraceA lhs acc d carry).length = (mulAddRaw lhs acc d carry).length := by
  induction lhs, acc, carry using mulAddRaw.induct (d := d) with
  | case1 lhs acc carry hbase =>
      obtain ⟨hL, hA, hc⟩ := hbase
      subst hL; subst hA
      have hc0 : carry.val = 0 := hc
      rw [show mulAddRaw ([] : List Digit) [] d carry = [] by rw [mulAddRaw]; simp [hc0],
        show mulAddTraceA ([] : List Digit) [] d carry = [] by rw [mulAddTraceA]; simp [hc0]]
  | case2 lhs acc carry hbase dc ih =>
      have hunfoldR : mulAddRaw lhs acc d carry = dc.1 :: mulAddRaw lhs.tail acc.tail d dc.2 := by
        rw [mulAddRaw, dite_eq_right hbase]
      have hunfoldT : mulAddTraceA lhs acc d carry
          = lhs.headD 0 :: mulAddTraceA lhs.tail acc.tail d dc.2 := by
        rw [mulAddTraceA, dite_eq_right hbase]
      rw [hunfoldR, hunfoldT, List.length_cons, List.length_cons, ih]

/-- `mulAddTraceA`'s numeric value is exactly `lhs`'s: every "phantom" digit it records beyond
    `lhs`'s own length is `0` (`mulAddTraceA`'s docstring), which contributes nothing to
    `digitsToNat` — no case split on whether `lhs` is exhausted is needed, the same "harmless
    default" argument `digitsToNat_mulAddRaw` itself uses. -/
lemma digitsToNat_mulAddTraceA (lhs acc : List Digit) (d carry : Digit) :
    digitsToNat (mulAddTraceA lhs acc d carry) = digitsToNat lhs := by
  induction lhs, acc, carry using mulAddRaw.induct (d := d) with
  | case1 lhs acc carry hbase =>
      obtain ⟨hL, hA, hc⟩ := hbase
      subst hL; subst hA
      have hc0 : carry.val = 0 := hc
      rw [show mulAddTraceA ([] : List Digit) [] d carry = [] by rw [mulAddTraceA]; simp [hc0]]
  | case2 lhs acc carry hbase dc ih =>
      have hunfoldT : mulAddTraceA lhs acc d carry
          = lhs.headD 0 :: mulAddTraceA lhs.tail acc.tail d dc.2 := by
        rw [mulAddTraceA, dite_eq_right hbase]
      rw [hunfoldT]
      have hcons : digitsToNat (lhs.headD 0 :: mulAddTraceA lhs.tail acc.tail d dc.2)
          = (lhs.headD 0).val + 16 * digitsToNat (mulAddTraceA lhs.tail acc.tail d dc.2) := by
        simp [digitsToNat, Nat.ofDigits_cons]
      rw [hcons, ih, ← digitsToNat_headD_tail]

/-! ## The outer Horner loop: one full multiplier digit per step

`mulAddRaw`'s inner ripple is the *whole* per-digit work for one multiplier digit `d`, run
against the accumulator shifted left by one position (`default :: acc`, a single leading zero at
the LSB end — matching `mulAddRaw`'s own LSB-first convention). `mulOuterStep` trims the raw
result to canonical (`natToDigits`) form immediately (reusing
`DigitSub.dropWhile_zero_reverse_eq_natToDigits`, generic over any digit list) rather than only
at the very end: this is free (trimming never changes the represented value) and keeps every
intermediate accumulator `natToDigits`-shaped, which is what lets `mulRawAux_natToDigits` below
conclude an *exact* list equality by induction, not just a `digitsToNat` value fact. -/

/-- One Horner step: `acc ↦ acc*16 + lhs*d`, trimmed to canonical form. -/
def mulOuterStep (lhs : List Digit) (d : Digit) (acc : List Digit) : List Digit :=
  ((mulAddRaw lhs (default :: acc) d default).reverse.dropWhile
    (fun x => decide (x.val = 0))).reverse

/-- `mulOuterStep`'s output is *always* exactly `natToDigits` of its represented value,
    regardless of whether the input `acc` was itself canonical — the key fact letting
    `mulRawAux_natToDigits` re-canonicalize at every step without a separate induction. -/
lemma mulOuterStep_eq_natToDigits (lhs : List Digit) (d : Digit) (acc : List Digit) :
    mulOuterStep lhs d acc = natToDigits (digitsToNat lhs * d.val + 16 * digitsToNat acc) := by
  rw [mulOuterStep, dropWhile_zero_reverse_eq_natToDigits]
  congr 1
  rw [digitsToNat_mulAddRaw]
  simp [digitsToNat, Nat.ofDigits_cons]

/-- Process the multiplier's digits `srcBmsb` (MSB-first — the physical order `GenericMul.lean`'s
    `rhsOperand` scratch holds them in, built via a single copy-reversal of the register's own
    LSB-first content) one at a time via `mulOuterStep`, starting from accumulator `acc`. -/
def mulRawAux (lhs : List Digit) (acc : List Digit) : List Digit → List Digit
  | [] => acc
  | d :: rest => mulRawAux lhs (mulOuterStep lhs d acc) rest

/-- Appending a single digit `x` at an LSB-first list's end contributes `x.val * 16^l.length` —
    the "most-significant new digit" fact `DigitSub.dropWhile_zero_reverse_eq_natToDigits`'s own
    proof establishes inline; extracted here for reuse. -/
lemma digitsToNat_append_singleton (l : List Digit) (x : Digit) :
    digitsToNat (l ++ [x]) = digitsToNat l + x.val * 16 ^ l.length := by
  simp [digitsToNat, Nat.ofDigits_append, Nat.ofDigits_singleton, mul_comm]

/-- `mulRawAux` started from an already-canonical accumulator (`natToDigits X`) stays canonical
    at every step (module docstring), spelled out as an exact list equality rather than just a
    `digitsToNat` value fact. -/
lemma mulRawAux_natToDigits (lhs : List Digit) (X : ℕ) (srcBmsb : List Digit) :
    mulRawAux lhs (natToDigits X) srcBmsb
      = natToDigits (digitsToNat lhs * digitsToNat srcBmsb.reverse + X * 16 ^ srcBmsb.length) := by
  induction srcBmsb generalizing X with
  | nil => simp [mulRawAux, digitsToNat]
  | cons d rest ih =>
      rw [mulRawAux, mulOuterStep_eq_natToDigits, digitsToNat_natToDigits,
        ih (digitsToNat lhs * d.val + 16 * X)]
      congr 1
      have hrev : digitsToNat (d :: rest).reverse
          = digitsToNat rest.reverse + d.val * 16 ^ rest.length := by
        rw [List.reverse_cons, digitsToNat_append_singleton, List.length_reverse]
      rw [List.length_cons]
      have hpow : (16:ℕ) ^ (rest.length + 1) = 16 ^ rest.length * 16 := by ring
      nlinarith [hrev, hpow]

/-- Long multiplication (Horner scheme): process the multiplier `srcB`'s digits MSB-first
    (`.reverse`, since `srcB` itself is LSB-first) via `mulRawAux`, starting from `0`. -/
def mulRaw (srcA srcB : List Digit) : List Digit := mulRawAux srcA [] srcB.reverse

/-- `mulRaw` on two `natToDigits`-shaped operands is itself `natToDigits`-shaped: the canonical
    digit encoding of their product, not just numerically equal to it. Mirrors
    `DigitAdd.addRaw_natToDigits`. -/
lemma mulRaw_natToDigits (a b : ℕ) :
    mulRaw (natToDigits a) (natToDigits b) = natToDigits (a * b) := by
  have hnil0 : ([] : List Digit) = natToDigits 0 := by
    symm; simpa using (natToDigits_ne_nil_iff 0)
  rw [mulRaw, hnil0, mulRawAux_natToDigits, List.reverse_reverse]
  simp only [digitsToNat_natToDigits]
  simp

end NPComplete.RAMToTM

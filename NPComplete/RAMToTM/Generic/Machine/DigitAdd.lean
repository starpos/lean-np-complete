module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import NPComplete.RAMToTM.Generic.Machine.Binary

/-!
# Digit-serial ripple-carry addition: the pure reference model

`addRaw` specifies addition on LSB-first base-16 digit lists by consuming one pair of digits at a
time and threading a carry. Its output is also LSB-first. A stack implementation that pushes each
result digit therefore needs a reversal before the result can be reused as an operand.

The base case is checked before consuming a digit pair, so exhausted operands with no carry produce
`[]` rather than an extra zero digit. `addMeasure` supports well-founded recursion, but it can drop
by more than one per iteration and therefore bounds termination without giving the exact step count.
The exact loop count is `addRaw srcA srcB carry |>.length + 1`: one step per result digit and one
final empty/no-carry check. -/

@[expose] public section

namespace NPComplete.RAMToTM

/-- Add two hex digits and an incoming carry bit, returning the sum digit and outgoing carry. -/
def addDigits (a b : Digit) (carryIn : Bool) : Digit × Bool :=
  let sum := a.val + b.val + (if carryIn then 1 else 0)
  (⟨sum % 16, by omega⟩, decide (16 ≤ sum))

/-- `addDigits` is a faithful base-16 full adder: `sum digit + 16 * carry-out = a + b + carry-in`. -/
lemma addDigits_correct (a b : Digit) (c : Bool) :
    (addDigits a b c).1.val + 16 * (if (addDigits a b c).2 then 1 else 0)
      = a.val + b.val + (if c then 1 else 0) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [addDigits, decide_eq_true_eq]
  split_ifs <;> omega

/-- A termination measure for the digit-add loop: strictly decreases each iteration
    (`addMeasure_decreases`), but by 1, 2, or 3 depending on the case — *not* the exact
    remaining step count (see the module docstring). Used only to justify `addRaw`'s
    well-founded recursion. -/
def addMeasure (srcA srcB : List Digit) (carry : Bool) : ℕ :=
  srcA.length + srcB.length + (if carry then 1 else 0)

/-- One digit-add iteration (consume the head of each operand if present, defaulting to `0`
    for an exhausted operand, add with the carry) strictly decreases `addMeasure`, in every
    case except the excluded base case (both operands empty, no carry). -/
lemma addMeasure_decreases (srcA srcB : List Digit) (carry : Bool)
    (hbase : ¬ (srcA = [] ∧ srcB = [] ∧ carry = false)) :
    addMeasure srcA.tail srcB.tail
        (addDigits (srcA.headD 0) (srcB.headD 0) carry).2 + 1
      ≤ addMeasure srcA srcB carry := by
  rcases srcA with _ | ⟨da, ta⟩
  · rcases srcB with _ | ⟨db, tb⟩
    · rcases carry with _ | _
      · exact absurd ⟨rfl, rfl, rfl⟩ hbase
      · simp only [addMeasure, List.tail_nil, List.length_nil, List.headD_nil, addDigits,
          decide_eq_true_eq]
        decide
    · simp only [addMeasure, List.tail_nil, List.tail_cons, List.length_nil, List.length_cons,
        List.headD_nil, List.headD_cons]
      have hd := db.isLt
      simp only [addDigits, decide_eq_true_eq, Fin.val_zero]
      split_ifs <;> omega
  · rcases srcB with _ | ⟨db, tb⟩
    · simp only [addMeasure, List.tail_nil, List.tail_cons, List.length_nil, List.length_cons,
        List.headD_nil, List.headD_cons]
      have hd := da.isLt
      simp only [addDigits, decide_eq_true_eq, Fin.val_zero]
      split_ifs <;> omega
    · simp only [addMeasure, List.tail_cons, List.length_cons, List.headD_cons]
      have hda := da.isLt
      have hdb := db.isLt
      simp only [addDigits, decide_eq_true_eq]
      split_ifs <;> omega

/-- Pure reference model for the raw LSB-first digit-add output: the digits computed by `addLoop`
    in low-to-high order. The destination stack prepends them, so its final order is reversed. -/
-- The termination proof passes `_h`, the stopping condition, to `addMeasure_decreases`.  It is
-- underscored because the unused-variable linter does not look inside termination proofs.
def addRaw (srcA srcB : List Digit) (carry : Bool) : List Digit :=
  if _h : srcA = [] ∧ srcB = [] ∧ carry = false then []
  else
    let dc := addDigits (srcA.headD 0) (srcB.headD 0) carry
    dc.1 :: addRaw srcA.tail srcB.tail dc.2
termination_by addMeasure srcA srcB carry
decreasing_by
  have := addMeasure_decreases srcA srcB carry _h
  omega

/-- The three stacks of the addition machine: the two operands and the destination. -/
inductive AddStack | a | b | dst
  deriving DecidableEq

/-- Transient scratch (`a`, `b`: the digit just peeked/popped from each operand, `Option`
    because an exhausted operand contributes no digit) plus the persistent carry. -/
structure AddState where
  a : Option Digit
  b : Option Digit
  carry : Bool
  deriving DecidableEq, Fintype

/-- `loop` processes one more digit pair if either operand still has one, or the carry is
    still live; `done` is the exit label. -/
inductive AddLbl | loop | done
  deriving DecidableEq

instance : Fintype AddLbl :=
  Fintype.ofList [AddLbl.loop, AddLbl.done] (by
    intro x
    cases x <;> simp)

open Turing Turing.TM2.Stmt

/-- Unfolding `digitsToNat` one digit at a time, matching `List.headD`/`List.tail`'s own
    handling of the empty case (both sides are `0` when `l = []`) — the form `addRaw`'s
    recursion needs, since it recurses on `.headD 0`/`.tail` rather than pattern-matching. -/
lemma digitsToNat_headD_tail (l : List Digit) :
    digitsToNat l = (l.headD 0).val + 16 * digitsToNat l.tail := by
  cases l with
  | nil => simp [digitsToNat]
  | cons d l' => simp [digitsToNat, Nat.ofDigits_cons]

/-- `addRaw`'s LSB-first digit value is the numeric sum. This semantic fact complements the
    loop's transition-count and output-shape properties. -/
lemma digitsToNat_addRaw (srcA srcB : List Digit) (carry : Bool) :
    digitsToNat (addRaw srcA srcB carry)
      = digitsToNat srcA + digitsToNat srcB + (if carry then 1 else 0) := by
  induction srcA, srcB, carry using addRaw.induct with
  | case1 srcA srcB carry hbase =>
      obtain ⟨hA, hB, hc⟩ := hbase
      subst hA; subst hB; subst hc
      simp [addRaw, digitsToNat]
  | case2 srcA srcB carry hbase dc ih =>
      have hunfold : addRaw srcA srcB carry = dc.1 :: addRaw srcA.tail srcB.tail dc.2 := by
        rw [addRaw]; simp [hbase, dc]
      rw [hunfold]
      have hcons : digitsToNat (dc.1 :: addRaw srcA.tail srcB.tail dc.2)
          = dc.1.val + 16 * digitsToNat (addRaw srcA.tail srcB.tail dc.2) := by
        simp [digitsToNat, Nat.ofDigits_cons]
      rw [hcons, ih]
      have hcorrect := addDigits_correct (srcA.headD 0) (srcB.headD 0) carry
      have hA := digitsToNat_headD_tail srcA
      have hB := digitsToNat_headD_tail srcB
      simp only [dc]
      omega

/-- Dropping the head of a nonempty-tailed list doesn't change its last element: `getLast?`
    only ever depends on the *last* cons cell, never the first. Lets a canonicality hypothesis
    on `srcA`/`srcB` (last digit nonzero) transport unchanged onto `srcA.tail`/`srcB.tail` when
    chasing `addRaw`'s own recursion, without needing the tails to independently be
    `natToDigits`-shaped. -/
lemma getLast?_tail_some {α} (l : List α) (d : α) (h : l.tail.getLast? = some d) :
    l.getLast? = some d := by
  cases l with
  | nil => simp at h
  | cons a l' => rw [List.tail_cons] at h; rw [List.getLast?_cons, h]; rfl

lemma addRaw_eq_nil_iff (x y : List Digit) (c : Bool) :
    addRaw x y c = [] ↔ x = [] ∧ y = [] ∧ c = false := by
  constructor
  · intro h
    by_contra hc
    rw [addRaw] at h
    simp [hc] at h
  · rintro ⟨hx, hy, hc⟩
    subst hx; subst hy; subst hc
    rw [addRaw]; simp

/-- `addRaw` preserves canonicality: given two canonical operands (no zero digit at the MSB
    end, e.g. `natToDigits`'s own shape), its output is canonical too. `addRaw.induct`'s
    recursive case splits on whether the recursive tail (`rest`) is empty: if not, `rest`'s own
    (inductively canonical) last digit is unchanged by prepending the newly produced digit; if
    so, the newly produced digit *is* the terminal one, and `addRaw_eq_nil_iff` pins down that
    both operand tails are exhausted with no carry, so `addDigits_correct` reduces the claim to
    "the input digits actually being summed (from canonical, hence nonzero-or-absent operands)
    plus carry is positive" — automatically ruling out the base case via `hbase`. -/
lemma addRaw_getLast_ne_zero (srcA srcB : List Digit) (carry : Bool)
    (hA : ∀ d, srcA.getLast? = some d → d.val ≠ 0)
    (hB : ∀ d, srcB.getLast? = some d → d.val ≠ 0) :
    ∀ d, (addRaw srcA srcB carry).getLast? = some d → d.val ≠ 0 := by
  induction srcA, srcB, carry using addRaw.induct with
  | case1 srcA srcB carry hbase =>
      obtain ⟨hA', hB', hc'⟩ := hbase
      subst hA'; subst hB'; subst hc'
      rw [show addRaw ([] : List Digit) [] false = [] by rw [addRaw]; simp]
      intro d hd; simp at hd
  | case2 srcA srcB carry hbase dc ih =>
      have hdc : dc = addDigits (srcA.headD 0) (srcB.headD 0) carry := rfl
      have hunfold : addRaw srcA srcB carry = dc.1 :: addRaw srcA.tail srcB.tail dc.2 := by
        rw [addRaw]; simp [hbase, dc]
      have hAtail : ∀ d, srcA.tail.getLast? = some d → d.val ≠ 0 :=
        fun d h => hA d (getLast?_tail_some srcA d h)
      have hBtail : ∀ d, srcB.tail.getLast? = some d → d.val ≠ 0 :=
        fun d h => hB d (getLast?_tail_some srcB d h)
      rw [hunfold, List.getLast?_cons]
      rcases hrest : (addRaw srcA.tail srcB.tail dc.2).getLast? with _ | rd
      · simp only [Option.getD_none]
        intro d hd
        have hd' : dc.1 = d := (Option.some.injEq _ _).mp hd
        rw [hdc] at hd'
        subst hd'
        obtain ⟨htA, htB, htc⟩ := (addRaw_eq_nil_iff _ _ _).mp (List.getLast?_eq_none_iff.mp hrest)
        rw [hdc] at htc
        have hcorrect := addDigits_correct (srcA.headD 0) (srcB.headD 0) carry
        rw [htc] at hcorrect
        simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero] at hcorrect
        rcases srcA with _ | ⟨a, as⟩
        · rcases srcB with _ | ⟨b, bs⟩
          · simp only [List.headD_nil, Fin.val_zero] at hcorrect ⊢
            have hcarry : carry = true := by
              rcases carry with _ | _
              · exact absurd ⟨rfl, rfl, rfl⟩ hbase
              · rfl
            simp [hcarry] at hcorrect ⊢
            omega
          · simp only [List.tail_cons] at htB
            subst htB
            have hbval := hB b (by simp)
            simp only [List.headD_nil, Fin.val_zero, List.headD_cons] at hcorrect ⊢
            omega
        · simp only [List.tail_cons] at htA
          subst htA
          have haval := hA a (by simp)
          simp only [List.headD_cons] at hcorrect ⊢
          omega
      · simp only [Option.getD_some]
        intro d hd
        have hd' : rd = d := (Option.some.injEq _ _).mp hd
        subst hd'
        exact ih hAtail hBtail rd hrest

/-- `addRaw` on two `natToDigits`-shaped operands is *itself* `natToDigits`-shaped: not just
    numerically the right sum (`digitsToNat_addRaw` + `digitsToNat_natToDigits`), but literally
    the canonical digit encoding of it, via `Binary.natToDigits_digitsToNat_of_canonical` plus
    `addRaw_getLast_ne_zero`'s canonicality. Needed to feed `add`'s destination register
    directly into `store3`'s `natToDigits val`-shaped start condition. -/
lemma addRaw_natToDigits (t y : ℕ) :
    addRaw (natToDigits t) (natToDigits y) false = natToDigits (t + y) := by
  have hcanon := addRaw_getLast_ne_zero (natToDigits t) (natToDigits y) false
    (natToDigits_canonical t) (natToDigits_canonical y)
  have hval : digitsToNat (addRaw (natToDigits t) (natToDigits y) false) = t + y := by
    rw [digitsToNat_addRaw, digitsToNat_natToDigits, digitsToNat_natToDigits]
    simp
  rw [← hval]
  exact (natToDigits_digitsToNat_of_canonical _ hcanon).symm

/-- `addRaw`'s "add one with carry" against a `natToDigits`-shaped operand is itself
    `natToDigits`-shaped: the increment counterpart of `addRaw_natToDigits`, needed to identify
    a prologue's running address counter (built by repeated `addRaw _ [] true` increments,
    `GenericPrologue.lean`) with `natToDigits` of the bit count scanned so far. -/
lemma addRaw_natToDigits_succ (t : ℕ) :
    addRaw (natToDigits t) [] true = natToDigits (t + 1) := by
  have hcanon := addRaw_getLast_ne_zero (natToDigits t) [] true
    (natToDigits_canonical t) (fun d hd => by simp at hd)
  have hval : digitsToNat (addRaw (natToDigits t) [] true) = t + 1 := by
    rw [digitsToNat_addRaw, digitsToNat_natToDigits]
    simp [digitsToNat]
  rw [← hval]
  exact (natToDigits_digitsToNat_of_canonical _ hcanon).symm

end NPComplete.RAMToTM

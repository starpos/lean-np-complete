module

public import NPComplete.RAMToTM.Generic.Machine.Binary
public import NPComplete.RAMToTM.Generic.Machine.DigitAdd
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Digit-serial ripple-borrow subtraction on `FinTM2` stacks

`sub rd rs rt`'s RAM semantics is *natural* subtraction (`regs rd ← regs rs - regs rt`, truncated
to `0` when `regs rs < regs rt`), unlike `add`'s unconditional wraparound-free sum. This forces a
different termination discipline for the digit-serial loop than `DigitAdd.addRaw`'s: `addRaw` keeps
consuming digits *while the carry is still live*, which is correct for addition (a live carry past
both operands' length always terminates in at most one more digit) but would loop forever here — a
`borrow` that survives past both operands being exhausted (e.g. subtracting a larger number from a
smaller one) never clears on its own, since `0 - 0 - 1` always re-borrows.

`subRawFull` instead stops as soon as *both* operands are exhausted, regardless of the pending
borrow, and returns that final borrow bit alongside the (possibly non-canonical) digit list. The
two facts a caller needs are then proved separately rather than as one wraparound-aware identity
(`subRawFull_borrow_iff` decides the boolean; `digitsToNat_subRawFull` gives the digit list's value,
but only conditionally on the borrow being `false` — the `true` case never needs a digit-accurate
result, since the RAM truncates to `0` there and the realized instruction discards the raw digits
outright).

**Non-canonicality, unlike `addRaw`**: even when the subtraction doesn't underflow, the raw digit
list can develop a *new* zero at the most-significant end that neither operand had (`100 - 99 = 1`
in decimal terms: three-and-two-digit operands collapse to a one-digit result). `addRaw` has no
analogous problem (`DigitAdd.addRaw_getLast_ne_zero`), so the realized instruction (`GenericSub.lean`)
needs an explicit trim pass; `dropWhile_zero_reverse_eq_natToDigits` is the pure-math fact backing
it — dropping leading (most-significant-first) zero digits and reversing back to the LSB-first
convention is exactly `natToDigits ∘ digitsToNat`, regardless of how many zero digits accumulated.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- Transient scratch (`a`, `b`: the digit just popped from each operand, `Option` because an
    exhausted operand contributes no digit) plus the persistent borrow bit — same shape as
    `DigitAdd.AddState`, kept as its own type per `GenericProgramMachine.lean`'s "one field per
    realized instruction" convention (`sub` needs its own `AllInstrState` field, distinct from
    `add`'s, even though the two structures coincide). -/
structure SubState where
  a : Option Digit
  b : Option Digit
  borrow : Bool
  deriving DecidableEq, Fintype

/-- Subtract hex digit `b` (plus an incoming borrow bit) from `a`, returning the difference digit
    and the outgoing borrow. Mirrors `DigitAdd.addDigits`'s shape. -/
def subDigits (a b : Digit) (borrowIn : Bool) : Digit × Bool :=
  let bi := b.val + (if borrowIn then 1 else 0)
  if h : a.val < bi then (⟨a.val + 16 - bi, by omega⟩, true)
  else (⟨a.val - bi, by have := b.isLt; omega⟩, false)

/-- `subDigits` is a faithful base-16 full subtractor: the digit plus what was subtracted equals
    the minuend, with the borrow-out accounting for any wraparound — the additive form (no `ℕ`
    truncation in the statement itself) mirrors `DigitAdd.addDigits_correct`. -/
lemma subDigits_correct (a b : Digit) (c : Bool) :
    (subDigits a b c).1.val + (b.val + (if c then 1 else 0))
      = a.val + 16 * (if (subDigits a b c).2 then 1 else 0) := by
  have ha : a.val < 16 := a.isLt
  have hb : b.val < 16 := b.isLt
  have hcf : (if c then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
  rcases Nat.lt_or_ge a.val (b.val + (if c then 1 else 0)) with hlt | hge
  · rw [subDigits, dite_eq_left hlt]; dsimp only; simp only [ite_true]; omega
  · rw [subDigits, dite_eq_right (not_lt.mpr hge)]; dsimp only; simp; omega

/-- Termination measure for `subRawFull`'s loop: unlike `DigitAdd.addMeasure`, this never needs to
    inspect the borrow bit — the loop always stops once both operands are exhausted (module
    docstring), so plain combined length strictly decreases every non-base iteration. -/
def subMeasure (srcA srcB : List Digit) : ℕ := srcA.length + srcB.length

/-- Pure reference model for ripple-borrow subtraction: consumes `srcA`/`srcB` LSB-first (an
    exhausted operand contributes `0` via `headD`, exactly as `DigitAdd.addRaw` does), stopping
    once *both* are empty regardless of the pending borrow (module docstring) — the returned
    `Bool` is that final borrow. The digit list itself is LSB-first, like `addRaw`'s own list (the
    `DigitAdd.lean` docstring's "raw / push order" description is about the `FinTM2` stack's
    physical layout after push-based construction, not this pure function's own indexing). -/
-- `simp_all` uses the stopping condition `_h` to close the measure goal.  It is underscored
-- because the unused-variable linter does not look inside termination proofs.
def subRawFull (srcA srcB : List Digit) (borrow : Bool) : List Digit × Bool :=
  if _h : srcA = [] ∧ srcB = [] then ([], borrow)
  else
    let dc := subDigits (srcA.headD 0) (srcB.headD 0) borrow
    let rest := subRawFull srcA.tail srcB.tail dc.2
    (dc.1 :: rest.1, rest.2)
termination_by subMeasure srcA srcB
decreasing_by
  rcases srcA with _ | ⟨da, ta⟩ <;> rcases srcB with _ | ⟨db, tb⟩ <;>
    simp_all [subMeasure]; omega

/-- `subRawFull` produces one digit per iteration and stops once both operands are exhausted, so
    its output is never longer than the larger operand (needed by the quantitative bound: `subRawFull`'s digit list
    length is the `sub` realization's own step count, and `sub`'s `instructionCost` only charges
    for `bitLen`, not this digit count directly). -/
lemma subRawFull_length_le (srcA srcB : List Digit) (borrow : Bool) :
    (subRawFull srcA srcB borrow).1.length ≤ max srcA.length srcB.length := by
  have key : ∀ n (srcA srcB : List Digit) (borrow : Bool), srcA.length + srcB.length ≤ n →
      (subRawFull srcA srcB borrow).1.length ≤ max srcA.length srcB.length := by
    intro n
    induction n with
    | zero =>
        intro srcA srcB borrow hle
        have hA : srcA = [] := by rw [← List.length_eq_zero_iff]; omega
        have hB : srcB = [] := by rw [← List.length_eq_zero_iff]; omega
        simp [subRawFull, hA, hB]
    | succ n ih =>
        intro srcA srcB borrow hle
        by_cases hbase : srcA = [] ∧ srcB = []
        · simp [subRawFull, hbase]
        · rw [subRawFull, dite_eq_right hbase]
          simp only [List.length_cons]
          have hIH := ih srcA.tail srcB.tail (subDigits (srcA.headD 0) (srcB.headD 0) borrow).2
            (by rw [List.length_tail, List.length_tail]; omega)
          rw [List.length_tail, List.length_tail] at hIH
          have hbase' : ¬ (srcA.length = 0 ∧ srcB.length = 0) := by
            simpa [List.length_eq_zero_iff] using hbase
          omega
  exact key (srcA.length + srcB.length) srcA srcB borrow le_rfl

/-- The final borrow bit exactly decides underflow: `subRawFull` borrows out iff the minuend
    (plus incoming borrow) is numerically smaller than the subtrahend. Proved by induction
    mirroring `subRawFull`'s own recursion; each step only needs `subDigits_correct` plus the
    per-digit bound (`Digit.isLt`) for `omega` to relate the whole-number comparison to the
    digit-level one — no wraparound bookkeeping (e.g. an explicit `16 ^ n` term) is needed since
    this is a purely boolean claim (contrast `digitsToNat_subRawFull` below, which does need the
    hypothesis to avoid `ℕ` truncation on the value side). -/
lemma subRawFull_borrow_iff (srcA srcB : List Digit) (borrowIn : Bool) :
    (subRawFull srcA srcB borrowIn).2 = true
      ↔ digitsToNat srcA < digitsToNat srcB + (if borrowIn then 1 else 0) := by
  induction srcA, srcB, borrowIn using subRawFull.induct with
  | case1 srcA srcB borrowIn hbase =>
      obtain ⟨hA, hB⟩ := hbase
      subst hA; subst hB
      rw [show subRawFull ([] : List Digit) [] borrowIn = ([], borrowIn) by rw [subRawFull]; simp]
      cases borrowIn <;> simp [digitsToNat]
  | case2 srcA srcB borrowIn hbase dc ih =>
      have hunfold : subRawFull srcA srcB borrowIn
          = (dc.1 :: (subRawFull srcA.tail srcB.tail dc.2).1,
              (subRawFull srcA.tail srcB.tail dc.2).2) := by
        rw [subRawFull]; simp [hbase, dc]
      rw [hunfold]; dsimp only; rw [ih]
      have hdc : dc = subDigits (srcA.headD 0) (srcB.headD 0) borrowIn := rfl
      have hcorrect := subDigits_correct (srcA.headD 0) (srcB.headD 0) borrowIn
      rw [← hdc] at hcorrect
      have hda := (srcA.headD 0).isLt
      have hdb := (srcB.headD 0).isLt
      have hcf : (if borrowIn then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
      have hcf2 : (if dc.2 then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
      have hA := digitsToNat_headD_tail srcA
      have hB := digitsToNat_headD_tail srcB
      omega

/-- When the subtraction does not underflow (the hypothesis, needed to avoid `ℕ` truncation in the
    statement itself), the digit list `subRawFull` produces denotes exactly the true difference.
    Uses `subRawFull_borrow_iff` at each recursive step (via `by_contra`) to know the *tail*
    computation also stays underflow-free, which is what lets `ih` apply. -/
lemma digitsToNat_subRawFull (srcA srcB : List Digit) (borrowIn : Bool)
    (hno : digitsToNat srcB + (if borrowIn then 1 else 0) ≤ digitsToNat srcA) :
    digitsToNat (subRawFull srcA srcB borrowIn).1
      = digitsToNat srcA - digitsToNat srcB - (if borrowIn then 1 else 0) := by
  induction srcA, srcB, borrowIn using subRawFull.induct with
  | case1 srcA srcB borrowIn hbase =>
      obtain ⟨hA, hB⟩ := hbase
      subst hA; subst hB
      rw [show subRawFull ([] : List Digit) [] borrowIn = ([], borrowIn) by rw [subRawFull]; simp]
      simp [digitsToNat] at hno ⊢
  | case2 srcA srcB borrowIn hbase dc ih =>
      have hunfold : subRawFull srcA srcB borrowIn
          = (dc.1 :: (subRawFull srcA.tail srcB.tail dc.2).1,
              (subRawFull srcA.tail srcB.tail dc.2).2) := by
        rw [subRawFull]; simp [hbase, dc]
      rw [hunfold]; dsimp only
      have hdc : dc = subDigits (srcA.headD 0) (srcB.headD 0) borrowIn := rfl
      have hcorrect := subDigits_correct (srcA.headD 0) (srcB.headD 0) borrowIn
      rw [← hdc] at hcorrect
      have hda := (srcA.headD 0).isLt
      have hdb := (srcB.headD 0).isLt
      have hcf : (if borrowIn then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
      have hcf2 : (if dc.2 then (1 : ℕ) else 0) ≤ 1 := by split_ifs <;> omega
      have hA := digitsToNat_headD_tail srcA
      have hB := digitsToNat_headD_tail srcB
      have hborrow := subRawFull_borrow_iff srcA.tail srcB.tail dc.2
      have hno2 : digitsToNat srcB.tail + (if dc.2 then 1 else 0) ≤ digitsToNat srcA.tail := by
        by_contra hcon
        push Not at hcon
        have := hborrow.mpr hcon
        omega
      rw [digitsToNat_cons, ih hno2]
      omega

/-- Dropping leading (most-significant-first) zero digits from `l`'s reverse and reversing back to
    the LSB-first convention is exactly `natToDigits (digitsToNat l)` — the trim `GenericSub.lean`'s
    `skipZeros` phase performs, physically popping from the top of a stack that holds `l.reverse`
    (module docstring). Proved by showing the LHS both denotes the same value as `l`
    (`List.reverseRecOn`, unfolding one most-significant digit at a time via `Nat.ofDigits_append`)
    and is itself canonical (`List.head?_dropWhile_not`: whatever remains after the drop, if
    anything, is nonzero by construction), then invoking uniqueness
    (`Binary.natToDigits_digitsToNat_of_canonical`). -/
lemma dropWhile_zero_reverse_eq_natToDigits (l : List Digit) :
    (l.reverse.dropWhile (fun d => decide (d.val = 0))).reverse = natToDigits (digitsToNat l) := by
  have hval : digitsToNat ((l.reverse.dropWhile (fun d => decide (d.val = 0))).reverse)
      = digitsToNat l := by
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton xs x ih =>
        rw [List.reverse_append]
        simp only [List.reverse_singleton, List.singleton_append]
        by_cases hx : x.val = 0
        · rw [List.dropWhile_cons]; simp only [hx, decide_true, ite_true]; rw [ih]
          simp [digitsToNat, List.map_append, Nat.ofDigits_append, hx]
        · rw [List.dropWhile_cons]; simp [hx]
  have hcan : ∀ d, ((l.reverse.dropWhile (fun d => decide (d.val = 0))).reverse).getLast? = some d
      → d.val ≠ 0 := by
    intro d hd
    rw [List.getLast?_reverse] at hd
    have hhead := List.head?_dropWhile_not (fun d : Digit => decide (d.val = 0)) l.reverse
    rw [hd] at hhead
    simpa using hhead
  rw [← hval]
  exact (natToDigits_digitsToNat_of_canonical _ hcan).symm

/-- Underflow, in `natToDigits`-shaped terms: the form `GenericSub.lean`'s realization proof
    consumes directly. -/
lemma sub_result_underflow (rsVal rtVal : ℕ) (h : rsVal < rtVal) :
    (subRawFull (natToDigits rsVal) (natToDigits rtVal) false).2 = true :=
  (subRawFull_borrow_iff _ _ _).mpr (by simp [digitsToNat_natToDigits]; omega)

/-- No underflow, in `natToDigits`-shaped terms: the raw computation doesn't borrow out, and
    trimming its leading zeros (module docstring) yields exactly the canonical encoding of the
    true difference — the form `GenericSub.lean`'s realization proof consumes directly. -/
lemma sub_result_ge (rsVal rtVal : ℕ) (h : rtVal ≤ rsVal) :
    (subRawFull (natToDigits rsVal) (natToDigits rtVal) false).2 = false ∧
    ((subRawFull (natToDigits rsVal) (natToDigits rtVal) false).1.reverse.dropWhile
        (fun d => decide (d.val = 0))).reverse = natToDigits (rsVal - rtVal) := by
  have hno : digitsToNat (natToDigits rtVal) + (if (false : Bool) then 1 else 0)
      ≤ digitsToNat (natToDigits rsVal) := by simp [digitsToNat_natToDigits]; omega
  have hval := digitsToNat_subRawFull (natToDigits rsVal) (natToDigits rtVal) false hno
  simp only [digitsToNat_natToDigits, Bool.false_eq_true, ite_false, Nat.sub_zero] at hval
  refine ⟨?_, by rw [dropWhile_zero_reverse_eq_natToDigits, hval]⟩
  by_contra hc
  have := (subRawFull_borrow_iff (natToDigits rsVal) (natToDigits rtVal) false).mp (by simpa using hc)
  simp [digitsToNat_natToDigits] at this
  omega

end NPComplete.RAMToTM

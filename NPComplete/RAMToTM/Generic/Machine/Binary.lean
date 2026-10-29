module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas
public import NPComplete.BitCostRAM

/-!
# Fixed-base digit alphabet for `FinTM2` number representation

`BitCostRAM.Bank` cells hold arbitrary-magnitude `ℕ` values, but a `Turing.FinTM2` stack
alphabet used as the input stack must be a `Fintype`, and the machine built here keeps
*every* stack alphabet finite, so a fixed machine
can still process unboundedly large register/memory values by spreading them one digit at a
time across finitely many stack cells. `BitEncoding.encodeNat` uses one bit per unit of magnitude,
so its representation grows with the value; base-16 digits keep arithmetic values compact while
still allowing digit-by-digit processing.

Rather than hand-roll a binary encoder, this reuses Mathlib's `Nat.digits`/`Nat.ofDigits`
(base 16, LSB-first) and only narrows the codomain to the finite `Digit` type at the
FinTM2-facing boundary.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- A single hex digit: the `FinTM2` stack alphabet element for number representation. -/
abbrev Digit : Type := Fin 16

/-- `n`'s LSB-first digit list in base 16. -/
def natToDigits (n : ℕ) : List Digit :=
  (Nat.digits 16 n).pmap (fun d h => (⟨d, h⟩ : Digit))
    (fun _ hd => Nat.digits_lt_base (by norm_num) hd)

/-- Reconstruct the `ℕ` a digit list denotes (LSB-first, base 16). -/
def digitsToNat (l : List Digit) : ℕ := Nat.ofDigits 16 (l.map Fin.val)

lemma digitsToNat_natToDigits (n : ℕ) : digitsToNat (natToDigits n) = n := by
  unfold digitsToNat natToDigits
  rw [List.map_pmap]
  simp only [List.pmap_eq_map]
  rw [List.map_id']
  exact Nat.ofDigits_digits 16 n

lemma natToDigits_length (n : ℕ) : (natToDigits n).length = (Nat.digits 16 n).length := by
  unfold natToDigits
  rw [List.length_pmap]

/-- The digit-list length is monotone in the encoded value: a loop that only ever holds values
    `≤ n` (e.g. a countdown register) never needs more digits than `n` itself does. -/
lemma natToDigits_length_mono {m n : ℕ} (h : m ≤ n) :
    (natToDigits m).length ≤ (natToDigits n).length := by
  rw [natToDigits_length, natToDigits_length]
  exact Nat.le_length_digits_le 16 m n h

/-- A hex digit list is never longer than the binary bit-length: base 16 packs at least as much
    per digit as base 2, so `Nat.log 16 n ≤ Nat.log 2 n` (`Nat.log_anti_left`). This is the bridge
    time-aggregation bounds use to restate a site's own (digit-length-phrased) TM step
    count against `BitCostRAM.instructionCost`'s `bitLen`-phrased charge. -/
lemma natToDigits_length_le_bitLen (n : ℕ) :
    (natToDigits n).length ≤ NPComplete.BitCostRAM.bitLen n := by
  rw [natToDigits_length]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [NPComplete.BitCostRAM.bitLen]
  · rw [Nat.length_digits 16 n (by norm_num) hn, NPComplete.BitCostRAM.bitLen,
      Nat.log2_eq_log_two]
    have := Nat.log_anti_left (b := 16) (c := 2) (n := n) (by norm_num) (by norm_num)
    omega

/-- The converse direction of `natToDigits_length_le_bitLen`: a hex digit list's length also
    bounds `bitLen` from above (each digit packs exactly 4 bits, base 16 = 2^4), needed to convert
    a `Represents`-log-length bound (digit-list units) back into a `bitLen`-phrased
    `instructionCost` charge. -/
lemma bitLen_le_of_natToDigits_length (n : ℕ) :
    NPComplete.BitCostRAM.bitLen n ≤ 4 * (natToDigits n).length + 1 := by
  rw [natToDigits_length]
  apply NPComplete.BitCostRAM.bitLen_le_of_lt_two_pow (by omega)
  have hlt : n < 16 ^ (Nat.digits 16 n).length :=
    (Nat.digits_length_le_iff (by norm_num) n).mp le_rfl
  calc n < 16 ^ (Nat.digits 16 n).length := hlt
    _ = 2 ^ (4 * (Nat.digits 16 n).length) := by
        rw [show (16:ℕ) = 2^4 from rfl, ← pow_mul]
    _ ≤ 2 ^ (4 * (Nat.digits 16 n).length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Equality on `List α` transports across a `pmap`, regardless of which (propositionally
    equal, hence defeq by proof irrelevance) side-condition proof each list carries — needed
    to reconnect `natToDigits`'s own `pmap` proof term with an externally-constructed one after
    rewriting the underlying `List ℕ` via `Nat.digits_ofDigits`. -/
lemma pmap_congr_of_eq {α β} {p : α → Prop} (l1 l2 : List α) (heq : l1 = l2)
    (f : ∀ a, p a → β) (h1 : ∀ a ∈ l1, p a) (h2 : ∀ a ∈ l2, p a) :
    l1.pmap f h1 = l2.pmap f h2 := by
  subst heq; rfl

lemma pmap_map_fin_val (l : List Digit) (proof : ∀ x ∈ l.map Fin.val, x < 16) :
    (l.map Fin.val).pmap (fun d h => (⟨d, h⟩ : Digit)) proof = l := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    simp only [List.map_cons, List.pmap_cons]
    congr 1
    apply ih

/-- The converse of `digitsToNat_natToDigits`: `natToDigits ∘ digitsToNat` is the identity
    exactly on *canonical* digit lists (no zero digit at the MSB end, matching `Nat.digits`'s
    own normal form). Needed to show `addRaw`'s output — proved canonical separately in
    `DigitAdd.lean` — already *is* the digit encoding of the sum it represents, not just some
    list that decodes to the right value. -/
lemma natToDigits_digitsToNat_of_canonical (l : List Digit)
    (hl : ∀ d, l.getLast? = some d → d.val ≠ 0) :
    natToDigits (digitsToNat l) = l := by
  have hw1 : ∀ x ∈ l.map Fin.val, x < 16 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, _, rfl⟩ := hx
    exact d.isLt
  have hw2 : ∀ h : l.map Fin.val ≠ [], (l.map Fin.val).getLast h ≠ 0 := by
    intro h
    have hne : l ≠ [] := fun heq => h (by rw [heq]; rfl)
    rw [List.getLast_map]
    intro hzero
    refine hl (l.getLast hne) ((List.getLast_eq_iff_getLast?_eq_some hne).mp rfl) ?_
    rw [← Fin.val_zero (n := 15)]; exact hzero
  have hdig := Nat.digits_ofDigits 16 (by norm_num) (l.map Fin.val) hw1 hw2
  show (Nat.digits 16 (Nat.ofDigits 16 (l.map Fin.val))).pmap (fun d h => (⟨d, h⟩ : Digit)) _ = l
  exact (pmap_congr_of_eq _ _ hdig _ _ hw1).trans (pmap_map_fin_val l hw1)

lemma natToDigits_ne_nil_iff (n : ℕ) : natToDigits n ≠ [] ↔ n ≠ 0 := by
  unfold natToDigits
  rw [ne_eq, List.pmap_eq_nil_iff, Nat.digits_eq_nil_iff_eq_zero]

/-- `0`'s digit list is empty — the "no digits at all" fact a length-entry's zero address field
    (`MemoryEncoding.lean`'s `encodeEntry 0 val`) relies on. -/
lemma natToDigits_zero : natToDigits 0 = [] := by
  unfold natToDigits
  simp

/-- `natToDigits` is itself canonical: no zero digit at the MSB end. Reused by every arithmetic
    result (`addRaw_natToDigits` etc.) that needs to show its *own* output is canonical, since
    those results always start from `natToDigits`-shaped operands. -/
lemma natToDigits_canonical (n : ℕ) : ∀ d, (natToDigits n).getLast? = some d → d.val ≠ 0 := by
  intro d hd
  rcases eq_or_ne n 0 with hn | hn
  · exfalso; subst hn; simp [natToDigits] at hd
  · have hne : natToDigits n ≠ [] := (natToDigits_ne_nil_iff n).mpr hn
    have heq : (natToDigits n).getLast hne = d := (List.getLast_eq_iff_getLast?_eq_some hne).mpr hd
    rw [← heq]
    unfold natToDigits at hne ⊢
    rw [List.getLast_pmap]
    exact Nat.getLast_digit_ne_zero 16 hn

/-! ## Comparing digit lists

`compareDigits` is the pure-math specification `setIfLt`/`setIfEq`/`branchIfLt`'s TM realization
must compute: given two LSB-first digit lists, decide the `Ordering` of the numbers they denote.
Recursing into the tails (the *more*-significant digits, since the input is LSB-first) before
ever consulting the current (least-significant-so-far) digit is what makes a length mismatch —
naturally encoded by the `[]`/`_ :: _` base cases — win unconditionally over any digit-level
difference already found in a shared low-order prefix, matching positional numeral semantics: a
canonical (no-leading-zero) list with strictly more digits always denotes a strictly larger
number, regardless of what any of its digits are. -/

/-- Compare two LSB-first digit lists as the numbers they denote (spec for `compareDigits`, see
    module docstring for why the recursion is tail-first). -/
def compareDigits : List Digit → List Digit → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compareDigits as bs with
      | .eq => compare a b
      | ord => ord

/-- Canonical: no zero digit at the (list-order) last position — matching `natToDigits`'s own
    normal form (`natToDigits_canonical`), stated generically since `compareDigits_correct` below
    is proved for arbitrary canonical lists, not just `natToDigits`-shaped ones. -/
def CanonicalDigits (l : List Digit) : Prop := ∀ d, l.getLast? = some d → d.val ≠ 0

lemma canonicalDigits_tail (a : Digit) (as : List Digit) (h : CanonicalDigits (a :: as)) :
    CanonicalDigits as := by
  intro d hd
  apply h
  rw [List.getLast?_cons, hd]
  simp

lemma digitsToNat_cons (a : Digit) (as : List Digit) :
    digitsToNat (a :: as) = a.val + 16 * digitsToNat as := by
  simp only [digitsToNat, List.map_cons, Nat.ofDigits_cons]

/-- A nonempty canonical digit list never denotes `0` — its last (most significant) digit
    contributes positively no matter how the rest of the list compares. -/
lemma canonicalDigits_pos (l : List Digit) (hcan : CanonicalDigits l) (hne : l ≠ []) :
    0 < digitsToNat l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as ih =>
      rcases eq_or_ne as [] with has | has
      · subst has
        have hd : a.val ≠ 0 := hcan a rfl
        rw [digitsToNat_cons]
        omega
      · have hcanas : CanonicalDigits as := canonicalDigits_tail a as hcan
        have hpos := ih hcanas has
        rw [digitsToNat_cons]
        omega

/-- `compareDigits`'s correctness spec: on canonical lists, it computes exactly `compare` on the
    numbers they denote. Proved by simultaneous structural induction on both lists — the
    length-mismatch base cases (`canonicalDigits_pos`) and the tail-first recursive step (a
    strictly-more-significant place value dominates any lower-order digit, `a.isLt`/`b.isLt`
    bounding each digit below `16`) match `compareDigits`'s own recursion exactly. -/
lemma compareDigits_correct : ∀ (xs ys : List Digit), CanonicalDigits xs → CanonicalDigits ys →
    compareDigits xs ys = compare (digitsToNat xs) (digitsToNat ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ hcanys
      cases ys with
      | nil => simp [compareDigits, digitsToNat]
      | cons b bs =>
          have hpos : 0 < digitsToNat (b :: bs) := canonicalDigits_pos (b :: bs) hcanys (by simp)
          have h0 : digitsToNat ([] : List Digit) = 0 := rfl
          rw [h0]
          exact (compare_lt_iff_lt.mpr hpos).symm
  | cons a as ih =>
      intro ys hcanxs hcanys
      cases ys with
      | nil =>
          have hpos : 0 < digitsToNat (a :: as) := canonicalDigits_pos (a :: as) hcanxs (by simp)
          have h0 : digitsToNat ([] : List Digit) = 0 := rfl
          rw [h0]
          exact (compare_gt_iff_gt.mpr hpos).symm
      | cons b bs =>
          have hcanas : CanonicalDigits as := canonicalDigits_tail a as hcanxs
          have hcanbs : CanonicalDigits bs := canonicalDigits_tail b bs hcanys
          have ihas := ih bs hcanas hcanbs
          rw [digitsToNat_cons, digitsToNat_cons]
          show (match compareDigits as bs with | .eq => compare a b | ord => ord)
              = compare (a.val + 16 * digitsToNat as) (b.val + 16 * digitsToNat bs)
          rw [ihas]
          rcases Nat.lt_trichotomy (digitsToNat as) (digitsToNat bs) with hlt | heq | hgt
          · rw [show compare (digitsToNat as) (digitsToNat bs) = .lt from compare_lt_iff_lt.mpr hlt]
            have hab : a.val + 16 * digitsToNat as < b.val + 16 * digitsToNat bs := by
              have := a.isLt; have := b.isLt; omega
            exact (compare_lt_iff_lt.mpr hab).symm
          · rw [show compare (digitsToNat as) (digitsToNat bs) = .eq from compare_eq_iff_eq.mpr heq]
            show compare a b = compare (a.val + 16 * digitsToNat as) (b.val + 16 * digitsToNat bs)
            rcases Nat.lt_trichotomy a.val b.val with h | h | h
            · have hab : a.val + 16 * digitsToNat as < b.val + 16 * digitsToNat bs := by omega
              rw [(compare_lt_iff_lt.mpr h : compare a b = .lt)]
              exact (compare_lt_iff_lt.mpr hab).symm
            · have hab : a.val + 16 * digitsToNat as = b.val + 16 * digitsToNat bs := by omega
              rw [(compare_eq_iff_eq.mpr (Fin.ext h) : compare a b = .eq)]
              exact (compare_eq_iff_eq.mpr hab).symm
            · have hab : a.val + 16 * digitsToNat as > b.val + 16 * digitsToNat bs := by omega
              rw [(compare_gt_iff_gt.mpr h : compare a b = .gt)]
              exact (compare_gt_iff_gt.mpr hab).symm
          · rw [show compare (digitsToNat as) (digitsToNat bs) = .gt from compare_gt_iff_gt.mpr hgt]
            have hab : a.val + 16 * digitsToNat as > b.val + 16 * digitsToNat bs := by
              have := a.isLt; have := b.isLt; omega
            exact (compare_gt_iff_gt.mpr hab).symm

/-- `compareDigits` specialized to two arbitrary naturals via their canonical `natToDigits`
    encoding — the form `setIfLt`/`setIfEq`/`branchIfLt`'s realization proofs actually use. -/
lemma compareDigits_natToDigits (a b : ℕ) :
    compareDigits (natToDigits a) (natToDigits b) = compare a b := by
  rw [compareDigits_correct (natToDigits a) (natToDigits b) (natToDigits_canonical a)
    (natToDigits_canonical b), digitsToNat_natToDigits, digitsToNat_natToDigits]

/-- Accumulator-style comparison, matching how a TM must scan two LSB-first digit lists in
    lockstep (front = least significant): `acc` starts as the provisional result and gets
    overwritten by the current digit pair's comparison whenever that is non-`eq`; a length
    mismatch (one list exhausted while the other still has more-significant digits left)
    resolves immediately, discarding `acc` — matching `compareDigits`'s own base cases. -/
def scanCompare : Ordering → List Digit → List Digit → Ordering
  | acc, [], [] => acc
  | _, [], _ :: _ => .lt
  | _, _ :: _, [] => .gt
  | acc, a :: as, b :: bs => scanCompare ((compare a b).then acc) as bs

/-- `scanCompare`'s bridge to the pure spec `compareDigits`: scanning LSB-first with an
    accumulator that `Ordering.then`-composes each digit pair's comparison computes exactly
    `compareDigits`'s tail-first recursion, since `compareDigits`'s own recursive step is
    literally `(compareDigits as bs).then (compare a b)` and `Ordering.then` is associative. -/
lemma scanCompare_eq_compareDigits (acc : Ordering) (xs ys : List Digit) :
    scanCompare acc xs ys = (compareDigits xs ys).then acc := by
  induction xs generalizing ys acc with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs => rfl
  | cons a as ih =>
      cases ys with
      | nil => rfl
      | cons b bs =>
          show scanCompare ((compare a b).then acc) as bs = _
          rw [ih]
          show _ = (match compareDigits as bs with | .eq => compare a b | ord => ord).then acc
          cases hcd : compareDigits as bs <;> cases hcab : compare a b <;> rfl

end NPComplete.RAMToTM

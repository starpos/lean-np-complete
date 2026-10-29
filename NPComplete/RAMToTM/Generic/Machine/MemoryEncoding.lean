module

public import NPComplete.RAMToTM.Generic.Machine.Binary
public import NPComplete.RAMToTM.Generic.Machine.FiniteStore
public import Mathlib.Data.Fintype.Sum

/-!
# Flat, self-delimiting serialization of the memory write-log

`FiniteStore.WriteLog := List (ℕ × ℕ)` is the *pure* reference model for the memory write-log,
but a `Turing.FinTM2` stack can only ever hold a `Fintype` alphabet, so an actual write-log
stack must serialize each `(addr, value)` entry as a finite run of symbols rather than storing
a `ℕ × ℕ` pair whole. `Digit := Fin 16` alone
cannot mark where one field ends and the next begins, so this widens the alphabet by exactly
the two boundary markers a scanning machine needs to tell an entry's address field from its
value field, and one entry from the next.

Each field is laid out **MSB-first**. This is not an arbitrary choice: the copy loop that
realizes `store` reads a register's LSB-first digit stack by popping one digit at a time and
pushing each copy straight onto the write-log stack as it goes, and since
`push` always prepends, that naturally leaves the pushed run in the *reverse* of the order it
was read — i.e. MSB-first — with no separate reversal pass needed (unlike `DigitAdd`'s
destination stack, whose MSB-first result exists only because a *reversal* is due). This file
fixes the resulting encoding as a pure list operation, independent of any stack/`Stmt` machinery,
and proves it is unambiguously parseable: `decodeEntry` recovers exactly the `(addr, val)` pair
`encodeEntry` wrote, together with whatever follows it in the underlying list.
-/

@[expose] public section

namespace NPComplete.RAMToTM

/-- The memory write-log stack's alphabet: a digit, or one of two field/entry boundary
    markers. Two markers (not one) are required to know where the value field ends without
    look-ahead, since the address field's length varies per entry. -/
inductive MemSym
  | digit (d : Digit)
  | addrEnd
  | entryEnd
  deriving DecidableEq

/-- `MemSym` as an `Equiv` to `Digit ⊕ Unit ⊕ Unit`: `deriving Fintype` cannot synthesize a
    `Fintype` instance for a hand-written inductive mixing a data-carrying constructor with
    bare ones, so this exposes the underlying finite structure explicitly, which the stack
    alphabets' `Fintype` instances need. -/
def memSymEquiv : MemSym ≃ Digit ⊕ Unit ⊕ Unit where
  toFun
    | MemSym.digit d => Sum.inl d
    | MemSym.addrEnd => Sum.inr (Sum.inl ())
    | MemSym.entryEnd => Sum.inr (Sum.inr ())
  invFun
    | Sum.inl d => MemSym.digit d
    | Sum.inr (Sum.inl ()) => MemSym.addrEnd
    | Sum.inr (Sum.inr ()) => MemSym.entryEnd
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with d | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype MemSym := Fintype.ofEquiv _ memSymEquiv.symm

/-- One write-log entry, MSB-first per field (see the module docstring for why): the address's
    digits, `addrEnd`, the value's digits, `entryEnd`. -/
def encodeEntry (addr val : ℕ) : List MemSym :=
  (natToDigits addr).reverse.map MemSym.digit ++ [MemSym.addrEnd] ++
    (natToDigits val).reverse.map MemSym.digit ++ [MemSym.entryEnd]

/-- The full write-log stack contents: every entry's encoding, newest-first (matching
    `WriteLog`'s own newest-first convention), concatenated. -/
def encodeLog (log : WriteLog) : List MemSym :=
  (log.map (fun e => encodeEntry e.1 e.2)).flatten

/-- `encodeLog` is a monoid homomorphism from list-append to list-append — needed whenever a
    log is built incrementally (e.g. a scanning realization prepending one entry per write) and
    the resulting `Kg.mem` content must be related back to `encodeLog` of the combined log. -/
lemma encodeLog_append (l1 l2 : WriteLog) :
    encodeLog (l1 ++ l2) = encodeLog l1 ++ encodeLog l2 := by
  simp [encodeLog, List.map_append, List.flatten_append]

/-- Consume a run of digits up to (and past) the first occurrence of `marker`, returning the
    digits read (in the order they appear, i.e. MSB-first for an `encodeEntry` field) and
    whatever comes after `marker`. `none` if `marker` never occurs — cannot happen for
    `encodeEntry`'s output, per `decodeEntry_encodeEntry` below. -/
def splitAtMarker (marker : MemSym) : List MemSym → Option (List Digit × List MemSym)
  | [] => none
  | MemSym.digit d :: rest =>
      (splitAtMarker marker rest).map (fun p => (d :: p.1, p.2))
  | m :: rest => if m = marker then some ([], rest) else none

/-- `splitAtMarker` against exactly the shape `encodeEntry`'s address field produces: a
    `digit`-wrapped run followed immediately by `addrEnd`. A digit-wrapped element can never
    equal `addrEnd` (different constructors), so the scan always runs the full length of `ds`
    before stopping, regardless of `ds`'s contents. -/
lemma splitAtMarker_addrEnd_append_digits (ds : List Digit) (rest : List MemSym) :
    splitAtMarker MemSym.addrEnd (ds.map MemSym.digit ++ (MemSym.addrEnd :: rest))
      = some (ds, rest) := by
  induction ds with
  | nil => simp [splitAtMarker]
  | cons d ds' ih => simp [splitAtMarker, ih]

/-- The `entryEnd` analogue of `splitAtMarker_addrEnd_append_digits`, for the value field. -/
lemma splitAtMarker_entryEnd_append_digits (ds : List Digit) (rest : List MemSym) :
    splitAtMarker MemSym.entryEnd (ds.map MemSym.digit ++ (MemSym.entryEnd :: rest))
      = some (ds, rest) := by
  induction ds with
  | nil => simp [splitAtMarker]
  | cons d ds' ih => simp [splitAtMarker, ih]

/-- Parse one entry off the front of a `MemSym` list: the address, the value (both restored to
    `ℕ`, undoing the MSB-first field layout), and whatever list remains after the entry. -/
def decodeEntry (l : List MemSym) : Option ((ℕ × ℕ) × List MemSym) :=
  match splitAtMarker MemSym.addrEnd l with
  | none => none
  | some (addrDigits, rest1) =>
      match splitAtMarker MemSym.entryEnd rest1 with
      | none => none
      | some (valDigits, rest2) =>
          some ((digitsToNat addrDigits.reverse, digitsToNat valDigits.reverse), rest2)

/-- `encodeEntry` is self-delimiting: `decodeEntry` recovers exactly the `(addr, val)` pair it
    encoded, together with whatever follows it — so a scan never needs look-ahead past one
    entry to know where it ends. -/
lemma decodeEntry_encodeEntry (addr val : ℕ) (rest : List MemSym) :
    decodeEntry (encodeEntry addr val ++ rest) = some ((addr, val), rest) := by
  unfold decodeEntry encodeEntry
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    splitAtMarker_addrEnd_append_digits, splitAtMarker_entryEnd_append_digits,
    List.reverse_reverse, digitsToNat_natToDigits]

/-! ## Bounding a stored value by the log's own length

`Represents`'s memory component is existential over the write-log, so any value the log can
produce (via `lookupD`) needs its digit length bounded *by the same concrete log the caller
receives*, not by `r.mem`'s abstract value alone (the same reason
`regSize`'s register bound is phrased over a concrete `RAM` rather than a `Represents` witness). -/

/-- Every value an entry in `log` stores has digit length at most the whole encoded log's own
    length — `encodeEntry`'s value field alone already contributes `(natToDigits val).length`
    symbols, and `encodeLog` only ever concatenates every entry's encoding onto that. -/
lemma natToDigits_length_le_encodeLog_length_of_mem (log : WriteLog) (a v : ℕ)
    (h : (a, v) ∈ log) :
    (natToDigits v).length ≤ (encodeLog log).length := by
  induction log with
  | nil => simp at h
  | cons e rest ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq
      simp only [encodeLog, List.map_cons, List.flatten_cons, List.length_append]
      have hee : (encodeEntry a v).length =
          (natToDigits a).length + 1 + ((natToDigits v).length + 1) := by
        simp [encodeEntry]; omega
      omega
    · have hrest := ih hmem
      simp only [encodeLog, List.map_cons, List.flatten_cons, List.length_append] at *
      omega

/-- `lookupD`'s result is either `default` or the value of some entry actually present in
    `log` (`List.mem_of_find?_eq_some`), so its digit length never exceeds the larger of
    `default`'s own digit length and the encoded log's length. -/
lemma natToDigits_length_lookupD_le (log : WriteLog) (addr default : ℕ) :
    (natToDigits (lookupD log addr default)).length ≤
      max (natToDigits default).length (encodeLog log).length := by
  unfold lookupD
  cases h : log.find? (fun e => e.1 = addr) with
  | none => simp
  | some p =>
    obtain ⟨a, v⟩ := p
    simp only
    exact le_max_of_le_right
      (natToDigits_length_le_encodeLog_length_of_mem log a v (List.mem_of_find?_eq_some h))

end NPComplete.RAMToTM

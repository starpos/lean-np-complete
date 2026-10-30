module

meta import NPComplete.Meta.ApiLayer
public import Mathlib.Data.Nat.Basic

/-!
# Generic prefix-free bit encodings

These prefix-free encodings provide a reusable bit-level basis for reductions and machine inputs
without depending on problem-specific state or operational semantics.

A natural `n` is emitted as `n` `false` bits followed by a terminating `true`. The unique
terminator makes the encoding prefix-free, and fixed-order concatenation carries this property
to compound encodings.
-/

@[expose] public section

namespace NPComplete.BitEncoding

/-- Serialized bits. All encodings in this module produce `Bits`. -/
@[stable_api] abbrev Bits := List Bool

/-! ## `Nat`: unary with a terminating `true` -/

/-- `encodeNat n = false^n ++ [true]`: `n` `false` bits followed by a terminating
    `true`. Prefix-free — the terminator is the sole `true` — so concatenations decode
    uniquely from left to right. -/
@[stable_api] def encodeNat : ℕ → Bits
  | 0 => [true]
  | n + 1 => false :: encodeNat n

/-- Base equation of the unary encoding. Together with `encodeNat_succ` it determines `encodeNat`,
    so the pair pins the contract that survives rewriting the definition. -/
@[stable_api, simp] lemma encodeNat_zero : encodeNat 0 = [true] := rfl

/-- Step equation of the unary encoding: each successor prepends one `false`. -/
@[stable_api] lemma encodeNat_succ (n : ℕ) : encodeNat (n + 1) = false :: encodeNat n := rfl

@[construction_api] lemma encodeNat_getElem : ∀ (n i : ℕ) (h : i < (encodeNat n).length),
    (encodeNat n)[i] = decide (i = n)
  | 0, 0, _ => rfl
  | 0, i + 1, h => by simp at h
  | n + 1, 0, _ => by simp [encodeNat_succ]
  | n + 1, i + 1, h => by
      have h' : i < (encodeNat n).length := by simpa [encodeNat_succ] using h
      simp [encodeNat_succ, encodeNat_getElem n i h']

/-- The unary encoding of `n` has exactly `n + 1` bits, which is the size measure that
    polynomial bounds are stated against. -/
@[stable_api] lemma encodeNat_length : ∀ n, (encodeNat n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [encodeNat_succ, encodeNat_length n]

/-- **Prefix-free splitting.** If two prefix-free `Nat` encodings each followed by a
    tail agree as concatenated lists, the `Nat` parts agree and the tails agree. The
    workhorse behind every downstream injectivity proof. -/
lemma encodeNat_append_inj {m n : ℕ} {xs ys : Bits}
    (h : encodeNat m ++ xs = encodeNat n ++ ys) : m = n ∧ xs = ys := by
  induction m generalizing n xs ys with
  | zero =>
      cases n with
      | zero => simp [encodeNat] at h; exact ⟨rfl, h⟩
      | succ n' => simp [encodeNat] at h
  | succ m' ih =>
      cases n with
      | zero => simp [encodeNat] at h
      | succ n' =>
          simp [encodeNat] at h
          obtain ⟨heq, htail⟩ := ih h
          exact ⟨congrArg Nat.succ heq, htail⟩

@[stable_api] lemma encodeNat_injective : Function.Injective encodeNat := by
  intro m n h
  exact (encodeNat_append_inj (xs := []) (ys := []) (by simpa using h)).1

/-! ## Length-prefixed list encoding

A list of already-encoded pieces (each prefix-free) is emitted as `encodeNat l.length`
followed by the concatenation of the piece encodings. The length prefix makes the
decoder know how many pieces to consume, so the whole list encoding remains
prefix-free even when the tail is a further encoding. -/

/-- Encode a list by prepending an `encodeNat`-length prefix, then concatenating the
    encoded pieces. Injectivity requires the piece encoder `enc` itself to be
    prefix-free — every `encodeNat`-based encoding in this file is. -/
@[stable_api] def encodeList (enc : α → Bits) (l : List α) : Bits :=
  encodeNat l.length ++ (l.map enc).flatten

/-- Length-equal lists of prefix-freely-encoded pieces, concatenated with tails, split
    uniquely: the lists agree and the tails agree. The core lemma feeding
    `encodeList_append_inj`. -/
lemma encodeList_flatten_append_inj
    {enc : α → Bits}
    (henc : ∀ {x y : α} {p q : Bits}, enc x ++ p = enc y ++ q → x = y ∧ p = q) :
    ∀ {l1 l2 : List α}, l1.length = l2.length → ∀ {xs ys : Bits},
      (l1.map enc).flatten ++ xs = (l2.map enc).flatten ++ ys →
      l1 = l2 ∧ xs = ys := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 hlen xs ys h
      cases l2 with
      | nil => simp at h; exact ⟨rfl, h⟩
      | cons _ _ => simp at hlen
  | cons x xs' ih =>
      intro l2 hlen xxs yys h
      cases l2 with
      | nil => simp at hlen
      | cons y ys' =>
          simp at hlen
          simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
          obtain ⟨hxy, hrest⟩ := henc h
          obtain ⟨hlist, htail⟩ := ih hlen hrest
          exact ⟨by rw [hxy, hlist], htail⟩

/-- **Prefix-free splitting for `encodeList`.** If two length-prefixed encoded lists
    each followed by a tail agree, the lists agree and the tails agree. -/
lemma encodeList_append_inj
    {enc : α → Bits}
    (henc : ∀ {x y : α} {p q : Bits}, enc x ++ p = enc y ++ q → x = y ∧ p = q)
    {l1 l2 : List α} {xs ys : Bits}
    (h : encodeList enc l1 ++ xs = encodeList enc l2 ++ ys) : l1 = l2 ∧ xs = ys := by
  simp only [encodeList, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := encodeNat_append_inj h
  exact encodeList_flatten_append_inj henc hlen hrest

@[stable_api] lemma encodeList_injective
    {enc : α → Bits}
    (henc : ∀ {x y : α} {p q : Bits}, enc x ++ p = enc y ++ q → x = y ∧ p = q) :
    Function.Injective (encodeList enc) := by
  intro l1 l2 h
  exact (encodeList_append_inj henc (xs := []) (ys := []) (by simpa using h)).1

/-- **Bit-size lower bound for `encodeList`.** The encoding starts with a unary
    `encodeNat l.length` of length `l.length + 1`, so the total bit-size is at
    least `l.length + 1 > l.length` for any piece encoder. -/
@[construction_api] lemma encodeList_length_ge {α : Type _} (enc : α → Bits) (l : List α) :
    l.length + 1 ≤ (encodeList enc l).length := by
  simp only [encodeList, List.length_append, encodeNat_length]
  omega

/-- **Per-element bit-size lower bound for `encodeList`.** Any member's own encoding is no
    longer than the whole length-prefixed list encoding, since it sits inside the flattened
    body. -/
@[construction_api] lemma encodeList_length_ge_of_mem {α : Type _} (enc : α → Bits) {l : List α} {x : α}
    (hx : x ∈ l) : (enc x).length ≤ (encodeList enc l).length := by
  have hflat : (enc x).length ≤ (l.map enc).flatten.length := by
    induction l with
    | nil => cases hx
    | cons y ys ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        rcases List.mem_cons.mp hx with h | h
        · subst h; omega
        · exact Nat.le_add_left_of_le (ih h)
  simp only [encodeList, List.length_append]
  exact Nat.le_add_left_of_le hflat

/-! ## `Bool`: a fixed-length one-bit encoding -/

/-- Encode a `Bool` as its single bit — fixed length, trivially prefix-free. -/
@[stable_api] def encodeBool : Bool → Bits := fun b => [b]

lemma encodeBool_length (b : Bool) : (encodeBool b).length = 1 := by cases b <;> rfl

lemma encodeBool_append_inj {a b : Bool} {xs ys : Bits}
    (h : encodeBool a ++ xs = encodeBool b ++ ys) : a = b ∧ xs = ys := by
  cases a <;> cases b <;> simp [encodeBool] at h ⊢ <;> exact h

@[stable_api] lemma encodeBool_injective : Function.Injective encodeBool := by
  intro a b h
  exact (encodeBool_append_inj (xs := []) (ys := []) (by simpa using h)).1

end NPComplete.BitEncoding

module

public import NPComplete

@[expose] public section

namespace NPCompleteTest.UnaryReader

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitEncoding

def sampleStore (r : ℕ) : ℕ :=
  if r = 0 then 5 else if r = 3 then 4 else if r = 8 then 1 else if r = 9 then 1 else 0

lemma sample_bits : BitsFrom sampleStore 5 (encodeNat 3 ++ [true, false]) := by
  intro i hi
  have h : i < 6 := by simpa [encodeNat, encodeNat_succ] using hi
  interval_cases i <;> rfl

example : (readUnaryProgAt 0 1 2 3).eval sampleStore 1 = 3 := by
  have h := readUnaryProgAt_correct (c := 0) (k := 1) (d := 2) (lr := 3)
    (b := 5) (n := 3) (rest := [true, false]) (σ := sampleStore)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) sample_bits
  exact h.2.1

example {P : ℕ → Prop} (h0 : ¬ P 0) (h1 : ¬ P 1) (h2 : ¬ P 2) :
    (readUnaryProgAt 0 1 2 3).Avoids P := readUnaryProgAt_avoids h0 h1 h2

example {σ : Store} {b : ℕ} {xs ys : Bits} (h : BitsFrom σ b xs)
    (h' : BitsFrom σ (b + xs.length) ys) : BitsFrom σ b (xs ++ ys) :=
  BitsFrom.append h h'

example : BitsFrom ((readUnaryProgAt 0 1 2 3).eval sampleStore) 9 [true, false] :=
  (readUnaryProgAt_frame_rest (by decide) (by decide) (by decide) sample_bits).2

example (bits : Bits) {B : ℕ} (hB : 1 ≤ B) (hb : bits.length ≤ B) :
    StoreValuesLe B (bitInputStore bits) := storeValuesLe_bitInputStore bits hB hb

example {S P : ℕ → Prop} {Q : Store → Prop} {p : Program} {σ : Store}
    (hp : WritesIn S p σ) (hq : ReadsOnly P Q) (h : ∀ r, P r → ¬ S r) (hσ : Q σ) :
    Q (p.eval σ) := hp.preserves hq h hσ

end NPCompleteTest.UnaryReader

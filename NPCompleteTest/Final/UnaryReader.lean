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

end NPCompleteTest.UnaryReader

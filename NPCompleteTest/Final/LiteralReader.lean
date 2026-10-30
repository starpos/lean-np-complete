module

public import NPComplete

@[expose] public section

namespace NPCompleteTest.LiteralReader

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitEncoding NPComplete.SAT
open NPComplete.CookLevin

def sampleLiteralStore (r : ℕ) : ℕ :=
  if r = 0 then 6 else if r = 4 then 4 else if r = 6 then 1 else if r = 9 then 1 else if r = 11 then 1 else 0

lemma sample_bits : BitsFrom sampleLiteralStore 6 (encodeLiteral (.neg 2) ++ [false, true]) := by
  intro i hi
  have h : i < 6 := by simpa [encodeLiteral, encodeNat, encodeNat_succ] using hi
  interval_cases i <;> rfl

example : (decodeLiteralValueProgramAt 0 1 2 3 4).eval sampleLiteralStore 2 = 2 := by
  have h := decodeLiteralValueProgramAt_correct 0 1 2 3 4 4 6 (.neg 2) [false, true]
    sampleLiteralStore (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) sample_bits
  exact h.2.2.1

end NPCompleteTest.LiteralReader

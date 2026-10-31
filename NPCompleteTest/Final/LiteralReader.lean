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

example (σ : Store) : (decodeLiteralValueProgramAt 0 1 2 3 4).eval σ 5 = σ 5 :=
  decodeLiteralValueProgramAt_frame 0 1 2 3 4 5 σ (by decide) (by decide) (by decide) (by decide)

example : ProgramBoundedIn 11 sampleLiteralStore (decodeLiteralValueProgramAt 0 1 2 3 4) :=
  decodeLiteralValueProgramAt_bounded (b := 6) (l := .neg 2) (rest := [false, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) sample_bits (by decide) (by decide)

example : BitsFrom ((decodeLiteralValueProgramAt 0 1 2 3 4).eval sampleLiteralStore)
    (6 + (encodeLiteral (.neg 2)).length) [false, true] :=
  (decodeLiteralValueProgramAt_frame_rest 0 1 2 3 4 6 (.neg 2) [false, true]
    sampleLiteralStore (by decide) (by decide) (by decide) (by decide) sample_bits).2

end NPCompleteTest.LiteralReader

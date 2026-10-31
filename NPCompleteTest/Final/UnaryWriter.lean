module

public import NPComplete

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.BitEncoding

example (σ : Store) (h : σ 14 = 0) :
    (writeUnaryProgAt 100 13 14).eval σ (100 + σ 13) = 1 := by
  have hc := writeUnaryProgAt_correct (base := 100) (c := 13) (k := 14) (σ := σ)
    (by omega) (by omega) (by omega)
  have hb := hc.2.1 0 (by simp [h])
  simpa [h, encodeNat, Nat.add_zero] using hb

example (σ : Store) (h13 : σ 13 = 0) (n m : ℕ) (hn : σ 14 = n) (hm : σ 15 = m) :
    let τ := (writeUnaryProgAt 100 13 14).eval σ
    let υ := (writeUnaryProgAt 100 13 15).eval τ
    υ 13 = n + m + 2 ∧ BitsFrom υ 100 (encodeNat n) ∧
      BitsFrom υ (100 + n + 1) (encodeNat m) ∧
      (∀ r, r ≠ 13 → r < 100 → υ r = σ r) ∧
      (∀ r, 100 + n + m + 2 ≤ r → υ r = σ r) := by
  dsimp only
  let τ := (writeUnaryProgAt 100 13 14).eval σ
  let υ := (writeUnaryProgAt 100 13 15).eval τ
  have hc1 := writeUnaryProgAt_correct (base := 100) (c := 13) (k := 14) (σ := σ)
    (by omega) (by omega) (by omega)
  have ht13 : τ 13 = n + 1 := by simpa [τ, h13, hn] using hc1.1
  have ht15 : τ 15 = m := by
    rw [show τ 15 = σ 15 from
      writeUnaryProgAt_frame (by omega) (by omega) (by omega) (by omega) (by omega), hm]
  have hc2 := writeUnaryProgAt_correct (base := 100) (c := 13) (k := 15) (σ := τ)
    (by omega) (by omega) (by omega)
  have hb1 : BitsFrom τ 100 (encodeNat n) := by simpa [τ, h13, hn] using hc1.2.1
  change υ 13 = _ ∧ BitsFrom υ 100 _ ∧ BitsFrom υ (100 + n + 1) _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (writeUnaryProgAt 100 13 15).eval τ 13 = _
    rw [hc2.1, ht13, ht15]; omega
  · apply bitsFrom_of_eq_on _ hb1
    intro i hi
    have hi' : i < n + 1 := by simpa [encodeNat_length] using hi
    apply writeUnaryProgAt_frame (by omega) (by omega) (by omega) (by omega)
    left; rw [ht13]; omega
  · simpa [υ, ht13, ht15, Nat.add_assoc] using hc2.2.1
  · intro r hr hr100
    change υ r = σ r
    rw [show υ r = τ r from writeUnaryProgAt_frame (by omega) (by omega) (by omega) hr
      (by left; rw [ht13]; omega)]
    exact writeUnaryProgAt_frame (by omega) (by omega) (by omega) hr (by left; rw [h13]; omega)
  · intro r hr
    change υ r = σ r
    have hr13 : r ≠ 13 := by omega
    rw [show υ r = τ r from writeUnaryProgAt_frame (by omega) (by omega) (by omega) hr13
      (by right; rw [ht13, ht15]; omega)]
    exact writeUnaryProgAt_frame (by omega) (by omega) (by omega) hr13
      (by right; rw [h13, hn]; omega)

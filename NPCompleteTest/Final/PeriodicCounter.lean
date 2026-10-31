module

public import NPComplete

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM

example (σ : Store) (h : σ 2 = 1) :
    (periodicCounterProg 3 1 2).eval σ 1 = σ 1 ∧
    (periodicCounterProg 3 1 2).eval σ 2 = 2 := by
  have hc := periodicCounterProg_correct (d := 3) (cr := 1) (pr := 2) (σ := σ)
    (by decide) (by omega)
  constructor
  · simpa only [h, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] using hc.1
  · simpa only [h, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd] using hc.2.1

example (σ : Store) (h : σ 2 = 2) :
    (periodicCounterProg 3 1 2).eval σ 1 = σ 1 + 1 ∧
    (periodicCounterProg 3 1 2).eval σ 2 = 0 := by
  have hc := periodicCounterProg_correct (d := 3) (cr := 1) (pr := 2) (σ := σ)
    (by decide) (by omega)
  constructor
  · simpa only [h, Nat.reduceSub, ↓reduceIte] using hc.1
  · simpa only [h, Nat.reduceSub, ↓reduceIte] using hc.2.1

example (σ : Store) (h : σ 2 = 0) :
    (periodicCounterProg 1 1 2).eval σ 1 = σ 1 + 1 ∧
    (periodicCounterProg 1 1 2).eval σ 2 = 0 := by
  have hc := periodicCounterProg_correct (d := 1) (cr := 1) (pr := 2) (σ := σ)
    (by decide) (by omega)
  constructor
  · simpa only [h, Nat.reduceSub, ↓reduceIte] using hc.1
  · simpa only [h, Nat.reduceSub, ↓reduceIte] using hc.2.1

example (σ : Store) (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    (periodicCounterProg 3 1 2).eval σ r = σ r :=
  (periodicCounterProg_avoids 3 1 2).eval_frame σ ⟨h1, h2⟩

example (σ : Store) (B : ℕ) (hp : σ 2 < 3) (hB : 3 ≤ B) (hc : σ 1 + 1 ≤ B) :
    ProgramBoundedIn B σ (periodicCounterProg 3 1 2) :=
  periodicCounterProg_bounded (by decide) hp (by omega) (by omega) hB hc

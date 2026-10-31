module

public import NPComplete

@[expose] public section

open NPComplete.BoundedWhile NPComplete.RAMToTM

example (B : ℕ) (σ : Store) (h : σ 2 + 1 ≤ B) (hb : 2 ≤ B) :
    ProgramBoundedIn B σ (.assign 2 (.add (.reg 2) (.const 1))) := by
  bounded_simp [h, hb]
  omega

example (B : ℕ) (σ : Store) (h : σ 1 ≤ B) (_hv : σ 2 ≤ B)
    (hb : 2 ≤ B) : ProgramBoundedIn B σ (.assignInd (.reg 1) (.reg 2)) := by
  bounded_simp [h]
  omega

example (B : ℕ) (σ : Store) (h : 3 ≤ B) (_hc : σ 1 ≤ B) :
    ProgramBoundedIn B σ (.ifNZ (.reg 1) (.assign 2 (.const 2))
      (.assign 3 (.const 3))) := by
  by_cases hzero : σ 1 = 0
  · bounded_simp [hzero]
    omega
  · bounded_simp [hzero]
    omega

example (B x y : ℕ) (σ : Store) (hx : x ≤ B) (hy : y ≤ B) (h : x * y ≤ B) :
    ProgramBoundedIn B σ (.assign 0 (.mul (.const x) (.const y))) := by
  bounded_simp [hx, hy]
  exact ⟨Nat.zero_le _, h⟩

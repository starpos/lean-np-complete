module

public import NPComplete.CookLevin.Verifier.SATBool

/-!
The SAT and 3SAT verifier specifications share the same assignment-window lemmas; keeping them
in one support module prevents their proofs from drifting.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT

lemma getD_range_map (τ : ℕ → Bool) (n v : ℕ) (hv : v < n) :
    (List.map τ (List.range n)).getD v false = τ v := by
  have hlen : v < (List.map τ (List.range n)).length := by
    simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_map,
    List.getElem_range (by simpa using hv)]
  rfl

/-- A literal whose variable is covered by the agreement window evaluates identically under `w`
    and `τ`. -/
lemma literal_eval_congr {w : List Bool} {τ : Literal.Assignment} {n : ℕ}
    (hW : ∀ v, v < n → w.getD v false = τ v) (l : Literal) (hl : l.var < n) :
    l.eval (decodeAssignment w) = l.eval τ := by
  cases l with
  | pos v => show w.getD v false = τ v; exact hW v hl
  | neg v => show (!w.getD v false) = (!τ v); rw [hW v hl]

end NPComplete.CookLevin

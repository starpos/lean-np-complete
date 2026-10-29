module

public import NPComplete.CookLevin.Tableau.ClauseBuilders

/-!
# Initial tape snapshot

The initial tableau row must agree with the machine's tape convention, including blank cells
outside the input. This module records indexed tape facts and their behavior under blank extension
so initial clauses can be justified from an actual input.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing TM0
open NPComplete.SAT (Literal)
open NPComplete.CookLevin.TM1to0 (FinTM0)
open NPComplete.CookLevin.TM2to1 (StepsTo stepsTo_zero stepsTo_succ)

variable {Γ Λ : Type*}

/-! ## Initial / accept snapshot on `Tape.mk₁` -/

def initSymbol [Inhabited Γ] (input : List Γ) (p : ℤ) : Γ :=
  if 0 ≤ p then input.getI p.toNat else default

lemma tape_mk₁_left [Inhabited Γ] (l : List Γ) :
    (Tape.mk₁ l).left = ListBlank.mk [] :=
  rfl

lemma list_blank_nth_nil [Inhabited Γ] (i : ℕ) :
    (ListBlank.mk ([] : List Γ)).nth i = default := by
  rw [ListBlank.nth_mk]
  simp [List.getI]

lemma tape_mk₁_nth_neg [Inhabited Γ] (l : List Γ) (i : ℕ) :
    (Tape.mk₁ l).nth (-(i + 1 : ℕ)) = default := by
  have h : (Tape.mk₁ l).nth (-(i + 1 : ℕ)) = (Tape.mk₁ l).left.nth i := rfl
  rw [h, tape_mk₁_left, list_blank_nth_nil]

lemma tape_mk₁_nth_negSucc [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (Tape.mk₁ l).nth (Int.negSucc n) = default := by
  simpa [Int.negSucc_eq] using tape_mk₁_nth_neg l n

lemma tape_mk₁_nth_nat [Inhabited Γ] (l : List Γ) (i : ℕ) :
    (Tape.mk₁ l).nth i = l.getI i := by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]

lemma tape_mk₁_nth [Inhabited Γ] (l : List Γ) (p : ℤ) :
    (Tape.mk₁ l).nth p = initSymbol l p := by
  cases p with
  | ofNat n => simp [initSymbol, tape_mk₁_nth_nat]
  | negSucc n => simp [initSymbol, Int.negSucc_not_nonneg, tape_mk₁_nth_negSucc]

lemma initSymbol_append_left [Inhabited Γ] (pref suffix : List Γ)
    {n : ℕ} (hn : n < pref.length) :
    initSymbol (pref ++ suffix) (n : ℤ) = initSymbol pref (n : ℤ) := by
  simp [initSymbol, List.getI_append, hn]

lemma initSymbol_append_right [Inhabited Γ] (pref suffix : List Γ) (n : ℕ) :
    initSymbol (pref ++ suffix) ((pref.length + n : ℕ) : ℤ) = suffix.getI n := by
  rw [initSymbol]
  have hnonneg : (0 : ℤ) ≤ (pref.length + n : ℕ) := by omega
  rw [ite_eq_left hnonneg]
  change (pref ++ suffix).getI (pref.length + n) = suffix.getI n
  have hlen : pref.length ≤ pref.length + n := by omega
  rw [List.getI_append_right _ _ _ hlen]
  simp

lemma initSymbol_append_default [Inhabited Γ] (pref suffix : List Γ) (n : ℕ) :
    initSymbol (pref ++ suffix)
        ((pref.length + suffix.length + n : ℕ) : ℤ) = default := by
  rw [initSymbol]
  have hnonneg : (0 : ℤ) ≤ (pref.length + suffix.length + n : ℕ) := by omega
  rw [ite_eq_left hnonneg]
  change (pref ++ suffix).getI (pref.length + suffix.length + n) = default
  apply List.getI_eq_default
  simp [List.length_append]

lemma tape_mk₁_append_blank [Inhabited Γ] (l : List Γ) (n : ℕ) :
    Tape.mk₁ (l ++ List.replicate n (default : Γ)) = Tape.mk₁ l := by
  simp only [Tape.mk₁, Tape.mk₂]
  congr 1
  exact Quotient.sound' (Or.inr ⟨n, rfl⟩)

lemma machineOutputsInTime_append_blank [Inhabited Λ]
    {M : Machine (Option Bool) Λ} {input output : List (Option Bool)}
    {T n : ℕ} (h : MachineOutputsInTime M input output T) :
    MachineOutputsInTime M (input ++ List.replicate n none) output T := by
  obtain ⟨q, t, ht, hs, hh⟩ := h
  refine ⟨q, t, ht, ?_, hh⟩
  simp only [init]
  have htape : Tape.mk₁ (input ++ List.replicate n (none : Option Bool)) =
      Tape.mk₁ input := tape_mk₁_append_blank input n
  rw [htape]
  exact hs

lemma machineOutputsInTime_of_append_blank [Inhabited Λ]
    {M : Machine (Option Bool) Λ} {input output : List (Option Bool)}
    {T n : ℕ} (h : MachineOutputsInTime M
      (input ++ List.replicate n none) output T) :
    MachineOutputsInTime M input output T := by
  obtain ⟨q, t, ht, hs, hh⟩ := h
  refine ⟨q, t, ht, ?_, hh⟩
  simp only [init] at hs ⊢
  have htape : Tape.mk₁ (input ++ List.replicate n (none : Option Bool)) =
      Tape.mk₁ input := tape_mk₁_append_blank input n
  rw [htape] at hs
  exact hs

lemma initSymbol_append_idxToPos_prefix [Inhabited Γ]
    (pref suffix : List Γ) (T p : ℕ) (hp : p < T + pref.length) :
    initSymbol (pref ++ suffix) (idxToPos T p) =
      initSymbol pref (idxToPos T p) := by
  by_cases hpt : p < T
  · have hneg : idxToPos T p < 0 := by
      simp [idxToPos]
      omega
    have hnot : ¬ 0 ≤ idxToPos T p := by omega
    simp [initSymbol, hnot]
  · let n := p - T
    have hpEq : p = T + n := by
      dsimp [n]
      omega
    have hn : n < pref.length := by
      dsimp [n]
      omega
    rw [hpEq]
    simpa [idxToPos] using initSymbol_append_left pref suffix hn

lemma initSymbol_append_idxToPos_suffix [Inhabited Γ]
    (pref suffix : List Γ) (T p : ℕ)
    (hp : T + pref.length ≤ p)
    (hp' : p < T + pref.length + suffix.length) :
    initSymbol (pref ++ suffix) (idxToPos T p) =
      suffix.getI (p - (T + pref.length)) := by
  let n := p - (T + pref.length)
  have hpEq : p = T + pref.length + n := by
    dsimp [n]
    omega
  have hn : n < suffix.length := by
    dsimp [n]
    omega
  rw [hpEq]
  have hsub : T + pref.length + n - (T + pref.length) = n := by omega
  rw [hsub]
  simpa [idxToPos, Nat.add_assoc] using initSymbol_append_right pref suffix n

lemma initSymbol_append_idxToPos_default [Inhabited Γ]
    (pref suffix : List Γ) (T p : ℕ)
    (hp : T + pref.length + suffix.length ≤ p) :
    initSymbol (pref ++ suffix) (idxToPos T p) = default := by
  let n := p - (T + pref.length + suffix.length)
  have hpEq : p = T + pref.length + suffix.length + n := by
    dsimp [n]
    omega
  rw [hpEq]
  simpa [idxToPos, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    initSymbol_append_default pref suffix n


end NPComplete.CookLevin

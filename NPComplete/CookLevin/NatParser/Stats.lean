module

public import NPComplete.CookLevin.NatParser.Foundation

/-! ## Pure statistics for the sliding-window reduction

The executable parser above exposes the maximum variable of one clause.  The
reduction also needs the number of fresh variables and the number of emitted
three-clauses.  These small recurrences mirror `splitTail` and `clauseToThree`
without depending on the reduction module, so they can be used by an emitter
or by a scanner before the semantic CNF layer is imported.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr cost_forN loopCost loopCost_le_of_body_le
    eval_seq eval_assign eval_ifNZ eval_forN loopEval loopEval_succ cost_seq cost_assign
    writeReg writeReg_same writeReg_diff)
open NPComplete.BitEncoding
  (Bits encodeNat encodeList encodeList_length_ge encodeNat_length)
open NPComplete.SAT (Literal)

def splitTailBaseStat (base : ℕ) : List Literal → ℕ
  | [] => base
  | [_] => base
  | [_, _] => base
  | _ :: l2 :: l3 :: rest => splitTailBaseStat (base + 1) (l2 :: l3 :: rest)

def splitTailCountStat : List Literal → ℕ
  | [] => 1
  | [_] => 1
  | [_, _] => 1
  | _ :: l2 :: l3 :: rest => splitTailCountStat (l2 :: l3 :: rest) + 1

def clauseFreshBaseStat (base : ℕ) : List Literal → ℕ
  | [] => base + 1
  | [_] => base
  | [_, _] => base
  | _ :: _ :: l3 :: rest => splitTailBaseStat (base + 1) (l3 :: rest)

def clauseThreeCountStat : List Literal → ℕ
  | [] => 2
  | [_] => 1
  | [_, _] => 1
  | _ :: _ :: l3 :: rest => splitTailCountStat (l3 :: rest) + 1

def cnfFreshBaseStat (base : ℕ) : List (List Literal) → ℕ
  | [] => base
  | ls :: rest => cnfFreshBaseStat (clauseFreshBaseStat base ls) rest

def cnfThreeCountStat : List (List Literal) → ℕ
  | [] => 0
  | ls :: rest => clauseThreeCountStat ls + cnfThreeCountStat rest

def cnfLiteralVarMaxStat : ℕ → List (List Literal) → ℕ
  | m, [] => m
  | m, ls :: rest => cnfLiteralVarMaxStat (max m (literalVarMax ls)) rest

lemma splitTailBaseStat_cons3 (base : ℕ) (l1 l2 l3 : Literal)
    (rest : List Literal) :
    splitTailBaseStat base (l1 :: l2 :: l3 :: rest) =
      splitTailBaseStat (base + 1) (l2 :: l3 :: rest) := by
  rfl

lemma splitTailCountStat_cons3 (l1 l2 l3 : Literal) (rest : List Literal) :
    splitTailCountStat (l1 :: l2 :: l3 :: rest) =
      splitTailCountStat (l2 :: l3 :: rest) + 1 := by
  rfl

def splitTailFreshIncByLength : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | n + 3 => n + 1

def splitTailCountByLength : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => n + 2

def clauseFreshIncByLength : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => max 1 n

def clauseThreeCountByLength : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | n + 3 => max 2 (n + 1)

lemma splitTailFreshIncByLength_cons3 (n : ℕ) :
    1 + splitTailFreshIncByLength (n + 1) = max 1 n := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              simp [splitTailFreshIncByLength]
              omega

lemma splitTailFreshIncByLength_succ (n : ℕ) :
    1 + splitTailFreshIncByLength (n + 2) =
      splitTailFreshIncByLength (n + 3) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          simp [splitTailFreshIncByLength]
          omega

lemma splitTailCountByLength_add_one (n : ℕ) :
    splitTailCountByLength n + 1 = max 2 n := by
  cases n with
  | zero => simp [splitTailCountByLength]
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              simp [splitTailCountByLength]

lemma splitTailCountByLength_succ (n : ℕ) :
    splitTailCountByLength (n + 2) + 1 =
      splitTailCountByLength (n + 3) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          simp [splitTailCountByLength]

lemma clauseFreshIncByLength_cons3 (n : ℕ) :
    clauseFreshIncByLength (n + 3) = max 1 n := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n => simp [clauseFreshIncByLength]

lemma clauseThreeCountByLength_cons3 (n : ℕ) :
    clauseThreeCountByLength (n + 3) = max 2 (n + 1) := by
  cases n with
  | zero => rfl
  | succ n => simp [clauseThreeCountByLength]

lemma splitTailBaseStat_eq_length (base : ℕ) (xs : List Literal) :
    splitTailBaseStat base xs = base + splitTailFreshIncByLength xs.length := by
  induction xs generalizing base with
  | nil => rfl
  | cons l rest ih =>
      cases rest with
      | nil => rfl
      | cons l2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons l3 rest3 =>
              rw [splitTailBaseStat_cons3]
              rw [ih (base + 1)]
              simp only [List.length_cons]
              rw [show rest3.length + 2 = rest3.length + 1 + 1 by omega]
              rw [show rest3.length + 3 = rest3.length + 1 + 2 by omega]
              rw [Nat.add_assoc]
              rw [splitTailFreshIncByLength_succ]

lemma splitTailCountStat_eq_length (xs : List Literal) :
    splitTailCountStat xs = splitTailCountByLength xs.length := by
  induction xs with
  | nil => rfl
  | cons l rest ih =>
      cases rest with
      | nil => rfl
      | cons l2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons l3 rest3 =>
              rw [splitTailCountStat_cons3]
              rw [ih]
              simp only [List.length_cons]
              rw [show rest3.length + 2 = rest3.length + 1 + 1 by omega]
              rw [show rest3.length + 3 = rest3.length + 1 + 2 by omega]
              rw [splitTailCountByLength_succ]

lemma clauseFreshBaseStat_eq_length (base : ℕ) (xs : List Literal) :
    clauseFreshBaseStat base xs = base + clauseFreshIncByLength xs.length := by
  match xs with
  | [] => rfl
  | [l] => rfl
  | [l1, l2] => rfl
  | l1 :: l2 :: l3 :: rest =>
      rw [show clauseFreshBaseStat base (l1 :: l2 :: l3 :: rest) =
        splitTailBaseStat (base + 1) (l3 :: rest) by rfl]
      rw [splitTailBaseStat_eq_length]
      simp only [List.length_cons]
      rw [Nat.add_assoc]
      rw [splitTailFreshIncByLength_cons3]
      rw [clauseFreshIncByLength_cons3]

lemma clauseThreeCountStat_eq_length (xs : List Literal) :
    clauseThreeCountStat xs = clauseThreeCountByLength xs.length := by
  match xs with
  | [] => rfl
  | [l] => rfl
  | [l1, l2] => rfl
  | l1 :: l2 :: l3 :: rest =>
      rw [show clauseThreeCountStat (l1 :: l2 :: l3 :: rest) =
        splitTailCountStat (l3 :: rest) + 1 by rfl]
      rw [splitTailCountStat_eq_length]
      simp only [List.length_cons]
      rw [splitTailCountByLength_add_one]
      rw [clauseThreeCountByLength_cons3]

end NPComplete.CookLevin

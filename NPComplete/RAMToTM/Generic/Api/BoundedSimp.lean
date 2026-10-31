module

public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded

/-! Explicit simplification for resource obligations avoids changing global simp behavior. -/

@[expose] public section

namespace NPComplete.RAMToTM
open NPComplete.BoundedWhile

syntax "bounded_simp" Lean.Parser.Tactic.simpArgs : tactic
macro_rules
  | `(tactic| bounded_simp [$args,*]) =>
    `(tactic| simp (disch := omega) only [$args,*,
      programBoundedIn_assign_iff, programBoundedIn_assignInd_iff,
      programBoundedIn_seq_iff, programBoundedIn_ifNZ_iff, ExprBoundedIn, Expr.eval,
      eval_seq, eval_assign, eval_assignInd, eval_ifNZ, writeReg,
      Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLeDiff,
      Nat.reduceLT, Nat.succ_ne_self, ↓reduceIte, ite_eq_left, ite_eq_right,
      Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
      and_true, true_and, and_self, and_self_left, and_self_right])

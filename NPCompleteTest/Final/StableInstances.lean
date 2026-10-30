module

public import NPComplete

@[expose] public section

#synth DecidableEq NPComplete.SAT.Literal
#synth Repr NPComplete.SAT.Literal
#synth Inhabited NPComplete.SAT.Literal
#synth DecidableEq NPComplete.CookLevin.Clause
#synth Repr NPComplete.CookLevin.Clause
#synth Inhabited NPComplete.CookLevin.Clause
#synth DecidableEq NPComplete.CookLevin.CNF
#synth Repr NPComplete.CookLevin.CNF
#synth DecidableEq NPComplete.SAT.ThreeClause
#synth Repr NPComplete.SAT.ThreeClause
#synth Repr NPComplete.SAT.ThreeCNF
#synth Repr NPComplete.BoundedWhile.Expr
#synth Repr NPComplete.BoundedWhile.Program

structure FourLiterals where
  first : NPComplete.SAT.Literal
  second : NPComplete.SAT.Literal
  third : NPComplete.SAT.Literal
  fourth : NPComplete.SAT.Literal
  deriving DecidableEq, Repr

#synth DecidableEq FourLiterals
#synth Repr FourLiterals

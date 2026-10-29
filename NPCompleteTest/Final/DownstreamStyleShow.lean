module

import NPComplete

/-!
# `show` / `change` checks for a structural definition's `.seq` case

`show ProgramBoundedIn B σ (.assign ...) ∧ ProgramBoundedIn B (...eval σ) ...` unfolds
`ProgramBoundedIn` on `.seq` by defeq. Plain `import`: ProgramBoundedIn is a structural def with an
exposed body, so this is expected ok.
-/

open NPComplete.BoundedWhile NPComplete.RAMToTM

example (B : Nat) (σ : Store) (a b : Nat) (e : Expr)
    (h1 : ProgramBoundedIn B σ (.assign a (.const 0)))
    (h2 : ProgramBoundedIn B ((Program.assign a (Expr.const 0)).eval σ) (.assign b e)) :
    ProgramBoundedIn B σ (.seq (.assign a (.const 0)) (.assign b e)) := by
  show ProgramBoundedIn B σ (.assign a (.const 0)) ∧
    ProgramBoundedIn B ((Program.assign a (Expr.const 0)).eval σ) (.assign b e)
  exact ⟨h1, h2⟩

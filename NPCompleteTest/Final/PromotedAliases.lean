module

public import NPComplete

/-!
The compatibility names must resolve to the promoted declarations even when both namespaces are
open; otherwise a source-compatible promotion introduces ambiguous unqualified references.
-/

@[expose] public section

section Loop
open NPComplete.BoundedWhile NPComplete.RAMToTM

example (body : Program) (σ : Store) : loopEval body 1 σ = body.eval σ := by
  exact loopEval_one body σ

example (body : Program) (a b : ℕ) (σ : Store) :
    loopEval body (a + b) σ = loopEval body b (loopEval body a σ) := by
  rw [loopEval_add]

example (body : Program) (σ : Store) : loopEval body 1 σ = body.eval σ := by
  exact NPComplete.RAMToTM.loopEval_one body σ

example (body : Program) (a b : ℕ) (σ : Store) :
    loopEval body (a + b) σ = loopEval body b (loopEval body a σ) := by
  exact NPComplete.RAMToTM.loopEval_add body a b σ
end Loop

section Store
open NPComplete.BoundedWhile NPComplete.CookLevin NPComplete.RAMToTM

example {B : ℕ} (σ : Store) (p : Program) (hB : 1 ≤ B) (hσ : StoreValuesLe B σ)
    (hp : ProgramBoundedIn B σ p) (hsf : ScanFree p) : StoreValuesLe B (p.eval σ) := by
  exact program_eval_storeValuesLe σ p hB hσ hp hsf

example {B : ℕ} (σ : Store) (p : Program) (hB : 1 ≤ B) (hσ : StoreValuesLe B σ)
    (hp : ProgramBoundedIn B σ p) (hsf : ScanFree p) : StoreValuesLe B (p.eval σ) := by
  exact NPComplete.CookLevin.program_eval_storeValuesLe σ p hB hσ hp hsf
end Store

section Unary
open NPComplete.BoundedWhile NPComplete.CookLevin NPComplete.RAMToTM

example (c k d : ℕ) (e : Expr) : ScanFree (decodeUnaryProgAt c k d e) := by
  exact scanFree_decodeUnaryProgAt c k d e

example (c k d : ℕ) (e : Expr) : ScanFree (decodeUnaryProgAt c k d e) := by
  exact NPComplete.CookLevin.scanFree_decodeUnaryProgAt c k d e
end Unary

section Encoding
open NPComplete.CookLevin NPComplete.SAT

example (l : Literal) : ∃ xs, encodeLiteral l = xs ++ [true] := by
  exact encodeLiteral_ends_true l

example (l : Literal) : ∃ xs, encodeLiteral l = xs ++ [true] := by
  exact NPComplete.CookLevin.encodeLiteral_ends_true l
end Encoding

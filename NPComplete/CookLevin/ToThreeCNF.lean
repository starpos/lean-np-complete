module

public import NPComplete.CookLevin.ToThreeCNF.Basic
public import NPComplete.CookLevin.ToThreeCNF.Rewrite
public import NPComplete.CookLevin.ToThreeCNF.Encode
public import NPComplete.CookLevin.ToThreeCNF.Writer
public import NPComplete.CookLevin.ToThreeCNF.SplitTailRel
public import NPComplete.CookLevin.ToThreeCNF.SplitTailDone
public import NPComplete.CookLevin.ToThreeCNF.SplitTailFrame
public import NPComplete.CookLevin.ToThreeCNF.SplitTailIntermediate
public import NPComplete.CookLevin.ToThreeCNF.LongSafety
public import NPComplete.CookLevin.ToThreeCNF.LongLoop
public import NPComplete.CookLevin.ToThreeCNF.LongClause
public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitProg
public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitShapeEval
public import NPComplete.CookLevin.ToThreeCNF.ClauseEmitShapeFrame
public import NPComplete.CookLevin.ToThreeCNF.CNFEmitRel
public import NPComplete.CookLevin.ToThreeCNF.CNFEmitStep
public import NPComplete.CookLevin.ToThreeCNF.CNFEmitLong
public import NPComplete.CookLevin.ToThreeCNF.CNFEmitCons
public import NPComplete.CookLevin.ToThreeCNF.Abi

/-!
# SAT to three-CNF

Cook-Levin tableaux produce clauses of unrestricted width, while the hardness statement uses the
`ValidThreeCNF` encoding. This umbrella gathers the width reduction, its witness-preserving encoding,
and the output-program layers into one conversion pipeline.
-/

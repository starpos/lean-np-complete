module

public import NPComplete.CookLevin.NatParser.Foundation
public import NPComplete.CookLevin.NatParser.Stats
public import NPComplete.CookLevin.NatParser.LengthPrefix
public import NPComplete.CookLevin.NatParser.LengthEval
public import NPComplete.CookLevin.NatParser.CNFStepEval
public import NPComplete.CookLevin.NatParser.CNFLoopEval
public import NPComplete.CookLevin.NatParser.CNFClauseStep

/-!
# A reusable unary length parser

This module exposes the RAM primitive used by the 3-SAT pipeline for the actual
`encodeNat`/`encodeList` representation.  The parser reads `false` cells until the
first `true` terminator, leaves the input window unchanged, and advances a cursor
past the terminator.  The controls are required to be below the input window; this
is the separation invariant used by the compiled RAM programs as well.
-/

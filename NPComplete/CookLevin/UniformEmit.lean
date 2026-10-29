module

public import NPComplete.CookLevin.UniformEmit.SplitTailScratch
public import NPComplete.CookLevin.UniformEmit.SplitTailProgram
public import NPComplete.CookLevin.UniformEmit.SplitTailTransport
public import NPComplete.CookLevin.UniformEmit.Dispatch
public import NPComplete.CookLevin.UniformEmit.TopLevel
public import NPComplete.CookLevin.UniformEmit.ClauseTransport
public import NPComplete.CookLevin.UniformEmit.StartupTransport
public import NPComplete.CookLevin.UniformEmit.CNFEmitHead
public import NPComplete.CookLevin.UniformEmit.CNFEmitLoop
public import NPComplete.CookLevin.UniformEmit.DecodeBounds
public import NPComplete.CookLevin.UniformEmit.LowRegisterBounds
public import NPComplete.CookLevin.UniformEmit.LayoutBounds
public import NPComplete.CookLevin.UniformEmit.StartupState
public import NPComplete.CookLevin.UniformEmit.ProducerRelation
public import NPComplete.CookLevin.UniformEmit.Producer
public import NPComplete.CookLevin.UniformEmit.Final

/-!
# Input-independent CNF emitter

`splitTailEmitProg` bakes `.const (tailBound + 1)` into the AST, and the second-pass
rewind uses `decodeNatProgram` with a compile-time unary bound.  The input-independent
producer expresses both bounds with registers and `Expr` values, so a single `Program` serves
every CNF.  Its first pass relocates the input window, zeroes the control registers, and scans the
encoding with `decodeCNFProgramAtSeen`, whose unary bound is read from a register at loop entry
and which also records whether any clause is nonempty.
-/

module

public import NPComplete.CookLevin.Generate.Steps
public import NPComplete.CookLevin.Generate.EncodeLength
public import NPComplete.CookLevin.Generate.ExecCompiler
public import NPComplete.CookLevin.Generate.VerifierCNF
public import NPComplete.CookLevin.Generate.CompactLayout
public import NPComplete.CookLevin.Generate.VarMapBridge
public import NPComplete.CookLevin.Generate.ExecMapSAT
public import NPComplete.CookLevin.Generate.ClauseShape
public import NPComplete.CookLevin.Generate.BoundedSAT
public import NPComplete.CookLevin.Generate.BoundedSATWindow
public import NPComplete.CookLevin.Generate.BoundedMap
public import NPComplete.CookLevin.Generate.VerifierExact

/-!
The semantic tableau is not a TM0 program. Hardness needs a poly-size
3CNF whose encoding is the same map used by the TM2-level hypothesis that 3SAT is not
promise-poly-decidable, plus a precise
computability surface for that generator.
-/

module

public import NPComplete.CookLevin.OutputWriter.Basic
public import NPComplete.CookLevin.OutputWriter.SecondPass
public import NPComplete.CookLevin.OutputWriter.Literal
public import NPComplete.CookLevin.OutputWriter.SplitTailLink
public import NPComplete.CookLevin.OutputWriter.Clause

/-!
# Verified output-buffer writers

This file packages the dynamic-cursor emitters from `CanonicalStoreFinalize` as a small
append interface.  Cell `0` contains the workspace limit `M`, the output cursor is stored at
`M + curJ`, and the bits in the interval `[start, cursor)` are the already emitted prefix.
The strict workspace bound keeps the output interval disjoint from the dynamic control cells;
callers may place their input below `start` or above `M + tmpJ`.
-/

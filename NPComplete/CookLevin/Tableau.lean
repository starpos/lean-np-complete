module

public import NPComplete.CookLevin.Tableau.VarNumbering
public import NPComplete.CookLevin.Tableau.Layout
public import NPComplete.CookLevin.Tableau.Alphabet
public import NPComplete.CookLevin.Tableau.ClauseBuilders
public import NPComplete.CookLevin.Tableau.InitialSnapshot
public import NPComplete.CookLevin.Tableau.ClauseFamilies
public import NPComplete.CookLevin.Tableau.FreeSuffix
public import NPComplete.CookLevin.Tableau.SATImplication
public import NPComplete.CookLevin.Tableau.RunSnapshot
public import NPComplete.CookLevin.Tableau.RunCorrectness
public import NPComplete.CookLevin.Tableau.RunBounds
public import NPComplete.CookLevin.Tableau.CellEvolution
public import NPComplete.CookLevin.Tableau.NextIndex
public import NPComplete.CookLevin.Tableau.TransOneWitness
public import NPComplete.CookLevin.Tableau.RunAdvance
public import NPComplete.CookLevin.Tableau.Persistence
public import NPComplete.CookLevin.Tableau.SATRun
public import NPComplete.CookLevin.Tableau.StepsToBridge
public import NPComplete.CookLevin.Tableau.TapeEquality
public import NPComplete.CookLevin.Tableau.Forward

/-!
The NP-hardness kernel is a local constraint system for one bounded
TM0 run. Satisfiability must mean that the machine produces the Boolean
accept tape in the allotted time. A poly-time generator and the SAT→3CNF
step are a later reduction, not part of this constraint system.
-/

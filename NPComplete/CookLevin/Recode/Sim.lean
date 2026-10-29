module

public import NPComplete.CookLevin.Recode.Sim.Foundation
public import NPComplete.CookLevin.Recode.Sim.Machine
public import NPComplete.CookLevin.Recode.Sim.CleanMachine
public import NPComplete.CookLevin.Recode.Sim.Support
public import NPComplete.CookLevin.Recode.Sim.Time
public import NPComplete.CookLevin.Recode.Sim.BlockEncoding
public import NPComplete.CookLevin.Recode.Sim.TapeRelations
public import NPComplete.CookLevin.Recode.Sim.CleanMicrosteps
public import NPComplete.CookLevin.Recode.Sim.CleanPhases
public import NPComplete.CookLevin.Recode.Sim.CleanBoundary
public import NPComplete.CookLevin.Recode.Sim.CleanPartialMacros
public import NPComplete.CookLevin.Recode.Sim.CleanMoves
public import NPComplete.CookLevin.Recode.Sim.CleanStatement
public import NPComplete.CookLevin.Recode.Sim.CleanContent
public import NPComplete.CookLevin.Recode.Sim.CleanOccupied
public import NPComplete.CookLevin.Recode.Sim.Reachability
public import NPComplete.CookLevin.Recode.Sim.InputEncoding
public import NPComplete.CookLevin.Recode.Sim.Certificate
public import NPComplete.CookLevin.Recode.Sim.Initial
public import NPComplete.CookLevin.Recode.Sim.Computable

/-!
The reduction uses a Boolean tape, while simulated machines have a finite
alphabet. This module re-exports the fixed-width block simulation over
`Option Bool`, including clean and raw step and macro proofs, reachability, input
and certificate encodings, initialization, and computability.
-/

module

public import NPComplete.CookLevin.UniformPackaging.OutputBounds
public import NPComplete.CookLevin.UniformPackaging.Reverse
public import NPComplete.CookLevin.UniformPackaging.Envelopes
public import NPComplete.CookLevin.UniformPackaging.WriterRawBounds
public import NPComplete.CookLevin.UniformPackaging.EmitStateBounds
public import NPComplete.CookLevin.UniformPackaging.SplitTailTmp
public import NPComplete.CookLevin.UniformPackaging.DispatchTmp
public import NPComplete.CookLevin.UniformPackaging.OuterLoopBounds
public import NPComplete.CookLevin.UniformPackaging.ReverseBounds
public import NPComplete.CookLevin.UniformPackaging.DecoderBounds
public import NPComplete.CookLevin.UniformPackaging.SplitTailReachability
public import NPComplete.CookLevin.UniformPackaging.SplitTailTerminalBounds
public import NPComplete.CookLevin.UniformPackaging.SplitTailCertificates
public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailBounds
public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailStore
public import NPComplete.CookLevin.UniformPackaging.UniformSplitTailReachability
public import NPComplete.CookLevin.UniformPackaging.DispatchShortBounds
public import NPComplete.CookLevin.UniformPackaging.DispatchLongBounds
public import NPComplete.CookLevin.UniformPackaging.DispatchAssembly
public import NPComplete.CookLevin.UniformPackaging.OuterAccounting
public import NPComplete.CookLevin.UniformPackaging.ClauseFrame
public import NPComplete.CookLevin.UniformPackaging.IterationFrame
public import NPComplete.CookLevin.UniformPackaging.StartupBounds
public import NPComplete.CookLevin.UniformPackaging.OuterZero
public import NPComplete.CookLevin.UniformPackaging.ProducerProgram
public import NPComplete.CookLevin.UniformPackaging.DecodeOuterBounds
public import NPComplete.CookLevin.UniformPackaging.ProducerSetupBounds
public import NPComplete.CookLevin.UniformPackaging.CostAndOperands

/-!
# Uniform producer packaging

Semantic correctness of the SAT-to-3CNF producer belongs to `UniformEmit`, but a polynomial-time
reduction also needs a machine-level output contract and resource bounds. This umbrella groups the
bridge from the forward writer to the TM2 reduction interface, keeping ABI and cost accounting
separate from emitter correctness.
-/

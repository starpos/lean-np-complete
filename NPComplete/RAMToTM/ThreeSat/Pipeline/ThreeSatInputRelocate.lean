module

public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.RAMToTM.Generic.Relocate
public import NPComplete.RAMToTM.ThreeSat.Pipeline.ThreeSatRuntimeCore

/-!
# 3-SAT input relocation compatibility

This module keeps the established import path available to 3-SAT clients while the input
relocation contract and implementation live in the generic RAM-to-TM layer.
-/

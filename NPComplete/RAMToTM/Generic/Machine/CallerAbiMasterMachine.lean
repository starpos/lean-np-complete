module

public import NPComplete.RAMToTM.Generic.Machine.CallerAbiMasterRam

/-!
# Caller ABI master machine

The generic master machine accepts a program and its ABI slots as separate
arguments, so callers otherwise repeat that wiring. This module fixes the four
ABI registers and defines the corresponding finite machine, with lemmas exposing
its initial configuration and step relation.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.RAMToTM.Generic
open NPComplete.BitEncoding (Bits)

/-- Master FinTM2 on `abiProgram`, with ABI registers fixed at `abiBase..abiBase+3`. -/
@[reducible] noncomputable def masterMachineAbi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) : Turing.FinTM2 where
  K := Generic.EmitK (abiProgram d.p d.outReg)
  k₀ := Generic.EmitK.base Generic.Kg.io
  k₁ := Generic.EmitK.out
  Γ := Generic.EmitΓ (abiProgram d.p d.outReg)
  Λ := Generic.MasterΛ (abiProgram d.p d.outReg)
  main := Generic.MasterΛ.ram (Generic.Λg.prologue .scanInput)
  σ := Generic.MasterState (abiProgram d.p d.outReg)
  initialState := Generic.MasterState.canonical
  m := Generic.masterProg (programSupported_any _)
    (masterOutRegAbi d.p d.outReg)
    (abiAddrReg d.p d.outReg) (abiDestReg d.p d.outReg)
    (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg)

/-- `initList` on `masterMachineAbi`, unfolded to its `MasterΛ`/`MasterState`/stack components. -/
lemma initList_masterMachineAbi {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) (bits : Bits) :
    Turing.initList (masterMachineAbi d) bits =
      ⟨some (Generic.MasterΛ.ram (Generic.Λg.prologue .scanInput)), Generic.MasterState.canonical,
        Generic.initialMasterSg (Generic.initialSg (abiProgram d.p d.outReg) bits)⟩ := by
  have hl : (Turing.initList (masterMachineAbi d) bits).l =
      some (Generic.MasterΛ.ram (Generic.Λg.prologue .scanInput)) := rfl
  have hvar : (Turing.initList (masterMachineAbi d) bits).var =
      Generic.MasterState.canonical := rfl
  have hstk : (Turing.initList (masterMachineAbi d) bits).stk =
      Generic.initialMasterSg (Generic.initialSg (abiProgram d.p d.outReg) bits) := by
    funext k
    cases k with
    | base k' => cases k' <;> simp [Turing.initList, masterMachineAbi, Generic.initialMasterSg,
        Generic.initialSg]
    | out => simp [Turing.initList, masterMachineAbi, Generic.initialMasterSg]
    | countdown => simp [Turing.initList, masterMachineAbi, Generic.initialMasterSg]
  rw [show Turing.initList (masterMachineAbi d) bits =
      ⟨(Turing.initList (masterMachineAbi d) bits).l,
        (Turing.initList (masterMachineAbi d) bits).var,
        (Turing.initList (masterMachineAbi d) bits).stk⟩ from rfl,
    hl, hvar, hstk]

lemma masterMachineAbi_step {α : Type} {enc : α → Bits} {D L : α → Prop}
    (d : BoundedWhileDecider enc D L) :
    flip Bind.bind (masterMachineAbi d).step =
      master_flipBind (programSupported_any (abiProgram d.p d.outReg))
        (masterOutRegAbi d.p d.outReg) (abiAddrReg d.p d.outReg)
        (abiDestReg d.p d.outReg) (abiOneReg d.p d.outReg) (abiLenReg d.p d.outReg) := rfl

end NPComplete.RAMToTM

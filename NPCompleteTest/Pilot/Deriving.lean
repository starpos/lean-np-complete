module

import NPCompleteTest.Pilot.DerivExpose
import NPCompleteTest.Pilot.DerivPublicOnly
import NPComplete.SAT.ThreeSAT
import NPComplete.BitCostRAM

/-!
# `deriving DecidableEq` seen through a plain `import`

Expected: inside `@[expose] public section` every shape (enum inductive, structure,
recursive inductive) decides; inside a bare `public section` only the enum inductive decides,
the structure and the recursive inductive FAIL. Library types: `Literal` (ThreeSAT) and
`Instruction` (BitCostRAM) are in exposed sections, so they decide.
-/

open NPCompleteTest.Pilot

-- expose section: expected ok
example : DerivExpose.C.r ≠ DerivExpose.C.g := by decide
example : (⟨1, .r⟩ : DerivExpose.S) ≠ ⟨1, .g⟩ := by decide
example : DerivExpose.T.node (.leaf 1) (.leaf 2) ≠ .leaf 1 := by decide
example : (⟨1, .r⟩ : DerivExpose.S) ≠ ⟨1, .g⟩ := by decide +kernel
-- public section only: enum ok, structure and recursive inductive expected FAIL
example : DerivPublicOnly.C.r ≠ DerivPublicOnly.C.g := by decide
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : (⟨1, .r⟩ : DerivPublicOnly.S) ≠ ⟨1, .g⟩ := by decide
/-- Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : DerivPublicOnly.T.node (.leaf 1) (.leaf 2) ≠ .leaf 1 := by decide
-- library types: expected ok
open NPComplete.SAT NPComplete.BitCostRAM in
example : Literal.pos 1 ≠ Literal.neg 1 := by decide
open NPComplete.SAT NPComplete.BitCostRAM in
example : Literal.pos 1 = Literal.pos 1 := by decide +kernel
open NPComplete.SAT NPComplete.BitCostRAM in
example : Instruction.halt ≠ Instruction.jump 0 := by decide
open NPComplete.SAT NPComplete.BitCostRAM in
example : Instruction.loadImm 1 2 = Instruction.loadImm 1 2 := by decide +kernel

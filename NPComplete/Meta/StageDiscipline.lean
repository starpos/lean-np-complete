module

public meta import Lean.Attributes
import Lean.Attributes

/-!
# Classification tags for the stage discipline

A construction built from stage contracts keeps its maintenance cost low only if register numbers,
concrete stores and program internals stay in the places that own them.  Every declaration of a
checked scope therefore carries one of three tags, and `#check_stage_discipline` (in
`StageDisciplineCheck.lean`) enforces what each class may mention:

* `stage_layout`: the layout vocabulary (role type, register placement, accessors and the
  lemmas about concrete values).  This is the one place where register numbers are written.
* `stage_impl`: program definitions, their evaluation formulas and the proofs of stage contracts.
  Raw stores, `writeReg` and evaluation lemmas are used here.
* `stage_contract`: the published contract of an implementation.  Its statement is held to the
  boundary rules, while its proof may use the implementation freely.
* `stage_boundary`: facts, programs written against a layout and compositions of contracts.  They
  never mention register numbers, concrete stores or implementation internals.

`stage_adapter` marks a library entry that imports a raw program and its proof into a bundled
stage.  Only an implementation declaration may use it.

This module imports only `Lean.Attributes` so that any module may import it to classify its
declarations; the checker lives in `StageDisciplineCheck.lean`.
-/

open Lean

public section

namespace NPComplete.StageDiscipline

initialize stageLayoutAttr : TagAttribute ←
  registerTagAttribute `stage_layout
    "Layout vocabulary of a stage construction: register placement, accessors and their concrete values."

initialize stageImplAttr : TagAttribute ←
  registerTagAttribute `stage_impl
    "Implementation of a stage: program definitions, evaluation formulas, proofs of stage contracts."

initialize stageContractAttr : TagAttribute ←
  registerTagAttribute `stage_contract
    "Published contract of a stage implementation: the statement obeys the boundary rules, the proof is free."

initialize stageBoundaryAttr : TagAttribute ←
  registerTagAttribute `stage_boundary
    "Boundary or composition of stages: facts, contract statements and compositions, free of register numbers and internals."

initialize stageAdapterAttr : TagAttribute ←
  registerTagAttribute `stage_adapter
    "Entry that imports a raw program and its proof into a bundled stage; usable only from `stage_impl` declarations."

end NPComplete.StageDiscipline

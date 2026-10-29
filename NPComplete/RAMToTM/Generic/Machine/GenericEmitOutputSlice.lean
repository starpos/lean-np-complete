module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmit

/-!
# `OutputSlice`: the write-log region convention `emit_run_length_bounded` streams out

`GenericEmit.emit_run_length_bounded`'s conclusion is stated against its own internal recursion
`bitsFor log addr rest0` (a `List Unit`-length-indexed accumulator matching the loop's own
`checkMore`/`countdown` structure). Callers *producing* the write-log region (which a later RAM
computation is expected to fill in) think in terms of a `(base, length)` descriptor and a plain
index `i ↦ bit at base + i`, not a recursive marker list. `OutputSlice` packages only that
descriptor; the bitness precondition required by `emit_run_length_bounded` remains a separate
hypothesis. `physicalBits_eq_range` bridges the two representations, so the
`(List.range length).map` view and the `bitsFor`-shaped `emit_run_length_bounded` guarantee
provably agree.

`OutputSlice` is a pure naming and bridging layer: prep's `EmitPrepPhase` and emit's `EmitPhase`
are distinct local machines and only become one machine through the master dispatcher. This file
does not state an output-length polynomial bound, because the concrete polynomial depends on the
reduction algorithm that supplies the slice.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.RAMToTM (WriteLog lookupD)

/-- A caller-chosen write-log region `[base, base + length)`, the unit `emit_run_length_bounded`
    (`GenericEmit.lean`) streams onto `EmitK.out` once `length` many `countdown` markers are in
    place (via `GenericEmitPrep.prep_run_length_bounded`). -/
structure OutputSlice where
  base : ℕ
  length : ℕ

/-- The `Bool` sequence `o` names, in the order `emit_run_length_bounded` reads it (`base`,
    `base + 1`, ...): `bitsFor` applied to a length-`o.length` marker list, i.e.
    `emit_run_length_bounded`'s own termination value verbatim (`Sgf EmitK.out = (o.physicalBits log).reverse ++ Sg0 EmitK.out`
    once `rest0 := List.replicate o.length ()`) — this definition adds no new arithmetic, it just
    gives that existing quantity an ABI name. -/
def OutputSlice.physicalBits (log : WriteLog) (o : OutputSlice) : List Bool :=
  bitsFor log o.base (List.replicate o.length ())

/-- `bitsFor`'s recursion unfolds to the `(List.range length).map` closed form used to read the
    region — proved by induction on `length`,
    generalizing `base` (mirrors `emit_run_length_bounded`'s own `cons` case index-shift,
    `addr + (i+1) = addr + 1 + i`, but resolved into a closed form here rather than left as a bare recursion). -/
lemma bitsFor_eq_range (log : WriteLog) (base n : ℕ) :
    bitsFor log base (List.replicate n ())
      = (List.range n).map (fun i => decide (lookupD log (base + i) 0 = 1)) := by
  induction n generalizing base with
  | zero => simp [bitsFor]
  | succ n ih =>
    rw [List.replicate_succ]
    show decide (lookupD log base 0 = 1) :: bitsFor log (base + 1) (List.replicate n ())
      = (List.range (n + 1)).map (fun i => decide (lookupD log (base + i) 0 = 1))
    rw [ih (base + 1), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [show base + 1 + i = base + i.succ from by omega]

/-- `bitsFor_eq_range`'s `OutputSlice`-packaged form. -/
lemma physicalBits_eq_range (log : WriteLog) (o : OutputSlice) :
    o.physicalBits log
      = (List.range o.length).map (fun i => decide (lookupD log (o.base + i) 0 = 1)) :=
  bitsFor_eq_range log o.base o.length

end NPComplete.RAMToTM.Generic

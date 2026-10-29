module

public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.BoundedWhile.WritesIn

/-!
# Write footprint: a bounded program never writes above its bound

Matching the finalize phase's store against the canonical loader `bitInputStore outputBits` is a
`funext` obligation over *every* address, not just the output region: cells above the loader's
input end must read `0`, and `bitInputStore_eq_zero_of_ge_inputEnd` gives exactly that for the
loader's own initial store. What is still missing is that a program run from that store leaves
every cell above some bound `B` untouched, so it never overwrites those zeros with something else.

`ProgramBoundedIn` (`CompileExecBounded.lean`) already tracks both the value bound and the
write-address bound of every assignment.  It was built for bounding compiled operands; the
write-address half is a `WritesIn (· ≤ B)` certificate, and `WritesIn.eval_frame` turns that
into the footprint equation, so this file does not re-induct on program structure.  Its
`scanList`/`lookup` cases are `True` (unconstrained), which would make the write-footprint claim
false for them; `ScanFree` excludes exactly those two constructors, matching every construct
needed by the bounded programs considered here.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile (Program Store WritesIn)
open NPComplete.BitEncoding (Bits)

/-- `ScanFree` and `ProgramBoundedIn B` together say every address written is `≤ B`.
    `ifNZ` contributes only the branch taken; `forN` reuses the visited-store obligations
    `ProgramBoundedIn` already records. `scanList`/`lookup` are excluded by `ScanFree`. -/
lemma writesIn_of_programBoundedIn (B : ℕ) :
    ∀ (p : Program) (σ : Store), ScanFree p → ProgramBoundedIn B σ p →
      WritesIn (fun a => a ≤ B) p σ := by
  intro p
  induction p with
  | skip => intro _ _ _; trivial
  | assign r _ => intro _ _ hp; exact hp.1
  | assignInd _ _ => intro _ _ hp; exact hp.2.2
  | seq _ _ ih1 ih2 =>
    intro σ hsf hp
    exact ⟨ih1 σ hsf.1 hp.1, ih2 _ hsf.2 hp.2⟩
  | ifNZ _ _ _ iht ihf =>
    intro σ hsf hp
    simp only [WritesIn]; split
    · exact iht σ hsf.1 hp.2.1
    · exact ihf σ hsf.2 hp.2.2
  | forN _ _ ih =>
    intro σ hsf hp m hm
    exact ih _ hsf (hp.2 m hm)
  | scanList _ _ _ => intro _ hsf; exact hsf.elim
  | lookup _ _ _ => intro _ hsf; exact hsf.elim

/-- A `ScanFree`, `ProgramBoundedIn B`-compliant program never writes to any cell above `B`:
    such a cell reads the same value before and after running the program. `scanList`/`lookup`
    are excluded by `ScanFree` since `ProgramBoundedIn` leaves their write targets unconstrained
    (`True`), which would make the claim false for them. -/
lemma eval_eq_of_gt_of_programBoundedIn (B : ℕ) :
    ∀ (p : Program) (σ : Store), ScanFree p → ProgramBoundedIn B σ p →
      ∀ r, B < r → (p.eval σ) r = σ r := by
  intro p σ hsf hp r hr
  exact WritesIn.eval_frame p σ (writesIn_of_programBoundedIn B p σ hsf hp)
    (fun hle => by omega)

/-- Convenience corollary for the canonical loader: any `ScanFree`, `B`-bounded program run from
    `bitInputStore bits` reads exactly `0` (the loader's own value) at every cell above `B`. -/
lemma eval_eq_zero_of_gt (B : ℕ) (p : Program) (bits : Bits) (hB : bits.length ≤ B)
    (hsf : ScanFree p) (hb : ProgramBoundedIn B (bitInputStore bits) p) :
    ∀ r, B < r → (p.eval (bitInputStore bits)) r = 0 := by
  intro r hr
  rw [eval_eq_of_gt_of_programBoundedIn B p (bitInputStore bits) hsf hb r hr]
  exact bitInputStore_eq_zero_of_ge_inputEnd bits r (by omega)

end NPComplete.RAMToTM

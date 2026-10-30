# NPComplete

## 1. Overview

`NPComplete` is a Lean 4 library that formalizes complexity classes, polynomial-time reductions,
and the NP-completeness of SAT/3SAT (Cook-Levin). It provides a TM0 class API for proving
`InNP` / `NPHard` for new encoded languages, and a construction API based on BoundedWhile, RAM,
and TM2.

### 1.1 Requirements and building

The Lake package name is `np-complete` (version `0.4.0`). It is built with Lean `v4.35.0` and
depends only on Mathlib `v4.35.0` (`lakefile.toml`).

Install [elan](https://github.com/leanprover/elan), Lean's toolchain manager; the `lean-toolchain`
file selects the required Lean version. Then:

```sh
git clone https://github.com/starpos/lean-np-complete.git
cd lean-np-complete
lake exe cache get
lake build
```

`lake exe cache get` downloads prebuilt Mathlib files. Skipping it still works, because
`lake build` compiles Mathlib from source, but that takes much longer.

The committed `lake-manifest.json` records the dependency revisions this library is built and tested
with. Do not run `lake update` as part of routine setup: it re-resolves the dependencies and may
change the manifest.

`lake build` builds the `NPComplete` library (the default target). Section 7 lists the full set of
checks.

### 1.2 Using the library from another package

Add it to the `lakefile.toml` of your package. The Lake package name is `np-complete`. Pin `rev` to
a release tag (here `v0.4.0`) for reproducible builds:

```toml
[[require]]
name = "np-complete"
git = "https://github.com/starpos/lean-np-complete.git"
rev = "v0.4.0"
```

The equivalent `lakefile.lean` entry is:

```lean
require «np-complete» from git
  "https://github.com/starpos/lean-np-complete.git" @ "v0.4.0"
```

Then run `lake update np-complete` and `import NPComplete` in your modules. Running `lake exe cache
get` in your package afterwards fetches the prebuilt Mathlib files. Your package should use the same
Lean toolchain as this library (`lean-toolchain`, currently `v4.35.0`) and, if it also requires
Mathlib directly, the same Mathlib revision (currently `v4.35.0`), because a Lake workspace uses one
revision of each package.

### 1.3 Relationship to CSLib

`NPComplete` is an independent formalization. It builds on Mathlib's Turing-machine models (TM0 and
TM2), with its own definition of polynomial-time computability for TM0 and its own RAM-based
development. As of October 2026 ([CSLib commit
`6ff325e870`](https://github.com/leanprover/cslib/tree/6ff325e870)),
[CSLib](https://github.com/leanprover/cslib) formalizes time and space bounds for Turing machines
but not yet complexity classes such as P and NP, polynomial-time reductions, or the Cook-Levin
theorem. This library is published in the meantime. If CSLib comes to provide these notions, we will
consider migrating to them or providing a bridge; there is no timeline. Statements in this library
follow the compatibility policy of Section 6.

## 2. Main theorems and namespaces

The main Cook-Levin declarations are in `NPComplete.CookLevin`.

| Declaration | Statement |
| --- | --- |
| `sat_NPHard`, `sat_NPComplete` | SAT over CNF is NP-hard / NP-complete |
| `threeSAT_NPHard`, `threeSAT_NPComplete` | 3SAT over valid 3CNF is NP-hard / NP-complete |
| `sat_inNP`, `threeSAT_inNP` | SAT / 3SAT are in NP |
| `p_ne_np_implies_h3sat` | Under `PneNP`, 3SAT has no polynomial-time TM2 promise decider |
| `sat_InP_implies_PeqNP` | If SAT is `InP`, then `PeqNP` |
| `threeSAT_InP_implies_PeqNP` | If 3SAT is `InP`, then `PeqNP` |

`NPHard` / `NPComplete` are TM0 classes. The 3SAT types and predicates `ThreeCNF` / `ThreeSAT` /
`ValidThreeCNF` are in `NPComplete.SAT` (`NPComplete/SAT/ThreeSAT.lean`), and so is
`NPComplete.SAT.ValidThreeCNF.encode`. RAMToTM is in `NPComplete.RAMToTM`, the BoundedWhile DSL
in `NPComplete.BoundedWhile`, and the bit-cost RAM in `NPComplete.BitCostRAM`. Every declaration
owned by this library is under `NPComplete.*`.

```lean
import NPComplete

open NPComplete.CookLevin
open NPComplete.SAT (ThreeSAT ValidThreeCNF)
```

`p_ne_np_implies_h3sat` is a cross-model corollary: it connects a polynomial-time TM2 Boolean
decider to TM0 via
`TM2ComputableInPolyTime.toTM0`, with no extra decoder proof. Read it separately from the TM0
class theorems.

## 3. Computation model and encodings

- `Bits` is `List Bool`. `encodeNat n = false^n ++ [true]` is unary and has length `n + 1`.
  `encodeList` concatenates the element count and the encoded elements.
- CNF is encoded by `encodeLiteral` → `encodeClause` → `encodeCNF`; valid 3CNF by
  `encodeThreeClause` / `encodeThreeCNF` (the three 3CNF encoders are in `NPComplete.SAT.*`).
- The encoding is the measure of complexity itself: time polynomials are in the encoded input
  length `length (enc x)`. Integers are unary, so the guarantees do not carry over to binary
  encodings. Decision guarantees hold on inputs of the given encoded type.
- `InP enc L` is a deterministic polynomial-time TM0 decider with `encodeBool` output, together
  with its correctness.
- `InNP enc L` is a polynomial-length certificate and a deterministic polynomial-time TM0
  verifier on `pairBits (enc x) w`.
- `enc` is not required to be injective. A machine reads only `enc x` from the tape, so if
  `InP enc L` or `InNP enc L` holds and `enc x = enc y`, then `L x ↔ L y`
  (`InP.respects_enc`, `InNP.respects_enc`). Read such a language as a language on the
  equivalence classes of `enc`. The encoders `encodeNat`, `encodeList` (for element encoders
  that decode uniquely from a prefix) and `ValidThreeCNF.encode` are injective
  (`encodeNat_injective`, `encodeList_injective`, `ValidThreeCNF.encode_injective`).
- `NPHard eb L` means that every TM0 `InNP` language has a `PolyTimeReduction` to `L`.
  `NPComplete eb L := InNP eb L ∧ NPHard eb L`.
- `PolyTimeReduction` consists of a polynomial-time TM0-computable map and
  `Lα x ↔ Lβ (map x)`. Reductions
  compose with `PolyTimeReduction.trans`.
- `TM0ComputableInPolyTime` is a finite-alphabet TM0 with a step bound polynomial in the encoded
  input length. `InNP`, `NPHard`, and `PolyTimeReduction` are the TM0 versions.

## 4. Proving results for a new language

### 4.1 `InNP`

1. Choose an encoding `enc`, a polynomial `p` bounding certificate length, and a Boolean
   verifier `V x w`.
2. Prove the correctness equivalence
   `L x ↔ ∃ w, w.length ≤ p.eval (enc x).length ∧ V x w = true`.
3. If you have a polynomial-time TM2 Boolean computation on `pairBits (enc x) w`, connect it to
   TM0 with
   `TM2ComputableInPolyTime.toTM0`. When the output is `encodeBool`, the decoder is built in and
   no extra decoder proof is needed.
4. Wrap the machine evidence for `InNP` as `Nonempty (TM0ComputableInPolyTime ...)`.
   Existing examples are `sat_inNP` and `threeSAT_inNP`.

For a BoundedWhile verifier, the paired input can be split up front with `pairPreludeProg`, then
composed with the verifier body as `pairPreludeProg.seq rest`. This contract starts from the
canonical store `bitInputStore (pairBits x w)`, where `x` is the encoded instance; it is not a
guarantee for an arbitrary initial store. `pairPreludeProg_runs` bundles the post-state contract
`PairPreludeSpec` with a `ProgramBoundedIn` resource bound of `pairPreludeBound` at the paired-input
length.

`PairPreludeSpec` puts the bases of `x` and `w` in registers 1 and 5, the instance length in
register 3, and the paired-input length in register 0. It makes each bit readable from the
corresponding base; the witness region is specified with `getD` through `max x.length w.length`,
so a shorter `w` is zero-filled. The contract guarantees `100 ≤ τ 5 < τ 1`: the witness base
(`τ 5`) is at least 100 and below the instance base (`τ 1`), leaving registers 0 through 99 free for
callers' own control band without colliding with either published region. These are workspace and
ordering guarantees, not a placement formula. The frame preserves each cell `r` with `5 < r ≤ input
length` and each cell above `pairPreludeBound`. The prelude uses registers 1–5, and cells above the
input length but at or below `pairPreludeBound` are not generally preserved. The SAT and 3SAT
verifier wirings are examples of this composition.

### 4.2 `NPHard`

1. Fix the target language `L` and its encoding `eb`.
2. Provide one TM0 `PolyTimeReduction` from 3SAT to `L`.
3. Pass it to `NPHard.of_threeSAT` (`NPComplete.of_threeSAT` also takes `InNP`).
   Internally it composes `threeSAT_NPHard` with `PolyTimeReduction.trans`, so users do not
   need to redo a Cook-Levin-style construction. For a reduction from another NP-hard language,
   use `NPHard.of_reduction`.
4. Usage looks like this:

```lean
import NPComplete

open NPComplete.CookLevin
open NPComplete.SAT (ThreeSAT)

lemma target_NPComplete {β : Type} (eb : β → List Bool) (L : β → Prop) (hL : InNP eb L)
    (r3toL : PolyTimeReduction
      NPComplete.SAT.ValidThreeCNF.encode eb
      (ThreeSAT ∘ Subtype.val) L) : NPComplete eb L :=
  NPComplete.of_threeSAT hL r3toL
```

## 5. Three API layers and high-level entry points

Declarations carry a layer attribute. Declarations without one are internal and have no
compatibility guarantee.

- **Stable (`@[stable_api]`)**: the statement is a compatibility promise. This layer contains
  the main theorems, the complexity classes (`InP` `InNP` `NPHard` `NPComplete`
  `PolyTimeReduction` `PeqNP` `PneNP`), hardness transfer (`NPHard.of_reduction`
  `NPHard.of_threeSAT` `NPComplete.of_threeSAT` `InP.of_reduction`), the TM2 decision entry
  (`PromisePolyDecidable` `promisePolyDecidable_to_InP`), encodings (`Bits` `encodeNat`
  `encodeList` `encodeBool`), the SAT/3SAT types, and the semantics of the BoundedWhile language
  (`Store` `Expr` `Program` `eval` `cost` `writeReg` with their equations and frame lemmas).
  Among the frame lemmas, the `Program.Avoids` / `AvoidsAbove` / `WritesAvoid` family is stable;
  the semantic `WritesIn` family, which handles store-dependent write targets, is construction
  API. The parameterized stride-address arithmetic (`arenaAddr`, `arenaAddr_eq`,
  `arenaAddr_ne`) is also stable; this does not stabilize any caller's choice of base, stride,
  or lanes. The main theorems, the SAT/3SAT types, and the hardness-transfer entry points
  `NPHard.of_threeSAT` and `NPComplete.of_threeSAT` listed above are stable by explicit decision,
  although they are specific to SAT/3SAT. For the other stable declarations, the criteria are: no
  dependence on a specific problem or memory layout, and no internal-layer types in the statement.
  This includes `BoundedWhile.loopEval_one` and `loopEval_add`, as well as the tagged `Repr`,
  `DecidableEq`, and `Inhabited` instances on stable types.
- **Construction API (`@[construction_api]`)**: usable, but may change. This layer contains
  `BoundedWhileDecider` (`.ofBounds` `.result` `.TMRealizable`),
  `tmRealizable_of_boundedWhileDecider`, `bitInputStore`, `CompiledOperandBound` and
  `compiledOperandBound_of_programBoundedIn` (with its hypothesis predicates `ProgramBoundedIn`
  `ScanFree` `StoreValuesLe`), `TM2ComputableInPolyTime.toTM0`,
  `TM0ComputableInPolyTime.congr_map` / `congr_enc`, the high-level entry points below, and the
  semantic `WritesIn` family (`WritesIn` `WritesIn.eval_frame` `WritesIn.mono` `WritesIn.ifNZ_of`
  `WritesIn.forN_of_inv` `WritesIn.forN_of_indexed` `WritesIn.scanList_of_inv`
  `Program.AvoidsAbove.writesIn` `loopEval_eq_of_writesIn` `scanListEval_eq_of_writesIn`).
  The pair-prelude contract (`pairPreludeProg`, `pairPreludeBound`, `PairPreludeSpec`,
  `ScanFree_pairPreludeProg`, `pairPreludeProg_runs`) for splitting BoundedWhile verifier inputs is
  also construction API. It guarantees `100 ≤ τ 5 < τ 1`: the witness base is at least 100 and
  below the instance base, leaving registers 0 through 99 free for caller control. This is a
  workspace and ordering guarantee, not a placement formula. Declarations whose types mention
  RAM-layer predicates, along with the `WritesIn` family, are not stable.
  The BitCostRAM types (`RAM` `Instruction` `Bank`) and `bitLen` `run` are also construction API,
  but only because the statement of `CompiledOperandBound` refers to them and the layer check
  requires it. Ordinary users do not need to handle `RAM` `Instruction` `Bank` `run` directly.
  `bitLen` appears only when writing an upper bound for an operand bound (for example, through
  `bitLen_le_succ` in the external usage example below).
- **Internal**: emitters, the ABI (`WriteLog` `OutputSlice` `ReductionOutput`), `depairProg` and
  its placement/layout constants, plus SAT-specific lemmas.

The classes are defined over TM0. TM2 decision (`PromisePolyDecidable`) is a compatibility
interface that yields `InP` for any `enc` / `L` via `promisePolyDecidable_to_InP` (only when the
promise is trivial).

### High-level entry points

Write a BoundedWhile program and prove its cost and operand bounds; no RAM-to-TM wiring is
needed.

- `InP.of_boundedWhileDecider` gives `InP ea L` from a decider with a trivial promise.
- `InNP.of_bounded_while_verifier` gives `InNP enc L` from a certificate bound and a decider on
  `pairBits (enc x) w`.
- `PolyTimeReduction.of_forwardBitProducer` builds a TM0 reduction from a program that leaves its
  output bits in the final store. `TM0ComputableInPolyTime.of_forwardBitProducer` gives the
  corresponding computability result before forming a reduction.
- `BoundedWhileDecider.ofBounds` defines the decided predicate from a producer's output, requiring
  only cost and operand-bound proofs.
- `NPHard.of_threeSAT` / `NPComplete.of_threeSAT` give hardness / completeness from a reduction
  from 3SAT (and `InNP` for completeness).

For constructing verifiers and reduction producers, these construction-layer tools help discharge
resource and store obligations:

- `RAMToTM.BoundedWhileDecider.ofProgramBoundedIn` builds a decider for a scan-free program from a
  polynomial value bound. `RAMToTM.exists_resources_of_programBoundedIn` provides cost and operand
  bounds separately; `RAMToTM.exists_resources_of_monomial_bound` specializes to a monomial bound.
- `CookLevin.pairPreludeDecider` builds a verifier decider from a bounded body and its correctness.
  `CookLevin.exists_pairPrelude_resources` and `exists_pairPrelude_resources_of_monomial_bound`
  provide the complete prelude-plus-body resource bounds separately.
- `RAMToTM.exists_cost_le_of_programBoundedIn` bounds a scan-free program's cost polynomially in
  its value bound, including for intermediate stores.
- The syntax-specific `ProgramBoundedIn` lemmas decompose resource proofs; in particular,
  `RAMToTM.programBoundedIn_forN_of_indexed` uses an indexed invariant for a loop body.
- `RAMToTM.BitsFrom` describes bits stored from a given cell, useful for verifier and producer
  correctness proofs.
- `RAMToTM.readUnaryProgAt` reads unary data with initialized counters; `decodeUnaryProgAt` is the
  lower-level reader. `CookLevin.decodeLiteralValueProgramAt` reads an encoded literal's value.
- `RAMToTM.forwardCopyProg` moves an input region to a higher, non-overlapping destination while
  preserving the source, providing workspace for a verifier or producer.

The producer entry points do not expose ABI types in their statements. Their hypotheses are
facts about the final store: cell 0 holds the output start address, cell 1 the output length,
cell `outputBase + i` the `i`-th bit (`0`/`1`), plus a polynomial bound on the output length.
**In addition, the output `eb (f x)` must end with `true` and have length at least 2**
(`hends` `hlen2`; needed to decode the raw tape). Length-prefixing alone does not guarantee
these conditions (for example, `encodeList encodeNat [] = [true]` has length 1, and
`encodeList encodeBool [false]` ends with `false`), so verify `hends` and `hlen2` for the chosen
output encoding. `encodeNat 0 = [true]` and one-bit outputs (a bare `encodeBool`) have length
below 2, so this entry point cannot be used for them.

The standard way to prove the `compiled_operands_le` field of `BoundedWhileDecider` is
`compiledOperandBound_of_programBoundedIn`: given `1 ≤ B`,
`StoreValuesLe B (bitInputStore bits)`, `ProgramBoundedIn B (bitInputStore bits) p`, and
`ScanFree p`, every compiled operand fits in `bitLen B` bits.

The high-level entry points take care of the direction of the output buffer, so you do not need
to handle it yourself.
Reductions are stated with the TM0 `PolyTimeReduction`; the library has no separate TM2
reduction structure. Build one from a producer with `PolyTimeReduction.of_forwardBitProducer`;
a TM2 computation with Boolean output connects to TM0 via `TM2ComputableInPolyTime.toTM0`.

### External usage example

The example body below matches the code between the markers in
`NPComplete/Test/ReadmeExample.lean`. The test places `import NPComplete` before that block because
Lean imports must precede the example declarations; `lake build NPComplete.Extra` compiles it, so
the example is checked against the current library.

```lean
import NPComplete

open NPComplete.CookLevin NPComplete.RAMToTM NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits encodeNat)
open NPComplete.BitCostRAM (bitLen bitLen_le_succ)

namespace ReadmeExample

/-- A program that only reads the loaded input keeps every compiled operand within `bitLen (n + 1)`
bits, which is below `2 * (n + 1) ^ 2`. This discharges `compiled_operands_le` below. -/
lemma skip_operands (bits : Bits) :
    ∃ W, W ≤ 2 * (bits.length + 1) ^ 2 ∧ CompiledOperandBound Program.skip bits W := by
  refine ⟨bitLen (bits.length + 1), ?_, compiledOperandBound_of_programBoundedIn Program.skip bits
    (bits.length + 1) (by omega) ?_ trivial trivial⟩
  · have h := bitLen_le_succ (bits.length + 1)
    nlinarith [Nat.zero_le bits.length]
  · intro i
    match i with
    | 0 => simp [bitInputStore]
    | i + 1 => simp only [bitInputStore]; split <;> omega

/-- The language of bit strings whose first bit is `true`. -/
def FirstBit (x : Bits) : Prop := x.getD 0 false = true

/-- The program does nothing; the answer is already in cell `1` (bit `0` as `0`/`1`) of the
canonical input store. -/
def firstBitDecider : BoundedWhileDecider (fun x : Bits => x) (fun _ => True) FirstBit where
  p := Program.skip
  outReg := 1
  c := 1
  correct := fun x _ => by
    cases h : x.getD 0 false <;> simp [FirstBit, bitInputStore]
  cost_le := fun x _ => by simp
  bit_c := 2
  compiled_operands_le := fun x _ => skip_operands x

/-- `InP` from a decider written in the DSL. -/
lemma firstBit_inP : InP (fun x : Bits => x) FirstBit :=
  InP.of_boundedWhileDecider firstBitDecider

/-- Certificates of length at most `1` for the single instance `()`: the verifier sees
`pairBits [] w = false :: w`, so the certificate bit is cell `2`. -/
def verifierDecider :
    BoundedWhileDecider (fun xw : Unit × List Bool => pairBits [] xw.2) (fun _ => True)
      (fun xw => xw.2.getD 0 false = true) where
  p := Program.skip
  outReg := 2
  c := 1
  correct := fun xw _ => by
    obtain ⟨_, w⟩ := xw
    cases w with
    | nil => simp [pairBits, bitInputStore]
    | cons b w => cases b <;> simp [pairBits, bitInputStore]
  cost_le := fun xw _ => by simp
  bit_c := 2
  compiled_operands_le := fun xw _ => skip_operands _

/-- `InNP` from a verifier written in the DSL. -/
lemma unit_inNP : InNP (fun _ : Unit => ([] : Bits)) (fun _ => True) :=
  InNP.of_bounded_while_verifier (fun _ : Unit => ([] : Bits)) (fun _ => True) 1
    (fun _ w => w.getD 0 false = true)
    (fun _ => ⟨fun _ => ⟨[true], by simp, rfl⟩, fun _ => trivial⟩)
    verifierDecider

/-- Writes the output `encodeNat 1 = [false, true]` at base `4` with cell `0` = base and
cell `1` = length, as `of_forwardBitProducer` requires. The output ends with `true` and has
length `2`, the minimum allowed. -/
def constProducer : Program :=
  (Program.assign 0 (.const 4)).seq <|
  (Program.assign 1 (.const 2)).seq <|
  (Program.assign 4 (.const 0)).seq (Program.assign 5 (.const 1))

lemma constProducer_eval (σ : Store) :
    constProducer.eval σ = writeReg (writeReg (writeReg (writeReg σ 0 4) 1 2) 4 0) 5 1 := by
  simp [constProducer, Expr.eval]

/-- Only the two quantitative obligations are supplied; `ofBounds` fills in the rest. -/
def constDecider : BoundedWhileDecider (fun _ : Unit => ([] : Bits)) (fun _ => True)
    (fun _ => constProducer.eval (bitInputStore []) 0 = 1) :=
  BoundedWhileDecider.ofBounds (fun _ : Unit => ([] : Bits)) constProducer 0 8 9
    (fun x => by simp [constProducer, Expr.cost])
    (fun x => ⟨bitLen 8, by simpa using bitLen_le_succ 8,
      compiledOperandBound_of_programBoundedIn constProducer [] 8 (by omega)
        (fun i => by cases i <;> simp [bitInputStore])
        (by simp [constProducer, ProgramBoundedIn, ExprBoundedIn])
        (by simp [constProducer, ScanFree])⟩)

/-- A reduction from a one-point language to "equals `1`" on `ℕ` under `encodeNat`. -/
noncomputable def constReduction :
    PolyTimeReduction (fun _ : Unit => ([] : Bits)) encodeNat (fun _ => True) (fun n => n = 1) :=
  PolyTimeReduction.of_forwardBitProducer (f := fun _ : Unit => 1) constDecider
    4 (Polynomial.C 2)
    (fun x => by simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, writeReg])
    (fun x => by simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, encodeNat, writeReg])
    (fun x i hi => by
      simp [encodeNat] at hi
      interval_cases i <;> simp [constDecider, BoundedWhileDecider.ofBounds, constProducer_eval, encodeNat, writeReg])
    (fun x => by simp [encodeNat])
    (fun x => ⟨[false], by simp [encodeNat]⟩)
    (fun x => by simp [encodeNat])
    (fun x => by simp)

/-- NP-completeness of a language `L` needs `L ∈ NP` and one polynomial-time reduction from 3SAT
to `L`. The Cook-Levin construction is not repeated. -/
lemma target_NPComplete {β : Type} (eb : β → Bits) (L : β → Prop) (hL : InNP eb L)
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L) : NPComplete eb L :=
  NPComplete.of_threeSAT hL r

/-- Without membership in NP, the same reduction still gives NP-hardness. -/
lemma target_NPHard {β : Type} (eb : β → Bits) (L : β → Prop)
    (r : PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L) : NPHard eb L :=
  NPHard.of_threeSAT r

/-- Hardness moves along a further reduction. -/
lemma target_NPHard_of_reduction {β γ : Type} {eb : β → Bits} {ec : γ → Bits}
    {L : β → Prop} {M : γ → Prop} (hL : NPHard eb L) (r : PolyTimeReduction eb ec L M) :
    NPHard ec M :=
  NPHard.of_reduction hL r

end ReadmeExample
```

## 6. Compatibility and maintenance policy

Lean cannot forbid the use of a declaration, so the layers of Section 5 differ only in how
changes are made, not in what you may use.

**Entry point.** `import NPComplete` is the only import path that is kept stable. The paths of
leaf modules (for example `NPComplete.CookLevin.…`) may change without notice, like untagged
declarations. You may import a leaf module directly, but you bear the risk that its path changes.

**Changes by layer.**

- `@[stable_api]`: the statement is a compatibility promise. A change is breaking and is made
  deliberately, with the pinned statements in `NPComplete/Test/StableApi.lean` updated.
- `@[construction_api]`: you may use it, but it may change. A change raises the minor version.
- Untagged (internal): changed without notice. You may use it, but it may change silently.

**Versions.** The library starts at 0.x (`lakefile.toml`). While the major version is 0, a
breaking change to a stable declaration also raises the minor version. From 1.0 on, a breaking
change to a stable declaration raises the major version, and a change to a construction
declaration raises the minor version. Version 0.4.0 adds construction entry points and moves some
declarations to namespaces matching their subjects. Their former internal names remain as aliases,
but internal names are outside the compatibility promise.

**Meaning of stable definitions.** For a stable recursive definition, the equation lemmas (one per
constructor) are stable and fix its meaning. The unfolded form that `simp [f]` or similar tactics
expose is not part of the contract; state the dependence on the meaning through the equation
lemmas.

**Module importers.** The library is written in the Lean module system. A file without a `module`
header can import it and sees everything, as before. A module file can import it too, but what it
sees depends on the kind of import. With a plain `import NPComplete`, the bodies of the mutually
recursive and well-founded definitions (for example `Program.eval`, `Program.cost`, `loopEval`, and
`scanListEval` in `NPComplete.BoundedWhile`, and `compile` in `NPComplete.RAMToTM`) are not visible,
so `simp only [Program.eval]`, `unfold Program.eval`, and `rw [Program.eval]` stop at an auxiliary
form such as `Program.eval._mutual` and do not close the goal. To unfold such a definition, write
`public import NPComplete`. If you keep the plain import, rewrite with the equation lemmas that the
library ships instead, for example `eval_skip`, `eval_assign`, `eval_seq`, `loopEval_zero`,
`loopEval_succ`, `cost_skip`, and `cost_seq` in `NPComplete.BoundedWhile`. Structurally recursive
definitions such as `Expr.eval` unfold under either import, and `simp [Program.eval]` (without
`only`) can still succeed under a plain import when the `@[simp]` equation lemmas close the goal.

**Namespace.** Please do not add declarations to `NPComplete.*` from downstream code. This cannot be
enforced, but if the library later adds a declaration with the same name, you get a duplicate
declaration error and the library's declaration takes precedence. If you need an additional lemma
about a concept of the library, state it in your own namespace.

## 7. Verification

```sh
lake build NPComplete
lake build NPComplete.Extra
scripts/check_importer_tests.sh
```

`NPComplete.Extra` is not part of the regular API; it is the verification entry point for
modules and witnesses not reachable from `NPComplete`. Build both targets for full verification.
`#print axioms` for the nine main theorems (`sat_NPHard`, `sat_NPComplete`, `threeSAT_NPHard`,
`threeSAT_NPComplete`, `sat_inNP`, `threeSAT_inNP`, `p_ne_np_implies_h3sat`,
`sat_InP_implies_PeqNP`, and `threeSAT_InP_implies_PeqNP`) reports only `propext`,
`Classical.choice`, and `Quot.sound`.

`NPComplete.Extra` also checks the API layers (`NPComplete/Test/`). It pins the types of stable
declarations with `#guard_msgs` (`StableApi.lean`) and checks that the statements of tagged
declarations do not refer to internal declarations (`ApiLayers.lean`; `ApiLayersNegative.lean`
confirms that the check detects violations). A change to the type of a stable declaration
therefore breaks the build.

`scripts/check_importer_tests.sh` checks that `import NPComplete` behaves as described in Section 6
for both module and non-module importers (the README example, the visibility of definition bodies,
and the expected failures under a plain import); it builds the separate `NPCompleteTest` library.

## Development and forks

This repository does not accept pull requests or issues. You are free to fork it and modify it under
the terms of the Apache License, Version 2.0 (see `LICENSE`). [DEVELOPMENT.md](DEVELOPMENT.md)
describes the conventions the code follows.

## License

Copyright 2026 Takashi HOSHINO. Licensed under the Apache License, Version 2.0; see `LICENSE`.

# Development conventions

This file describes the development conventions used in `NPComplete`. It is meant for people who
fork the library and want their changes to stay consistent with the existing code. See the README
for the terms on which the repository can be forked.

## Setting up

Install [elan](https://github.com/leanprover/elan) first; `lean-toolchain` selects the Lean version.
Then, in the repository root:

```sh
lake exe cache get
lake build
```

The committed `lake-manifest.json` records the dependency revisions this library is built and tested
with. Do not run `lake update` as part of routine setup: it re-resolves the dependencies and may
change the manifest. Changing the Lean or Mathlib version is a change of its own: the toolchain and
the dependency revisions in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` move
together.

## Rules for the library

- **Dependencies.** The package depends only on Mathlib (`lakefile.toml` has a single
  `[[require]]`), and the checks assume this.
- **Proof trust and completeness.** Do not introduce `axiom` declarations, use `admit`, or use
  `native_decide`. A finished change contains no `sorry`. The main theorems (`sat_NPComplete`,
  `threeSAT_NPComplete`) must keep depending only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- **No warnings.** The build is expected to finish without warnings or errors. Do not raise
  `maxHeartbeats` or similar limits to make a proof go through; restructure the proof instead.
- **Namespace and layout.** Every declaration owned by this library is under `NPComplete.*`.
  Modules are arranged by subject: a top-level directory or single module per major namespace
  (`CookLevin`, `RAMToTM`, `BoundedWhile`, `BitCostRAM`, `BitEncoding`, `SAT`, and so on). Place a
  new module with the subject it belongs to.
  - `RAMToTM/Generic/` must not import the upper layers (`CookLevin`, `SAT`, `RAMToTM.ThreeSat`).
    A declaration that connects the two sides goes in a bridge module outside `Generic/`.
  - Renaming a declaration or moving a module is a compatibility concern (see "API layers"). Do it
    by hand and with care, not by a bulk text replacement.
- **`lemma` and `theorem`.** Use `lemma` by default; `theorem` is for the main
  results. Do not introduce `private` lemmas: if a helper is worth stating, make it public (and
  tag it, see below, if it belongs to the public surface).

## The module system

Every file of the library is a Lean module. A new file looks like this:

```lean
module

meta import NPComplete.Meta.ApiLayer   -- only if the file uses a layer attribute
public import Mathlib.Tactic           -- every other import is a `public import`

/-!
# Title

Why this module exists.
-/

@[expose] public section

namespace NPComplete.Foo
...
```

`public import` and `@[expose] public section` matter for users of the library: with a plain
`import`, the bodies of mutually recursive and well-founded definitions are invisible to the
importer, so `simp [f]` and `unfold f` stop at an auxiliary form. Please read the "Module
importers" paragraph of the README. If a module system change makes a Mathlib tactic or instance
unavailable, add the Mathlib module you need as a `public import`. Put `deriving` clauses on the
type definition itself rather than in a separate `deriving instance` command.

A new library module (a file under `NPComplete/`) must be reachable by import from `NPComplete.lean`
or from `NPComplete/Extra.lean`; a file that nothing imports is not built by the package build and
may be broken without notice. Build a new module by name (`lake build NPComplete.Foo.Bar`) and then
import it. Files that the main theorems do not use (checks, witnesses of non-vacuity) are registered
in `NPComplete/Test/Witnesses.lean` or `NPComplete/Extra.lean` and not in the umbrella. The importer
tests under `NPCompleteTest/` are a separate library: they are built by `lake build NPCompleteTest`,
and the files in `NPCompleteTest/ShouldFail/` are checked by `scripts/check_importer_tests.sh`.

## API layers

Public declarations carry a layer attribute (defined in `NPComplete/Meta/ApiLayer.lean`; the policy
is Section 5 and Section 6 of the README):

- `@[stable_api]`: the statement is a compatibility promise. The main theorems, the SAT/3SAT types,
  and the hardness-transfer entry points `NPHard.of_threeSAT` and `NPComplete.of_threeSAT` are
  stable by explicit decision, although they are specific to SAT/3SAT (Section 5 of the README lists
  what is stable). For the other stable declarations, the criteria are: no dependence on a specific
  problem or memory layout, and no internal-layer types in the statement.
- `@[construction_api]`: usable by clients but may change.
- No attribute: internal.

The statement of a tagged declaration may only mention `NPComplete.*` declarations of a suitable
layer: everything it refers to must be `stable_api` if it is stable, and `stable_api` or
`construction_api` if it is a construction. `NPComplete/Test/ApiLayers.lean` checks this. If it
reports a violation, decide whether the dependency can reasonably be put in the same layer; do not
tag an internal type just to silence the check.

Changing the type of a stable declaration makes `NPComplete/Test/StableApi.lean` fail (it pins the
types with `#guard_msgs`). That is intended: it is a breaking change, so update the expected output
deliberately. When you add a stable declaration, add a `#check @X`
to `StableApi.lean` (and `#print X` for a structure, inductive type, or predicate definition).

Tagged declarations must be defined in the import closure of `NPComplete.lean`
(`#check_api_umbrella` checks this).

## Proof style

- Keep proofs short and structured. As a guideline, a proof has at most about 100 lines and nests
  case analyses at most three levels deep; a long `have` (more than about 10 lines) is a candidate
  for its own lemma. Prefer an induction or a lemma over unfolding one step at a time. These are
  guidelines, not hard limits. Prefer the clearest proof structure, and keep exceptions rare.
- Prefer self-explanatory proof structure over line-by-line commentary. Use comments for non-obvious
  ideas or to mark the stages of a longer proof. Explain why a lemma or module exists (in its
  docstring), not what each line does.
- Docstrings and comments must not refer to source line numbers.
- Before stating a lemma, check it on a concrete example to make sure it is not false or vacuous.
- For statements that a program leaves a register unchanged, use the machinery of
  `NPComplete/BoundedWhile/Frame.lean` (`Program.Avoids` certificates) rather than chaining
  `writeReg_diff` by hand.

## Naming

The project follows the Lean 4 and Mathlib naming conventions.

- Types, structures, classes, and predicates such as `SAT`, `InNP`, `NPHard`: `PascalCase`
  (acronyms stay capitalized: `ThreeCNF`, `BitCostRAM`).
- Lemmas and theorems: `snake_case`, with acronyms capitalized (`sat_InP_implies_PeqNP`).
- Structure fields: `snake_case` for proofs, `lowerCamelCase` for data.

## Checking your change

Run these from the repository root after a change:

```sh
lake build NPComplete
lake build NPComplete.Extra
scripts/check_importer_tests.sh
```

The full check script requires Bash 4 or later (it uses `mapfile`), Python 3, and GNU-compatible
command-line tools (for example `readlink -f`, `mktemp`, and `find`).

- `NPComplete.Extra` builds the checks that the umbrella does not import: witnesses, the API-layer
  checker, the pinned stable statements, and the README example.
- `scripts/check_importer_tests.sh` builds `NPCompleteTest`, which imports `NPComplete` the way
  downstream packages do (module and non-module importers), and checks that the files in
  `NPCompleteTest/ShouldFail/` are rejected with the expected error. A file added to `ShouldFail/`
  must also be listed in the script.
- If you change the main theorems, check `#print axioms` of `sat_NPComplete` and
  `threeSAT_NPComplete`; `NPCompleteTest/Final/Axioms.lean` pins the expected output.

### README and its example

The README example code and `NPComplete/Test/ReadmeExample.lean` (between the `README BEGIN` and
`README END` markers; compiled by `NPComplete.Extra`) are synchronized by hand: if you change the
example, edit both places, and no script compares them with `README.md`. The generator
`scripts/gen_readme_importer_tests.py` reads only `ReadmeExample.lean` and writes two copies for the
importer tests, `NPCompleteTest/Final/ReadmePlain.lean` and `NPCompleteTest/NonModule/Readme.lean`.
Do not edit these two by hand. After changing `ReadmeExample.lean`, regenerate them and check them:

```sh
python3 scripts/gen_readme_importer_tests.py
python3 scripts/gen_readme_importer_tests.py --check
```

`--check` verifies that the two copies are identical to what the generator would write now; it does
not look at `README.md`. `scripts/check_importer_tests.sh` runs this check.

The README is documentation for users of the library. Notes for developers belong in this file.

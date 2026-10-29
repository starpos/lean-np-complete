# NPCompleteTest

Tests that `import NPComplete` the way downstream packages do, as a second `[[lean_lib]]` of this package.
`lake build NPCompleteTest` builds every module below except `ShouldFail/`. It is not part of
`defaultTargets`.

The library is written in the Lean module system, so what an importer can see depends on the importer:
a module that uses a plain `import` does not see the bodies of non-`@[expose]` definitions, and the
attribute implementations of `NPComplete.Meta.ApiLayer` need a `meta import`. These tests pin that
behaviour. A test that expects an error uses `#guard_msgs (substring := true)`, so it passes only for the
expected error text and breaks the build if it starts to succeed or fails differently.

## Groups

| directory | importer | content and expected result |
|---|---|---|
| `Pilot/` | module files, small imports | One topic per file: `simp`/`unfold`/`rw` on mutual and well-founded definitions (fail under plain `import`, work under `public import`), `Avoids` certificates by `decide` for imported programs (which must be exposed; local programs need no exposure), `deriving DecidableEq`, the API-layer attributes (need `meta import`). Support modules: `Defs`, `DefsHidden`, `DerivExpose`, `DerivPublicOnly`, `Mid`. |
| `Final/` | module files, `import NPComplete` | Uses in the style of a large downstream package, the README example, `#print axioms` of the two main theorems, the API-layer checker through the umbrella (it must see at least 240 tagged declarations). |
| `NonModule/` | files without a `module` header | The same operations as a package that has not adopted the module system. What fails under a plain-import module importer because of the module boundary works here; closed-term `decide` on `Program.eval` still fails, as it does for any importer. |
| `Sentinel/` | module files | Trivial files, one of which pins an expected error, to show that the build elaborates module test files. |
| `ShouldFail/` | module files | Must be rejected. Outside the library globs; run by the script below. |

Lint options `linter.unusedSimpArgs` and `linter.unusedVariables` are switched off in some files, where
an unnecessary `simp` argument or variable is part of what is tested.

## README example

`NPComplete/Test/ReadmeExample.lean` (built by `NPComplete.Extra`, under `public import NPComplete`) is the
single source of the README example. `Final/ReadmePlain.lean` and `NonModule/Readme.lean` are generated
from it by `scripts/gen_readme_importer_tests.py`, which only changes the header and namespace. Do not edit
them by hand; `scripts/check_importer_tests.sh` fails when they are out of date.

## Scripts

    lake build NPCompleteTest              # all test modules
    scripts/check_importer_tests.sh        # full check

The script checks that the generated copies are current and that every file under
`NPCompleteTest/`, except those in `ShouldFail/` and `NonModule/`, starts with `module`.
It also checks that `lake build NPCompleteTest` has no warning and produces an `.ilean`
for every test module (after deleting the previous outputs), and that each file in
`ShouldFail/` is rejected with its expected error text. When a file is added to
`ShouldFail/`, list it in the script as well.

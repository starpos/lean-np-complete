#!/usr/bin/env bash
# Usage: scripts/check_importer_tests.sh
# Checks NPCompleteTest, the tests that import NPComplete as downstream packages do:
#   1. the README-example copies are up to date;
#   2. every test file has the expected header (`module` everywhere except NonModule/);
#   3. `lake build NPCompleteTest` succeeds with no warning, and every test module has a fresh .ilean
#      (so a module that the build skipped is noticed);
#   4. every file in NPCompleteTest/ShouldFail/ is rejected with its expected error text.
# Exits non-zero on any mismatch. Never runs `lake update` or `lake exe cache get`.
set -u
cd "$(dirname "$(readlink -f "$0")")/.."
bad=0
fail() { echo "FAIL: $*"; bad=$((bad+1)); }

python3 scripts/gen_readme_importer_tests.py --check || fail "README-example copies are out of date"

mapfile -t tests < <(find NPCompleteTest -name '*.lean' -not -path 'NPCompleteTest/ShouldFail/*' | sort)
for f in "${tests[@]}"; do
  first=$(head -1 "$f")
  case "$f" in
    NPCompleteTest/NonModule/*) [ "$first" != "module" ] || fail "$f must not start with 'module'" ;;
    *) [ "$first" = "module" ] || fail "$f must start with 'module'" ;;
  esac
done

log=$(mktemp)
# remove the test modules' outputs so that a stale artifact cannot make a skipped module look built
# (find -delete instead of rm -rf, which the sandbox refuses)
for d in .lake/build/lib/lean/NPCompleteTest .lake/build/ir/NPCompleteTest; do
  [ -d "$d" ] && find "$d" -depth -delete
done
lake build NPCompleteTest >"$log" 2>&1; rc=$?
cat "$log"
[ $rc -eq 0 ] && grep -q "Build completed successfully" "$log" || fail "lake build NPCompleteTest"
if grep -q -E "(^|: )(warning|error)" "$log"; then fail "build log contains warning or error"; fi
for f in "${tests[@]}"; do
  ilean=".lake/build/lib/lean/${f%.lean}.ilean"
  [ -f "$ilean" ] || fail "no .ilean for $f (module was not built)"
done
echo "built ${#tests[@]} test modules"

# file : text that must occur in the error output
should_fail=(
  "NPCompleteTest/ShouldFail/DecideFalse.lean:proved that the proposition"
  "NPCompleteTest/ShouldFail/PlainImportSimp.lean:_mutual"
  'NPCompleteTest/ShouldFail/UntaggedInstance.lean:instance `NPComplete.Test.arbitraryInstanceName` for public type `NPComplete.Test.InstanceFixture` is untagged'
  'NPCompleteTest/ShouldFail/StageAdapterBoundary.lean:mentions stage_adapter `NPComplete.RAMToTM.LayoutStage.ofSpec`'
  'NPCompleteTest/ShouldFail/StageRawEntry.lean:mentions the raw store operation `NPComplete.RAMToTM.LayoutSpec.assign`'
  'NPCompleteTest/ShouldFail/StageUncheckedMention.lean:mentions stage_unchecked `NPCompleteTest.ShouldFail.StageUncheckedMention.legacy`'
  'NPCompleteTest/ShouldFail/StageEvalLemma.lean:mentions the raw store operation `NPComplete.BoundedWhile.eval_seq`'
  'NPCompleteTest/ShouldFail/StageBuildsStore.lean:builds a `Store` by a lambda'
  'NPCompleteTest/ShouldFail/StageConcreteStore.lean:a closed `Store` passed as an argument'
  'NPCompleteTest/ShouldFail/StageImplEval.lean:mentions stage_impl `NPCompleteTest.Final.StageFix.bump_eval`'
  'NPCompleteTest/ShouldFail/StageMentionsUnclassified.lean:mentions unclassified `NPCompleteTest.ShouldFail.StageMentionsUnclassified.hidden`'
  'NPCompleteTest/ShouldFail/StageNumAssign.lean:a numeric register in the target of `Program.assign`'
  'NPCompleteTest/ShouldFail/StageNumAssignInd.lean:a numeric address in `Program.assignInd`'
  'NPCompleteTest/ShouldFail/StageNumReg.lean:a numeric register in `Expr.reg`'
  'NPCompleteTest/ShouldFail/StageNumTree.lean:has a numeric register in the target of `Program.assign`'
  'NPCompleteTest/ShouldFail/StageStoreNumeral.lean:a numeral applied to a `Store`'
  'NPCompleteTest/ShouldFail/StageStoreNumeralHelper.lean:a numeral applied to a `Store`'
  'NPCompleteTest/ShouldFail/StageStoreNumeralStmt.lean:a numeral applied to a `Store`'
  "NPCompleteTest/ShouldFail/StageUnclassified.lean:is not classified"
  'NPCompleteTest/ShouldFail/StageWriteReg.lean:mentions the raw store operation `NPComplete.BoundedWhile.writeReg`'
  'NPCompleteTest/ShouldFail/StageDefaultViol.lean:a numeric register in `Expr.reg`'
  'NPCompleteTest/ShouldFail/StageDefaultLenient.lean:stage_default_free'
  'NPCompleteTest/ShouldFail/StageDefaultConflict.lean:conflicting defaults'
  'NPCompleteTest/ShouldFail/StageDefaultMention.lean:mentions stage_impl'
)
for entry in "${should_fail[@]}"; do
  f=${entry%%:*}; needle=${entry#*:}
  out=$(lake lean "$f" 2>&1); rc=$?
  if [ $rc -ne 0 ] && grep -q "error" <<<"$out" && grep -q -- "$needle" <<<"$out"; then
    echo "rejected as expected: $f"
  else
    fail "$f was not rejected with '$needle' (rc=$rc)"
  fi
done
n=$(find NPCompleteTest/ShouldFail -name '*.lean' | wc -l)
[ "$n" -eq "${#should_fail[@]}" ] || fail "ShouldFail/ has $n files but ${#should_fail[@]} are listed"

rm -f "$log"
[ $bad -eq 0 ] && echo "OK: importer tests as expected" || echo "$bad problem(s)"
[ $bad -eq 0 ]

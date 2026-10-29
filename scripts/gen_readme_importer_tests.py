#!/usr/bin/env python3
"""Generate the importer tests that repeat the README example.

NPComplete/Test/ReadmeExample.lean is the source (it is kept in sync with README.md and is built by
`lake build NPComplete.Extra` under `public import NPComplete`). The text between its README BEGIN and
README END markers is copied, with the namespace renamed, into NPCompleteTest/ to run the same example
from importers of other kinds. `--check` verifies that the committed copies are up to date.
"""
import os
import sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = os.path.join(root, 'NPComplete', 'Test', 'ReadmeExample.lean')
text = open(src, encoding='utf-8').read()
body = text.split('-- README BEGIN\n')[1].split('-- README END')[0]

TARGETS = [
    ('NPCompleteTest/Final/ReadmePlain.lean', 'ReadmePlainExample',
     'module\n\nimport NPComplete',
     '# README example, module importer, plain `import NPComplete`\n\n'
     'Generated from `NPComplete/Test/ReadmeExample.lean` by `scripts/gen_readme_importer_tests.py`.\n'
     'That source covers `public import NPComplete`; this copy covers the plain import. Expected: ok.'),
    ('NPCompleteTest/NonModule/Readme.lean', 'ReadmeNonModuleExample',
     'import NPComplete',
     '# README example, non-module importer\n\n'
     'Generated from `NPComplete/Test/ReadmeExample.lean` by `scripts/gen_readme_importer_tests.py`.\n'
     'Expected: ok.'),
]


def render(ns, head, doc):
    b = body.replace('namespace ReadmeExample', 'namespace ' + ns).replace('end ReadmeExample', 'end ' + ns)
    return head + '\n\n/-!\n' + doc + '\n-/\n\n' + b


def main():
    check = '--check' in sys.argv[1:]
    stale = []
    for rel, ns, head, doc in TARGETS:
        path = os.path.join(root, rel)
        new = render(ns, head, doc)
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if check:
            if old != new:
                stale.append(rel)
        elif old != new:
            open(path, 'w', encoding='utf-8').write(new)
            print('updated', rel)
    if stale:
        print('out of date (run scripts/gen_readme_importer_tests.py):', *stale)
        return 1
    return 0


sys.exit(main())

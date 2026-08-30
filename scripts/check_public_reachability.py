#!/usr/bin/env python3
"""Check that no module under a non-public directory is reachable, by
direct or transitive import, from the public umbrella `Scaffold.lean`.

Proposal: `proposals/axiom-audit-tooling.md` (Deliverable 3). The
vocabulary-free version of "reject quarantined modules": the repository
already treats `wip/` as its non-public experiment area (spikes, axcheck
files, scratch logs — never built by `lake build`, never imported by
shelf modules). A shelf module importing a `wip/` file would fail the
build for lack of an olean anyway, but only if it is *reached* by a
build target — a stale-olen or hand-build accident could hide it, and
the static check also catches the leak at review time rather than build
time, including `wip.`-named imports that resolve to no file at all.

Step-0 survey (2026-08-30, recorded in the proposal): `wip/` is the
only non-public Lean directory in the tree — `Scaffold/Internal/` and
`Scaffold/Trusted/` hold READMEs only, `research/` holds no `.lean`
files, and nothing under `Scaffold/` imports `wip.*` today. If a future
non-public Lean area appears, add its module prefix to
NON_PUBLIC_PREFIXES below (one line, and this docstring stays the
record of the decision).

The walk: parse every repo `.lean` file's `import` lines, map module
names to files (`Scaffold/Foo/Bar.lean` <-> `Scaffold.Foo.Bar`,
`wip/baz.lean` <-> `wip.baz`), and BFS from the umbrella root module
`Scaffold`. Non-public leakage fails in two forms: a visited module
whose file lives under a non-public directory, and a `wip.`-prefixed
*import edge* inside the closure even when it resolves to no file
(Mathlib and other external imports resolve to nothing and are fine).
"""

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Module-name prefixes (equivalently, directory roots) the repository
# treats as non-public. Extend deliberately; see the docstring.
NON_PUBLIC_PREFIXES = ('wip.',)

IMPORT_RE = re.compile(r'^import\s+([A-Za-z_][\w.]*)', re.MULTILINE)


def module_name_of(path):
    return str(path.relative_to(REPO)).removesuffix('.lean').replace('/', '.')


def build_graph():
    """Return ({module: [imports]}, {module: file})."""
    edges = {}
    files = {}
    skip_parts = {'.lake', '.git'}
    for path in REPO.rglob('*.lean'):
        rel = path.relative_to(REPO).parts
        if rel[0] in skip_parts:
            continue
        mod = module_name_of(path)
        files[mod] = path
        edges[mod] = IMPORT_RE.findall(path.read_text())
    return edges, files


def main():
    edges, files = build_graph()
    failures = []
    visited = set()
    frontier = ['Scaffold']
    if 'Scaffold' not in files:
        print('FAIL: umbrella module `Scaffold` (Scaffold.lean) not found')
        sys.exit(1)
    while frontier:
        mod = frontier.pop()
        if mod in visited:
            continue
        visited.add(mod)
        f = files.get(mod)
        if f is not None and any(
                str(f.relative_to(REPO)).startswith(p.rstrip('.'))
                for p in NON_PUBLIC_PREFIXES):
            failures.append(
                f'non-public module `{mod}` '
                f'({f.relative_to(REPO)}) is reachable from the public '
                f'umbrella')
        for imp in edges.get(mod, []):
            for p in NON_PUBLIC_PREFIXES:
                if imp == p.rstrip('.') or imp.startswith(p):
                    src = f.relative_to(REPO) if f else 'Scaffold.lean'
                    failures.append(
                        f'public-umbrella module `{mod}` ({src}) imports '
                        f'`{imp}` — a non-public ({p}*) module')
            if imp not in visited and imp in files:
                frontier.append(imp)
    if failures:
        for x in dict.fromkeys(failures):
            print(f'FAIL: {x}')
        print(f'public import closure: {len(visited)} repo modules')
        sys.exit(1)
    print(f'OK: public umbrella import closure is {len(visited)} repo '
          f'modules; no non-public ({", ".join(NON_PUBLIC_PREFIXES)}) '
          f'module reachable')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Check negative-witness independence: a refutation or fence QA
declaration must not depend, in its proof term, on the axiom it refutes.

Proposal: `proposals/axiom-audit-tooling.md` (Deliverable 1, the Active
table's High row). "A refutation cannot consume what it refutes" has
been checked by hand via `#print axioms` in every axiom-repair record
so far (Bernstein, `matrix_hoeffding` centering, `MatrixMDS`
measurability, the pairwise-independence six); this script makes the
check mechanical so a future delivery cannot get it wrong silently.

Mechanism: QA declarations carry an explicit inline tag

    /-- docstring -/
    -- @refutes: matrix_hoeffding
    theorem old_matrix_hoeffding_refuted_fin0_QA ... := by ...

The tag line must sit after the docstring (or anywhere above the
declaration) and before any other tag; it binds to the next
`theorem`/`lemma`/`def`/`example` declaration in the file. The tag's
target must name a *currently admitted* axiom (an `axiom` declaration
under `Scaffold/Mathlib`); a tag naming anything else — a retired
axiom name (now a proved theorem), a theorem, a typo — is an error, so
tags stay load-bearing and cannot rot into noise after a retirement.

For every tagged declaration the script generates one temporary Lean
file importing the containing modules and issuing `#print axioms` on
each full declaration name, runs `lake env lean` on it, and parses the
reported dependency sets (real environment-derived extraction, the
same channel the hand audits used — no textual approximation of proof
terms). It fails when:

- a tagged declaration's dependency set contains its target axiom;
- a tag's target is not a current axiom;
- a tag binds to a `private` declaration (private names are invisible
  to importing modules, so no honest `#print axioms` file can reach
  them);
- a tagged declaration's `#print axioms` record is missing or the
  elaboration reports an error;
- zero tags are found at all (a vacuous pass is the false-silence
  failure mode; the current tree carries tags, and their silent
  removal should be loud).

Scope decision (Step-0 survey, recorded in the proposal): only
declarations refuting a *current axiom's* shape are tagged. The QA
tree's 60+ `_refuted`/`_fence` declarations mostly refute
hypothesis-dropped shapes of *proved theorems* — depending on a proved
theorem is legitimate, so those get no tag. After an axiom is retired
to a theorem, its old refutations' tags are removed with the
retirement (the check fails them until then, which is the intended
prompt).
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

TAG_RE = re.compile(r'^\s*--\s*@refutes:\s*([A-Za-z_][\w.]*)\s*$')
DECL_RE = re.compile(
    r'^\s*(?:@\[.*\]\s*)?(?:private\s+)?(theorem|lemma|def|example)\s+'
    r'([A-Za-z_]\w*)')
AXIOM_RE = re.compile(r'^axiom\s+([A-Za-z_]\w*)', re.MULTILINE)
IMPORT_RE = re.compile(r'^import\s+([A-Za-z_][\w.]*)', re.MULTILINE)


def _mask_block_comments(text):
    """Blank out `/- ... -/` block-comment interiors (docstrings, module
    docs; these nest in Lean) so a prose docstring line like 'axiom was
    materially false' cannot match the axiom regex. Returns text with
    those interiors replaced by spaces, preserving line structure."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
        elif text.startswith('-/', i) and depth > 0:
            depth -= 1
            out.append('  ')
            i += 2
        else:
            out.append(text[i] if depth == 0 else ' ')
            i += 1
    return ''.join(out)


def current_axioms():
    """Names of all `axiom` declarations under Scaffold/Mathlib
    (comment interiors masked, so prose never yields phantom names)."""
    names = {}
    for f in (REPO / 'Scaffold' / 'Mathlib').rglob('*.lean'):
        for m in AXIOM_RE.finditer(_mask_block_comments(f.read_text())):
            names[m.group(1)] = f
    return names


def module_name_of(path):
    """`Scaffold/QA/Foo.lean` -> `Scaffold.QA.Foo`."""
    return str(path.relative_to(REPO)).removesuffix('.lean').replace('/', '.')


def scan_tags():
    """Return (entries, problems): entries are dicts
    {file, module, decl, full, target, line}; problems are strings."""
    entries = []
    problems = []
    for path in sorted((REPO / 'Scaffold' / 'QA').rglob('*.lean')):
        lines = path.read_text().splitlines()
        namespace = []
        pending = None   # tag awaiting its declaration, or None
        seen_line = None
        for idx, line in enumerate(lines):
            m = re.match(r'^namespace\s+([A-Za-z_][\w.]*)', line)
            if m:
                namespace.append(m.group(1))
                continue
            if re.match(r'^end\b', line):
                if namespace:
                    namespace.pop()
                continue
            t = TAG_RE.match(line)
            if t:
                pending = t.group(1)
                seen_line = idx + 1
                continue
            if pending is not None:
                d = DECL_RE.match(line)
                if d:
                    if 'private' in line:
                        problems.append(
                            f'{path}:{idx + 1}: @refutes tag targets a '
                            f'private declaration ({d.group(2)}) — private '
                            f'names are invisible to the import-based '
                            f'axiom audit')
                    full = '.'.join(namespace + [d.group(2)]) \
                        if d.group(1) != 'example' else None
                    entries.append({
                        'file': path,
                        'module': module_name_of(path),
                        'decl': d.group(2),
                        'full': full,
                        'target': pending,
                        'line': idx + 1,
                    })
                    pending = None
                    continue
                if seen_line is not None and idx + 1 - seen_line > 60:
                    problems.append(
                        f'{path}:{seen_line}: @refutes tag has no '
                        f'declaration within 60 lines')
                    pending = None
    return entries, problems


def run_print_axioms(entries):
    """Generate one temp Lean file, run `lake env lean`, parse the
    dependency records. Returns ({full_name: [dep names]}, errors)."""
    modules = sorted({e['module'] for e in entries if e['full']})
    names = [e['full'] for e in entries if e['full']]
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td) / 'refutation_independence_audit.lean'
        body = '\n'.join(
            ['-- generated by scripts/check_refutation_independence.py',
             *[f'import {m}' for m in modules],
             '',
             *[f'#print axioms {n}' for n in names],
             ''])
        tmp.write_text(body)
        try:
            proc = subprocess.run(
                ['lake', 'env', 'lean', str(tmp)],
                cwd=REPO, capture_output=True, text=True, timeout=1200)
        except FileNotFoundError:
            return {}, ['lake not found on PATH — run from the repo root']
        except subprocess.TimeoutExpired:
            return {}, ['lake env lean timed out after 1200s']
    out = proc.stdout + proc.stderr
    deps = {}
    for m in re.finditer(
            r"^'([^']+)'\s+depends on axioms:\s*\[(.*?)\]",
            out, re.MULTILINE | re.DOTALL):
        deps[m.group(1)] = [d.strip() for d in m.group(2).split(',')
                            if d.strip()]
    for m in re.finditer(
            r"^'([^']+)'\s+does not depend on any axioms",
            out, re.MULTILINE):
        deps[m.group(1)] = []
    errors = []
    if proc.returncode != 0 or re.search(r'^.*error:', out, re.MULTILINE):
        errors.append('elaboration of the generated #print axioms file '
                      f'failed (exit {proc.returncode}):\n{out.strip()}')
    return deps, errors


def main():
    problems = []
    axioms = current_axioms()
    entries, scan_problems = scan_tags()
    problems.extend(scan_problems)

    if not entries and not problems:
        print('FAIL: no @refutes tags found under Scaffold/QA — the '
              'independence check is vacuous (tags removed?)')
        sys.exit(1)

    for e in entries:
        if e['target'] not in axioms:
            problems.append(
                f"{e['file']}:{e['line']}: @refutes target "
                f"`{e['target']}` is not a currently admitted axiom "
                f"(retired names and theorems take no tag; current "
                f"axioms: {', '.join(sorted(axioms))})")

    checkable = [e for e in entries if e['full'] and e['target'] in axioms]
    deps, run_errors = run_print_axioms(checkable)
    problems.extend(run_errors)

    for e in checkable:
        got = deps.get(e['full'])
        if got is None:
            problems.append(
                f"{e['file']}:{e['line']}: no #print axioms record for "
                f"`{e['full']}` (unknown identifier or parse miss)")
            continue
        hit = [d for d in got
               if d == e['target'] or d.endswith('.' + e['target'])]
        if hit:
            problems.append(
                f"{e['file']}:{e['line']}: refutation "
                f"`{e['full']}` DEPENDS on the axiom it refutes "
                f"({e['target']}) — a refutation cannot consume what it "
                f"refutes; its evidential value is void")

    if problems:
        for p in problems:
            print(f'FAIL: {p}')
        print(f'checked {len(checkable)} tagged declarations against '
              f'{len(axioms)} current axioms')
        sys.exit(1)
    print(f'OK: {len(checkable)} tagged refutation/fence declarations '
          f'checked; none consumes the axiom it refutes '
          f'({len(axioms)} current axioms: {", ".join(sorted(axioms))})')


if __name__ == '__main__':
    main()

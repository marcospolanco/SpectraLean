#!/usr/bin/env python3
"""Lint axiom declarations for consistency.

Three checks:

1. No `axiom` declarations under `Scaffold/Trusted` (the public axiom
   location is `Scaffold/Mathlib`; Trusted is explanatory material).
2. Every `Scaffold/Mathlib` axiom is mentioned in some `index/` file
   (warning tier only).
3. Degenerate-corner guard check
   (`proposals/lint-axiom-degenerate-corner-guards.md`, delivered
   2026-08-28): every `axiom` under `Scaffold/Mathlib` whose effective
   signature carries
   - a `Fintype`-carried type variable used as a matrix/vector index
     (`Matrix V V _`, `V → _`, or a `Fintype.card V` prefactor), with no
     visible `Nonempty V`-style guard, or
   - a `Measure`-typed argument with no visible `IsProbabilityMeasure`,
     `IsFiniteMeasure`, or explicit total-mass-equation guard
   is flagged, unless a per-(axiom, kind) allowlist entry below records
   *why* the corner is accepted. Both of this repository's axiom
   defects of 2026-08-28 (the matrix concentration trio's missing
   `[Nonempty V]`; `hoeffding_lemma`'s missing measure guard) were
   visible in the signature alone; this check makes that state loud at
   admission time instead of waiting for an adversarial fixture.

   This is a linter, not a theorem prover: a finding says "confirm the
   degenerate corner is either guarded or genuinely harmless
   (hypothesis-unsatisfiable) and record which," never "this axiom is
   wrong." Over-flagging is the accepted failure direction; the
   under-flag direction (a real missing guard the pattern misses) is
   the one weighted against.

   Scoping decision, recorded deliberately: literal sample-index
   binders of the form `Fin n → _` over a visible `{n : ℕ}` are *not*
   flagged. Their degeneracy (`n = 0`) is named in the signature itself
   and the two incident repairs both concerned *abstract* index types,
   whose emptiness the signature hides; the proposal's acceptance bar
   likewise expects only `perron_frobenius` and `primitive_power_tendsto`
   to flag on the post-repair tree. If a future axiom with an
   `n`-dependent prefactor breaks at `n = 0`, extend TRIGGER patterns
   with the `Fin n` shape and its guard set (`0 < n`, `NeZero n`,
   `Nonempty (Fin n)`) — this note is the record of that decision, so
   the omission is deliberate rather than silent.

Signature-modeling notes (the parser approximates Lean's elaborator):
- `variable`/`variables` binders are tracked with namespace/section
  scoping (a `variable` inside a closed `namespace` does not leak past
  its `end`), and a variable binder joins an axiom's effective
  signature when the declaration mentions its name, or transitively
  when an already-included binder's type mentions it, mirroring Lean's
  inclusion rule for instance-implicit variables. Six of the ten
  current axioms carry their measure guard in a `variable` line rather
  than in the declaration itself.
- Binders are parsed by bracket matching (not regex splitting), so
  multi-name groups (`{a v : ℝ}`) and anonymous instance groups
  (`[Nonempty V]`) are handled.
"""

import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Allowlist: axiom name -> {finding kind -> recorded reason}.
#
# An entry records WHY the flagged axiom is accepted at its degenerate
# corner. Entries marked provisional cite docstring-level reasoning; the
# Lean-confirmed verdicts are the companion audit's job
# (proposals/audit-perron-frobenius-family-degenerate-corner.md), and an
# entry is upgraded when that lands. An axiom that acquires a real guard
# should have its entry REMOVED so the guard, not the entry, is what
# silences the finding.
# ---------------------------------------------------------------------------

ALLOWLIST = {
    'perron_frobenius': {
        'index-type-guard': (
            'Lean-confirmed 2026-08-28 (proposals/'
            'audit-perron-frobenius-family-degenerate-corner.md): at '
            'Fintype.card V = 0 the hypothesis hex : exists i j, 0 < A i j '
            'is UNSATISFIABLE — an empty index type supplies no witness — '
            'proved unconditionally as Scaffold.LinearAlgebra.QA.'
            'perron_frobenius_hex_unsat_card_zero_QA (standard three '
            'axioms only). The axiom has no instantiation at the '
            'degenerate dimension: safe by unsatisfiability, no guard '
            'needed. The card V = 1 corner was also audited '
            '(perron_frobenius_S1_QA: every hypothesis satisfiable, '
            'conclusion pinned to the hand Perron data 1)'
        ),
    },
    'primitive_power_tendsto': {
        'index-type-guard': (
            'Lean-confirmed 2026-08-28 (proposals/'
            'audit-perron-frobenius-family-degenerate-corner.md): at '
            'Fintype.card V = 0 the hypothesis hπsum : ∑ i, π i = 1 is '
            'UNSATISFIABLE — the empty sum is 0 — proved unconditionally '
            'as Scaffold.QA.SpectralGraph.mass_one_unsat_card_zero_QA '
            '(standard three axioms only). The axiom has no instantiation '
            'at the degenerate dimension: safe by unsatisfiability, no '
            'guard needed. The card V = 1 corner was also audited '
            '(P1_singleton_axiom_QA / P1_singleton_hand_QA: every '
            'hypothesis satisfiable, the limit hand-provable as the '
            'constant sequence)'
        ),
    },
}

# Finding kinds and the guard families each recognizes.
KIND_INDEX = 'index-type-guard'
KIND_MEASURE = 'measure-guard'

_OPENERS = {'{': '}', '[': ']', '(': ')'}
_CLOSERS = {'}': '{', ']': '[', ')': '('}


def _match_bracket(text, start):
    """Return the index of the bracket matching text[start] (an opener),
    or -1 if unmatched. Respects nesting across the three bracket kinds."""
    depth = []
    for i in range(start, len(text)):
        c = text[i]
        if c in _OPENERS:
            depth.append(c)
        elif c in _CLOSERS:
            if not depth or depth[-1] != _CLOSERS[c]:
                return -1
            depth.pop()
            if not depth:
                return i
    return -1


def _split_top_level_colon(content):
    """Split binder content at the first depth-0 colon: (names, type).
    Returns (None, content) when there is no top-level colon (an
    anonymous binder, e.g. `[Nonempty V]`)."""
    depth = []
    for i, c in enumerate(content):
        if c in _OPENERS:
            depth.append(c)
        elif c in _CLOSERS:
            if depth:
                depth.pop()
        elif c == ':' and not depth:
            return content[:i], content[i + 1:]
    return None, content


def parse_binders(text):
    """Parse a binder list like `{a : T} [I : T'] (b : T'') {x y : U}`
    into a list of dicts {name, kind, type}. Anonymous binders (no
    colon) carry name None with the whole content as their type."""
    binders = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in _OPENERS:
            close = _match_bracket(text, i)
            if close < 0:
                break
            content = text[i + 1:close]
            kind = {'{': 'implicit', '[': 'instance', '(': 'explicit'}[c]
            names, type_part = _split_top_level_colon(content)
            if names is None:
                binders.append({'name': None, 'kind': kind,
                                'type': content.strip()})
            else:
                for name in names.split():
                    binders.append({'name': name, 'kind': kind,
                                    'type': type_part.strip()})
            i = close + 1
        else:
            i += 1
    return binders


_TYPE_RE = re.compile(r'^(Type\*?|Type\s+\w+|Sort\s+\S+)$')


def _is_type_binder(b):
    return b['name'] is not None and bool(_TYPE_RE.match(b['type']))


_CMD_RE = re.compile(
    r'^(/--|/-|@\[|theorem\b|lemma\b|axiom\b|def\b|noncomputable\b|'
    r'instance\b|structure\b|example\b|abbrev\b|end\b|namespace\b|'
    r'section\b|variable\b|variables\b|open\b|import\b|export\b|#)')


def _extract_axioms(lines):
    """Yield (line_index, name, declaration_text) for every `axiom`
    declaration, where declaration_text spans to the first blank line or
    next top-level command."""
    results = []
    i = 0
    n = len(lines)
    while i < n:
        m = re.match(r'^axiom\s+(\w+)', lines[i])
        if m:
            decl = [lines[i]]
            j = i + 1
            while j < n and lines[j].strip() and not _CMD_RE.match(lines[j]):
                decl.append(lines[j])
                j += 1
            results.append((i, m.group(1), '\n'.join(decl)))
            i = j
        else:
            i += 1
    return results


def _scan_variables(lines):
    """Track namespace/section-scoped `variable` binders line by line.
    Returns {line_index: [active binder dicts up to and including that
    line]} evaluated lazily per axiom position."""
    active = []          # list of binder dicts currently in scope
    frames = []          # stack of lists of binders introduced per frame

    def open_frame():
        frames.append([])

    def close_frame():
        if frames:
            for b in frames.pop():
                if b in active:
                    active.remove(b)

    snapshots = {}
    for idx, line in enumerate(lines):
        stripped = line.strip()
        m = re.match(r'^(namespace|section)\b', stripped)
        if m:
            open_frame()
            snapshots[idx] = list(active)
            continue
        m = re.match(r'^end\b', stripped)
        if m and not line[0].isspace():
            close_frame()
            snapshots[idx] = list(active)
            continue
        m = re.match(r'^variables?\s+(.*)$', stripped)
        if m:
            new = parse_binders(m.group(1))
            active.extend(new)
            if frames:
                frames[-1].extend(new)
            snapshots[idx] = list(active)
            continue
        snapshots[idx] = list(active)
    return snapshots


def _effective_signature(decl_text, active_vars):
    """Compute the axiom's effective signature: the declaration text
    plus the variable binders Lean would include. Inclusion: a variable
    joins when its name is mentioned in the declaration, or appears in
    the type of an already-included binder (transitive); instance
    binders join when their type mentions an included name. Returns
    (inline_binders, included_binders, guard_text)."""
    mentioned = set(re.findall(r"[^\W\d][\w']*", decl_text))
    included = []
    changed = True
    while changed:
        changed = False
        for b in active_vars:
            if b in included:
                continue
            names_in_type = set(re.findall(
                r"[^\W\d][\w']*", b['type'] or ''))
            if (b['name'] is not None and b['name'] in mentioned) or \
               (b['name'] is None and b['kind'] == 'instance' and
                    names_in_type & mentioned):
                included.append(b)
                mentioned |= names_in_type
                changed = True
                continue
            # Transitive: any binder whose type mentions an included
            # name (mirrors Lean pulling in a variable free in an
            # included binder's type).
            free_in_included = set()
            for inc in included:
                free_in_included |= set(re.findall(
                    r"[^\W\d][\w']*", inc['type'] or ''))
                if inc['name'] is not None:
                    free_in_included.add(inc['name'])
            if (b['name'] is not None and b['name'] in free_in_included) or \
               (names_in_type & free_in_included):
                included.append(b)
                mentioned |= names_in_type
                changed = True
    # Inline binders: everything after the axiom name up to the top-level
    # conclusion colon on the declaration's first region. Approximation:
    # parse binders from the whole declaration text (conclusion colons
    # and set-builder braces may yield spurious entries; those carry
    # names that can only add guards, never triggers, since triggers
    # require a Type-typed binder with a Fintype instance elsewhere).
    inline = parse_binders(decl_text)
    binder_text = ' '.join(
        f"{b['name']} : {b['type']}" if b['name'] is not None
        else f"_ : {b['type']}"
        for b in included + inline)
    return inline, included, decl_text + '\n' + binder_text


def check_degenerate_corner_guards(root='.'):
    """The degenerate-corner guard check over `root`'s Scaffold/Mathlib
    tree. Returns (hard_issues, allowlisted_notes)."""
    issues = []
    notes = []
    base = Path(root) / 'Scaffold' / 'Mathlib'
    if not base.exists():
        return issues, notes
    for lean_file in sorted(base.rglob('*.lean')):
        lines = lean_file.read_text().splitlines()
        snapshots = _scan_variables(lines)
        for idx, name, decl_text in _extract_axioms(lines):
            active_vars = snapshots.get(max(idx - 1, 0), [])
            inline, included, guard_text = _effective_signature(
                decl_text, active_vars)
            all_binders = inline + included
            binder_types = ' '.join(b['type'] or '' for b in all_binders)

            # Kind 1: Fintype-carried index type variable with no
            # Nonempty guard.
            type_vars = [b['name'] for b in all_binders if _is_type_binder(b)]
            for tv in type_vars:
                if not re.search(rf'Fintype\s+{re.escape(tv)}\b', binder_types):
                    continue
                trigger = (re.search(rf'Matrix\s+{re.escape(tv)}\b',
                                     guard_text) or
                           re.search(rf'\b{re.escape(tv)}\s*→', guard_text) or
                           re.search(rf'Fintype\.card\s+{re.escape(tv)}\b',
                                     guard_text))
                if not trigger:
                    continue
                if re.search(rf'Nonempty\s+{re.escape(tv)}\b', guard_text):
                    continue
                _record(issues, notes, lean_file, idx, name, KIND_INDEX,
                        f'Fintype-carried index type variable `{tv}` '
                        f'(Matrix/vector-indexed, or a Fintype.card '
                        f'prefactor) with no visible `Nonempty {tv}` guard')

            # Kind 2: Measure-typed argument with no probability-style
            # guard. Only measures whose name the declaration actually
            # uses (or that it binds inline) are in scope.
            decl_mentions = set(re.findall(
                r"[^\W\d][\w']*", decl_text))
            for b in all_binders:
                if b['name'] is None or \
                        not re.match(r'^Measure\b', b['type'] or ''):
                    continue
                mname = b['name']
                if b not in inline and mname not in decl_mentions:
                    continue
                guarded = (re.search(
                    rf'IsProbabilityMeasure\s+{re.escape(mname)}\b',
                    guard_text) or re.search(
                    rf'IsFiniteMeasure\s+{re.escape(mname)}\b',
                    guard_text) or re.search(
                    rf'{re.escape(mname)}\s+(Set\.)?univ\s*=\s*1',
                    guard_text))
                if guarded:
                    continue
                _record(issues, notes, lean_file, idx, name, KIND_MEASURE,
                        f'Measure-typed argument `{mname}` with no visible '
                        f'IsProbabilityMeasure / IsFiniteMeasure / '
                        f'total-mass-equation guard')
    return issues, notes


def _record(issues, notes, lean_file, idx, name, kind, description):
    entry = ALLOWLIST.get(name, {}).get(kind)
    location = f'{lean_file}:{idx + 1}'
    if entry is not None:
        notes.append(
            f'Allowlisted: {location}: axiom {name} — {kind} finding '
            f'accepted: {entry}')
    else:
        issues.append(
            f'{location}: axiom {name} has a {description} — confirm the '
            f'degenerate corner is either guarded or genuinely harmless '
            f'(hypothesis-unsatisfiable) and record which (allowlist entry '
            f'in scripts/lint_axioms.py, kind `{kind}`)')


def check_axiom_in_public_api():
    """Check that no axioms are in the wrong location."""
    issues = []

    # Check for axioms in Trusted (should use theorem := by sorry)
    trusted_dir = Path('Scaffold/Trusted')
    if trusted_dir.exists():
        for lean_file in trusted_dir.rglob('*.lean'):
            with open(lean_file, 'r') as f:
                content = f.read()
            if re.search(r'^axiom\s+', content, re.MULTILINE):
                issues.append(f"{lean_file}: Found 'axiom' in Trusted directory (use 'theorem := by sorry')")

    return issues

def check_index_coverage():
    """Check that axioms are documented in index files."""
    issues = []

    # Extract all axiom names from Lean files
    axiom_names = set()
    for lean_file in Path('Scaffold/Mathlib').rglob('*.lean'):
        with open(lean_file, 'r') as f:
            content = f.read()
        for match in re.finditer(r'^axiom\s+(\w+)', content, re.MULTILINE):
            axiom_names.add(match.group(1))

    # Check if mentioned in index files (warning only)
    for axiom_name in axiom_names:
        found = False
        for index_file in Path('index').rglob('*.md'):
            with open(index_file, 'r') as f:
                if axiom_name in f.read():
                    found = True
                    break
        if not found:
            issues.append(f"Warning: Axiom '{axiom_name}' not found in index files")

    return issues

def main():
    """Run all lint checks."""
    issues = []

    # Check for axioms in wrong location
    issues.extend(check_axiom_in_public_api())

    # Check index coverage (warnings)
    issues.extend(check_index_coverage())

    # Degenerate-corner guard check (allowlisted findings are notes,
    # unallowlisted findings fail the lint)
    guard_issues, guard_notes = check_degenerate_corner_guards()
    issues.extend(guard_issues)

    if issues or guard_notes:
        for note in guard_notes:
            print(note)
        for issue in issues:
            print(issue)
        if any('Warning' not in i for i in issues):
            sys.exit(1)
    else:
        print("No lint issues found!")

if __name__ == '__main__':
    main()

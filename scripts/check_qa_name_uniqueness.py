#!/usr/bin/env python3
"""QA name-collision guard (2026-09-05, proposals/qa-name-collision-guard.md).

Fails when any *named* top-level declaration (theorem/lemma/def/abbrev/
instance/opaque/structure/inductive) is declared in more than one module
under ``Scaffold/QA/`` within the same namespace — the latent defect
class behind the 2026-09-05 ``edgeAdj`` lattice repair: QA modules are
leaf builds, so two modules defining the same name each elaborate fine
and only fail when some future module imports both ("environment
already contains ..."), typically a cross-family reconciliation wrapper
that a later run is trying to write.

The check is the ``lint_axioms.py`` degenerate-corner-guard pattern
applied to the QA lattice: every *residual* cross-module duplicate is
recorded in ``ALLOWLIST`` with its exact sorted file set, and the check
fails if (a) a NEW collision appears, or (b) any allowlisted name's
file set drifts (a rename landing or a new file joining a collision) —
either way the disposition is settled deliberately at that boundary,
not discovered later by an import failure. Residual pairs are repaired
on demand per the ``edgeAdj`` recipe (map reference domains from the
import graph first; check for shelf-level same-named API before
renaming QA fixtures; expect QA modules outside the default build
target to need explicit rebuilds — ``check_build_completeness.py`` is
the safety net).

Doc comments (`/- ... -/`) and line comments (`-- ...`) are stripped
before matching, so prose lines beginning with e.g. "theorem and ..."
are never counted. Anonymous instances (no name) are not counted.
``Scaffold/Mathlib`` is out of scope: the shelf is co-imported by the
umbrella build, so a shelf-level collision fails the build immediately
rather than staying latent.
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
QA_ROOT = REPO_ROOT / "Scaffold" / "QA"

# Residual cross-module duplicate names, recorded at the 2026-09-05
# survey. Each entry: name -> exact sorted set of files declaring it.
# Disposition: latent (no co-import consumer yet); repair on demand per
# the edgeAdj recipe. Any drift here fails until this table is settled.
ALLOWLIST: dict[str, frozenset[str]] = {
    # Calibrated by the 2026-09-05 survey (24 names). Mechanisms:
    # identical-body duplicates (asymAdj2, edgeAdj2, pathAdj family —
    # the same fixture redeclared per file, the pre-2026-09-04
    # "no QA imports" convention's cost), different-body duplicates
    # (k2Adj, path3Adj, triAdj — same graph, different spellings), and
    # shared two-point pin helpers (list_two_eq, two_point_pin,
    # two_point_pin_of_sum_prod, constantStream).
    "Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA.list_two_eq":
        frozenset({"Scaffold.QA.Perturbation.DavisKahan_QA",
                   "Scaffold.QA.Perturbation.ProjectionGap_QA",
                   "Scaffold.QA.Perturbation.Weyl_QA"}),
    "SpectralGraphTheory.Derived.QA.constantStream":
        frozenset({"Scaffold.QA.Derived.EventStream_QA",
                   "Scaffold.QA.Derived.ProjectorDrift_QA"}),
    "SpectralGraphTheory.Derived.QA.constantStream_increment_zero_QA":
        frozenset({"Scaffold.QA.Derived.EventStream_QA",
                   "Scaffold.QA.Derived.ProjectorDrift_QA"}),
    "SpectralGraphTheory.QA.asymAdj2":
        frozenset({"Scaffold.QA.SpectralGraph.Exhaustive_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.edgeAdj2":
        frozenset({"Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.edgeAdj2_deg":
        frozenset({"Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.k2Adj":
        frozenset({"Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.k2Adj_nonneg":
        frozenset({"Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.list_two_eq":
        frozenset({"Scaffold.QA.SpectralGraph.Cheeger_QA",
                   "Scaffold.QA.SpectralGraph.CourantFischer_QA",
                   "Scaffold.QA.SpectralGraph.Heat_QA",
                   "Scaffold.QA.SpectralGraph.Interlacing_QA",
                   "Scaffold.QA.SpectralGraph.IrregularCheeger_QA"}),
    "SpectralGraphTheory.QA.path3Adj":
        frozenset({"Scaffold.QA.SpectralGraph.CourantFischer_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.path3Adj_nonneg":
        frozenset({"Scaffold.QA.SpectralGraph.CourantFischer_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.path3Adj_symmetric":
        frozenset({"Scaffold.QA.SpectralGraph.CourantFischer_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.pathAdj":
        frozenset({"Scaffold.QA.SpectralGraph.Cuts_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.pathAdj_deg_one":
        frozenset({"Scaffold.QA.SpectralGraph.Cuts_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.pathAdj_deg_pos":
        frozenset({"Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.pathAdj_deg_two":
        frozenset({"Scaffold.QA.SpectralGraph.Cuts_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.pathAdj_deg_zero":
        frozenset({"Scaffold.QA.SpectralGraph.Cuts_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.pathAdj_isSymm":
        frozenset({"Scaffold.QA.SpectralGraph.Cuts_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Normalized_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.path_vol_QA":
        frozenset({"Scaffold.QA.SpectralGraph.Mixing_QA",
                   "Scaffold.QA.SpectralGraph.Stationary_QA"}),
    "SpectralGraphTheory.QA.rayleigh_zero_QA":
        frozenset({"Scaffold.QA.SpectralGraph.Basic_QA",
                   "Scaffold.QA.SpectralGraph.Variational_QA"}),
    "SpectralGraphTheory.QA.triAdj":
        frozenset({"Scaffold.QA.SpectralGraph.ElectricalFlow_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA"}),
    "SpectralGraphTheory.QA.triAdj_isSymm":
        frozenset({"Scaffold.QA.SpectralGraph.ElectricalFlow_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA"}),
    "SpectralGraphTheory.QA.triAdj_nonneg":
        frozenset({"Scaffold.QA.SpectralGraph.ElectricalFlow_QA",
                   "Scaffold.QA.SpectralGraph.Mixing_QA"}),
    "SpectralGraphTheory.QA.two_point_pin":
        frozenset({"Scaffold.QA.SpectralGraph.Cheeger_QA",
                   "Scaffold.QA.SpectralGraph.Heat_QA"}),
    "Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA.two_point_pin_of_sum_prod":
        frozenset({"Scaffold.QA.Perturbation.DavisKahan_QA",
                   "Scaffold.QA.Perturbation.ProjectionGap_QA",
                   "Scaffold.QA.Perturbation.Weyl_QA"}),
}


DECL_RE = re.compile(
    r"^(?:@\[[^\n]*\]\s*\n?[ \t]*)?"  # optional @[attr]
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|instance|opaque|structure|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)"
)

DOC_COMMENT_RE = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def strip_comments(text: str) -> str:
    text = DOC_COMMENT_RE.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    # A `--` inside a string literal would be mangled, but QA fixtures
    # do not carry string literals in declaration position.
    return LINE_COMMENT_RE.sub("", text)


def module_names(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT).with_suffix("")
    return ".".join(rel.parts)


def declarations(path: Path) -> list[tuple[str, str]]:
    """Yield (namespace, name) for every named top-level declaration."""
    text = strip_comments(path.read_text())
    ns_stack: list[tuple[str, str]] = []  # (kind, name); kind in {ns, sec}
    out: list[tuple[str, str]] = []
    for line in text.splitlines():
        stripped = line.strip()
        m = re.match(r"^namespace\s+([A-Za-z_][\w.]*)", stripped)
        if m:
            ns_stack.append(("ns", m.group(1)))
            continue
        m = re.match(r"^section\s+([A-Za-z_]\w*)", stripped)
        if m:
            ns_stack.append(("sec", m.group(1)))
            continue
        if re.match(r"^section\b", stripped):
            ns_stack.append(("sec", ""))
            continue
        m = re.match(r"^end\b\s*(.*)$", stripped)
        if m:
            target = m.group(1).strip()
            if target == "":
                if ns_stack:
                    ns_stack.pop()
            else:
                # pop through to the matching named entry (namespace or
                # named section); tolerate unmatched ends.
                for k in range(len(ns_stack) - 1, -1, -1):
                    if ns_stack[k][1] == target:
                        del ns_stack[k:]
                        break
            continue
        dm = DECL_RE.match(line)
        if dm:
            ns = ".".join(n for kind, n in ns_stack if kind == "ns")
            out.append((ns, dm.group(2)))
    return out


def main() -> int:
    by_name: dict[tuple[str, str], set[str]] = defaultdict(set)
    for path in sorted(QA_ROOT.rglob("*.lean")):
        mod = module_names(path)
        for ns, name in declarations(path):
            by_name[(ns, name)].add(mod)

    failures: list[str] = []
    residual_changed: list[str] = []
    for (ns, name), files in sorted(by_name.items()):
        if len(files) < 2:
            continue
        key = name if ns == "" else f"{ns}.{name}"
        allowed = ALLOWLIST.get(key)
        if allowed is None:
            failures.append(
                f"NEW collision: {key} declared in {len(files)} modules:\n"
                + "".join(f"    {f}\n" for f in sorted(files))
                + "  Rename file-uniquely (edgeAdj recipe) or settle an\n"
                "  allowlist entry recording why the pair is accepted."
            )
        elif frozenset(allowed) != files:
            residual_changed.append(
                f"ALLOWLIST DRIFT: {key}\n"
                f"    recorded: {sorted(allowed)}\n"
                f"    actual:   {sorted(files)}\n"
                "  Update the allowlist deliberately (a rename landed or a\n"
                "  new file joined the collision)."
            )
        else:
            print(f"allowlisted residual: {key} ({len(files)} modules)")

    for msg in failures + residual_changed:
        print(msg, file=sys.stderr)
    if failures or residual_changed:
        print(
            f"FAIL: {len(failures)} new collision(s), "
            f"{len(residual_changed)} allowlist drift(s).",
            file=sys.stderr,
        )
        return 1
    print("QA name-collision guard: clean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

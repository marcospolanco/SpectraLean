#!/usr/bin/env python3
"""Reconcile Lake build artifacts against on-disk sources.

A successful `lake build` exit status alone is not evidence that every
`.lean` file in the working tree was checked: the default target builds
the umbrella `Scaffold.lean` and everything reachable from it, so a file
that is merely *present on disk* but not (yet) imported by the umbrella —
for example a QA module drafted seconds ago by an interrupted run — is
silently absent from the checked set rather than reported as an error.
That exact false positive occurred in this repository during the
2026-08-24/25 session (see `proposals/verify-build-completeness.md`).

This script is the independent cross-check: it enumerates every library
source file (`Scaffold.lean` plus everything under `Scaffold/`, excluding
git-ignored scratch), computes the expected `.olean` artifact path under
`.lake/build/lib/`, and fails with a nonzero exit listing every file whose
artifact is *missing* or *mtime-stale* (an artifact older than its source
is the signature of an edit that no build has actually processed).

Semantics, calibrated against Lake's measured behavior on the pinned
toolchain (v4.14.0; see the delivery record of
`proposals/verify-build-completeness.md`):

* MISSING — the module has never been elaborated by any build invocation
  in this workspace. Unambiguous hard failure; the incident's primary
  signature (an interrupted run's freshly drafted file).
* STALE — the source's mtime postdates the artifact. Two subcases, and
  the filesystem alone cannot tell them apart: (a) a *content* edit no
  build has processed — the incident's variant, and a real catch: this
  check found a live one on its first run (an 08-20 edit whose artifact
  stayed 08-18); (b) a byte-identical roundtrip (git stash/checkout,
  editor save) — Lake's up-to-date check is content-hash based and will
  *skip* such a module without rewriting the artifact, so the mtime gap
  is unfixable by a plain rebuild. Remediation that always terminates:
  run `lake build <module>` (rewrites subcase (a)); if Lake reports the
  module up to date yet the check still flags it, remove the derived
  artifact (`.lake/build/lib/<path>.olean` and its `.hash`/`.trace`/
  `.ilean` siblings) and rebuild once — forcing re-elaboration, which
  both refreshes the timestamp and re-proves the current content
  compiles. Deleting artifacts is safe: they are gitignored derived
  data.

It is deliberately NOT a re-implementation of Lean's type checker, does
not read the lakefile, and does not invoke Lean: a source file with no
import relationship to the umbrella still gets an artifact whenever its
explicit `lake build <module>` target has run, and that is the
reconciliation this check performs — "everything on disk has been
built" — which is a necessary, not sufficient, condition for
verification.

Usage:
    python3 scripts/check_build_completeness.py [--root REPO_ROOT]

Exit codes:
    0  complete — every source file has a fresh artifact
    1  incomplete — at least one missing or stale artifact (listed)
    2  operational error (bad root, unreadable paths)
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

BUILD_LIB_SUBDIR = Path(".lake") / "build" / "lib"
LIBRARY_ROOT_SOURCE = "Scaffold.lean"
SOURCE_SUBTREE = "Scaffold"
IGNORABLE_TOP_LEVELS = {"wip", ".lake", ".opencode", ".git"}

EXIT_COMPLETE = 0
EXIT_INCOMPLETE = 1
EXIT_ERROR = 2


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parent.parent


def enumerate_sources(root: Path) -> list[Path]:
    """Every library source file the completeness check covers.

    The set is the umbrella `Scaffold.lean` (the default target itself,
    so it must always have an artifact) plus every `.lean` file under
    `Scaffold/`. Git-ignored scratch trees (`wip/`) are excluded: they
    are not library modules and are never expected to build.
    """
    sources: list[Path] = []

    umbrella = root / LIBRARY_ROOT_SOURCE
    if umbrella.is_file():
        sources.append(umbrella)

    subtree = root / SOURCE_SUBTREE
    if not subtree.is_dir():
        return sources

    for path in sorted(subtree.rglob("*.lean")):
        # Defensive: `wip/` lives at the repo root today, but any future
        # scratch directory nested under Scaffold/ stays out of scope the
        # same way, and .lake must never be re-entered if relocated.
        rel = path.relative_to(root)
        if rel.parts and rel.parts[0] in IGNORABLE_TOP_LEVELS:
            continue
        if any(part in IGNORABLE_TOP_LEVELS for part in rel.parts):
            continue
        sources.append(path)

    return sources


def expected_artifact(root: Path, source: Path) -> Path:
    return root / BUILD_LIB_SUBDIR / source.relative_to(root).with_suffix(".olean")


def classify(root: Path, source: Path) -> tuple[str, str]:
    """Return (status, detail) for one source file.

    status is one of "fresh", "stale", "missing". mtime comparison uses
    nanosecond resolution and flags only *strictly older* artifacts: an
    artifact written in the same filesystem tick as its source is the
    normal outcome of a build that just processed it.
    """
    artifact = expected_artifact(root, source)
    if not artifact.is_file():
        return "missing", f"no artifact at {artifact.relative_to(root)}"
    src_ns = source.stat().st_mtime_ns
    art_ns = artifact.stat().st_mtime_ns
    if art_ns < src_ns:
        src_s = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(src_ns / 1e9))
        art_s = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(art_ns / 1e9))
        return (
            "stale",
            f"artifact {artifact.relative_to(root)} mtime {art_s} "
            f"older than source mtime {src_s}",
        )
    return "fresh", ""


def main(argv: list[str]) -> int:
    root: Path
    if len(argv) == 1 and argv[0] == "--help":
        print(__doc__)
        return EXIT_COMPLETE
    args = argv[1:]
    if not args:
        root = repo_root_from_script()
    elif len(args) == 2 and args[0] == "--root":
        root = Path(args[1]).resolve()
    else:
        print(
            "usage: check_build_completeness.py [--root REPO_ROOT]",
            file=sys.stderr,
        )
        return EXIT_ERROR

    if not root.is_dir():
        print(f"error: repository root {root} is not a directory", file=sys.stderr)
        return EXIT_ERROR

    sources = enumerate_sources(root)
    if not sources:
        print(
            "error: no library sources found under "
            f"{root / SOURCE_SUBTREE} — wrong root?",
            file=sys.stderr,
        )
        return EXIT_ERROR

    missing: list[tuple[Path, str]] = []
    stale: list[tuple[Path, str]] = []
    for source in sources:
        status, detail = classify(root, source)
        if status == "missing":
            missing.append((source, detail))
        elif status == "stale":
            stale.append((source, detail))

    total = len(sources)
    fresh = total - len(missing) - len(stale)

    for source, detail in missing:
        print(f"MISSING {source.relative_to(root)}: {detail}")
    for source, detail in stale:
        print(f"STALE   {source.relative_to(root)}: {detail}")

    print(
        f"{total} source files, {fresh} fresh artifacts, "
        f"{len(stale)} stale, {len(missing)} missing"
    )

    if missing or stale:
        print(
            "build completeness FAILED: the build artifacts do not cover every "
            "on-disk source. For each listed module run `lake build <module>`; "
            "if Lake reports it up to date yet this check still flags it "
            "(byte-identical roundtrip — Lake's up-to-date check is "
            "content-based), remove the artifact under .lake/build/lib/ and "
            "rebuild once to force re-elaboration.",
            file=sys.stderr,
        )
        return EXIT_INCOMPLETE
    return EXIT_COMPLETE


if __name__ == "__main__":
    sys.exit(main(sys.argv))

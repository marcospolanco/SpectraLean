#!/usr/bin/env python3
"""Reconcile the transit map's two data tables against ground truth.

`scripts/generate_scaffold_map_svg.py` (hardcoded `CORE`/`SPOKES`, the
source of `docs/scaffold_map.svg`) and `docs/scaffold_map.html` (an
independent `CORE`/`SPOKES` copy inside its inline script) are
hand-maintained side documents, not derived artifacts. The pre-commit
hook regenerates the SVG's *rendering* on every commit but has no
connection to any proposal's actual status, so both tables drifted
silently for days (see `proposals/verify-scaffold-map-freshness.md`:
eight stale nodes, a stats line two axioms and 1200+ QA declarations
behind, and a note contradicting `proposals/README.md`'s own corrected
finding) while appearing fresh. This script is the mechanical fix, the
same pattern as `scripts/check_build_completeness.py`: reconcile
against source, fail loud.

Two tiers:

Tier 1 (hard fail, zero heuristics):
  1. Every `Repo-wide: N explicit axioms · M QA declarations · K
     sorries` stamp embedded in either map file must match the numbers
     `scripts/generate_qa_scoreboard.py` actually wrote into
     `docs/5_QA_SCOREBOARD.md` — the scoreboard is parsed, never
     re-hardcoded here.
  2. The SVG script's station data and the HTML's station data must
     agree pairwise, by name, on status AND on the `source` field. A
     station present in one file and missing from the other is a
     failure, not a silent skip.

Tier 2 (a staleness signal, not an oracle — it fails the check so a
human or agent must look, and NEVER auto-edits a status):
  3. Each station may carry a `source` naming the `proposals/*.md` file
     whose status it tracks (`None` where none exists — classical core
     entries, admitted-axiom stations with no delivery proposal, or
     deliberately unlinked mixed-status files such as Foster's Theorem).
     The proposal's `**Status:**` paragraph is keyword-classified:
       gated-words ("gated", "blocked", "requires an operator decision",
       "human decision required", "decision required") take precedence
       → expect station tier `gated`; then
       "complete"/"delivered" → expect `proved` or `axiom`
       (axiom stations with delivered admission proposals are sound);
       then a bare "Proposed" → expect `open` or `gated`; anything else
       is no-claim and skipped.
  4. A declared tier outside the expected set is a finding: file,
     station, declared tier, expected bucket, the proposal's own status
     text. Picking `proved` vs `axiom` vs `progress` for a genuinely
     ambiguous delivery is the judgment this repository reserves for
     the run doing the actual status update — hence the sanctioned
     narrowings, recorded here rather than hidden: `progress` never
     appears in an expectation set (no keyword distinguishes "partly
     delivered, in progress" from "delivered"), and the proposed bucket
     accepts both `open` and `gated` (the authorized-vs-gated
     distinction lives in `proposals/README.md`'s priority table, not in
     the proposal's own status prose).

Known limits, deliberately out of scope (the proposal's Non-goals):
  * Note *text* contradicted by evidence (the Matrix Chernoff Bridge
    incident) has no cheap general rule and stays a documented manual
    example, not an automated check.
  * Missing stations for delivered results (Ramanujan ceiling, Fiedler
    Davis–Kahan, ...) are a completeness gap for a human to place, not
    something this script invents nodes for; they surface only through
    the explicit no-source coverage list.

Usage:
    python3 scripts/check_scaffold_map_freshness.py [--root REPO_ROOT]

Exit codes:
    0  fresh — both tables agree with each other and with the scoreboard,
       and every linked proposal's status bucket admits its station tier
    1  findings — at least one reconciliation failure (listed)
    2  operational error (missing files, unparseable tables)
"""

from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

SCOREBOARD = Path("docs") / "5_QA_SCOREBOARD.md"
SVG_GENERATOR = Path("scripts") / "generate_scaffold_map_svg.py"
HTML_MAP = Path("docs") / "scaffold_map.html"
PROPOSALS = Path("proposals")

STATUS_TIERS = {"proved", "axiom", "progress", "open", "gated"}

GATED_WORDS = (
    "gated",
    "blocked",
    "requires an operator decision",
    "human decision required",
    "decision required",
)
DELIVERED_WORDS = ("complete", "delivered")

EXPECT_FOR_BUCKET = {
    "gated": {"gated"},
    "delivered": {"proved", "axiom"},
    "proposed": {"open", "gated"},
}

# Anchored by literal suffixes rather than "no digits in between": the
# stamps embed HTML entities ('&#183;') whose digits must not be
# mistaken for the counts.
STAMP_RE = re.compile(
    r"Repo-wide:\s*(\d+)\s*explicit axioms\b.*?"
    r"(\d+)\s*QA declarations\b.*?(\d+)\s*sorries\b"
)

EXIT_FRESH = 0
EXIT_FINDINGS = 1
EXIT_ERROR = 2


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parent.parent


# ---------------------------------------------------------------- Tier 1a


def parse_scoreboard(root: Path) -> tuple[int, int, int]:
    """(qa_declarations, explicit_axioms, sorry_tokens) from the generated
    metrics table of docs/5_QA_SCOREBOARD.md — the single source of truth
    for repo-wide numbers."""
    path = root / SCOREBOARD
    text = path.read_text(encoding="utf-8")
    rows = {
        "qa": r"\|\s*QA theorem/lemma declarations\s*\|\s*(\d+)\s*\|",
        "axioms": r"\|\s*Explicit axioms in `Scaffold/Mathlib`\s*\|\s*(\d+)\s*\|",
        "sorries": r"\|\s*`sorry`/`admit` tokens in QA code\s*\|\s*(\d+)\s*\|",
    }
    values = {}
    for key, pattern in rows.items():
        m = re.search(pattern, text)
        if not m:
            raise ValueError(f"scoreboard row not found: {key} ({path})")
        values[key] = int(m.group(1))
    return values["qa"], values["axioms"], values["sorries"]


def check_stamps(text: str, where: str, qa: int, axioms: int, sorries: int,
                 findings: list[str]) -> None:
    """Every stamp occurrence in `text` must carry the scoreboard numbers."""
    stamps = list(STAMP_RE.finditer(text))
    if not stamps:
        findings.append(
            f"{where}: no 'Repo-wide: N explicit axioms · M QA declarations · "
            f"K sorries' stamp found — the stats line was deleted, not updated"
        )
        return
    for m in stamps:
        got = (int(m.group(1)), int(m.group(2)), int(m.group(3)))
        if got != (axioms, qa, sorries):
            findings.append(
                f"{where}: stats stamp reads {got[0]} explicit axioms · "
                f"{got[1]} QA declarations · {got[2]} sorries, scoreboard "
                f"says {axioms} · {qa} · {sorries}"
            )


# ---------------------------------------------------------------- Tier 1b


def parse_svg_tables(root: Path) -> list[tuple[str, str, str | None]]:
    """(name, status, source) for every station in the SVG generator's
    CORE + SPOKES data tables, parsed as Python (ast.literal_eval), so a
    syntax error in the data is an operational error, not a silent skip.
    CORE roster entries are 'proved' by construction."""
    path = root / SVG_GENERATOR
    tree = ast.parse(path.read_text(encoding="utf-8"))
    assigns = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ("CORE", "SPOKES"):
                    assigns[target.id] = ast.literal_eval(node.value)
    missing = {"CORE", "SPOKES"} - set(assigns)
    if missing:
        raise ValueError(f"{path}: missing data table(s) {sorted(missing)}")

    stations: list[tuple[str, str, str | None]] = []
    for entry in assigns["CORE"]:
        name, source = entry
        stations.append((name, "proved", source))
    for _axis, _sub, entries in assigns["SPOKES"]:
        for name, status, source in entries:
            stations.append((name, status, source))
    return stations


def _extract_balanced(text: str, start: int) -> tuple[int, int]:
    """Index range of the brace/bracket-delimited block starting at
    `start`, string-literal aware (notes embed `{2t}` inside quotes)."""
    open_ch = text[start]
    close_ch = {"{": "}", "[": "]"}[open_ch]
    depth = 0
    in_string = False
    i = start
    while i < len(text):
        ch = text[i]
        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
        elif ch == '"':
            in_string = True
        elif ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return start, i
        i += 1
    raise ValueError(f"unbalanced block starting at offset {start}")


def _skip_string(text: str, start: int) -> int:
    """Index just past the string literal opening at `start`."""
    i = start + 1
    while i < len(text):
        if text[i] == "\\":
            i += 2
        elif text[i] == '"':
            return i + 1
        else:
            i += 1
    raise ValueError(f"unterminated string literal at offset {start}")


def _collect_objects(block: str, out: list[str]) -> None:
    """Recursively collect the source text of every {...} object literal
    in a data region (string-literal aware), outer before inner."""
    i = 0
    while i < len(block):
        ch = block[i]
        if ch == "{":
            start, end = _extract_balanced(block, i)
            obj = block[start + 1:end]
            out.append(obj)
            _collect_objects(obj, out)
            i = end + 1
        elif ch == "[":
            start, end = _extract_balanced(block, i)
            _collect_objects(block[start + 1:end], out)
            i = end + 1
        elif ch == '"':
            i = _skip_string(block, i)
        else:
            i += 1


def _own_keys(obj: str) -> str:
    """The object's own key/value text with nested {...}/[...] blocks
    blanked, so a station nested inside a spoke object is not mistaken
    for the spoke's own key."""
    out: list[str] = []
    i = 0
    while i < len(obj):
        ch = obj[i]
        if ch in "{[":
            _, end = _extract_balanced(obj, i)
            out.append(" " * (end + 1 - i))
            i = end + 1
        elif ch == '"':
            end = _skip_string(obj, i)
            out.append(obj[i:end])
            i = end
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def parse_html_tables(root: Path) -> list[tuple[str, str, str | None]]:
    """(name, status, source) for every station in the HTML map's
    CORE.items + SPOKES[].stations data tables (station objects are the
    literals whose OWN keys include name: and status:)."""
    path = root / HTML_MAP
    text = path.read_text(encoding="utf-8")
    stations: list[tuple[str, str, str | None]] = []
    for var, anchor, open_ch in (
        ("CORE", "var CORE =", "{"),
        ("SPOKES", "var SPOKES =", "["),
    ):
        idx = text.find(anchor)
        if idx < 0:
            raise ValueError(f"{path}: data table '{var}' not found")
        start = text.find(open_ch, idx)
        _, end = _extract_balanced(text, start)
        objects: list[str] = []
        _collect_objects(text[start + 1:end], objects)
        for obj in objects:
            own = _own_keys(obj)
            if not re.search(r"\bname\s*:", own) or not re.search(r"\bstatus\s*:", own):
                continue
            name = re.search(r'name:\s*"((?:[^"\\]|\\.)*)"', own)
            status = re.search(r'status:\s*"([^"]*)"', own)
            source = re.search(r'source:\s*(?:"([^"]*)"|null)', own)
            if not name or not status:
                raise ValueError(f"{path}: station object missing name/status: {obj[:80]!r}")
            stations.append((
                name.group(1),
                status.group(1),
                source.group(1) if (source and source.group(1)) else None,
            ))
    return stations


def check_parity(svg: list[tuple[str, str, str | None]],
                 html: list[tuple[str, str, str | None]],
                 findings: list[str]) -> None:
    svg_by_name = {name: (status, source) for name, status, source in svg}
    html_by_name = {name: (status, source) for name, status, source in html}
    if len(svg_by_name) != len(svg):
        findings.append(
            "scripts/generate_scaffold_map_svg.py: duplicate station name in data table"
        )
    if len(html_by_name) != len(html):
        findings.append("docs/scaffold_map.html: duplicate station name in data table")
    for name in sorted(svg_by_name.keys() - html_by_name.keys()):
        findings.append(
            f"station parity: {name!r} in the SVG data table but missing from "
            f"docs/scaffold_map.html"
        )
    for name in sorted(html_by_name.keys() - svg_by_name.keys()):
        findings.append(
            f"station parity: {name!r} in docs/scaffold_map.html but missing "
            f"from the SVG data table"
        )
    for name in sorted(svg_by_name.keys() & html_by_name.keys()):
        s_status, s_source = svg_by_name[name]
        h_status, h_source = html_by_name[name]
        if s_status not in STATUS_TIERS:
            findings.append(f"station {name!r}: unknown status tier {s_status!r} (SVG data)")
        if h_status not in STATUS_TIERS:
            findings.append(f"station {name!r}: unknown status tier {h_status!r} (HTML data)")
        if s_status != h_status:
            findings.append(
                f"station parity: {name!r} is {s_status!r} in the SVG data table "
                f"but {h_status!r} in docs/scaffold_map.html"
            )
        if s_source != h_source:
            findings.append(
                f"station parity: {name!r} tracks {s_source!r} in the SVG data "
                f"table but {h_source!r} in docs/scaffold_map.html"
            )


# ----------------------------------------------------------------- Tier 2


def proposal_status_paragraph(root: Path, source: str) -> str:
    """The first `**Status:**` paragraph of a proposal (hand-written
    prose; multi-line by convention, and the marker itself is not fully
    uniform across the corpus — `**Status:** X` and `**Status: X**`
    both occur — so both spellings are accepted)."""
    path = root / PROPOSALS / source
    if not path.is_file():
        raise ValueError(f"cited proposal does not exist: {path}")
    text = path.read_text(encoding="utf-8")
    m = re.search(r"\*\*Status:\s*(\*\*)?", text)
    if not m:
        raise ValueError(f"{path}: no '**Status:**' line")
    rest = text[m.end():]
    paragraph = rest.split("\n\n")[0]
    paragraph = re.sub(r"\s+", " ", paragraph).strip()
    return paragraph.strip("*").strip()


def classify(paragraph: str) -> str | None:
    """Bucket for a proposal status paragraph: 'gated', 'delivered',
    'proposed', or None (no claim — skip). Keyword order is the
    documented precedence: gated-words first (a proposal that is partly
    blocked is not cleanly delivered), then delivery words, then a bare
    proposal."""
    low = paragraph.lower()
    if any(word in low for word in GATED_WORDS):
        return "gated"
    if any(word in low for word in DELIVERED_WORDS):
        return "delivered"
    if "proposed" in low:
        return "proposed"
    return None


def check_sources(root: Path,
                  stations: list[tuple[str, str, str | None]],
                  findings: list[str]) -> tuple[int, list[str]]:
    """Tier 2 on one file's table; returns (linked_count, unlinked_names)."""
    linked = 0
    unlinked: list[str] = []
    for name, status, source in stations:
        if source is None:
            unlinked.append(name)
            continue
        linked += 1
        try:
            paragraph = proposal_status_paragraph(root, source)
        except ValueError as err:
            findings.append(f"station {name!r}: {err}")
            continue
        bucket = classify(paragraph)
        if bucket is None:
            continue
        expected = EXPECT_FOR_BUCKET[bucket]
        if status not in expected:
            findings.append(
                f"station {name!r} is declared {status!r} but its source "
                f"{source} says [{bucket}]: “{paragraph[:110]}…”"
            )
    return linked, unlinked


# ------------------------------------------------------------------- main


def main(argv: list[str]) -> int:
    if len(argv) == 1 and argv[0] == "--help":
        print(__doc__)
        return EXIT_FRESH
    args = argv[1:]
    if not args:
        root = repo_root_from_script()
    elif len(args) == 2 and args[0] == "--root":
        root = Path(args[1]).resolve()
    else:
        print("usage: check_scaffold_map_freshness.py [--root REPO_ROOT]",
              file=sys.stderr)
        return EXIT_ERROR

    findings: list[str] = []
    try:
        qa, axioms, sorries = parse_scoreboard(root)
        svg_stations = parse_svg_tables(root)
        html_stations = parse_html_tables(root)
        svg_text = (root / SVG_GENERATOR).read_text(encoding="utf-8")
        html_text = (root / HTML_MAP).read_text(encoding="utf-8")
    except (OSError, ValueError, SyntaxError) as err:
        print(f"error: {err}", file=sys.stderr)
        return EXIT_ERROR

    # Tier 1a: stats stamps vs the generated scoreboard.
    check_stamps(svg_text, str(SVG_GENERATOR), qa, axioms, sorries, findings)
    check_stamps(html_text, str(HTML_MAP), qa, axioms, sorries, findings)

    # Tier 1b: pairwise station parity.
    check_parity(svg_stations, html_stations, findings)

    # Tier 2: proposal-status buckets (on both tables; parity already
    # guarantees they agree, so both must clear independently).
    svg_linked, svg_unlinked = check_sources(root, svg_stations, findings)
    html_linked, html_unlinked = check_sources(root, html_stations, findings)

    for line in findings:
        print(f"FINDING {line}")
    print(
        f"{len(svg_stations)} stations checked; {svg_linked} with a proposal "
        f"source, {len(svg_unlinked)} without "
        f"(HTML table: {html_linked}/{len(html_unlinked)}); scoreboard "
        f"{axioms} axioms · {qa} QA · {sorries} sorries"
    )
    print("no-source stations (coverage gaps, listed not hidden): "
          + ", ".join(svg_unlinked))

    if findings:
        print(
            "scaffold map freshness FAILED: the transit map disagrees with "
            "the scoreboard, its own second copy, or a cited proposal's "
            "status. Update the station data tables (both "
            "scripts/generate_scaffold_map_svg.py and docs/scaffold_map.html), "
            "regenerate the SVG, and re-run.",
            file=sys.stderr,
        )
        return EXIT_FINDINGS
    return EXIT_FRESH


if __name__ == "__main__":
    sys.exit(main(sys.argv))

#!/usr/bin/env python3
"""Refresh source-derived metrics in docs/5_QA_SCOREBOARD.md."""

from __future__ import annotations

import re
from collections import defaultdict
from datetime import date
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCOREBOARD = ROOT / "docs" / "5_QA_SCOREBOARD.md"
START = "<!-- BEGIN GENERATED SOURCE METRICS -->"
END = "<!-- END GENERATED SOURCE METRICS -->"
DECLARATION = re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
PLACEHOLDER = re.compile(r"\b(?:sorry|admit)\b")


def strip_lean_comments(source: str) -> str:
    """Remove line and nested block comments while retaining Lean code."""
    result: list[str] = []
    depth = 0
    index = 0
    while index < len(source):
        pair = source[index : index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif pair == "-/" and depth:
            depth -= 1
            index += 2
        elif pair == "--" and depth == 0:
            newline = source.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
        else:
            if depth == 0:
                result.append(source[index])
            index += 1
    return "".join(result)


def lean_files(directory: Path) -> list[Path]:
    return sorted(directory.rglob("*.lean"))


def build_metrics() -> str:
    qa_rows: list[tuple[str, int, int]] = []
    qa_total = 0
    qa_placeholders = 0
    domain_counts: dict[str, int] = defaultdict(int)

    for path in lean_files(ROOT / "Scaffold" / "QA"):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        declarations = len(DECLARATION.findall(code))
        placeholders = len(PLACEHOLDER.findall(code))
        relative = path.relative_to(ROOT).as_posix()
        domain = path.relative_to(ROOT / "Scaffold" / "QA").parts[0]
        qa_rows.append((relative, declarations, placeholders))
        domain_counts[domain] += declarations
        qa_total += declarations
        qa_placeholders += placeholders

    public_axioms = 0
    public_placeholders = 0
    for path in lean_files(ROOT / "Scaffold" / "Mathlib"):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        public_axioms += len(AXIOM.findall(code))
        public_placeholders += len(PLACEHOLDER.findall(code))

    lines = [
        START,
        f"_Generated from Lean source on {date.today().isoformat()}._",
        "",
        "| Metric | Count |",
        "| --- | ---: |",
        f"| QA theorem/lemma declarations | {qa_total} |",
        f"| `sorry`/`admit` tokens in QA code | {qa_placeholders} |",
        f"| Explicit axioms in `Scaffold/Mathlib` | {public_axioms} |",
        f"| `sorry`/`admit` tokens in `Scaffold/Mathlib` code | {public_placeholders} |",
        "",
        "### QA declarations by domain",
        "",
        "| Domain | Declarations |",
        "| --- | ---: |",
    ]
    lines.extend(f"| {domain} | {count} |" for domain, count in sorted(domain_counts.items()))
    lines.extend(
        [
            "",
            "### QA files",
            "",
            "| File | Declarations | Placeholder tokens |",
            "| --- | ---: | ---: |",
        ]
    )
    lines.extend(f"| `{path}` | {count} | {placeholders} |" for path, count, placeholders in qa_rows)
    lines.extend([END, "", ""])
    return "\n".join(lines)


def main() -> None:
    document = SCOREBOARD.read_text(encoding="utf-8")
    if START not in document or END not in document:
        raise SystemExit(f"generated markers are missing from {SCOREBOARD}")
    prefix, remainder = document.split(START, 1)
    _, suffix = remainder.split(END, 1)
    SCOREBOARD.write_text(prefix + build_metrics() + suffix.lstrip("\n"), encoding="utf-8")


if __name__ == "__main__":
    main()
